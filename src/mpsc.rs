
use std::{sync::atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, compiler_fence}, mem::{size_of, MaybeUninit, forget, ManuallyDrop, transmute, align_of, transmute_copy}, ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut, drop_in_place}, thread::{JoinHandle, self, park, yield_now, Thread, current, sleep}, cell::UnsafeCell, str::FromStr, cmp::min, alloc::{alloc, Layout}, marker::PhantomData, ops::Add, time::{Duration, SystemTime}, iter::zip};

use crate::{root_alloc::{RootAllocator, Block4KPtr}, utils::{ptr_align_dist, with_scoped_consume, bitcopy, high_order_pow2, DrainablePageHolder, offset_to_higher_multiple, bitcast}, cast, loopbuffer::{InlineLoopBuffer, LoopBufferTraverser}, array::Array, garbage, semi_inline_seqv::SemiInlineSeqv, driver::SubRegionAllocator,  };

pub struct MPSCQueue<T> {
  internals: MPMCQueueImpl,
  __:PhantomData<T>
}
unsafe impl <T> Sync for MPSCQueue<T> {}

impl <T> MPSCQueue<T> {
  pub fn new() -> Self {
    return Self{
      __:PhantomData,
      internals: MPMCQueueImpl::new()
    };
  }
  pub fn enqueue_item(&self, item:T, page_sourse: &mut dyn DrainablePageHolder) { unsafe {
    self.internals.enqueue_item_impl(
      addr_of!(item).cast::<u8>(),
      size_of::<T>() as u32, align_of::<T>() as u8, transmute_copy(&page_sourse));
    forget(item);
  } }
  pub fn dequeue_item(&self, page_store: &mut SubRegionAllocator) -> Option<T> {
    let mut val = garbage!(T);
    let mut success = false;
    self.internals.dequeue_item_impl(
      align_of::<T>(), size_of::<T>(), page_store, addr_of_mut!(val).cast(), &mut success);
    if success {
      return Some(val)
    }
    forget(val);
    return None
  }
}
pub(crate) struct MPMCQueueImpl {
  write_head: (AtomicU32, AtomicU32),
  read_head: AtomicU64,
}

#[repr(align(8))]
struct MessageQueuePageHeaderSplit(AtomicU16,AtomicU16,AtomicU32);
struct MessageQueuePageHeaderCombined(AtomicU64);
#[repr(align(8))]
struct MessageQueuePageHeaderSplitNonatomic(u16,u16,u32);

impl MPMCQueueImpl {
  pub(crate) fn new() -> Self { unsafe {
    let mut new = MaybeUninit::<Self>::uninit();
    addr_of_mut!(new).cast::<u8>().write_bytes(0, size_of::<Self>());
    return new.assume_init()
  } }
  #[inline(never)]
  pub(crate) fn enqueue_item_impl(
    &self,
    msg_ptr: *const u8,
    msg_byte_stride: u32,
    msg_align: u8,
    page_source: *mut dyn DrainablePageHolder
  ) { unsafe {
    let addr_split = addr_of!(self.write_head);
    let addr_single = addr_split.cast::<AtomicU64>();
    let head_split = &*addr_split;
    let head_single = &*addr_single;
    loop {
      let prior = head_single.fetch_add(
        (msg_byte_stride as u64) << 40, Ordering::Relaxed);
      let compacted_ptr = prior & ((1 << 40) - 1);
      if compacted_ptr == 0 { // we gotta perfrom the first init
        let outcome = head_split.0.compare_exchange(
          0, u8::MAX as u32, Ordering::Relaxed, Ordering::Relaxed);
        match outcome {
          Err(actual) => {
            if actual == u8::MAX as u32 { // other's doing it
              while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
            }
            fence(Ordering::Acquire);
            continue;
          },
          Ok(_) => { // we put first page
            let Block4KPtr(first_page) = (*page_source).try_drain_page().unwrap();
            first_page.write_bytes(0, size_of::<MessageQueuePageHeaderCombined>());
            self.read_head.store(first_page as u64, Ordering::Release);

            let compacted = first_page as u64 >> 12;
            assert!(compacted & u32::MAX as u64 != u8::MAX as u64);

            let mut offset_past_header = size_of::<MessageQueuePageHeaderCombined>() as u64;
            offset_past_header += offset_to_higher_multiple(offset_past_header, msg_align as usize);
            let offseted = compacted | (offset_past_header << 40);

            head_single.store(offseted, Ordering::Release);
            continue;
          }
        }
      }
      if prior & (u32::MAX as u64) == u8::MAX as u64 { // someone is installing the page
        while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
        fence(Ordering::Acquire);
        continue;
      }

      // main path
      let byte_offset = prior >> 40;
      let offset_went_beyound_boundry = byte_offset >= 4096;
      if offset_went_beyound_boundry { // gotta replace the page
        let outcome = head_split.0.compare_exchange(
          (prior & (u32::MAX as u64)) as u32, u8::MAX as u32,
          Ordering::Relaxed, Ordering::Relaxed);
        match outcome {
          Err(actual) => {
            if actual & u8::MAX as u32 == u8::MAX as u32 { // someone is installing the page
              while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
              fence(Ordering::Acquire);
            }
            continue;
          },
          Ok(_) => {
            // switching is on us
            let current_norm_ptr = compacted_ptr << 12;
            let norm_ptr = current_norm_ptr as *const MessageQueuePageHeaderCombined;
            let Block4KPtr(next_page) = (*page_source).try_drain_page().unwrap();
            let next_compacted = next_page as u64 >> 12;
            (&*norm_ptr).0.fetch_or(next_compacted, Ordering::Release);

            let mut offset_past_header = size_of::<MessageQueuePageHeaderCombined>() as u64;
            offset_past_header += offset_to_higher_multiple(offset_past_header, msg_align as usize);
            let combined = next_compacted | (offset_past_header << 40);
            head_single.store(combined, Ordering::Release);
            continue;
          }
        }
      }
      // if some thread has put in the page, see it as happened
      fence(Ordering::Acquire);
      // we have our piece of memory. it is safe to do anything with it.
      let normalised_ptr = (compacted_ptr << 12) as *mut u8;
      let slot_mem = normalised_ptr.add(byte_offset as usize);
      copy_nonoverlapping(msg_ptr, slot_mem, msg_byte_stride as usize);

      let page_meta = &*(normalised_ptr as *mut AtomicU64);
      let _ = page_meta.fetch_add(1 << 40, Ordering::Release); // publish it for the consumer

      return
    }
  } }
  #[inline(never)]
  pub(crate) fn dequeue_item_impl(
    &self,
    msg_align: usize,
    msg_byte_stride: usize,
    sralloc: *mut SubRegionAllocator,
    write_back: *mut u8,
    did_return_value: &mut bool
  ) { unsafe {
    let limit = (4096 - size_of::<MessageQueuePageHeaderCombined>()) / msg_byte_stride;
    let mut fm_off = size_of::<MessageQueuePageHeaderCombined>() as u64;
    fm_off += offset_to_higher_multiple(fm_off, msg_align);
    'page: loop {
      let rh = self.read_head.load(Ordering::Acquire);
      if rh == 0 { // first init didnt happen
        *did_return_value = false;
        return
      }
      let mut page = rh as *mut ();
      'inner: loop {
        let meta = &*page.cast::<MessageQueuePageHeaderCombined>();
        let data_meta = meta.0.load(Ordering::Acquire);
        let reader_index = data_meta >> 52;
        let writer_index = (data_meta >> 40) & ((1 << 12) - 1);
        if reader_index >= limit as u64 {
          // no more items on this page.
          let compacted_next = data_meta & ((1u64 << 40) - 1);
          let has_next = compacted_next != 0;
          if has_next {
            let normalised_next = compacted_next << 12;
            let outcome = self.read_head.compare_exchange(
              rh, normalised_next, Ordering::Release, Ordering::Acquire);
            match outcome {
              Err(actual) => { // other thread did it
                page = actual as *mut ();
                continue 'inner;
              },
              Ok(_) => {
                (*sralloc).give_page_for_recycle(Block4KPtr(rh as _));
                continue 'page;
              }
            }
          } else { // nothing more on this page
            *did_return_value = false;
            return
          }
        }
        if !(writer_index > reader_index) {
          // read all items on this page.
          // page is not saturated yet
          *did_return_value = false;
          return
        }
        // bump reader count
        let real = meta.0.fetch_add(1 << 52, Ordering::AcqRel);
        let reader_index = real >> 52;
        assert!(reader_index <= ((1 << 12) - 1), "we have corrupted the metadata");
        if reader_index >= limit as u64 { continue 'page; }

        let msg_ptr = page.cast::<u8>()
          .add(fm_off as usize).add(reader_index as usize * msg_byte_stride);
        copy_nonoverlapping(msg_ptr, write_back, msg_byte_stride);
        *did_return_value = true;
        return
      }
    }

  }; }
}

unsafe impl Sync for MPMCQueueImpl {}

#[repr(align(8))]
struct MQU(u32, u32);
#[test]
fn single_store() { unsafe {
  assert!(align_of::<MPMCQueueImpl>() == 8);
  let mut a = (u32::MAX, 0u32);
  let ptr = addr_of_mut!(a).cast::<u32>();
  assert!(*ptr == u32::MAX && *ptr.add(1) == 0);
  *ptr.cast::<u64>() = (u32::MAX as u64) << 32;
  assert!(a == (0, u32::MAX))
} }

struct TestPageAlloc;
impl DrainablePageHolder for TestPageAlloc {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
    let mem = unsafe { alloc(Layout::from_size_align_unchecked(4096, 4096)) };
    return Some(Block4KPtr(mem))
  }
}

#[test]
fn basic_inout_queue_test() {
  let mq = MPSCQueue::new();
  let mut allocer = TestPageAlloc;
  let mut srallocer = SubRegionAllocator::new(&mut allocer);

  let limit = 1_000_000;
  for i in 0 .. limit {
    mq.enqueue_item(i, &mut allocer);
  }
  for i in 0 .. limit {
    let val = mq.dequeue_item(&mut srallocer);
    match val {
      None => panic!(),
      Some(val) => {
        assert!(i == val)
      }
    }
  }
}

#[test]
fn many_writers_one_reader() {
  let mut r = RootAllocator::new();
  let mut sraloc = SubRegionAllocator::new(&mut r);
  let q = MPSCQueue::new();
  let t = addr_of_mut!(sraloc);
  let thread_count = 64u32;
  let per_thread_msg_count = 100000;
  let sync = AtomicU64::new(0);
  let begin = SystemTime::now();
  thread::scope(|scope|{
    for i in 0 .. thread_count {
      let q = &q;
      let n = t as u64;
      let sync = addr_of!(sync) as u64;
      scope.spawn(move || {
        let sync = unsafe {&*(sync as *const AtomicU64)};
        for k in (i * per_thread_msg_count) .. (i + 1) * per_thread_msg_count {
          let t = n as *mut SubRegionAllocator;
          q.enqueue_item(k, unsafe{&mut*t});
          sync.fetch_add(1, Ordering::Relaxed);
        }
      });
    }
  });
  let el = begin.elapsed().unwrap();
  println!("{} ms", el.as_millis());
  let mut vec = Vec::new();
  let total_count = thread_count * per_thread_msg_count;
  vec.reserve(total_count as usize);
  let mut sraloc = SubRegionAllocator::new(t);
  while sync.load(Ordering::Relaxed) != total_count as u64 {}
  for _ in 0 .. total_count {
    let msg = q.dequeue_item(&mut sraloc);
    match msg {
      None => panic!(),
      Some(msg) => {
        vec.push(msg);
      }
    }
  }
  vec.sort();
  println!("{}", vec.len());
  for i in 0 .. total_count {
    let ok = *vec.get(i as usize).unwrap() == i ;
    assert!(ok)
  }
}

#[test]
fn rust_mpsc() {
  let (s,r) = std::sync::mpsc::channel();
  let thread_count = 64u32;
  let per_thread_msg_count = 100000;
  let sync = AtomicU64::new(0);
  let begin = SystemTime::now();
  thread::scope(|scope|{
    for i in 0 .. thread_count {
      let s = s.clone();
      let sync = addr_of!(sync) as u64;
      scope.spawn(move || {
        let sync = unsafe {&*(sync as *const AtomicU64)};
        for k in (i * per_thread_msg_count) .. (i + 1) * per_thread_msg_count {
          s.send(k).unwrap();
          sync.fetch_add(1, Ordering::Relaxed);
        }
      });
    }
  });
  let el = begin.elapsed().unwrap();
  println!("{} ms", el.as_millis());
  let mut vec = Vec::new();
  let total_count = thread_count * per_thread_msg_count;
  vec.reserve(total_count as usize);
  while sync.load(Ordering::Relaxed) != total_count as u64 {}
  for _ in 0 .. total_count {
    let msg = r.recv().unwrap();
    vec.push(msg);
  }
  vec.sort();
  println!("{}", vec.len());
  for i in 0 .. total_count {
    let ok = *vec.get(i as usize).unwrap() == i ;
    assert!(ok)
  }
}

#[test]
fn concurent_reads() {
  let mut r = TestPageAlloc;
  let reader_thread_count = 64 ;
  let q = MPSCQueue::new();
  let item_per_thread = 10000;
  let total_item_count = reader_thread_count * item_per_thread;
  println!("{total_item_count}");
  let stores_completed = AtomicBool::new(false);
  for i in 0 .. total_item_count {
    q.enqueue_item(i, &mut r);
  }
  stores_completed.store(true, Ordering::Release);
  thread::scope(|scope|{
    let mut handles = Vec::new();
    handles.reserve(reader_thread_count);
    for _ in 0 .. reader_thread_count {
      let p = addr_of_mut!(r) as u64;
      let q = &q;
      let done = addr_of!(stores_completed) as u64;
      let h = scope.spawn(move ||{
        let p = unsafe { transmute::<_, &mut RootAllocator>(p) };
        let mut sraloc = SubRegionAllocator::new(p);
        let mut vec = Vec::new();
        vec.reserve(item_per_thread);
        let done = unsafe {&*(done as *const AtomicBool)};
        while !done.load(Ordering::Relaxed) {};
        fence(Ordering::Acquire);
        loop {
          let item = q.dequeue_item(&mut sraloc);
          match item {
            None => {
              break
            },
            Some(item) => {
              vec.push(item);
              continue;
            }
          }
        }
        return vec
      });
      handles.push(h)
    }
    let mut res = Vec::new();
    res.reserve(total_item_count);
    for h in handles {
      let mut v = h.join().unwrap();
      res.append(&mut v)
    }
    println!("{}", res.len());
    res.sort();
    let mut printed = false;
    for i in 0 .. total_item_count {
      let v = *res.get(i).unwrap();
      // assert!(v == i)
      if v != i && !printed {
        printed = false;
      }
    }
    let mut str = String::new();
    for (g,e) in zip(res, 0..) {
      str.push_str(format!("{e} {g}; ").as_str())
    };
    println!("{}", str)
  });
}

#[test]
fn many_writers_many_readers() {
  let mut r = RootAllocator::new();
  let writer_thread_count = 32 ;
  let reader_thread_count = 32 ;
  let q = MPSCQueue::new() ;
  let items_per_thread = 100000;
  let total_item_count = writer_thread_count * items_per_thread;
  println!("{}", total_item_count);
  thread::scope(|scope|{
    let write_count = AtomicU64::new(0);
    for i in 0 .. writer_thread_count {
      let r = addr_of_mut!(r) as u64;
      let q = &q;
      let store_count = addr_of!(write_count) as u64;
      scope.spawn(move || {
        for k in (i * items_per_thread) .. (i + 1) * items_per_thread {
          let r = unsafe {&mut * (r as *mut RootAllocator)};
          q.enqueue_item(k, r);
          let store_count = unsafe {&*(store_count as *const AtomicU64)};
          store_count.fetch_add(1, Ordering::Relaxed);
        }
      });
    }
    let mut rts = Vec::new();
    rts.reserve(writer_thread_count);
    for _ in 0 .. reader_thread_count {
      let store_count = addr_of!(write_count) as u64;
      let r = addr_of_mut!(r) as u64;
      let q = &q;
      let rt = scope.spawn(move ||{
        let r = unsafe {&mut * (r as *mut RootAllocator)};
        let store_count = unsafe {&*(store_count as *const AtomicU64)};
        let mut sr = SubRegionAllocator::new(r);
        let mut vec = Vec::new();
        loop {
          let item = q.dequeue_item(&mut sr);
          match item {
            None => {
              if store_count.load(Ordering::Relaxed) as usize != total_item_count {
                continue;
              }
              break;
            },
            Some(val) => {
              vec.push(val);
            }
          }
        }
        return vec
      });
      rts.push(rt);
    }
    let mut res = Vec::new();
    res.reserve(total_item_count);
    for rt in rts {
      let mut v = rt.join().unwrap();
      res.append(&mut v);
    }
    res.sort();
    println!("{}", res.len());
  })
}
