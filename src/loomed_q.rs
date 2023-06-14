// use std::{marker::PhantomData, ptr::{addr_of, addr_of_mut, copy_nonoverlapping}, mem::{size_of, transmute_copy, align_of, forget, MaybeUninit, transmute}, sync::atomic::{Ordering, fence}};

// use crate::{utils::{DrainablePageHolder, num_align_dist}, driver::SubRegionAllocator, garbage, root_alloc::{Block4KPtr, RootAllocator}};

// use loom::sync::{atomic::{AtomicU64, AtomicU32, AtomicBool}};
// use loom::thread::spawn;

// struct MPMCQueue<T> {
//   internals: MPMCQueueImpl,
//   __:PhantomData<T>
// }
// unsafe impl <T> Sync for MPMCQueue<T> {}

// impl <T> MPMCQueue<T> {
//   fn new() -> Self {
//     return Self{
//       __:PhantomData,
//       internals: MPMCQueueImpl::new()
//     };
//   }
//   fn enqueue_item(&self, item:T, page_sourse: &mut dyn DrainablePageHolder) { unsafe {
//     self.internals.enqueue_item_impl(
//       addr_of!(item).cast::<u8>(),
//       size_of::<T>() as u32, align_of::<T>() as u8, transmute_copy(&page_sourse));
//     forget(item);
//   } }
//   fn dequeue_item(&self, page_store: &mut SubRegionAllocator) -> Option<T> {
//     let mut val = garbage!(T);
//     let mut success = false;
//     self.internals.dequeue_item_impl(
//       align_of::<T>(), size_of::<T>(), page_store, addr_of_mut!(val).cast(), &mut success);
//     if success {
//       return Some(val)
//     }
//     forget(val);
//     return None
//   }
// }
// struct MPMCQueueImpl {
//   write_head: (AtomicU32, AtomicU32),
//   read_head: AtomicU64,
// }

// struct MessageQueuePageHeaderCombined(AtomicU64);

// impl MPMCQueueImpl {
//   fn new() -> Self { unsafe {
//     let mut new = MaybeUninit::<Self>::uninit();
//     addr_of_mut!(new).cast::<u8>().write_bytes(0, size_of::<Self>());
//     return new.assume_init()
//   } }
//   #[inline(never)]
//   fn enqueue_item_impl(
//     &self,
//     msg_ptr: *const u8,
//     msg_byte_stride: u32,
//     msg_align: u8,
//     page_source: *mut dyn DrainablePageHolder
//   ) { unsafe {
//     let addr_split = addr_of!(self.write_head);
//     let addr_single = addr_split.cast::<AtomicU64>();
//     let head_split = &*addr_split;
//     let head_single = &*addr_single;
//     loop {
//       let prior = head_single.fetch_add(
//         (msg_byte_stride as u64) << 40, Ordering::Relaxed);
//       let compacted_ptr = prior & ((1 << 40) - 1);
//       if compacted_ptr == 0 { // we gotta perfrom the first init
//         let outcome = head_split.0.compare_exchange(
//           0, u8::MAX as u32, Ordering::Relaxed, Ordering::Relaxed);
//         match outcome {
//           Err(actual) => {
//             if actual == u8::MAX as u32 { // other's doing it
//               while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
//             }
//             fence(Ordering::Acquire);
//             continue;
//           },
//           Ok(_) => { // we put first page
//             let Block4KPtr(first_page) = (*page_source).try_drain_page().unwrap();
//             first_page.write_bytes(0, size_of::<MessageQueuePageHeaderCombined>());
//             self.read_head.store(first_page as u64, Ordering::Release);

//             let compacted = first_page as u64 >> 12;
//             assert!(compacted & u32::MAX as u64 != u8::MAX as u64);

//             let mut offset_past_header = size_of::<MessageQueuePageHeaderCombined>() as u64;
//             offset_past_header += num_align_dist(offset_past_header, msg_align as usize);
//             let offseted = compacted | (offset_past_header << 40);

//             head_single.store(offseted, Ordering::Release);
//             continue;
//           }
//         }
//       }
//       if prior & (u32::MAX as u64) == u8::MAX as u64 { // someone is installing the page
//         while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
//         fence(Ordering::Acquire);
//         continue;
//       }

//       // main path
//       let byte_offset = prior >> 40;
//       let offset_went_beyound_boundry = byte_offset >= 4096;
//       if offset_went_beyound_boundry { // gotta replace the page
//         let outcome = head_split.0.compare_exchange(
//           (prior & (u32::MAX as u64)) as u32, u8::MAX as u32,
//           Ordering::Relaxed, Ordering::Relaxed);
//         match outcome {
//           Err(actual) => {
//             if actual & u8::MAX as u32 == u8::MAX as u32 { // someone is installing the page
//               while head_split.0.load(Ordering::Relaxed) == u8::MAX as u32 {}
//               fence(Ordering::Acquire);
//             }
//             continue;
//           },
//           Ok(_) => {
//             // switching is on us
//             let current_norm_ptr = compacted_ptr << 12;
//             let norm_ptr = current_norm_ptr as *const MessageQueuePageHeaderCombined;
//             let Block4KPtr(next_page) = (*page_source).try_drain_page().unwrap();
//             let next_compacted = next_page as u64 >> 12;
//             (&*norm_ptr).0.fetch_or(next_compacted, Ordering::Release);

//             let mut offset_past_header = size_of::<MessageQueuePageHeaderCombined>() as u64;
//             offset_past_header += num_align_dist(offset_past_header, msg_align as usize);
//             let combined = next_compacted | (offset_past_header << 40);
//             head_single.store(combined, Ordering::Release);
//             continue;
//           }
//         }
//       }
//       // if some thread has put in the page, see it as happened
//       fence(Ordering::Acquire);
//       // we have our piece of memory. it is safe to do anything with it.
//       let normalised_ptr = (compacted_ptr << 12) as *mut u8;
//       let slot_mem = normalised_ptr.add(byte_offset as usize);
//       copy_nonoverlapping(msg_ptr, slot_mem, msg_byte_stride as usize);

//       let page_meta = &*(normalised_ptr as *mut AtomicU64);
//       let _ = page_meta.fetch_add(1 << 40, Ordering::Release); // publish it for the consumer

//       return
//     }
//   } }
//   #[inline(never)]
//   fn dequeue_item_impl(
//     &self,
//     msg_align: usize,
//     msg_byte_stride: usize,
//     sralloc: *mut SubRegionAllocator,
//     write_back: *mut u8,
//     did_return_value: &mut bool
//   ) { unsafe {
//     let limit = (4096 - size_of::<MessageQueuePageHeaderCombined>()) / msg_byte_stride;
//     let mut fm_off = size_of::<MessageQueuePageHeaderCombined>() as u64;
//     fm_off += num_align_dist(fm_off, msg_align);
//     loop {
//       let rh = self.read_head.load(Ordering::Acquire);
//       if rh == 0 { // first init didnt happen
//         *did_return_value = false;
//         return
//       }
//       let page = rh as *mut ();
//       let meta = &*page.cast::<MessageQueuePageHeaderCombined>();
//       let data_meta = meta.0.load(Ordering::Acquire);
//       let reader_index = data_meta >> 52;
//       let writer_index = (data_meta >> 40) & ((1 << 12) - 1);
//       if reader_index >= limit as u64 {
//         // no more items on this page.
//         let compacted_next = data_meta & ((1u64 << 40) - 1);
//         let has_next = compacted_next != 0;
//         if has_next {
//           let normalised_next = compacted_next << 12;
//           let outcome = self.read_head.compare_exchange(
//             rh, normalised_next, Ordering::Release, Ordering::Relaxed);
//           match outcome {
//             Err(_) => continue, // other thread did it
//             Ok(_) => {
//               (*sralloc).give_page_for_recycle(Block4KPtr(rh as _));
//               continue;
//             }
//           }
//         } else {
//           *did_return_value = false;
//           return
//         }
//       }
//       if !(writer_index > reader_index) {
//         *did_return_value = false;
//         return
//       }

//       let real = meta.0.fetch_add(1 << 52, Ordering::AcqRel);
//       let reader_index = real >> 52;
//       if reader_index >= limit as u64 { continue; }

//       let msg_ptr = page.cast::<u8>()
//         .add(fm_off as usize).add(reader_index as usize * msg_byte_stride);
//       copy_nonoverlapping(msg_ptr, write_back, msg_byte_stride);
//       *did_return_value = true;
//       return
//     }

//   }; }
// }

// unsafe impl Sync for MPMCQueueImpl {}


// #[test]
// fn concurent_reads_loomed() {
//   loom::model(||{
//     let mut r = RootAllocator::new();
//     let reader_thread_count = 2 ;
//     let q = MPMCQueue::<usize>::new();
//     let item_per_thread = 100;
//     let total_item_count = reader_thread_count * item_per_thread;
//     println!("{total_item_count}");
//     let stores_completed = AtomicBool::new(false);
//     for i in 0 .. total_item_count {
//       q.enqueue_item(i, &mut r);
//     }
//     stores_completed.store(true, Ordering::Release);

//     let mut handles = Vec::new();
//     handles.reserve(reader_thread_count);
//     for _ in 0 .. reader_thread_count {
//       let p = addr_of_mut!(r) as u64;
//       let q = addr_of!(q) as u64;
//       let done = addr_of!(stores_completed) as u64;
//       let h = spawn(move ||{
//         let p = unsafe { transmute::<_, &mut RootAllocator>(p) };
//         let q = unsafe { transmute::<_, &MPMCQueue<usize>>(q) };
//         let mut sraloc = SubRegionAllocator::new(p);
//         let mut vec = Vec::new();
//         vec.reserve(item_per_thread);
//         let done = unsafe {&*(done as *const AtomicBool)};
//         while !done.load(Ordering::Relaxed) {};
//         fence(Ordering::Acquire);
//         loop {
//           let item = q.dequeue_item(&mut sraloc);
//           match item {
//             None => {
//               break
//             },
//             Some(item) => {
//               vec.push(item);
//               continue;
//             }
//           }
//         }
//         return vec
//       });
//       handles.push(h)
//     }
//     let mut res = Vec::new();
//     res.reserve(total_item_count);
//     for h in handles {
//       let mut v = h.join().unwrap();
//       res.append(&mut v)
//     }
//     println!("{}", res.len());
//     res.sort();
//     for i in 0 .. total_item_count {
//       let v = *res.get(i).unwrap();
//       // assert!(v == i)
//     }
//   })
// }