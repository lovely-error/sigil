
use std::{sync::{atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, compiler_fence}, mpsc::{Receiver, channel, Sender}}, mem::{size_of, MaybeUninit, forget, ManuallyDrop, transmute, align_of, transmute_copy, needs_drop}, ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut, drop_in_place}, thread::{JoinHandle, self, park, yield_now, Thread, current, sleep, spawn}, cell::UnsafeCell, str::FromStr, cmp::min, alloc::{alloc, Layout}, marker::PhantomData, ops::Add, time::{Duration, SystemTime}, iter::zip, collections::HashMap, os::fd::{AsRawFd, RawFd}};

use core_affinity::CoreId;
use polling::{Poller, Source, Event};

use crate::{root_alloc::{RootAllocator, Block4KPtr}, utils::{ptr_align_dist, with_scoped_consume, bitcopy, high_order_pow2, PageSource, offset_to_higher_multiple, bitcast}, cast, loopbuffer::{InlineLoopBuffer, LoopBufferTraverser}, array::Array, garbage, semi_inline_seqv::SemiInlineSeqv, mpsc::MPSCQueue,  };

extern crate core_affinity;

pub struct SubRegionAllocator {
  page_provider: *mut dyn PageSource,
  current_page_start: *mut u8,
  allocation_tail: *mut u8,
  free_list: *mut u8
}

static mut DEALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);
static mut ALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);

impl SubRegionAllocator {
  pub fn new(
    page_provider: *mut dyn PageSource
  ) -> Self {
    let mut raw = garbage!(Self);
    raw.page_provider = page_provider;
    raw.free_list = null_mut();
    raw.current_page_start = null_mut();
    return raw;
  }
  pub(crate) fn give_page_for_recycle_impl(&mut self, Block4KPtr(ptr):Block4KPtr) { unsafe {
    *ptr.cast::<*mut u8>() = self.free_list;
    self.free_list = ptr;
  } }
  fn try_take_spare_page(&mut self) -> Option<Block4KPtr> { unsafe {
    if self.free_list == null_mut() { return None }
    let current = self.free_list;
    let next = *self.free_list.cast::<*mut u8>();
    self.free_list = next;
    return Some(Block4KPtr(current))
  } }
  fn set_new_page(&mut self) { unsafe {
    let new_page_ptr;
    let maybe_page = self.drain_spare_page();
    match maybe_page {
      Some(Block4KPtr(ptr)) => new_page_ptr = ptr,
      None => {
        let Block4KPtr(ptr) = (*self.page_provider).try_drain_page().unwrap_or_else(||{
          panic!("infailable page provider failed to give page")
        });
        new_page_ptr = ptr
      }
    }
    self.current_page_start = new_page_ptr;
    {
      let ptr = &mut *new_page_ptr.cast::<RegionMetadata>();
      ptr.ref_count = AtomicU16::new(0);
    };
    self.allocation_tail = new_page_ptr.add(size_of::<RegionMetadata>());
  } }
  #[track_caller]
  pub fn sralloc(
    &mut self,
    byte_size: usize,
    alignment: usize
  ) -> SubRegionRef { unsafe {
    ALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);

    assert!(byte_size != 0);
    let mut reserved_space = size_of::<RegionMetadata>();
    reserved_space += offset_to_higher_multiple(reserved_space as u64, alignment) as usize;
    assert!(
      byte_size <= 4096 - reserved_space,
      "too big allocation, ill fix it when need come");
    if self.current_page_start.is_null() {
      self.set_new_page()
    }
    loop {
      let mut ptr = self.allocation_tail;
      let off = ptr_align_dist(ptr, alignment);
      ptr = ptr.add(off as usize);
      let next_allocation_tail = ptr.add(byte_size);
      if next_allocation_tail as u64 >= (self.current_page_start as u64 + 4096) {
        self.set_new_page(); continue;
      }
      let _ = (*self.current_page_start.cast::<RegionMetadata>())
        .ref_count.fetch_add(1, Ordering::AcqRel);

      self.allocation_tail = next_allocation_tail;
      let dist = ptr as u64 - self.current_page_start as u64;
      assert!(dist <= u16::MAX as u64);

      return SubRegionRef::new(self.current_page_start, dist as u16);
    }
  }; }
  #[track_caller]
  pub fn dispose(&mut self, ptr: SubRegionRef) { unsafe {
    DEALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);

    let (root,_) = ptr.get_components();
    let i = (&*root.cast::<RegionMetadata>()).ref_count.fetch_sub(1, Ordering::AcqRel);
    if i == 1 {
      // this page is ours!
      self.give_page_for_recycle_impl(Block4KPtr(root.cast()));
    }
    // forget(ptr);
  } }
  fn drain_spare_page(&mut self) -> Option<Block4KPtr> { unsafe {
    if self.free_list == null_mut() { return None }
    let page = self.free_list;
    let page_after_current = *self.free_list.cast::<*mut u8>();
    self.free_list = page_after_current;
    return Some(Block4KPtr(page))
  } }
}

impl PageSource for SubRegionAllocator {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      if let k@Some(_) = self.drain_spare_page() {
        return k
      } else {
        unsafe { (&mut *self.page_provider).try_drain_page() }
      }
  }
}
impl PageSink for SubRegionAllocator {
  fn give_page_for_recycle(&mut self, page: Block4KPtr) {
    self.give_page_for_recycle_impl(page)
  }
}
impl PageManager for SubRegionAllocator {}

pub struct SubRegionRef(u64);
impl SubRegionRef {
  pub fn new_null() -> Self {
    SubRegionRef(0)
  }
  pub fn is_null(&self) -> bool {
    self.0 == 0
  }
  pub fn new(
    region_start_addr: *mut u8,
    byte_offset: u16,
  ) -> Self {
    let ptrint = (region_start_addr as u64) << 16;
    let mtded = ptrint + byte_offset as u64;
    return Self(mtded)
  }
  pub fn get_components(&self) -> (*mut (), u16) {
    let mtd = self.0 & (1u64 << 16) - 1;
    let ptr = (self.0 >> 16) as *mut ();
    return (ptr, mtd as u16);
  }
  pub fn deref(&self) -> *mut u8 {
    let (ptr, off) = self.get_components();
    let spot = unsafe { ptr.cast::<u8>().add(off as usize) };
    return spot
  }
}
// it turns out this causes more harm then good
// impl Drop for SubRegionRef {
//   fn drop(&mut self) {
//       panic!(
//         "The lyfecycle of this object cannot be managed implicitly. It must to be manually disposed into any available SubRegionAllocator")
//   }
// }

struct RegionMetadata {
  ref_count: AtomicU16
}


#[test]
fn test_acks_work() { unsafe {
  let mut ralloc = RootAllocator::new();
  let mut sralloc = SubRegionAllocator::new(&mut ralloc);
  let mut boxes: [MaybeUninit<SubRegionRef>; 64] = MaybeUninit::uninit().assume_init();
  let boxess = boxes.as_mut_ptr().cast::<SubRegionRef>();
  for i in 0 ..64-1 {
    let v = sralloc.sralloc(16, 64);
    let ptr = v.deref();
    *ptr.cast() = u16::MAX;
    boxess.add(i).write(v);
  }
  let above = sralloc.sralloc(16, 64); // must cause page replace
  above.deref().cast::<u16>().write(u16::MAX);
  boxess.add(63).write(above);
  for i in 0 .. 64 {
    let item = boxess.add(i).read();
    let val = *item.deref().cast::<u16>();
    assert!(val == u16::MAX);
    sralloc.dispose(item);
  }
} }

struct IOPollingWorker {
  work_group: *mut WorkGroup,
  handle: Option<JoinHandle<()>>,
  out_port: Receiver<IOPollingCallbackData>,
  core_pin_index: CoreId,
}
impl IOPollingWorker {
  fn start(&mut self) {
    if let None = self.handle {
      let this = unsafe { transmute_copy::<_, u64>(&self) };
      self.handle = Some(spawn(move || {
        let this = unsafe { transmute(this) };
        io_polling_routine(this)
      }))
    }
  }
}
struct IOPollingCallbackData {
  task_to_resume: Task,
  target: RawFd,
  readable: bool,
  writeable: bool
}
fn io_polling_routine(this: &mut IOPollingWorker) { unsafe {
  let ok = core_affinity::set_for_current(this.core_pin_index);
  assert!(ok, "failed to pin io thread to core");
  let mut pending_tasks = HashMap::<usize, (Task, RawFd)>::new();
  let poller = Poller::new().unwrap();
  let work_source = &mut this.out_port;
  let mut wait_time = Duration::from_millis(1);
  let mut gathered_events = Vec::new();
  let mut batch_for_resume = Vec::new();
  let mut id = 0usize;
  let mut get_id = || { id = id.wrapping_add(1); return id };
  let work_set = &(*this.work_group).worker_set;
  loop {
    let maybe_some_data = work_source.try_recv();
    match maybe_some_data {
      Ok(data) => {
        let id = get_id();
        pending_tasks.insert(id, (data.task_to_resume, data.target));
        let ev = Event {
          key: id,
          readable: data.readable,
          writable: data.writeable
        };
        poller.add(data.target, ev).unwrap();
      },
      Err(err) => {
        match err {
          std::sync::mpsc::TryRecvError::Disconnected => {
            return
          },
          std::sync::mpsc::TryRecvError::Empty => {

          }
        }
      }
    }
    gathered_events.clear();
    poller.wait(&mut gathered_events, Some(Duration::from_secs(0))).unwrap();
    let no_continuations_to_resume = gathered_events.is_empty();
    if no_continuations_to_resume {
      let should_stop =
        work_set.all_workers_are_idle() &&
        pending_tasks.is_empty() ;
      if should_stop {
        (*work_set.0.get()).io_worker_stopped.store(true, Ordering::Relaxed);
        return
      }
      sleep(wait_time);
      if wait_time <= Duration::from_secs(1) { wait_time *= 2 };
      continue;
    } else {
      wait_time = Duration::from_millis(1)
    }
    for event in &gathered_events {
      let (task, fd) = pending_tasks.remove(&event.key).unwrap();
      poller.delete(fd).unwrap();
      let child_count = &mut*task.frame_ptr.deref().cast::<ChildrenCountTaskMetadataView>();
      let count = child_count.mref_internals().lock_count.fetch_sub(1, Ordering::Relaxed);
      if count == 1 {
        // we should resume this task
        fence(Ordering::Acquire); // syncs thunk invocation as happened at this point
        batch_for_resume.push(task);
      } else {
        // one of child tasks will awake this task
      }
    }
    let no_resume_batch = batch_for_resume.is_empty();
    if !no_resume_batch {
      if let Some(free_worker) = (*this.work_group).worker_set.try_acquire_free_worker_mref() {
        if !free_worker.flags.was_started() { free_worker.start() }
        free_worker.with_synced_access(|worker| {
          let task_set = &mut (*worker.inner_context_ptr.assume_init()).workset;
          while let Some(task) = batch_for_resume.pop() {
            task_set.enque(task)
          }
        });
        batch_for_resume.clear();
      }
      continue;
    }
  }
} }

const ASSUMED_NUMBER_OF_CORES_ON_AVERAGE_MODERN_MACHINE : usize = 16;
struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  inline_workers: [MaybeUninit<Worker>; ASSUMED_NUMBER_OF_CORES_ON_AVERAGE_MODERN_MACHINE],
  outline_workers: Option<Array<Worker>>,
  inline_free_indicies: AtomicU64,
  outline_free_indicies: Option<Array<AtomicU64>>,
  total_worker_count: u32,
  io_worker_stopped: AtomicBool,
  io_thread: IOPollingWorker // sorry :(
}

impl WorkerSet {
  fn inline_free_indicies(&self) -> &AtomicU64 {
    &unsafe { &*self.0.get() }.inline_free_indicies
  }
  fn io_worker_stoped(&self) -> bool {
    unsafe { &*self.0.get() }.io_worker_stopped.load(Ordering::Relaxed)
  }
  fn total_worker_count(&self) -> u32 {
    unsafe { &*self.0.get() }.total_worker_count
  }
  fn mref_worker_at_index(&self, index: u32) -> &mut Worker { unsafe {
    let this = &mut *self.0.get();
    let work_count = this.total_worker_count;
    if index >= work_count { panic!("invalid worker index") }
    if index < work_count {
      let ptr = addr_of_mut!(this.inline_workers).cast::<Worker>();
      let worker = &mut *ptr.add(index as usize );
      return worker
    } else {
      if let Some(w) = &this.outline_workers {
        let worker = w.ref_item_at_index(index as usize - 16).unwrap();
        return worker;
      };
      panic!()
    };
  }; }
  fn set_as_free(&self, index: u32) {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { panic!("invalid worker index") }

    let index_mask = 1u64 << index;
    let mask = !index_mask ;
    // we must see changes to indicies as immidiate thus acqrel
    let _ = this.inline_free_indicies.fetch_and(mask, Ordering::SeqCst);
  }
  // true, if already occupied
  fn set_as_occupied(&self, index: u32) -> bool {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { panic!("invalid index of worker") }

    let mask = 1u64 << index;
    // we mut see changes to indicies as immidiate or
    // some two wokers might end up aquiring third one and
    // that would be pretty bad
    let old = this.inline_free_indicies.fetch_or(mask, Ordering::SeqCst);
    let already_taken = old & mask != 0;
    return already_taken
  }
  fn try_acquire_free_worker_mref(&self) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    let relevance_mask = u64::MAX << this.total_worker_count;
    let mut indicies = this.inline_free_indicies.load(Ordering::SeqCst);
    loop {
      if indicies | relevance_mask == u64::MAX {
        // nothign to grab in inlines
        if let Some(_) = this.outline_workers {
          todo!()
        }
        return None ;
      };
      let some_index = indicies.trailing_ones();
      let index_mask = 1u64 << some_index;
      indicies = this.inline_free_indicies.fetch_or(index_mask, Ordering::SeqCst);
      let did_acquire = indicies & index_mask == 0;
      if !did_acquire { continue; }

      let ptr = this.inline_workers.as_ptr().add(some_index as usize);
      let ptr = ptr.cast::<Worker>() as *mut _;
      let val = &mut *ptr;
      return Some(val)
    }
  } }
  fn all_workers_are_idle(&self) -> bool { unsafe {
    let this = &mut *self.0.get();
    let idle = this.inline_free_indicies.load(Ordering::Relaxed) == 0;
    if idle {
      if let Some(_) = this.outline_free_indicies {
        todo!()
      }
    }
    return idle
  } }
}

struct TaskSet<const LocalCacheCapacity: usize> {
  inline_tasks: InlineLoopBuffer<LocalCacheCapacity, Task>,
  outline_tasks: Array<Task>,
}
impl <const LocalCacheCapacity: usize> TaskSet<LocalCacheCapacity> {
  fn item_count(&self) -> usize {
    let inline = self.inline_tasks.item_count();
    let outline = self.outline_tasks.item_count();
    return inline + outline;
  }
  fn enque(&mut self, new_item: Task) {
    let clone = unsafe { addr_of!(new_item).read() };
    let did_push = self.inline_tasks.push_to_tail(new_item);
    if !(did_push) {
      self.outline_tasks.push(clone)
    } else {
      forget(clone)
    }
  }
  fn deque(&mut self) -> Option<Task> {
    let task = self.inline_tasks.pop_from_head();
    if let None = task {
      let task = self.outline_tasks.pop();
      return task;
    }
    return task
  }
}


struct WorkerFlags(AtomicU8);
impl WorkerFlags {
  fn new() -> Self {
    Self(AtomicU8::new(0))
  }
  const TERMINATION_BIT: u8 = 1 << 0;
  fn mark_for_termination(&self) {
    let _ = self.0.fetch_or(Self::TERMINATION_BIT, Ordering::SeqCst);
  }
  fn is_marked_for_termination(&self) -> bool {
    let flags = self.0.load(Ordering::SeqCst);
    return flags & Self::TERMINATION_BIT != 0;
  }
  const SUSPEND_BIT: u8 = 1 << 1;
  fn mark_for_suspend(&self) {
    let _ = self.0.fetch_or(Self::SUSPEND_BIT, Ordering::Relaxed);
  }
  fn unmark_for_suspend(&self) {
    let _ = self.0.fetch_and(!Self::SUSPEND_BIT, Ordering::Relaxed);
  }
  fn is_marked_for_suspend(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::SUSPEND_BIT != 0
  }
  const CTX_INIT_BIT: u8 = 1 << 2;
  fn mark_as_initialised(&self) {
    let _ = self.0.fetch_or(Self::CTX_INIT_BIT, Ordering::Relaxed);
  }
  fn is_initialised(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::CTX_INIT_BIT != 0
  }
  const FIRST_INIT_BIT: u8 = 1 << 3;
  fn mark_as_started(&self) {
    let _ = self.0.fetch_or(Self::FIRST_INIT_BIT, Ordering::Relaxed);
  }
  fn was_started(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::FIRST_INIT_BIT != 0;
  }
  const WORK_SUBMITED_BIT: u8 = 1 << 4;
  fn mark_first_work_as_submited(&self) {
    let _ = self.0.fetch_or(Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn unmark_work_as_submited(&self) {
    let _ = self.0.fetch_and(!Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn is_first_work_submited(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::WORK_SUBMITED_BIT != 0
  }
  const TRANSACTION_BEGAN_BIT: u8 = 1 << 5;
  fn mark_transaction_begin(&self) {
    let _ = self.0.fetch_or(Self::TRANSACTION_BEGAN_BIT, Ordering::Relaxed);
  }
  const TRANSACTION_ENDED_BIT:u8 = 1 << 6;
  fn mark_transaction_ended(&self) {
    let _ = self.0.fetch_or(Self::TRANSACTION_ENDED_BIT, Ordering::Relaxed);
  }
  fn has_transaction_began(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::TRANSACTION_BEGAN_BIT != 0
  }
  fn has_trunsaction_ended(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::TRANSACTION_ENDED_BIT != 0
  }
  fn clear_transaction_bits(&self) {
    let clear_mask = Self::TRANSACTION_BEGAN_BIT | Self::TRANSACTION_ENDED_BIT;
    let _ = self.0.fetch_and(!clear_mask, Ordering::Relaxed);
  }
}

struct Worker {
  runner_handle: Option<JoinHandle<()>>,
  work_group: *mut WorkGroup,
  inner_context_ptr: MaybeUninit<*mut CommonWorkerInnerContext>,
  index: u32,
  flags: WorkerFlags,
  core_pin_id: core_affinity::CoreId,
  io_tasks_sink: Sender<IOPollingCallbackData>
}
impl Worker {
  // false if already occupied
  fn mark_as_occupied(&self) -> bool { unsafe {
    (*self.work_group).worker_set.set_as_occupied(self.index)
  } }
  fn mark_as_free(&self) {
    unsafe{(*self.work_group).worker_set.set_as_free(self.index)}
  }
  fn wakeup(&self) {
    if let Some(thread) = &self.runner_handle {
      thread.thread().unpark();
    };
  }
  fn start(&mut self) { unsafe {
    let init_bit = WorkerFlags::FIRST_INIT_BIT;
    let prior = self.flags.0.fetch_or(init_bit, Ordering::AcqRel);
    if prior & init_bit != 0 {
      panic!("attempt to reinit worker")
    }
    let _ = self.mark_as_occupied();
    if let None = self.runner_handle {
      let copy = transmute_copy::<_, u64>(&self);
      let thread = thread::spawn(move ||{
        let ptr = transmute::<_, &mut Worker>(copy);
        worker_processing_routine(ptr);
      });
      self.runner_handle = Some(thread);
    }
  } }
  fn terminate(&mut self) {
    with_scoped_consume(&mut self.runner_handle, |g| {
      let v = g.consume();
      if let Some(thread) = v {
        let () = thread.join().unwrap();
        g.recover(None);
      } else {
        g.recover(v)
      };
    });
  }
  fn with_synced_access(&mut self, action: impl FnOnce(&mut Self)) {
    let was_started = self.flags.was_started();
    assert!(was_started, "cannot acccess context of a worker that was not started");
    while !self.flags.is_initialised() {}
    fence(Ordering::Acquire);
    if self.flags.is_first_work_submited() {
      self.flags.mark_transaction_begin();
      action(self);
      fence(Ordering::Release);
      self.flags.mark_transaction_ended();
      self.wakeup();
    } else {
      action(self);
      fence(Ordering::Release);
      self.flags.mark_first_work_as_submited()
    }
  }
}

// this thing is created with intention to
// metigate the situation when local objects contain
// too many stale pages. We ask those objects to give away pages
// they dont use and put them to use somewhere else.
struct PageRerouter<const Capacity:usize> {
  subscribed_donors: InlineLoopBuffer<Capacity, *mut dyn PageSource>,
  ralloc: *mut RootAllocator
}
impl <const Capacity:usize> PageRerouter<Capacity> {
  fn new(ralloc: *mut RootAllocator) -> Self {
    Self { subscribed_donors: InlineLoopBuffer::new(), ralloc }
  }
  fn register(&mut self, new_donor: *mut dyn PageSource) {
    let ok = self.subscribed_donors.push_to_tail(new_donor);
    assert!(ok);
  }
  fn get_page(&mut self) -> Block4KPtr { unsafe {
    let mut iter = LoopBufferTraverser::new(&self.subscribed_donors);
    loop {
      let maybe_donor = iter.next();
      if let Some(donor) = maybe_donor {
        let maybe_page = (&mut **donor).try_drain_page();
        if let Some(page) = maybe_page {
          return page
        }
      } else {
        let page = (&mut *self.ralloc).get_block();
        return page
      };
    }
  }; }
}
impl <const Capacity:usize> PageSource for PageRerouter<Capacity> {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      Some(self.get_page())
  }
}

struct AcquiredIsolates {
  index: usize,
  storage: Vec<SomeIsolateRef>
}
impl AcquiredIsolates {
  fn add(&mut self, iso_ref:SomeIsolateRef) {
    self.storage.push(iso_ref)
  }
  fn remove_at_index(&mut self, index:usize) {
    let _ = self.storage.swap_remove(index);
    if self.index != 0 { self.index -= 1 }
  }
  fn get_next_pending_index(&mut self) -> Option<usize> {
    let count = self.storage.len();
    if count == 0 { return None }
    let return_index = self.index;
    self.index += 1;
    if self.index == count { self.index = 0 }
    return Some(return_index)
  }
}

type CommonWorkerInnerContext = WorkerInnerContext<4, TASK_CACHE_SIZE>;
struct WorkerInnerContext<const S0:usize, const S1:usize> {
  page_router: PageRerouter<S0>,
  allocator: SubRegionAllocator,
  workset: TaskSet<S1>,
  acquired_isolates: AcquiredIsolates,
}

const TASK_CACHE_SIZE:usize = 16;

fn worker_processing_routine(worker: &mut Worker) { unsafe {
  let ok = core_affinity::set_for_current(worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", worker.index, worker.core_pin_id);
  let ralloc = addr_of_mut!((&mut *worker.work_group).ralloc);
  let mut inner_context = {
    let mut ctx: CommonWorkerInnerContext = garbage!();
    let router_ptr = addr_of_mut!(ctx.page_router);
    router_ptr.write(PageRerouter::<4>::new(ralloc));
    addr_of_mut!(ctx.allocator).write(SubRegionAllocator::new(router_ptr));
    addr_of_mut!(ctx.workset).write(TaskSet::<TASK_CACHE_SIZE>{
      inline_tasks:InlineLoopBuffer::new(),
      outline_tasks: Array::new(router_ptr)
    });
    addr_of_mut!(ctx.acquired_isolates).write(
      AcquiredIsolates { index: 0, storage: Vec::new() });
    ctx.page_router.register(&mut ctx.workset.outline_tasks);
    ctx
  };
  worker.inner_context_ptr.write(addr_of_mut!(inner_context));
  fence(Ordering::Release); // publish context init to the consumer
  worker.flags.mark_as_initialised();

  while !worker.flags.is_first_work_submited() {}
  fence(Ordering::Acquire);

  let workset_ = addr_of_mut!(inner_context.workset);
  let task_context = TaskContext::new(&mut inner_context, worker.work_group);
  let task_context_ref = &mut *task_context.0.get();
  let mut immidiate_state = ImmidiateState {
    spawned_subtask_count: 0,
    slot_for_dormant_parent_task: null_mut(),
    region_ref: MaybeUninit::uninit(),
    current_task: garbage!()
  };
  task_context_ref.immidiate_state = addr_of_mut!(immidiate_state);

  let mut index = None;
  'quantum:loop {
    if let Some(task) = (*workset_).deque() {
      immidiate_state.current_task = task;
    } else {
      if let i@Some(_) = inner_context.acquired_isolates.get_next_pending_index() {
        index = i;
      } else {
        // not queue has any work to be done nor isolates has any work to offer.
        // try go dormant
        let selfkill = suspend(&worker);
        if selfkill {
          return; // goodbye sweet prince
        }
        continue;
      }
    }
    let mut current_thunk = immidiate_state.current_task.action.project_fun_ptr();
    'local_work:loop {
      let continuation = {
        if let Some(index_) = index {
          index = None;
          immidiate_state.current_task = Task {
            action:Action::new_null(), frame_ptr:SubRegionRef::new_null()};
          let iso_ref = inner_context.acquired_isolates.storage.get_unchecked(index_);
          let (reg, off) = iso_ref.0.get_components();
          let iso_ptr = reg.cast::<u8>().add(off as usize);
          let meta = &*iso_ptr.cast::<IsolateMetadata>();
          let val = meta.send_method_impl.fetch_or(
            IsolateMetadata::BEING_PROCESSED_BIT, Ordering::Relaxed);
          let being_handled = val & IsolateMetadata::BEING_PROCESSED_BIT != 0;
          if being_handled { continue 'quantum }
          fence(Ordering::Acquire);
          let data_offset = meta.offset_to_data();
          let data_ptr = iso_ptr.add(data_offset).cast();
          let resolver = transmute::<_, UniversalMsgRespondSig>(meta.respond_method_impl);
          let maybe_cont = resolver(data_ptr, &task_context);
          let _ = meta.send_method_impl.fetch_and(
            !IsolateMetadata::BEING_PROCESSED_BIT, Ordering::Release);
          let cont = if let Some(cont) = maybe_cont { cont } else {
            let ilc = meta.liveness_count.load(Ordering::Relaxed);
            if ilc == 1 { // we are the last observer of this isolate
              (meta.destructor)(data_ptr);
              inner_context.allocator.dispose(transmute_copy(&iso_ref.0));
              inner_context.acquired_isolates.remove_at_index(index_);
            };
            continue 'quantum;
          };
          cont
        } else {
          let cont = current_thunk(&task_context);
          fence(Ordering::Release);
          // we want to see all thunk invocations as happened
          // when we'll read the subtasks lock count as 0.
          // not nescessarily in global order relative to each other
          // but in the global order relative to the worker
          // reading 0 on child task count
          cont
        }
      };
      let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
      match (continuation, produced_subtasks) {
        (Continuation::Await(fd, r, w, next), _) => {
          immidiate_state.current_task.action.set_fun_ptr(next);
          if immidiate_state.current_task.frame_ptr.is_null() {
            immidiate_state.current_task.frame_ptr = inner_context.allocator.sralloc(
              size_of::<ChildrenCountTaskMetadataView>(), align_of::<ChildrenCountTaskMetadataView>());
          };
          immidiate_state.spawned_subtask_count += 1;
          (*immidiate_state.current_task.frame_ptr.deref().cast::<ChildrenCountTaskMetadataView>())
            .mref_internals().lock_count = AtomicU64::new(
              immidiate_state.spawned_subtask_count);
          if produced_subtasks {
            *immidiate_state.slot_for_dormant_parent_task =
              transmute_copy(&immidiate_state.current_task);
          }

          let item = IOPollingCallbackData {
            task_to_resume: transmute_copy(&immidiate_state.current_task),
            target: fd, readable: r, writeable: w
          };
          worker.io_tasks_sink.send(item).unwrap();
          task_context.clear_dirty_state();
          continue 'quantum;
        },
        (Continuation::Then(next_thunk), false) => {
          // task need not await its children.
          // or do pretty much anything fancy
          current_thunk = next_thunk;
          continue 'local_work;
        },
        (Continuation::Then(next_thunk), true) => {
          // this task has been parked and last child
          // will put it back in action
          immidiate_state.current_task.action.set_fun_ptr(next_thunk);
          // set lock count
          if immidiate_state.current_task.frame_ptr.is_null() {
            immidiate_state.current_task.frame_ptr = inner_context.allocator.sralloc(
              size_of::<ChildrenCountTaskMetadataView>(), align_of::<ChildrenCountTaskMetadataView>());
          };
          (*immidiate_state.current_task.frame_ptr.deref().cast::<ChildrenCountTaskMetadataView>()).mref_internals().lock_count = AtomicU64::new(immidiate_state.spawned_subtask_count);
          *immidiate_state.slot_for_dormant_parent_task =
            transmute_copy(&immidiate_state.current_task);
          task_context.clear_dirty_state();
          schedule_work(worker, workset_);
          continue 'quantum;
        },
        (Continuation::Done, true) => {
          // last child is responsible for frame of the parrent
          immidiate_state.current_task.action.mref_flags().mark_as_dead();
          // set lock count
          if immidiate_state.current_task.frame_ptr.is_null() {
            immidiate_state.current_task.frame_ptr = inner_context.allocator.sralloc(
              size_of::<ChildrenCountTaskMetadataView>(), align_of::<ChildrenCountTaskMetadataView>());
          };
          (*immidiate_state.current_task.frame_ptr.deref().cast::<ChildrenCountTaskMetadataView>()).mref_internals().lock_count = AtomicU64::new(immidiate_state.spawned_subtask_count);
          *immidiate_state.slot_for_dormant_parent_task =
            transmute_copy(&immidiate_state.current_task);
          task_context.clear_dirty_state();
          schedule_work(worker, workset_);
          continue 'quantum;
        },
        (Continuation::Done, false) => {
          // this is a terminal step
          let should_drop_lock_count =
            immidiate_state.current_task.action.mref_flags().is_parent_waker();
          let current_frame_delete: SubRegionRef =
            transmute_copy(&immidiate_state.current_task.frame_ptr);
          if should_drop_lock_count {
            let frame_ptr = current_frame_delete.deref();
            let mtd = &*frame_ptr.cast::<ParentedTaskMetadataView>();
            let parked_parent_slot = addr_of!(mtd.mref_internals().parent_task_ref).read();
            let parent_task = parked_parent_slot.deref().cast::<Task>().read();
            let parent_frame = parent_task.frame_ptr.deref();
            let parent_mtd = &*parent_frame.cast::<ParentedTaskMetadataView>();
            let lock_count = parent_mtd.mref_internals().lock_count.fetch_sub(
              1, Ordering::Relaxed);
            let last_child = lock_count == 1;
            let parent_dead = parent_task.action.mref_flags().is_dead();
            match (last_child, parent_dead) {
              (true, true) => {
                // this syncs on subtask count. thunk exec in each subtask
                // does not happen after the counter bump down, so the last task
                // which sets it to 0, will never happen before any other sibling subtask.
                // all uses of parent frame by subtasks will not cross this barier
                fence(Ordering::Acquire);
                inner_context.allocator.dispose(parked_parent_slot);
                inner_context.allocator.dispose(current_frame_delete);
                inner_context.allocator.dispose(parent_task.frame_ptr);
                continue 'quantum;
              },
              (true, false) => {
                fence(Ordering::Acquire); // same as above holds for this one
                inner_context.allocator.dispose(current_frame_delete);
                inner_context.allocator.dispose(parked_parent_slot);
                immidiate_state.current_task = parent_task;
                current_thunk = immidiate_state.current_task.action.project_fun_ptr();
                continue 'local_work;
              },
              (false, _) => {
                // this child only has to put its frame mem for recycle
                inner_context.allocator.dispose(current_frame_delete);
                continue 'quantum
              }
            }
          } else {
            // we dont have a parrent to carry about
            if !current_frame_delete.is_null() {
              inner_context.allocator.dispose(current_frame_delete);
            }
            continue 'quantum;
          }
        },
      }
    }
  }
} }

fn suspend(worker: &Worker) -> bool {
  worker.mark_as_free();
  let self_kill = loop {
    if worker.flags.is_marked_for_termination() {
      break true
    };
    if worker.flags.has_transaction_began() {
      while !worker.flags.has_trunsaction_ended() {}
      fence(Ordering::Acquire);
      worker.flags.clear_transaction_bits();
      break false;
    }
    park();
  };
  return self_kill
}

fn schedule_work<const C:usize>(
  worker: *mut Worker, workset: *mut TaskSet<C>
) { unsafe {
  let workset = &mut *workset;
  let worker_set = &mut(*(*worker).work_group).worker_set;
  // todo: use task weight metric
  loop {
    let local_item_count = workset.item_count();
    let have_too_many_tasks = local_item_count > TASK_CACHE_SIZE;
    if have_too_many_tasks {
      let maybe_free_worker = worker_set.try_acquire_free_worker_mref();
      match maybe_free_worker {
        Some(subordinate_worker) => {
          if !subordinate_worker.flags.was_started() {
            subordinate_worker.start()
          }
          subordinate_worker.with_synced_access(|subordinate_worker|{
            let src = &mut(&mut *((&mut *worker).inner_context_ptr).assume_init_read()).workset;
            let dest = &mut (*subordinate_worker.inner_context_ptr.assume_init()).workset;
            // todo: make transfers fast
            let mut task_limit = 0;
            loop {
              if let Some(task) = src.deque() {
                dest.enque(task);
                task_limit += 1;
                if task_limit == TASK_CACHE_SIZE { return }
              } else {
                return
              }
            }
          });
          continue;
        },
        None => {
          return
        }
      }
    } else {
      return
    }
  }
} }

struct ParentedTaskMetadataView(UnsafeCell<ParentedTaskMetadataViewInternals>);
impl ParentedTaskMetadataView {
  fn mref_internals(&self) -> &mut ParentedTaskMetadataViewInternals {
    unsafe { &mut *self.0.get() }
  }
}
#[repr(C)]
struct ParentedTaskMetadataViewInternals {
  lock_count: AtomicU64,
  parent_task_ref: SubRegionRef
}
struct ChildrenCountTaskMetadataView(UnsafeCell<ChildrenCountTaskMetadataViewInternals>);
impl ChildrenCountTaskMetadataView {
  fn mref_internals(&self) -> &mut ChildrenCountTaskMetadataViewInternals {
    unsafe { &mut *self.0.get() }
  }
}
#[repr(C)]
struct ChildrenCountTaskMetadataViewInternals {
  lock_count: AtomicU64,
}
pub struct Arc<T> { ref_count:AtomicU64, value:T }
pub struct ArcBox<T>(SubRegionRef, PhantomData<T>);
pub struct BasicBox<T>(SubRegionRef, PhantomData<T>);
impl <T>ArcBox<T> {
  fn as_mut_ptr(&mut self) -> *mut T { unsafe {
    let val = &mut *self.0.deref().cast::<Arc<T>>();
    return addr_of_mut!(val.value)
  } }
}
impl <T> AsMut<T> for ArcBox<T> {
  fn as_mut(&mut self) -> &mut T {
    unsafe { &mut*self.as_mut_ptr() }
  }
}
impl <T> AsRef<T> for ArcBox<T> {
  fn as_ref(&self) -> &T { unsafe {
    let val = &*self.0.deref().cast::<Arc<T>>();
    return &val.value
  } }
}

struct ImmidiateState {
  current_task: Task,
  spawned_subtask_count: u64,
  slot_for_dormant_parent_task: *mut Task,
  region_ref: MaybeUninit<SubRegionRef>,
}
pub struct TaskContext(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  immidiate_state: *mut ImmidiateState,
  worker_inner_context_ref: *mut CommonWorkerInnerContext,
  work_group_ref: *mut WorkGroup,
}
enum MsgStore {
  Immidiate([u8;15]), Indirect(*mut u8)
}
pub trait PageSink {
  fn give_page_for_recycle(&mut self, page: Block4KPtr);
}
pub trait PageManager: PageSource + PageSink {}
impl TaskContext {
  fn new(
    worker_inner_context: *mut CommonWorkerInnerContext,
    worker_group_ref: *mut WorkGroup
  ) -> Self {
    TaskContext(UnsafeCell::new(TaskContextInternals {
      immidiate_state: null_mut(),
      work_group_ref: worker_group_ref,
      worker_inner_context_ref: worker_inner_context,
    }))
  }
  // false if fails
  fn try_acustody_isolate(&self, iso_ref: SomeIsolateRef) -> bool { unsafe {
    let this = &mut *self.0.get();
    let maybe_worker = (*this.work_group_ref).worker_set.try_acquire_free_worker_mref();
    if let Some(worker) = maybe_worker {
      if !worker.flags.was_started() {
        worker.start()
      }
      worker.with_synced_access(|worker| {
        (*worker.inner_context_ptr.assume_init()).acquired_isolates.add(iso_ref)
      });
      return true
    } else {
      return false
    }
  }; }
  pub fn get_page_provider(&self) -> &mut dyn PageManager { unsafe {
    let this = &mut *self.0.get();
    &mut (*this.worker_inner_context_ref).allocator
  } }
  pub fn install_task_frame<T>(&self) { unsafe {
    let this = &mut *self.0.get();
    let fptr = &mut (*this.immidiate_state).current_task.frame_ptr;
    assert!(fptr.is_null(), "task already has a frame");
    let flags = (*this.immidiate_state).current_task.action.mref_flags();
    flags.set_offset_order(align_of::<T>() as u8);
    let mut frame_size = size_of::<ChildrenCountTaskMetadataView>();
    frame_size += offset_to_higher_multiple(frame_size as u64, align_of::<T>()) as usize;
    frame_size += size_of::<T>();
    let reg_ref = (*this.worker_inner_context_ref).allocator.sralloc(
      frame_size, align_of::<ChildrenCountTaskMetadataView>());
    *fptr = reg_ref;
  } }
  pub fn access_task_frame<T>(&self) -> *mut T { unsafe {
    let this = &mut *self.0.get();
    let task = &(*this.immidiate_state).current_task;
    let offset = task.action.byte_offset_to_data();
    let data_offset = task.frame_ptr.deref().add(offset);
    return data_offset.cast()
  }; }
  // does not need destructor
  pub fn spawn_basic_box<T>(&self, data:T) -> BasicBox<T> { unsafe {
    assert!(!needs_drop::<T>(), "detected value with nontrivial destructor");
    if size_of::<T>() == 0 {
      return BasicBox(SubRegionRef::new_null(), PhantomData)
    }
    let this = &mut *self.0.get();
    let region_ref = (*this.worker_inner_context_ref).allocator.sralloc(
      size_of::<T>(), align_of::<T>());
    let loc = region_ref.deref();
    loc.cast::<T>().write(data);
    return BasicBox(region_ref, PhantomData)
  } }
  pub fn dispose_basic_box<T>(&self, some_box: BasicBox<T>) { unsafe {
    let this = &mut *self.0.get();
    (*this.worker_inner_context_ref).allocator.dispose(some_box.0)
  } }
  pub fn spawn_rc_box<T>(&self, data:T) -> ArcBox<T> { unsafe {
    assert!(needs_drop::<T>(), "value must provide a destructor");
    let this = &mut *self.0.get();
    let region_ref = (*this.worker_inner_context_ref).allocator.sralloc(
      size_of::<Arc<T>>(), align_of::<Arc<T>>());
    let loc = region_ref.deref();
    let box_ = loc.cast::<Arc<T>>();
    (*box_).ref_count = AtomicU64::new(1);
    addr_of_mut!((*box_).value).write(data);
    return ArcBox(region_ref, PhantomData)
  }; }
  pub fn dispose_rc_box<T>(&self, some_box: ArcBox<T>) { unsafe {
    let val = &*some_box.0.deref().cast::<Arc<T>>();
    let rc = val.ref_count.fetch_sub(1, Ordering::AcqRel);
    if rc == 1 {
      let this = &mut *self.0.get();
      (*this.worker_inner_context_ref).allocator.dispose(some_box.0)
    }
  } }
  // #[inline(never)]
  // fn send_message_common_impl(
  //   &self,
  //   meta_ref: &IsolateMetadata,
  //   data_ptr: *mut u8) {

  // }
  pub fn send_message<T:Isolate>(
    &self,
    reciever: &IsolateRef<T>,
    message: T::Message,
  ) -> T::MsgSendOutcome { unsafe {
    let iso_ptr = reciever.0.deref();
    let iso_meta = &*iso_ptr.cast::<IsolateMetadata>();
    let mut send_impl_ptr ;
    let mut smth ;
    loop {
      smth = iso_meta.send_method_impl.fetch_or(
        IsolateMetadata::OWNERSHIP_BIT , Ordering::AcqRel);
      send_impl_ptr = smth & ((1 << 48) - 1);
      if send_impl_ptr == 0 { continue; }
      break;
    }
    let send = transmute::<_, UniversalMsgSendSig<T::MsgSendOutcome, T::Message>>(send_impl_ptr);

    let mut offset = size_of::<IsolateMetadata>();
    offset += offset_to_higher_multiple(offset as u64, align_of::<T>()) as usize;
    let iso_data = iso_ptr.add(offset);
    let send_outcome = send(
      iso_data.cast(),
      self,
      message);

    let idle = smth & IsolateMetadata::BEING_PROCESSED_BIT == 0;
    let this = &mut *self.0.get();
    if idle {

    }

    let orphan = smth & IsolateMetadata::OWNERSHIP_BIT == 0;
    if orphan {
      let copied = reciever.copy_ref().erase_to_some();
      let copy : SomeIsolateRef = transmute_copy(&copied);
      // lets try to give this iso to an idle worker
      let ok = self.try_acustody_isolate(copy);
      if !ok {
        // there were no available workers.
        // we take this isolate
        let copy = transmute_copy(&copied);
        (*this.worker_inner_context_ref).acquired_isolates.add(copy);
      }
    }
    return send_outcome
  } }
  pub fn spawn_isolate<T: Isolate>(&self, isolate: T) -> IsolateRef<T> {unsafe {
    let this = &mut *self.0.get();
    let mut data_dist = size_of::<IsolateMetadata>();
    data_dist += offset_to_higher_multiple(data_dist as u64, align_of::<T>()) as usize;
    let whole_size = data_dist + size_of::<T>();
    let item = (*this.worker_inner_context_ref).allocator.sralloc(
      whole_size, align_of::<IsolateMetadata>());
    let raw = item.deref();
    let meta = &mut *raw.cast::<IsolateMetadata>();
    meta.respond_method_impl = T::respond_to_message as *mut () as u64;
    meta.send_method_impl.store(0, Ordering::Relaxed);
    meta.set_data_align_order(align_of::<T>());
    meta.liveness_count = AtomicU64::new(1);
    meta.destructor = transmute(drop_in_place::<T> as *mut ());
    let data_ptr = raw.add(data_dist);
    data_ptr.cast::<T>().write(isolate);
    meta.send_method_impl.fetch_or(T::send_message as *mut () as u64, Ordering::Release);

    return IsolateRef(item, PhantomData)
  } }
  pub fn dispose_isolate<T:Isolate>(&self, iso_ref: IsolateRef<T>) { unsafe {
    let (reg, off) = iso_ref.0.get_components();
    let iso_ptr = reg.cast::<u8>().add(off as usize);
    let meta = &*iso_ptr.cast::<IsolateMetadata>();
    let lc = meta.liveness_count.fetch_sub(1, Ordering::AcqRel);
    if lc == 1 {
      let data = iso_ptr.add(meta.offset_to_data());
      (meta.destructor)(data.cast());
      let this = &mut *self.0.get();
      (*this.worker_inner_context_ref).allocator.dispose(iso_ref.0);
    }
  } }
  // parents never get ahead of their children in the execution timeline.
  // subtasks are never parentless
  pub fn spawn_subtask<T: Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<u8>(),
      size_of::<T>(), align_of::<T>(), thunk, false);
    forget(env)
  }
  // parent does not depend on this subtask
  pub fn spawn_detached_task<T:Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<u8>(),
      size_of::<T>(), align_of::<T>(), thunk, true);
    forget(env)
  }
  #[inline(never)]
  fn spawn_task_common_impl(
    &self,
    env_ptr:*const u8, env_size:usize, env_align:usize,
    thunk: Thunk, detached: bool
  ) { unsafe {
    let this = &mut *self.0.get();
    let immidiate_state_ref = &mut *this.immidiate_state;
    let frame_size = if detached {
      size_of::<ChildrenCountTaskMetadataView>()
    } else {
      size_of::<ParentedTaskMetadataView>()
    };
    if !detached {
      self.idempotently_aquire_parking_lot_for_parent_task();
      immidiate_state_ref.spawned_subtask_count += 1;
    }
    let (real_frame_size, offset_order) =
      adjusted_frame_size(env_size, env_align, frame_size);
    let frame_ref = if env_size != 0 || !detached {
      let frame_allocation_limit = 4096 - size_of::<RegionMetadata>();
      if real_frame_size >= frame_allocation_limit {
        panic!("FIXME:Cant allocate this much for a task frame.")
      }
      let sralloc = &mut (*this.worker_inner_context_ref).allocator;
      let frame_ref = sralloc.sralloc(real_frame_size, align_of::<ParentedTaskMetadataView>());
      let frame_ptr = frame_ref.deref();
      let mtd = (*frame_ptr.cast::<ChildrenCountTaskMetadataView>()).mref_internals();
      mtd.lock_count = AtomicU64::new(0);
      if !detached {
        let mtd = (&mut *frame_ptr.cast::<ParentedTaskMetadataView>()).mref_internals();
        mtd.parent_task_ref = immidiate_state_ref.region_ref.assume_init_read();
      }
      let offset_to_data = renorm_offset_order(offset_order);
      let data = frame_ptr.add(offset_to_data);
      copy_nonoverlapping(env_ptr, data, env_size);
      frame_ref
    } else {
      SubRegionRef::new_null()
    };
    let subtask = Task {action:Action::new(thunk), frame_ptr: frame_ref};
    subtask.action.mref_flags().set_offset_order(offset_order as u8);
    if !detached {
      subtask.action.mref_flags().mark_as_parent_waker();
    }
    let task_set = &mut (*this.worker_inner_context_ref).workset;
    task_set.enque(subtask);
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
    imm_ctx.slot_for_dormant_parent_task = null_mut();
  }
  fn idempotently_aquire_parking_lot_for_parent_task(&self) { unsafe {
    let this = &mut *self.0.get() ;
    let imm_ctx = &mut *this.immidiate_state;
    if imm_ctx.slot_for_dormant_parent_task == null_mut() {
      let srallocator = &mut (*this.worker_inner_context_ref).allocator;
      let slot = srallocator.sralloc(size_of::<Task>(), align_of::<Task>());
      let parked_task_ptr = slot.deref().cast::<Task>();
      imm_ctx.slot_for_dormant_parent_task = parked_task_ptr;
      imm_ctx.region_ref.as_mut_ptr().write(slot);
    }
  } }
  pub fn reschedule_this_thunk(&self) {
    todo!()
  }
}
// (real_frame_size, offset_order)
fn adjusted_frame_size(env_size: usize, env_align:usize, mtd_size: usize) -> (usize, usize) { unsafe {
  // assert!(mtd_size != 0);
  let mut adjusted_size : *mut u8 = null_mut();
  adjusted_size = adjusted_size.add(mtd_size);
  let off = ptr_align_dist(adjusted_size, env_align);
  adjusted_size = adjusted_size.add(off as usize);
  let mut order = adjusted_size as usize >> 3;
  if order > 0 {
    order = 64usize - (order - 1).leading_zeros() as usize ;
  }
  let real_size = renorm_offset_order(order) + env_size;

  assert!(order <= (1 << 3) - 1);
  return (real_size, order)
} }
fn renorm_offset_order(offset_order: usize) -> usize {
  (1 << 3) << offset_order
}

struct TaskFlags([u8;2]);
impl TaskFlags {
  fn new() -> Self {
    Self([0;2])
  }
  // fn mark_as_terminator(&mut self) {
  //   self.0[0] |= 1 << 0
  // }
  // fn is_terminator(&self) -> bool {
  //   self.0[0] & (1 << 0) != 0
  // }
  fn mark_as_parent_waker(&mut self) {
    self.0[0] |= 1 << 1
  }
  fn is_parent_waker(&self) -> bool {
    self.0[0] & (1 << 1) != 0
  }
  fn mark_as_dead(&mut self) {
    self.0[0] |= 1 << 2
  }
  fn is_dead(&self) -> bool {
    self.0[0] & (1 << 2) != 0
  }
  fn set_offset_order(&mut self, order:u8) {
    assert!(order < (1 << 4) - 1);
    let off = order << 5;
    let transplanted = self.0[1] & (1u8 << 5) - 1;
    let combined = off | transplanted;
    self.0[1] = combined;
  }
  fn get_offset_order_of_frame(&self) -> u8 {
    let off = 0b111 << 5;
    let proj = self.0[1] & off;
    let projnorm = proj >> 5;
    return projnorm
  }
}

pub enum Continuation {
  Done,
  Then(Thunk),
  Await(RawFd, bool, bool, Thunk)
}
impl Continuation {
  pub fn wait_on(
    obj: impl Source,
    watch_readability: bool,
    watch_writeability:bool,
    continuation: Thunk
  ) -> Self {
    let desc = obj.raw();
    Self::Await(desc, watch_readability, watch_writeability, continuation)
  }
}
type Thunk = fn (&TaskContext) -> Continuation;
struct Action(UnsafeCell<ActionInternals>);
#[repr(align(8))]
struct ActionInternals([u8;6],[u8;2]);
impl Action {
  fn new_null() -> Self { cast!(0u64, _) }
  fn project_internals(&self) -> &mut ActionInternals {
    unsafe { &mut *self.0.get() }
  }
  fn new(fun_ptr: Thunk) -> Self { unsafe {
    let mut ptr: [u8;6] = garbage!();
    let mut flags: [u8;2] = garbage!();
    let intptr = fun_ptr as u64;
    copy_nonoverlapping(addr_of!(intptr) as *const u8, addr_of_mut!(ptr) as *mut u8, 6);
    *cast!(&mut flags, &mut TaskFlags) = TaskFlags::new();
    return Self(UnsafeCell::new(ActionInternals(ptr, flags)))
  } }
  fn project_fun_ptr(&self) -> Thunk {
    let mut ptr = 0u64;
    let ugh = addr_of!(unsafe { &*self.0.get() }.0) as *mut u8;
    unsafe { copy_nonoverlapping(ugh, addr_of_mut!(ptr) as *mut u8, 6) };
    return cast!(ptr, Thunk);
  }
  fn mref_flags(&self) -> &mut TaskFlags {
    unsafe { &mut *(*self.0.get()).1.as_mut_ptr().cast::<TaskFlags>() }
  }
  fn set_fun_ptr(&mut self, fun_ptr: Thunk) { unsafe {
    let ptr = (*self.0.get()).0.as_mut_ptr() ;
    let intptr = fun_ptr as u64;
    copy_nonoverlapping(addr_of!(intptr) as *mut u8, ptr, 6);
  } }
  fn byte_offset_to_data(&self) -> usize {
    let f = self.mref_flags();
    let mut off = if f.is_parent_waker() {
      size_of::<ParentedTaskMetadataView>()
    } else {
      size_of::<ChildrenCountTaskMetadataView>()
    };
    off += offset_to_higher_multiple(off as u64, 1usize << f.get_offset_order_of_frame()) as usize;
    return off
  }
}

fn example(ctx: &TaskContext) -> Continuation { Continuation::Then(example) }
#[test]
fn action_is_not_bullshit() {
  let a = Action::new(example);
  let fptr = a.project_fun_ptr();
  assert!(fptr as u64 == example as u64)
}

struct Task {
  action: Action,
  frame_ptr: SubRegionRef
}
struct FramePtr(SubRegionRef);
impl FramePtr {

}

pub struct WorkGroup {
  ralloc: RootAllocator,
  worker_set: WorkerSet,
}

impl WorkGroup {
  pub fn new<T: Sync + Send>(env: T, head: Thunk) -> Box<Self> { unsafe {
    let core_ids = core_affinity::get_core_ids().unwrap_or_else(||{
      panic!("cannot retrieve core indicies")
    });
    let total_core_count = core_ids.len();
    if total_core_count > 64 {
      panic!("fixme: write impls for some stuff here and there")
    }
    let (worker_count, io_core_pin) = {
      let last = core_ids.last().unwrap().clone();
      if total_core_count == 1 { (total_core_count, last) }
      else {
        let count = total_core_count - 1;
        (count, last)
      }
    };
    let boxed = alloc(
      Layout::from_size_align_unchecked(size_of::<Self>(), align_of::<Self>()));
    let boxed = boxed.cast::<Self>();
    let (send, recv) = channel();
    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        inline_workers:MaybeUninit::uninit().assume_init(),
        outline_workers: None,
        inline_free_indicies: AtomicU64::new(0),
        outline_free_indicies: None,
        total_worker_count: worker_count as u32,
        io_thread: IOPollingWorker {
          work_group: boxed,
          handle: None,
          out_port: recv,
          core_pin_index: io_core_pin,
        },
        io_worker_stopped: AtomicBool::new(false)
      })),
    });
    for wix in 0 .. worker_count as u32 {
      let wref = (*boxed).worker_set.mref_worker_at_index(wix);
      let pin = core_ids.get(wix as usize).unwrap().clone();
      let worker = Worker {
        index: wix,
        runner_handle: None,
        work_group: boxed,
        flags: WorkerFlags::new(),
        inner_context_ptr: MaybeUninit::uninit(),
        core_pin_id: pin,
        io_tasks_sink: send.clone()
      };
      cast!(wref, *mut Worker).write(worker);
    }
    let initiator = (*boxed).worker_set.mref_worker_at_index(0);
    initiator.start();
    initiator.with_synced_access(|worker|{
      let ctx = &mut *worker.inner_context_ptr.assume_init();
      let mut initial_task = garbage!(Task);
      initial_task.frame_ptr = if size_of::<T>() != 0 {
        let mut size = size_of::<ChildrenCountTaskMetadataView>();
        size += offset_to_higher_multiple(size as u64, align_of::<T>()) as usize;
        let dist_to_data = size;
        size += size_of::<T>();
        let frame = ctx.allocator.sralloc(
          size, align_of::<ChildrenCountTaskMetadataView>());
        let task_slot = frame.deref();
        let task_meta = &*task_slot.cast::<ChildrenCountTaskMetadataView>();
        task_meta.mref_internals().lock_count = AtomicU64::new(0);
        let task_data_ptr = task_slot.add(dist_to_data);
        task_data_ptr.cast::<T>().write(env);
        frame
      } else {
        SubRegionRef::new_null()
      };
      initial_task.action = Action::new(head);
      ctx.workset.enque(initial_task);
    });
    let boxed = Box::from_raw(boxed);
    (*boxed.worker_set.0.get()).io_thread.start();
    return boxed
  } }
  pub fn await_completion(&mut self) { unsafe {
    let work_set = &mut(self.worker_set);
    loop {
      if work_set.all_workers_are_idle() && work_set.io_worker_stoped() {
        break
      }
      yield_now()
    }
    let total_worker_count = work_set.total_worker_count();
    for ix in 0 .. total_worker_count {
      let wref = work_set.mref_worker_at_index(ix);
      wref.flags.mark_for_termination();
      wref.wakeup();
      wref.terminate();
    }
    let io_worker_handle = &mut(*work_set.0.get()).io_thread.handle;
    with_scoped_consume(io_worker_handle, |proxy|{
      let handle = proxy.consume();
      if let Some(thread) = handle {
        thread.join().unwrap();
      }
      proxy.recover(None);
    });
  } }
}


#[test]
fn frame_aligner() {
  let renorm = |n: usize| { (1 << 3) << n };
  let (a, b) = adjusted_frame_size(8 * 13, 8, 16);
  assert!(a== 120 && renorm(b)==16);
  let (a, b) = adjusted_frame_size(8, 8, 16);
  assert!(a==24 && renorm(b)==16);
  let (a, b) = adjusted_frame_size(8 * 16, 64, 16);
  assert!(a==192 && renorm(b)==64);
  let (a, b) = adjusted_frame_size(1, 1, 16);
  assert!(a==17 && renorm(b)==16);
  let (a, b) = adjusted_frame_size(8*100, 512, 16);
  assert!(a==1312 && renorm(b)==512);
  let (a, b) = adjusted_frame_size(8*3, 8, 8);
  assert!(a==32 && renorm(b)==8);
  let (a, b) = adjusted_frame_size(8*0, 8, 8);
  assert!(a==8 && renorm(b)==8);
  let (a, b) = adjusted_frame_size(8*5, 16, 24);
  assert!(a==72 && renorm(b)==32);
  let (a, b) = adjusted_frame_size(8*5, 1, 1);
  assert!(a==48 && renorm(b)==8);
  let (a, b) = adjusted_frame_size(8*5, 1, 24);
  assert!(a==72 && renorm(b)==32);
  // let (a, b) = adjusted_frame_size(8*5, 1, 0);
  // assert!(a == 40 && renorm(b) == 0); // actual is (48, 1, 8)
  // technically the last one gives incorrect answer
  // but I dont give a fuck, it is not possible to
  // make a task that does not have metadata.
  // println!("{} {} {}", a, b, renorm(b));
}


#[test]
fn test_trivial_tasking() {
  static mut evil_formula : &str = "";
  fn single_print(ctx: &TaskContext) -> Continuation {
    unsafe { evil_formula = "CH3O2"; }
    return Continuation::Done;
  }

  let mut work_group = WorkGroup::new((), single_print);
  work_group.await_completion();
  assert!("CH3O2" == unsafe { evil_formula });
}
#[test]
fn non_basic_box_spawninng() {
  const val : &str = "may dark days last least";
  fn single_print(ctx: &TaskContext) -> Continuation {
    let box_ = ctx.spawn_rc_box(String::from_str(val).unwrap());
    ctx.install_task_frame::<String>();
    return Continuation::Then(|ctx|{

      return Continuation::Done
    });
  }

  let mut work_group = WorkGroup::new((), single_print);
  work_group.await_completion();
}

#[test]
fn one_shild_one_parent() {

  static mut name: &str = "";
  fn parent(ctx: &TaskContext) -> Continuation {
    ctx.spawn_subtask((), child);
    return Continuation::Done
  }
  fn child(ctx: &TaskContext) -> Continuation {
    unsafe { name = "I am Jason";};
    return Continuation::Done;
  }

  let mut work_group = WorkGroup::new((), parent);
  work_group.await_completion();

  assert!("I am Jason" == unsafe {name});
}

#[test]
fn child_child_check_dead() {
  const Limit:usize = 4 * 1000;
  struct ParentData { counter: AtomicU64, str: String, iter: u64 }
  fn parent(ctx: &TaskContext) -> Continuation {
    let frame = unsafe { &mut *ctx.access_task_frame::<ParentData>() };
    // println!("{}", frame.str);
    for _ in 0 .. Limit {
      ctx.spawn_subtask(&frame.counter, child);
    }
    // if frame.iter == 0 { return Continuation::Next(check)}
    // frame.iter -= 1;
    return Continuation::Then(check)
  }
  fn child(ctx: &TaskContext) -> Continuation {
    let counter = unsafe { &*ctx.access_task_frame::<&AtomicU64>() };
    let _ = counter.fetch_add(1, Ordering::Relaxed);
    return Continuation::Done;
  }
  fn check(ctx: &TaskContext) -> Continuation {
    let frame = unsafe { &*ctx.access_task_frame::<ParentData>() };
    let val = frame.counter.load(Ordering::Relaxed);
    // assert!(val == Limit as u64);
    println!("{}", val);

    return Continuation::Done
  }

  let str = String::from_str("are you okay pal?").unwrap();
  let frame = ParentData {counter: AtomicU64::new(0), str, iter: 1 };
  let mut work_group = WorkGroup::new(frame, parent);
  work_group.await_completion();
  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    println!("{} {}", acqc, relc);
    assert!(relc == acqc);
  }
}


struct IsolateFlags(AtomicU8);
impl IsolateFlags {
  fn new() -> Self { Self(AtomicU8::new(0))}
  fn set_msg_align(&self, align: u8) {
    let order = high_order_pow2(align as u64) - 1;
    if order > 0b1111 { panic!("align is too big") }
    let erased = self.0.load(Ordering::Acquire) & (!0 << 4);
    let replaced = erased | (order as u8);
    self.0.store(replaced, Ordering::Release)
  }
  fn get_msg_align(&self) -> u8 {
    let val = self.0.load(Ordering::Acquire);
    let val = val & 0b1111;
    return val + 1
  }
  // false if already serviced
  fn try_claim_ownership(&self) -> bool {
    let prior = self.0.fetch_or(1 << 4, Ordering::AcqRel);
    prior & (1 << 4) == 0
  }
}
#[repr(C)]
struct IsolateMetadata {
  send_method_impl: AtomicU64,
  respond_method_impl: u64,
  liveness_count: AtomicU64,
  destructor: fn(*mut())
}
impl IsolateMetadata {
  const OWNERSHIP_BIT: u64 = 1 << 48;
  // false if already owned
  fn try_claim_ownership(&self, order: Ordering) -> bool {
    let prior = self.send_method_impl.fetch_or(Self::OWNERSHIP_BIT, order);
    let already_owned = prior & Self::OWNERSHIP_BIT != 0;
    return already_owned
  }
  const BEING_PROCESSED_BIT: u64 = 1 << 49;
  fn try_mark_as_being_processed(&self, order: Ordering) -> bool {
    todo!()
  }
  fn set_data_align_order(&self, align: usize) {
    let order = high_order_pow2(align as u64);
    assert!(order <= 0b1111);
    let _ = self.send_method_impl.fetch_or(order << 60 , Ordering::Relaxed);
  }
  fn get_data_align_order(&self) -> u8 {
    let i = self.send_method_impl.load(Ordering::Relaxed);
    let v = i >> 60;
    return v as u8
  }
  fn offset_to_data(&self) -> usize {
    let align = 1 << self.get_data_align_order();
    let mut offset = size_of::<Self>();
    offset += offset_to_higher_multiple(offset as u64, align) as usize;
    return offset
  }
}

#[test] #[ignore]
fn mem_locations() { unsafe {
  let memer = || {
    alloc(Layout::from_size_align_unchecked(1 << 21, 4096))
  };
  let mut highs = 0;
  for _ in 0 .. 16 {
    let mem_addr = memer();
    let k = ((mem_addr as u64) >> 12) >> 32;
    if highs == 0 { highs = k } else {
      assert!(highs == k);
    }
  }
} }

pub struct IsolateRef<T:Isolate>(SubRegionRef, PhantomData<T>);
impl <T:Isolate> IsolateRef<T> {
  fn copy_ref(&self) -> Self { unsafe {
    let iso_ptr = self.0.deref();
    let iso_meta = &*iso_ptr.cast::<IsolateMetadata>();
    let _ = iso_meta.liveness_count.fetch_add(1, Ordering::AcqRel);
    let new = transmute_copy::<_, SubRegionRef>(&self.0);
    return Self(new, PhantomData)
  } }
  fn erase_to_some(self) -> SomeIsolateRef {
    unsafe { transmute(self) }
  }
}
impl <T:Isolate> Clone for IsolateRef<T> {
  fn clone(&self) -> Self {
    self.copy_ref()
  }
}

pub struct SomeIsolateRef(SubRegionRef);

type UniversalMsgSendSig<T, K> =
  fn (*const (), &TaskContext, K) -> T;
type UniversalMsgRespondSig = fn (*mut (), &TaskContext) -> Option<Continuation>;
pub trait Isolate {
  type Message: Send ;
  type MsgSendOutcome ;
  type SyncView: Sync ;
  // this method can be called from multiple threads
  fn send_message(
    this: &Self::SyncView, // thread safe view of self
    ctx: &TaskContext,
    message: Self::Message) -> Self::MsgSendOutcome;
  // this method is never called from single thread.
  // if none then there are no messages in queue
  fn respond_to_message(&mut self, ctx: &TaskContext) -> Option<Continuation>;
}

struct HillariousIso {
  count: u64,
  queue: MPSCQueue<HillariousIsoMessage>
}
impl HillariousIso {
  fn shit_pants(&mut self) {
    self.count += 1;
  }
  fn anounce(&self) {
    println!("pants have been shited {} times", self.count)
  }
}
enum HillariousIsoMessage {
  ShitPants, Anounce
}
impl Isolate for HillariousIso {
  type Message = HillariousIsoMessage;
  type MsgSendOutcome = ();
  type SyncView = Self;
  fn respond_to_message(&mut self, ctx:&TaskContext) -> Option<Continuation> { unsafe {
    let allocer = &mut(*(*ctx.0.get()).worker_inner_context_ref).allocator;
    let msg = self.queue.dequeue_item(allocer);
    match msg {
      None => return None,
      Some(msg) => {
        match msg {
          HillariousIsoMessage::Anounce => self.anounce(),
          HillariousIsoMessage::ShitPants => self.shit_pants()
        }
        return Some(Continuation::Done)
      }
    }
  } }
  fn send_message(
    this: &Self,
    ctx: &TaskContext,
    message: Self::Message
  ) { unsafe {
    let src = &mut *ctx.0.get();
    let ptr = &mut (*src.worker_inner_context_ref).allocator;
    this.queue.enqueue_item(message, ptr);
  } }
}

#[test]
fn messaging_isolate() {
  struct Ctx {
    iso_ref: IsolateRef<HillariousIso>,
    counter: u32
  }
  fn begin(ctx: &TaskContext) -> Continuation { unsafe {
    let frame = &mut *ctx.access_task_frame::<Ctx>();

    frame.counter = 1;

    let iso = ctx.spawn_isolate(HillariousIso{count: 0, queue: MPSCQueue::new()});
    frame.iso_ref = iso;

    return Continuation::Then(looper);
  } }
  fn looper(ctx: &TaskContext) -> Continuation {
    let frame = unsafe {&mut *ctx.access_task_frame::<Ctx>()};

    ctx.send_message(
      &frame.iso_ref,
      HillariousIsoMessage::ShitPants);

    if frame.counter == 0 { return Continuation::Then(|ctx| {
      let frame = unsafe {&mut *ctx.access_task_frame::<Ctx>()};

      ctx.send_message(&frame.iso_ref, HillariousIsoMessage::Anounce);
      let copy = unsafe {transmute_copy::<_, IsolateRef<HillariousIso>>(&frame.iso_ref)};
      ctx.dispose_isolate(copy);

      return Continuation::Done
    }) }
    frame.counter -= 1;
    return Continuation::Then(looper)
  }
  let mut wg = WorkGroup::new(garbage!(Ctx), begin);
  wg.await_completion();
  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    println!("{} {}", relc, acqc);
    assert!(relc == acqc);
  }
}

#[test]
fn deffered_frame_installation() {

  type Frame = Option<ArcBox<String>>;
  fn begin(ctx: &TaskContext) -> Continuation { unsafe {
    let str_ = String::from_str("quite a shiny day, eh?").unwrap();
    ctx.install_task_frame::<Frame>();
    let frame = ctx.access_task_frame::<Frame>();
    let box_ = ctx.spawn_rc_box(str_);
    frame.write(Some(box_));

    return Continuation::Then(|ctx|{
      let frame = &mut *ctx.access_task_frame::<Frame>();
      let val = frame.take().unwrap();
      assert!(val.as_ref() == &String::from_str("quite a shiny day, eh?").unwrap());
      ctx.dispose_rc_box(val);
      return Continuation::Done;
    })
  } }
  let mut wg = WorkGroup::new((), begin);
  wg.await_completion();
  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    assert!(relc == acqc);
  }
}

static mut WAS_DESTROYED: bool = false;
struct DestructibleIso;
impl Drop for DestructibleIso {
  fn drop(&mut self) {
    unsafe { WAS_DESTROYED = true }
  }
}
impl Isolate for DestructibleIso {
  type Message = ();
  type MsgSendOutcome = ();
  type SyncView =  Self;
  fn respond_to_message(&mut self, ctx: &TaskContext) -> Option<Continuation> {
    return None
  }
  fn send_message(
    this: &Self::SyncView, // thread safe view of self
    ctx: &TaskContext,
    message: Self::Message) -> Self::MsgSendOutcome {

  }
}
#[test]
fn destructibe_isolate() {
  fn fun(ctx: &TaskContext) -> Continuation {
    let iso = ctx.spawn_isolate(DestructibleIso);
    ctx.dispose_isolate(iso);
    return Continuation::Done;
  }
  let mut wg = WorkGroup::new((), fun);
  wg.await_completion();
  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    assert!(relc == acqc);
    assert!(WAS_DESTROYED);
  }
}

enum AnouncerMessage {
  Text(String), Flush
}
struct Anouncer {
  items: Vec<String>,
  queue: MPSCQueue<AnouncerMessage>,
}

impl Isolate for Anouncer {
  type Message = AnouncerMessage;
  type MsgSendOutcome = ();
  type SyncView = Self;
  fn respond_to_message(&mut self, ctx: &TaskContext) -> Option<Continuation> {
    let sralloc =  unsafe{ &mut(*(*ctx.0.get()).worker_inner_context_ref).allocator};
    let msg = self.queue.dequeue_item(sralloc);
    match msg {
      Some(msg) => {
        match msg {
          AnouncerMessage::Flush => println!("{}", self.items.join("; ")),
          AnouncerMessage::Text(text) => self.items.push(text)
        };
        return Some(Continuation::Done)
      },
      None => return None
    }
  }
  fn send_message(
    this: &Self::SyncView, // thread safe view of self
    ctx: &TaskContext,
    message: Self::Message) -> Self::MsgSendOutcome {
    let sralloc =  unsafe{ &mut(*(*ctx.0.get()).worker_inner_context_ref).allocator};
    this.queue.enqueue_item(message, sralloc);
  }
}

#[test]
fn send_in_task_in_send() {
  struct Ctx { iso_ref: IsolateRef<Anouncer> }
  fn fun(ctx: &TaskContext) -> Continuation {
    let iso = ctx.spawn_isolate(
      Anouncer {items: Vec::new(), queue: MPSCQueue::new()});
    for i in 0 .. 10 {
      ctx.spawn_subtask((iso.clone(),i), |ctx|{
        let (iso, i) = unsafe{ &mut *ctx.access_task_frame::<(IsolateRef<Anouncer>, i32)>() };
        ctx.send_message(&iso, AnouncerMessage::Text(format!("{i}")));
        ctx.dispose_isolate(unsafe {transmute_copy::<_, IsolateRef<Anouncer>>(iso) });
        return Continuation::Done
      })
    }
    ctx.send_message(&iso, AnouncerMessage::Flush);
    ctx.dispose_isolate(iso);
    return Continuation::Done;
  }
  let mut wg = WorkGroup::new((), fun);
  wg.await_completion();
  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    println!("{} {}", acqc, relc);
    assert!(relc == acqc);
  }
}
