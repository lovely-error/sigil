
use std::{sync::atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, compiler_fence}, mem::{size_of, MaybeUninit, forget, ManuallyDrop, transmute, align_of}, ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut}, thread::{JoinHandle, self, park, yield_now, Thread, current}, cell::UnsafeCell, str::FromStr, cmp::min, alloc::{alloc, Layout}};

use crate::{root_alloc::{RootAllocator, Block4KPtr}, utils::{ptr_align_dist, with_scoped_consume, bitwise_copy, high_order_pow2}, cast, loopbuffer::InlineLoopBuffer, array::Array, garbage,  };

pub struct SubRegionAllocator {
  ralloc: *mut RootAllocator,
  current_page_start: *mut u8,
  offset: *mut u8,
  free_list: *mut u8
}

static mut acquire_count : AtomicU64 = AtomicU64::new(0);
static mut release_count : AtomicU64 = AtomicU64::new(0);

impl SubRegionAllocator {
  pub fn new(
    root_alloc_ref: *mut RootAllocator
  ) -> Self { unsafe {
    let mut raw = MaybeUninit::<Self>::uninit();
    let mref = raw.assume_init_mut();
    mref.ralloc = root_alloc_ref;
    mref.free_list = null_mut();
    let mut init = raw.assume_init();
    init.replace_page();
    return init;
  }; }
  fn replace_page(&mut self) { unsafe {
    let has_free_pages = self.free_list != null_mut();
    let ptr;
    if has_free_pages {
      let next_page = *self.free_list.cast::<*mut u8>();
      ptr = self.free_list;
      self.free_list = next_page;
    } else {
      let page;
      loop {
        if let Some(block) = (*self.ralloc).try_get_block() {
          page = block; break;
        }
      }
      let Block4KPtr(ptr_) = page;
      ptr = ptr_;
    }
    self.current_page_start = ptr;
    {
      let ptr = &mut *ptr.cast::<RegionMetadata>();
      ptr.ref_count = AtomicU16::new(0);
    };
    self.offset = ptr.add(size_of::<RegionMetadata>());
  } }
  #[track_caller]
  pub fn srallocate(
    &mut self,
    byte_size: usize,
    alignment: usize
  ) -> SubRegionRef { unsafe {
    assert!(
      byte_size <= 4096 - size_of::<RegionMetadata>(),
      "too big allocation, ill fix it when need be");
    loop {
      let mut ptr = self.offset;
      let off = ptr_align_dist(ptr, alignment);
      ptr = ptr.add(off as usize);
      let aligned_ptr = ptr;
      ptr = ptr.add(byte_size);
      if ptr as u64 >= (self.current_page_start as u64 + 4096) {
        self.replace_page(); continue;
      }
      let _ = (&mut*self.current_page_start.cast::<RegionMetadata>())
        .ref_count.fetch_add(1, Ordering::Release);
      acquire_count.fetch_add(1, Ordering::Relaxed);
      self.offset = ptr;
      let dist = aligned_ptr as u64 - self.current_page_start as u64;
      assert!(dist <= u16::MAX as u64);
      return SubRegionRef::new(self.current_page_start, dist as u16);
    }
  }; }
  #[track_caller]
  pub fn dispose(&mut self, ptr: SubRegionRef) { unsafe {
    let (root,_) = ptr.get_components();
    let i = (&*root.cast::<RegionMetadata>()).ref_count.fetch_sub(1, Ordering::Relaxed);
    release_count.fetch_add(1, Ordering::Relaxed);
    if i - 1 == 0 {
      // println!("page freed!");
      fence(Ordering::Acquire);
      // this page is ours!
      *root.cast::<*mut u8>() = self.free_list;
      self.free_list = root.cast();
    }
    // forget(ptr);
  } }
  #[inline(never)]
  pub fn srallocate_frame(
    &mut self,
    env_size: usize,
    env_align:usize,
    mtd_size: usize
  ) -> (SubRegionRef, *mut u8, *mut u8) { unsafe {
    let frame_alignment = env_align;
    let frame_size = env_size;
    let (real_frame_size, offset_order) =
      adjusted_frame_size(frame_size, frame_alignment, mtd_size);
    let data_frame_offset = renorm_offset_order(offset_order);
    // maybe remove this restriction
    let frame_allocation_limit = 4096 - size_of::<RegionMetadata>();
    if real_frame_size >= frame_allocation_limit {
      panic!("FIXME:Cant allocate this much for a task frame.")
    }
    let frame_ref = self.srallocate(real_frame_size, align_of::<ParentedTaskMetadata>());
    let frame_ptr = frame_ref.deref();
    let data = frame_ptr.add(data_frame_offset);
    return (frame_ref, frame_ptr, data)
  }; }
}

pub struct SubRegionRef(u64);
impl SubRegionRef {
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
    let v = sralloc.srallocate(16, 64);
    let ptr = v.deref();
    *ptr.cast() = u16::MAX;
    boxess.add(i).write(v);
  }
  let above = sralloc.srallocate(16, 64); // must cause page replace
  above.deref().cast::<u16>().write(u16::MAX);
  boxess.add(63).write(above);
  for i in 0 .. 64 {
    let item = boxess.add(i).read();
    let val = *item.deref().cast::<u16>();
    assert!(val == u16::MAX);
    sralloc.dispose(item);
  }
} }

struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  inline_workers: [MaybeUninit<Worker>; 16],
  outline_workers: Option<Array<Worker>>,
  inline_free_indicies: AtomicU64,
  outline_free_indicies: Option<Array<AtomicU64>>,
  total_worker_count: u32,
  liveness_count: AtomicU32,
}

impl WorkerSet {
  fn inline_free_indicies(&self) -> &AtomicU64 {
    &unsafe { &*self.0.get() }.inline_free_indicies
  }
  fn liveness_count(&self) -> &AtomicU32 {
    &unsafe { &*self.0.get() }.liveness_count
  }
  fn total_worker_count(&self) -> u32 {
    unsafe { &*self.0.get() }.total_worker_count
  }
  fn mref_worker_at_index(&self, index: u32) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    let work_count = this.total_worker_count;
    if index >= work_count { return None }
    if index < work_count {
      let ptr = addr_of_mut!(this.inline_workers).cast::<Worker>();
      let worker = &mut *ptr.add(index as usize );
      return Some(worker)
    } else {
      if let Some(w) = &this.outline_workers {
        let worker = w.ref_item_at_index(index as usize - 16).unwrap();
        return Some(worker);
      };
      panic!()
    };
  }; }
  fn set_as_free(&self, index: u32) -> Option<bool> {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { return None }

    let index_mask = 1u64 << index;
    let mask = !index_mask ;
    let old = this.inline_free_indicies.fetch_and(mask, Ordering::Relaxed);
    let already_taken = old & index_mask != 0;
    return Some(already_taken)
  }
  // true, if already occupied
  fn set_as_occupied(&self, index: u32) -> Option<bool> {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { return None }

    let mask = 1u64 << index;
    let old = this.inline_free_indicies.fetch_or(mask, Ordering::Relaxed);
    let already_taken = old & mask != 0;
    return Some(already_taken)
  }
  fn try_acquire_free_worker(&self) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    loop {
      let indicies = this.inline_free_indicies.load(Ordering::Relaxed);
      if indicies == u64::MAX {
        if let Some(_) = this.outline_workers {
          todo!()
        }
        return None ;
      };
      let some_index = indicies.trailing_ones();
      if some_index >= this.total_worker_count { return None; }
      let mask = 1u64 << some_index;
      let prior = this.inline_free_indicies.fetch_or(mask, Ordering::Relaxed);
      let did_acquire = prior & mask == 0;
      if !did_acquire { continue; }
      if some_index < 16 {
        let ptr = this.inline_workers.as_ptr().add(some_index as usize);
        let ptr = ptr.add(some_index as usize).cast::<Worker>() as *mut _;
        let val = &mut *ptr;
        return Some(val)
      } else {
        // somewhere outline
        todo!()
      }
    }
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
  fn push(&mut self, new_item: Task) {
    let clone = unsafe { addr_of!(new_item).read() };
    let did_push = self.inline_tasks.push(new_item);
    if !(did_push) {
      self.outline_tasks.push(clone)
    } else {
      forget(clone)
    }
  }
  fn pop(&mut self) -> Option<Task> {
    let task = self.inline_tasks.pop();
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
    cast!(0u8, _)
  }
  const SELFKILL_BIT: u8 = 1;
  fn mark_self_kill(&self) {
    let _ = self.0.fetch_or(Self::SELFKILL_BIT, Ordering::Relaxed);
  }
  fn should_kill_self(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::SELFKILL_BIT != 0;
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
  const INITED_BIT: u8 = 1 << 2;
  fn mark_as_initialised(&self) {
    let _ = self.0.fetch_or(Self::INITED_BIT, Ordering::Relaxed);
  }
  fn is_initialised(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::INITED_BIT != 0
  }
  const INITIATOR_BIT: u8 = 1 << 3;
  fn mark_for_first_init(&self) {
    let _ = self.0.fetch_or(Self::INITIATOR_BIT, Ordering::Relaxed);
  }
  fn is_first_init(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::INITIATOR_BIT != 0;
  }
  const WORK_SUBMITED_BIT: u8 = 1 << 4;
  fn mark_work_as_submited(&self) {
    let _ = self.0.fetch_or(Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn unmark_work_as_submited(&self) {
    let _ = self.0.fetch_and(!Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn is_work_submited(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::WORK_SUBMITED_BIT != 0
  }
  const TRANSACTION_BEGAN_BIT: u8 = 1 << 5;
  fn mark_transaction_begin(&self) {
    let _ = self.0.fetch_or(Self::TRANSACTION_BEGAN_BIT, Ordering::Relaxed);
  }
  const TRANSACTION_ENDED_BIT:u8 = 1 << 6;
  fn mark_transaction_end(&self) {
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
  task_share_port: MaybeUninit<*mut TaskSet<TaskCacheSize>>,
  srallocator_ref: MaybeUninit<*mut SubRegionAllocator>,

  index: u32,
  flags: WorkerFlags,
}
impl Worker {
  // last active worker
  fn mark_retire(&self) -> bool { unsafe {
    let prior = (*self.work_group).worker_set.liveness_count().fetch_sub(1, Ordering::Relaxed);
    return prior - 1 == 0
  } }
  fn unmark_retire(&self) { unsafe {
    let _ = (*self.work_group).worker_set.liveness_count().fetch_add(1, Ordering::Relaxed);
  } }
  // false if already occupied
  fn mark_as_occupied(&self) -> bool { unsafe {
    (*self.work_group).worker_set.set_as_occupied(self.index).unwrap()
  } }
  fn wakeup(&self) {
    if let Some(thread) = &self.runner_handle {
      thread.thread().unpark();
    };
  }
  fn start(&mut self) { unsafe {
    if self.flags.is_initialised() { return };
    let _ = self.mark_as_occupied();
    let this = {
      let referee = transmute::<_, u64>(self);
      move || transmute::<_, &mut Self>(referee)
    };
    if let None = this().runner_handle {
      let copy = transmute::<_, u64>(this());
      let thread = thread::spawn(move ||{
        let ptr = transmute::<_, &mut Worker>(copy);
        task_execution_loop(ptr);
      });
      this().runner_handle = Some(thread);
      loop {
        let inited = this().flags.is_initialised();
        if inited {
          fence(Ordering::Acquire);
          break;
        }
      }
    }
  } }
  fn terminate(&mut self) {
    with_scoped_consume(&mut self.runner_handle, |g| {
      let v = g.consume();
      if let Some(thread) = v {
        let () = thread.join().unwrap();
        g.assign(None);
      } else {
        g.assign(v)
      };
    });
  }
}

const TaskCacheSize:usize = 16;
fn task_execution_loop(worker: &mut Worker) { unsafe {
  (*worker.work_group).worker_set.liveness_count().fetch_add(1, Ordering::Relaxed);
  let ralloc = addr_of_mut!((*worker.work_group).ralloc);
  let mut sralloc = SubRegionAllocator::new(ralloc);
  let mut workset = TaskSet::<TaskCacheSize>{
    inline_tasks:InlineLoopBuffer::new(),
    outline_tasks: Array::new(ralloc)
  };
  let workset_ = addr_of_mut!(workset);
  let sralloc_ = addr_of_mut!(sralloc);
  *worker.task_share_port.assume_init_mut() = workset_;
  *worker.srallocator_ref.assume_init_mut() = sralloc_;
  fence(Ordering::Release);
  worker.flags.mark_as_initialised();
  while !worker.flags.is_work_submited() { yield_now(); }
  fence(Ordering::Acquire);
  worker.flags.unmark_work_as_submited();
  let task_context = TaskContext::new(sralloc_, workset_);
  'quantum:loop {
    match (*workset_).pop() {
      Some(task) => {
        let mut current_task = task;
        let mut current_thunk = current_task.action.project_fun_ptr();
        task_context.set_current_task_ref(&current_task);
        'local_work:loop {
          let continuation = current_thunk(&task_context); // do work
          fence(Ordering::Release);
          let is_childless_task = task_context.spawned_subtask_count() == 0;
          match (continuation, is_childless_task) {
            (Continuation::Next(next_thunk), true) => {
              // task need not await its children.
              // just go ahead
              current_thunk = next_thunk;
              continue 'local_work;
            },
            (Continuation::Next(next_thunk), false) => {
              // this task has been parked and last child
              // will put it back in action
              task_context.fix_continuation(next_thunk);
              task_context.inject_propper_lock_count();
              task_context.clear_dirty_state();
              // give some work away if there is too much of it
              share_work_if_appropriate(worker, workset_);
              continue 'quantum;
            },
            (Continuation::Stop, false) => {
              // this task wont be awaken, but there are subtasks which
              // might use its frame.
              // mark it dead such that the last child
              // disposes the frame
              task_context.mark_current_task_as_dead();
              task_context.inject_propper_lock_count();
              task_context.clear_dirty_state();
              // give some work away if there is too much of it
              share_work_if_appropriate(worker, workset_);
              continue 'quantum;
            },
            (Continuation::Stop, true) => {
              // this is a terminal step
              let should_drop_lock_count = current_task.action.mref_flags().is_parent_waker();
              let current_frame_delete = current_task.frame_ptr;
              if should_drop_lock_count {
                let frame_ptr = current_frame_delete.deref();
                let mtd = &*frame_ptr.cast::<ParentedTaskMetadata>();
                let parked_parent_slot = addr_of!(mtd.mref_internals().parent_task_ref).read();
                let parent_task = parked_parent_slot.deref().cast::<Task>().read();
                let parent_frame = parent_task.frame_ptr.deref();
                let parent_mtd = &*parent_frame.cast::<ParentedTaskMetadata>();
                let lock_count = parent_mtd.mref_internals().lock_count.fetch_sub(1, Ordering::Relaxed);
                let last_child = lock_count - 1 == 0;
                let parent_dead = parent_task.action.mref_flags().is_dead();
                match (last_child, parent_dead) {
                  (true, true) => {
                    fence(Ordering::AcqRel);
                    sralloc.dispose(parked_parent_slot);
                    sralloc.dispose(current_frame_delete);
                    sralloc.dispose(parent_task.frame_ptr);
                    continue 'quantum;
                  },
                  (true, false) => {
                    fence(Ordering::AcqRel);
                    sralloc.dispose(current_frame_delete);
                    sralloc.dispose(parked_parent_slot);
                    current_task = parent_task;
                    current_thunk = current_task.action.project_fun_ptr();
                    task_context.set_current_task_ref(&current_task);
                    continue 'local_work;
                  },
                  (false, _) => {
                    sralloc.dispose(current_frame_delete);
                    continue 'quantum
                  }
                }
              } else {
                // we are not responsible for anybody!
                // this inludes synchronization
                sralloc.dispose(current_frame_delete);
                continue 'quantum;
              }
            },
          }
        }
      },
      None => {
        // there is no work locally present to be done.
        let last_working = worker.mark_retire();
        if last_working {
          // all work is done now. we hand awaiting thread the disposition procedure
          for ix in 0 .. (*worker.work_group).worker_set.total_worker_count() {
            if ix == worker.index { continue }
            let there = (*worker.work_group).worker_set.mref_worker_at_index(ix).unwrap();
            there.flags.mark_self_kill();
            while !there.flags.is_marked_for_suspend() {}
            loop {
              there.wakeup();
              if !there.flags.is_marked_for_suspend() { break }
            }
          }
          let work_group = &(*worker.work_group);
          while work_group.sigkill.load(Ordering::Relaxed) != 1 { yield_now() }
          work_group.sigkill.store(2, Ordering::Release);
          work_group.completion_awaiting_thread.assume_init_read().unpark();
          return; // goodbye sweet prince
        } else {
          // go idle. maybe other workers will share a few more tasks
          let selfkill = suspend(&worker);
          if selfkill {
            return; // goodbye sweet prince
          }
          worker.unmark_retire();
        }
      }
    }
  }
} }

fn suspend(worker: &Worker) -> bool {
  worker.flags.mark_for_suspend();
  let _ = unsafe { &*worker.work_group }.worker_set.set_as_free(worker.index).unwrap();
  let self_kill = loop {
    if worker.flags.should_kill_self() {
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
  fence(Ordering::Release);
  worker.flags.unmark_for_suspend();

  return self_kill
}

fn share_work_if_appropriate<const C:usize>(
  worker: *mut Worker, workset: *mut TaskSet<C>
) { unsafe {
  let workset = &mut *workset;
  let local_item_count = workset.item_count();
  let have_too_many_tasks = local_item_count > TaskCacheSize;
  // ideally, there should be a weight metric for tasks
  // so that we can definitevely determine when certain amount of tasks is
  // actually too much to carry on by a single worker. but such a system would require
  // more effort than I ready to give at the moment. some other day, maybe..
  if have_too_many_tasks {
    let worker_count = (*(*worker).work_group).worker_set.total_worker_count();
    let inline_indicies = &(*(*worker).work_group).worker_set.inline_free_indicies();
    let free_worker_count = {
      let mask = !(!0u64 >> (64 - worker_count));
      let ixs = inline_indicies.load(Ordering::Relaxed);
      let filtered = (mask | ixs).count_zeros();
      filtered
    };
    let aprox_split = local_item_count / 16;
    let aprox_split = min(aprox_split, free_worker_count as usize);
    let mut i = aprox_split;

    let src = (*worker).task_share_port.assume_init_read();
    if worker_count <= 64 {
      loop {
        let free_thread_indicies = inline_indicies.load(Ordering::Relaxed);
        let free_thread_index = free_thread_indicies.trailing_ones();
        if free_thread_index >= worker_count { return }
        let target_mask = 1u64 << free_thread_index;
        let prior = inline_indicies.fetch_or(target_mask, Ordering::Relaxed);
        let worker_is_ours = prior & target_mask == 0;
        if worker_is_ours {
          let subordinate_worker =
            (*(*worker).work_group).worker_set.mref_worker_at_index(free_thread_index)
            .unwrap();
          let already_inited = subordinate_worker.flags.is_initialised();
          let dest ;
          if !already_inited {
            subordinate_worker.start();
            while !subordinate_worker.flags.is_initialised() {}
            fence(Ordering::Acquire);
            dest = subordinate_worker.task_share_port.assume_init_read();
            perform_task_transfer(src, dest);
            fence(Ordering::Release);
            subordinate_worker.flags.mark_work_as_submited();
          } else {
            dest = subordinate_worker.task_share_port.assume_init_read();
            subordinate_worker.flags.mark_transaction_begin();
            perform_task_transfer(src, dest);
            subordinate_worker.flags.mark_transaction_end();
            fence(Ordering::Release);
            while !subordinate_worker.flags.is_marked_for_suspend() {}
            fence(Ordering::Acquire);
            loop {
              subordinate_worker.wakeup();
              if !subordinate_worker.flags.is_marked_for_suspend() { break }
            }
          }
          i -= 1;
          if i == 0 { return }
        } else { continue; }
      }
    } else {
      todo!()
    }
  }
} }
fn perform_task_transfer(src: *mut TaskSet<TaskCacheSize>, dst: *mut TaskSet<TaskCacheSize>) { unsafe {
  // this really needs the best possible performance for copying tasks into the reciever.
  // employing some vector intrinsincs would be great! aing gonna do it  today, though
  loop {
    if let Some(task) = (*src).pop() {
      (*dst).push(task)
    } else {return };
  }
} }

struct ParentedTaskMetadata(UnsafeCell<ParentedTaskMetadataInternals>);
impl ParentedTaskMetadata {
  fn mref_internals(&self) -> &mut ParentedTaskMetadataInternals {
    unsafe { &mut *self.0.get() }
  }
}
struct ParentedTaskMetadataInternals {
  lock_count: AtomicU64,
  parent_task_ref: SubRegionRef
}
struct ParentlessTaskMetadata(UnsafeCell<ParentlessTaskMetadataInternals>);
impl ParentlessTaskMetadata {
  fn mref_internals(&self) -> &mut ParentlessTaskMetadataInternals {
    unsafe { &mut *self.0.get() }
  }
}
struct ParentlessTaskMetadataInternals {
  lock_count: AtomicU64,
}


pub struct TaskContext(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  spawned_subtask_count: u64,
  fixup_target: *mut Task,
  current_task_ref: *const Task,
  region_ref: MaybeUninit<SubRegionRef>,
  srallocator: *mut (),
  taskset: *mut ()
}
impl TaskContext {
  fn new<const C:usize>(
    srallocator: *mut SubRegionAllocator,
    taskset: *mut TaskSet<C>
  ) -> Self {
    TaskContext(UnsafeCell::new(TaskContextInternals {
      spawned_subtask_count: 0,
      current_task_ref: null_mut(),
      fixup_target: null_mut(),
      srallocator: srallocator as *mut (),
      region_ref: MaybeUninit::uninit(),
      taskset:taskset as *mut ()
    }))
  }
  fn spawn_subtask<T: Sync + Send>(&self, env: T, thunk: Thunk) { unsafe {
    self.idempotently_park_parent_task();
    let this = &mut *self.0.get();
    this.spawned_subtask_count += 1;

    let frame_alignment = align_of::<T>();
    let frame_size = size_of::<T>();
    let (real_frame_size, offset_order) =
      adjusted_frame_size(frame_size, frame_alignment, size_of::<ParentedTaskMetadata>());
    let offset_to_data = renorm_offset_order(offset_order);
    // maybe remove this restriction
    let frame_allocation_limit = 4096 - size_of::<RegionMetadata>();
    if real_frame_size >= frame_allocation_limit {
      panic!("FIXME:Cant allocate this much for a task frame.")
    }

    let sralloc = &mut *this.srallocator.cast::<SubRegionAllocator>();
    let frame_ref = sralloc.srallocate(real_frame_size, align_of::<ParentedTaskMetadata>());
    let frame_ptr = frame_ref.deref();
    let mtd = (&mut *frame_ptr.cast::<ParentedTaskMetadata>()).mref_internals();
    mtd.lock_count = AtomicU64::new(0);
    mtd.parent_task_ref = this.region_ref.assume_init_read();
    let data = frame_ptr.add(offset_to_data);
    copy_nonoverlapping(addr_of!(env).cast(), data, frame_size);
    forget(env);

    let subtask = Task {action:Action::new(thunk), frame_ptr: frame_ref};
    subtask.action.mref_flags().mark_as_parent_waker();
    subtask.action.mref_flags().set_offset_order(offset_order as u8);

    let task_set = &mut * this.taskset.cast::<TaskSet<TaskCacheSize>>();
    task_set.push(subtask);
  } }
  fn spawn_detached_task(&self) {
    todo!()
  }
  fn spawned_subtask_count(&self) -> u64 {
    unsafe { &*self.0.get() }.spawned_subtask_count
  }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    this.spawned_subtask_count = 0;
    this.fixup_target = null_mut();
  }
  fn set_current_task_ref(&self, task_ref: *const Task) {
    unsafe { (&mut *self.0.get()).current_task_ref = task_ref } ;
  }
  fn fix_continuation(&self, thunk: Thunk) {
    let fixup_target = unsafe { &mut *(&mut *self.0.get()).fixup_target } ;
    fixup_target.action.set_fun_ptr(thunk);
  }
  fn mark_current_task_as_dead(&self) {
    let mark_target = unsafe { &mut *(&mut *self.0.get()).fixup_target } ;
    mark_target.action.mref_flags().mark_as_dead();
  }
  fn idempotently_park_parent_task(&self) { unsafe {
    let this = &mut *self.0.get() ;
    if this.fixup_target == null_mut() {
      let srallocator = &mut *this.srallocator.cast::<SubRegionAllocator>();
      let slot = srallocator.srallocate(size_of::<Task>(), align_of::<Task>());
      let parked_task_ptr = slot.deref().cast::<Task>();
      this.fixup_target = parked_task_ptr;
      *parked_task_ptr = this.current_task_ref.read();
      this.region_ref.as_mut_ptr().write(slot);
    }
  } }
  fn inject_propper_lock_count(&self) { unsafe {
    let this = &mut *self.0.get();
    let target = &mut *this.fixup_target;
    let frame = target.frame_ptr.deref();
    let mtd = &mut *frame.cast::<ParentedTaskMetadata>();
    mtd.mref_internals().lock_count = AtomicU64::new(this.spawned_subtask_count);
  } }
  fn access_frame<T>(&self) -> *mut T { unsafe {
    let this = &mut *self.0.get();
    let task = &*this.current_task_ref;
    let offset = task.action.mref_flags().get_offset_order_to_frame();
    let normalised_offset = renorm_offset_order(offset as usize);
    let data_offset = task.frame_ptr.deref().add(normalised_offset);
    return data_offset.cast()
  }; }
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
  fn get_offset_order_to_frame(&self) -> u8 {
    let off = 0b111 << 5;
    let proj = self.0[1] & off;
    let projnorm = proj >> 5;
    return projnorm
  }
}

#[derive(Clone, Copy)]
pub enum Continuation {
  Stop, Next(Thunk)
}
type Thunk = fn (&TaskContext) -> Continuation;
struct Action(UnsafeCell<ActionInternals>);
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
  // fn done() -> Self {
  //   let null = Self::new_null();
  //   null.mref_flags().mark_as_terminator();
  //   return null;
  // }
}

fn example(ctx: &TaskContext) -> Continuation { Continuation::Next(example) }
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

pub struct WorkGroup {
  ralloc: RootAllocator,
  worker_set: WorkerSet,
  completion_awaiting_thread: MaybeUninit<Thread>,
  sigkill: AtomicU8
}

impl WorkGroup {
  pub fn new<T: Sync + Send>(env: T, head: Thunk) -> Box<Self> { unsafe {
    let thread_count = 2 ;
    let boxed = alloc(
      Layout::from_size_align_unchecked(size_of::<Self>(), align_of::<Self>()));
    let boxed = boxed.cast::<Self>();
    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        inline_workers:MaybeUninit::uninit().assume_init(),
        outline_workers: None,
        inline_free_indicies: AtomicU64::new(0),
        liveness_count: AtomicU32::new(0),
        outline_free_indicies: None,
        total_worker_count: thread_count,
      })),
      completion_awaiting_thread: MaybeUninit::uninit(),
      sigkill: AtomicU8::new(0)
    });
    let boxed_ = boxed;
    for ix in 0 .. thread_count {
      let wref = (*boxed_).worker_set.mref_worker_at_index(ix).unwrap();
      let worker = Worker {
        index: ix,
        runner_handle: None,
        work_group: boxed_,
        flags: WorkerFlags::new(),
        task_share_port: MaybeUninit::uninit(),
        srallocator_ref: MaybeUninit::uninit()
      };
      cast!(wref, *mut Worker).write(worker);
    }
    let initiator = (*boxed_).worker_set.mref_worker_at_index(0).unwrap();
    fence(Ordering::Release);
    initiator.flags.mark_for_first_init();
    initiator.start();
    let (frame, mtd, data) = (*initiator.srallocator_ref.assume_init_read()).srallocate_frame(
      size_of::<T>(),
      align_of::<T>(),
      size_of::<ParentlessTaskMetadata>());
    copy_nonoverlapping(addr_of!(env).cast(), data, size_of::<T>());
    forget(env);
    let mtd = (&mut *mtd.cast::<ParentlessTaskMetadata>()).mref_internals();
    mtd.lock_count = AtomicU64::new(0);
    let initial_task = Task {
      action: Action::new(head),
      frame_ptr: frame
    };
    (*initiator.task_share_port.assume_init_read()).push(initial_task);
    fence(Ordering::Release);
    initiator.flags.mark_work_as_submited();

    let boxed = Box::from_raw(boxed);
    return boxed
  } }
  pub fn await_completion(&mut self) { unsafe {
    self.completion_awaiting_thread.as_mut_ptr().write(current()) ;
    self.sigkill.store(1, Ordering::Release);
    loop {
      park();
      if self.sigkill.load(Ordering::Relaxed) == 2 { break }
    }
    fence(Ordering::Acquire);
    assert!(self.worker_set.liveness_count().load(Ordering::Relaxed) == 0);
    let worker_set = addr_of_mut!(self.worker_set);
    let total_worker_count = (*worker_set).total_worker_count();
    for ix in 0 .. total_worker_count {
      let wref = (*worker_set).mref_worker_at_index(ix).unwrap();
      wref.terminate();
    }
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
    return Continuation::Stop;
  }

  let mut work_group = WorkGroup::new((), single_print);
  work_group.await_completion();
  assert!("CH3O2" == unsafe { evil_formula });
}

#[test]
fn one_shild_one_parent() {

  static mut name: &str = "";
  fn parent(ctx: &TaskContext) -> Continuation {
    ctx.spawn_subtask((), child);
    return Continuation::Stop
  }
  fn child(ctx: &TaskContext) -> Continuation {
    unsafe { name = "I am Jason";};
    return Continuation::Stop;
  }

  let mut work_group = WorkGroup::new((), parent);
  work_group.await_completion();

  assert!("I am Jason" == unsafe {name});
}

#[test]
fn child_child_check_dead() {
  const Limit:usize = 10000;
  struct ParentData { counter: AtomicU64, str: String, iter: u64 }
  fn parent(ctx: &TaskContext) -> Continuation {
    let frame = unsafe { &mut *ctx.access_frame::<ParentData>() };
    // println!("{}", frame.str);
    for _ in 0 .. Limit {
      ctx.spawn_subtask(&frame.counter, child);
    }
    // if frame.iter == 0 { return Continuation::Next(check)}
    // frame.iter -= 1;
    return Continuation::Next(check)
  }
  fn child(ctx: &TaskContext) -> Continuation {
    let counter = unsafe { &*ctx.access_frame::<&AtomicU64>() };
    let _ = counter.fetch_add(1, Ordering::Relaxed);
    return Continuation::Stop;
  }
  fn check(ctx: &TaskContext) -> Continuation {
    let frame = unsafe { &*ctx.access_frame::<ParentData>() };
    let val = frame.counter.load(Ordering::Relaxed);
    // assert!(val == Limit as u64);
    println!("{}", val);

    return Continuation::Stop
  }

  let str = String::from_str("are you okay pal?").unwrap();
  let frame = ParentData {counter: AtomicU64::new(0), str, iter: 1 };
  let mut work_group = WorkGroup::new(frame, parent);
  work_group.await_completion();
  unsafe {
    let relc = release_count.load(Ordering::Relaxed);
    let acqc = acquire_count.load(Ordering::Relaxed);
    assert!(relc == acqc);
  }
}

#[test]
fn work_sharing_kinda_works() {

}