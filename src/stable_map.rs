
use std::{cmp::max,cell::UnsafeCell, marker::PhantomData, sync::{atomic::{AtomicU64, Ordering, fence}, Mutex}, ptr::{copy_nonoverlapping, addr_of_mut, null_mut, addr_of}, hash::Hasher, collections::{hash_map::DefaultHasher, HashMap}, alloc::{alloc, Layout, alloc_zeroed}, mem::{size_of, forget, MaybeUninit, needs_drop, align_of}, thread, time::{SystemTime, Duration}};
use core::hash::Hash;

use crate::utils::{ptr_align_dist, offset_to_higher_multiple};


struct StableMap<Key: Hash + Eq + Clone, Value>(
  UnsafeCell<StableMapInternals>,
  PhantomData<(Key, Value)>);

unsafe impl <Key: Hash + Eq + Clone, Value> Sync for StableMap<Key, Value> {}

impl <Key: Hash + Eq + Clone, Value> StableMap<Key, Value> {
  fn new() -> Self {
    Self(UnsafeCell::new(
      StableMapInternals {
        write_bucket: AtomicU64::new(0),
        wb_item_count: AtomicU64::new(0),
        tail_bucket: AtomicU64::new(0),
        count: AtomicU64::new(0) }), PhantomData)
  }
  fn kill_shadows() {
    // since some of the values may get shadowed because of
    // how insertion work we have to deal with the situation
    // where entries with identical hashes become ignored for a pretty long time.
    // for values that do not hold resources for disposal
    // that's absolutely not a problem, but if there's a shadowed
    // value that requires destructor call, we have to traverse the entire
    // map to find shadowed items. this is not as bad as it may seem cus
    // we may mark some entries as 'stop point' so that future shadow kill crusades will
    // not need to go deep every time this procedure runs.
    // shadow killing mayb also be run as async computation, it wont block things
    if needs_drop::<Value>() { todo!() }
  }
  fn item_count(&self) -> usize { unsafe {
    let this = &mut *self.0.get();
    return this.count.load(Ordering::Relaxed) as usize
  } }
  fn insert(&self, key: Key, value: Value) -> Option<Value> { unsafe {
    let obj = &*self.0.get();
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();
    assert!(hash != 0 && hash != u64::MAX);
    let mut result = MaybeUninit::<Value>::uninit();
    let did_replace = StableMap_insert_common_impl(
      obj,
      hash,
      size_of::<Value>(),
      align_of::<Value>(),
      addr_of!(value).cast(),
      result.as_mut_ptr().cast());
    forget(value);
    if did_replace {
      return Some(result.assume_init())
    }
    return None
  }; }
  fn mref_item_at_index(&self, key: Key) -> Option<MapItemRef<Value>> { unsafe {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();
    let obj = &*self.0.get();
    let mut wb = MaybeUninit::uninit().assume_init();
    let did_find = StableMap_mref_item_at_index_common_impl(
      obj, hash, size_of::<Value>(),
      align_of::<Value>(), &mut wb,);
    if did_find {
      let (meta, data) = wb;
      let ref_ = MapItemRef { data: data.cast(), mtd: meta };
      return Some(ref_)
    }
    return None
  };}
  fn with_inserting<R>(
    key: Key,
    new_value: Value,
    on_collision: impl FnOnce(*mut Value, Value) -> R
  ) -> Option<R> {
    todo!()
  }
}

#[inline(never)]
fn StableMap_mref_item_at_index_common_impl(
  object: &StableMapInternals,
  hash: u64,
  value_size: usize,
  value_align: usize,
  write_back: &mut (*mut AtomicU64, *mut u8),
) -> bool { unsafe {

  let this = object;
  let mut current_read_bucket ;
  loop {
    current_read_bucket = this.tail_bucket.load(Ordering::Relaxed);
    match current_read_bucket {
      0 => {return false} ,
      u64::MAX => continue,
      _ => {
        fence(Ordering::SeqCst);
        break
      }
    }
  }
  let mut slot_size = 8usize;
  let dist_to_data = offset_to_higher_multiple(slot_size as u64, value_align) as usize;
  slot_size += value_size + dist_to_data;
  let slot_size = slot_size as usize;
  let mut consumed_slot_count = max(1, size_of::<BucketMetadata>() / slot_size);
  if consumed_slot_count * slot_size < size_of::<BucketMetadata>() {
    consumed_slot_count += 1;
  }
  loop {

    let current_bucket_mtd_mref = &*(current_read_bucket as *mut u8).cast::<BucketMetadata>();
    let bucket_byte_size = 4096u64 << current_bucket_mtd_mref.get_size_order();
    let slot_count =
      (bucket_byte_size / slot_size as u64) - consumed_slot_count as u64;
    let slot_index = hash % slot_count ;

    let slot_ptr = (current_read_bucket as *mut u8)
      .add(consumed_slot_count * slot_size)
      .add(slot_index as usize * slot_size);
    let meta_ptr = slot_ptr.cast::<AtomicU64>();
    let meta = &*meta_ptr;
    let mtd_in_slot = meta.load(Ordering::Relaxed);

    let hash_in_slot = mtd_in_slot >> 1;
    let matched = hash_in_slot == hash & !(1u64 << 63);
    if matched {
      let data = slot_ptr.add(8 + dist_to_data);
      *write_back = (meta_ptr, data);
      return true;
    } else {
      // go to previous bucket
      fence(Ordering::Acquire); // see allocs
      let previous = current_bucket_mtd_mref.get_previos_bucket_addr();
      if previous == null_mut() {
        return false
      }
      current_read_bucket = previous as _;
      continue;
    }
  }
}; }

#[inline(never)]
fn StableMap_insert_common_impl(
  object: &StableMapInternals,
  hash: u64,
  value_size: usize,
  value_align: usize,
  new_value: *const u8,
  write_back: *mut u8,
) -> bool { unsafe {

  let this = object;
  this.count.fetch_add(1, Ordering::Relaxed); // always succeeds
  let mut current_write_bucket = this.write_bucket.load(Ordering::Relaxed);
  match current_write_bucket {
    0 => {
      current_write_bucket = this.perform_late_init() as u64;
    },
    u64::MAX => {
      loop {
        current_write_bucket = this.write_bucket.load(Ordering::Relaxed);
        if current_write_bucket == u64::MAX { continue; }
        break;
      }
    },
    _ => (),
  }
  fence(Ordering::Acquire);
  let mut slot_size = 8usize;
  let dist_to_data = offset_to_higher_multiple(slot_size as u64, value_align) as usize;
  slot_size += value_size + dist_to_data;
  let slot_size = slot_size as usize;
  let mut consumed_slot_count = max(1, size_of::<BucketMetadata>() / slot_size);
  if consumed_slot_count * slot_size < size_of::<BucketMetadata>() {
    consumed_slot_count += 1;
  }
  'bucket_jumping: loop {
    assert!(current_write_bucket != u64::MAX);
    let current_bucket_mtd_mref = &*(current_write_bucket as *mut u8).cast::<BucketMetadata>();
    let bucket_byte_size = 4096u64 << current_bucket_mtd_mref.get_size_order();
    let slot_count =
      (bucket_byte_size / slot_size as u64) - consumed_slot_count as u64;
    let slot_index = hash % slot_count ;

    let slot_ptr = (current_write_bucket as *mut u8)
      .add(consumed_slot_count * slot_size)
      .add(slot_index as usize * slot_size);
    let meta = slot_ptr.cast::<AtomicU64>();
    let data = slot_ptr.add(8 + dist_to_data);
    let meta = &*meta;

    let meta_value = meta.compare_exchange(
      0, 1, Ordering::SeqCst, Ordering::Relaxed);
    match meta_value {
      Err(mut actual) => {
        let mut hash_in_slot ;
        loop {
          hash_in_slot = actual >> 1;
          if hash_in_slot == 0 {
            actual = meta.load(Ordering::Relaxed);
            continue;
          }
          break;
        }
        let hashes_match = hash_in_slot == hash & (!0u64 >> 1);
        if hashes_match {
          // lock this slot
          while meta.fetch_or(1, Ordering::Relaxed) & 1 == 1 {}
          fence(Ordering::Acquire); // see what value last thread stored there
          copy_nonoverlapping(data,write_back,value_size);
          copy_nonoverlapping(new_value,data, value_size);
          meta.fetch_and(!0 << 1, Ordering::Release);
          return true
        } else {
          // slot is occupied but hashed dont match.
          // goto next bucket and try there.
          let buck_pop = this.wb_item_count.fetch_add(1, Ordering::Relaxed) + 1;
          let proc = (100 / slot_count) * buck_pop;
          let time_to_replace = proc >= 70;

          // lets probe next bucket
          let outcome = current_bucket_mtd_mref.2.compare_exchange(
            0, u64::MAX, Ordering::SeqCst, Ordering::SeqCst);
          match outcome {
            Err(actual) => { // next bucket exist
              let actual = if actual == u64::MAX {
                // but now it is being allocated by another thread
                loop {
                  let actual = current_bucket_mtd_mref.2.load(Ordering::Relaxed);
                  if actual == u64::MAX { continue; }
                  break actual; // alloc has ended
                }
              } else { actual };
              fence(Ordering::Acquire); // see the allocation as happened
              current_write_bucket = actual;
              if time_to_replace {
                this.write_bucket.store(actual, Ordering::Relaxed);
              }
              continue 'bucket_jumping;
            },
            Ok(_) => { // there isnt a next bucket, we must make one
              let mut next_order = current_bucket_mtd_mref.get_size_order();
              if next_order != 8 { next_order += 1 } // max size of the bucket is 1 MB
              let real_size = 4096usize << next_order;
              let mem = alloc(
                Layout::from_size_align(real_size, 4096).unwrap());
              mem.write_bytes(0, real_size);
              let meta = &mut *mem.cast::<BucketMetadata>();
              meta.set_previos_bucket_addr(current_write_bucket as _);
              meta.set_size_order(next_order);
              fence(Ordering::Release); // publish allocation
              current_bucket_mtd_mref.2.store(mem as _, Ordering::Relaxed);
              this.tail_bucket.store(mem as _, Ordering::SeqCst);
              if time_to_replace {
                this.write_bucket.store(mem as _, Ordering::Relaxed);
              }
              current_write_bucket = mem as _;
              continue 'bucket_jumping
            }
          }
        }
      },
      Ok(_) => { // we have locked the empty slot
        copy_nonoverlapping(new_value,data,value_size);
        meta.store(hash << 1, Ordering::Release);
        return false;
      }
    }
  }
}; }

struct MapItemRef<T> {
  data: *mut T,
  mtd: *const AtomicU64
}
impl <T> MapItemRef<T> {
  fn replace(&self, new_item: T) -> T { todo!() }
  // returns true if failed
  fn try_access(&self, action: impl FnOnce(&mut T) -> ()) -> bool { unsafe {
    let mtd = &*self.mtd;
    let data_ref = &mut *self.data;
    let mtd_in_slot = mtd.fetch_or(1, Ordering::Relaxed);
    let already_locked = mtd_in_slot & 1 != 0;
    if already_locked { return false }
    fence(Ordering::Acquire);
    action(data_ref);
    mtd.fetch_and(!0, Ordering::Release);
    return true
  }; }
  fn remove(&self) { todo!() }
}

struct Slot<V> {
  meta: AtomicU64,
  value: V
}

struct StableMapInternals {
  write_bucket: AtomicU64,
  wb_item_count: AtomicU64,
  tail_bucket: AtomicU64,
  count: AtomicU64,
}
impl StableMapInternals {
  #[inline(never)]
  fn perform_late_init(&self) -> *mut u8 { unsafe {
    let this = self;
    let outcome = this.write_bucket.compare_exchange(
      0, u64::MAX, Ordering::SeqCst, Ordering::SeqCst);
    match outcome {
      Err(actual) => {
        let taken_for_init = actual == u64::MAX;
        if taken_for_init {
          loop {
            let smth = this.write_bucket.load(Ordering::Relaxed);
            if smth == u64::MAX { continue; }
            fence(Ordering::Acquire);
            return smth as *mut u8
          }
        }
        fence(Ordering::Acquire);
        return actual as *mut u8;
      },
      Ok(_) => {
        let mem = alloc_zeroed(Layout::from_size_align_unchecked(4096, 4096));
        let mtd = &mut *mem.cast::<BucketMetadata>();
        mtd.set_previos_bucket_addr(null_mut());
        mtd.2.store(0, Ordering::Relaxed);
        mtd.set_size_order(0);
        fence(Ordering::Release);
        this.tail_bucket.store(mem as _, Ordering::Relaxed);
        this.write_bucket.store(mem as _, Ordering::Relaxed);
        return mem
      }
    }
  } }
}

struct BucketMetadata([u8;2],[u8;6],AtomicU64);

impl BucketMetadata {
  fn set_previos_bucket_addr(&mut self, addr: *mut u8) { unsafe {
    copy_nonoverlapping(addr_of!(addr).cast::<u8>(), addr_of_mut!(self.1).cast::<u8>(), 6);
  } }
  fn get_previos_bucket_addr(&self) -> *mut u8 {
    let mut ptr : *mut u8 = null_mut();
    let byte_source = self.1.as_ptr();
    let byte_sink = addr_of_mut!(ptr).cast::<u8>();
    unsafe { copy_nonoverlapping(byte_source, byte_sink, 6) }
    return ptr;
  }
  fn set_size_order(&mut self, order: u8) {
    self.0[0] = order;
  }
  fn get_size_order(&self) -> u8 {
    self.0[0]
  }
  fn get_next_bucket_ptr(&self) -> *mut u8 {
    let val = self.2.load(Ordering::Relaxed);
    let val = val as u64;
    let val = val & (!0u64 >> 1);
    return val as *mut u8
  }

}



#[test]
fn single_thread_inout() {
  let map = StableMap::<u64, u64>::new();
  let limit = 10000;
  for i in 0 .. limit {
    let outcome = map.insert(i, i);
    if let Some(_) = outcome { panic!() }
  }
  for i in 0 .. limit {
    let smth = map.mref_item_at_index(i);
    if let Some(val) = smth {
      let mut v = None;
      let ok = val.try_access(|vl| v = Some(*vl));
      assert!(ok);
      if let Some(val) = v { assert!(val == i) } else {
        panic!() }
    } else {
      panic!() };
  }
}

#[test]
fn single_thread_insertion_and_search_timing() {
  let map = StableMap::<u64, u64>::new();
  let limit = 10000;
  let begin = SystemTime::now();
  for i in 0 .. limit {
    let outcome = map.insert(i, i);
    if let Some(_) = outcome { panic!() }
  }
  let diff_ = begin.elapsed().unwrap().as_micros();
  println!("{diff_} micros spent on inserting {limit} elements in map");
  let begin = SystemTime::now();
  for i in 0 .. limit {
    let smth = map.mref_item_at_index(i);
    if let Some(val) = smth {
      let mut v = None;
      let ok = val.try_access(|vl| v = Some(*vl));
      assert!(ok);
      if let Some(val) = v { assert!(val == i) } else {
        panic!() }
    } else {
      panic!() };
  }
  let diff = begin.elapsed().unwrap().as_micros();
  println!("{diff} micros spent on searching {limit} elements in map");
  println!("{} micros in total", diff + diff_);

  let mut map = HashMap::new();
  let begin = SystemTime::now();
  for i in 0 .. limit {
    let outcome = map.insert(i, i);
    if let Some(_) = outcome { panic!() }
  }
  let diff_ = begin.elapsed().unwrap().as_micros();
  println!("{diff_} micros spent on inserting {limit} elements in map");
  let begin = SystemTime::now();
  for i in 0 .. limit {
    let item = map.get(&i).unwrap();
    assert!(*item == i)
  }
  let diff = begin.elapsed().unwrap().as_micros();
  println!("{diff} micros spent on searching {limit} elements in map");
  println!("{} micros in total", diff + diff_)
}

#[test]
fn multi_thread_insertion_and_search_timing() {
  let map = StableMap::<u64, u64>::new();
  let limit = 1000;
  let thread_count = 4;
  let begin = SystemTime::now();
  thread::scope(|scope|{
    let split = limit;
    for i in 0 .. thread_count {
      let copied = &map;
      scope.spawn(move ||{
        for k in (i * split) .. ((i * split) + split) {
          let old = copied.insert(k, k);
          if let Some(_) = old { panic!() }
        }
      });
    }
  });
  let diff_ = begin.elapsed().unwrap().as_micros();
  println!(
    "{} micros spent on inserting {} elements in the map from {} threads",
    diff_, limit * thread_count, thread_count);
  println!("Item count is {}", map.item_count());
  let begin = SystemTime::now();
  for i in 0 .. (limit * thread_count) {
    let smth = map.mref_item_at_index(i);
    if let Some(val) = smth {
      let mut v = None;
      let ok = val.try_access(|vl| v = Some(*vl));
      assert!(ok);
      if let Some(val) = v { assert!(val == i) } else {
        panic!() }
    } else {
      panic!() };
  }
  let diff = begin.elapsed().unwrap().as_micros();
  println!(
    "{} micros spent on searching {} elements in map from 1 thread",
    diff, limit * thread_count);
  println!("{} micros in total for table", diff + diff_);

  let mut map = Mutex::new(HashMap::<u64, u64>::new());
  let begin = SystemTime::now();
  thread::scope(|scope|{
    let split = limit;
    for i in 0 .. thread_count {
      let copied = &map;
      scope.spawn(move ||{
        for k in (i * split) .. ((i * split) + split) {
          let old = copied.lock().unwrap().insert(k, k);
          if let Some(_) = old { panic!() }
        }
      });
    }
  });
  let diff_ = begin.elapsed().unwrap().as_micros();
  println!(
    "{} micros spent on inserting {} elements in map from {} threads",
    diff_, limit *thread_count, thread_count);
  let begin = SystemTime::now();
  for i in 0 .. (limit * thread_count) {
    let item = map.get_mut().unwrap().get(&i).unwrap();
    assert!(*item == i)
  }
  let diff = begin.elapsed().unwrap().as_micros();
  println!(
    "{} micros spent on searching {} elements in map from 1 thread",
    diff, limit * thread_count);
  println!("{} micros in total for hashmap", diff + diff_)
}

#[test]
fn no_crap_with_the_map() {
  let mut find_fail_count = 0;
  for _ in 0 .. 100 {
    let map = StableMap::<u64, u64>::new();
    let limit = 1000;
    let thread_count = 4;
    let join_point: AtomicU64 = AtomicU64::new(0);
    let jp = &join_point;
    thread::scope(|scope|{
      let split = limit;
      for i in 0 .. thread_count {
        let copied = &map;
        let jp = jp;
        scope.spawn(move ||{
          for k in (i * split) .. ((i * split) + split) {
            let old = copied.insert(k, k);
            if let Some(_) = old { panic!() }
          }
          let _ = jp.fetch_add(1, Ordering::Release);
        });
      }
    });
    while join_point.load(Ordering::Acquire) != thread_count {}
    for i in 0 .. (limit * thread_count) {
      let smth = map.mref_item_at_index(i);
      if let Some(val) = smth {
        let mut v = None;
        let ok = val.try_access(|vl| v = Some(*vl));
        assert!(ok, "not ok");
        if let Some(val) = v { assert!(val == i) } else {
          panic!() }
      } else {
        find_fail_count += 1 };
    }
  }
  println!("failed to find {find_fail_count} items");
  assert!(find_fail_count == 0);
}

