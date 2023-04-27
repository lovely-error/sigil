
use std::{cmp::max,cell::UnsafeCell, marker::PhantomData, sync::atomic::{AtomicU64, Ordering, fence}, ptr::{copy_nonoverlapping, addr_of_mut, null_mut, addr_of}, hash::Hasher, collections::hash_map::DefaultHasher, alloc::{alloc, Layout, alloc_zeroed}, mem::{size_of, forget, MaybeUninit, needs_drop}, thread};
use core::hash::Hash;


struct StableMap<Key: Hash + Eq + Clone, Value>(
  UnsafeCell<StableMapInternals>,
  PhantomData<(Key, Value)>);

impl <Key: Hash + Eq + Clone, Value> StableMap<Key, Value> {
  fn new() -> Self {
    Self(UnsafeCell::new(
      StableMapInternals {
        head_bucket: 0,
        write_bucket: AtomicU64::new(0),
        wb_item_count: AtomicU64::new(0),
        count: AtomicU64::new(0) }), PhantomData)
  }
  fn kill_shadows() {
    // since some of the values may get shadowed because of
    // how insertion work we have to deal with the situation
    // where entries with identical hashes become ignored for a pretty long time.
    // for values that do not hold resources for disposal
    // that's absolutely not a problem, but if there's a shadowed
    // value that requires destructor call, we have to traverse the entire
    // map to the end if no shadowing has occured
  }
  fn perform_late_init(&self) { unsafe {
    let this = &mut *self.0.get();
    let outcome = this.write_bucket.compare_exchange(
      0, u64::MAX, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Err(actual) => {
        let taken_for_init = actual == u64::MAX;
        if taken_for_init { while this.write_bucket.load(Ordering::Relaxed) == u64::MAX {} }
        fence(Ordering::Acquire);
      },
      Ok(_) => {
        let mem = alloc_zeroed(Layout::from_size_align_unchecked(4096, 4096));
        let mtd = &mut *mem.cast::<BucketMetadata>();
        mtd.set_previos_bucket_addr(null_mut());
        mtd.2.store(0, Ordering::Relaxed);
        mtd.set_size_order(0);
        this.write_bucket.store(mem as u64, Ordering::Release);
      }
    }
  } }
  fn _mref_item_at_index(&self, key: Key) -> Option<MapItemRef<Value>> { unsafe {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();
    assert!(hash != 0 && hash != u64::MAX);

    let this = &mut *self.0.get();
    let mut current_read_bucket ;
    loop {
      current_read_bucket = this.write_bucket.load(Ordering::Relaxed);
      match current_read_bucket {
        0 => return None,
        u64::MAX => continue,
        _ => { fence(Ordering::Acquire); break }
      }
    }
    let slot_size = size_of::<Slot<Key, Value>>();
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

      let data_ptr = (current_read_bucket as *mut u8)
        .add(consumed_slot_count)
        .add(slot_index as usize * slot_size);
      let data_ptr = data_ptr.cast::<Slot<Key, Value>>();
      let data_ref = &mut *data_ptr;

      let mut value_there;
      loop {
        // fixme:this is terrific approach to lock minimisation
        value_there = data_ref.meta.load(Ordering::Relaxed);
        match value_there {
          0 => return None,
          u64::MAX => continue,
          _ => { break }
        }
      }
      let hash_there = value_there >> 1;
      let matched = hash_there == hash & !(1u64 << 63);
      if matched {
        fence(Ordering::Acquire);
        let ref_ = MapItemRef {
          data: addr_of_mut!(data_ref.value),
          mtd: addr_of_mut!(data_ref.meta),
          hash
        };
        return Some(ref_)
      } else {
        // go to previous bucket
        let previous = current_bucket_mtd_mref.get_previos_bucket_addr();
        if previous == null_mut() { return None }
        current_read_bucket = previous as _;
        continue;
      }
    }
  }; }
  fn mref_item_at_index(&self, key: Key) -> Option<MapItemRef<Value>> { unsafe {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();
    assert!(hash != 0 && hash != u64::MAX);

    let this = &mut *self.0.get();
    let mut current_read_bucket ;
    loop {
      current_read_bucket = this.write_bucket.load(Ordering::Relaxed);
      match current_read_bucket {
        0 => return None,
        u64::MAX => continue,
        _ => { fence(Ordering::Acquire); break }
      }
    }
    let slot_size = size_of::<Slot<Key, Value>>();
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
        .add(consumed_slot_count)
        .add(slot_index as usize * slot_size);
      let slot_ptr = slot_ptr.cast::<Slot<Key, Value>>();
      let slot_ref = &mut *slot_ptr;

      let mtd_in_slot = slot_ref.meta.load(Ordering::Relaxed);
      if mtd_in_slot == 0 { return None }

      let hash_in_slot = mtd_in_slot >> 1;
      let matched = hash_in_slot == hash & !(1u64 << 63);
      if matched {
        let ref_ = MapItemRef {
          data: addr_of_mut!(slot_ref.value),
          mtd: addr_of_mut!(slot_ref.meta),
        };
        return Some(ref_)
      } else {
        // go to previous bucket
        let previous = current_bucket_mtd_mref.get_previos_bucket_addr();
        if previous == null_mut() { return None }
        current_read_bucket = previous as _;
        continue;
      }
    }
  }; }
  fn _insert(&self, key: Key, value: Value) -> Option<Value> { unsafe {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();

    let this = &mut *self.0.get();
    this.count.fetch_add(1, Ordering::Relaxed); // always succeeds
    let mut current_write_bucket = this.write_bucket.load(Ordering::Relaxed);
    if current_write_bucket == 0 {
      self.perform_late_init();
      current_write_bucket = this.write_bucket.load(Ordering::Relaxed);
    }
    let slot_size = size_of::<Slot<Key, Value>>();
    let mut consumed_slot_count = max(1, size_of::<BucketMetadata>() / slot_size);
    if consumed_slot_count * slot_size < size_of::<BucketMetadata>() {
      consumed_slot_count += 1;
    }
    'bucket_jumping: loop {

      let current_bucket_mtd_mref = &*(current_write_bucket as *mut u8).cast::<BucketMetadata>();
      let bucket_byte_size = 4096u64 << current_bucket_mtd_mref.get_size_order();
      let slot_count =
        (bucket_byte_size / slot_size as u64) - consumed_slot_count as u64;
      let slot_index = hash % slot_count ;

      let data_ptr = (current_write_bucket as *mut u8)
        .add(consumed_slot_count)
        .add(slot_index as usize * slot_size);
      let data_ptr = data_ptr.cast::<Slot<Key, Value>>();
      let data_ref = &mut *data_ptr;
      loop {
        // try aquire the slot assuming that it is initially empty
        let outcome = data_ref.meta.compare_exchange(
          0, u64::MAX, Ordering::Relaxed, Ordering::Relaxed);
        match outcome {
          Err(actual) => { // it is not empty
            if actual == u64::MAX { // it is already locked by someone else
              while data_ref.meta.load(Ordering::Relaxed) == u64::MAX {} // wait til unlocking has happened
            };
            if needs_drop::<Value>() {
              // deal with the shadows
            }
            let hash_there = actual >> 1;
            let matched = hash_there == hash & (!0u64 >> 1);
            if matched { // we have to do replace
              loop {
                // try to put lock on slot
                let outcome = data_ref.meta.compare_exchange(
                  actual, u64::MAX, Ordering::Relaxed, Ordering::Relaxed);
                match outcome {
                  Err(_) => { // someone else has already locked this slot
                    if actual == 0 { return None } // someone has removed this item
                    continue;
                  },
                  Ok(_) => break // we own the slot now
                }
              };
              fence(Ordering::Acquire); // see what other threads did store in slot
              let mut val : Value = MaybeUninit::uninit().assume_init();
              copy_nonoverlapping(
                addr_of!(data_ref.value), addr_of_mut!(val), size_of::<Value>());
              copy_nonoverlapping(
                addr_of!(value), addr_of_mut!(data_ref.value), size_of::<Value>());
              data_ref.meta.store(actual, Ordering::Release); // release the lock and publish changes
              forget(value);
              return Some(val)
            } else {
              // lets try our luck in another bucket
              // check if bucket is too populated
              let buck_pop = this.wb_item_count.fetch_add(1, Ordering::Relaxed) + 1;
              let proc = (100 / slot_count) * buck_pop;
              let time_to_replace = proc >= 70;

              let outcome = current_bucket_mtd_mref.2.compare_exchange(
                0, u64::MAX, Ordering::Relaxed, Ordering::Relaxed);
              match outcome {
                Err(actual) => { // someone is busy allocating next bucket
                  let actual = if actual == u64::MAX {
                    loop {
                      let actual = current_bucket_mtd_mref.2.load(Ordering::Relaxed);
                      if actual == u64::MAX { continue; }
                      break actual;
                    }
                  } else { actual };
                  fence(Ordering::Acquire); // see the allocating as happened
                  current_write_bucket = actual;
                  if time_to_replace {
                    this.write_bucket.store(actual, Ordering::Relaxed);
                  }
                  continue 'bucket_jumping;
                },
                Ok(_) => { // there isnt a next bucket, we must make one
                  let mut next_order = current_bucket_mtd_mref.get_size_order();
                  if next_order != 8 { next_order += 1 } // max size of the bucket is 1 MB
                  let real_size = (4096u64 << next_order) as usize;
                  let mem = alloc(
                    Layout::from_size_align(real_size, 4096).unwrap());
                  mem.write_bytes(0, real_size);
                  let meta = &mut *mem.cast::<BucketMetadata>();
                  meta.set_previos_bucket_addr(current_write_bucket as _);
                  meta.set_size_order(next_order);
                  current_bucket_mtd_mref.2.store(mem as _, Ordering::Release); // publish allocation
                  current_write_bucket = mem as _;
                  if time_to_replace {
                    this.write_bucket.store(mem as _, Ordering::Relaxed);
                  }
                  continue 'bucket_jumping
                }
              }
            }
          }
          Ok(_) => { // yay, we are lucky this time
            copy_nonoverlapping(
              addr_of!(value), addr_of_mut!(data_ref.value), size_of::<Value>());
            forget(value);
            let hash = hash << 1;
            data_ref.meta.store(hash, Ordering::Release);
            return None
          }
        }
      }
    }
  }; }

  fn insert(&self, key: Key, value: Value) -> Option<Value> { unsafe {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let hash = hasher.finish();

    let this = &mut *self.0.get();
    this.count.fetch_add(1, Ordering::Relaxed); // always succeeds
    let mut current_write_bucket = this.write_bucket.load(Ordering::Acquire);
    if current_write_bucket == 0 {
      self.perform_late_init();
      current_write_bucket = this.write_bucket.load(Ordering::Relaxed);
    }
    let slot_size = size_of::<Slot<Key, Value>>();
    let mut consumed_slot_count = max(1, size_of::<BucketMetadata>() / slot_size);
    if consumed_slot_count * slot_size < size_of::<BucketMetadata>() {
      consumed_slot_count += 1;
    }
    'bucket_jumping: loop {

      let current_bucket_mtd_mref = &*(current_write_bucket as *mut u8).cast::<BucketMetadata>();
      let bucket_byte_size = 4096u64 << current_bucket_mtd_mref.get_size_order();
      let slot_count =
        (bucket_byte_size / slot_size as u64) - consumed_slot_count as u64;
      let slot_index = hash % slot_count ;

      let slot_ptr = (current_write_bucket as *mut u8)
        .add(consumed_slot_count)
        .add(slot_index as usize * slot_size);
      let data_ptr = slot_ptr.cast::<Slot<Key, Value>>();
      let slot_ref = &mut *data_ptr;
      let mut locked_by_us = false;
      loop {
        let prior = slot_ref.meta.load(Ordering::Relaxed);
        if prior == 0 { // free
          let prior = slot_ref.meta.fetch_or(1, Ordering::Relaxed);
          let got_locked = prior & 1 != 0;
          if got_locked {
            while slot_ref.meta.fetch_or(1, Ordering::Relaxed) & 1 != 0 {}
            locked_by_us = true;
            continue;
          }
          // store in empty slot
          copy_nonoverlapping(addr_of!(value), addr_of_mut!(slot_ref.value), size_of::<Value>());
          slot_ref.meta.store(hash << 1, Ordering::Release);
          forget(value);
          return None
        }
        // something is here
        let hash_in_slot = prior >> 1;
        let matched = hash & (!0u64 >> 1) == hash_in_slot;
        if matched {
          if !locked_by_us {
            loop {
              let prior = slot_ref.meta.fetch_or(1, Ordering::Relaxed);
              let already_locked = prior & 1 != 0;
              if already_locked { continue }
              break;
            }
          }
          fence(Ordering::Acquire);
          let mut old : Value = MaybeUninit::uninit().assume_init();
          copy_nonoverlapping(addr_of!(slot_ref.value), addr_of_mut!(old), size_of::<Value>());
          copy_nonoverlapping(addr_of!(value), addr_of_mut!(slot_ref.value), size_of::<Value>());
          slot_ref.meta.fetch_and(!0, Ordering::Release);
          forget(value);
          return Some(old)
        } else {
          // next bucket awaits!
          let buck_pop = this.wb_item_count.fetch_add(1, Ordering::Relaxed) + 1;
          let proc = (100 / slot_count) * buck_pop;
          let time_to_replace = proc >= 70;

          let outcome = current_bucket_mtd_mref.2.compare_exchange(
            0, u64::MAX, Ordering::Relaxed, Ordering::Relaxed);
          match outcome {
            Err(actual) => { // someone is busy allocating next bucket
              let actual = if actual == u64::MAX {
                loop {
                  let actual = current_bucket_mtd_mref.2.load(Ordering::Relaxed);
                  if actual == u64::MAX { continue; }
                  break actual;
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
              let real_size = (4096u64 << next_order) as usize;
              let mem = alloc(
                Layout::from_size_align(real_size, 4096).unwrap());
              mem.write_bytes(0, real_size);
              let meta = &mut *mem.cast::<BucketMetadata>();
              meta.set_previos_bucket_addr(current_write_bucket as _);
              meta.set_size_order(next_order);
              current_bucket_mtd_mref.2.store(mem as _, Ordering::Release); // publish allocation
              current_write_bucket = mem as _;
              if time_to_replace {
                this.write_bucket.store(mem as _, Ordering::Release);
              }
              continue 'bucket_jumping
            }
          }
        }
      }
    }
  }; }
}

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
    action(data_ref);
    mtd.fetch_and(!0, Ordering::Release);
    return true
  }; }
  fn remove(&self) { todo!() }
}

struct Slot<K, V> {
  meta: AtomicU64,
  key: K,
  value: V
}

struct StableMapInternals {
  head_bucket: u64,
  write_bucket: AtomicU64,
  wb_item_count: AtomicU64,
  count: AtomicU64,
}

struct BucketMetadata([u8;6],[u8;2],AtomicU64);

impl BucketMetadata {
  fn set_previos_bucket_addr(&mut self, addr: *mut u8) { unsafe {
    copy_nonoverlapping(&addr, addr_of_mut!(self.0).cast(), 6);
  } }
  fn get_previos_bucket_addr(&self) -> *mut u8 {
    let mut ptr = null_mut();
    unsafe { copy_nonoverlapping(addr_of!(self.0).cast(), addr_of_mut!(ptr), 6) }
    return ptr;
  }
  fn set_size_order(&mut self, order: u8) {
    self.1[0] = order;
  }
  fn get_size_order(&self) -> u8 {
    self.1[0]
  }
  fn get_next_bucket_ptr(&self) -> *mut u8 {
    let val = self.2.load(Ordering::Relaxed);
    let val = val as u64;
    let val = val & (!0u64 >> 1);
    return val as *mut u8
  }

}



#[test]
fn single_thread_inserts() {
  let map = StableMap::<u64, u64>::new();
  let limit = 100;
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
      if let Some(val) = v { assert!(val == i) } else { panic!() }
    } else { panic!() };
  }
}

#[test]
fn sooqa() { unsafe {
  let l = Layout::from_size_align(16384, 4096).unwrap();
  let mem = alloc(l) ;
  mem.write_bytes(u8::MAX, 16384);
  println!("{:?}", *mem.cast::<[u8;16384]>())
} }