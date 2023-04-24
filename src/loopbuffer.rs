use std::{mem::{MaybeUninit, size_of, forget}, cell::UnsafeCell, ptr::{addr_of_mut, copy_nonoverlapping, addr_of}};



// non-thread safe, bounded queue.
// pushes and pops do not invalidate refs to this object.
pub struct InlineLoopBuffer<const Capacity:usize, T>(
  UnsafeCell<InlineLoopBufferData<Capacity, T>>);
struct InlineLoopBufferData<const Capacity:usize, T> {
  items: [MaybeUninit<T>; Capacity],
  write_index: usize,
  read_index: usize,
  item_count: usize,
}
trait InlineLoopBufferDataAccessorImpl {
  fn get_internals(&mut self)
    -> (*mut u8, &mut usize, &mut usize, &mut usize);
}

impl <const Capacity:usize, T>
  InlineLoopBufferDataAccessorImpl
  for InlineLoopBufferData<Capacity, T> {

  fn get_internals(&mut self)
    -> (*mut u8, &mut usize, &mut usize, &mut usize) {

    (
      addr_of_mut!(self.items).cast(),
      &mut self.write_index,
      &mut self.read_index,
      &mut self.item_count
    )
  }
}

impl <const Capacity:usize, T> InlineLoopBuffer<Capacity, T> {
  pub fn new() -> Self { unsafe {
    Self(UnsafeCell::new(
      InlineLoopBufferData {
        items: MaybeUninit::uninit().assume_init(),
        write_index: 0,
        read_index: 0,
        item_count: 0 }))
  } }
  // true if pushing was successful
  pub fn push(&self, new_item: T) -> bool { unsafe {
    let this = &mut *self.0.get();
    let result = InlineLoopBuffer_push_impl(
      this, addr_of!(new_item).cast(), size_of::<T>(), Capacity);
    forget(new_item);
    return result
  } }
  pub fn pop(&self) -> Option<T> { unsafe {
    let this = &mut *self.0.get();
    let mut result = MaybeUninit::<(T, bool)>::uninit();
    let result_mref = &mut *result.as_mut_ptr();
    let result_addr = addr_of_mut!(result_mref.0);
    InlineLoopBuffer_pop_impl(
      this, size_of::<T>(), Capacity, (result_addr.cast(), &mut result_mref.1));
    let (value, did_write) = result.assume_init();
    if did_write { return Some(value) }
    return None
  }; }
  pub fn item_count(&self) -> usize {
    unsafe { (&*self.0.get()).item_count }
  }
}

#[inline(never)]
fn InlineLoopBuffer_push_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  new_item_addr: *const u8,
  item_byte_size: usize,
  max_capacity: usize,
) -> bool { unsafe {
  let (storage_ptr, write_index, _, item_count) = object.get_internals();
  if *item_count == max_capacity { return false };
  let slot_ptr = storage_ptr.add(*write_index * item_byte_size);
  copy_nonoverlapping(new_item_addr, slot_ptr, item_byte_size);
  let mut new_index = *write_index + 1;
  if new_index == max_capacity { new_index = 0 }
  *write_index = new_index;
  *item_count += 1;
  return true
}; }

#[inline(never)]
fn InlineLoopBuffer_pop_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  item_byte_size: usize,
  max_capacity: usize,
  result_loc: (*mut u8, &mut bool)
) { unsafe {
  let (storage_ptr, _, read_index, item_count) = object.get_internals();
  if *item_count == 0 { *result_loc.1 = false; return }
  let slot_ptr = storage_ptr.add(*read_index * item_byte_size);
  copy_nonoverlapping(slot_ptr, result_loc.0, item_byte_size);
  let mut new_read_index = *read_index + 1;
  if new_read_index == max_capacity { new_read_index = 0 };
  *read_index = new_read_index;
  *item_count -= 1;
  *result_loc.1 = true;
} }



#[test]
fn inout_items() {
  const ITEM_COUNT: usize = 255;
  let items = InlineLoopBuffer::<ITEM_COUNT, usize>::new();
  for i in 0 .. ITEM_COUNT {
    let did_push = items.push(i);
    assert!(did_push);
  }
  let did_push = items.push(usize::MAX);
  assert!(!did_push);
  for i in 0 .. ITEM_COUNT {
    let val = items.pop();
    if let Some(k) = val {
      assert!(k == i)
    } else { panic!() }
  }
  let pop = items.pop();
  if let Some(_) = pop { panic!() }
}