use std::{iter::zip, mem::{align_of, size_of, MaybeUninit}, ptr::{drop_in_place, copy_nonoverlapping, addr_of}, cell::UnsafeCell, str::FromStr};


#[macro_export]
macro_rules! cast {
    ($Val:expr, $Ty:ty) => {
      {
        use core::mem::transmute;
        unsafe { transmute::<_, $Ty>($Val) }
      }
    };
}

pub fn high_order_pow2(number: u64) -> u64 {
  if number == 0 { return 0 }
  if number == 1 { return 1 }
  64u64 - (number - 1).leading_zeros() as u64
}
#[test]
fn valid_order_count() {
  let nums = [
    0, 1, 3, 5, 7, 11, 13, 17, 23];
  let orders = [
    0, 1, 2, 3, 3, 4, 4, 5, 5];
  for (n, o) in zip(nums, orders) {
    assert!(high_order_pow2(n) == o);
  }
}

#[test]
fn ex () {
  println!("{}", high_order_pow2(0))
}

pub fn ptr_align_dist<T>(ptr: *const T, align: usize) -> u64 {
  let ptrint = ptr as u64;
  let order = high_order_pow2(align as u64);
  let mul = ptrint >> order;
  let mut result = mul << order;
  if (result as u64) < ptrint { result += align as u64 };
  return result - ptrint;
}

pub fn num_align_dist(addr: u64, align: usize) -> u64 {
  let order = high_order_pow2(align as u64);
  let mul = addr >> order;
  let mut result = mul << order;
  if (result as u64) < addr { result += align as u64 };
  return result - addr;
}

#[test]
fn test_align_works() {
  let ptr = (8 * 7) as *mut u8;
  let m = ptr.align_offset(32);
  let k = ptr_align_dist(ptr, 32);
  println!("{} {}",m, k);
}

pub struct RestoreGuard<T>(UnsafeCell<(*mut T, bool)>);
impl <T> RestoreGuard<T> {
  pub fn consume(&self) -> T { unsafe {
    let this = &mut *self.0.get();
    assert!(!this.1);
    let value = this.0.read() ;
    this.1 = true;
    return value;
  } }
  pub fn assign(&self, new_value: T) { unsafe {
    let this = &mut *self.0.get();
    if !this.1 { drop_in_place(this.0) }
    this.0.write(new_value);
    this.1 = false;
  } }
}
pub fn with_scoped_consume<T, K>(
  source: &mut T, action: impl FnOnce(&RestoreGuard<T>) -> K
) -> K {
  let guard = RestoreGuard(UnsafeCell::new((source, false)));
  let result = action(&guard);
  let this = unsafe { &*guard.0.get() };
  assert!(!this.1, "Consumed value was not restored");
  return result;
}

struct Box<T>(T);
#[test]
fn quick_sanity_check(){
  let str = "Hello, ya loving rust too??";
  let mut val = Box(String::from_str(str).unwrap());
  with_scoped_consume(&mut val.0, |val|{
    let v = val.consume();
    assert!(v == String::from_str(str).unwrap());
    val.assign(String::from_str("yeah..").unwrap());
  });
  assert!(val.0 == String::from_str("yeah..").unwrap())
}
#[test]
fn no_double_free () {}

#[test]
fn guard_guards() {}

#[macro_export]
macro_rules! garbage {
    () => {
      {MaybeUninit::uninit().assume_init()}
    };
    ($ty:ty) => {
      {MaybeUninit::<$ty>::uninit().assume_init()}
    }
}


pub unsafe fn bitwise_copy<T>(val: &T) -> T {
  let mut interm = MaybeUninit::<T>::uninit();
  let source = cast!(val, *const T);
  copy_nonoverlapping(source, interm.as_mut_ptr(), 1);
  return interm.assume_init()
}

// #[macro_export]
// macro_rules! fuckborrowchecker {
//   ($expr:expr, $Ty:ty) => {
//     {
//       use std::mem::transmute;
//       let copied_mref = transmute::<_, u64>(&mut $expr);
//       move || { &mut *transmute::<_, *mut $Ty>(copied_mref) }
//     }
//   };
// }

// #[macro_export]
// macro_rules! unborrowcheck {
//   ($expr:expr, $Ty:ty) => {
//     {
//       use std::mem::transmute;
//       let copied_mref = transmute::<_, u64>($expr);
//       move || { &mut *transmute::<_, *mut $Ty>(copied_mref) }
//     }
//   };
// }