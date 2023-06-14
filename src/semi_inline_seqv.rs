use std::{cell::UnsafeCell, marker::PhantomData, ptr::{addr_of_mut, addr_of}, mem::forget};

use crate::{loopbuffer::InlineLoopBuffer, array::Array, utils::DrainablePageHolder};


pub struct SemiInlineSeqv<const InlineCapactity: usize, T>(
  UnsafeCell<Internals<InlineCapactity,T>>,
  PhantomData<T>);

struct Internals<const InlineCapactity: usize, T> {
  inlines: InlineLoopBuffer<InlineCapactity,T>,
  outlines: Array<T>
}

impl <const InlineCapactity: usize, T> SemiInlineSeqv<InlineCapactity, T> {
  pub fn new(page_source: *mut dyn DrainablePageHolder) -> Self {
    Self(UnsafeCell::new(
      Internals {
        inlines: InlineLoopBuffer::new(),
        outlines: Array::new(page_source) }),
      PhantomData)
  }
  pub fn push(&self, new_item: T) { unsafe {
    let this = &mut *self.0.get();
    let clone = addr_of!(new_item).read();
    let ok = this.inlines.push_to_tail(new_item);
    if !ok {
      this.outlines.push(clone)
    } else {
      forget(clone)
    }
  } }
  pub fn pop(&self) -> Option<T> { unsafe {
    let this = &mut *self.0.get();
    if let item@Some(_) = this.outlines.pop() {
      return item
    };
    if let item@Some(_) = this.inlines.pop_from_tail() {
      return item
    }
    return None
  } }
  pub fn item_count(&self) -> usize { unsafe {
    let this = &*self.0.get();
    this.inlines.item_count() + this.outlines.item_count()
  } }
}

pub trait SomeSemiInlineSeqv<T> {
  fn push(&self, new_item: T);
  fn pop(&self) -> Option<T>;
}

struct SemiInlineSeqvTraverser<'i, T> {
  related_object: &'i dyn SomeSemiInlineSeqv<T>
}

impl <const S:usize, T> DrainablePageHolder for SemiInlineSeqv<S, T> {
  fn try_drain_page(&mut self) -> Option<crate::root_alloc::Block4KPtr> { unsafe {
    let this = &mut *self.0.get();
    this.outlines.try_drain_page()
  } }
}