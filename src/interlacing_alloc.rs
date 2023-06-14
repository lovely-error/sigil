use std::{marker::PhantomData, ptr::{copy_nonoverlapping, addr_of, addr_of_mut, null_mut}, mem::{size_of, align_of}, str::FromStr};

use crate::{utils::{DrainablePageHolder, ptr_align_dist}, garbage, root_alloc::{Block4KPtr, RootAllocator}};

struct NodePageHeader {
  next_page: *mut u8
}
pub struct InterlaceAllocator {
  origin: *mut u8,
  current_write_page_start: *mut u8,
  write_head: *mut u8,
}
impl InterlaceAllocator {
  pub fn new() -> Self {
    Self { origin: null_mut(),
           current_write_page_start: null_mut(),
           write_head: null_mut() }
  }
  fn switch_to(&mut self, page: Block4KPtr) { unsafe {
    assert!(self.write_head as usize % 4096 != 0);
    let Block4KPtr(page) = page ;
    page.write_bytes(0, 4096);
    (*page.cast::<NodePageHeader>()).next_page = null_mut() ;
    let current_page_header = self.header_of_current_page();
    current_page_header.next_page = page;
    let new_write_head = page.add(size_of::<NodePageHeader>());
    self.write_head = new_write_head.cast();
    self.current_write_page_start = page;
  }; }
  fn header_of_current_page(&self) -> &mut NodePageHeader {
    unsafe {&mut *(self.current_write_page_start as *mut NodePageHeader) }
  }
  fn perform_late_init(&mut self, Block4KPtr(page): Block4KPtr) { unsafe {
    page.write_bytes(0, 4096);
    self.origin = page;
    (*page.cast::<NodePageHeader>()).next_page = null_mut();
    self.current_write_page_start = page;
    let past_header = page.add(size_of::<NodePageHeader>());
    self.write_head = past_header.cast()
  } }
  pub fn store_item<T>(
    &mut self,
    item: T,
    page_source: &mut dyn DrainablePageHolder
  ) -> InterlacedSeqvItemRef<T> { unsafe {
    let mut head = self.write_head;
    *head.cast::<Tag>() = Tag::JumpSignal;
    head = head.add(8);
    loop {
      let data = head.add(head.align_offset(align_of::<T>()));
      let tail = data.add(size_of::<T>());
      let bound = self.current_write_page_start as usize + 4096;
      if tail as usize >= bound {
        let new_page = page_source.try_drain_page().unwrap();
        self.switch_to(new_page);
        head = self.write_head;
        continue;
      }
      self.write_head = tail;
      data.cast::<T>().write(item);
      return InterlacedSeqvItemRef(data.cast())
    }
  } }
  pub fn start_seqv<T>(
    &mut self,
    page_source: &mut dyn DrainablePageHolder
  ) -> SeqvWriter<T> { unsafe {
    if self.origin == null_mut() {
      let page = page_source.try_drain_page().unwrap();
      self.perform_late_init(page);
    }
    // writer ensures there is always space for jumping
    let mut wh = self.write_head;
    wh.cast::<Tag>().write(Tag::JumpSignal);
    wh = wh.add(8);
    loop {
      // do we have enough free space on this page ?
      let next = wh.add(size_of::<Tag>());
      let item_loc = next.add(next.align_offset(align_of::<T>()));
      let tail = item_loc.add(size_of::<T>());
      let w_next = tail.add(8);
      let bound = self.current_write_page_start as usize + 4096;
      if w_next as usize >= bound { // no we dont. gotta jump
        let new_page = page_source.try_drain_page().unwrap();
        self.switch_to(new_page);
        wh = self.write_head;
        continue;
      }
      self.write_head = tail;
      return SeqvWriter {
        write_head: wh, seqv_start_point: wh, master: self, count: 0, phantom: PhantomData
      }
    }
  } }
}

#[repr(u8)] #[derive(Debug, Clone, Copy)]
enum Tag { Item, JumpSignal, JumpDirective }

pub struct InterlacedSeqvItemRef<T>(*mut T);
impl <T> InterlacedSeqvItemRef<T> {
  pub fn load_item(self) -> T {
    unsafe { self.0.read() }
  }
  pub fn mref(&self) -> &mut T {
    unsafe { &mut *self.0 }
  }
}

pub struct SeqvWriter<T> {
  master: *mut InterlaceAllocator,
  seqv_start_point: *mut u8,
  write_head: *mut u8,
  count: u16,
  phantom: PhantomData<T>
}
impl <T> SeqvWriter<T> {
  pub fn end_seqv(self) -> SeqvRef<T> {
    let ptr = SeqvRef::new(self.seqv_start_point, self.count);
    return ptr
  }
  fn take_free_slot(
    &mut self,
    page_source: &mut dyn DrainablePageHolder
  ) -> *mut T { unsafe {
    self.count += 1;
    loop {
      let mut current_wh = self.write_head;
      if let Tag::JumpSignal = *current_wh.cast::<Tag>() {
        let next = (*self.master).write_head;
        let comp = (next as usize) << 8;
        let comp = comp | (Tag::JumpDirective as usize);
        current_wh.cast::<usize>().write_unaligned(comp);
        current_wh = next;
      }
      let w_tag = current_wh.add(size_of::<Tag>());
      let data = w_tag.add(w_tag.align_offset(align_of::<T>()));
      let tail = data.add(size_of::<T>());
      let w_next = tail.add(8);
      let bound = (*self.master).current_write_page_start as usize + 4096;
      if w_next as usize >= bound {
        let page = page_source.try_drain_page().unwrap();
        (*self.master).switch_to(page);
        let next = (*self.master).write_head;
        self.write_head = next;
        let marker = ((next as usize) << 8) | (Tag::JumpDirective as usize);
        current_wh.cast::<usize>().write_unaligned(marker);
        continue;
      }
      current_wh.cast::<Tag>().write(Tag::Item);
      self.write_head = tail;
      (*self.master).write_head = tail;
      return data.cast()
    }
  }; }
  pub fn append_item(&mut self, item: T, page_source: &mut dyn DrainablePageHolder) {
    let slot = self.take_free_slot(page_source);
    unsafe {slot.write(item)}
  }
  pub fn item_count(&self) -> u16 {
    self.count
  }
  pub fn is_empty(&self) -> bool {
    self.count == 0
  }
}

#[repr(align(8))]
pub struct SeqvRef<T>([u8;6], u16, PhantomData<T>);
impl <T> SeqvRef<T> {
  fn new(ptr: *mut u8, count: u16) -> Self { unsafe {
    let mut item = garbage!(SeqvRef<T>);
    copy_nonoverlapping(
      addr_of!(ptr).cast::<u8>(),
      addr_of_mut!(item.0).cast::<u8>(),
      6);
    item.1 = count;
    return item
  } }
  pub fn get_seqv_start_ptr(&self) -> *mut u8 { unsafe {
    let mut i = 0u64;
    copy_nonoverlapping(
      addr_of!(self.0).cast::<u8>(),
      addr_of_mut!(i).cast(),
      6);
    return i as _
  } }
  pub fn get_count(&self) -> u16 {
    self.1
  }
}

pub struct SeqvReader<'i, T> {
  read_head: *mut u8,
  counter: u16,
  phantom: PhantomData<(&'i (), T)>
}
impl <T> SeqvReader<'_, T> {
  pub fn new_from_seqv_ref<'i>(master: &'i SeqvRef<T>) -> SeqvReader<'i, T> {
    SeqvReader { counter: master.get_count(),
                 read_head: master.get_seqv_start_ptr(),
                 phantom: PhantomData }
  }
  pub fn new_from_writer_ref<'i>(master: &'i SeqvWriter<T>) -> SeqvReader<'i, T> {
    todo!("implement if needed")
  }
  pub fn next(&mut self) -> Option<&T> { unsafe {
    if self.counter == 0 { return None }
    loop {
      let read_head = self.read_head;
      let tag = *read_head.cast::<Tag>();
      match tag {
        Tag::Item => {
          self.counter -= 1;
          let mut data = read_head.add(size_of::<Tag>());
          data = data.add(data.align_offset(align_of::<T>()));
          let tail = data.add(size_of::<T>());
          self.read_head = tail;
          let item_ref = &*data.cast::<T>();
          return Some(item_ref)
        },
        Tag::JumpDirective => {
          let next = read_head.cast::<u64>().read_unaligned();
          let next = (next >> 8) as *mut u8;
          self.read_head = next;
          continue;
        },
        Tag::JumpSignal => return None
      }
    }
  } }
}

#[test]
fn basic_inout_w_interleave() {
  let mut pager = RootAllocator::new();
  let mut ialloc = InterlaceAllocator::new();
  let mut a_seqv_w = ialloc.start_seqv(&mut pager);
  for i in 0 .. 4 {
    a_seqv_w.append_item(i, &mut pager);
  }
  let mut b_seqv_w = ialloc.start_seqv(&mut pager);
  for i in 0 .. 4 {
    b_seqv_w.append_item(i, &mut pager)
  }
  for i in 4 .. 8 {
    a_seqv_w.append_item(i, &mut pager)
  }
  for i in 4 .. 8 {
    b_seqv_w.append_item(i, &mut pager)
  }
  let a_seqv = a_seqv_w.end_seqv();
  let mut a_reader = SeqvReader::new_from_seqv_ref(&a_seqv);
  for i in 0 .. 8 {
    let thing = a_reader.next().unwrap();
    assert!(i == *thing)
  }
  let b_seqv = b_seqv_w.end_seqv();
  let mut b_reader = SeqvReader::new_from_seqv_ref(&b_seqv);
  for i in 0 .. 8 {
    let thing = b_reader.next().unwrap();
    assert!(i == *thing)
  }
}

#[test]
fn cross_page_jumps() {
  let mut pager = RootAllocator::new();
  let mut ialloc = InterlaceAllocator::new();
  let mut a_seqv_w = ialloc.start_seqv(&mut pager);
  type Item = usize;
  let mut item_size = size_of::<Tag>() as *mut u8;
  item_size = unsafe{item_size.add(item_size.align_offset(align_of::<Item>()))};
  item_size = unsafe{item_size.add(size_of::<Item>())};
  let size = item_size as usize ;
  let limit = (4096 - size_of::<NodePageHeader>()) / size;
  let limit_ = limit * 2 as Item;
  for i in 0 .. limit_ {
    a_seqv_w.append_item(i, &mut pager)
  }
  let b_seqv = a_seqv_w.end_seqv();
  let mut a_reader = SeqvReader::new_from_seqv_ref(&b_seqv);
  for i in 0 .. limit_ {
    if let Some(val) = a_reader.next() {
      assert!(*val == i)
    } else {
      panic!()
    }
  }
}

#[test]
fn storing_while_in_seqv() {
  let mut pager = RootAllocator::new();
  let mut ialloc = InterlaceAllocator::new();
  let mut a_seqv_w = ialloc.start_seqv(&mut pager);
  for i in 0 .. 4u8 {
    a_seqv_w.append_item(i, &mut pager);
  }
  let str = String::from_str("well, that's called maturation").unwrap();
  let str_ref = ialloc.store_item(str.clone(), &mut pager);
  for i in 4 .. 8 {
    a_seqv_w.append_item(i, &mut pager);
  }
  let a_seqv = a_seqv_w.end_seqv();
  let mut a_reader = SeqvReader::new_from_seqv_ref(&a_seqv);
  for i in 0 .. 8 {
    let item = a_reader.next().unwrap();
    assert!(i == *item)
  }
  assert!(str == str_ref.load_item())
}