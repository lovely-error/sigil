use std::{sync::atomic::{AtomicU64, Ordering, AtomicBool}, thread::{self, sleep, spawn, JoinHandle, park}, time::Duration, ptr::{addr_of_mut, addr_of}};




#[test]
fn k() {
  let start_count = AtomicU64::new(0);
  let end_count = AtomicU64::new(0);
  let thread_count = 32;
  let mut hs = Vec::<(AtomicBool, JoinHandle<()>)>::new();
  hs.reserve(thread_count);
  for i in 0 .. thread_count {
    let start_count = addr_of!(start_count)as u64;
    let hs_ = addr_of_mut!(hs) as u64;
    let end_count = addr_of!(end_count) as u64;
    let t = spawn(move || {
      // println!("{i} started");
      let start_count = unsafe {&*(start_count as *const AtomicU64)};
      let hs = unsafe {&*(hs_ as *const Vec<(AtomicBool, JoinHandle<()>)>)};
      let sold = start_count.fetch_add(1, Ordering::AcqRel);
      sleep(Duration::from_millis(1));
      let end_count = unsafe {&*(end_count as *const AtomicU64)};
      let eold = end_count.fetch_add(1, Ordering::AcqRel);
      println!("{sold} {eold} {i}");
      let done = sold == eold;
      if done {
        println!("{i} become terminator");
        for (f, h) in hs {
          f.store(true, Ordering::Relaxed);
          h.thread().unpark();
        }
      } else {
        // println!("{i} went sleeping");
        let (v, _) = hs.get(i).unwrap();
        loop {
          park();
          if v.load(Ordering::Relaxed) { break }
        }
        // println!("{i} terminated")
      }
    });
    hs.push((AtomicBool::new(false),t));
  }
  for (_,i) in hs {
    i.join().unwrap();
  }
  println!("{}", start_count.load(Ordering::Relaxed));
}