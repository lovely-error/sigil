mod root_alloc;
mod utils;
mod loopbuffer;
mod driver;
mod array;
mod stable_map;

fn main() {
    use core::mem::transmute;

    println!("{:#064b}", main as u64);
}
