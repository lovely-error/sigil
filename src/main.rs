mod root_alloc;
mod utils;
mod loopbuffer;
mod driver;
mod array;

fn main() {
    use core::mem::transmute;

    println!("{:#064b}", main as u64);
}
