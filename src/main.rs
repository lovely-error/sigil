#![feature(portable_simd)]
#![feature(exact_size_is_empty)]
#![feature(absolute_path)]

mod root_alloc;
mod utils;
mod loopbuffer;
mod driver;
mod array;
mod stable_map;

mod semi_inline_seqv;

mod loomed_q;

mod coordinated_killing;

mod mpsc;

mod parser;

mod cli;

mod interlacing_alloc;

fn main() {
  cli::main()
}