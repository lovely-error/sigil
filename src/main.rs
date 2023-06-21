#![feature(portable_simd)]
#![feature(exact_size_is_empty)]
#![feature(absolute_path)]
#![feature(trait_upcasting)]

mod root_alloc;
mod utils;
mod loopbuffer;
mod driver;
mod array;
mod stable_map;

mod semi_inline_seqv;

mod sema;

mod coordinated_killing;

mod mpsc;

mod lexer;

mod cli;

mod parser;

mod interlacing_alloc;

mod reductor;


fn main() {
  cli::main()
}