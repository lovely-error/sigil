//! Minimal CLI: `sigil-neo check <file>`, `sigil-neo <file>`, `--help`.

use std::io::{self, Read};

pub fn run() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        None | Some("--help") | Some("-h") | Some("help") => {
            print_help();
        }
        Some("check") => {
            match args.get(2) {
                Some(path) => check_file(path),
                None => {
                    eprintln!("usage: sigil-neo check <file.sig>");
                    std::process::exit(2);
                }
            }
        }
        // A bare `-` reads from stdin (same as `check -`); anything else
        // starting with `-` is not a file.
        Some(path) if !path.starts_with('-') || path == "-" => check_file(path),
        Some(other) => {
            eprintln!("unknown command '{other}'; try `sigil-neo --help`");
            std::process::exit(2);
        }
    }
}

fn print_help() {
    println!(
        "sigil-neo: a small dependently typed language (MVP core)\n\
         \n\
         usage:\n\
          \x20 sigil-neo check <file.sig>   scope-check + type-check a file\n\
          \x20 sigil-neo <file.sig>          same as `check`\n\
          \x20 sigil-neo check -             read the program from stdin\n\
          \x20 sigil-neo --help              this message\n\
         \n\
         language (two-sort core):\n\
         \x20 def name : T = v;                 top-level defs, `;`-separated\n\
         \x20 (x : A) -> B    A -> B            dependent / non-dependent functions\n\
         \x20 \\x y. body     fun x => body      lambdas\n\
         \x20 f x y                             application (juxtaposition)\n\
         \x20 let x : A = v in body             annotated let\n\
         \x20 let x = v in body                 unannotated let (type inferred)\n\
         \x20 *  Type  Type0 ...              sorts (`*` impredicative bottom,\n\
         \x20                                  `Type` ambiguous, `Type<n>` concrete)\n\
         \x20 Void  absurd                        empty type + vacuous eliminator\n\
         \x20 (x : A) and B   A and B             dependent / non-dependent pairs\n\
         \x20 (a, b)  fst p  snd p                pair values + projections\n\
         \x20 sig_rect A B P f p                  dependent eliminator (iota)\n\
         \x20 A or B  inl a  inr b                sums + injections\n\
         \x20 either_rect A B P f g e             sum eliminator (iota both sides)\n\
         \x20 Quot A R  quot_mk a                 set quotients + introduction\n\
         \x20 quot_lift A R B f h q               quotient eliminator (iota)\n\
         \x20 quot_ind A R P f coh q              dependent eliminator (iota)\n\
         \x20 quot_sound A R a b h                soundness axiom (stuck)\n\
         \x20 Unit  ()  unit_rect P b u            unit type, value + eliminator\n\
         \x20 W A B  sup A B a f  w_rect A B P s w  well-founded trees\n\
         \x20 -- comment                        line comments\n\
         \n\
         theory: `* : Type0 : Type1 : ...`, impredicative Pi into `*`,\n\
         predicative `max` otherwise, cumulativity upward,\n\
         beta/delta + eta conversion. No forward/self\n\
         references (MVP)."
    );
}

fn check_file(path: &str) {
    let src = if path == "-" {
        let mut s = String::new();
        if let Err(e) = io::stdin().read_to_string(&mut s) {
            eprintln!("cannot read stdin: {e}");
            std::process::exit(1);
        }
        s
    } else {
        match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("cannot open '{path}': {e}");
                std::process::exit(1);
            }
        }
    };
    match check_program_big_stack(&src) {
        Ok(checker) => {
            print!("{}", checker.report());
            if checker.has_errors() {
                std::process::exit(1);
            }
        }
        Err(msg) => {
            eprintln!("error: {msg}");
            std::process::exit(1);
        }
    }
}

/// Run the checker on a thread with a generous stack. Debug builds use fat
/// frames, so deeply nested (but legal — under the parser's depth cap) input
/// overflows the small default main-thread stack and aborts the process
/// instead of checking. A big stack turns those into ordinary checking
/// (success or a clean checked error), and a worker panic — which must never
/// happen on user input — becomes a clean failure, never an abort.
fn check_program_big_stack(src: &str) -> Result<crate::check::Checker, String> {
    const STACK: usize = 256 * 1024 * 1024;
    let owned = src.to_string();
    match std::thread::Builder::new()
        .name("sigil-check".to_string())
        .stack_size(STACK)
        .spawn(move || crate::check::check_program(&owned))
    {
        Ok(handle) => match handle.join() {
            Ok(result) => result,
            Err(_) => Err("internal error (checker worker failed — please report)".to_string()),
        },
        // Thread spawn itself failed (resource exhaustion): fall back to the
        // calling thread rather than refusing to check.
        Err(_) => crate::check::check_program(src),
    }
}
