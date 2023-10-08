
use core::panic;
use std::{fs::File, path::{Path, self}, io::{Write, Read, self, Stdout, BufWriter, stdout, Stdin, stdin}, str::FromStr, cell::UnsafeCell, net::{TcpListener, TcpStream, SocketAddr, SocketAddrV4}, mem::{transmute_copy, replace, size_of}, sync::mpsc::Receiver, any::Any, simd::u8x4,};

use crate::{driver::{TaskContext, Continuation, WorkGroupRef, WorkGroup}, utils::{with_scoped_consume, PageSource}, mpsc::{MPSCQueue}, garbage, lexer::{SourceTextParser, Letters, RawDecl, ParseFailure}, parser::resolve_precendece, sema::{DeclCheckCtx, ScopedDecl, self, SemanticError}};


pub fn main() {
  let _ = main_impl();
  // basic()
}

#[test]
fn test() {
  let _ = main_impl();
}

fn main_impl() {

    let mut out = BufWriter::new(stdout());
    let in_ = stdin();

    let mut inp_str = String::new();

    let mut println = |msg:&str| {
      let _ = out.write(msg.as_bytes());
      let _ = out.write("\n".as_bytes());
      let _ = out.flush();
    };

    let greeting = build_greeting(80);
    println(&greeting);

    'main:loop {
      inp_str.clear();
      let _ = in_.read_line(&mut inp_str);
      if inp_str.is_empty() {
        println("No command has been given");
        continue;
      }
      let components = inp_str
        .trim()
        .split(|e| e == ' ')
        .collect::<Vec<_>>();
      let head = components[0];
      if head == "exit" { return }
      for (name, _, fun) in COMMANDS {
        if *name == head {
          fun(&components, &mut println);
          continue 'main;
        }
      }
      println("Unknown command has been given");
      continue;
    }

}

fn build_greeting(term_width: usize) -> String {
  let header =
    ("███████╗██╗ ██████╗ ██╗██╗     \n".to_string() +
    "██╔════╝██║██╔════╝ ██║██║     \n" +
    "███████╗██║██║  ███╗██║██║     \n" +
    "╚════██║██║██║   ██║██║██║     \n" +
    "███████║██║╚██████╔╝██║███████╗\n" +
    "╚══════╝╚═╝ ╚═════╝ ╚═╝╚══════╝")
    .split(|e| e == '\n')
    .map(|e| String::from_str(e).unwrap())
    .collect::<Vec<String>>();
  let header_common_line_width = header[0].chars().count();
  if header_common_line_width > term_width {
    return header.join("\n")
  }
  let left_offset_for_header = (term_width - header_common_line_width) / 2;
  let header = header.iter().map(
    |e| String::from_iter(std::iter::repeat(' ').take(left_offset_for_header)) + e);
  let mut header = header.collect::<Vec<_>>().join("\n");
  header.push('\n');
  return header;
}

const COMMANDS : &[(&str, &str, fn (&Vec<&str>, &mut dyn FnMut(&str)))] = &[
  ("help", "prints help message", |_, prt|{
    let hmsg = help_message();
    prt(&hmsg);
  }),
  ("lff", "loads items defined in a given textual file", |components, printer|{
    if components.len() != 2 {
      printer("expected command and filepath, but got something else");
    }
    let path_str = components[1];
    let file = File::open(path_str) ;
    match file {
      Err(err) => {
        let err_msg = format!("cant open file at {} because {}", path_str, err);
        printer(&err_msg);
        return;
      },
      Ok(mut file) => {
        let mut bytes = Vec::new();
        let _ = file.read_to_end(&mut bytes);
        for _ in bytes.len() .. bytes.len().next_multiple_of(size_of::<u8x4>()) {
          bytes.push(Letters::EOT);
        }
        let out = build_defs(bytes.as_slice());
        printer(&format!("{:#?}", out));
        return;
      }
    }
  }),
  ("give", "begins a term forming session", |_, ptr|{
    ptr("not implemented yet");
    return;
  }),
  ("exit", "terminates the programm", |_, prt|{
    prt("bye");
    return;
  })
];

fn help_message() -> String {
  let mut str = String::new();
  for (cname, desc, _) in COMMANDS {
    str.push_str(&cname);
    str.push_str("\n    ");
    str.push_str(&desc);
    str.push_str("\n");
  }
  return str
}

#[derive(Debug)]
enum SomeError {
  SemanticErrors(Vec<SemanticError>),
  ParseError(ParseFailure)
}

fn build_defs(
  bytes: &[u8],
) -> Result<Vec<ScopedDecl>, SomeError>{
  let mut parser = SourceTextParser::new(bytes);
  let res = parser.parse_to_end();
  match res {
    Ok(defs) => {
      let mut scchk = DeclCheckCtx::new(bytes);
      let out = sema::check_decls(&mut scchk, &defs);
      if let Some(errs) = scchk.get_errors_if_any() {
        return Err(SomeError::SemanticErrors(errs));
      }
      return Ok(out);
    },
    Err(err) => {
      return Err(SomeError::ParseError(err));
    },
  }
}