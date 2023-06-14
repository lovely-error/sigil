
use std::{fs::File, path::{Path, self}, io::{Write, Read, self}, str::FromStr, cell::UnsafeCell, time::Duration, ops::Deref};

use crate::driver::{TaskContext, Continuation, WorkGroup};
use polling::{self, Event, Poller};

pub fn main() {
  main_impl()
}

#[test]
fn test() {
  main_impl()
}

fn main_impl() {
  let mut work_group = WorkGroup::new((), cli_iface_begin);
  work_group.await_completion();
}

fn begin(_: &TaskContext) -> Continuation {
  let args : Vec<String> = std::env::args().collect();
  if args.len() < 2 {
    println!("No path to source file was provided");
    return Continuation::Done
  }
  let path_str = &args[1];
  let file = File::open(path_str) ;
  match file {
    Err(err) => {
      println!("cant open file at {} because {}", path_str, err);
      return Continuation::Done;
    },
    Ok(mut file) => {
      let mut out = std::io::stdout();
      let outcome = io::copy(&mut file, &mut out);
      match outcome {
        Err(err) => {
          println!("failed to write file to stdout because {}", err);
        },
        Ok(_) => ()
      }
      return Continuation::Done
    }
  }
}
struct CliCtx(UnsafeCell<CliCtxImpl>);
struct CliCtxImpl {
  input: std::io::Stdin,
  output: std::io::Stdout,
  events: Vec<Event>,
  poller: Poller,
  id: usize,
  input_chars: String,
  output_chars: String
}
impl CliCtx {
  fn new() -> Self {
    let obj = CliCtxImpl {
      input: std::io::stdin(),
      output: std::io::stdout(),
      input_chars: String::new(),
      output_chars: String::new(),
      events: Vec::new(),
      poller: Poller::new().unwrap(),
      id: 0
    };
    obj.poller.add(
      &obj.input,
      Event::readable(obj.id)).unwrap();
    Self(UnsafeCell::new(obj))
  }
  fn append_to_text_output(&self, text: &str) {
    let this = unsafe { &mut *self.0.get() };
    this.output_chars.push_str(text)
  }
  fn flush_output_text_in_terminal(&self) {
    let this = unsafe { &mut *self.0.get() };
    this.output.write(this.output_chars.as_bytes()).unwrap();
    this.output.flush().unwrap();
    this.output_chars.clear();
  }
  fn try_read_text_from_terminal(&self) -> Option<&str> {
    let this = unsafe { &mut *self.0.get() };
    let outcome = this.poller.wait(&mut this.events, Some(Duration::from_secs(0)));
    match outcome {
      Err(err) => panic!("{}", err),
      Ok(count) => {
        if count == 0 { return None }
        this.input.read_line(&mut this.input_chars).unwrap();
        this.events.clear();
        this.poller.modify(&this.input, Event::readable(this.id)).unwrap();
        return Some(this.input_chars.as_str())
      }
    }
  }
  fn print(&self, str: &str) {
    self.append_to_text_output(str);
    self.flush_output_text_in_terminal();
  }
}

fn cli_iface_begin(ctx: &TaskContext) -> Continuation {
  ctx.install_task_frame::<CliCtx>();
  let ctx_data = CliCtx::new();
  let raw_frame = ctx.access_task_frame::<CliCtx>();
  unsafe { raw_frame.write(ctx_data) };
  let frame = unsafe {&mut *raw_frame};

  let greeting = build_greeting(90);
  frame.append_to_text_output(&greeting);
  frame.append_to_text_output("> ");
  frame.flush_output_text_in_terminal();

  return Continuation::Then(cli_iface_main_loop)
}
fn cli_iface_main_loop(ctx:&TaskContext) -> Continuation {
  let frame = unsafe {&mut *ctx.access_task_frame::<CliCtx>()};
  let inp = frame.try_read_text_from_terminal();
  if let Some(inp) = inp {
    if inp.is_empty() {
      frame.print("No command has been given");
      return Continuation::Rerun;
    }
    let components = inp.split(|e| e == ' ').collect::<Vec<_>>();
    match components[0] {
      "load_from_file" => {
        if components.len() != 2 {
          frame.print(
            "cannot respond to an invocation of load_from_file with with provided arguments");
          return Continuation::Rerun
        }
        let path_str = components[1];
        let file = File::open(path_str) ;
        match file {
          Err(err) => {
            frame.print(format!("cant open file at {} because {}", path_str, err).as_str());
            return Continuation::Rerun;
          },
          Ok(mut file) => {
            let stdout = unsafe { &mut (*frame.0.get()).output };
            let outcome = io::copy(&mut file, stdout);
            match outcome {
              Err(err) => {
                frame.print(format!("failed to write file to stdout because {}", err).as_str())
              },
              Ok(_) => ()
            }
            return Continuation::Rerun
          }
        }
      },
      _ => {
        frame.print("Unknown command has been given");
        return Continuation::Rerun;
      }
    }
  } else {
    return Continuation::Rerun
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



