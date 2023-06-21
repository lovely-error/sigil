
use core::panic;
use std::{fs::File, path::{Path, self}, io::{Write, Read, self, Stdout}, str::FromStr, cell::UnsafeCell, net::{TcpListener, TcpStream, SocketAddr, SocketAddrV4}, mem::{transmute_copy, replace}, sync::mpsc::Receiver,};

use crate::{driver::{TaskContext, Continuation, WorkGroup, Isolate, IsolateRef}, utils::{with_scoped_consume, PageSource}, mpsc::{MPSCQueue}};


pub fn main() {
  main_impl()
  // basic()
}

#[test]
fn test() {
  main_impl()
}

fn basic() {
  let lis = TcpListener::bind("localhost:13137").unwrap();
  loop {
    match lis.accept() {
      Ok((mut stream, _)) => {
        let mut buf = Vec::new();
        loop {
          stream.read_to_end(&mut buf).unwrap();
          let str = buf.escape_ascii();
          println!("got {}", str);
          buf.clear();
        }
      },
      Err(_) => {

      }
    }
  }
}


fn main_impl() {
  let mut work_group = WorkGroup::new((), cli_iface_begin);
  work_group.await_completion();
}

struct CliCtx(UnsafeCell<CliCtxImpl>);
struct CliCtxImpl {
  input: std::io::Stdin,
  output: Stdout,
  input_chars: String,
  output_chars: String,
  server_started: bool,
  printer_ref: Option<IsolateRef<Printer>>
}
impl CliCtx {
  fn new() -> Self {
    let obj = CliCtxImpl {
      input: std::io::stdin(),
      output: std::io::stdout(),
      input_chars: String::new(),
      output_chars: String::new(),
      server_started: false,
      printer_ref: None
    };
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
  fn read_text_from_terminal(&self) -> Option<&str> {
    let this = unsafe { &mut *self.0.get() };
    this.input_chars.clear();
    this.input.read_line(&mut this.input_chars).unwrap();
    return Some(&this.input_chars)
  }
  fn print(&self, str: &str, ctx: &TaskContext) {
    let this = unsafe { &mut *self.0.get() };
    self.append_to_text_output(str);
    if let Some(printer) = &this.printer_ref {
      let str = replace(&mut this.output_chars, String::new());
      ctx.send_message(printer, PrinterMsg::PrintStr(str));
    } else {
      panic!()
    };
  }
}

fn cli_iface_begin(ctx: &TaskContext) -> Continuation {
  ctx.install_task_frame::<CliCtx>();
  let ctx_data = CliCtx::new();
  let raw_frame = ctx.access_task_frame::<CliCtx>();
  unsafe { raw_frame.write(ctx_data) };
  let frame = unsafe {&mut *raw_frame};

  let greeting = build_greeting(90);
  frame.append_to_text_output("\n\n");
  frame.append_to_text_output(&greeting);
  frame.append_to_text_output("\n");
  frame.flush_output_text_in_terminal();

  let printer = Printer {
    queue: MPSCQueue::new(),
    stdout: std::io::stdout()
  };
  let iso = ctx.spawn_isolate(printer);
  unsafe {(*frame.0.get()).printer_ref = Some(iso)};

  return Continuation::Then(cli_iface_main_loop)
}

fn cli_iface_main_loop(ctx:&TaskContext) -> Continuation {
  let frame = unsafe {&mut *ctx.access_task_frame::<CliCtx>()};
  frame.print("\n> ", ctx);
  let iofd = unsafe{ &(*frame.0.get()).input} ;
  return Continuation::wait_on(iofd, true, false, |ctx| {
    let frame = unsafe {&mut *ctx.access_task_frame::<CliCtx>()};
    let inp = frame.read_text_from_terminal();
    if let Some(inp) = inp {
      if inp.is_empty() {
        frame.print("No command has been given", ctx);
        return Continuation::Then(cli_iface_main_loop);
      }
      let components = inp
        .trim()
        .split(|e| e == ' ')
        .collect::<Vec<_>>();
      match components[0] {
        "help" => {
          let help = help_message();
          frame.print(&help, ctx);
          return Continuation::Then(cli_iface_main_loop)
        },
        "exit" => {
          return Continuation::Done
        },
        "server" => {
          let len = components.len();
          if len < 2 {
            frame.print("invalid invocation of server command", ctx);
            return Continuation::Then(cli_iface_main_loop)
          }
          match len {
            2 if components[1] == "start" => {
              let started = unsafe {&mut (*frame.0.get()).server_started};
              if *started {
                frame.print("server was already started", ctx);
                return Continuation::Then(cli_iface_main_loop);
              }
              *started = true;
              let listener_ = TcpListener::bind("localhost:13137").unwrap();
              frame.print(&format!("started server at {}", listener_.local_addr().unwrap()), ctx);
              ctx.spawn_detached_task(
                SocketManCtx {
                  listener: listener_,
                  stream: None,
                  buffer: Vec::new(),
                  printer_ref: unsafe{(*frame.0.get()).printer_ref.clone().unwrap()}
                },
                socket_man);
              return Continuation::Then(cli_iface_main_loop)
            },
            2 if components[1] == "stop" => {
              let started = unsafe {&mut (*frame.0.get()).server_started};
              if !*started {
                frame.print("server was not started", ctx);
                return Continuation::Then(cli_iface_main_loop)
              }
              frame.print("stopping serv is not impled", ctx);
              return Continuation::Then(cli_iface_main_loop)
            },
            3 if components[1] == "start" => {
              todo!()
            },
            _ => {
              frame.print("invalid invocation of server command", ctx);
              return Continuation::Then(cli_iface_main_loop)
            }
          }
        },
        "load_from_file" => {
          if components.len() != 2 {
            frame.print(
              "expected command and filepath, but got something else", ctx);
            return Continuation::Then(cli_iface_main_loop)
          }
          let path_str = components[1];
          let file = File::open(path_str) ;
          match file {
            Err(err) => {
              frame.print(format!("cant open file at {} because {}", path_str, err).as_str(), ctx);
              return Continuation::Then(cli_iface_main_loop);
            },
            Ok(mut file) => {
              let stdout = unsafe { &mut (*frame.0.get()).output };
              let outcome = io::copy(&mut file, stdout);
              match outcome {
                Err(err) => {
                  frame.print(format!("failed to write file to stdout because {}", err).as_str(), ctx)
                },
                Ok(_) => ()
              }
              return Continuation::Then(cli_iface_main_loop)
            }
          }
        },
        _ => {
          frame.print("Unknown command has been given", ctx);
          return Continuation::Then(cli_iface_main_loop);
        }
      }
    } else {
      return Continuation::Then(cli_iface_main_loop)
    }
  });
}
struct Printer {
  queue: MPSCQueue<PrinterMsg>,
  stdout: Stdout
}
enum PrinterMsg {
  PrintStr(String),
  PrintBytes(Vec<u8>)
}
impl Isolate for Printer {
  type Message = PrinterMsg;
  type SyncView = Self;
  type MsgSendOutcome = ();
  fn send_message(
      this: &Self::SyncView, // thread safe view of self
      ctx: &TaskContext,
      message: Self::Message) -> Self::MsgSendOutcome {
      let page_sourse = ctx.get_page_provider();
      this.queue.enqueue_item(message, page_sourse)
  }
  fn respond_to_message(&mut self, ctx: &TaskContext) -> Option<Continuation> {
    let ps = ctx.get_page_provider();
    let msg = self.queue.dequeue_item(ps);
    match msg {
      None => return None,
      Some(msg) => {
        match msg {
          PrinterMsg::PrintStr(str) => {
            self.stdout.write(str.as_bytes()).unwrap();
            self.stdout.flush().unwrap();
            return Some(Continuation::Done)
          },
          PrinterMsg::PrintBytes(bytes) => {
            self.stdout.write(&bytes).unwrap();
            self.stdout.flush().unwrap();
            return Some(Continuation::Done)
          }
        }
      }
    }
  }
}

struct SocketManCtx {
  listener: TcpListener,
  stream: Option<(TcpStream, SocketAddr)>,
  buffer: Vec<u8>,
  printer_ref: IsolateRef<Printer>
}
fn socket_man(ctx: &TaskContext) -> Continuation {
  let frame = unsafe { &mut *ctx.access_task_frame::<SocketManCtx>() };
  frame.listener.set_nonblocking(true).unwrap();
  return Continuation::Then(socket_setup)
}
fn socket_setup(ctx: &TaskContext) -> Continuation {
  let frame = unsafe { &mut *ctx.access_task_frame::<SocketManCtx>() };
  let outcome = frame.listener.accept();
  match outcome {
    Ok(conn) => {
      conn.0.set_nonblocking(true).unwrap();
      frame.stream = Some(conn);
      return Continuation::Then(socket_read_loop)
    },
    Err(err) if err.kind() == io::ErrorKind::WouldBlock => {
      // println!("listening would block");
      return Continuation::wait_on(&frame.listener, true, false, socket_setup);
    }
    _ => panic!()
  }
}
fn socket_read_loop(ctx: &TaskContext) -> Continuation {
  let frame = unsafe { &mut *ctx.access_task_frame::<SocketManCtx>() };
  if let Some((stream, _)) = &mut frame.stream {
    return Continuation::wait_on(&*stream, true, false, |ctx| {
      let frame = unsafe { &mut *ctx.access_task_frame::<SocketManCtx>() };
      let (stream, _) = frame.stream.as_mut().unwrap();
      let outcome = stream.read_to_end(&mut frame.buffer);
      match outcome {
        Ok(_) => {
          return process_bytes_from_socket(&mut frame.buffer, ctx)
        },
        Err(err) if err.kind() == io::ErrorKind::WouldBlock => {
          println!("listening on conn would block");
          return Continuation::wait_on(&*stream, true, false, socket_read_loop)
        },
        _ => panic!()
      }
    });
  } else {
    panic!()
  }
}
fn process_bytes_from_socket(bytes: &mut Vec<u8>, ctx: &TaskContext) -> Continuation {
  let frame = unsafe { &mut *ctx.access_task_frame::<SocketManCtx>() };
  let bytes = replace(bytes, Vec::new());
  ctx.send_message(&frame.printer_ref, PrinterMsg::PrintBytes(bytes));
  return Continuation::Then(socket_read_loop)
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

fn help_message() -> String {
  "".to_string() +
  "exit\n" +
  "  terminates the programm\n" +
  "load_from_file <file_path>\n" +
  "  loads definitions from text file\n" +
  "server start <sock_addr>?\n" +
  "  starts server at provided address. if none given uses default\n" +
  "  localhost:13137\n" +
  "server stop\n" +
  "  terminates the server"
}

