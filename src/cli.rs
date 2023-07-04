
use core::panic;
use std::{fs::File, path::{Path, self}, io::{Write, Read, self, Stdout, BufWriter, stdout, Stdin, stdin}, str::FromStr, cell::UnsafeCell, net::{TcpListener, TcpStream, SocketAddr, SocketAddrV4}, mem::{transmute_copy, replace}, sync::mpsc::Receiver,};

use crate::{driver::{TaskContext, Continuation, WorkGroupRef, WorkGroup}, utils::{with_scoped_consume, PageSource}, mpsc::{MPSCQueue}, garbage};


pub fn main() {
  main_impl()
  // basic()
}

#[test]
fn test() {
  main_impl()
}



fn main_impl() {
  let work_group = WorkGroup::new();
  work_group.submit_and_await(garbage!(CliCtx), cli_iface_begin);
}

struct CliCtx {
  stdout: BufWriter<Stdout>,
  stdin: Stdin,
  stdin_read_buffer: String,
  server_started: bool
}
impl CliCtx {
  fn new() -> Self {
    CliCtx {
      stdout: BufWriter::new(stdout()),
      stdin: stdin(),
      stdin_read_buffer: String::new(),
      server_started: false
    }
  }
  fn append_to_output(&mut self, str: &str) {
    self.stdout.write(str.as_bytes()).unwrap();
  }
  fn commit(&mut self) {
    self.stdout.flush().unwrap();
  }
  fn print(&mut self, str: &str) {
    self.commit();
    self.append_to_output(str);
    self.commit();
  }
  fn read_from_terminal(&mut self) -> String {
    self.stdin.read_line(&mut self.stdin_read_buffer).unwrap();
    let str = replace(&mut self.stdin_read_buffer, String::new());
    return str
  }
}

fn cli_iface_begin(ctx: &TaskContext) -> Continuation {

  let ctx_data = CliCtx::new();
  let raw_frame = ctx.acccess_frame_as_raw().cast::<CliCtx>();
  unsafe { raw_frame.write(ctx_data) };
  let frame = unsafe {&mut *raw_frame};

  let greeting = build_greeting(90);
  frame.append_to_output("\n\n");
  frame.append_to_output(&greeting);
  frame.append_to_output("\n");
  frame.commit();

  return Continuation::then(cli_iface_main_loop)
}

fn cli_iface_main_loop(ctx:&TaskContext) -> Continuation {
  let frame = ctx.access_frame_as_init::<CliCtx>();
  frame.print("\n> ");
  let iofd = &frame.stdin;
  return Continuation::await_io(iofd, true, false, |ctx| {
    let frame = ctx.access_frame_as_init::<CliCtx>();
    let inp = frame.read_from_terminal();
    if inp.is_empty() {
      frame.print("No command has been given");
      return Continuation::then(cli_iface_main_loop);
    }
    let components = inp
      .trim()
      .split(|e| e == ' ')
      .collect::<Vec<_>>();
    match components[0] {
      "help" => {
        let help = help_message();
        frame.print(&help);
        return Continuation::then(cli_iface_main_loop)
      },
      "exit" => {
        return Continuation::done()
      },
      "server" => {
        let len = components.len();
        if len < 2 {
          frame.print("invalid invocation of server command");
          return Continuation::then(cli_iface_main_loop)
        }
        match len {
          2 if components[1] == "start" => {
            let started = &mut frame.server_started;
            if *started {
              frame.print("server was already started");
              return Continuation::then(cli_iface_main_loop);
            }
            *started = true;
            let listener_ = TcpListener::bind("localhost:13137").unwrap();
            frame.print(&format!("started server at {}", listener_.local_addr().unwrap()));
            ctx.spawn_detached_task(
              SocketManCtx {
                listener: listener_,
                stream: None,
                buffer: Vec::new()
              },
              socket_man);
            return Continuation::then(cli_iface_main_loop)
          },
          2 if components[1] == "stop" => {
            let started = &mut frame.server_started;
            if !*started {
              frame.print("server was not started");
              return Continuation::then(cli_iface_main_loop)
            }
            frame.print("stopping serv is not impled");
            return Continuation::then(cli_iface_main_loop)
          },
          3 if components[1] == "start" => {
            todo!()
          },
          _ => {
            frame.print("invalid invocation of server command");
            return Continuation::then(cli_iface_main_loop)
          }
        }
      },
      "load_from_file" => {
        if components.len() != 2 {
          frame.print(
            "expected command and filepath, but got something else");
          return Continuation::then(cli_iface_main_loop)
        }
        let path_str = components[1];
        let file = File::open(path_str) ;
        match file {
          Err(err) => {
            frame.print(format!("cant open file at {} because {}", path_str, err).as_str());
            return Continuation::then(cli_iface_main_loop);
          },
          Ok(mut file) => {
            let stdout = &mut frame.stdout;
            let outcome = io::copy(&mut file, stdout);
            match outcome {
              Err(err) => {
                frame.print(
                  format!("failed to write file to stdout because {}", err).as_str())
              },
              Ok(_) => ()
            }
            return Continuation::then(cli_iface_main_loop)
          }
        }
      },
      _ => {
        frame.print("Unknown command has been given");
        return Continuation::then(cli_iface_main_loop);
      }
    }
  });
}

struct SocketManCtx {
  listener: TcpListener,
  stream: Option<(TcpStream, SocketAddr)>,
  buffer: Vec<u8>,
}
fn socket_man(ctx: &TaskContext) -> Continuation {
  let frame = ctx.access_frame_as_init::<SocketManCtx>();
  frame.listener.set_nonblocking(true).unwrap();
  return Continuation::then(socket_setup)
}
fn socket_setup(ctx: &TaskContext) -> Continuation {
  let frame = ctx.access_frame_as_init::<SocketManCtx>() ;
  let outcome = frame.listener.accept();
  match outcome {
    Ok(conn) => {
      conn.0.set_nonblocking(true).unwrap();
      frame.stream = Some(conn);
      return Continuation::then(socket_read_loop)
    },
    Err(err) if err.kind() == io::ErrorKind::WouldBlock => {

      return Continuation::await_io(&frame.listener, true, false, socket_setup);
    }
    _ => panic!()
  }
}
fn socket_read_loop(ctx: &TaskContext) -> Continuation {
  let frame = ctx.access_frame_as_init::<SocketManCtx>();
  if let Some((stream, _)) = &mut frame.stream {
    return Continuation::await_io(&*stream, true, false, |ctx| {
      let frame = ctx.access_frame_as_init::<SocketManCtx>() ;
      let (stream, _) = frame.stream.as_mut().unwrap();
      let outcome = stream.read_to_end(&mut frame.buffer);
      match outcome {
        Ok(_) => {
          return process_bytes_from_socket(&mut frame.buffer, ctx)
        },
        Err(err) if err.kind() == io::ErrorKind::WouldBlock => {
          println!("listening on conn would block");
          return Continuation::await_io(&*stream, true, false, socket_read_loop)
        },
        _ => panic!()
      }
    });
  } else {
    panic!()
  }
}
fn process_bytes_from_socket(bytes: &mut Vec<u8>, ctx: &TaskContext) -> Continuation {
  let frame = unsafe { &mut *ctx.access_frame_as_init::<SocketManCtx>() };
  let bytes = replace(bytes, Vec::new());
  // ctx.send_message(&frame.printer_ref, PrinterMsg::PrintBytes(bytes));
  return Continuation::then(socket_read_loop)
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

