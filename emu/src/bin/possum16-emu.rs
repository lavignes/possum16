use std::{
    error::Error,
    fs::File,
    io::{self, Read, Stdout, Write},
    path::PathBuf,
    process::ExitCode,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use clap::Parser;
use possum16::{
    cpu::{Cpu, Flags, Mode},
    sys::Sys,
};
use signal_hook::{consts, flag};
use termion::{
    raw::{IntoRawMode, RawTerminal},
    AsyncReader,
};
use tracing::Level;

struct Tty {
    tx: RawTerminal<Stdout>,
    rx: AsyncReader,
}

impl Tty {
    fn new() -> Self {
        let tx = io::stdout().into_raw_mode().unwrap();
        let rx = termion::async_stdin();
        Self { tx, rx }
    }
}

impl Read for Tty {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.rx.read(buf)
    }
}

impl Write for Tty {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.tx.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.tx.flush()
    }
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to rom file
    rom: PathBuf,

    /// FD0 image file
    #[arg(long)]
    fd0: PathBuf,

    /// One of `TRACE`, `DEBUG`, `INFO`, `WARN`, or `ERROR`
    #[arg(short, long, default_value_t = Level::INFO)]
    log_level: Level,

    /// Start with debugger enabled
    #[arg(short, long)]
    debug: bool,

    /// Debugger symbol file
    #[arg(short, long)]
    sym: Option<PathBuf>,
}

fn main() -> ExitCode {
    let args = Args::parse();
    tracing_subscriber::fmt()
        .with_max_level(args.log_level)
        .with_writer(io::stderr)
        .init();
    if let Err(e) = main_real(&args) {
        tracing::error!("{}", e.into());
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn main_real(args: &Args) -> Result<(), impl Into<Box<dyn Error>>> {
    let mut rom = Vec::new();
    File::open(&args.rom)
        .map_err(|e| format!("failed to open ROM file: {e}"))?
        .read_to_end(&mut rom)
        .map_err(|e| format!("failed to read ROM file: {e}"))?;
    if rom.len() != 0x0F00 {
        return Err(format!(
            "ROM file is {} bytes, but it must be exactly 3840 bytes (3.75KiB) in length!",
            rom.len()
        ));
    }
    let debug_mode = Arc::new(AtomicBool::new(args.debug));
    flag::register(consts::SIGUSR1, debug_mode.clone())
        .map_err(|e| {
            tracing::warn!("external debugger unavailable: failed to install SIGUSR1 handler: {e}")
        })
        .ok();
    let mut sys = Sys::new(&rom, Tty::new());
    sys.reset();
    'emu: loop {
        if debug_mode.load(Ordering::Relaxed) {
            sys.ser0_mut().handle_mut().tx.suspend_raw_mode().unwrap();
            let mut cached_parts = Vec::new();
            loop {
                print_regs(sys.cpu());
                print!(">");
                sys.ser0_mut().handle_mut().tx.flush().unwrap();
                let mut line = Vec::new();
                // kind of jank, but reads are async, so we busy-wait
                loop {
                    let mut buf = [0];
                    if sys.ser0_mut().handle_mut().rx.read(&mut buf).unwrap() != 1 {
                        continue;
                    }
                    if buf[0] == 0x0A {
                        break;
                    }
                    line.push(buf[0]);
                }
                let line = String::from_utf8(line).unwrap();
                let parts = line
                    .split_whitespace()
                    .map(String::from)
                    .collect::<Vec<String>>();
                let parts = if parts.is_empty() {
                    cached_parts.clone()
                } else {
                    cached_parts = parts.clone();
                    parts
                };
                if !parts.is_empty() {
                    let arg = parts.get(1).map(String::as_str);
                    match parts[0].as_str() {
                        "c" => break,      // continue emulator
                        "q" => break 'emu, // quit emulator
                        "s" | "n" => {
                            // single step
                            sys.tick();
                        }
                        _ => println!("unknown command: `{}`. type `?` for help", parts[0]),
                    }
                }
            }
            // restore raw tty
            sys.ser0_mut().handle_mut().tx.activate_raw_mode().unwrap();
            debug_mode.store(false, Ordering::Relaxed);
        }
        sys.tick();
    }
    Ok(())
}

fn print_regs(cpu: &Cpu) {
    print!(
        "C={:04X} X={:04X} Y={:04X} S={:04X} PC={:04X} D={:02X} PBR={:02X} DBR={:02X} P=[",
        cpu.c(),
        cpu.x(),
        cpu.y(),
        cpu.s(),
        cpu.pc(),
        cpu.d(),
        cpu.pbr(),
        cpu.dbr(),
    );
    print!("{}", if (cpu.p() & Flags::N) != 0 { 'N' } else { 'n' });
    print!("{}", if (cpu.p() & Flags::V) != 0 { 'V' } else { 'v' });
    print!("{}", if (cpu.p() & Flags::M) != 0 { 'M' } else { 'm' });
    if cpu.mode() == Mode::Emulation {
        print!("{}", if (cpu.p() & Flags::B) != 0 { 'B' } else { 'b' });
    } else {
        print!("{}", if (cpu.p() & Flags::X) != 0 { 'X' } else { 'x' });
    }
    print!("{}", if (cpu.p() & Flags::D) != 0 { 'D' } else { 'd' });
    print!("{}", if (cpu.p() & Flags::I) != 0 { 'I' } else { 'i' });
    print!("{}", if (cpu.p() & Flags::Z) != 0 { 'Z' } else { 'z' });
    print!("{}", if (cpu.p() & Flags::C) != 0 { 'C' } else { 'c' });
    println!("]");
}
