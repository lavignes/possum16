//! 6551 UART Emulation

use std::io::{Read, Write};

use crate::bus::{Bus, BusDevice};

enum StatusFlags {}

impl StatusFlags {
    const PARITY_ERROR: u8 = 1 << 0;
    const FRAMING_ERROR: u8 = 1 << 1;
    const OVERRUN: u8 = 1 << 2;
    const RX_DATA_REGISTER_FULL: u8 = 1 << 3;
    const TX_DATA_REGISTER_EMPTY: u8 = 1 << 4;
    const DATA_CARRIER_DETECT: u8 = 1 << 5;
    const DATA_SET_READY: u8 = 1 << 6;
    const INTERRUPT: u8 = 1 << 7;
}

enum ControlFlags {}

impl ControlFlags {
    const BAUD_RATE_MASK: u8 = 0b0000_1111;
    const RX_CLOCK_SOURCE: u8 = 1 << 4;
    const WORD_LENGTH_MASK: u8 = 0b0110_0000;
    const STOP_BIT: u8 = 1 << 7;
}

enum CommandFlags {}

impl CommandFlags {
    const DATA_TERMINAL_READY: u8 = 1 << 0;
    const RX_INTERRUPT_REQUEST_DISABLED: u8 = 1 << 1;
    const TX_INTERRUPT_CONTROL_MASK: u8 = 0b0000_1100;
    const RX_ECHO_MODE: u8 = 1 << 4;
    const PARITY_MODE_ENABLED: u8 = 1 << 5;
    const PARITY_MODE_CONTROL_MASK: u8 = 0b1100_0000;
}

pub struct Uart<T> {
    handle: T,
    status: u8,
    control: u8,
    command: u8,
    tx: Option<u8>,
    rx: Option<u8>,
    irq: bool,
}

impl<T> Uart<T> {
    pub fn new(handle: T) -> Self {
        Self {
            handle,
            status: 0,
            control: 0,
            command: 0,
            tx: None,
            rx: None,
            irq: false,
        }
    }

    pub fn irq(&self) -> bool {
        (self.status & StatusFlags::INTERRUPT) != 0
    }

    pub fn handle_mut(&mut self) -> &mut T {
        &mut self.handle
    }
}

impl<T: Read + Write> BusDevice for Uart<T> {
    fn reset<B: Bus>(&mut self, _bus: &mut B) {
        self.status = StatusFlags::TX_DATA_REGISTER_EMPTY;
        self.control = 0;
        self.command = 0;
        self.tx = None;
        self.rx = None;
        self.irq = false;
    }

    fn tick<B: Bus>(&mut self, bus: &mut B) {
        if (self.command & CommandFlags::DATA_TERMINAL_READY) == 0 {
            return;
        }

        if let Some(tx) = self.tx.take() {
            match self.handle.write(&[tx]) {
                // no transmit happened. can this even happen?
                Ok(n) if n == 0 => {
                    self.tx = Some(tx);
                }
                Err(e) => {
                    todo!("need to handle tx error: {e}");
                }
                _ => {
                    self.status |= StatusFlags::TX_DATA_REGISTER_EMPTY;
                    if (self.command & CommandFlags::TX_INTERRUPT_CONTROL_MASK) == 0b0000_0100 {
                        self.status |= StatusFlags::INTERRUPT;
                    }
                }
            }
            self.handle.flush().unwrap();
        } else {
        }

        if self.rx.is_none() {
            let mut buf = [0];
            match self.handle.read(&mut buf) {
                // modem has nothing else to send us?
                Ok(n) if n == 0 => {}
                Err(e) => {
                    todo!("need to handle rx error: {e}");
                }
                _ => {
                    self.rx = Some(buf[0]);
                    self.status |= StatusFlags::RX_DATA_REGISTER_FULL;
                    if (self.command & CommandFlags::RX_INTERRUPT_REQUEST_DISABLED) == 0 {
                        self.status |= StatusFlags::INTERRUPT;
                    }
                }
            }
        } else {
        }
    }

    fn read(&mut self, addr: u32) -> u8 {
        match addr {
            0 => {
                // all error conditions are cleared on data read
                self.status &= !(StatusFlags::RX_DATA_REGISTER_FULL
                    | StatusFlags::PARITY_ERROR
                    | StatusFlags::FRAMING_ERROR
                    | StatusFlags::OVERRUN);
                self.rx.take().unwrap_or(0)
            }
            1 => {
                // clear interrupt on status read.
                let status = self.status;
                self.status &= !StatusFlags::INTERRUPT;
                status
            }
            2 => self.command,
            3 => self.control,
            _ => unreachable!(),
        }
    }

    fn write(&mut self, addr: u32, data: u8) {
        match addr {
            0 => {
                self.status &= !StatusFlags::TX_DATA_REGISTER_EMPTY;
                self.tx = Some(data);
            }
            1 => {
                self.tx = None;
                self.rx = None;
                self.command = CommandFlags::RX_INTERRUPT_REQUEST_DISABLED;
                // TODO: this isn't accurate. only overrun should clear on soft reset
                //   but I use this flag to know whether to push bytes
                self.status = StatusFlags::TX_DATA_REGISTER_EMPTY;
            }
            2 => self.command = data,
            3 => self.control = data,
            _ => unreachable!(),
        }
    }
}
