use std::io::{Read, Write};

use crate::{
    bus::{Bus, BusDevice},
    cpu::Cpu,
    uart::Uart,
    vdp::Vdp,
};

pub struct Mem {
    inner: Vec<u8>,
}

impl Mem {
    fn new() -> Self {
        Self {
            inner: vec![0; 0x010000],
        }
    }

    fn read(&mut self, addr: u32) -> u8 {
        self.inner[(addr & 0x00FFFFFF) as usize]
    }

    fn write(&mut self, addr: u32, data: u8) {
        self.inner[(addr & 0x00FFFFFF) as usize] = data;
    }
}

pub struct Sys<S0> {
    cpu: Cpu,
    vdp: Vdp,
    ser0: Uart<S0>,
    mem: Mem,
    irq_latch: u8,
}

impl<S0> Sys<S0>
where
    S0: Read + Write,
{
    pub fn new(rom: &[u8], ser0: S0) -> Self {
        let cpu = Cpu::new();
        let vdp = Vdp::new();
        let ser0 = Uart::new(ser0);
        let mut mem = Mem::new();
        for (i, data) in rom.iter().enumerate() {
            mem.write((0x0000F100 + i) as u32, *data);
        }
        Self {
            cpu,
            vdp,
            ser0,
            mem,
            irq_latch: 0,
        }
    }

    pub fn reset(&mut self) {
        let Self {
            ref mut cpu,
            ref mut vdp,
            ref mut ser0,
            ref mut mem,
            ref mut irq_latch,
        } = self;
        cpu.reset(&mut CpuView { mem, irq_latch });
        let mut io_view = IoView {};
        ser0.reset(&mut io_view);
    }

    pub fn tick(&mut self) {
        let Self {
            ref mut cpu,
            ref mut vdp,
            ref mut ser0,
            ref mut mem,
            ref mut irq_latch,
        } = self;
        cpu.tick(&mut CpuView { mem, irq_latch });
        let mut io_view = IoView {};
        ser0.tick(&mut io_view);
        // TODO: irqs
    }

    pub fn ser0_mut(&mut self) -> &mut Uart<S0> {
        &mut self.ser0
    }

    pub fn cpu(&self) -> &Cpu {
        &self.cpu
    }

    pub fn mem(&self) -> &Mem {
        &self.mem
    }
}

struct IoView {}

impl Bus for IoView {
    fn read(&mut self, _addr: u32) -> u8 {
        0xFF
    }

    fn write(&mut self, _addr: u32, _data: u8) {}
}

struct CpuView<'a> {
    mem: &'a mut Mem,
    irq_latch: &'a mut u8,
}

impl<'a> Bus for CpuView<'a> {
    fn read(&mut self, addr: u32) -> u8 {
        match addr {
            0xF000..=0xF0FE => 0xFF,
            0xF0FF => {
                let irq = *self.irq_latch;
                *self.irq_latch = 0;
                irq
            }
            _ => self.mem.read(addr),
        }
    }

    fn write(&mut self, addr: u32, data: u8) {
        match addr {
            0xF000..=0xF0FE => {}
            0xF0FF => {}
            _ => self.mem.write(addr, data),
        }
    }
}
