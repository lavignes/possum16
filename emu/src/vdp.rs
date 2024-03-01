//! Yamaha V9938 Emulation

use crate::bus::{Bus, BusDevice};

pub struct Vdp {
    port1_data_latch: u8,
    port1_addr_latch: u8,
}

impl Vdp {
    pub fn new() -> Self {
        Self {
            port1_data_latch: 0,
            port1_addr_latch: 0,
        }
    }
}

impl BusDevice for Vdp {
    fn reset<B: Bus>(&mut self, bus: &mut B) {}

    fn tick<B: Bus>(&mut self, bus: &mut B) {}

    fn read(&mut self, _addr: u32) -> u8 {
        0xFF
    }

    fn write(&mut self, _addr: u32, _data: u8) {}
}
