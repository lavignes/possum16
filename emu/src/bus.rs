pub trait Bus {
    fn read(&mut self, addr: u32) -> u8;

    fn write(&mut self, addr: u32, data: u8);
}

pub trait BusDevice {
    fn reset<B: Bus>(&mut self, bus: &mut B);

    fn tick<B: Bus>(&mut self, bus: &mut B);

    fn read(&mut self, _addr: u32) -> u8 {
        0xFF
    }

    fn write(&mut self, _addr: u32, _data: u8) {}
}
