use crate::bus::{Bus, BusDevice};

enum Flags {}

impl Flags {
    const C: u8 = 1 << 0; // carry
    const E: u8 = 1 << 0; // 6502 emulation
    const Z: u8 = 1 << 1; // zero
    const I: u8 = 1 << 2; // interrupt 0=enabled 1=disable
    const D: u8 = 1 << 3; // decimal
    const B: u8 = 1 << 4; // break (only in emulation mode)
    const X: u8 = 1 << 4; // 0=16-bit 1=8-bit index
    const M: u8 = 1 << 5; // 0=16-bit 1=8-bit accumulator/memory
    const V: u8 = 1 << 6; // overflow
    const N: u8 = 1 << 7; // negative
}

enum IntKind {
    Abrt,
    Nmi,
    Irq,
    Brk,
}

#[derive(PartialEq, Eq)]
enum Mode {
    Emulation,
    Native,
}

impl Default for Mode {
    fn default() -> Self {
        Self::Emulation
    }
}

#[derive(Default)]
pub struct Cpu {
    pc: u16,    // program counter
    c: [u8; 2], // accumulator
    x: [u8; 2], // index x
    y: [u8; 2], // index y
    s: [u8; 2], // stack pointer
    d: u16,     // direct page
    dbr: u8,    // data bank (aka: b)
    pbr: u8,    // program bank (aka: k)
    p: u8,      // processor status

    abort: bool,
    nmi: bool,
    irq: bool,
    mode: Mode,
}

impl Cpu {
    pub fn new() -> Self {
        Self::default()
    }

    fn push<B: Bus>(&mut self, bus: &mut B, data: u8) {
        bus.write(u16::from_le_bytes(self.s) as u32, data);
        if self.mode == Mode::Emulation {
            self.s[0] = self.s[0].wrapping_sub(1);
        } else {
            self.s = u16::from_le_bytes(self.s).wrapping_sub(1).to_le_bytes();
        }
    }

    fn pull<B: Bus>(&mut self, bus: &mut B) -> u8 {
        if self.mode == Mode::Emulation {
            self.s[0] = self.s[0].wrapping_add(1);
        } else {
            self.s = u16::from_le_bytes(self.s).wrapping_add(1).to_le_bytes();
        }
        bus.read(u16::from_le_bytes(self.s) as u32)
    }

    fn set_flag(&mut self, mask: u8, value: bool) {
        if value {
            self.p |= mask;
        } else {
            self.p &= !mask;
        }
    }

    fn set_p(&mut self, value: u8) {
        if self.mode == Mode::Emulation {
            self.p = value | Flags::X | Flags::M;
        } else {
            self.p = value;
        }
        // when switched to 8-bit, the index register hi bytes always reset
        if (self.p & Flags::X) != 0 {
            self.x[1] = 0;
            self.y[1] = 0;
        }
    }

    fn interrupt<B: Bus>(&mut self, bus: &mut B, kind: IntKind) {
        if self.mode == Mode::Native {
            self.push(bus, self.pbr);
        }
        let [lo, hi] = self.pc.to_le_bytes();
        self.push(bus, hi);
        self.push(bus, lo);
        if self.mode == Mode::Emulation {}
        /*
        match kind {
            IntKind::Nmi | IntKind::Irq | IntKind::Brk => {
            }
        }
        */
    }

    fn fetch<B: Bus>(&mut self, bus: &mut B) -> u8 {
        let data = bus.read(((self.pbr as u32) << 16) | (self.pc as u32));
        self.pc = self.pc.wrapping_add(1);
        data
    }

    fn addr_imm8<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let addr = ((self.pbr as u32) << 16) | (self.pc as u32);
        self.pc = self.pc.wrapping_add(1);
        addr
    }

    fn addr_imm16<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let addr = ((self.pbr as u32) << 16) | (self.pc as u32);
        self.pc = self.pc.wrapping_add(2);
        addr
    }

    fn addr_sr<B: Bus>(&mut self, bus: &mut B) -> u32 {
        u16::from_le_bytes(self.s).wrapping_add(self.fetch(bus) as u16) as u32
    }

    fn addr_dp<B: Bus>(&mut self, bus: &mut B) -> u32 {
        self.d.wrapping_add(self.fetch(bus) as u16) as u32
    }

    fn addr_dpx<B: Bus>(&mut self, bus: &mut B) -> u32 {
        self.d
            .wrapping_add(self.fetch(bus) as u16)
            .wrapping_add(u16::from_le_bytes(self.x)) as u32
    }

    fn addr_dpy<B: Bus>(&mut self, bus: &mut B) -> u32 {
        self.d
            .wrapping_add(self.fetch(bus) as u16)
            .wrapping_add(u16::from_le_bytes(self.y)) as u32
    }

    fn addr_idp<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self.d.wrapping_add(self.fetch(bus) as u16);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        u32::from_le_bytes([lo, hi, self.dbr, 0])
    }

    fn addr_idx<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self
            .d
            .wrapping_add(self.fetch(bus) as u16)
            .wrapping_add(u16::from_le_bytes(self.x));
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        u32::from_le_bytes([lo, hi, self.dbr, 0])
    }

    fn addr_idy<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self.d.wrapping_add(self.fetch(bus) as u16);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        u32::from_le_bytes([lo, hi, self.dbr, 0]).wrapping_add(u16::from_le_bytes(self.y) as u32)
    }

    fn addr_idl<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self.d.wrapping_add(self.fetch(bus) as u16);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        let bank = bus.read(ptr.wrapping_add(2) as u32);
        u32::from_le_bytes([lo, hi, bank, 0])
    }

    fn addr_ily<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self.d.wrapping_add(self.fetch(bus) as u16);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        let bank = bus.read(ptr.wrapping_add(2) as u32);
        u32::from_le_bytes([lo, hi, bank, 0]).wrapping_add(u16::from_le_bytes(self.y) as u32)
    }

    fn addr_isy<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let ptr = self
            .d
            .wrapping_add(self.fetch(bus) as u16)
            .wrapping_add(u16::from_le_bytes(self.s));
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        u32::from_le_bytes([lo, hi, self.dbr, 0]).wrapping_add(u16::from_le_bytes(self.y) as u32)
    }

    fn addr_abs<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        u32::from_le_bytes([lo, hi, self.dbr, 0])
    }

    fn addr_abx<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        u32::from_le_bytes([lo, hi, self.dbr, 0]).wrapping_add(u16::from_le_bytes(self.x) as u32)
    }

    fn addr_aby<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        u32::from_le_bytes([lo, hi, self.dbr, 0]).wrapping_add(u16::from_le_bytes(self.y) as u32)
    }

    fn addr_abl<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        let bank = self.fetch(bus);
        u32::from_le_bytes([lo, hi, bank, 0])
    }

    fn addr_alx<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        let bank = self.fetch(bus);
        u32::from_le_bytes([lo, hi, bank, 0]).wrapping_add(u16::from_le_bytes(self.x) as u32)
    }

    fn addr_iab<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        let ptr = u16::from_le_bytes([lo, hi]);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        u32::from_le_bytes([lo, hi, self.pbr, 0])
    }

    fn addr_iax<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        let ptr = u32::from_le_bytes([lo, hi, self.pbr, 0])
            .wrapping_add(u16::from_le_bytes(self.x) as u32);
        let lo = bus.read(ptr);
        let hi = bus.read(ptr.wrapping_add(1));
        u32::from_le_bytes([lo, hi, self.pbr, 0])
    }

    fn addr_ial<B: Bus>(&mut self, bus: &mut B) -> u32 {
        let lo = self.fetch(bus);
        let hi = self.fetch(bus);
        let ptr = u16::from_le_bytes([lo, hi]);
        let lo = bus.read(ptr as u32);
        let hi = bus.read(ptr.wrapping_add(1) as u32);
        let bank = bus.read(ptr.wrapping_add(2) as u32);
        u32::from_le_bytes([lo, hi, bank, 0])
    }

    fn op_brk<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        todo!();
    }

    fn op_ora<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] | data;
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = u16::from_le_bytes(self.c) | data;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_cop<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        todo!();
    }

    fn op_tsb<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] | data;
            bus.write(addr, result);
            self.set_flag(Flags::Z, (self.c[0] & data) == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let c = u16::from_le_bytes(self.c);
            let result = c | data;
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::Z, (c & data) == 0);
        }
    }

    fn op_asl<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = data << 1;
            bus.write(addr, result);
            self.set_flag(Flags::C, (data & 0x80) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = data << 1;
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::C, (data & 0x8000) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_php<B: Bus>(&mut self, bus: &mut B) {
        self.push(bus, self.p);
    }

    fn op_asl_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let a = self.c[0];
            let result = a << 1;
            self.c[0] = result;
            self.set_flag(Flags::C, (a & 0x80) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = c << 1;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::C, (c & 0x8000) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_phd<B: Bus>(&mut self, bus: &mut B) {
        self.push(bus, (self.d >> 8) as u8);
        self.push(bus, self.d as u8);
    }

    fn op_bpl<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::N) == 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_trb<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] & !data;
            bus.write(addr, result);
            self.set_flag(Flags::Z, (self.c[0] & data) == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let c = u16::from_le_bytes(self.c);
            let result = c & !data;
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::Z, (c & data) == 0);
        }
    }

    fn op_clc(&mut self) {
        self.set_flag(Flags::C, false);
    }

    fn op_inc_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let result = self.c[0].wrapping_add(1);
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = c.wrapping_add(1);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tcs(&mut self) {
        if self.mode == Mode::Emulation {
            self.s[0] = self.c[0];
        } else {
            self.s = self.c;
        }
    }

    fn op_jsr<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        self.push(bus, (self.pc >> 8) as u8);
        self.push(bus, self.pc as u8);
        self.pc = addr as u16;
    }

    fn op_and<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] & data;
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = u16::from_le_bytes(self.c) & data;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_jsl<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        self.push(bus, self.pbr);
        self.push(bus, (self.pc >> 8) as u8);
        self.push(bus, self.pc as u8);
        self.pbr = (addr >> 16) as u8;
        self.pc = addr as u16;
    }

    fn op_bit<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] & data;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::V, (result & 0x40) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = u16::from_le_bytes(self.c) & data;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::V, (result & 0x4000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_rol<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = (data << 1) | (self.p & Flags::C);
            bus.write(addr, result);
            self.set_flag(Flags::C, (data & 0x80) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = (data << 1) | ((self.p & Flags::C) as u16);
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::C, (data & 0x8000) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_plp<B: Bus>(&mut self, bus: &mut B) {
        let data = self.pull(bus);
        self.set_p(data);
    }

    fn op_rol_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let a = self.c[0];
            let result = (a << 1) | (self.p & Flags::C);
            self.c[0] = result;
            self.set_flag(Flags::C, (a & 0x80) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = (c << 1) | ((self.p & Flags::C) as u16);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::C, (c & 0x8000) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_pld<B: Bus>(&mut self, bus: &mut B) {
        let lo = self.pull(bus);
        let hi = self.pull(bus);
        let data = u16::from_le_bytes([lo, hi]);
        self.d = data;
        self.set_flag(Flags::N, (data & 0x8000) != 0);
        self.set_flag(Flags::Z, data == 0);
    }

    fn op_bmi<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::N) != 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_sec(&mut self) {
        self.set_flag(Flags::C, true);
    }

    fn op_dec_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let result = self.c[0].wrapping_sub(1);
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = c.wrapping_sub(1);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tsc(&mut self) {
        self.c = self.s;
        let result = u16::from_le_bytes(self.c);
        self.set_flag(Flags::N, (result & 0x8000) != 0);
        self.set_flag(Flags::Z, result == 0);
    }

    fn op_rti<B: Bus>(&mut self, bus: &mut B) {
        let p = self.pull(bus);
        self.set_p(p);
        let lo = self.pull(bus);
        let hi = self.pull(bus);
        self.pc = u16::from_le_bytes([lo, hi]);
        if self.mode == Mode::Native {
            self.pbr = self.pull(bus);
        }
    }

    fn op_eor<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = self.c[0] ^ data;
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = u16::from_le_bytes(self.c) ^ data;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_wdc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        todo!();
    }

    fn op_mvp<B: Bus>(&mut self, bus: &mut B) {
        todo!();
    }

    fn op_lsr<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = data >> 1;
            bus.write(addr, result);
            self.set_flag(Flags::C, (data & 0x01) != 0);
            self.set_flag(Flags::N, false);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = data >> 1;
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::C, (data & 0x0001) != 0);
            self.set_flag(Flags::N, false);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_pha<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::M) != 0 {
            self.push(bus, self.c[0]);
        } else {
            self.push(bus, self.c[1]);
            self.push(bus, self.c[0]);
        }
    }

    fn op_lsr_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let a = self.c[0];
            let result = a >> 1;
            self.c[0] = result;
            self.set_flag(Flags::C, (a & 0x01) != 0);
            self.set_flag(Flags::N, false);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = c >> 1;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::C, (c & 0x0001) != 0);
            self.set_flag(Flags::N, false);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_phk<B: Bus>(&mut self, bus: &mut B) {
        self.push(bus, self.pbr);
    }

    fn op_jmp<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        self.pc = ea(self, bus) as u16;
    }

    fn op_bvc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::V) == 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_mvn<B: Bus>(&mut self, bus: &mut B) {
        todo!();
    }

    fn op_cli(&mut self) {
        self.set_flag(Flags::I, false);
    }

    fn op_phy<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::X) != 0 {
            self.push(bus, self.y[0]);
        } else {
            self.push(bus, self.y[1]);
            self.push(bus, self.y[0]);
        }
    }

    fn op_tcd(&mut self) {
        let result = u16::from_le_bytes(self.c);
        self.set_flag(Flags::N, (result & 0x8000) != 0);
        self.set_flag(Flags::Z, result == 0);
        self.d = result;
    }

    fn op_jml<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        self.pc = addr as u16;
        self.pbr = (addr >> 16) as u8;
    }

    fn op_rts<B: Bus>(&mut self, bus: &mut B) {
        let lo = self.pull(bus);
        let hi = self.pull(bus);
        self.pc = u16::from_le_bytes([lo, hi]);
    }

    fn op_adc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let (result, carry1) = self.c[0].overflowing_add(data);
            let (result, carry2) =
                result.overflowing_add(if (self.p & Flags::C) != 0 { 1 } else { 0 });
            let overflow = ((!(self.c[0] ^ data)) & (self.c[0] ^ result) & 0x80) != 0;
            self.c[0] = result;
            self.set_flag(Flags::V, overflow);
            self.set_flag(Flags::C, carry1 || carry2);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let c = u16::from_le_bytes(self.c);
            let (result, carry1) = c.overflowing_add(data);
            let (result, carry2) =
                result.overflowing_add(if (self.p & Flags::C) != 0 { 1 } else { 0 });
            let overflow = ((!(c ^ data)) & (c ^ result) & 0x8000) != 0;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::V, overflow);
            self.set_flag(Flags::C, carry1 || carry2);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_per<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let lo = bus.read(addr);
        let hi = bus.read(addr.wrapping_add(1));
        let offset = i16::from_le_bytes([lo, hi]);
        let result = self.pc.wrapping_add_signed(offset);
        self.push(bus, (result >> 8) as u8);
        self.push(bus, result as u8);
    }

    fn op_stz<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            bus.write(addr, 0);
        } else {
            bus.write(addr, 0);
            bus.write(addr.wrapping_add(1), 0);
        }
    }

    fn op_ror<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = (data >> 1) | ((self.p & Flags::C) << 7);
            bus.write(addr, result);
            self.set_flag(Flags::C, (data & 0x01) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = (data >> 1) | (((self.p & Flags::C) as u16) << 15);
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::C, (data & 0x0001) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_pla<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::M) != 0 {
            let result = self.pull(bus);
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = self.pull(bus);
            let hi = self.pull(bus);
            let result = u16::from_le_bytes([lo, hi]);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_ror_a(&mut self) {
        if (self.p & Flags::M) != 0 {
            let a = self.c[0];
            let result = (a >> 1) | ((self.p & Flags::C) << 7);
            self.c[0] = a;
            self.set_flag(Flags::C, (a & 0x01) != 0);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let c = u16::from_le_bytes(self.c);
            let result = (c >> 1) | (((self.p & Flags::C) as u16) << 15);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::C, (c & 0x0001) != 0);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_rtl<B: Bus>(&mut self, bus: &mut B) {
        let lo = self.pull(bus);
        let hi = self.pull(bus);
        self.pbr = self.pull(bus);
        self.pc = u16::from_le_bytes([lo, hi]);
    }

    fn op_bvs<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::V) != 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_sei(&mut self) {
        self.set_flag(Flags::I, true);
    }

    fn op_ply<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::X) != 0 {
            let result = self.pull(bus);
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = self.pull(bus);
            let hi = self.pull(bus);
            let result = u16::from_le_bytes([lo, hi]);
            self.y = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tdc(&mut self) {
        self.c = self.d.to_le_bytes();
        self.set_flag(Flags::N, (self.d & 0x8000) != 0);
        self.set_flag(Flags::Z, self.d == 0);
    }

    fn op_bra<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        self.pc = self.pc.wrapping_add_signed(offset as i16);
    }

    fn op_sta<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            bus.write(addr, self.c[0]);
        } else {
            bus.write(addr, self.c[0]);
            bus.write(addr.wrapping_add(1), self.c[1]);
        }
    }

    fn op_brl<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let lo = bus.read(addr);
        let hi = bus.read(addr);
        let offset = i16::from_le_bytes([lo, hi]);
        self.pc = self.pc.wrapping_add_signed(offset);
    }

    fn op_sty<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::X) != 0 {
            bus.write(addr, self.y[0]);
        } else {
            bus.write(addr, self.y[0]);
            bus.write(addr.wrapping_add(1), self.y[1]);
        }
    }

    fn op_stx<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::X) != 0 {
            bus.write(addr, self.x[0]);
        } else {
            bus.write(addr, self.x[0]);
            bus.write(addr.wrapping_add(1), self.y[1]);
        }
    }

    fn op_dey(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.y[0].wrapping_sub(1);
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let y = u16::from_le_bytes(self.y);
            let result = y.wrapping_sub(1);
            self.y = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_txa(&mut self) {
        if (self.p & Flags::M) != 0 {
            let result = self.x[0];
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.x);
            self.c = self.x;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_phb<B: Bus>(&mut self, bus: &mut B) {
        self.push(bus, self.dbr);
    }

    fn op_bcc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::C) == 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_tya(&mut self) {
        if (self.p & Flags::M) != 0 {
            let result = self.y[0];
            self.c[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.y);
            self.c = self.y;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_txs(&mut self) {
        if self.mode == Mode::Emulation {
            self.s[0] = self.x[0];
        } else {
            self.s = self.x;
        }
    }

    fn op_txy(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.x[0];
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.x);
            self.y = self.x;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_ldy<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::X) != 0 {
            let data = bus.read(addr);
            self.y[0] = data;
            self.set_flag(Flags::N, (data & 0x80) != 0);
            self.set_flag(Flags::Z, data == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let result = u16::from_le_bytes([lo, hi]);
            self.y = [lo, hi];
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_lda<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            self.c[0] = data;
            self.set_flag(Flags::N, (data & 0x80) != 0);
            self.set_flag(Flags::Z, data == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let result = u16::from_le_bytes([lo, hi]);
            self.c = [lo, hi];
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_ldx<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            self.x[0] = data;
            self.set_flag(Flags::N, (data & 0x80) != 0);
            self.set_flag(Flags::Z, data == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let result = u16::from_le_bytes([lo, hi]);
            self.x = [lo, hi];
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tay(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.c[0];
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.c);
            self.y = self.c;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tax(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.c[0];
            self.x[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.c);
            self.x = self.c;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_plb<B: Bus>(&mut self, bus: &mut B) {
        let result = self.pull(bus);
        self.pbr = result;
        self.set_flag(Flags::N, (result & 0x80) != 0);
        self.set_flag(Flags::Z, result == 0);
    }

    fn op_bcs<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::C) != 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_clv(&mut self) {
        self.set_flag(Flags::V, false);
    }

    fn op_tsx(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.s[0];
            self.x[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.s);
            self.x = self.s;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_tyx(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.x[0];
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let result = u16::from_le_bytes(self.x);
            self.y = self.x;
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_cpy<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::X) != 0 {
            let data = bus.read(addr);
            let (result, carry) = self.y[0].overflowing_sub(data);
            self.y[0] = result;
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let y = u16::from_le_bytes(self.y);
            let (result, carry) = y.overflowing_sub(data);
            self.y = result.to_le_bytes();
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_cmp<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let (result, carry) = self.c[0].overflowing_sub(data);
            self.c[0] = result;
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let c = u16::from_le_bytes(self.c);
            let (result, carry) = c.overflowing_sub(data);
            self.c = result.to_le_bytes();
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_rep<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let data = bus.read(addr);
        self.set_flag(data, false);
        if self.mode == Mode::Emulation {
            self.set_flag(Flags::X | Flags::M, true);
        }
    }

    fn op_dec<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = data.wrapping_sub(1);
            bus.write(addr, result);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = data.wrapping_sub(1);
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_iny(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.y[0].wrapping_add(1);
            self.y[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let y = u16::from_le_bytes(self.y);
            let result = y.wrapping_add(1);
            self.y = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_dex(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.x[0].wrapping_sub(1);
            self.x[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let x = u16::from_le_bytes(self.x);
            let result = x.wrapping_sub(1);
            self.x = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_wai(&mut self) {
        todo!();
    }

    fn op_bne<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::Z) == 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_pei<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        todo!();
    }

    fn op_cld(&mut self) {
        self.set_flag(Flags::D, false);
    }

    fn op_phx<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::X) != 0 {
            self.push(bus, self.x[0]);
        } else {
            self.push(bus, self.x[1]);
            self.push(bus, self.x[0]);
        }
    }

    fn op_stp(&mut self) {
        todo!();
    }

    fn op_cpx<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::X) != 0 {
            let data = bus.read(addr);
            let (result, carry) = self.x[0].overflowing_sub(data);
            self.x[0] = result;
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let x = u16::from_le_bytes(self.x);
            let (result, carry) = x.overflowing_sub(data);
            self.x = result.to_le_bytes();
            self.set_flag(Flags::C, carry);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_sbc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = !bus.read(addr); // invert!
            let (result, carry1) = self.c[0].overflowing_sub(data);
            let (result, carry2) =
                result.overflowing_add(if (self.p & Flags::C) != 0 { 1 } else { 0 });
            let overflow = ((!(self.c[0] ^ data)) & (self.c[0] ^ result) & 0x80) != 0;
            self.c[0] = result;
            self.set_flag(Flags::V, overflow);
            self.set_flag(Flags::C, carry1 || carry2);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = !u16::from_le_bytes([lo, hi]); // invert!
            let c = u16::from_le_bytes(self.c);
            let (result, carry1) = c.overflowing_add(data);
            let (result, carry2) =
                result.overflowing_add(if (self.p & Flags::C) != 0 { 1 } else { 0 });
            let overflow = ((!(c ^ data)) & (c ^ result) & 0x8000) != 0;
            self.c = result.to_le_bytes();
            self.set_flag(Flags::V, overflow);
            self.set_flag(Flags::C, carry1 || carry2);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_sep<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let data = bus.read(addr);
        self.set_p(data);
    }

    fn op_inc<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        if (self.p & Flags::M) != 0 {
            let data = bus.read(addr);
            let result = data.wrapping_add(1);
            bus.write(addr, result);
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = bus.read(addr);
            let hi = bus.read(addr.wrapping_add(1));
            let data = u16::from_le_bytes([lo, hi]);
            let result = data.wrapping_add(1);
            bus.write(addr, result as u8);
            bus.write(addr.wrapping_add(1), (result >> 8) as u8);
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_inx(&mut self) {
        if (self.p & Flags::X) != 0 {
            let result = self.x[0].wrapping_add(1);
            self.x[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let x = u16::from_le_bytes(self.x);
            let result = x.wrapping_add(1);
            self.x = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_nop(&mut self) {}

    fn op_xba(&mut self) {
        let tmp = self.c[1];
        self.c[1] = self.c[0];
        self.c[0] = tmp;
        self.set_flag(Flags::N, (tmp & 0x80) != 0);
        self.set_flag(Flags::Z, tmp == 0);
    }

    fn op_beq<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        let offset = bus.read(addr) as i8;
        if (self.p & Flags::Z) != 0 {
            self.pc = self.pc.wrapping_add_signed(offset as i16);
        }
    }

    fn op_pea<B: Bus, A: Fn(&mut Self, &mut B) -> u32>(&mut self, bus: &mut B, ea: A) {
        let addr = ea(self, bus);
        self.push(bus, (addr >> 8) as u8);
        self.push(bus, addr as u8);
    }

    fn op_sed(&mut self) {
        self.set_flag(Flags::D, true);
    }

    fn op_plx<B: Bus>(&mut self, bus: &mut B) {
        if (self.p & Flags::X) != 0 {
            let result = self.pull(bus);
            self.x[0] = result;
            self.set_flag(Flags::N, (result & 0x80) != 0);
            self.set_flag(Flags::Z, result == 0);
        } else {
            let lo = self.pull(bus);
            let hi = self.pull(bus);
            let result = u16::from_le_bytes([lo, hi]);
            self.x = result.to_le_bytes();
            self.set_flag(Flags::N, (result & 0x8000) != 0);
            self.set_flag(Flags::Z, result == 0);
        }
    }

    fn op_xce(&mut self) {
        let carry = (self.p & Flags::C) != 0;
        self.set_flag(Flags::C, self.mode == Mode::Emulation);
        if carry {
            self.mode = Mode::Emulation;
            self.set_flag(Flags::X | Flags::M, true);
            self.x[1] = 0;
            self.y[1] = 0;
            self.s[1] = 1;
        } else {
            self.mode = Mode::Native;
        }
    }
}

impl BusDevice for Cpu {
    fn reset<B: Bus>(&mut self, bus: &mut B) {
        let lo = bus.read(0x00FFFC);
        let hi = bus.read(0x00FFFD);
        self.pc = u16::from_le_bytes([lo, hi]);
        self.x[1] = 0;
        self.y[1] = 0;
        self.s = [0, 1];
        self.d = 0;
        self.dbr = 0;
        self.pbr = 0;
        self.p = Flags::M | Flags::X | Flags::I | Flags::E;
        self.abort = false;
        self.nmi = false;
        self.irq = false;
        self.mode = Mode::Emulation;
    }

    fn tick<B: Bus>(&mut self, bus: &mut B) {
        /*
        if self.abort {
            self.abort = false;
            self.interrupt(bus, IntKind::Abrt);
            return;
        }
        if self.nmi {
            self.nmi = false;
            self.interrupt(bus, IntKind::Nmi);
            return;
        }
        if self.irq && ((self.p & Flags::I) == 0) {
            self.irq = false;
            self.interrupt(bus, IntKind::Irq);
            return;
        }
        */
        match self.fetch(bus) {
            0x00 => self.op_brk(bus, Self::addr_imm8),
            0x01 => self.op_ora(bus, Self::addr_idx),
            0x02 => self.op_cop(bus, Self::addr_imm8),
            0x03 => self.op_ora(bus, Self::addr_sr),
            0x04 => self.op_tsb(bus, Self::addr_dp),
            0x05 => self.op_ora(bus, Self::addr_dp),
            0x06 => self.op_asl(bus, Self::addr_dp),
            0x07 => self.op_ora(bus, Self::addr_idl),
            0x08 => self.op_php(bus),
            0x09 if (self.p & Flags::M) == 0 => self.op_ora(bus, Self::addr_imm16),
            0x09 => self.op_ora(bus, Self::addr_imm8),
            0x0A => self.op_asl_a(),
            0x0B => self.op_phd(bus),
            0x0C => self.op_tsb(bus, Self::addr_abs),
            0x0D => self.op_ora(bus, Self::addr_abs),
            0x0E => self.op_asl(bus, Self::addr_abs),
            0x0F => self.op_ora(bus, Self::addr_abl),

            0x10 => self.op_bpl(bus, Self::addr_imm8),
            0x11 => self.op_ora(bus, Self::addr_idy),
            0x12 => self.op_ora(bus, Self::addr_idp),
            0x13 => self.op_ora(bus, Self::addr_isy),
            0x14 => self.op_trb(bus, Self::addr_dp),
            0x15 => self.op_ora(bus, Self::addr_dpx),
            0x16 => self.op_asl(bus, Self::addr_dpx),
            0x17 => self.op_ora(bus, Self::addr_ily),
            0x18 => self.op_clc(),
            0x19 => self.op_ora(bus, Self::addr_aby),
            0x1A => self.op_inc_a(),
            0x1B => self.op_tcs(),
            0x1C => self.op_trb(bus, Self::addr_abs),
            0x1D => self.op_ora(bus, Self::addr_abx),
            0x1E => self.op_asl(bus, Self::addr_abx),
            0x1F => self.op_ora(bus, Self::addr_alx),

            0x20 => self.op_jsr(bus, Self::addr_abs),
            0x21 => self.op_and(bus, Self::addr_idx),
            0x22 => self.op_jsl(bus, Self::addr_abl),
            0x23 => self.op_and(bus, Self::addr_sr),
            0x24 => self.op_bit(bus, Self::addr_dp),
            0x25 => self.op_and(bus, Self::addr_dp),
            0x26 => self.op_rol(bus, Self::addr_dp),
            0x27 => self.op_and(bus, Self::addr_idl),
            0x28 => self.op_plp(bus),
            0x29 if (self.p & Flags::M) == 0 => self.op_and(bus, Self::addr_imm16),
            0x29 => self.op_and(bus, Self::addr_imm8),
            0x2A => self.op_rol_a(),
            0x2B => self.op_pld(bus),
            0x2C => self.op_bit(bus, Self::addr_abs),
            0x2D => self.op_and(bus, Self::addr_abs),
            0x2E => self.op_rol(bus, Self::addr_abs),
            0x2F => self.op_and(bus, Self::addr_abl),

            0x30 => self.op_bmi(bus, Self::addr_imm8),
            0x31 => self.op_and(bus, Self::addr_idy),
            0x32 => self.op_and(bus, Self::addr_idp),
            0x33 => self.op_and(bus, Self::addr_isy),
            0x34 => self.op_bit(bus, Self::addr_dpx),
            0x35 => self.op_and(bus, Self::addr_idx),
            0x36 => self.op_rol(bus, Self::addr_dpx),
            0x37 => self.op_and(bus, Self::addr_ily),
            0x38 => self.op_sec(),
            0x39 => self.op_and(bus, Self::addr_aby),
            0x3A => self.op_dec_a(),
            0x3B => self.op_tsc(),
            0x3C => self.op_bit(bus, Self::addr_abx),
            0x3D => self.op_and(bus, Self::addr_abx),
            0x3E => self.op_rol(bus, Self::addr_abx),
            0x3F => self.op_and(bus, Self::addr_alx),

            0x40 => self.op_rti(bus),
            0x41 => self.op_eor(bus, Self::addr_idx),
            0x42 => self.op_wdc(bus, Self::addr_imm8),
            0x43 => self.op_eor(bus, Self::addr_sr),
            0x44 => self.op_mvp(bus),
            0x45 => self.op_eor(bus, Self::addr_dp),
            0x46 => self.op_lsr(bus, Self::addr_dp),
            0x47 => self.op_eor(bus, Self::addr_idl),
            0x48 => self.op_pha(bus),
            0x49 if (self.p & Flags::M) == 0 => self.op_eor(bus, Self::addr_imm16),
            0x49 => self.op_eor(bus, Self::addr_imm8),
            0x4A => self.op_lsr_a(),
            0x4B => self.op_phk(bus),
            0x4C => self.op_jmp(bus, Self::addr_abs),
            0x4D => self.op_eor(bus, Self::addr_abs),
            0x4E => self.op_lsr(bus, Self::addr_abs),
            0x4F => self.op_and(bus, Self::addr_abl),

            0x50 => self.op_bvc(bus, Self::addr_imm8),
            0x51 => self.op_eor(bus, Self::addr_idy),
            0x52 => self.op_eor(bus, Self::addr_idp),
            0x53 => self.op_eor(bus, Self::addr_isy),
            0x54 => self.op_mvn(bus),
            0x55 => self.op_eor(bus, Self::addr_dpx),
            0x56 => self.op_lsr(bus, Self::addr_dpx),
            0x57 => self.op_eor(bus, Self::addr_ily),
            0x58 => self.op_cli(),
            0x59 => self.op_eor(bus, Self::addr_aby),
            0x5A => self.op_phy(bus),
            0x5B => self.op_tcd(),
            0x5C => self.op_jml(bus, Self::addr_ial),
            0x5D => self.op_eor(bus, Self::addr_abx),
            0x5E => self.op_lsr(bus, Self::addr_abx),
            0x5F => self.op_eor(bus, Self::addr_alx),

            0x60 => self.op_rts(bus),
            0x61 => self.op_adc(bus, Self::addr_idx),
            0x62 => self.op_per(bus, Self::addr_imm16),
            0x63 => self.op_adc(bus, Self::addr_sr),
            0x64 => self.op_stz(bus, Self::addr_dp),
            0x65 => self.op_adc(bus, Self::addr_dp),
            0x66 => self.op_ror(bus, Self::addr_dp),
            0x67 => self.op_adc(bus, Self::addr_idl),
            0x68 => self.op_pla(bus),
            0x69 if (self.p & Flags::M) == 0 => self.op_adc(bus, Self::addr_imm16),
            0x69 => self.op_adc(bus, Self::addr_imm8),
            0x6A => self.op_ror_a(),
            0x6B => self.op_rtl(bus),
            0x6C => self.op_jmp(bus, Self::addr_iab),
            0x6D => self.op_adc(bus, Self::addr_abs),
            0x6E => self.op_ror(bus, Self::addr_abs),
            0x6F => self.op_adc(bus, Self::addr_abl),

            0x70 => self.op_bvs(bus, Self::addr_imm8),
            0x71 => self.op_adc(bus, Self::addr_idy),
            0x72 => self.op_adc(bus, Self::addr_idp),
            0x73 => self.op_adc(bus, Self::addr_isy),
            0x74 => self.op_stz(bus, Self::addr_idx),
            0x75 => self.op_adc(bus, Self::addr_dpx),
            0x76 => self.op_ror(bus, Self::addr_dpx),
            0x77 => self.op_adc(bus, Self::addr_ily),
            0x78 => self.op_sei(),
            0x79 => self.op_adc(bus, Self::addr_aby),
            0x7A => self.op_ply(bus),
            0x7B => self.op_tdc(),
            0x7C => self.op_jmp(bus, Self::addr_iax),
            0x7D => self.op_adc(bus, Self::addr_abx),
            0x7E => self.op_ror(bus, Self::addr_abx),
            0x7F => self.op_adc(bus, Self::addr_alx),

            0x80 => self.op_bra(bus, Self::addr_imm8),
            0x81 => self.op_sta(bus, Self::addr_idx),
            0x82 => self.op_brl(bus, Self::addr_imm16),
            0x83 => self.op_sta(bus, Self::addr_sr),
            0x84 => self.op_sty(bus, Self::addr_dp),
            0x85 => self.op_sta(bus, Self::addr_dp),
            0x86 => self.op_stx(bus, Self::addr_dp),
            0x87 => self.op_stx(bus, Self::addr_idl),
            0x88 => self.op_dey(),
            0x89 if (self.p & Flags::M) == 0 => self.op_bit(bus, Self::addr_imm16),
            0x89 => self.op_bit(bus, Self::addr_imm8),
            0x8A => self.op_txa(),
            0x8B => self.op_phb(bus),
            0x8C => self.op_sty(bus, Self::addr_abs),
            0x8D => self.op_sta(bus, Self::addr_abs),
            0x8E => self.op_stx(bus, Self::addr_abs),
            0x8F => self.op_sta(bus, Self::addr_abl),

            0x90 => self.op_bcc(bus, Self::addr_imm8),
            0x91 => self.op_sta(bus, Self::addr_idy),
            0x92 => self.op_sta(bus, Self::addr_idp),
            0x93 => self.op_sta(bus, Self::addr_isy),
            0x94 => self.op_sty(bus, Self::addr_dpx),
            0x95 => self.op_sta(bus, Self::addr_dpx),
            0x96 => self.op_stx(bus, Self::addr_dpy),
            0x97 => self.op_sta(bus, Self::addr_ily),
            0x98 => self.op_tya(),
            0x99 => self.op_sta(bus, Self::addr_aby),
            0x9A => self.op_txs(),
            0x9B => self.op_txy(),
            0x9C => self.op_stz(bus, Self::addr_abs),
            0x9D => self.op_sta(bus, Self::addr_abx),
            0x9E => self.op_stz(bus, Self::addr_abx),
            0x9F => self.op_sta(bus, Self::addr_alx),

            0xA0 if (self.p & Flags::X) == 0 => self.op_ldy(bus, Self::addr_imm16),
            0xA0 => self.op_ldy(bus, Self::addr_imm8),
            0xA1 => self.op_lda(bus, Self::addr_idx),
            0xA2 if (self.p & Flags::X) == 0 => self.op_ldx(bus, Self::addr_imm16),
            0xA2 => self.op_ldx(bus, Self::addr_imm8),
            0xA3 => self.op_lda(bus, Self::addr_sr),
            0xA4 => self.op_ldy(bus, Self::addr_dp),
            0xA5 => self.op_lda(bus, Self::addr_dp),
            0xA6 => self.op_ldx(bus, Self::addr_dp),
            0xA7 => self.op_lda(bus, Self::addr_idl),
            0xA8 => self.op_tay(),
            0xA9 if (self.p & Flags::M) == 0 => self.op_lda(bus, Self::addr_imm16),
            0xA9 => self.op_lda(bus, Self::addr_imm8),
            0xAA => self.op_tax(),
            0xAB => self.op_plb(bus),
            0xAC => self.op_ldy(bus, Self::addr_abs),
            0xAD => self.op_lda(bus, Self::addr_abs),
            0xAE => self.op_ldx(bus, Self::addr_abs),
            0xAF => self.op_lda(bus, Self::addr_abl),

            0xB0 => self.op_bcs(bus, Self::addr_imm8),
            0xB1 => self.op_lda(bus, Self::addr_idy),
            0xB2 => self.op_lda(bus, Self::addr_idp),
            0xB3 => self.op_lda(bus, Self::addr_isy),
            0xB4 => self.op_ldy(bus, Self::addr_dpx),
            0xB5 => self.op_lda(bus, Self::addr_dpx),
            0xB6 => self.op_ldx(bus, Self::addr_dpy),
            0xB7 => self.op_lda(bus, Self::addr_ily),
            0xB8 => self.op_clv(),
            0xB9 => self.op_lda(bus, Self::addr_aby),
            0xBA => self.op_tsx(),
            0xBB => self.op_tyx(),
            0xBC => self.op_ldy(bus, Self::addr_abx),
            0xBD => self.op_lda(bus, Self::addr_abx),
            0xBE => self.op_ldx(bus, Self::addr_aby),
            0xBF => self.op_lda(bus, Self::addr_alx),

            0xC0 if (self.p & Flags::X) == 0 => self.op_cpy(bus, Self::addr_imm16),
            0xC0 => self.op_cpy(bus, Self::addr_imm8),
            0xC1 => self.op_cmp(bus, Self::addr_idx),
            0xC2 => self.op_rep(bus, Self::addr_imm8),
            0xC3 => self.op_cmp(bus, Self::addr_sr),
            0xC4 => self.op_cpy(bus, Self::addr_dp),
            0xC5 => self.op_cmp(bus, Self::addr_dp),
            0xC6 => self.op_dec(bus, Self::addr_dp),
            0xC7 => self.op_cmp(bus, Self::addr_idl),
            0xC8 => self.op_iny(),
            0xC9 if (self.p & Flags::M) == 0 => self.op_cmp(bus, Self::addr_imm16),
            0xC9 => self.op_cmp(bus, Self::addr_imm8),
            0xCA => self.op_dex(),
            0xCB => self.op_wai(),
            0xCC => self.op_cpy(bus, Self::addr_abs),
            0xCD => self.op_cmp(bus, Self::addr_abs),
            0xCE => self.op_dec(bus, Self::addr_abs),
            0xCF => self.op_cmp(bus, Self::addr_abl),

            0xD0 => self.op_bne(bus, Self::addr_imm8),
            0xD1 => self.op_cmp(bus, Self::addr_idy),
            0xD2 => self.op_cmp(bus, Self::addr_idp),
            0xD3 => self.op_cmp(bus, Self::addr_isy),
            0xD4 => self.op_pei(bus, Self::addr_idp),
            0xD5 => self.op_cmp(bus, Self::addr_dpx),
            0xD6 => self.op_dec(bus, Self::addr_dpx),
            0xD7 => self.op_cmp(bus, Self::addr_ily),
            0xD8 => self.op_cld(),
            0xD9 => self.op_cmp(bus, Self::addr_aby),
            0xDA => self.op_phx(bus),
            0xDB => self.op_stp(),
            0xDC => self.op_jmp(bus, Self::addr_ial),
            0xDD => self.op_cmp(bus, Self::addr_abx),
            0xDE => self.op_dec(bus, Self::addr_abx),
            0xDF => self.op_cmp(bus, Self::addr_alx),

            0xE0 if (self.p & Flags::X) == 0 => self.op_cpx(bus, Self::addr_imm16),
            0xE0 => self.op_cpx(bus, Self::addr_imm8),
            0xE1 => self.op_sbc(bus, Self::addr_idx),
            0xE2 => self.op_sep(bus, Self::addr_imm8),
            0xE3 => self.op_sbc(bus, Self::addr_sr),
            0xE4 => self.op_cpy(bus, Self::addr_dp),
            0xE5 => self.op_sbc(bus, Self::addr_dp),
            0xE6 => self.op_inc(bus, Self::addr_dp),
            0xE7 => self.op_sbc(bus, Self::addr_idl),
            0xE8 => self.op_inx(),
            0xE9 if (self.p & Flags::M) == 0 => self.op_sbc(bus, Self::addr_imm16),
            0xE9 => self.op_sbc(bus, Self::addr_imm8),
            0xEA => self.op_nop(),
            0xEB => self.op_xba(),
            0xEC => self.op_cpx(bus, Self::addr_abs),
            0xED => self.op_sbc(bus, Self::addr_abs),
            0xEE => self.op_inc(bus, Self::addr_abs),
            0xEF => self.op_sbc(bus, Self::addr_abl),

            0xF0 => self.op_beq(bus, Self::addr_imm8),
            0xF1 => self.op_sbc(bus, Self::addr_idy),
            0xF2 => self.op_sbc(bus, Self::addr_idp),
            0xF3 => self.op_sbc(bus, Self::addr_isy),
            0xF4 => self.op_pea(bus, Self::addr_abs),
            0xF5 => self.op_sbc(bus, Self::addr_dpx),
            0xF6 => self.op_inc(bus, Self::addr_dpx),
            0xF7 => self.op_sbc(bus, Self::addr_ily),
            0xF8 => self.op_sed(),
            0xF9 => self.op_sbc(bus, Self::addr_aby),
            0xFA => self.op_plx(bus),
            0xFB => self.op_xce(),
            0xFC => self.op_jsr(bus, Self::addr_iax),
            0xFD => self.op_sbc(bus, Self::addr_abx),
            0xFE => self.op_inc(bus, Self::addr_abx),
            0xFF => self.op_sbc(bus, Self::addr_alx),
        };
    }
}
