use std::{
    error::Error,
    fs::File,
    io::{self, ErrorKind, Read, Seek, Write},
    marker::PhantomData,
    mem,
    path::PathBuf,
    process::ExitCode,
    slice,
    str::{self, FromStr},
};

use clap::Parser;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Input file
    input: PathBuf,

    /// Output file (default: stdout)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Symbol file
    #[arg(short, long)]
    sym: Option<PathBuf>,

    /// Pre-defined symbols (repeatable)
    #[arg(short = 'D', long, value_name="KEY1=val", value_parser = parse_defines::<String, i32>)]
    define: Vec<(String, i32)>,
}

fn parse_defines<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid SYMBOL=value: no `=` found in `{s}`"))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

fn main() -> ExitCode {
    if let Err(e) = main_real() {
        eprintln!("{e}");
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn main_real() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    let file = File::open(args.input).map_err(|e| format!("cant open file: {e}"))?;
    let lexer = Lexer::new(file);
    let output: Box<dyn Write> = match args.output {
        Some(path) => Box::new(
            File::options()
                .write(true)
                .create(true)
                .truncate(true)
                .open(path)
                .map_err(|e| format!("cant open file: {e}"))?,
        ),
        None => Box::new(io::stdout()),
    };

    let mut asm = Asm::new(lexer, output);
    for (name, val) in &args.define {
        let string = asm.str_int.intern(name);
        asm.syms.push((Label::new(None, string), *val));
    }

    eprint!("pass1: ");
    asm.pass()?;
    eprintln!("ok");

    eprint!("pass2: ");
    asm.rewind()?;
    asm.pass()?;
    eprintln!("ok");

    eprintln!("== stats ==");
    eprintln!("symbols: {}", asm.syms.len());
    eprintln!(
        "string heap: {}/{} bytes",
        asm.str_int
            .storages
            .iter()
            .fold(0, |accum, storage| accum + storage.len()),
        asm.str_int
            .storages
            .iter()
            .fold(0, |accum, storage| accum + storage.capacity())
    );
    eprintln!(
        "macro heap: {}/{} bytes",
        asm.tok_int.storages.iter().fold(0, |accum, storage| accum
            + (storage.len() * mem::size_of::<MacroTok>())),
        asm.tok_int.storages.iter().fold(0, |accum, storage| accum
            + (storage.capacity() * mem::size_of::<MacroTok>()))
    );

    Ok(())
}

struct Asm<'a> {
    toks: Vec<Box<dyn TokStream + 'a>>,
    str_int: StrInterner<'a>,
    tok_int: TokInterner<'a>,
    output: Box<dyn Write>,
    pc: u32,
    dat: u32,
    pc_end: bool,
    dat_end: bool,
    dat_mode: bool,
    c16_mode: bool,
    accum_16: bool,
    index_16: bool,
    syms: Vec<(Label<'a>, i32)>,
    scope: Option<&'a str>,
    emit: bool,
    if_level: usize,

    macros: Vec<Macro<'a>>,

    values: Vec<i32>,
    operators: Vec<Op>,
}

impl<'a> Asm<'a> {
    fn new<R: Read + Seek + 'static>(lexer: Lexer<R>, output: Box<dyn Write>) -> Self {
        Self {
            toks: vec![Box::new(lexer)],
            str_int: StrInterner::new(),
            tok_int: TokInterner::new(),
            output,
            pc: 0,
            dat: 0,
            pc_end: false,
            dat_end: false,
            dat_mode: false,
            c16_mode: false,
            accum_16: false,
            index_16: false,
            syms: Vec::new(),
            scope: None,
            emit: false,
            if_level: 0,

            macros: Vec::new(),

            values: Vec::new(),
            operators: Vec::new(),
        }
    }

    fn rewind(&mut self) -> io::Result<()> {
        self.toks.last_mut().unwrap().rewind()?;
        self.pc = 0;
        self.dat = 0;
        self.pc_end = false;
        self.dat_end = false;
        self.dat_mode = false;
        self.c16_mode = false;
        self.accum_16 = false;
        self.index_16 = false;
        self.scope = None;
        self.emit = true;
        self.if_level = 0;
        self.macros.clear();
        Ok(())
    }

    fn pass(&mut self) -> io::Result<()> {
        loop {
            if self.peek()? == Tok::EOF {
                if self.toks.len() <= 1 {
                    break;
                }
                self.toks.pop();
            }
            // special case, setting the PC
            if self.peek()? == Tok::STAR {
                self.eat();
                if (self.peek()? != Tok::IDENT) && !self.str_like("EQU") {
                    return Err(self.err("expected equ"));
                }
                self.eat();
                let expr = self.expr()?;
                self.set_pc(self.const_24(expr)?);
                self.eol()?;
                continue;
            }
            if self.peek()? == Tok::IDENT {
                let mne = MNEMONICS.iter().find(|mne| self.str_like(mne.0 .0));
                let dir = DIRECTIVES.iter().find(|dir| self.str_like(dir.0 .0));
                // is this a label?
                if mne.is_none() && dir.is_none() && !self.str_like("EQU") && !self.str_like("MAC")
                {
                    // is this a defined macro?
                    if let Some(mac) = self
                        .macros
                        .iter()
                        .find(|mac| self.str() == mac.name)
                        .copied()
                    {
                        let line = self.tok().line();
                        self.eat();
                        let mut args = Vec::new();
                        loop {
                            match self.peek()? {
                                Tok::NEWLINE | Tok::EOF => break,
                                Tok::IDENT => args.push(MacroTok::Ident(self.str_intern())),
                                Tok::STR => args.push(MacroTok::Str(self.str_intern())),
                                Tok::NUM => args.push(MacroTok::Num(self.tok().num())),
                                tok => args.push(MacroTok::Tok(tok)),
                            }
                            self.eat();
                            if self.peek()? != Tok::COMMA {
                                break;
                            }
                            self.eat();
                        }
                        self.toks.push(Box::new(MacroInvocation {
                            inner: mac,
                            line,
                            index: 0,
                            args,
                        }));
                        continue;
                    }

                    let string = self.str_intern();
                    let label = if !self.str().starts_with(".") {
                        self.scope.replace(string);
                        Label::new(None, string)
                    } else {
                        Label::new(self.scope, string)
                    };
                    self.eat();

                    // being defined to a macro?
                    if (self.peek()? == Tok::IDENT) && self.str_like("MAC") {
                        if label.string.starts_with(".") {
                            return Err(self.err("macro must be global"));
                        }
                        self.eat();
                        self.macrodef(label)?;
                        self.eol()?;
                        continue;
                    }
                    let index = if let Some(item) = self
                        .syms
                        .iter()
                        .enumerate()
                        .find(|item| &item.1 .0 == &label)
                    {
                        // allowed to redef during second pass
                        // TODO: should test if label value didnt change
                        // TODO: allow variable kinds that are redefinable
                        if !self.emit {
                            return Err(self.err("symbol already defined"));
                        }
                        item.0
                    } else {
                        // save in the symbol table with default value
                        let index = self.syms.len();
                        self.syms.push((label, 0));
                        index
                    };
                    // check if this label is being defined to a value
                    if (self.peek()? == Tok::IDENT) && self.str_like("EQU") {
                        self.eat();
                        let expr = self.expr()?;
                        if self.emit {
                            self.syms[index].1 = self.const_expr(expr)?;
                        } else if let Some(expr) = expr {
                            self.syms[index].1 = expr;
                        } else {
                            // we couldn't evaluate this yet, so remove it
                            self.syms.pop();
                        }
                        self.eol()?;
                        continue;
                    }
                    // otherwise it is a pointer to the current PC
                    self.syms[index].1 = self.pc() as i32;
                    continue;
                }
                // if this isn't a mnemonic or directive, then its an error
                if mne.is_none() && dir.is_none() {
                    return Err(self.err("unrecognized instruction"));
                }
                // is this a directive
                if let Some((dir, allow_dat)) = dir {
                    if self.dat_mode && !allow_dat {
                        return Err(self.err("not allowed in dat mode"));
                    }
                    self.directive(*dir)?;
                    self.eol()?;
                    continue;
                }
                // must be an mnemonic
                self.eat();
                self.operand(mne.unwrap())?;
            }
            self.eol()?;
        }
        Ok(())
    }

    fn pc(&self) -> u32 {
        if self.dat_mode {
            self.dat
        } else {
            self.pc
        }
    }

    fn set_pc(&mut self, val: u32) {
        if self.dat_mode {
            self.dat = val;
        } else {
            self.pc = val;
        }
    }

    fn add_pc(&mut self, amt: u32) -> io::Result<()> {
        let val = self.pc().wrapping_add(amt);
        if (val < self.pc()) || (val > 0x01000000) {
            return Err(self.err("pc overflow"));
        }
        self.set_pc(val);
        Ok(())
    }

    fn err(&self, msg: &str) -> io::Error {
        self.tok().err(msg)
    }

    fn str(&self) -> &str {
        self.tok().str()
    }

    fn str_like(&self, string: &str) -> bool {
        self.tok().str().eq_ignore_ascii_case(string)
    }

    fn str_intern(&mut self) -> &'a str {
        let Self {
            ref mut str_int,
            toks,
            ..
        } = self;
        let string = toks.last().unwrap().str();
        str_int.intern(string)
    }

    fn peek(&mut self) -> io::Result<Tok> {
        self.tok_mut().peek()
    }

    fn eat(&mut self) {
        self.tok_mut().eat();
    }

    fn write(&mut self, buf: &[u8]) -> io::Result<()> {
        self.output.write_all(buf)
    }

    fn write_str(&mut self) -> io::Result<()> {
        let Self {
            ref mut output,
            toks,
            ..
        } = self;
        output.write_all(toks.last().unwrap().str().as_bytes())
    }

    fn tok(&self) -> &dyn TokStream {
        self.toks.last().unwrap().as_ref()
    }

    fn tok_mut(&mut self) -> &mut dyn TokStream {
        self.toks.last_mut().unwrap().as_mut()
    }

    fn eol(&mut self) -> io::Result<()> {
        match self.peek()? {
            Tok::NEWLINE => {
                self.eat();
                Ok(())
            }
            Tok::EOF => {
                if self.toks.len() > 1 {
                    self.toks.pop();
                }
                Ok(())
            }
            _ => Err(self.err("expected end of line")),
        }
    }

    fn const_expr(&self, expr: Option<i32>) -> io::Result<i32> {
        expr.ok_or_else(|| self.err("expression unresolved"))
    }

    fn const_24(&self, expr: Option<i32>) -> io::Result<u32> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > 0x007FFFFFu32 {
            return Err(self.err("expression >3 bytes"));
        }
        Ok(expr as u32)
    }

    fn const_16(&self, expr: Option<i32>) -> io::Result<u16> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u16::MAX as u32) {
            return Err(self.err("expression >2 bytes"));
        }
        Ok(expr as u16)
    }

    fn const_8(&self, expr: Option<i32>) -> io::Result<u8> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u8::MAX as u32) {
            return Err(self.err("expression >1 byte"));
        }
        Ok(expr as u8)
    }

    fn expr_precedence(&self, op: Op) -> u8 {
        match op {
            Op::Unary(Tok::LPAREN) => 0xFF, // lparen is lowest precedence
            Op::Unary(_) => 0,              // other unary is highest precedence
            Op::Binary(Tok::SOLIDUS | Tok::MODULUS | Tok::STAR) => 1,
            Op::Binary(Tok::PLUS | Tok::MINUS) => 2,
            Op::Binary(Tok::ASL | Tok::ASR | Tok::LSR) => 3,
            Op::Binary(Tok::LT | Tok::LTE | Tok::GT | Tok::GTE) => 4,
            Op::Binary(Tok::EQ | Tok::NEQ) => 5,
            Op::Binary(Tok::AMP) => 6,
            Op::Binary(Tok::CARET) => 7,
            Op::Binary(Tok::PIPE) => 8,
            Op::Binary(Tok::AND) => 9,
            Op::Binary(Tok::OR) => 10,
            _ => unreachable!(),
        }
    }

    fn expr_apply(&mut self, op: Op) {
        let rhs = self.values.pop().unwrap();
        match op {
            Op::Unary(Tok::PLUS) => self.values.push(rhs),
            Op::Unary(Tok::MINUS) => self.values.push(-rhs),
            Op::Unary(Tok::TILDE) => self.values.push(!rhs),
            Op::Unary(Tok::BANG) => self.values.push((rhs == 0) as i32),
            Op::Unary(Tok::LT) => self.values.push(((rhs as u32) & 0xFF) as i32),
            Op::Unary(Tok::GT) => self.values.push((((rhs as u32) & 0xFF00) >> 8) as i32),
            Op::Unary(Tok::CARET) => self.values.push((((rhs as u32) & 0xFF0000) >> 16) as i32),
            Op::Binary(tok) => {
                let lhs = self.values.pop().unwrap();
                match tok {
                    Tok::PLUS => self.values.push(lhs.wrapping_add(rhs)),
                    Tok::MINUS => self.values.push(lhs.wrapping_sub(rhs)),
                    Tok::STAR => self.values.push(lhs.wrapping_mul(rhs)),
                    Tok::SOLIDUS => self.values.push(lhs.wrapping_div(rhs)),
                    Tok::MODULUS => self.values.push(lhs.wrapping_rem(rhs)),
                    Tok::ASL => self.values.push(lhs.wrapping_shl(rhs as u32)),
                    Tok::ASR => self.values.push(lhs.wrapping_shr(rhs as u32)),
                    Tok::LSR => self
                        .values
                        .push((lhs as u32).wrapping_shl(rhs as u32) as i32),
                    Tok::LT => self.values.push((lhs < rhs) as i32),
                    Tok::LTE => self.values.push((lhs <= rhs) as i32),
                    Tok::GT => self.values.push((lhs > rhs) as i32),
                    Tok::GTE => self.values.push((lhs >= rhs) as i32),
                    Tok::EQ => self.values.push((lhs == rhs) as i32),
                    Tok::NEQ => self.values.push((lhs != rhs) as i32),
                    Tok::AMP => self.values.push(lhs & rhs),
                    Tok::PIPE => self.values.push(lhs | rhs),
                    Tok::CARET => self.values.push(lhs ^ rhs),
                    Tok::AND => self.values.push(((lhs != 0) && (rhs != 0)) as i32),
                    Tok::OR => self.values.push(((lhs != 0) || (rhs != 0)) as i32),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }

    fn expr_push_apply(&mut self, op: Op) {
        while let Some(top) = self.operators.last() {
            if self.expr_precedence(*top) > self.expr_precedence(op) {
                break;
            }
            self.expr_apply(*top);
            self.operators.pop();
        }
        self.operators.push(op);
    }

    fn expr(&mut self) -> io::Result<Option<i32>> {
        self.values.clear();
        self.operators.clear();
        let mut seen_val = false;
        let mut paren_depth = 0;
        let mut seen_unknown_label = false;
        loop {
            match self.peek()? {
                // star is multiply or the PC
                Tok::STAR => {
                    if !seen_val {
                        self.values.push(self.pc() as i32);
                        seen_val = true;
                        self.eat();
                        continue;
                    }
                    self.expr_push_apply(Op::Binary(Tok::STAR));
                    seen_val = false;
                    self.eat();
                    continue;
                }
                // these are optionally unary
                tok @ (Tok::PLUS | Tok::MINUS | Tok::CARET | Tok::LT | Tok::GT) => {
                    if seen_val {
                        self.expr_push_apply(Op::Binary(tok));
                    } else {
                        self.expr_push_apply(Op::Unary(tok));
                    }
                    seen_val = false;
                    self.eat();
                    continue;
                }
                // always unary
                tok @ (Tok::BANG | Tok::TILDE) => {
                    if !seen_val {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Unary(tok));
                    seen_val = false;
                    self.eat();
                    continue;
                }
                #[rustfmt::skip]
                tok @ (Tok::PIPE | Tok::AND | Tok::OR | Tok::SOLIDUS | Tok::MODULUS | Tok::ASL
                      | Tok::ASR | Tok::LSR | Tok::LTE | Tok::GTE | Tok::EQ | Tok::NEQ) => {
                    if !seen_val {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Binary(tok));
                    seen_val = false;
                    self.eat();
                    continue;
                }
                Tok::NUM => {
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(self.tok().num());
                    seen_val = true;
                    self.eat();
                    continue;
                }
                Tok::LPAREN => {
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    paren_depth += 1;
                    self.operators.push(Op::Unary(Tok::LPAREN));
                    seen_val = false;
                    self.eat();
                    continue;
                }
                Tok::RPAREN => {
                    // this rparen is probably part of the indirect address
                    if self.operators.is_empty() && (paren_depth == 0) {
                        break;
                    }
                    paren_depth -= 1;
                    if !seen_val {
                        return Err(self.err("expected value"));
                    }
                    loop {
                        if let Some(op) = self.operators.pop() {
                            // we apply ops until we see the start of this grouping
                            match op {
                                Op::Binary(tok) | Op::Unary(tok) if tok == Tok::LPAREN => {
                                    break;
                                }
                                _ => {}
                            }
                            self.expr_apply(op);
                        } else {
                            return Err(self.err("unbalanced parens"));
                        }
                    }
                    self.eat();
                    continue;
                }
                Tok::IDENT => {
                    let string = self.str_intern();
                    let label = if !self.str().starts_with(".") {
                        Label::new(None, string)
                    } else {
                        Label::new(self.scope, string)
                    };
                    if let Some(sym) = self.syms.iter().find(|sym| &sym.0 == &label).copied() {
                        if seen_val {
                            return Err(self.err("expected operator"));
                        }
                        self.values.push(sym.1);
                        seen_val = true;
                        self.eat();
                        continue;
                    }
                    seen_unknown_label = true;
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(1);
                    seen_val = true;
                    self.eat();
                    continue;
                }
                _ => break,
            }
        }
        while let Some(top) = self.operators.pop() {
            self.expr_apply(top);
        }
        if seen_unknown_label {
            return Ok(None);
        }
        if let Some(value) = self.values.pop() {
            return Ok(Some(value));
        }
        Err(self.err("expected value"))
    }

    fn find_opcode(&self, addrs: &[u8; 23], addr: Addr) -> Option<u8> {
        let op = addrs[addr.0 as usize];
        if op == ____ {
            return None;
        }
        Some(op)
    }

    fn check_opcode(&self, addrs: &[u8; 23], addr: Addr) -> io::Result<u8> {
        let op = self
            .find_opcode(addrs, addr)
            .ok_or_else(|| self.err("illegal address mode"))?;
        if !self.c16_mode && C16_OPCODES.contains(&op) {
            Err(self.err("illegal instruction"))
        } else {
            Ok(op)
        }
    }

    fn expect(&mut self, tok: Tok) -> io::Result<()> {
        if self.peek()? != tok {
            return Err(self.err("unexpected garbage"));
        }
        self.eat();
        Ok(())
    }

    fn operand(&mut self, mne: &(Mne, &[u8; 23])) -> io::Result<()> {
        match self.peek()? {
            Tok::NEWLINE => {
                let op = self.check_opcode(mne.1, Addr::IMP)?;
                if self.emit {
                    self.write(&[op])?;
                }
                self.add_pc(1)
            }
            Tok::HASH => {
                // TODO: I hate checking the mnemonic
                // could use a table instead
                #[rustfmt::skip]
                let width = match mne.0 {
                    Mne::ADC | Mne::AND | Mne::BIT | Mne::CMP | Mne::EOR | Mne::ORA | Mne::LDA | Mne::SBC
                        => if self.accum_16 { 2 } else { 1 },
                    Mne::CPX | Mne::CPY | Mne::LDX | Mne::LDY
                        => if self.index_16 { 2 } else { 1 },
                    _ => 1,
                };
                let op = self.check_opcode(mne.1, Addr::IMM)?;
                self.eat();
                let expr = self.expr()?;
                if self.emit {
                    self.write(&[op])?;
                    if width == 1 {
                        self.write(&self.const_8(expr)?.to_le_bytes())?;
                    } else {
                        self.write(&self.const_16(expr)?.to_le_bytes())?;
                    }
                }
                self.add_pc(1 + width)
            }
            Tok::LPAREN => {
                self.eat();
                let expr = self.expr()?;
                // TODO: hate, but it makes it easy to know whether its an IAB or IAX
                if let Mne::JMP | Mne::JSR = mne.0 {
                    let op = if self.peek()? == Tok::COMMA {
                        let op = self.check_opcode(mne.1, Addr::IAX)?;
                        self.eat();
                        self.expect(Tok::X)?;
                        op
                    } else {
                        self.check_opcode(mne.1, Addr::IAB)?
                    };
                    self.expect(Tok::RPAREN)?;
                    if self.emit {
                        self.write(&[op])?;
                        self.write(&self.const_16(expr)?.to_le_bytes())?;
                    }
                    return self.add_pc(3);
                }
                // IDX or ISY
                if self.peek()? == Tok::COMMA {
                    self.eat();
                    let op = if self.peek()? == Tok::S {
                        let op = self.check_opcode(mne.1, Addr::ISY)?;
                        self.eat();
                        self.expect(Tok::COMMA)?;
                        self.expect(Tok::Y)?;
                        op
                    } else {
                        let op = self.check_opcode(mne.1, Addr::IDX)?;
                        self.expect(Tok::COMMA)?;
                        self.expect(Tok::X)?;
                        op
                    };
                    self.expect(Tok::RPAREN)?;
                    if self.emit {
                        self.write(&[op])?;
                        self.write(&self.const_8(expr)?.to_le_bytes())?;
                    }
                    return self.add_pc(2);
                }
                self.expect(Tok::RPAREN)?;
                // IDP or IDY
                let op = if self.peek()? == Tok::COMMA {
                    let op = self.check_opcode(mne.1, Addr::IDY)?;
                    self.eat();
                    self.expect(Tok::Y)?;
                    op
                } else {
                    self.check_opcode(mne.1, Addr::IDP)?
                };
                if self.emit {
                    self.write(&[op])?;
                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                }
                self.add_pc(2)
            }
            Tok::LBRACK => {
                self.eat();
                let expr = self.expr()?;
                // TODO: hate, but it makes it easy to know whether its an IAL
                if mne.0 == Mne::JML {
                    let op = self.check_opcode(mne.1, Addr::IAL)?;
                    self.expect(Tok::RBRACK)?;
                    if self.emit {
                        self.write(&[op])?;
                        self.write(&self.const_16(expr)?.to_le_bytes())?;
                    }
                    return self.add_pc(3);
                }
                self.expect(Tok::RBRACK)?;
                // IDL or ILY
                let op = if self.peek()? == Tok::COMMA {
                    let op = self.check_opcode(mne.1, Addr::ILY)?;
                    self.eat();
                    self.expect(Tok::Y)?;
                    op
                } else {
                    self.check_opcode(mne.1, Addr::IDL)?
                };
                if self.emit {
                    self.write(&[op])?;
                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                }
                self.add_pc(2)
            }
            _ => {
                if let Some(op) = self.find_opcode(mne.1, Addr::REL) {
                    self.check_opcode(mne.1, Addr::REL)?; // handle c02 errors
                    let expr = self.expr()?;
                    if self.emit {
                        let branch = (self.pc() as i32) + self.const_expr(expr)?;
                        if (branch < (i8::MIN as i32)) || (branch > (i8::MAX as i32)) {
                            return Err(self.err("branch distance too far"));
                        }
                        self.write(&[op])?;
                        self.write(&(branch as i8).to_le_bytes())?;
                    }
                    return self.add_pc(2);
                }
                if let Some(op) = self.find_opcode(mne.1, Addr::RLL) {
                    self.check_opcode(mne.1, Addr::RLL)?; // handle c02 errors
                    let expr = self.expr()?;
                    if self.emit {
                        let branch = (self.pc() as i32) + self.const_expr(expr)?;
                        if (branch < (i16::MIN as i32)) || (branch > (i16::MAX as i32)) {
                            return Err(self.err("branch distance too far"));
                        }
                        self.write(&[op])?;
                        self.write(&(branch as i16).to_le_bytes())?;
                    }
                    return self.add_pc(3);
                }
                if let Some(op) = self.find_opcode(mne.1, Addr::BM) {
                    self.check_opcode(mne.1, Addr::BM)?; // handle c02 errors
                    let src = self.expr()?;
                    self.expect(Tok::COMMA)?;
                    let dst = self.expr()?;
                    if self.emit {
                        self.write(&[op])?;
                        self.write(&self.const_8(src)?.to_le_bytes())?;
                        self.write(&self.const_8(dst)?.to_le_bytes())?;
                    }
                    return self.add_pc(3);
                }
                // check for address width override
                let width = match self.peek()? {
                    Tok::PIPE => {
                        self.eat();
                        Width::ABS
                    }
                    Tok::ASP => {
                        self.eat();
                        Width::ABL
                    }
                    _ => Width::DP,
                };
                let expr = self.expr()?;
                match (width, self.peek()?) {
                    // SR, DPX, DPY
                    (Width::DP, Tok::COMMA) => {
                        self.eat();
                        match self.peek()? {
                            Tok::S => {
                                self.eat();
                                let op = self.check_opcode(mne.1, Addr::SR)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(2)
                            }
                            Tok::X => {
                                // try promoting up
                                if let Some(val) = expr {
                                    if (val as u32) > (u16::MAX as u32) {
                                        let op = self.check_opcode(mne.1, Addr::ALX)?;
                                        if self.emit {
                                            self.write(&[op])?;
                                            self.write(&self.const_24(expr)?.to_le_bytes())?;
                                        }
                                        self.eat();
                                        return self.add_pc(4);
                                    }
                                    if (val as u32) > (u8::MAX as u32) {
                                        let op = self.check_opcode(mne.1, Addr::ABX)?;
                                        if self.emit {
                                            self.write(&[op])?;
                                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                                        }
                                        self.eat();
                                        return self.add_pc(3);
                                    }
                                }
                                let op = self.check_opcode(mne.1, Addr::DPX)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.eat();
                                self.add_pc(2)
                            }
                            Tok::Y => {
                                // try promoting up
                                if let Some(val) = expr {
                                    if (val as u32) > (u8::MAX as u32) {
                                        let op = self.check_opcode(mne.1, Addr::ABY)?;
                                        if self.emit {
                                            self.write(&[op])?;
                                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                                        }
                                        self.eat();
                                        return self.add_pc(3);
                                    }
                                }
                                let op = self.check_opcode(mne.1, Addr::DPY)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.eat();
                                self.add_pc(2)
                            }
                            _ => Err(self.err("illegal address mode")),
                        }
                    }
                    // DP
                    (Width::DP, _) => {
                        // try promoting up
                        if let Some(val) = expr {
                            if (val as u32) > (u16::MAX as u32) {
                                let op = self.check_opcode(mne.1, Addr::ABL)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_24(expr)?.to_le_bytes())?;
                                }
                                return self.add_pc(4);
                            }
                            if (val as u32) > (u8::MAX as u32) {
                                let op = self.check_opcode(mne.1, Addr::ABS)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                                }
                                return self.add_pc(3);
                            }
                        }
                        let op = self.check_opcode(mne.1, Addr::DP)?;
                        if self.emit {
                            self.write(&[op])?;
                            self.write(&self.const_8(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(2)
                    }
                    // ABX or ABY
                    (Width::ABS, Tok::COMMA) => {
                        self.eat();
                        match self.peek()? {
                            Tok::X => {
                                // try promoting up
                                if let Some(val) = expr {
                                    if (val as u32) > (u16::MAX as u32) {
                                        let op = self.check_opcode(mne.1, Addr::ALX)?;
                                        if self.emit {
                                            self.write(&[op])?;
                                            self.write(&self.const_24(expr)?.to_le_bytes())?;
                                        }
                                        self.eat();
                                        return self.add_pc(4);
                                    }
                                }
                                let op = self.check_opcode(mne.1, Addr::ABX)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                                }
                                self.eat();
                                self.add_pc(3)
                            }
                            Tok::Y => {
                                let op = self.check_opcode(mne.1, Addr::ABY)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                                }
                                self.eat();
                                self.add_pc(3)
                            }
                            _ => Err(self.err("illegal address mode")),
                        }
                    }
                    // ABS
                    (Width::ABS, _) => {
                        // try promoting up
                        if let Some(val) = expr {
                            if (val as u32) > (u16::MAX as u32) {
                                let op = self.check_opcode(mne.1, Addr::ABL)?;
                                if self.emit {
                                    self.write(&[op])?;
                                    self.write(&self.const_24(expr)?.to_le_bytes())?;
                                }
                                return self.add_pc(4);
                            }
                        }
                        let op = self.check_opcode(mne.1, Addr::ABS)?;
                        if self.emit {
                            self.write(&[op])?;
                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(3)
                    }
                    // ALX
                    (Width::ABL, Tok::X) => {
                        let op = self.check_opcode(mne.1, Addr::ALX)?;
                        if self.emit {
                            self.write(&[op])?;
                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                        }
                        self.eat();
                        self.add_pc(3)
                    }
                    // ABL
                    (Width::ABL, _) => {
                        let op = self.check_opcode(mne.1, Addr::ABL)?;
                        if self.emit {
                            self.write(&[op])?;
                            self.write(&self.const_24(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(4)
                    }
                }
            }
        }
    }

    fn directive(&mut self, dir: Dir) -> io::Result<()> {
        match dir {
            Dir::BYT => loop {
                self.eat();
                if self.peek()? == Tok::STR {
                    if self.emit {
                        self.write_str()?;
                    }
                    self.add_pc(self.str().len() as u32)?;
                    self.eat();
                } else {
                    let expr = self.expr()?;
                    if self.emit {
                        self.write(&self.const_8(expr)?.to_le_bytes())?;
                    }
                    self.add_pc(1)?;
                }
                if self.peek()? != Tok::COMMA {
                    break;
                }
                self.eat();
            },
            Dir::WRD => loop {
                self.eat();
                let expr = self.expr()?;
                if self.emit {
                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                }
                self.add_pc(2)?;
                if self.peek()? != Tok::COMMA {
                    break;
                }
                self.eat();
            },
            Dir::DAT => {
                self.eat();
                self.dat_mode = true;
            }
            Dir::PRG => {
                self.eat();
                self.dat_mode = false;
            }
            Dir::PAD => {
                self.eat();
                let expr = self.expr()?;
                let pad = self.const_24(expr)?;
                if self.emit && !self.dat_mode {
                    for _ in 0..pad {
                        self.write(&[0])?;
                    }
                }
                self.add_pc(pad)?;
            }
            Dir::ADJ => {
                self.eat();
                let expr = self.expr()?;
                let adj = self.pc() % self.const_24(expr)?;
                if self.emit {
                    for _ in 0..adj {
                        self.write(&[0])?;
                    }
                }
                self.add_pc(adj)?;
            }
            Dir::PUT => {
                self.eat();
                if self.peek()? != Tok::STR {
                    return Err(self.err("expected file name"));
                }
                let file = File::open(self.str())?;
                self.eat();
                let lexer = Lexer::new(file);
                self.toks.push(Box::new(lexer));
            }
            Dir::IFF | Dir::IFD | Dir::IFN => {
                self.eat();
                let expr = self.expr()?;
                let skip = match dir {
                    Dir::IFF => self.const_expr(expr)? == 0,
                    Dir::IFD => expr.is_none(),
                    Dir::IFN => expr.is_some(),
                    _ => unreachable!(),
                };
                if skip {
                    let mut if_level = 0;
                    loop {
                        if self.peek()? == Tok::IDENT {
                            if self.str_like(Dir::IFF.0)
                                || self.str_like(Dir::IFD.0)
                                || self.str_like(Dir::IFN.0)
                                || self.str_like("MAC")
                            {
                                if_level += 1;
                            } else if self.str_like(Dir::END.0) {
                                if if_level == 0 {
                                    self.eat();
                                    return Ok(());
                                }
                                if_level -= 1;
                            }
                        }
                        self.eat();
                    }
                }
                self.if_level += 1;
            }
            Dir::END => {
                if self.if_level == 0 {
                    return Err(self.err("unexpected end"));
                }
                self.eat();
                self.if_level -= 1;
            }
            Dir::I08 => {
                self.eat();
                self.index_16 = false;
            }
            Dir::I16 => {
                self.eat();
                self.index_16 = true;
            }
            Dir::A08 => {
                self.eat();
                self.accum_16 = false;
            }
            Dir::A16 => {
                self.eat();
                self.accum_16 = true;
            }
            Dir::C02 => {
                self.eat();
                self.c16_mode = false;
            }
            Dir::C16 => {
                self.eat();
                self.c16_mode = true;
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn macrodef(&mut self, label: Label<'a>) -> io::Result<()> {
        self.eol()?;
        let mut toks = Vec::new();
        let mut if_level = 0;
        loop {
            if self.peek()? == Tok::IDENT {
                if self.str_like(Dir::IFF.0)
                    || self.str_like(Dir::IFD.0)
                    || self.str_like(Dir::IFN.0)
                    || self.str_like("MAC")
                {
                    if_level += 1;
                } else if self.str_like(Dir::END.0) {
                    if if_level == 0 {
                        self.eat();
                        toks.push(MacroTok::Tok(Tok::EOF));
                        break;
                    }
                    if_level -= 1;
                }
            }
            match self.peek()? {
                Tok::EOF => return Err(self.err("unexpected end of file")),
                Tok::IDENT => toks.push(MacroTok::Ident(self.str_intern())),
                Tok::STR => toks.push(MacroTok::Str(self.str_intern())),
                Tok::NUM => toks.push(MacroTok::Num(self.tok().num())),
                Tok::ARG => toks.push(MacroTok::Arg((self.tok().num() as usize) - 1)),
                tok => toks.push(MacroTok::Tok(tok)),
            }
            self.eat();
        }
        let toks = self.tok_int.intern(&toks);
        self.macros.push(Macro {
            name: label.string,
            toks,
        });
        Ok(())
    }
}

enum Width {
    DP,
    ABS,
    ABL,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Addr(u8);

#[rustfmt::skip]
impl Addr {
    const IMP: Self = Self(0);  //
    const IMM: Self = Self(1);  // #$00
    const SR: Self = Self(2);   // $00,S
    const DP: Self = Self(3);   // $00
    const DPX: Self = Self(4);  // $00,X
    const DPY: Self = Self(5);  // $00,Y
    const IDP: Self = Self(6);  // ($00)
    const IDX: Self = Self(7);  // ($00,X)
    const IDY: Self = Self(8);  // ($00),Y
    const IDL: Self = Self(9);  // [$00]
    const ILY: Self = Self(10); // [$00],Y
    const ISY: Self = Self(11); // ($00,S),Y
    const ABS: Self = Self(12); // |$0000
    const ABX: Self = Self(13); // |$0000,X
    const ABY: Self = Self(14); // |$0000,Y
    const ABL: Self = Self(15); // @$000000
    const ALX: Self = Self(16); // @$000000,X
    const IAB: Self = Self(17); // ($0000)
    const IAX: Self = Self(18); // ($0000,X)
    const IAL: Self = Self(19); // [$0000]
    const REL: Self = Self(20); // ±$00
    const RLL: Self = Self(21); // ±$0000
    const BM: Self = Self(22);  // $00,$00
}

#[derive(PartialEq, Eq)]
struct Mne(&'static str); // I really only newtype these to create namespaces

impl Mne {
    const ADC: Self = Self("ADC");
    const AND: Self = Self("AND");
    const ASL: Self = Self("ASL");
    const BCC: Self = Self("BCC");
    const BCS: Self = Self("BCS");
    const BEQ: Self = Self("BEQ");
    const BIT: Self = Self("BIT");
    const BMI: Self = Self("BMI");
    const BNE: Self = Self("BNE");
    const BPL: Self = Self("BPL");
    const BRA: Self = Self("BRA");
    const BRK: Self = Self("BRK");
    const BRL: Self = Self("BRL");
    const BVC: Self = Self("BVC");
    const BVS: Self = Self("BVS");
    const CLC: Self = Self("CLC");
    const CLD: Self = Self("CLD");
    const CLI: Self = Self("CLI");
    const CLV: Self = Self("CLV");
    const CMP: Self = Self("CMP");
    const COP: Self = Self("COP");
    const CPX: Self = Self("CPX");
    const CPY: Self = Self("CPY");
    const DEC: Self = Self("DEC");
    const DEX: Self = Self("DEX");
    const DEY: Self = Self("DEY");
    const EOR: Self = Self("EOR");
    const INC: Self = Self("INC");
    const INX: Self = Self("INX");
    const INY: Self = Self("INY");
    const JML: Self = Self("JML");
    const JMP: Self = Self("JMP");
    const JSL: Self = Self("JSL");
    const JSR: Self = Self("JSR");
    const LDA: Self = Self("LDA");
    const LDX: Self = Self("LDX");
    const LDY: Self = Self("LDY");
    const LSR: Self = Self("LSR");
    const MVN: Self = Self("MVN");
    const MVP: Self = Self("MVP");
    const NOP: Self = Self("NOP");
    const ORA: Self = Self("ORA");
    const PEA: Self = Self("PEA");
    const PEI: Self = Self("PEI");
    const PER: Self = Self("PER");
    const PHA: Self = Self("PHA");
    const PHB: Self = Self("PHB");
    const PHD: Self = Self("PHD");
    const PHK: Self = Self("PHK");
    const PHP: Self = Self("PHP");
    const PHX: Self = Self("PHX");
    const PHY: Self = Self("PHY");
    const PLA: Self = Self("PLA");
    const PLB: Self = Self("PLB");
    const PLD: Self = Self("PLD");
    const PLP: Self = Self("PLP");
    const PLX: Self = Self("PLX");
    const PLY: Self = Self("PLY");
    const REP: Self = Self("REP");
    const ROL: Self = Self("ROL");
    const ROR: Self = Self("ROR");
    const RTI: Self = Self("RTI");
    const RTL: Self = Self("RTL");
    const RTS: Self = Self("RTS");
    const SBC: Self = Self("SBC");
    const SEC: Self = Self("SEC");
    const SED: Self = Self("SED");
    const SEI: Self = Self("SEI");
    const SEP: Self = Self("SEP");
    const STA: Self = Self("STA");
    const STP: Self = Self("STP");
    const STX: Self = Self("STX");
    const STY: Self = Self("STY");
    const STZ: Self = Self("STZ");
    const TAX: Self = Self("TAX");
    const TAY: Self = Self("TAY");
    const TCD: Self = Self("TCD");
    const TCS: Self = Self("TCS");
    const TDC: Self = Self("TDC");
    const TRB: Self = Self("TRB");
    const TSB: Self = Self("TSB");
    const TSC: Self = Self("TSC");
    const TSX: Self = Self("TSX");
    const TXA: Self = Self("TXA");
    const TXS: Self = Self("TXS");
    const TXY: Self = Self("TXY");
    const TYA: Self = Self("TYA");
    const TYX: Self = Self("TYX");
    const WAI: Self = Self("WAI");
    const WDC: Self = Self("WDC");
    const XBA: Self = Self("XBA");
    const XCE: Self = Self("XCE");
}

const ____: u8 = 0x42; // $42 (WDC) is reserved so we special-case it as a blank

#[rustfmt::skip]
const MNEMONICS: &[(Mne, &[u8; 23])] = &[
    //           imp   imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   iab   iax   ial   rel   rll   bm
    (Mne::ADC, &[____, 0x69, 0x63, 0x65, 0x75, ____, 0x72, 0x61, 0x71, 0x67, 0x77, 0x73, 0x6D, 0x7D, 0x79, 0x6F, 0x7F, ____, ____, ____, ____, ____, ____]),
    (Mne::AND, &[____, 0x29, 0x23, 0x25, 0x35, ____, 0x32, 0x21, 0x31, 0x27, 0x37, 0x33, 0x2D, 0x3D, 0x39, 0x2F, 0x3F, ____, ____, ____, ____, ____, ____]),
    (Mne::ASL, &[0x0A, ____, ____, 0x06, 0x16, ____, ____, ____, ____, ____, ____, ____, 0x0E, 0x1E, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::BCC, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x90, ____, ____]),
    (Mne::BCS, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0xB0, ____, ____]),
    (Mne::BNE, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0xD0, ____, ____]),
    (Mne::BEQ, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0xF0, ____, ____]),
    (Mne::BIT, &[____, 0x89, ____, 0x24, 0x34, ____, ____, ____, ____, ____, ____, ____, 0x2C, 0x3C, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::BPL, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x10, ____, ____]),
    (Mne::BMI, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x30, ____, ____]),
    (Mne::BRA, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x80, ____, ____]),
    (Mne::BRK, &[____, 0x00, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::BRL, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x82, ____]),
    (Mne::BVC, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x50, ____, ____]),
    (Mne::BVS, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x70, ____, ____]),
    (Mne::CLC, &[0x18, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CLD, &[0xD8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CLI, &[0x58, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CLV, &[0xB8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CMP, &[____, 0xC9, 0xC3, 0xC5, 0xD5, ____, 0xD2, 0xC1, 0xD1, 0xC7, 0xD7, 0xD3, 0xCD, 0xDD, 0xD9, 0xCF, 0xDF, ____, ____, ____, ____, ____, ____]),
    (Mne::COP, &[____, 0x02, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CPX, &[____, 0xE0, ____, 0xE4, ____, ____, ____, ____, ____, ____, ____, ____, 0xEC, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::CPY, &[____, 0xC0, ____, 0xC4, ____, ____, ____, ____, ____, ____, ____, ____, 0xCC, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    //           imp   imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   iab   iax   ial   rel   rll   bm
    (Mne::DEC, &[0x3A, ____, ____, 0xC6, 0xD6, ____, ____, ____, ____, ____, ____, ____, 0xCE, 0xDE, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::DEX, &[0xCA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::DEY, &[0x88, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::EOR, &[____, 0x49, 0x43, 0x45, 0x55, ____, 0x52, 0x41, 0x51, 0x47, 0x57, 0x53, 0x4D, 0x5D, 0x59, 0x4F, 0x5F, ____, ____, ____, ____, ____, ____]),
    (Mne::INC, &[0x1A, ____, ____, 0xE6, 0xF6, ____, ____, ____, ____, ____, ____, ____, 0xEE, 0xFE, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::INX, &[0xE8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::INY, &[0xC8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::JML, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x5C, ____, ____, ____, 0xDC, ____, ____, ____]),
    (Mne::JMP, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x4C, ____, ____, ____, ____, 0x6C, 0x7C, ____, ____, ____, ____]),
    (Mne::JSL, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x22, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::JSR, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x20, ____, ____, ____, ____, ____, 0xFC, ____, ____, ____, ____]),
    (Mne::LDA, &[____, 0xA9, 0xA3, 0xA5, 0xB5, ____, 0xB2, 0xA1, 0xB1, 0xA7, 0xB7, 0xB3, 0xAD, 0xBD, 0xB9, 0xAF, 0xBF, ____, ____, ____, ____, ____, ____]),
    (Mne::LDX, &[____, 0xA2, ____, 0xA6, ____, 0xB6, ____, ____, ____, ____, ____, ____, 0xAE, ____, 0xBE, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::LDY, &[____, 0xA0, ____, 0xA4, 0xB4, ____, ____, ____, ____, ____, ____, ____, 0xAC, 0xBC, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::LSR, &[0x4A, ____, ____, 0x46, 0x56, ____, ____, ____, ____, ____, ____, ____, 0x4E, 0x5E, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::MVN, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x54]),
    (Mne::MVP, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x44]),
    (Mne::NOP, &[0xEA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::ORA, &[____, 0x09, 0x03, 0x05, 0x15, ____, 0x12, 0x01, 0x11, 0x07, 0x17, 0x13, 0x0D, 0x1D, 0x19, 0x0F, 0x1F, ____, ____, ____, ____, ____, ____]),
    (Mne::PEA, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0xF4, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PEI, &[____, ____, ____, 0xD4, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PER, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, 0x62, ____]),
    //           imp   imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   iab   iax   ial   rel   rll   bm
    (Mne::PHA, &[0x48, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHB, &[0x8B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHD, &[0x0B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHK, &[0x4B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHP, &[0x08, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHX, &[0xDA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PHY, &[0x5A, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLA, &[0x68, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLB, &[0xAB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLD, &[0x2B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLP, &[0x28, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLX, &[0xFA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::PLY, &[0x7A, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::REP, &[____, 0xC2, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::ROL, &[0x2A, ____, ____, 0x26, 0x36, ____, ____, ____, ____, ____, ____, ____, 0x2E, 0x3E, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::ROR, &[0x6A, ____, ____, 0x66, 0x76, ____, ____, ____, ____, ____, ____, ____, 0x6E, 0x7E, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::RTI, &[0x40, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::RTL, &[0x6B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::RTS, &[0x60, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::SBC, &[____, 0xE9, 0xE3, 0xE5, 0xF5, ____, 0xF2, 0xE1, 0xF1, 0xE7, 0xF7, 0xF3, 0xED, 0xFD, 0xF9, 0xEF, 0xFF, ____, ____, ____, ____, ____, ____]),
    (Mne::SEC, &[0x38, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::SED, &[0xF8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::SEI, &[0x78, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    //           imp   imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   iab   iax   ial   rel   rll   bm
    (Mne::SEP, &[____, 0xE2, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::STA, &[____, ____, 0x83, 0x85, 0x95, ____, 0x92, 0x81, 0x91, 0x87, 0x97, 0x93, 0x8D, 0x9D, 0x99, 0x8F, 0xBF, ____, ____, ____, ____, ____, ____]),
    (Mne::STP, &[0xDB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::STX, &[____, ____, ____, 0x86, ____, 0x96, ____, ____, ____, ____, ____, ____, 0x8E, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::STY, &[____, ____, ____, 0x84, 0x94, ____, ____, ____, ____, ____, ____, ____, 0x8C, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::STZ, &[____, ____, ____, 0x64, 0x74, ____, ____, ____, ____, ____, ____, ____, 0x9C, 0x9E, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TAX, &[0xAA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TAY, &[0xA8, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TCD, &[0x5B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TCS, &[0x1B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TDC, &[0x7B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TRB, &[____, ____, ____, 0x14, ____, ____, ____, ____, ____, ____, ____, ____, 0x1C, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TSB, &[____, ____, ____, 0x04, ____, ____, ____, ____, ____, ____, ____, ____, 0x0C, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TSC, &[0x3B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TSX, &[0xBA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TXA, &[0x8A, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TXS, &[0x9A, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TXY, &[0x9B, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TYA, &[0x98, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::TYX, &[0xBB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::WAI, &[0xCB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::WDC, &[____, 0x42, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::XBA, &[0xEB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::XCE, &[0xFB, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
];

#[rustfmt::skip]
const C16_OPCODES: &[u8] = &[
    0x02, 0x03, 0x07, 0x0B, 0x0F, 0x13, 0x17, 0x1B, 0x1F, 0x22, 0x23, 0x27, 0x2B, 0x2F,
    0x33, 0x37, 0x3B, 0x3F, 0x24, 0x43, 0x44, 0x47, 0x4B, 0x4F, 0x53, 0x54, 0x57, 0x5B, 0x5C, 0x5F,
    0x62, 0x63, 0x67, 0x6B, 0x6F, 0x73, 0x77, 0x7B, 0x7F, 0x82, 0x83, 0x87, 0x8B, 0x8F,
    0x93, 0x97, 0x9B, 0x9F, 0xA3, 0xA7, 0xAB, 0xAF, 0xB3, 0xB7, 0xBB, 0xBF,
    0xC2, 0xC3, 0xC7, 0xCF, 0xD3, 0xD4, 0xD7, 0xDC, 0xDF,
    0xE2, 0xE3, 0xE7, 0xEB, 0xEF, 0xF3, 0xF4, 0xF7, 0xFB, 0xFC, 0xFF
];

#[derive(Clone, Copy, PartialEq, Eq)]
struct Dir(&'static str);

impl Dir {
    const BYT: Self = Self("BYT");
    const WRD: Self = Self("WRD");
    const DAT: Self = Self("DAT");
    const PRG: Self = Self("PRG");
    const PAD: Self = Self("PAD");
    const ADJ: Self = Self("ADJ");
    const PUT: Self = Self("PUT");
    const IFF: Self = Self("IFF");
    const IFD: Self = Self("IFD");
    const IFN: Self = Self("IFN");
    const END: Self = Self("END");
    const I08: Self = Self("I08");
    const I16: Self = Self("I16");
    const A08: Self = Self("A08");
    const A16: Self = Self("A16");
    const C02: Self = Self("C02");
    const C16: Self = Self("C16");
}

const DIRECTIVES: &[(Dir, bool)] = &[
    (Dir::BYT, false),
    (Dir::WRD, false),
    (Dir::DAT, false),
    (Dir::PRG, true),
    (Dir::PAD, true),
    (Dir::ADJ, true),
    (Dir::PUT, true),
    (Dir::IFF, true),
    (Dir::IFD, true),
    (Dir::IFN, true),
    (Dir::END, true),
    (Dir::I08, true),
    (Dir::I16, true),
    (Dir::A08, true),
    (Dir::A16, true),
    (Dir::C02, true),
    (Dir::C16, true),
];

#[derive(Copy, Clone, PartialEq, Eq)]
struct Tok(u8);

#[rustfmt::skip]
impl Tok {
    const NEWLINE: Self = Self(b'\n');
    const MODULUS: Self = Self(b'%');
    const SOLIDUS: Self = Self(b'/');
    const STAR: Self = Self(b'*');
    const PLUS: Self = Self(b'+');
    const MINUS: Self = Self(b'-');
    const LT: Self = Self(b'<');
    const GT: Self = Self(b'>');
    const AMP: Self = Self(b'&');
    const CARET: Self = Self(b'^');
    const PIPE: Self = Self(b'|');
    const LPAREN: Self = Self(b'(');
    const RPAREN: Self = Self(b')');
    const LBRACK: Self = Self(b'[');
    const RBRACK: Self = Self(b']');
    const BANG: Self = Self(b'!');
    const TILDE: Self = Self(b'~');
    const HASH: Self = Self(b'#');
    const COMMA: Self = Self(b',');
    const ASP: Self = Self(b'@');

    const X: Self = Self(b'X');
    const Y: Self = Self(b'Y');
    const S: Self = Self(b'S');

    const EOF: Self = Self(0x80);
    const IDENT: Self = Self(0x81);
    const NUM: Self = Self(0x82);
    const STR: Self = Self(0x83);
    const ARG: Self = Self(0x84);

    const ASL: Self = Self(0x85); // <<
    const ASR: Self = Self(0x86); // >>
    const LSR: Self = Self(0x87); // ~>
    const LTE: Self = Self(0x88); // <=
    const GTE: Self = Self(0x89); // >=
    const EQ: Self = Self(0x8A);  // ==
    const NEQ: Self = Self(0x8B); // !=
    const AND: Self = Self(0x8C); // &&
    const OR: Self = Self(0x8D);  // ||
}

const GRAPHEMES: &[(&[u8; 2], Tok)] = &[
    (b"<<", Tok::ASL),
    (b">>", Tok::ASR),
    (b"~>", Tok::LSR),
    (b"<=", Tok::LTE),
    (b">=", Tok::GTE),
    (b"==", Tok::EQ),
    (b"!=", Tok::NEQ),
    (b"&&", Tok::AND),
    (b"||", Tok::OR),
];

#[derive(Clone, Copy)]
enum Op {
    Binary(Tok),
    Unary(Tok),
}

trait TokStream {
    fn err(&self, msg: &str) -> io::Error;

    fn peek(&mut self) -> io::Result<Tok>;

    fn eat(&mut self);

    fn rewind(&mut self) -> io::Result<()>;

    fn str(&self) -> &str;

    fn num(&self) -> i32;

    fn line(&self) -> usize;
}

struct StrInterner<'a> {
    storages: Vec<String>,
    marker: PhantomData<&'a ()>,
}

impl<'a> StrInterner<'a> {
    fn new() -> Self {
        Self {
            storages: Vec::new(),
            marker: PhantomData,
        }
    }

    fn intern(&mut self, string: &str) -> &'a str {
        let mut has_space = None;
        for (i, storage) in self.storages.iter().enumerate() {
            // pre-check if we have space for the string in case we have a cache miss
            if has_space.is_none() && ((storage.capacity() - storage.len()) >= string.len()) {
                has_space = Some(i);
            }
            if let Some(index) = storage.find(string) {
                // SAFETY: the assumption is that we never re-allocate storages
                unsafe {
                    return str::from_utf8_unchecked(slice::from_raw_parts(
                        storage.as_ptr().add(index),
                        string.len(),
                    ));
                }
            }
        }
        // cache miss, add to a storage if possible
        let storage = if let Some(index) = has_space {
            &mut self.storages[index]
        } else {
            self.storages.push(String::with_capacity(
                string.len().next_multiple_of(2).max(256),
            ));
            self.storages.last_mut().unwrap()
        };
        let index = storage.len();
        storage.push_str(string);
        // SAFETY: the assumption is that we never re-allocate storages
        unsafe {
            str::from_utf8_unchecked(slice::from_raw_parts(
                storage.as_ptr().add(index),
                string.len(),
            ))
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Label<'a> {
    scope: Option<&'a str>,
    string: &'a str,
}

impl<'a> Label<'a> {
    fn new(scope: Option<&'a str>, string: &'a str) -> Self {
        Self { scope, string }
    }
}

struct Lexer<R> {
    reader: PeekReader<R>,
    string: String,
    number: i32,
    stash: Option<Tok>,
    line: usize,
}

impl<R: Read + Seek> Lexer<R> {
    fn new(reader: R) -> Self {
        Self {
            reader: PeekReader::new(reader),
            string: String::new(),
            number: 0,
            stash: None,
            line: 1,
        }
    }
}

impl<R: Read + Seek> TokStream for Lexer<R> {
    fn err(&self, msg: &str) -> io::Error {
        io::Error::new(ErrorKind::InvalidData, format!("{}: {msg}", self.line))
    }

    fn peek(&mut self) -> io::Result<Tok> {
        if let Some(tok) = self.stash {
            return Ok(tok);
        }
        // skip whitespace
        while let Some(c) = self.reader.peek()? {
            if !b" \t\r".contains(&c) {
                break;
            }
            self.reader.eat();
        }
        // skip comment
        if let Some(b';') = self.reader.peek()? {
            while !matches!(self.reader.peek()?, Some(b'\n')) {
                self.reader.eat();
            }
        }
        match self.reader.peek()? {
            None => {
                self.reader.eat();
                self.stash = Some(Tok::EOF);
                Ok(Tok::EOF)
            }
            // macro argument
            Some(b'\\') => {
                self.reader.eat();
                while let Some(c) = self.reader.peek()? {
                    if !c.is_ascii_digit() {
                        break;
                    }
                    self.string.push(c as char);
                    self.reader.eat();
                }
                self.number =
                    i32::from_str_radix(&self.string, 10).map_err(|e| self.err(&e.to_string()))?;
                if self.number < 1 {
                    return Err(self.err("argument must be positive"));
                }
                self.stash = Some(Tok::ARG);
                Ok(Tok::ARG)
            }
            // number
            Some(c) if c.is_ascii_digit() || c == b'$' || c == b'%' => {
                let radix = match c {
                    b'$' => {
                        self.reader.eat();
                        16
                    }
                    b'%' => {
                        self.reader.eat();
                        2
                    }
                    _ => 10,
                };
                // edge case: modulus
                if (c == b'%') && self.reader.peek()?.is_some_and(|nc| !b"01".contains(&nc)) {
                    self.stash = Some(Tok::MODULUS);
                    return Ok(Tok::MODULUS);
                }
                // parse number
                while let Some(c) = self.reader.peek()? {
                    if c == b'_' {
                        continue; // allow '_' separators in numbers
                    }
                    if !c.is_ascii_alphanumeric() {
                        break;
                    }
                    self.string.push(c as char);
                    self.reader.eat();
                }
                self.number = i32::from_str_radix(&self.string, radix)
                    .map_err(|e| self.err(&e.to_string()))?;
                self.stash = Some(Tok::NUM);
                Ok(Tok::NUM)
            }
            // string
            Some(b'"') => {
                self.reader.eat();
                while let Some(c) = self.reader.peek()? {
                    if c == b'"' {
                        self.reader.eat();
                        break;
                    }
                    self.string.push(c as char);
                    self.reader.eat();
                }
                self.stash = Some(Tok::STR);
                Ok(Tok::STR)
            }
            // char
            Some(b'\'') => {
                self.reader.eat();
                if let Some(c) = self.reader.peek()? {
                    if c.is_ascii_graphic() {
                        self.reader.eat();
                        self.number = c as i32;
                        self.stash = Some(Tok::NUM);
                        return Ok(Tok::NUM);
                    }
                }
                Err(self.err("unexpected garbage"))
            }
            // idents and single chars
            Some(c) => {
                while let Some(c) = self.reader.peek()? {
                    if !c.is_ascii_alphanumeric() && !b"_.".contains(&c) {
                        break;
                    }
                    self.reader.eat();
                    self.string.push(c as char);
                }
                if self.string.len() > 1 {
                    if self.string.len() > 16 {
                        return Err(self.err("label too long"));
                    }
                    self.stash = Some(Tok::IDENT);
                    return Ok(Tok::IDENT);
                }
                // the char wasn't an ident, so wasnt eaten
                if self.string.len() == 0 {
                    self.reader.eat();
                }
                // check for grapheme
                if let Some(nc) = self.reader.peek()? {
                    let s = &[c, nc];
                    if let Some(tok) = GRAPHEMES
                        .iter()
                        .find_map(|(bs, tok)| (*bs == s).then_some(tok))
                        .copied()
                    {
                        self.reader.eat();
                        self.stash = Some(tok);
                        return Ok(tok);
                    }
                }
                // else return an uppercase of whatever this char is
                self.stash = Some(Tok(c.to_ascii_uppercase()));
                Ok(Tok(c.to_ascii_uppercase()))
            }
        }
    }

    fn eat(&mut self) {
        self.string.clear();
        if let Some(Tok::NEWLINE) = self.stash.take() {
            self.line += 1;
        }
    }

    fn rewind(&mut self) -> io::Result<()> {
        self.string.clear();
        self.stash = None;
        self.line = 1;
        self.reader.rewind()
    }

    fn str(&self) -> &str {
        &self.string
    }

    fn num(&self) -> i32 {
        self.number
    }

    fn line(&self) -> usize {
        self.line
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MacroTok<'a> {
    Tok(Tok),
    Str(&'a str),
    Ident(&'a str),
    Num(i32),
    Arg(usize),
}

#[derive(Clone, Copy)]
struct Macro<'a> {
    name: &'a str,
    toks: &'a [MacroTok<'a>],
}

struct MacroInvocation<'a> {
    inner: Macro<'a>,
    line: usize,
    index: usize,
    args: Vec<MacroTok<'a>>,
}

impl<'a> TokStream for MacroInvocation<'a> {
    fn err(&self, msg: &str) -> io::Error {
        io::Error::new(
            ErrorKind::InvalidData,
            format!("{}:{}: {msg}", self.line, self.inner.name),
        )
    }

    fn peek(&mut self) -> io::Result<Tok> {
        match self.inner.toks[self.index] {
            MacroTok::Tok(tok) => Ok(tok),
            MacroTok::Str(_) => Ok(Tok::STR),
            MacroTok::Ident(_) => Ok(Tok::IDENT),
            MacroTok::Num(_) => Ok(Tok::NUM),
            MacroTok::Arg(index) => {
                if index >= self.args.len() {
                    return Err(self.err("argument is undefined"));
                }
                match self.args[index] {
                    MacroTok::Tok(tok) => Ok(tok),
                    MacroTok::Str(_) => Ok(Tok::STR),
                    MacroTok::Ident(_) => Ok(Tok::IDENT),
                    MacroTok::Num(_) => Ok(Tok::NUM),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn eat(&mut self) {
        self.index += 1;
    }

    fn rewind(&mut self) -> io::Result<()> {
        self.index = 0;
        Ok(())
    }

    fn str(&self) -> &str {
        match self.inner.toks[self.index] {
            MacroTok::Str(string) => string,
            MacroTok::Ident(string) => string,
            MacroTok::Arg(index) => match self.args[index] {
                MacroTok::Str(string) => string,
                MacroTok::Ident(string) => string,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn num(&self) -> i32 {
        match self.inner.toks[self.index] {
            MacroTok::Num(val) => val,
            MacroTok::Arg(index) => match self.args[index] {
                MacroTok::Num(val) => val,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn line(&self) -> usize {
        self.line
    }
}

struct TokInterner<'a> {
    storages: Vec<Vec<MacroTok<'a>>>,
}

impl<'a> TokInterner<'a> {
    fn new() -> Self {
        Self {
            storages: Vec::new(),
        }
    }

    fn intern(&mut self, toks: &[MacroTok<'a>]) -> &'a [MacroTok<'a>] {
        let mut has_space = None;
        for (i, storage) in self.storages.iter().enumerate() {
            // pre-check if we have space for the toks in case we have a cache miss
            if has_space.is_none() && ((storage.capacity() - storage.len()) >= toks.len()) {
                has_space = Some(i);
            }
            if let Some(index) = storage.windows(toks.len()).position(|win| win == toks) {
                // SAFETY: the assumption is that we never re-allocate storages
                unsafe {
                    return slice::from_raw_parts(storage.as_ptr().add(index), toks.len());
                }
            }
        }
        // cache miss, add to a storage if possible
        let storage = if let Some(index) = has_space {
            &mut self.storages[index]
        } else {
            self.storages.push(Vec::with_capacity(toks.len().max(256)));
            self.storages.last_mut().unwrap()
        };
        let index = storage.len();
        storage.extend_from_slice(toks);
        // SAFETY: the assumption is that we never re-allocate storages
        unsafe { slice::from_raw_parts(storage.as_ptr().add(index), toks.len()) }
    }
}

struct PeekReader<R> {
    inner: R,
    stash: Option<u8>,
}

impl<R: Read + Seek> PeekReader<R> {
    fn new(reader: R) -> Self {
        Self {
            inner: reader,
            stash: None,
        }
    }

    fn peek(&mut self) -> io::Result<Option<u8>> {
        if self.stash.is_none() {
            let mut buf = [0];
            self.stash = self
                .inner
                .read(&mut buf)
                .map(|n| if n == 0 { None } else { Some(buf[0]) })?;
        }
        Ok(self.stash)
    }

    fn eat(&mut self) {
        self.stash.take();
    }

    fn rewind(&mut self) -> io::Result<()> {
        self.stash = None;
        self.inner.rewind()
    }
}
