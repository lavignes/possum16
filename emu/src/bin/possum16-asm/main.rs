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
    let file = File::open(args.input).map_err(|e| format!("cannot open file: {e}"))?;
    let lexer = Lexer::new(file);
    let output: Box<dyn Write> = match args.output {
        Some(path) => Box::new(
            File::options()
                .write(true)
                .create(true)
                .truncate(true)
                .open(path)
                .map_err(|e| format!("cannot open file: {e}"))?,
        ),
        None => Box::new(io::stdout()),
    };

    let mut asm = Asm::new(lexer, output);

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
                        self.eol()?;
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
                    self.eat(); // TODO: should go through code and only eat after
                                // we check for possible errors to improve the errors
                                // here we eat so the next error will report a bad location

                    // being defined to a macro?
                    if (self.peek()? == Tok::IDENT) && self.str_like("MAC") {
                        if label.string.starts_with(".") {
                            return Err(self.err("macro names must be global"));
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
                }
                // if this isn't a mnemonic or directive, then its an error
                if mne.is_none() && dir.is_none() {
                    return Err(self.err("unrecognized instruction"));
                }
                // is this a directive
                if let Some((dir, allow_dat)) = dir {
                    if self.dat_mode && !allow_dat {
                        return Err(self.err("directive not allowed in dat mode"));
                    }
                    self.eat();
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
        expr.ok_or_else(|| self.err("expression cannot be resolved"))
    }

    fn const_24(&self, expr: Option<i32>) -> io::Result<u32> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > 0x007FFFFFu32 {
            return Err(self.err("expression too large to fit in 3 bytes"));
        }
        Ok(expr as u32)
    }

    fn const_16(&self, expr: Option<i32>) -> io::Result<u16> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u16::MAX as u32) {
            return Err(self.err("expression too large to fit in 2 bytes"));
        }
        Ok(expr as u16)
    }

    fn const_8(&self, expr: Option<i32>) -> io::Result<u8> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u8::MAX as u32) {
            return Err(self.err("expression too large to fit in 1 byte"));
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
                    self.eat();
                    if !seen_val {
                        self.values.push(self.pc() as i32);
                        seen_val = true;
                        continue;
                    }
                    self.expr_push_apply(Op::Binary(Tok::STAR));
                    seen_val = false;
                    continue;
                }
                // these are optionally unary
                tok @ (Tok::PLUS | Tok::MINUS | Tok::CARET | Tok::LT | Tok::GT) => {
                    self.eat();
                    if seen_val {
                        self.expr_push_apply(Op::Binary(tok));
                    } else {
                        self.expr_push_apply(Op::Unary(tok));
                    }
                    continue;
                }
                // always unary
                tok @ (Tok::BANG | Tok::TILDE) => {
                    self.eat();
                    if !seen_val {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Unary(tok));
                    seen_val = false;
                    continue;
                }
                #[rustfmt::skip]
                tok @ (Tok::PIPE | Tok::AND | Tok::OR | Tok::SOLIDUS | Tok::MODULUS | Tok::ASL
                      | Tok::ASR | Tok::LSR | Tok::LTE | Tok::GTE | Tok::EQ | Tok::NEQ) => {
                    self.eat();
                    if !seen_val {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Binary(tok));
                    seen_val = false;
                    continue;
                }
                Tok::NUM => {
                    self.eat();
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(self.tok().num());
                    seen_val = true;
                    continue;
                }
                Tok::LPAREN => {
                    self.eat();
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    paren_depth += 1;
                    self.operators.push(Op::Unary(Tok::LPAREN));
                    seen_val = false;
                    continue;
                }
                Tok::RPAREN => {
                    // this rparen is probably part of the indirect address
                    if self.operators.is_empty() && (paren_depth == 0) {
                        break;
                    }
                    self.eat();
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
                        self.eat();
                        if seen_val {
                            return Err(self.err("expected operator"));
                        }
                        self.values.push(sym.1);
                        seen_val = true;
                        continue;
                    }
                    seen_unknown_label = true;
                    self.eat();
                    if seen_val {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(1);
                    seen_val = true;
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
        self.find_opcode(addrs, addr)
            .ok_or_else(|| self.err("illegal address mode"))
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
                self.eat();
                let op = self.check_opcode(mne.1, Addr::IMP)?;
                if self.emit {
                    self.write(&[op])?;
                }
                self.add_pc(1)
            }
            Tok::HASH => {
                self.eat();
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
                        self.eat();
                        self.expect(Tok::X)?;
                        self.check_opcode(mne.1, Addr::IAX)?
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
                        self.eat();
                        self.expect(Tok::COMMA)?;
                        self.expect(Tok::Y)?;
                        self.check_opcode(mne.1, Addr::ISY)?
                    } else {
                        self.expect(Tok::COMMA)?;
                        self.expect(Tok::X)?;
                        self.check_opcode(mne.1, Addr::IDX)?
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
                    self.eat();
                    self.expect(Tok::Y)?;
                    self.check_opcode(mne.1, Addr::IDY)?
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
                    self.expect(Tok::RBRACK)?;
                    if self.emit {
                        self.write(&self.check_opcode(mne.1, Addr::IAL)?.to_le_bytes())?;
                        self.write(&self.const_16(expr)?.to_le_bytes())?;
                    }
                    return self.add_pc(3);
                }
                self.expect(Tok::RBRACK)?;
                // IDL or ILY
                let op = if self.peek()? == Tok::COMMA {
                    self.eat();
                    self.expect(Tok::Y)?;
                    self.check_opcode(mne.1, Addr::ILY)?
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
                let width = match self.peek()? {
                    Tok::PIPE => Width::ABS,
                    Tok::ASP => Width::ABL,
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
                                if self.emit {
                                    self.write(&self.check_opcode(mne.1, Addr::SR)?.to_le_bytes())?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(2)
                            }
                            Tok::X => {
                                self.eat();
                                if self.emit {
                                    self.write(
                                        &self.check_opcode(mne.1, Addr::DPX)?.to_le_bytes(),
                                    )?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(2)
                            }
                            Tok::Y => {
                                self.eat();
                                if self.emit {
                                    self.write(
                                        &self.check_opcode(mne.1, Addr::DPY)?.to_le_bytes(),
                                    )?;
                                    self.write(&self.const_8(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(2)
                            }
                            _ => Err(self.err("illegal address mode")),
                        }
                    }
                    // DP
                    (Width::DP, _) => {
                        self.eat();
                        if self.emit {
                            self.write(&self.check_opcode(mne.1, Addr::DP)?.to_le_bytes())?;
                            self.write(&self.const_8(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(2)
                    }
                    // ABX or ABY
                    (Width::ABS, Tok::COMMA) => {
                        self.eat();
                        match self.peek()? {
                            Tok::X => {
                                self.eat();
                                if self.emit {
                                    self.write(
                                        &self.check_opcode(mne.1, Addr::ABX)?.to_le_bytes(),
                                    )?;
                                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(3)
                            }
                            Tok::Y => {
                                self.eat();
                                if self.emit {
                                    self.write(
                                        &self.check_opcode(mne.1, Addr::ABY)?.to_le_bytes(),
                                    )?;
                                    self.write(&self.const_16(expr)?.to_le_bytes())?;
                                }
                                self.add_pc(3)
                            }
                            _ => Err(self.err("illegal address mode")),
                        }
                    }
                    // ABS
                    (Width::ABS, _) => {
                        self.eat();
                        if self.emit {
                            self.write(&self.check_opcode(mne.1, Addr::ABS)?.to_le_bytes())?;
                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(3)
                    }
                    // ALX
                    (Width::ABL, Tok::X) => {
                        self.eat();
                        if self.emit {
                            self.write(&self.check_opcode(mne.1, Addr::ALX)?.to_le_bytes())?;
                            self.write(&self.const_16(expr)?.to_le_bytes())?;
                        }
                        self.add_pc(3)
                    }
                    // ALX
                    (Width::ABL, _) => {
                        self.eat();
                        if self.emit {
                            self.write(&self.check_opcode(mne.1, Addr::ABL)?.to_le_bytes())?;
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
                self.dat_mode = true;
            }
            Dir::PRG => {
                self.dat_mode = false;
            }
            Dir::PAD => {
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
                let expr = self.expr()?;
                let adj = self.pc() % self.const_24(expr)?;
                if self.emit {
                    for _ in 0..adj {
                        self.write(&[0])?;
                    }
                }
                self.add_pc(adj)?;
            }
            Dir::INS => {
                if self.peek()? != Tok::STR {
                    return Err(self.err("expected file name"));
                }
                let file = File::open(self.str())?;
                self.eat();
                let lexer = Lexer::new(file);
                self.toks.push(Box::new(lexer));
            }
            Dir::IFF | Dir::IFD | Dir::IFN => {
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
                self.if_level -= 1;
            }
            Dir::IBT => {
                self.index_16 = false;
            }
            Dir::IWD => {
                self.index_16 = true;
            }
            Dir::ABT => {
                self.accum_16 = false;
            }
            Dir::AWD => {
                self.accum_16 = true;
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

    const JML: Self = Self("JML");
    const JMP: Self = Self("JMP");
    const JSR: Self = Self("JSR");

    const LDA: Self = Self("LDA");
    const LDX: Self = Self("LDX");
    const LDY: Self = Self("LDY");

    const NOP: Self = Self("NOP");

    const ORA: Self = Self("ORA");

    const REP: Self = Self("REP");

    const SBC: Self = Self("SBC");

    const SEP: Self = Self("SEP");

    const WDC: Self = Self("WDC");
}

const ____: u8 = 0x42; // $42 (WDC) is reserved so we special-case it as a blank

#[rustfmt::skip]
const MNEMONICS: &[(Mne, &[u8; 23])] = &[
    //           imp   imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   iab   iax   ial   rel   rll   bm
    (Mne::ADC, &[____, 0x69, 0x63, 0x65, 0x75, ____, 0x72, 0x61, 0x71, 0x67, 0x77, 0x73, 0x6D, 0x7D, 0x79, 0x6F, 0x7F, ____, ____, ____, ____, ____, ____]),

    (Mne::BRK, &[____, 0x00, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),

    (Mne::NOP, &[0xEA, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),

    (Mne::WDC, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
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
    const INS: Self = Self("INS");
    const IFF: Self = Self("IFF");
    const IFD: Self = Self("IFD");
    const IFN: Self = Self("IFN");
    const END: Self = Self("END");
    const IBT: Self = Self("IBT");
    const IWD: Self = Self("IWD");
    const ABT: Self = Self("ABT");
    const AWD: Self = Self("AWD");
}

const DIRECTIVES: &[(Dir, bool)] = &[
    (Dir::BYT, false),
    (Dir::WRD, false),
    (Dir::DAT, false),
    (Dir::PRG, true),
    (Dir::PAD, true),
    (Dir::ADJ, true),
    (Dir::INS, true),
    (Dir::IFF, true),
    (Dir::IFD, true),
    (Dir::IFN, true),
    (Dir::END, true),
    (Dir::IBT, true),
    (Dir::IWD, true),
    (Dir::ABT, true),
    (Dir::AWD, true),
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
            Some(b'?') => {
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
                if index > self.args.len() {
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
