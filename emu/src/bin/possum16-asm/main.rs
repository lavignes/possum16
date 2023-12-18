use std::{
    error::Error,
    fs::File,
    io::{self, ErrorKind, Read, Seek, Write},
    marker::PhantomData,
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

    Ok(())
}

struct Asm<'a> {
    toks: Vec<Box<dyn TokStream>>,
    str_int: StrInterner<'a>,
    output: Box<dyn Write>,
    pc: u16,
    bss: u16,
    bss_mode: bool,
    syms: Vec<(Label<'a>, i32)>,
    scope: Option<&'a str>,
    emit: bool,

    values: Vec<i32>,
    operators: Vec<Op>,
}

impl<'a> Asm<'a> {
    fn new<R: Read + Seek + 'static>(lexer: Lexer<R>, output: Box<dyn Write>) -> Self {
        Self {
            toks: vec![Box::new(lexer)],
            str_int: StrInterner::new(),
            output,
            pc: 0,
            bss: 0,
            bss_mode: false,
            syms: Vec::new(),
            scope: None,
            emit: false,

            values: Vec::new(),
            operators: Vec::new(),
        }
    }

    fn rewind(&mut self) -> io::Result<()> {
        self.toks.last_mut().unwrap().rewind()?;
        self.pc = 0;
        self.bss = 0;
        self.bss_mode = false;
        self.scope = None;
        self.emit = true;

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
                    return Err(self.err("expected EQU"));
                }
                self.eat();
                let expr = self.expr()?;
                self.set_pc(self.const_word(expr)?);
                self.eol()?;
                continue;
            }
            if self.peek()? == Tok::IDENT {
                // is this a mnemonic
                let mne = MNEMONICS.iter().find(|mne| mne.0 .0 == self.tok().str());
                let dir = DIRECTIVES.iter().find(|dir| dir.0 .0 == self.tok().str());
                if mne.is_none() && dir.is_none() && !self.str_like("EQU") && !self.str_like("MAC")
                {
                    let string = self.str_intern();
                    let label = if !self.str().starts_with(".") {
                        self.scope.replace(string);
                        Label {
                            scope: None,
                            string,
                        }
                    } else {
                        Label {
                            scope: self.scope,
                            string,
                        }
                    };
                    self.eat();
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
                    self.syms[index].1 = self.pc() as u32 as i32;
                }
                // if this isn't a mnemonic or directive, then its an error
                if mne.is_none() && dir.is_none() {
                    return Err(self.err("unrecognized instruction"));
                }
                if let Some((dir, allow_bss)) = dir {
                    if self.bss_mode && !allow_bss {
                        return Err(self.err("directive not allowed in BSS mode"));
                    }
                    // TODO: execute directive
                    continue;
                }
                let mne = mne.unwrap();
                // TODO: execute mnemonic
            }
            self.eol()?;
        }
        Ok(())
    }

    fn pc(&self) -> u16 {
        if self.bss_mode {
            self.bss
        } else {
            self.pc
        }
    }

    fn set_pc(&mut self, val: u16) {
        if self.bss_mode {
            self.bss = val;
        } else {
            self.pc = val;
        }
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

    fn const_word(&self, expr: Option<i32>) -> io::Result<u16> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u16::MAX as u32) {
            return Err(self.err("expression too large to fit in word"));
        }
        Ok(expr as u16)
    }

    fn const_byte(&self, expr: Option<i32>) -> io::Result<u8> {
        let expr = self.const_expr(expr)?;
        if (expr as u32) > (u8::MAX as u32) {
            return Err(self.err("expression too large to fit in byte"));
        }
        Ok(expr as u8)
    }

    fn const_short_branch(&self, expr: Option<i32>) -> io::Result<u8> {
        let expr = self.const_expr(expr)?;
        let branch = expr - (self.pc() as u32 as i32);
        if (branch < (i8::MIN as i32)) || (branch > (i8::MAX as i32)) {
            return Err(self.err("branch distance too far"));
        }
        Ok(branch as i8 as u8)
    }

    fn const_long_branch(&self, expr: Option<i32>) -> io::Result<u16> {
        let expr = self.const_expr(expr)?;
        let branch = expr - (self.pc() as u32 as i32);
        if (branch < (i16::MIN as i32)) || (branch > (i16::MAX as i32)) {
            return Err(self.err("branch distance too far"));
        }
        Ok(branch as i16 as u16)
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
        let mut seen_value = false;
        let mut paren_depth = 0;
        let mut seen_unknown_label = false;
        loop {
            match self.peek()? {
                // star is multiply or the PC
                Tok::STAR => {
                    self.eat();
                    if !seen_value {
                        self.values.push(self.pc() as u32 as i32);
                        seen_value = true;
                        continue;
                    }
                    self.expr_push_apply(Op::Binary(Tok::STAR));
                    seen_value = false;
                    continue;
                }
                // these are optionally unary
                tok @ (Tok::PLUS | Tok::MINUS | Tok::LT | Tok::GT) => {
                    self.eat();
                    if seen_value {
                        self.expr_push_apply(Op::Binary(tok));
                    } else {
                        self.expr_push_apply(Op::Unary(tok));
                    }
                    continue;
                }
                // always unary
                tok @ (Tok::BANG | Tok::TILDE) => {
                    self.eat();
                    if !seen_value {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Unary(tok));
                    seen_value = false;
                    continue;
                }
                tok @ (Tok::CARET
                | Tok::PIPE
                | Tok::AND
                | Tok::OR
                | Tok::SOLIDUS
                | Tok::MODULUS
                | Tok::ASL
                | Tok::ASR
                | Tok::LSR
                | Tok::LTE
                | Tok::GTE
                | Tok::EQ
                | Tok::NEQ) => {
                    self.eat();
                    if !seen_value {
                        return Err(self.err("expected value"));
                    }
                    self.expr_push_apply(Op::Binary(tok));
                    seen_value = false;
                    continue;
                }
                Tok::NUM => {
                    self.eat();
                    if seen_value {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(self.tok().num());
                    seen_value = true;
                    continue;
                }
                Tok::LPAREN => {
                    self.eat();
                    if seen_value {
                        return Err(self.err("expected operator"));
                    }
                    paren_depth += 1;
                    self.operators.push(Op::Unary(Tok::LPAREN));
                    seen_value = false;
                    continue;
                }
                Tok::RPAREN => {
                    // this pclose is probably part of the indirect address
                    if self.operators.is_empty() && (paren_depth == 0) {
                        break;
                    }
                    self.eat();
                    paren_depth -= 1;
                    if !seen_value {
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
                        Label {
                            scope: None,
                            string,
                        }
                    } else {
                        Label {
                            scope: self.scope,
                            string,
                        }
                    };
                    if let Some(sym) = self.syms.iter().find(|sym| &sym.0 == &label).copied() {
                        self.eat();
                        if seen_value {
                            return Err(self.err("expected operator"));
                        }
                        self.values.push(sym.1);
                        seen_value = true;
                        continue;
                    }
                    seen_unknown_label = true;
                    self.eat();
                    if seen_value {
                        return Err(self.err("expected operator"));
                    }
                    self.values.push(1);
                    seen_value = true;
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
}

struct Addr(u8); // really u24

#[rustfmt::skip]
impl Addr {
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
    const ABS: Self = Self(12); // $0000
    const ABX: Self = Self(13); // $0000,X
    const ABY: Self = Self(14); // $0000,Y
    const ABL: Self = Self(15); // $000000
    const ALX: Self = Self(16); // $000000,X
    const IND: Self = Self(17); // ($0000)
    const IAX: Self = Self(18); // ($0000,X)
    const IAL: Self = Self(19); // [$000000]
    const REL: Self = Self(20); // ±$00
    const RLL: Self = Self(21); // ±$0000
    const BM: Self = Self(22);  // $00,$00
}

struct Mne(&'static str); // I really only newtype these to create namespaces

impl Mne {
    const ADC: Self = Self("ADC");
    const WDC: Self = Self("WDC");
}

const ____: u8 = 0x42; // $42 (WDC) is reserved so we special-case it as a blank

#[rustfmt::skip]
const MNEMONICS: &[(Mne, &[u8; 22])] = &[
    //           imm   sr    dp    dpx   dpy   idp   idx   idy   idl   ily   isy   abs   abx   aby   abl   alx   ind   iax   ial   rel   rll   bm
    (Mne::WDC, &[____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____, ____]),
    (Mne::ADC, &[0x69, 0x63, 0x65, 0x75, ____, 0x72, 0x61, 0x71, 0x67, 0x77, 0x73, 0x6D, 0x7D, 0x79, 0x6F, 0x7F, ____, ____, ____, ____, ____, ____]),
];

struct Dir(&'static str);

impl Dir {}

const DIRECTIVES: &[(Dir, bool)] = &[];

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
    const BANG: Self = Self(b'!');
    const TILDE: Self = Self(b'~');

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

    fn column(&self) -> usize;
}

// TODO: for macro storage
struct TokInterner<'a> {
    marker: PhantomData<&'a ()>,
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
                // SAFETY: the assumption is that
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
                string.len().next_power_of_two().max(256),
            ));
            self.storages.last_mut().unwrap()
        };
        let index = storage.len();
        storage.push_str(string);
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

struct Lexer<R> {
    reader: PeekReader<R>,
    string: String,
    number: i32,
    stash: Option<Tok>,
    line: usize,
    column: usize,
}

impl<R: Read + Seek> Lexer<R> {
    fn new(reader: R) -> Self {
        Self {
            reader: PeekReader::new(reader),
            string: String::new(),
            number: 0,
            stash: None,
            line: 1,
            column: 1,
        }
    }
}

impl<R: Read + Seek> TokStream for Lexer<R> {
    fn err(&self, msg: &str) -> io::Error {
        io::Error::new(
            ErrorKind::InvalidData,
            format!("{}:{}: {msg}", self.line, self.column),
        )
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
                        .cloned()
                    {
                        self.reader.eat();
                        self.stash = Some(tok);
                        return Ok(tok);
                    }
                }
                self.stash = Some(Tok(c.to_ascii_uppercase()));
                Ok(Tok(c.to_ascii_uppercase()))
            }
        }
    }

    fn eat(&mut self) {
        self.string.clear();
        self.column += 1;
        if let Some(Tok::NEWLINE) = self.stash.take() {
            self.column = 1;
            self.line += 1;
        }
    }

    fn rewind(&mut self) -> io::Result<()> {
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

    fn column(&self) -> usize {
        self.column
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
