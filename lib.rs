#![crate_name = "macro_parser"]
#![crate_type="dylib"]
#![feature(globs, plugin_registrar, macro_rules, quote, managed_boxes)]
#![experimental]

extern crate syntax;
extern crate rustc;
extern crate debug;

use syntax::ast::{Name, TokenTree, Item, MetaItem, CrateConfig};
use syntax::codemap::Span;
use syntax::ext::base::*;
use syntax::parse::token;

use syntax::ast;
use syntax::ext::base;
use syntax::parse;
use syntax::parse::{parser, ParseSess};
use syntax::parse::parser::Parser;
use syntax::parse::token::{Token, Nonterminal, };
use syntax::parse::token::InternedString;
use syntax::parse::attr::ParserAttr;
use syntax::parse::lexer::TtReader;

use syntax::ast::{MatchTok, MatchSeq, MatchNonterminal};

use rustc::plugin::Registry;

use std::any::{Any, AnyRefExt};
use std::mem;
use std::gc::GC;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("matches", matches);
}

fn matches(cx: &mut ExtCtxt, sp: Span, tts: &[TokenTree])
                   -> Box<MacResult> {
    let mut p = parse::new_parser_from_tts(cx.parse_sess(),
                                           cx.cfg(),
                                           tts.iter()
                                              .map(|x| (*x).clone())
                                              .collect());
    let mtch = p.parse_matchers();
    let prog = Program::new(mtch);
    // println!("{}", prog.insts);
    if run(&prog, &mut p, 0, prog.insts.len()) {
        MacExpr::new(quote_expr!(cx, true))
    } else {
        MacExpr::new(quote_expr!(cx, false))
    }
}

type InstIdx = uint;

#[deriving(Show, Clone)]
pub enum Inst {
    // When a Match instruction is executed, the current thread is successful.
    Match,

    OneTerminal(Token),

    // Matches a nonterminal.
    OneNonterminal(ast::Ident, ast::Ident, uint),

    // Saves the current position in the input string to the Nth save slot.
    Save(uint),

    // Jumps to the instruction at the index given.
    Jump(InstIdx),

    // Jumps to the instruction at the first index given. If that leads to
    // a failing state, then the instruction at the second index given is
    // tried.
    Split(InstIdx, InstIdx),
}

/// Program represents a compiled regular expression. Once an expression is
/// compiled, its representation is immutable and will never change.
///
/// All of the data in a compiled expression is wrapped in "MaybeStatic" or
/// "MaybeOwned" types so that a `Program` can be represented as static data.
/// (This makes it convenient and efficient for use with the `regex!` macro.)
#[deriving(Clone)]
pub struct Program {
    /// A sequence of instructions.
    pub insts: Vec<Inst>,
}

impl Program {
    /// Compiles a Regex given its AST.
    pub fn new(ast: Vec<ast::Matcher>) -> Program {
        let mut c = Compiler {
            insts: Vec::with_capacity(100),
            names: Vec::with_capacity(10),
        };

        c.insts.push(Save(0));
        for m in ast.move_iter() {
            c.compile(m);
        }
        c.insts.push(Save(1));
        c.insts.push(Match);

        let Compiler { insts, names } = c;
        let prog = Program {
            insts: insts,
        };
        prog
    }
}

struct Compiler<'r> {
    insts: Vec<Inst>,
    names: Vec<Option<String>>,
}

// The compiler implemented here is extremely simple. Most of the complexity
// in this crate is in the parser or the VM.
// The only tricky thing here is patching jump/split instructions to point to
// the right instruction.
impl<'r> Compiler<'r> {
    fn compile(&mut self, ast: ast::Matcher) {
        match ast.node {
            MatchTok(tok) => {
                self.push(OneTerminal(tok))
            }
            MatchSeq(seq, sep, true, lo, hi) => {
                let j1 = self.insts.len();
                let split = self.empty_split();
                let j2 = self.insts.len();
                for mtch in seq.move_iter() {
                    self.compile(mtch);
                }
                let jmp = self.empty_jump();
                let j3 = self.insts.len();

                self.set_jump(jmp, j1);
                self.set_split(split, j2, j3);
            }
            MatchSeq(seq, sep, false, lo, hi) => {
                let j1 = self.insts.len();
                for mtch in seq.move_iter() {
                    self.compile(mtch);
                }
                let split = self.empty_split();
                let j2 = self.insts.len();

                self.set_split(split, j1, j2);
            }
            MatchNonterminal(name, ty, pos) => {
                self.push(OneNonterminal(name, ty, pos));
            }
        }
    }

    /// Appends the given instruction to the program.
    #[inline]
    fn push(&mut self, x: Inst) {
        self.insts.push(x)
    }

    /// Appends an *empty* `Split` instruction to the program and returns
    /// the index of that instruction. (The index can then be used to "patch"
    /// the actual locations of the split in later.)
    #[inline]
    fn empty_split(&mut self) -> InstIdx {
        self.insts.push(Split(0, 0));
        self.insts.len() - 1
    }

    /// Sets the left and right locations of a `Split` instruction at index
    /// `i` to `pc1` and `pc2`, respectively.
    /// If the instruction at index `i` isn't a `Split` instruction, then
    /// `fail!` is called.
    #[inline]
    fn set_split(&mut self, i: InstIdx, pc1: InstIdx, pc2: InstIdx) {
        let split = self.insts.get_mut(i);
        match *split {
            Split(_, _) => *split = Split(pc1, pc2),
            _ => fail!("BUG: Invalid split index."),
        }
    }

    /// Appends an *empty* `Jump` instruction to the program and returns the
    /// index of that instruction.
    #[inline]
    fn empty_jump(&mut self) -> InstIdx {
        self.insts.push(Jump(0));
        self.insts.len() - 1
    }

    /// Sets the location of a `Jump` instruction at index `i` to `pc`.
    /// If the instruction at index `i` isn't a `Jump` instruction, then
    /// `fail!` is called.
    #[inline]
    fn set_jump(&mut self, i: InstIdx, pc: InstIdx) {
        let jmp = self.insts.get_mut(i);
        match *jmp {
            Jump(_) => *jmp = Jump(pc),
            _ => fail!("BUG: Invalid jump index."),
        }
    }
}

pub fn run<'r, 't>(prog: &'r Program, input: &'t mut Parser<'t, TtReader<'t>>,
                   start: uint, end: uint) -> bool {
    Nfa {
        prog: prog,
        start: start,
        end: end,
        ic: 0,
        parser: input,
    }.run()
}

struct Nfa<'r, 't> {
    prog: &'r Program,
    start: uint,
    end: uint,
    ic: uint,
    parser: &'t mut Parser<'t, TtReader<'t>>,
}

impl<'r, 't> Nfa<'r, 't> {
    fn run(&mut self) -> bool {
        let mut matched = false;
        let ninsts = self.prog.insts.len();
        let mut clist = &mut Threads::new(ninsts, 0);
        let mut nlist = &mut Threads::new(ninsts, 0);

        let mut next_ic = 1;
        while self.ic <= self.end {
            if clist.size == 0 {
                // We have a match and we're done exploring alternatives.
                // Time to quit.
                if matched {
                    break
                }
            }

            // This simulates a preceding '.*?' for every regex by adding
            // a state starting at the current position in the input for the
            // beginning of the program only if we don't already have a match.
            if clist.size == 0 || (!matched) {
                self.add(clist, 0)
            }

            // Now we try to read the next character.
            // As a result, the 'step' method will look at the previous
            // character.
            self.ic = next_ic;
            next_ic = self.ic + 1;

            for i in range(0, clist.size) {
                let (pc, popt) = clist.pc(i); // grab pc of i-th current state
                if self.step(nlist, pc, popt) {
                    matched = true;
                }
            }
            self.parser.bump();
            mem::swap(&mut clist, &mut nlist);
            nlist.empty();
        }
        matched
    }

    fn step(&mut self, nlist: &mut Threads<'t>,
            pc: uint, parser: &mut Option<Parser<'t, TtReader<'t>>>)
           -> bool {
        match *self.prog.insts.get(pc) {
            Match => {
                return true
            }
            OneTerminal(ref tok) => {
                let is_match = {
                    let parser = match parser {
                        &Some(ref mut p) => p,
                        &None => &mut *self.parser
                    };
                    parser.token == *tok
                };
                if is_match {
                    self.add(nlist, pc+1);
                }
            }
            OneNonterminal(_, ty, _) => {
                let (mut p, ttv) = {
                    let parser = match parser {
                        &Some(ref mut p) => p,
                        &None => &mut *self.parser
                    };

                    let ttv = parser.parse_all_token_trees();
                    let mut p = parse::new_parser_from_tts(parser.sess,
                                                           parser.cfg.clone(),
                                                           ttv.clone());
                    if parse_nt(&mut p, token::get_ident(ty).get()).is_some() {
                        (p, ttv)
                    } else {
                        mem::replace(parser, parse::new_parser_from_tts(p.sess,
                                                                        p.cfg.clone(),
                                                                        ttv));
                        return false;
                    }
                };

                let ttv2 = p.parse_all_token_trees();
                let mut p = parse::new_parser_from_tts(p.sess,
                                                       p.cfg.clone(),
                                                       ttv.clone());

                self.add_with_parser(nlist, pc+1, p.sess, p.cfg.clone(), ttv2.as_slice());
                let parser = match parser {
                    &Some(ref mut p) => p,
                    &None => &mut *self.parser
                };
                mem::replace(parser, p);
            }
            _ => {}
        }
        false
    }

    fn add(&self, nlist: &mut Threads, pc: uint) {
        if nlist.contains(pc) {
            return
        }
        // We have to add states to the threads list even if their empty.
        // TL;DR - It prevents cycles.
        // If we didn't care about cycles, we'd *only* add threads that
        // correspond to non-jumping instructions (OneChar, Any, Match, etc.).
        // But, it's possible for valid regexs (like '(a*)*') to result in
        // a cycle in the instruction list. e.g., We'll keep chasing the Split
        // instructions forever.
        // So we add these instructions to our thread queue, but in the main
        // VM loop, we look for them but simply ignore them.
        // Adding them to the queue prevents them from being revisited so we
        // can avoid cycles (and the inevitable stack overflow).
        //
        // We make a minor optimization by indicating that the state is "empty"
        // so that its capture groups are not filled in.
        match *self.prog.insts.get(pc) {
            Save(slot) => {
                self.add(nlist, pc + 1);
            }
            Jump(to) => {
                nlist.add(pc, true);
                self.add(nlist, to)
            }
            Split(x, y) => {
                nlist.add(pc, true);
                self.add(nlist, x);
                self.add(nlist, y);
            }
            _ => {
                nlist.add(pc, false);
            }
        }
    }

    fn add_with_parser<'a>(&self, nlist: &mut Threads<'a>, pc: uint, sess: &'a ParseSess, cfg: CrateConfig, tt: &[TokenTree]) {
        if nlist.contains(pc) {
            return
        }
        match *self.prog.insts.get(pc) {
            Save(slot) => {
                nlist.add_with_parser(pc, sess, cfg.clone(), tt);
                self.add_with_parser(nlist, pc + 1, sess, cfg, tt);
            }
            Jump(to) => {
                nlist.add_with_parser(pc, sess, cfg.clone(), tt);
                self.add_with_parser(nlist, to, sess, cfg, tt)
            }
            Split(x, y) => {
                nlist.add_with_parser(pc, sess, cfg.clone(), tt);
                self.add_with_parser(nlist, x, sess, cfg.clone(), tt);
                self.add_with_parser(nlist, y, sess, cfg, tt);
            }
            _ => {
                nlist.add_with_parser(pc, sess, cfg, tt);
            }
        }
    }
}

fn parse_nt(parser: &mut Parser<TtReader>, name: &str) -> Option<Nonterminal> {
    match name {
        "item" => match parser.parse_item(Vec::new()) {
          Some(i) => Some(token::NtItem(i)),
          None => None
        },
        "block" => Some(token::NtBlock(parser.parse_block())),
        "stmt" => Some(token::NtStmt(parser.parse_stmt(Vec::new()))),
        "pat" => Some(token::NtPat(parser.parse_pat())),
        "expr" => {
            if parser.token != token::EOF {
                Some(token::NtExpr(parser.parse_expr()))
            } else {
                None
            }
        }
        "ty" => Some(token::NtTy(parser.parse_ty(false /* no need to disambiguate*/))),
        // this could be handled like a token, since it is one
        "ident" => match parser.token {
          token::IDENT(sn,b) => { parser.bump(); Some(token::NtIdent(box sn,b)) }
          _ => {
              // let token_str = token::to_str(&p.token);
              // p.fatal((format!("expected ident, found {}",
                               // token_str.as_slice())).as_slice())
                None
          }
        },
        "path" => {
          Some(token::NtPath(box parser.parse_path(parser::LifetimeAndTypesWithoutColons).path))
        }
        "meta" => Some(token::NtMeta(parser.parse_meta_item())),
        "tt" => {
          parser.quote_depth += 1u; //but in theory, non-quoted tts might be useful
          let res = token::NtTT(box(GC) parser.parse_token_tree());
          parser.quote_depth -= 1u;
          Some(res)
        }
        "matchers" => Some(token::NtMatchers(parser.parse_matchers())),
        // _ => p.fatal("unsupported builtin nonterminal parser: ".to_owned() + name)
        _ => None
    }
}

struct Thread<'t> {
    pc: uint,
    // groups: Vec<Option<uint>>,
    parser: Option<Parser<'t, TtReader<'t>>>
}

struct Threads<'t> {
    queue: Vec<Thread<'t>>,
    sparse: Vec<uint>,
    size: uint,
}

impl<'t> Threads<'t> {
    // This is using a wicked neat trick to provide constant time lookup
    // for threads in the queue using a sparse set. A queue of threads is
    // allocated once with maximal size when the VM initializes and is reused
    // throughout execution. That is, there should be zero allocation during
    // the execution of a VM.
    //
    // See http://research.swtch.com/sparse for the deets.
    fn new<'a>(num_insts: uint, ncaps: uint) -> Threads<'a> {
        Threads {
            queue: Vec::from_fn(num_insts, |_| {
                Thread {
                    pc: 0,
                    parser: None
                }
            }),
            sparse: Vec::from_elem(num_insts, 0u),
            size: 0,
        }
    }

    fn add(&mut self, pc: uint, _empty: bool) {
        let t = self.queue.get_mut(self.size);
        t.pc = pc;
        *self.sparse.get_mut(pc) = self.size;
        self.size += 1;
    }

    fn add_with_parser(&mut self, pc: uint, sess: &'t ParseSess, cfg: CrateConfig, tts: &[TokenTree]) {
        let t = self.queue.get_mut(self.size);
        t.pc = pc;
        let p = parse::new_parser_from_tts(sess,
                                           cfg,
                                           tts.iter()
                                              .map(|x| (*x).clone())
                                              .collect());
        t.parser = Some(p);
        *self.sparse.get_mut(pc) = self.size;
        self.size += 1;
    }

    #[inline]
    fn contains(&self, pc: uint) -> bool {
        let s = *self.sparse.get(pc);
        s < self.size && self.queue.get(s).pc == pc
    }

    #[inline]
    fn empty(&mut self) {
        self.size = 0;
    }

    #[inline]
    fn pc<'a>(&'a mut self, i: uint) -> (uint, &'a mut Option<Parser<'t, TtReader<'t>>>) {
        let &Thread { pc, parser: ref mut popt } = self.queue.get_mut(i);
        (pc, popt)
    }
}
