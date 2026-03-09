/// Pattern compiler - mirrors lpcode.c
/// Compiles TTree (pattern AST) into VM instructions.

use crate::types::*;
use crate::charset::*;
use crate::tree::*;

/// Sentinel: "no instruction"
const NOINST: i32 = -1;

/// Full 256-bit charset (all bits set)
const FULLSET: Charset = [0xFF; CHARSETSIZE];

// ============================================================
// Compiler state
// ============================================================

pub struct CompileState<'a> {
    pub p: &'a mut Pattern,
    pub ncode: usize,
}

impl<'a> CompileState<'a> {
    fn getinstr(&self, i: usize) -> &Instruction {
        &self.p.code.as_ref().unwrap()[i]
    }

    fn getinstr_mut(&mut self, i: usize) -> &mut Instruction {
        &mut self.p.code.as_mut().unwrap()[i]
    }

    fn gethere(&self) -> usize {
        self.ncode
    }

    /// Ensure code vec has room for `n` more instructions, return current ncode.
    fn nextinstruction(&mut self, n: usize) -> usize {
        let code = self.p.code.as_mut().unwrap();
        while code.len() < self.ncode + n {
            code.push(Instruction::new(Opcode::IEmpty));
        }
        let idx = self.ncode;
        self.ncode += n;
        idx
    }

    fn addinstruction(&mut self, op: Opcode, aux: u8) -> usize {
        let i = self.nextinstruction(1);
        let inst = self.getinstr_mut(i);
        inst.code = op;
        inst.aux1 = aux;
        i
    }

    /// Add an instruction followed by space for an offset
    fn addoffsetinst(&mut self, op: Opcode) -> usize {
        let i = self.addinstruction(op, 0);
        self.addinstruction(Opcode::IEmpty, 0); // space for offset
        i
    }

    fn setoffset(&mut self, inst: usize, offset: i32) {
        self.getinstr_mut(inst + 1).offset = offset;
    }

    fn jumptothere(&mut self, inst: i32, target: usize) {
        if inst >= 0 {
            self.setoffset(inst as usize, target as i32 - inst as i32);
        }
    }

    fn jumptohere(&mut self, inst: i32) {
        let here = self.gethere();
        self.jumptothere(inst, here);
    }

    /// Add a capture instruction
    fn addinstcap(&mut self, op: Opcode, cap: CapKind, key: u16, aux: u8) -> usize {
        let i = self.addinstruction(op, Instruction::joinkindoff(cap, aux));
        self.getinstr_mut(i).key = key as i16;
        i
    }

    /// Add charset data after instruction `inst`
    fn addcharset(&mut self, inst: usize, info: &CharsetInfo) {
        let offset_bits = (info.offset * 8) as u8;
        let isize = instsize(info.size);
        {
            let instr = self.getinstr_mut(inst);
            instr.set_offset = offset_bits;
            instr.set_size = isize as u8;
            instr.aux1 = info.deflt;
        }
        // Fill charset buffer
        let mut buf = Vec::with_capacity(isize * INST_SIZE);
        for i in 0..isize * INST_SIZE {
            buf.push(getbytefromcharset(info, i));
        }
        self.getinstr_mut(inst).charset = Some(buf);
    }
}

/// Number of instruction slots needed to store `size` bytes of charset data.
fn instsize(size: usize) -> usize {
    // In C: (size + sizeof(Instruction) - 1) / sizeof(Instruction)
    // In our representation we store charset inline, so this is just
    // a normalized count. We keep it for offset/size bookkeeping.
    size
}

/// Size of one instruction (for layout purposes, used in charset byte count)
const INST_SIZE: usize = 1;

// ============================================================
// Code generation helpers
// ============================================================

fn codechar(compst: &mut CompileState, c: i32, tt: i32) {
    if tt >= 0 {
        let tcode = compst.getinstr(tt as usize).code;
        let taux = compst.getinstr(tt as usize).aux1;
        if tcode == Opcode::ITestChar && taux == c as u8 {
            compst.addinstruction(Opcode::IAny, 0);
            return;
        }
    }
    compst.addinstruction(Opcode::IChar, c as u8);
}

/// Check if charset info matches a TestSet instruction at position p
fn cs_equal(compst: &CompileState, p: usize, info: &CharsetInfo) -> bool {
    let inst = compst.getinstr(p);
    if inst.code != Opcode::ITestSet {
        return false;
    }
    if inst.set_offset != (info.offset * 8) as u8
        || inst.set_size != instsize(info.size) as u8
        || inst.aux1 != info.deflt
    {
        return false;
    }
    if let Some(ref cs) = inst.charset {
        for i in 0..instsize(info.size) * INST_SIZE {
            let b = if i < cs.len() { cs[i] } else { info.deflt };
            if b != getbytefromcharset(info, i) {
                return false;
            }
        }
        true
    } else {
        false
    }
}

fn codecharset(compst: &mut CompileState, tree: &[TTree], idx: usize, tt: i32) {
    let info = tree2cset(tree, idx);
    if tt >= 0 && cs_equal(compst, tt as usize, &info) {
        compst.addinstruction(Opcode::IAny, 0);
    } else {
        let i = compst.addinstruction(Opcode::ISet, 0);
        compst.addcharset(i, &info);
    }
}

fn codeutfr(compst: &mut CompileState, tree: &[TTree], idx: usize) {
    let i = compst.addoffsetinst(Opcode::IUTFR);
    let xinfo_idx = sib1(idx);
    assert!(tree[xinfo_idx].tag == TTag::TXInfo);
    let to = tree[xinfo_idx].n;
    let from = tree[idx].n;
    compst.getinstr_mut(i + 1).offset = from;
    compst.getinstr_mut(i).aux1 = (to & 0xFF) as u8;
    compst.getinstr_mut(i).key = (to >> 8) as i16;
}

/// Code a test set. Returns instruction index or NOINST.
fn codetestset(compst: &mut CompileState, cs: &Charset, e: bool) -> i32 {
    if e {
        return NOINST;
    }
    let mut info = CharsetInfo {
        cs: Vec::new(),
        offset: 0,
        size: 0,
        deflt: 0,
    };
    let op = charsettype(cs, &mut info);
    match op {
        Opcode::IFail => compst.addoffsetinst(Opcode::IJmp) as i32,
        Opcode::IAny => compst.addoffsetinst(Opcode::ITestAny) as i32,
        Opcode::IChar => {
            let i = compst.addoffsetinst(Opcode::ITestChar);
            compst.getinstr_mut(i).aux1 = info.offset as u8;
            i as i32
        }
        _ => {
            // ISet → ITestSet
            let i = compst.addoffsetinst(Opcode::ITestSet);
            compst.addcharset(i, &info);
            i as i32
        }
    }
}

/// Find final target of a chain of jumps
fn finaltarget(code: &[Instruction], mut i: usize) -> usize {
    while code[i].code == Opcode::IJmp {
        i = (i as i32 + code[i + 1].offset) as usize;
    }
    i
}

/// Final label (target of the label at instruction i)
fn finallabel(code: &[Instruction], i: usize) -> usize {
    let target = (i as i32 + code[i + 1].offset) as usize;
    finaltarget(code, target)
}

// ============================================================
// codebehind, codechoice, codeand, codecapture, coderuntime
// ============================================================

fn codebehind(compst: &mut CompileState, tree: &[TTree], idx: usize) {
    if tree[idx].n > 0 {
        compst.addinstruction(Opcode::IBehind, tree[idx].n as u8);
    }
    codegen(compst, tree, sib1(idx), false, NOINST, &FULLSET);
}

fn codechoice(
    compst: &mut CompileState,
    tree: &[TTree],
    p1: usize,
    p2: usize,
    opt: bool,
    fl: &Charset,
) {
    let emptyp2 = tree[p2].tag == TTag::TTrue;
    let mut cs1 = [0u8; CHARSETSIZE];
    let e1 = getfirst(tree, p1, &FULLSET, &mut cs1);
    if headfail(tree, p1)
        || (e1 == 0 && {
            let mut cs2 = [0u8; CHARSETSIZE];
            getfirst(tree, p2, fl, &mut cs2);
            cs_disjoint(&cs1, &cs2)
        })
    {
        // test(fail(p1)) → L1; p1; jmp L2; L1: p2; L2:
        let test = codetestset(compst, &cs1, false);
        let mut jmp = NOINST;
        codegen(compst, tree, p1, false, test, fl);
        if !emptyp2 {
            jmp = compst.addoffsetinst(Opcode::IJmp) as i32;
        }
        compst.jumptohere(test);
        codegen(compst, tree, p2, opt, NOINST, fl);
        compst.jumptohere(jmp);
    } else if opt && emptyp2 {
        // p1? == IPartialCommit; p1
        let pc = compst.addoffsetinst(Opcode::IPartialCommit);
        compst.jumptohere(pc as i32);
        codegen(compst, tree, p1, true, NOINST, &FULLSET);
    } else {
        // test(first(p1)) → L1; choice L1; <p1>; commit L2; L1: <p2>; L2:
        let test = codetestset(compst, &cs1, e1 != 0);
        let pchoice = compst.addoffsetinst(Opcode::IChoice);
        codegen(compst, tree, p1, emptyp2, test, &FULLSET);
        let pcommit = compst.addoffsetinst(Opcode::ICommit);
        compst.jumptohere(pchoice as i32);
        compst.jumptohere(test);
        codegen(compst, tree, p2, opt, NOINST, fl);
        compst.jumptohere(pcommit as i32);
    }
}

fn codeand(compst: &mut CompileState, tree: &[TTree], idx: usize, tt: i32) {
    let n = fixedlen(tree, idx);
    if n >= 0 && n <= MAXBEHIND as i32 && !hascaptures(tree, idx) {
        codegen(compst, tree, idx, false, tt, &FULLSET);
        if n > 0 {
            compst.addinstruction(Opcode::IBehind, n as u8);
        }
    } else {
        // Choice L1; p1; BackCommit L2; L1: Fail; L2:
        let pchoice = compst.addoffsetinst(Opcode::IChoice);
        codegen(compst, tree, idx, false, tt, &FULLSET);
        let pcommit = compst.addoffsetinst(Opcode::IBackCommit);
        compst.jumptohere(pchoice as i32);
        compst.addinstruction(Opcode::IFail, 0);
        compst.jumptohere(pcommit as i32);
    }
}

fn codecapture(
    compst: &mut CompileState,
    tree: &[TTree],
    idx: usize,
    tt: i32,
    fl: &Charset,
) {
    let body = sib1(idx);
    let len = fixedlen(tree, body);
    if len >= 0 && len <= MAXOFF as i32 && !hascaptures(tree, body) {
        codegen(compst, tree, body, false, tt, fl);
        compst.addinstcap(
            Opcode::IFullCapture,
            CapKind::from_u8(tree[idx].cap),
            tree[idx].key,
            len as u8,
        );
    } else {
        compst.addinstcap(
            Opcode::IOpenCapture,
            CapKind::from_u8(tree[idx].cap),
            tree[idx].key,
            0,
        );
        codegen(compst, tree, body, false, tt, fl);
        compst.addinstcap(Opcode::ICloseCapture, CapKind::Cclose, 0, 0);
    }
}

fn coderuntime(compst: &mut CompileState, tree: &[TTree], idx: usize, tt: i32) {
    compst.addinstcap(Opcode::IOpenCapture, CapKind::Cgroup, tree[idx].key, 0);
    codegen(compst, tree, sib1(idx), false, tt, &FULLSET);
    compst.addinstcap(Opcode::ICloseRunTime, CapKind::Cclose, 0, 0);
}

/// Create loop: jmp → test; test → here
fn closeloop(compst: &mut CompileState, test: i32) {
    let jmp = compst.addoffsetinst(Opcode::IJmp) as i32;
    compst.jumptohere(test);
    compst.jumptothere(jmp, test as usize);
}

// ============================================================
// coderepcharset, coderep, codenot
// ============================================================

fn coderepcharset(compst: &mut CompileState, tree: &[TTree], idx: usize) -> bool {
    match tree[idx].tag {
        TTag::TFalse => true, // fail* is a no-op
        TTag::TAny => {
            let test = compst.addoffsetinst(Opcode::ITestAny) as i32;
            compst.addinstruction(Opcode::IAny, 0);
            closeloop(compst, test);
            true
        }
        TTag::TChar => {
            let test = compst.addoffsetinst(Opcode::ITestChar) as i32;
            compst.getinstr_mut(test as usize).aux1 = tree[idx].n as u8;
            compst.addinstruction(Opcode::IAny, 0);
            closeloop(compst, test);
            true
        }
        TTag::TSet => {
            let i = compst.addinstruction(Opcode::ISpan, 0);
            let info = tree2cset(tree, idx);
            compst.addcharset(i, &info);
            true
        }
        _ => false,
    }
}

fn coderep(
    compst: &mut CompileState,
    tree: &[TTree],
    idx: usize,
    opt: bool,
    fl: &Charset,
) {
    if !coderepcharset(compst, tree, idx) {
        let mut st = [0u8; CHARSETSIZE];
        let e1 = getfirst(tree, idx, &FULLSET, &mut st);
        if headfail(tree, idx) || (e1 == 0 && cs_disjoint(&st, fl)) {
            // L1: test(fail(p1)) → L2; <p>; jmp L1; L2:
            let test = codetestset(compst, &st, false);
            codegen(compst, tree, idx, false, test, &FULLSET);
            closeloop(compst, test);
        } else {
            let test = codetestset(compst, &st, e1 != 0);
            if opt {
                let pc = compst.addoffsetinst(Opcode::IPartialCommit);
                compst.jumptohere(pc as i32);
            } else {
                let pchoice = compst.addoffsetinst(Opcode::IChoice);
                let _ = pchoice; // will be jumped to by test
                // jumptohere for pchoice happens at end
                let l2 = compst.gethere();
                codegen(compst, tree, idx, false, NOINST, &FULLSET);
                let commit = compst.addoffsetinst(Opcode::IPartialCommit);
                compst.jumptothere(commit as i32, l2);
                compst.jumptohere(pchoice as i32);
                compst.jumptohere(test);
                return;
            }
            let l2 = compst.gethere();
            codegen(compst, tree, idx, false, NOINST, &FULLSET);
            let commit = compst.addoffsetinst(Opcode::IPartialCommit);
            compst.jumptothere(commit as i32, l2);
            compst.jumptohere(test);
        }
    }
}

fn codenot(compst: &mut CompileState, tree: &[TTree], idx: usize) {
    let mut st = [0u8; CHARSETSIZE];
    let e = getfirst(tree, idx, &FULLSET, &mut st);
    let test = codetestset(compst, &st, e != 0);
    if headfail(tree, idx) {
        // test(fail(p1)) → L1; fail; L1:
        compst.addinstruction(Opcode::IFail, 0);
    } else {
        // test(fail(p)) → L1; choice L1; <p>; failtwice; L1:
        let pchoice = compst.addoffsetinst(Opcode::IChoice);
        codegen(compst, tree, idx, false, NOINST, &FULLSET);
        compst.addinstruction(Opcode::IFailTwice, 0);
        compst.jumptohere(pchoice as i32);
    }
    compst.jumptohere(test);
}

// ============================================================
// Grammar, call, sequence, main codegen, peephole, compile
// ============================================================

fn correctcalls(compst: &mut CompileState, positions: &[usize], from: usize, to: usize) {
    let code = compst.p.code.as_mut().unwrap();
    let mut i = from;
    while i < to {
        if code[i].code == Opcode::IOpenCall {
            let n = code[i].key as usize; // rule number
            let rule = positions[n];
            // check tail call: call; ret → jmp
            let tgt = (i as i32 + 2 + code[i + 1].offset) as usize;
            let ft = finaltarget(code, tgt.max(i + 2).min(code.len().saturating_sub(1)));
            if ft < code.len() && code[ft].code == Opcode::IRet {
                code[i].code = Opcode::IJmp;
            } else {
                code[i].code = Opcode::ICall;
            }
            code[i + 1].offset = rule as i32 - i as i32;
        }
        i += sizei(&code[i]);
    }
}

/// Get instruction size
pub fn sizei(inst: &Instruction) -> usize {
    match inst.code {
        Opcode::ISet | Opcode::ISpan => 1, // charset is stored inline
        Opcode::ITestSet => 2,              // inst + offset (charset inline)
        Opcode::ITestChar
        | Opcode::ITestAny
        | Opcode::IChoice
        | Opcode::IJmp
        | Opcode::ICall
        | Opcode::IOpenCall
        | Opcode::ICommit
        | Opcode::IPartialCommit
        | Opcode::IBackCommit
        | Opcode::IUTFR => 2,
        _ => 1,
    }
}

fn codegrammar(compst: &mut CompileState, tree: &[TTree], idx: usize) {
    let mut positions = Vec::new();
    let firstcall = compst.addoffsetinst(Opcode::ICall) as i32;
    let jumptoend = compst.addoffsetinst(Opcode::IJmp) as i32;
    let start = compst.gethere();
    compst.jumptohere(firstcall);

    let mut rule = sib1(idx);
    while rule < tree.len() && tree[rule].tag == TTag::TRule {
        let r = sib1(rule); // TXInfo
        assert!(tree[r].tag == TTag::TXInfo);
        positions.push(compst.gethere());
        codegen(compst, tree, sib1(r), false, NOINST, &FULLSET);
        compst.addinstruction(Opcode::IRet, 0);
        rule = sib2(tree, rule);
    }
    compst.jumptohere(jumptoend);
    let here = compst.gethere();
    correctcalls(compst, &positions, start, here);
}

fn codecall(compst: &mut CompileState, tree: &[TTree], idx: usize) {
    let c = compst.addoffsetinst(Opcode::IOpenCall);
    let rule = sib2(tree, idx);
    let xinfo = sib1(rule);
    assert!(tree[xinfo].tag == TTag::TXInfo);
    compst.getinstr_mut(c).key = tree[xinfo].n as i16; // rule number
}

fn codeseq1(
    compst: &mut CompileState,
    tree: &[TTree],
    p1: usize,
    p2: usize,
    tt: i32,
    fl: &Charset,
) -> i32 {
    if needfollow(tree, p1) {
        let mut fl1 = [0u8; CHARSETSIZE];
        getfirst(tree, p2, fl, &mut fl1);
        codegen(compst, tree, p1, false, tt, &fl1);
    } else {
        codegen(compst, tree, p1, false, tt, &FULLSET);
    }
    if fixedlen(tree, p1) != 0 {
        NOINST // invalidate test
    } else {
        tt // tt still protects sib2
    }
}

/// Main code generation dispatcher
fn codegen(
    compst: &mut CompileState,
    tree: &[TTree],
    mut idx: usize,
    mut opt: bool,
    mut tt: i32,
    fl: &Charset,
) {
    loop {
        match tree[idx].tag {
            TTag::TChar => {
                codechar(compst, tree[idx].n, tt);
                return;
            }
            TTag::TAny => {
                compst.addinstruction(Opcode::IAny, 0);
                return;
            }
            TTag::TSet => {
                codecharset(compst, tree, idx, tt);
                return;
            }
            TTag::TTrue => return,
            TTag::TFalse => {
                compst.addinstruction(Opcode::IFail, 0);
                return;
            }
            TTag::TUTFR => {
                codeutfr(compst, tree, idx);
                return;
            }
            TTag::TChoice => {
                codechoice(compst, tree, sib1(idx), sib2(tree, idx), opt, fl);
                return;
            }
            TTag::TRep => {
                coderep(compst, tree, sib1(idx), opt, fl);
                return;
            }
            TTag::TBehind => {
                codebehind(compst, tree, idx);
                return;
            }
            TTag::TNot => {
                codenot(compst, tree, sib1(idx));
                return;
            }
            TTag::TAnd => {
                codeand(compst, tree, sib1(idx), tt);
                return;
            }
            TTag::TCapture => {
                codecapture(compst, tree, idx, tt, fl);
                return;
            }
            TTag::TRunTime => {
                coderuntime(compst, tree, idx, tt);
                return;
            }
            TTag::TGrammar => {
                codegrammar(compst, tree, idx);
                return;
            }
            TTag::TCall => {
                codecall(compst, tree, idx);
                return;
            }
            TTag::TSeq => {
                let p1 = sib1(idx);
                let p2 = sib2(tree, idx);
                tt = codeseq1(compst, tree, p1, p2, tt, fl);
                // tail call: codegen(compst, tree, p2, opt, tt, fl)
                idx = p2;
                // fl stays the same, opt stays the same
                continue;
            }
            _ => return,
        }
    }
}

/// Peephole optimizer
fn peephole(compst: &mut CompileState) {
    let code = compst.p.code.as_mut().unwrap();
    let ncode = compst.ncode;
    let mut i = 0;
    while i < ncode {
        match code[i].code {
            Opcode::IChoice
            | Opcode::ICall
            | Opcode::ICommit
            | Opcode::IPartialCommit
            | Opcode::IBackCommit
            | Opcode::ITestChar
            | Opcode::ITestSet
            | Opcode::ITestAny => {
                // optimize label to final destination
                let fl = finallabel(code, i);
                code[i + 1].offset = fl as i32 - i as i32;
            }
            Opcode::IJmp => {
                let ft = finaltarget(code, i);
                match code[ft].code {
                    Opcode::IRet | Opcode::IFail | Opcode::IFailTwice | Opcode::IEnd => {
                        code[i] = code[ft].clone();
                        code[i + 1].code = Opcode::IEmpty;
                    }
                    Opcode::ICommit | Opcode::IPartialCommit | Opcode::IBackCommit => {
                        let fft = finallabel(code, ft);
                        code[i] = code[ft].clone();
                        code[i + 1].offset = fft as i32 - i as i32;
                        continue; // re-optimize
                    }
                    _ => {
                        code[i + 1].offset = ft as i32 - i as i32;
                    }
                }
            }
            _ => {}
        }
        i += sizei(&code[i]);
    }
}

/// Compile a pattern tree into VM instructions.
pub fn compile(p: &mut Pattern) {
    let tree_len = p.tree.len();
    let initial_size = tree_len / 2 + 2;

    // Initialize code vector
    let mut code = Vec::with_capacity(initial_size);
    for _ in 0..initial_size {
        code.push(Instruction::new(Opcode::IEmpty));
    }
    p.code = Some(code);

    let mut compst = CompileState { p, ncode: 0 };

    // Build a clone of tree for codegen (needed because we borrow compst.p mutably)
    let tree = compst.p.tree.clone();
    codegen(&mut compst, &tree, 0, false, NOINST, &FULLSET);
    compst.addinstruction(Opcode::IEnd, 0);

    // Trim code to actual size
    let ncode = compst.ncode;
    if let Some(ref mut code) = compst.p.code {
        code.truncate(ncode);
    }

    peephole(&mut compst);
}
