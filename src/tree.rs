use crate::charset::*;
/// Tree analysis and construction utilities - mirrors parts of lpcode.c and lptree.c
use crate::types::*;

// ============================================================
// Tree child access helpers
// ============================================================

/// First child is at idx+1
#[inline]
pub fn sib1(idx: usize) -> usize {
    idx + 1
}

/// Second child is at idx + tree[idx].ps
#[inline]
pub fn sib2(tree: &[TTree], idx: usize) -> usize {
    (idx as i32 + tree[idx].ps) as usize
}

// ============================================================
// Nullable / Nofail analysis (from lpcode.c checkaux)
// ============================================================

pub const PE_NULLABLE: u8 = 0;
pub const PE_NOFAIL: u8 = 1;

/// Check whether a pattern tree has a given property.
/// - PEnullable: can match without consuming any character
/// - PEnofail: never fails for any string
pub fn checkaux(tree: &[TTree], idx: usize, pred: u8) -> bool {
    let t = &tree[idx];
    match t.tag {
        TTag::TChar | TTag::TSet | TTag::TAny | TTag::TUTFR | TTag::TFalse | TTag::TOpenCall => {
            false
        }

        TTag::TRep | TTag::TTrue => true,

        TTag::TNot | TTag::TBehind => {
            if pred == PE_NOFAIL {
                false
            } else {
                true
            }
        }

        TTag::TAnd => {
            if pred == PE_NULLABLE {
                true
            } else {
                checkaux(tree, sib1(idx), pred)
            }
        }

        TTag::TRunTime => {
            if pred == PE_NOFAIL {
                false
            } else {
                checkaux(tree, sib1(idx), pred)
            }
        }

        TTag::TSeq => {
            if !checkaux(tree, sib1(idx), pred) {
                false
            } else {
                checkaux(tree, sib2(tree, idx), pred)
            }
        }

        TTag::TChoice => {
            if checkaux(tree, sib2(tree, idx), pred) {
                true
            } else {
                checkaux(tree, sib1(idx), pred)
            }
        }

        TTag::TCapture | TTag::TGrammar | TTag::TRule | TTag::TXInfo => {
            checkaux(tree, sib1(idx), pred)
        }

        TTag::TCall => checkaux(tree, sib2(tree, idx), pred),
    }
}

#[inline]
pub fn nullable(tree: &[TTree], idx: usize) -> bool {
    checkaux(tree, idx, PE_NULLABLE)
}

#[inline]
pub fn nofail(tree: &[TTree], idx: usize) -> bool {
    checkaux(tree, idx, PE_NOFAIL)
}

// ============================================================
// fixedlen: number of chars to match (or -1 if variable)
// ============================================================

pub fn fixedlen(tree: &[TTree], idx: usize) -> i32 {
    fixedlen_inner(tree, idx, 0)
}

fn fixedlen_inner(tree: &[TTree], idx: usize, len: i32) -> i32 {
    let t = &tree[idx];
    match t.tag {
        TTag::TChar | TTag::TSet | TTag::TAny => len + 1,

        TTag::TUTFR => {
            let s1 = sib1(idx);
            if t.cap == tree[s1].cap {
                len + t.cap as i32
            } else {
                -1
            }
        }

        TTag::TFalse | TTag::TTrue | TTag::TNot | TTag::TAnd | TTag::TBehind => len,

        TTag::TRep | TTag::TRunTime | TTag::TOpenCall => -1,

        TTag::TCapture | TTag::TRule | TTag::TGrammar | TTag::TXInfo => {
            fixedlen_inner(tree, sib1(idx), len)
        }

        TTag::TCall => {
            let n1 = fixedlen(tree, sib2(tree, idx));
            if n1 < 0 { -1 } else { len + n1 }
        }

        TTag::TSeq => {
            let n1 = fixedlen(tree, sib1(idx));
            if n1 < 0 {
                -1
            } else {
                fixedlen_inner(tree, sib2(tree, idx), len + n1)
            }
        }

        TTag::TChoice => {
            let n1 = fixedlen(tree, sib1(idx));
            let n2 = fixedlen(tree, sib2(tree, idx));
            if n1 != n2 || n1 < 0 { -1 } else { len + n1 }
        }
    }
}

// ============================================================
// hascaptures: check if tree has captures
// ============================================================

pub fn hascaptures(tree: &[TTree], idx: usize) -> bool {
    let t = &tree[idx];
    match t.tag {
        TTag::TCapture | TTag::TRunTime => true,

        TTag::TCall => {
            // Avoid infinite recursion for recursive rules
            hascaptures(tree, sib2(tree, idx))
        }

        TTag::TRule => hascaptures(tree, sib1(idx)),

        _ => {
            let siblings = NUM_SIBLINGS[t.tag as usize];
            match siblings {
                1 => hascaptures(tree, sib1(idx)),
                2 => hascaptures(tree, sib1(idx)) || hascaptures(tree, sib2(tree, idx)),
                _ => false,
            }
        }
    }
}

// ============================================================
// getfirst: computes the 'first set' of a pattern
// Returns non-zero if the pattern can match the empty string (bit 1)
// or has a match-time capture (bit 2)
// ============================================================

pub const FULLSET: Charset = [0xFF; CHARSETSIZE];

pub fn getfirst(tree: &[TTree], idx: usize, follow: &Charset, firstset: &mut Charset) -> u8 {
    let t = &tree[idx];
    match t.tag {
        TTag::TChar | TTag::TSet | TTag::TAny | TTag::TFalse => {
            tocharset(tree, idx, firstset);
            0
        }

        TTag::TUTFR => {
            clearset(firstset);
            let s1 = sib1(idx);
            for c in tree[idx].key..=tree[s1].key {
                if (c as usize) < 256 {
                    setchar(firstset, c as u8);
                }
            }
            0
        }

        TTag::TTrue => {
            *firstset = *follow;
            1 // accepts empty string
        }

        TTag::TChoice => {
            let mut csaux = [0u8; CHARSETSIZE];
            let e1 = getfirst(tree, sib1(idx), follow, firstset);
            let e2 = getfirst(tree, sib2(tree, idx), follow, &mut csaux);
            for i in 0..CHARSETSIZE {
                firstset[i] |= csaux[i];
            }
            e1 | e2
        }

        TTag::TSeq => {
            if !nullable(tree, sib1(idx)) {
                getfirst(tree, sib1(idx), &FULLSET, firstset)
            } else {
                let mut csaux = [0u8; CHARSETSIZE];
                let e2 = getfirst(tree, sib2(tree, idx), follow, &mut csaux);
                let e1 = getfirst(tree, sib1(idx), &csaux, firstset);
                if e1 == 0 {
                    0
                } else if (e1 | e2) & 2 != 0 {
                    2
                } else {
                    e2
                }
            }
        }

        TTag::TRep => {
            getfirst(tree, sib1(idx), follow, firstset);
            for i in 0..CHARSETSIZE {
                firstset[i] |= follow[i];
            }
            1
        }

        TTag::TCapture | TTag::TGrammar | TTag::TRule | TTag::TXInfo => {
            getfirst(tree, sib1(idx), follow, firstset)
        }

        TTag::TRunTime => {
            let e = getfirst(tree, sib1(idx), &FULLSET, firstset);
            if e != 0 { 2 } else { 0 }
        }

        TTag::TCall => getfirst(tree, sib2(tree, idx), follow, firstset),

        TTag::TAnd => {
            let e = getfirst(tree, sib1(idx), follow, firstset);
            for i in 0..CHARSETSIZE {
                firstset[i] &= follow[i];
            }
            e
        }

        TTag::TNot => {
            let mut temp = [0u8; CHARSETSIZE];
            if tocharset(tree, sib1(idx), &mut temp) {
                cs_complement(&mut temp);
                *firstset = temp;
                1
            } else {
                let e = getfirst(tree, sib1(idx), follow, firstset);
                *firstset = *follow;
                e | 1
            }
        }

        TTag::TBehind => {
            let e = getfirst(tree, sib1(idx), follow, firstset);
            *firstset = *follow;
            e | 1
        }

        TTag::TOpenCall => {
            clearset(firstset);
            0
        }
    }
}

// ============================================================
// headfail: true if tree can fail only on the next character
// ============================================================

pub fn headfail(tree: &[TTree], idx: usize) -> bool {
    let t = &tree[idx];
    match t.tag {
        TTag::TChar | TTag::TSet | TTag::TAny | TTag::TFalse => true,
        TTag::TTrue | TTag::TRep | TTag::TRunTime | TTag::TNot | TTag::TBehind | TTag::TUTFR => {
            false
        }
        TTag::TCapture | TTag::TGrammar | TTag::TRule | TTag::TXInfo | TTag::TAnd => {
            headfail(tree, sib1(idx))
        }
        TTag::TCall => headfail(tree, sib2(tree, idx)),
        TTag::TSeq => {
            if !nofail(tree, sib2(tree, idx)) {
                false
            } else {
                headfail(tree, sib1(idx))
            }
        }
        TTag::TChoice => {
            if !headfail(tree, sib1(idx)) {
                false
            } else {
                headfail(tree, sib2(tree, idx))
            }
        }
        TTag::TOpenCall => false,
    }
}

// ============================================================
// needfollow: does codegen benefit from a follow set?
// ============================================================

pub fn needfollow(tree: &[TTree], idx: usize) -> bool {
    let t = &tree[idx];
    match t.tag {
        TTag::TChar
        | TTag::TSet
        | TTag::TAny
        | TTag::TUTFR
        | TTag::TFalse
        | TTag::TTrue
        | TTag::TAnd
        | TTag::TNot
        | TTag::TRunTime
        | TTag::TGrammar
        | TTag::TCall
        | TTag::TBehind
        | TTag::TOpenCall => false,

        TTag::TChoice | TTag::TRep => true,

        TTag::TCapture | TTag::TXInfo | TTag::TRule => needfollow(tree, sib1(idx)),

        TTag::TSeq => needfollow(tree, sib2(tree, idx)),
    }
}
