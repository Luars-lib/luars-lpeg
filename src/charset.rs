/// Character set operations - mirrors lpcset.c / lpcset.h
use crate::types::*;

/// Analyze a 256-bit charset and classify it.
/// Returns the opcode type and fills CharsetInfo:
/// - IFail: empty set
/// - IAny: full set (all 256 chars)
/// - IChar: singleton set (info.offset = the char value)
/// - ISet: general set (info filled with compact range)
pub fn charsettype(cs: &Charset, info: &mut CharsetInfo) -> Opcode {
    // Find lowest byte with a 1-bit
    let mut low1 = 0usize;
    while low1 < CHARSETSIZE && cs[low1] == 0 {
        low1 += 1;
    }
    if low1 == CHARSETSIZE {
        return Opcode::IFail; // empty set
    }

    // Find highest byte with a 1-bit
    let mut high1 = CHARSETSIZE - 1;
    while cs[high1] == 0 {
        high1 -= 1; // low1 is sentinel
    }

    // Check singleton
    if low1 == high1 {
        let b = cs[low1];
        if b & (b - 1) == 0 {
            // only one bit set
            info.offset = onlybit(low1 * BITSPERCHAR, b as u32);
            return Opcode::IChar;
        }
    }

    // Find lowest byte with a 0-bit
    let mut low0 = 0usize;
    while low0 < CHARSETSIZE && cs[low0] == 0xFF {
        low0 += 1;
    }
    if low0 == CHARSETSIZE {
        return Opcode::IAny; // full set
    }

    // Find highest byte with a 0-bit
    let mut high0 = CHARSETSIZE - 1;
    while cs[high0] == 0xFF {
        high0 -= 1;
    }

    if high1 - low1 <= high0 - low0 {
        // range of 1s smaller than range of 0s
        info.offset = low1;
        info.size = high1 - low1 + 1;
        info.deflt = 0;
    } else {
        info.offset = low0;
        info.size = high0 - low0 + 1;
        info.deflt = 0xFF;
    }
    info.cs = cs[info.offset..info.offset + info.size].to_vec();
    Opcode::ISet
}

/// Get the single bit position in a byte, adding base offset `c`.
fn onlybit(c: usize, b: u32) -> usize {
    let mut c = c;
    let mut b = b;
    if b & 0xF0 != 0 {
        c += 4;
        b >>= 4;
    }
    if b & 0x0C != 0 {
        c += 2;
        b >>= 2;
    }
    if b & 0x02 != 0 {
        c += 1;
    }
    c
}

/// Get byte from compact charset, returning default if out of range.
pub fn getbytefromcharset(info: &CharsetInfo, index: usize) -> u8 {
    if index < info.cs.len() {
        info.cs[index]
    } else {
        info.deflt
    }
}

/// Convert a TTree node (TSet, TChar, TAny, TFalse) into a full 256-bit charset.
/// Returns true if conversion was possible.
pub fn tocharset(tree: &[TTree], idx: usize, cs: &mut Charset) -> bool {
    match tree[idx].tag {
        TTag::TChar => {
            clearset(cs);
            setchar(cs, tree[idx].n as u8);
            true
        }
        TTag::TAny => {
            fillset(cs, 0xFF);
            true
        }
        TTag::TFalse => {
            clearset(cs);
            true
        }
        TTag::TSet => {
            if let Some(ref set) = tree[idx].set {
                fillset(cs, set.deflt);
                for i in 0..set.size as usize {
                    if i < set.bitmap.len() {
                        cs[set.offset as usize + i] = set.bitmap[i];
                    }
                }
            } else {
                clearset(cs);
            }
            true
        }
        _ => false,
    }
}

/// Extract compact set info from a TSet tree node.
pub fn tree2cset(tree: &[TTree], idx: usize) -> CharsetInfo {
    let t = &tree[idx];
    assert!(t.tag == TTag::TSet);
    let set = t.set.as_ref().unwrap();
    CharsetInfo {
        offset: set.offset as usize,
        size: set.size as usize,
        deflt: set.deflt,
        cs: set.bitmap.clone(),
    }
}

/// Check if two charsets are disjoint (no common char).
pub fn cs_disjoint(cs1: &Charset, cs2: &Charset) -> bool {
    for i in 0..CHARSETSIZE {
        if cs1[i] & cs2[i] != 0 {
            return false;
        }
    }
    true
}

/// Complement a charset in place.
pub fn cs_complement(cs: &mut Charset) {
    for i in 0..CHARSETSIZE {
        cs[i] = !cs[i];
    }
}
