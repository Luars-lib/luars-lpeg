pub const VERSION: &str = "1.1.0";
pub const PATTERN_T: &str = "lpeg-pattern";

/// Default maximum backtrack stack size
pub const MAXBACK: usize = 400;
/// Maximum number of rules in a grammar
pub const MAXRULES: usize = 1000;

pub const BITSPERCHAR: usize = 8;
/// 256-bit bitmap = 32 bytes
pub const CHARSETSIZE: usize = 256 / BITSPERCHAR;

/// Maximum look-behind distance
pub const MAXBEHIND: usize = 255;
/// Maximum offset in IFullCapture
pub const MAXOFF: usize = 0xF;
/// Initial capture list size
pub const INITCAPSIZE: usize = 32;
/// Initial backtrack stack size
pub const INITBACK: usize = MAXBACK;

/// Maximum recursion level for capture processing
pub const MAXRECLEVEL: usize = 200;
/// Maximum lookback distance for findopen
pub const MAXLOP: usize = 20;

/// Number of fixed arguments to `match` (pattern, subject, init)
pub const FIXEDARGS: usize = 3;

// ============================================================
// Character set (256-bit bitmap)
// ============================================================

pub type Charset = [u8; CHARSETSIZE];

#[inline]
pub fn setchar(cs: &mut Charset, b: u8) {
    cs[(b >> 3) as usize] |= 1 << (b & 7);
}

#[inline]
pub fn clearset(cs: &mut Charset) {
    *cs = [0u8; CHARSETSIZE];
}

#[inline]
pub fn fillset(cs: &mut Charset, v: u8) {
    *cs = [v; CHARSETSIZE];
}

// ============================================================
// TTree node types (pattern AST)
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TTag {
    TChar = 0,
    TSet,
    TAny,
    TTrue,
    TFalse,
    /// UTF-8 codepoint range
    TUTFR,
    /// sib1*
    TRep,
    /// sib1 sib2
    TSeq,
    /// sib1 / sib2
    TChoice,
    /// !sib1
    TNot,
    /// &sib1
    TAnd,
    /// call rule; sib2 is the rule
    TCall,
    /// unresolved call
    TOpenCall,
    /// grammar rule; sib1=TXInfo, sib2=next rule
    TRule,
    /// extra info node
    TXInfo,
    /// grammar; sib1 is initial rule
    TGrammar,
    /// look-behind; sib1=pattern, n=distance
    TBehind,
    /// capture; cap=CapKind, sib1=body
    TCapture,
    /// runtime capture; key=function, sib1=body
    TRunTime,
}

/// Number of siblings for each TTag
pub const NUM_SIBLINGS: [u8; 19] = [
    0, 0, 0, // TChar, TSet, TAny
    0, 0, 0, // TTrue, TFalse, TUTFR
    1, // TRep
    2, 2, // TSeq, TChoice
    1, 1, // TNot, TAnd
    0, 0, // TCall, TOpenCall
    2, 1, 1, // TRule, TXInfo, TGrammar
    1, // TBehind
    1, 1, // TCapture, TRunTime
];

// ============================================================
// Capture kinds
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CapKind {
    Cclose = 0,
    Cposition,
    Cconst,
    Cbackref,
    Carg,
    Csimple,
    Ctable,
    Cfunction,
    Cacc,
    Cquery,
    Cstring,
    Cnum,
    Csubst,
    Cfold,
    Cruntime,
    Cgroup,
}

impl CapKind {
    pub fn from_u8(v: u8) -> Self {
        match v {
            0 => CapKind::Cclose,
            1 => CapKind::Cposition,
            2 => CapKind::Cconst,
            3 => CapKind::Cbackref,
            4 => CapKind::Carg,
            5 => CapKind::Csimple,
            6 => CapKind::Ctable,
            7 => CapKind::Cfunction,
            8 => CapKind::Cacc,
            9 => CapKind::Cquery,
            10 => CapKind::Cstring,
            11 => CapKind::Cnum,
            12 => CapKind::Csubst,
            13 => CapKind::Cfold,
            14 => CapKind::Cruntime,
            15 => CapKind::Cgroup,
            _ => panic!("invalid CapKind: {v}"),
        }
    }
}

// ============================================================
// VM opcodes
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Opcode {
    IAny = 0,
    IChar,
    ISet,
    ITestAny,
    ITestChar,
    ITestSet,
    ISpan,
    IUTFR,
    IBehind,
    IRet,
    IEnd,
    IChoice,
    IJmp,
    ICall,
    IOpenCall,
    ICommit,
    IPartialCommit,
    IBackCommit,
    IFailTwice,
    IFail,
    IGiveup,
    IFullCapture,
    IOpenCapture,
    ICloseCapture,
    ICloseRunTime,
    IEmpty,
}

// ============================================================
// Instruction (compiled VM instruction)
// ============================================================

#[derive(Debug, Clone)]
pub struct Instruction {
    pub code: Opcode,
    pub aux1: u8,
    /// For captures: key into ktable. For sets: (offset, size).
    pub key: i16,
    pub set_offset: u8,
    pub set_size: u8,
    /// Offset for jump instructions (stored in next slot in C, here inline)
    pub offset: i32,
    /// Charset data buffer (for ISet, ISpan, ITestSet)
    pub charset: Option<Vec<u8>>,
}

impl Instruction {
    pub fn new(code: Opcode) -> Self {
        Instruction {
            code,
            aux1: 0,
            key: 0,
            set_offset: 0,
            set_size: 0,
            offset: 0,
            charset: None,
        }
    }

    /// Extract CapKind from aux1 (lower 4 bits)
    #[inline]
    pub fn getkind(&self) -> CapKind {
        CapKind::from_u8(self.aux1 & 0xF)
    }

    /// Extract capture offset from aux1 (upper 4 bits)
    #[inline]
    pub fn getoff(&self) -> u8 {
        (self.aux1 >> 4) & 0xF
    }

    /// Pack kind and offset into aux1
    #[inline]
    pub fn joinkindoff(kind: CapKind, off: u8) -> u8 {
        (kind as u8) | (off << 4)
    }

    /// For IUTFR: extract 24-bit "to" value
    #[inline]
    pub fn utf_to(&self) -> i32 {
        ((self.key as i32) << 8) | (self.aux1 as i32)
    }

    /// Test if character is in the instruction's charset
    pub fn charinset(&self, c: u8) -> bool {
        if let Some(ref cs) = self.charset {
            let offset_bits = self.set_offset as u32;
            let size_bits = cs.len() as u32 * 8;
            let adjusted = (c as u32).wrapping_sub(offset_bits);
            if adjusted >= size_bits {
                return self.aux1 != 0; // default value
            }
            let byte_idx = (adjusted / 8) as usize;
            let bit_idx = adjusted % 8;
            if byte_idx < cs.len() {
                (cs[byte_idx] >> bit_idx) & 1 != 0
            } else {
                self.aux1 != 0
            }
        } else {
            false
        }
    }
}

// ============================================================
// TTree node (pattern AST node)
// ============================================================

/// Compact set info stored in TSet nodes
#[derive(Debug, Clone)]
pub struct CompactSet {
    pub offset: u8,
    pub size: u8,
    pub deflt: u8,
    pub bitmap: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct TTree {
    pub tag: TTag,
    /// Capture kind (for TCapture) or UTF-8 length (for TUTFR)
    pub cap: u8,
    /// Key into ktable (0 = no key)
    pub key: u16,
    /// union: ps (second child offset), n (counter/char value), or set
    pub ps: i32,
    pub n: i32,
    pub set: Option<CompactSet>,
}

impl TTree {
    pub fn new(tag: TTag) -> Self {
        TTree {
            tag,
            cap: 0,
            key: 0,
            ps: 0,
            n: 0,
            set: None,
        }
    }

    pub fn num_siblings(&self) -> u8 {
        NUM_SIBLINGS[self.tag as usize]
    }
}

// ============================================================
// Capture (runtime capture during matching)
// ============================================================

#[derive(Debug, Clone)]
pub struct Capture {
    /// Position in subject string
    pub index: u32,
    /// Extra info (ktable index, arg index, etc.)
    pub idx: u16,
    /// Capture kind
    pub kind: CapKind,
    /// Full capture size + 1 (0 = open capture, not yet closed)
    pub siz: u8,
}

impl Capture {
    pub fn new() -> Self {
        Capture {
            index: 0,
            idx: 0,
            kind: CapKind::Cclose,
            siz: 0,
        }
    }

    #[inline]
    pub fn is_close(&self) -> bool {
        self.kind == CapKind::Cclose
    }

    #[inline]
    pub fn is_open(&self) -> bool {
        self.siz == 0
    }

    /// Check if c2 is inside self
    #[inline]
    pub fn cap_inside(&self, c2: &Capture) -> bool {
        if self.is_open() {
            !c2.is_close()
        } else {
            c2.index < self.index + self.siz as u32 - 1
        }
    }

    /// Get size of this capture (for full captures or using a close cap)
    #[inline]
    pub fn cap_size(&self, close: &Capture) -> u32 {
        if self.is_open() {
            close.index - self.index
        } else {
            self.siz as u32 - 1
        }
    }
}

// ============================================================
// Backtrack stack entry
// ============================================================

#[derive(Debug, Clone)]
pub struct StackEntry {
    /// Saved subject position (None for call frames)
    pub s: Option<usize>,
    /// Next instruction index
    pub p: usize,
    /// Capture level
    pub caplevel: usize,
}

// ============================================================
// CharsetInfo (analysis result)
// ============================================================

#[derive(Debug, Clone)]
pub struct CharsetInfo {
    pub cs: Vec<u8>,
    pub offset: usize,
    pub size: usize,
    pub deflt: u8,
}
