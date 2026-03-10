use std::any::Any;

use luars::{
    CFunction, LuaResult, LuaState, LuaUserdata, LuaValue, UdValue, UserDataTrait,
    lua_value::LuaValueKind, lua_vm::LuaError,
};

use crate::{
    charset::{charsettype, tocharset},
    code::compile,
    tree::{fixedlen, hascaptures, nofail, nullable, sib1, sib2},
    types::{
        CHARSETSIZE, CapKind, Capture, Charset, CharsetInfo, CompactSet, FIXEDARGS, INITCAPSIZE,
        Instruction, MAXBEHIND, MAXRECLEVEL, MAXRULES, NUM_SIBLINGS, Opcode, PATTERN_T, TTag,
        TTree, VERSION, setchar,
    },
    vm::vm_match,
};

/// A full LPeg pattern: tree of nodes + optional compiled instructions + ktable
#[derive(Debug, Clone)]
pub struct Pattern {
    pub tree: Vec<TTree>,
    pub code: Option<Vec<Instruction>>,
    /// ktable: Lua values associated with pattern nodes (stored as indices to
    /// a Lua-side table, but we keep a Vec of LuaValue here)
    pub ktable: Vec<luars::LuaValue>,
}

impl Pattern {
    pub fn new(tree: Vec<TTree>) -> Self {
        Pattern {
            tree,
            code: None,
            ktable: Vec::new(),
        }
    }

    /// Invalidate compiled code (when tree is modified)
    pub fn invalidate_code(&mut self) {
        self.code = None;
    }
}

/// Try to convert a UdValue to a Pattern (for use in operator implementations)
fn udvalue_to_pattern(v: &UdValue) -> Option<Pattern> {
    match v {
        UdValue::UserdataRef(ptr) => {
            let any_ref = unsafe { &**ptr };
            any_ref.downcast_ref::<Pattern>().cloned()
        }
        UdValue::Integer(n) => {
            let n = *n as i32;
            if n == 0 {
                Some(Pattern::new(vec![TTree::new(TTag::TTrue)]))
            } else if n > 0 {
                let mut tree = Vec::with_capacity(n as usize);
                for _ in 0..n as usize {
                    tree.push(TTree::new(TTag::TAny));
                }
                if n > 1 {
                    // Build left-deep Seq chain
                    let mut seq_tree = Vec::new();
                    seq_tree.push(TTree::new(TTag::TAny));
                    for _ in 1..n as usize {
                        let old_len = seq_tree.len();
                        let mut seq = TTree::new(TTag::TSeq);
                        seq.ps = old_len as i32 + 1;
                        let mut new_tree = vec![seq];
                        new_tree.extend_from_slice(&seq_tree);
                        new_tree.push(TTree::new(TTag::TAny));
                        seq_tree = new_tree;
                    }
                    Some(Pattern::new(seq_tree))
                } else {
                    Some(Pattern::new(tree))
                }
            } else {
                // Negative n: match only if fewer than -n chars remain
                let n = (-n) as usize;
                let mut result_tree = Vec::new();
                let not = TTree::new(TTag::TNot);
                result_tree.push(not);
                for _ in 0..n {
                    result_tree.push(TTree::new(TTag::TAny));
                }
                if n > 1 {
                    // Build seq chain for the n any's
                    let mut inner = vec![TTree::new(TTag::TAny)];
                    for _ in 1..n {
                        let old_len = inner.len();
                        let mut seq = TTree::new(TTag::TSeq);
                        seq.ps = old_len as i32 + 1;
                        let mut new_inner = vec![seq];
                        new_inner.extend_from_slice(&inner);
                        new_inner.push(TTree::new(TTag::TAny));
                        inner = new_inner;
                    }
                    let mut not_tree = vec![TTree::new(TTag::TNot)];
                    not_tree.extend_from_slice(&inner);
                    Some(Pattern::new(not_tree))
                } else {
                    Some(Pattern::new(result_tree))
                }
            }
        }
        UdValue::Boolean(b) => {
            if *b {
                Some(Pattern::new(vec![TTree::new(TTag::TTrue)]))
            } else {
                Some(Pattern::new(vec![TTree::new(TTag::TFalse)]))
            }
        }
        UdValue::Str(s) => {
            if s.is_empty() {
                return Some(Pattern::new(vec![TTree::new(TTag::TTrue)]));
            }
            let bytes = s.as_bytes();
            Some(string_pattern(bytes))
        }
        _ => None,
    }
}

impl UserDataTrait for Pattern {
    fn type_name(&self) -> &'static str {
        PATTERN_T
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn get_field(&self, key: &str) -> Option<UdValue> {
        // Expose lpeg module functions as methods on pattern objects
        let f: CFunction = match key {
            "match" => lp_match,
            "B" => lp_behind,
            "V" => lp_V,
            "C" => lp_simplecapture,
            "Cc" => lp_constcapture,
            "Cmt" => lp_matchtime,
            "Cb" => lp_backref,
            "Carg" => lp_argcapture,
            "Cp" => lp_poscapture,
            "Cs" => lp_substcapture,
            "Ct" => lp_tablecapture,
            "Cf" => lp_foldcapture,
            "Cg" => lp_groupcapture,
            "P" => lp_P,
            "S" => lp_set,
            "R" => lp_range,
            "utfR" => lp_utfr,
            "locale" => lp_locale,
            "setmaxstack" => lp_setmax,
            "type" => lp_type,
            "version" => return Some(UdValue::Str(format!("LPeg {}", VERSION))),
            _ => return None,
        };
        Some(UdValue::Function(f))
    }

    // __add  → lp_choice
    fn lua_add(&self, other: &UdValue) -> Option<UdValue> {
        let p2 = udvalue_to_pattern(other)?;
        // Charset optimization
        let mut cs1 = [0u8; CHARSETSIZE];
        let mut cs2 = [0u8; CHARSETSIZE];
        if tocharset(&self.tree, 0, &mut cs1) && tocharset(&p2.tree, 0, &mut cs2) {
            for i in 0..CHARSETSIZE {
                cs1[i] |= cs2[i];
            }
            return Some(UdValue::UserdataOwned(Box::new(newcharset_pat(&cs1))));
        }
        if nofail(&self.tree, 0) || p2.tree[0].tag == TTag::TFalse {
            return Some(UdValue::UserdataOwned(Box::new(self.clone())));
        }
        if self.tree[0].tag == TTag::TFalse {
            return Some(UdValue::UserdataOwned(Box::new(p2)));
        }
        Some(UdValue::UserdataOwned(Box::new(newroot2sib(
            TTag::TChoice,
            self,
            &p2,
        ))))
    }

    // __mul → lp_seq
    fn lua_mul(&self, other: &UdValue) -> Option<UdValue> {
        let p2 = udvalue_to_pattern(other)?;
        if self.tree[0].tag == TTag::TFalse || p2.tree[0].tag == TTag::TTrue {
            return Some(UdValue::UserdataOwned(Box::new(self.clone())));
        }
        if self.tree[0].tag == TTag::TTrue {
            return Some(UdValue::UserdataOwned(Box::new(p2)));
        }
        Some(UdValue::UserdataOwned(Box::new(newroot2sib(
            TTag::TSeq,
            self,
            &p2,
        ))))
    }

    // __sub → lp_sub
    fn lua_sub(&self, other: &UdValue) -> Option<UdValue> {
        let p2 = udvalue_to_pattern(other)?;
        let mut cs1 = [0u8; CHARSETSIZE];
        let mut cs2 = [0u8; CHARSETSIZE];
        if tocharset(&self.tree, 0, &mut cs1) && tocharset(&p2.tree, 0, &mut cs2) {
            for i in 0..CHARSETSIZE {
                cs1[i] &= !cs2[i];
            }
            return Some(UdValue::UserdataOwned(Box::new(newcharset_pat(&cs1))));
        }
        // Build: Seq(Not(p2), self)
        let s1 = self.tree.len();
        let s2 = p2.tree.len();
        let mut tree = Vec::with_capacity(2 + s1 + s2);
        let mut seq = TTree::new(TTag::TSeq);
        seq.ps = 2 + s2 as i32;
        tree.push(seq);
        tree.push(TTree::new(TTag::TNot));
        tree.extend_from_slice(&p2.tree);
        tree.extend_from_slice(&self.tree);
        let mut result = Pattern::new(tree);
        result.ktable = self.ktable.clone();
        joinktables(&mut result, 2, &p2.ktable);
        Some(UdValue::UserdataOwned(Box::new(result)))
    }

    // __div → lp_divcapture
    fn lua_div(&self, other: &UdValue) -> Option<UdValue> {
        match other {
            UdValue::Function(f) => {
                let lv = LuaValue::cfunction(*f);
                Some(UdValue::UserdataOwned(Box::new(capture_aux(
                    self,
                    CapKind::Cfunction,
                    Some(lv),
                ))))
            }
            UdValue::Integer(n) => {
                let mut result = capture_aux(self, CapKind::Cnum, None);
                result.tree[0].key = *n as u16;
                Some(UdValue::UserdataOwned(Box::new(result)))
            }
            // String and Table captures need LuaState for allocation, handled by lp_divcapture
            _ => None,
        }
    }

    // __mod → lp_acccapture
    fn lua_mod(&self, other: &UdValue) -> Option<UdValue> {
        match other {
            UdValue::Function(f) => {
                let lv = LuaValue::cfunction(*f);
                Some(UdValue::UserdataOwned(Box::new(capture_aux(
                    self,
                    CapKind::Cacc,
                    Some(lv),
                ))))
            }
            _ => None,
        }
    }

    // __unm → lp_not
    fn lua_unm(&self) -> Option<UdValue> {
        Some(UdValue::UserdataOwned(Box::new(newroot1sib(
            TTag::TNot,
            self,
        ))))
    }

    // __len → lp_and
    fn lua_len(&self) -> Option<UdValue> {
        Some(UdValue::UserdataOwned(Box::new(newroot1sib(
            TTag::TAnd,
            self,
        ))))
    }

    fn lua_tostring(&self) -> Option<String> {
        Some(format!("pattern ({})", self.tree.len()))
    }

    fn set_field(&mut self, _key: &str, _value: luars::UdValue) -> Option<Result<(), String>> {
        None
    }

    fn lua_eq(&self, _other: &dyn UserDataTrait) -> Option<bool> {
        None
    }

    fn lua_lt(&self, _other: &dyn UserDataTrait) -> Option<bool> {
        None
    }

    fn lua_le(&self, _other: &dyn UserDataTrait) -> Option<bool> {
        None
    }

    fn lua_concat(&self, _other: &luars::UdValue) -> Option<luars::UdValue> {
        None
    }

    fn lua_gc(&mut self) {}

    fn lua_close(&mut self) {}

    fn lua_call(&self) -> Option<luars::lua_vm::CFunction> {
        None
    }

    fn lua_next(&self, _control: &luars::UdValue) -> Option<(luars::UdValue, luars::UdValue)> {
        None
    }

    fn field_names(&self) -> &'static [&'static str] {
        &[]
    }
}

pub(crate) fn lp_match(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if args.len() < 2 {
        return Err(l.error("lpeg.match: expected at least 2 arguments".to_string()));
    }

    // arg0 = pattern, arg1 = subject
    let subj_val = args[1].clone();
    let subj = match subj_val.as_str() {
        Some(s) => s,
        None => return Err(l.error("string expected as second argument".to_string())),
    };
    let subj_bytes = subj.as_bytes();
    let subj_len = subj_bytes.len();

    // Get extra args (arg3, arg4, ...) for Carg captures
    let extra_args: Vec<LuaValue> = if args.len() > FIXEDARGS {
        args[FIXEDARGS..].to_vec()
    } else {
        Vec::new()
    };

    // Get pattern and compile if needed
    let pat_val = args[0].clone();
    let pat = get_pattern_mut(&pat_val).ok_or_else(|| l.error("pattern expected".to_string()))?;

    // Compile pattern if not already compiled
    if pat.code.is_none() {
        // finalfix: resolve open calls (only needed for grammars)
        finalfix(&mut pat.tree, None, 0);
        compile(pat);
    }

    let init_pos = initposition(l, subj_len);

    let code = pat.code.as_ref().unwrap();
    let ktable = pat.ktable.clone();

    let mut captures = Vec::with_capacity(INITCAPSIZE);
    let result = vm_match(code, subj_bytes, init_pos, &mut captures);

    match result {
        None => {
            l.push_value(LuaValue::nil())?;
            Ok(1)
        }
        Some(end_pos) => {
            // Process captures
            let n = getcaptures(l, subj_bytes, end_pos, &captures, &ktable, &extra_args)?;
            Ok(n)
        }
    }
}

/// lpeg.C(p) — simple capture
pub(crate) fn lp_simplecapture(l: &mut LuaState) -> LuaResult<usize> {
    let p1 = getpatt(l, 0)?;
    let result = capture_aux(&p1, CapKind::Csimple, None);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cs(p) — substitution capture
pub(crate) fn lp_substcapture(l: &mut LuaState) -> LuaResult<usize> {
    let p1 = getpatt(l, 0)?;
    let result = capture_aux(&p1, CapKind::Csubst, None);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Ct(p) — table capture
pub(crate) fn lp_tablecapture(l: &mut LuaState) -> LuaResult<usize> {
    let p1 = getpatt(l, 0)?;
    let result = capture_aux(&p1, CapKind::Ctable, None);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cg(p [, name]) — group capture
pub(crate) fn lp_groupcapture(l: &mut LuaState) -> LuaResult<usize> {
    let p1 = getpatt(l, 0)?;
    let args = l.arg_slice();

    let label = if args.len() > 1 && !args[1].is_nil() {
        Some(args[1].clone())
    } else {
        None
    };
    let result = capture_aux(&p1, CapKind::Cgroup, label);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cf(p, f) — fold capture
pub(crate) fn lp_foldcapture(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if args.len() < 2 || !args[1].is_function() {
        return Err(l.error("function expected as 2nd argument to Cf".to_string()));
    }
    let func = args[1].clone();
    let p1 = getpatt(l, 0)?;
    let result = capture_aux(&p1, CapKind::Cfold, Some(func));
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cmt(p, f) — match-time capture
pub(crate) fn lp_matchtime(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if args.len() < 2 || !args[1].is_function() {
        return Err(l.error("function expected as 2nd argument to Cmt".to_string()));
    }
    let func = args[1].clone();
    let p1 = getpatt(l, 0)?;
    let s1 = p1.tree.len();
    let mut tree = Vec::with_capacity(1 + s1);
    let rt = TTree::new(TTag::TRunTime);
    tree.push(rt);
    tree.extend_from_slice(&p1.tree);
    let mut result = Pattern::new(tree);
    result.ktable = p1.ktable.clone();
    result.ktable.push(func);
    result.tree[0].key = result.ktable.len() as u16;
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cb(name) — back reference capture
pub(crate) fn lp_backref(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if args.is_empty() {
        return Err(l.error("value expected".to_string()));
    }
    let name = args[0].clone();
    let mut tree = vec![TTree::new(TTag::TCapture), TTree::new(TTag::TTrue)];
    tree[0].cap = CapKind::Cbackref as u8;
    let mut result = Pattern::new(tree);
    result.ktable.push(name);
    result.tree[0].key = result.ktable.len() as u16;
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Carg(n) — argument capture
pub(crate) fn lp_argcapture(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let n = args
        .first()
        .and_then(|v| v.as_integer())
        .ok_or_else(|| l.error("number expected".to_string()))? as i32;
    if n < 1 {
        return Err(l.error("invalid argument index".to_string()));
    }
    let mut tree = vec![TTree::new(TTag::TCapture), TTree::new(TTag::TTrue)];
    tree[0].cap = CapKind::Carg as u8;
    tree[0].key = n as u16;
    let result = Pattern::new(tree);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cp() — position capture
pub(crate) fn lp_poscapture(l: &mut LuaState) -> LuaResult<usize> {
    let mut tree = vec![TTree::new(TTag::TCapture), TTree::new(TTag::TTrue)];
    tree[0].cap = CapKind::Cposition as u8;
    let result = Pattern::new(tree);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.Cc(...) — constant capture
pub(crate) fn lp_constcapture(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let n = args.len();
    if n == 0 {
        let result = newleaf(TTag::TTrue);
        let val = create_pattern(l, result)?;
        l.push_value(val)?;
        return Ok(1);
    }
    if n == 1 {
        let constant = args[0].clone();
        let mut tree = vec![TTree::new(TTag::TCapture), TTree::new(TTag::TTrue)];
        tree[0].cap = CapKind::Cconst as u8;
        let mut result = Pattern::new(tree);
        if !constant.is_nil() {
            result.ktable.push(constant);
            result.tree[0].key = result.ktable.len() as u16;
        }
        let val = create_pattern(l, result)?;
        l.push_value(val)?;
        return Ok(1);
    }
    // Multiple values: group of const captures
    let mut tree = Vec::with_capacity(1 + 3 * (n - 1) + 2);
    let mut grp = TTree::new(TTag::TCapture);
    grp.cap = CapKind::Cgroup as u8;
    grp.key = 0;
    tree.push(grp);
    // Build sequence of const captures
    for _i in 0..n - 1 {
        let mut seq = TTree::new(TTag::TSeq);
        seq.ps = 3;
        tree.push(seq);
        let mut cap = TTree::new(TTag::TCapture);
        cap.cap = CapKind::Cconst as u8;
        tree.push(cap);
        tree.push(TTree::new(TTag::TTrue));
    }
    // Last const capture (no seq wrapper)
    let mut cap = TTree::new(TTag::TCapture);
    cap.cap = CapKind::Cconst as u8;
    tree.push(cap);
    tree.push(TTree::new(TTag::TTrue));

    let mut result = Pattern::new(tree);
    // Add each constant value to ktable
    let arg_values: Vec<LuaValue> = args.to_vec();
    for (i, v) in arg_values.iter().enumerate() {
        if !v.is_nil() {
            result.ktable.push(v.clone());
            let key = result.ktable.len() as u16;
            // Find the cap node for this constant
            if i < n - 1 {
                // In the sequence: group → seq → cap → true → seq → cap → true → ...
                // Cap at position: 1 + i*3 + 1 = 2 + i*3
                result.tree[2 + i * 3].key = key;
            } else {
                // Last cap: at position 1 + (n-1)*3
                result.tree[1 + (n - 1) * 3].key = key;
            }
        }
    }
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

// ============================================================
// Other API functions: S, R, utfR, B, V, locale, type, setmax
// ============================================================

/// lpeg.S(chars) — character set
pub(crate) fn lp_set(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let s = match args.first().and_then(|v| v.as_str()) {
        Some(s) => s,
        None => return Err(l.error("string expected".to_string())),
    };
    let mut cs = [0u8; CHARSETSIZE];
    for &b in s.as_bytes() {
        setchar(&mut cs, b);
    }
    let result = newcharset_pat(&cs);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.R(r1, r2, ...) — character ranges
pub(crate) fn lp_range(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let mut cs = [0u8; CHARSETSIZE];
    for arg in args.iter() {
        let s = match arg.as_str() {
            Some(s) => s,
            None => return Err(l.error("string expected".to_string())),
        };
        let bytes = s.as_bytes();
        if bytes.len() != 2 {
            return Err(l.error("range must have two characters".to_string()));
        }
        for c in bytes[0]..=bytes[1] {
            setchar(&mut cs, c);
        }
    }
    let result = newcharset_pat(&cs);
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.utfR(from, to) — UTF-8 codepoint range
pub(crate) fn lp_utfr(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let from = match args.first().and_then(|v| v.as_integer()) {
        Some(v) => v as u32,
        None => return Err(l.error("integer expected".to_string())),
    };

    let to = match args.get(1).and_then(|v| v.as_integer()) {
        Some(v) => v as u32,
        None => return Err(l.error("integer expected".to_string())),
    };
    if from > to {
        return Err(l.error("empty range".to_string()));
    }
    if to <= 0x7f {
        // ASCII range → regular charset
        let mut cs = [0u8; CHARSETSIZE];
        for c in from..=to {
            setchar(&mut cs, c as u8);
        }
        let result = newcharset_pat(&cs);
        let val = create_pattern(l, result)?;
        l.push_value(val)?;
    } else {
        // Multi-byte UTF-8 range
        let (from_len, from_fb) = utf_info(from);
        let (to_len, to_fb) = utf_info(to);
        let mut tree = vec![TTree::new(TTag::TUTFR), TTree::new(TTag::TXInfo)];
        tree[0].n = from as i32;
        tree[0].cap = from_len;
        tree[0].key = from_fb as u16;
        tree[1].n = to as i32;
        tree[1].cap = to_len;
        tree[1].key = to_fb as u16;
        let result = Pattern::new(tree);
        let val = create_pattern(l, result)?;
        l.push_value(val)?;
    }
    Ok(1)
}

fn utf_info(cp: u32) -> (u8, u8) {
    if cp <= 0x7f {
        (1, cp as u8)
    } else if cp <= 0x7ff {
        (2, (0xC0 | (cp >> 6)) as u8)
    } else if cp <= 0xffff {
        (3, (0xE0 | (cp >> 12)) as u8)
    } else {
        (4, (0xF0 | (cp >> 18)) as u8)
    }
}

/// lpeg.B(p) — look-behind
pub(crate) fn lp_behind(l: &mut LuaState) -> LuaResult<usize> {
    let p1 = getpatt(l, 0)?;
    let n = fixedlen(&p1.tree, 0);
    if n < 0 {
        return Err(l.error("pattern may not have fixed length".to_string()));
    }
    if hascaptures(&p1.tree, 0) {
        return Err(l.error("pattern have captures".to_string()));
    }
    if n > MAXBEHIND as i32 {
        return Err(l.error("pattern too long to look behind".to_string()));
    }
    let mut result = newroot1sib(TTag::TBehind, &p1);
    result.tree[0].n = n;
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.V(name) — non-terminal (rule reference for grammars)
#[allow(non_snake_case)]
pub(crate) fn lp_V(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if args.is_empty() || args[0].is_nil() {
        return Err(l.error("non-nil value expected".to_string()));
    }
    let name = args[0].clone();
    let tree = vec![TTree::new(TTag::TOpenCall)];
    let mut result = Pattern::new(tree);
    result.ktable.push(name);
    result.tree[0].key = result.ktable.len() as u16;
    let val = create_pattern(l, result)?;
    l.push_value(val)?;
    Ok(1)
}

/// lpeg.type(v) — returns "pattern" or nil
pub(crate) fn lp_type(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    if !args.is_empty() && is_pattern(&args[0]) {
        let s = l.create_string("pattern")?;
        l.push_value(s)?;
    } else {
        l.push_value(LuaValue::nil())?;
    }
    Ok(1)
}

/// lpeg.setmaxstack(n)
pub(crate) fn lp_setmax(_l: &mut LuaState) -> LuaResult<usize> {
    // In our implementation, stack is dynamic, but we accept the call
    Ok(0)
}

/// lpeg.locale([table]) — add locale character class patterns
pub(crate) fn lp_locale(l: &mut LuaState) -> LuaResult<usize> {
    let args = l.arg_slice();
    let table = if args.is_empty() || args[0].is_nil() {
        l.create_table(0, 12)?
    } else {
        if !args[0].is_table() {
            return Err(l.error("table expected".to_string()));
        }
        args[0].clone()
    };

    let cats: &[(&str, fn(u8) -> bool)] = &[
        ("alnum", |c| (c as char).is_ascii_alphanumeric()),
        ("alpha", |c| (c as char).is_ascii_alphabetic()),
        ("cntrl", |c| (c as char).is_ascii_control()),
        ("digit", |c| (c as char).is_ascii_digit()),
        ("graph", |c| c > 0x20 && c < 0x7f),
        ("lower", |c| (c as char).is_ascii_lowercase()),
        ("print", |c| c >= 0x20 && c < 0x7f),
        ("punct", |c| (c as char).is_ascii_punctuation()),
        ("space", |c| (c as char).is_ascii_whitespace()),
        ("upper", |c| (c as char).is_ascii_uppercase()),
        ("xdigit", |c| (c as char).is_ascii_hexdigit()),
    ];

    for &(name, pred) in cats {
        let mut cs = [0u8; CHARSETSIZE];
        for c in 0u16..=255 {
            if pred(c as u8) {
                setchar(&mut cs, c as u8);
            }
        }
        let pat = newcharset_pat(&cs);
        let pat_val = create_pattern(l, pat)?;
        let key = l.create_string(name)?;
        l.raw_set(&table, key, pat_val);
    }

    l.push_value(table)?;
    Ok(1)
}

#[allow(non_snake_case)]
pub(crate) fn lp_P(l: &mut LuaState) -> LuaResult<usize> {
    let p = getpatt(l, 0)?;
    let val = create_pattern(l, p)?;
    l.push_value(val)?;
    Ok(1)
}

// ============================================================
// Helper: extract Pattern from a LuaValue
// ============================================================

fn get_pattern(val: &LuaValue) -> Option<&Pattern> {
    val.as_userdata_mut()
        .and_then(|ud| ud.downcast_ref::<Pattern>())
}

fn get_pattern_mut(val: &LuaValue) -> Option<&mut Pattern> {
    val.as_userdata_mut()
        .and_then(|ud| ud.downcast_mut::<Pattern>())
}

fn is_pattern(val: &LuaValue) -> bool {
    val.as_userdata_mut()
        .and_then(|ud| ud.downcast_ref::<Pattern>())
        .is_some()
}

fn create_pattern(l: &mut LuaState, p: Pattern) -> LuaResult<LuaValue> {
    l.create_userdata(LuaUserdata::new(p))
}

fn newleaf(tag: TTag) -> Pattern {
    Pattern::new(vec![TTree::new(tag)])
}

/// Create a charset pattern from a 256-bit bitmap
fn newcharset_pat(cs: &Charset) -> Pattern {
    let mut info = CharsetInfo {
        cs: Vec::new(),
        offset: 0,
        size: 0,
        deflt: 0,
    };
    let op = charsettype(cs, &mut info);
    match op {
        Opcode::IFail => newleaf(TTag::TFalse),
        Opcode::IAny => newleaf(TTag::TAny),
        Opcode::IChar => {
            let mut t = TTree::new(TTag::TChar);
            t.n = info.offset as i32;
            Pattern::new(vec![t])
        }
        Opcode::ISet => {
            let mut t = TTree::new(TTag::TSet);
            t.set = Some(CompactSet {
                offset: info.offset as u8,
                size: info.size as u8,
                deflt: info.deflt,
                bitmap: info.cs.clone(),
            });
            Pattern::new(vec![t])
        }
        _ => newleaf(TTag::TFalse),
    }
}

/// Numbers as patterns: 0→true, n>0→n×any, n<0→not(|n|×any)
fn numtree(n: i32) -> Pattern {
    if n == 0 {
        return newleaf(TTag::TTrue);
    }
    let abs_n = n.unsigned_abs() as usize;
    if n > 0 {
        let mut tree = Vec::with_capacity(2 * abs_n - 1);
        for _i in 0..abs_n - 1 {
            let mut seq = TTree::new(TTag::TSeq);
            seq.ps = 2;
            tree.push(seq);
            tree.push(TTree::new(TTag::TAny));
        }
        tree.push(TTree::new(TTag::TAny));
        Pattern::new(tree)
    } else {
        let mut tree = Vec::with_capacity(2 * abs_n);
        let not = TTree::new(TTag::TNot);
        tree.push(not);
        for _i in 0..abs_n - 1 {
            let mut seq = TTree::new(TTag::TSeq);
            seq.ps = 2;
            tree.push(seq);
            tree.push(TTree::new(TTag::TAny));
        }
        tree.push(TTree::new(TTag::TAny));
        Pattern::new(tree)
    }
}

/// Build a pattern for a string literal: sequence of TChar nodes
fn string_pattern(s: &[u8]) -> Pattern {
    if s.is_empty() {
        return newleaf(TTag::TTrue);
    }
    let n = s.len();
    let mut tree = Vec::with_capacity(2 * n - 1);
    for i in 0..n - 1 {
        let mut seq = TTree::new(TTag::TSeq);
        seq.ps = 2;
        tree.push(seq);
        let mut ch = TTree::new(TTag::TChar);
        ch.n = s[i] as i32;
        tree.push(ch);
    }
    let mut ch = TTree::new(TTag::TChar);
    ch.n = s[n - 1] as i32;
    tree.push(ch);
    Pattern::new(tree)
}

// ============================================================
// getpatt: convert a Lua value into a Pattern
// ============================================================

/// Convert a Lua value to a Pattern. Returns Ok(Pattern) or Err.
/// Mirrors lptree.c getpatt.
fn getpatt(l: &mut LuaState, idx: usize) -> Result<Pattern, LuaError> {
    let args = l.arg_slice();
    if idx >= args.len() {
        return Err(l.error("pattern expected".to_string()));
    }
    let val = args[idx].clone();
    if is_pattern(&val) {
        let p = get_pattern(&val).unwrap();
        return Ok(p.clone());
    }
    match val.kind() {
        LuaValueKind::String => {
            let s = val.as_str().unwrap();
            Ok(string_pattern(s.as_bytes()))
        }
        LuaValueKind::Integer => {
            let n = val.as_integer().unwrap() as i32;
            Ok(numtree(n))
        }
        LuaValueKind::Boolean => {
            if val.as_boolean().unwrap() {
                Ok(newleaf(TTag::TTrue))
            } else {
                Ok(newleaf(TTag::TFalse))
            }
        }
        LuaValueKind::Table => {
            // Grammar
            newgrammar(l, idx)
        }
        LuaValueKind::Function => {
            // Function → runtime capture
            let tree = vec![TTree::new(TTag::TRunTime), TTree::new(TTag::TTrue)];
            let mut p = Pattern::new(tree);
            p.ktable.push(val.clone());
            p.tree[0].key = p.ktable.len() as u16;
            Ok(p)
        }
        _ => Err(l.error(format!("pattern expected, got {}", val.type_name()))),
    }
}

// ============================================================
// ktable merging: when combining two patterns, merge their ktables
// ============================================================

/// Correct ktable keys in tree nodes: add `n` to each key > 0
fn correctkeys(tree: &mut [TTree], idx: usize, n: u16) {
    if n == 0 {
        return;
    }
    correctkeys_inner(tree, idx, n);
}

fn correctkeys_inner(tree: &mut [TTree], idx: usize, n: u16) {
    if idx >= tree.len() {
        return;
    }
    match tree[idx].tag {
        TTag::TOpenCall | TTag::TCall | TTag::TRunTime | TTag::TRule => {
            if tree[idx].key > 0 {
                tree[idx].key += n;
            }
        }
        TTag::TCapture => {
            if tree[idx].key > 0
                && tree[idx].cap != CapKind::Carg as u8
                && tree[idx].cap != CapKind::Cnum as u8
            {
                tree[idx].key += n;
            }
        }
        _ => {}
    }
    let nsib = NUM_SIBLINGS[tree[idx].tag as usize];
    match nsib {
        1 => correctkeys_inner(tree, sib1(idx), n),
        2 => {
            correctkeys_inner(tree, sib1(idx), n);
            let s2 = sib2(tree, idx);
            correctkeys_inner(tree, s2, n);
        }
        _ => {}
    }
}

/// Join ktables from two patterns into a new pattern, adjusting keys.
/// `p` is the target pattern, `p2_tree_start` is where p2's tree starts in p.tree,
/// `p2_ktable` is p2's ktable.
fn joinktables(p: &mut Pattern, p2_tree_start: usize, p2_ktable: &[LuaValue]) {
    let n1 = p.ktable.len() as u16;
    if n1 == 0 && p2_ktable.is_empty() {
        return;
    }
    if p2_ktable.is_empty() {
        return;
    }
    if n1 == 0 {
        p.ktable = p2_ktable.to_vec();
        return;
    }
    // Merge: append p2_ktable to p.ktable, then correct keys in p2's subtree
    let offset = n1;
    p.ktable.extend_from_slice(p2_ktable);
    correctkeys(&mut p.tree, p2_tree_start, offset);
}

/// Merge another pattern's ktable into target pattern, correcting keys
/// in the subtree starting at `subtree_start`.
// ============================================================
// newroot1sib / newroot2sib: build pattern with 1 or 2 children
// ============================================================

/// New pattern: root(tag) with p1 as child. Copies p1's ktable.
fn newroot1sib(tag: TTag, p1: &Pattern) -> Pattern {
    let s1 = p1.tree.len();
    let mut tree = Vec::with_capacity(1 + s1);
    tree.push(TTree::new(tag));
    tree.extend_from_slice(&p1.tree);
    let mut result = Pattern::new(tree);
    result.ktable = p1.ktable.clone();
    result
}

/// New pattern: root(tag) with p1 and p2 as children. Merges ktables.
fn newroot2sib(tag: TTag, p1: &Pattern, p2: &Pattern) -> Pattern {
    let s1 = p1.tree.len();
    let s2 = p2.tree.len();
    let mut tree = Vec::with_capacity(1 + s1 + s2);
    let mut root = TTree::new(tag);
    root.ps = 1 + s1 as i32;
    tree.push(root);
    tree.extend_from_slice(&p1.tree);
    tree.extend_from_slice(&p2.tree);
    let mut result = Pattern::new(tree);
    result.ktable = p1.ktable.clone();
    let p2_tree_start = 1 + s1;
    joinktables(&mut result, p2_tree_start, &p2.ktable);
    result
}

/// Build sequence helper: place sib into a Seq node and return where sib2 goes
// ============================================================
// Lua API functions: lp_P, lp_match
// ============================================================

/// Get initial position for match (handles negative indices)
fn initposition(l: &LuaState, len: usize) -> usize {
    let args = l.arg_slice();
    let ii = if args.len() > 2 {
        args[2].as_integer().unwrap_or(1)
    } else {
        1
    };
    if ii > 0 {
        let ii = ii as usize;
        if ii <= len { ii - 1 } else { len }
    } else {
        let neg = (-ii) as usize;
        if neg <= len { len - neg } else { 0 }
    }
}

// ============================================================
// finalfix: resolve TOpenCall and correct associativity
// ============================================================

fn finalfix(tree: &mut Vec<TTree>, grammar: Option<&[(LuaValue, usize)]>, idx: usize) {
    if idx >= tree.len() {
        return;
    }
    match tree[idx].tag {
        TTag::TGrammar => return, // subgrammars already fixed
        TTag::TOpenCall => {
            // Should have been resolved during grammar construction
            // If we get here outside a grammar, it's an error
        }
        TTag::TSeq | TTag::TChoice => {
            // correctassociativity handled at construction time
        }
        _ => {}
    }
    let nsib = NUM_SIBLINGS[tree[idx].tag as usize];
    match nsib {
        1 => finalfix(tree, grammar, sib1(idx)),
        2 => {
            finalfix(tree, grammar, sib1(idx));
            let s2 = sib2(tree, idx);
            finalfix(tree, grammar, s2);
        }
        _ => {}
    }
}

/// Helper: create a capture node wrapping p1's body with optional label value
fn capture_aux(p1: &Pattern, cap: CapKind, label: Option<LuaValue>) -> Pattern {
    let s1 = p1.tree.len();
    let mut tree = Vec::with_capacity(1 + s1);
    let mut capnode = TTree::new(TTag::TCapture);
    capnode.cap = cap as u8;
    tree.push(capnode);
    tree.extend_from_slice(&p1.tree);
    let mut result = Pattern::new(tree);
    result.ktable = p1.ktable.clone();
    if let Some(lv) = label {
        if !lv.is_nil() {
            result.ktable.push(lv);
            result.tree[0].key = result.ktable.len() as u16;
        }
    }
    result
}

// ============================================================
// Grammar construction
// ============================================================

fn newgrammar(l: &mut LuaState, arg_idx: usize) -> Result<Pattern, luars::lua_vm::LuaError> {
    let args = l.arg_slice();
    let gram_table = args[arg_idx].clone();
    if !gram_table.is_table() {
        return Err(l.error("table expected for grammar".to_string()));
    }

    // Collect rules: first get initial rule
    // grammar[1] is either the initial rule name (string) or the initial rule (pattern)
    let first_val = l.raw_geti(&gram_table, 1);
    let (initial_key, initial_rule) = match first_val {
        Some(ref v) if v.is_string() => {
            // It's the name of the initial rule
            let name = v.clone();
            let rule = l
                .raw_get(&gram_table, &name)
                .ok_or_else(|| l.error("grammar has no initial rule".to_string()))?;
            (name, rule)
        }
        Some(v) => {
            // It IS the initial rule
            (LuaValue::integer(1), v)
        }
        None => {
            return Err(l.error("grammar has no initial rule".to_string()));
        }
    };

    if !is_pattern(&initial_rule) {
        return Err(l.error("initial rule is not a pattern".to_string()));
    }

    // Collect all rules: iterate over the table
    let pairs = gram_table
        .as_table()
        .ok_or_else(|| l.error("table expected".to_string()))?
        .iter_all();
    let mut rules: Vec<(LuaValue, Pattern)> = Vec::new();

    // Add initial rule first
    rules.push((
        initial_key.clone(),
        get_pattern(&initial_rule).unwrap().clone(),
    ));

    for (k, v) in &pairs {
        // Skip the initial rule (already added) and index 1 if it was a name
        if k.is_integer() && k.as_integer() == Some(1) {
            continue;
        }
        // Check if this is the same as initial_key
        if let (Some(ks), Some(iks)) = (k.as_str(), initial_key.as_str()) {
            if ks == iks {
                continue;
            }
        }
        if let (Some(ki), Some(iki)) = (k.as_integer(), initial_key.as_integer()) {
            if ki == iki {
                continue;
            }
        }
        if !is_pattern(v) {
            let name = k
                .as_str()
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("{:?}", k));
            return Err(l.error(format!("rule '{}' is not a pattern", name)));
        }
        rules.push((k.clone(), get_pattern(v).unwrap().clone()));
    }

    let n = rules.len();
    if n > MAXRULES {
        return Err(l.error("grammar has too many rules".to_string()));
    }

    // Build position table: map rule name → rule index
    let mut postable: Vec<(LuaValue, usize)> = Vec::new();
    for (i, (key, _)) in rules.iter().enumerate() {
        postable.push((key.clone(), i));
    }

    // Build grammar tree:
    // TGrammar → TRule → TXInfo → rule_body → TRule → TXInfo → rule_body → ... → TTrue
    let mut grammar_tree = Vec::new();
    let mut grammar_ktable: Vec<LuaValue> = Vec::new();

    // TGrammar node
    let mut gnode = TTree::new(TTag::TGrammar);
    gnode.n = n as i32;
    grammar_tree.push(gnode);

    // For each rule, add TRule → TXInfo → body
    let mut rule_positions: Vec<usize> = Vec::new();
    for (i, (key, rule_pat)) in rules.iter().enumerate() {
        let rule_start = grammar_tree.len();
        rule_positions.push(rule_start);

        let body_size = rule_pat.tree.len();
        let mut rule_node = TTree::new(TTag::TRule);
        rule_node.key = 0; // will be set when rule is referenced
        rule_node.ps = body_size as i32 + 2; // skip TXInfo + body to next rule
        grammar_tree.push(rule_node);

        let mut xinfo = TTree::new(TTag::TXInfo);
        xinfo.n = i as i32;
        grammar_tree.push(xinfo);

        let body_start = grammar_tree.len();
        grammar_tree.extend_from_slice(&rule_pat.tree);

        // Merge ktable
        let _offset = grammar_ktable.len();
        if !rule_pat.ktable.is_empty() {
            let old_len = grammar_ktable.len() as u16;
            grammar_ktable.extend_from_slice(&rule_pat.ktable);
            if old_len > 0 {
                correctkeys(&mut grammar_tree, body_start, old_len);
            }
        }

        // Add rule name to ktable for error messages
        grammar_ktable.push(key.clone());
    }
    // End with TTrue
    grammar_tree.push(TTree::new(TTag::TTrue));

    // Fix open calls: resolve TOpenCall → TCall
    for idx in 0..grammar_tree.len() {
        if grammar_tree[idx].tag == TTag::TOpenCall {
            let key_idx = grammar_tree[idx].key as usize;
            if key_idx == 0 || key_idx > grammar_ktable.len() {
                continue;
            }
            let rule_name = &grammar_ktable[key_idx - 1];
            // Find rule position
            let mut found = false;
            for (ri, (rkey, _)) in rules.iter().enumerate() {
                let matches = match (rule_name.as_str(), rkey.as_str()) {
                    (Some(a), Some(b)) => a == b,
                    _ => match (rule_name.as_integer(), rkey.as_integer()) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    },
                };
                if matches {
                    grammar_tree[idx].tag = TTag::TCall;
                    let rule_pos = rule_positions[ri];
                    grammar_tree[idx].ps = rule_pos as i32 - idx as i32;
                    // Set rule's key so it's marked as "used"
                    grammar_tree[rule_pos].key = grammar_tree[idx].key;
                    found = true;
                    break;
                }
            }
            if !found {
                let name = rule_name
                    .as_str()
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("{:?}", rule_name));
                return Err(l.error(format!("rule '{}' undefined in given grammar", name)));
            }
        }
    }

    // Set initial grammar name if not referenced
    if grammar_tree.len() > 1 && grammar_tree[1].key == 0 {
        grammar_ktable.push(initial_key);
        grammar_tree[1].key = grammar_ktable.len() as u16;
    }

    // Verify: check for left recursion and empty loops
    verify_grammar(&grammar_tree, &grammar_ktable, l)?;

    let mut result = Pattern::new(grammar_tree);
    result.ktable = grammar_ktable;
    Ok(result)
}

fn verify_grammar(
    tree: &[TTree],
    ktable: &[LuaValue],
    l: &mut LuaState,
) -> Result<(), luars::lua_vm::LuaError> {
    // Check left recursion for each rule
    let mut rule_idx = sib1(0); // first rule
    while rule_idx < tree.len() && tree[rule_idx].tag == TTag::TRule {
        if tree[rule_idx].key != 0 {
            // used rule
            let body = sib1(sib1(rule_idx)); // skip TXInfo
            let mut passed = Vec::new();
            if !verifyrule(tree, body, &mut passed) {
                // Check for left recursion
                if has_duplicate(&passed) {
                    let name = if tree[rule_idx].key > 0 {
                        ktable
                            .get(tree[rule_idx].key as usize - 1)
                            .and_then(|v| v.as_str())
                            .unwrap_or("?")
                    } else {
                        "?"
                    };
                    return Err(l.error(format!("rule '{}' may be left recursive", name)));
                }
            }
            // Check infinite loops
            if checkloops(tree, body) {
                let name = if tree[rule_idx].key > 0 {
                    ktable
                        .get(tree[rule_idx].key as usize - 1)
                        .and_then(|v| v.as_str())
                        .unwrap_or("?")
                } else {
                    "?"
                };
                return Err(l.error(format!("empty loop in rule '{}'", name)));
            }
        }
        rule_idx = sib2(tree, rule_idx);
    }
    Ok(())
}

fn has_duplicate(v: &[u16]) -> bool {
    for i in 0..v.len() {
        for j in 0..i {
            if v[i] == v[j] {
                return true;
            }
        }
    }
    false
}

/// Returns true if pattern is nullable (for left-recursion check)
fn verifyrule(tree: &[TTree], idx: usize, passed: &mut Vec<u16>) -> bool {
    if idx >= tree.len() {
        return true;
    }
    match tree[idx].tag {
        TTag::TChar | TTag::TSet | TTag::TAny | TTag::TFalse | TTag::TUTFR => false,
        TTag::TTrue | TTag::TBehind => true,
        TTag::TNot | TTag::TAnd | TTag::TRep => verifyrule(tree, sib1(idx), passed),
        TTag::TCapture | TTag::TRunTime | TTag::TXInfo => verifyrule(tree, sib1(idx), passed),
        TTag::TCall => verifyrule(tree, sib2(tree, idx), passed),
        TTag::TSeq => {
            if !verifyrule(tree, sib1(idx), passed) {
                false
            } else {
                verifyrule(tree, sib2(tree, idx), passed)
            }
        }
        TTag::TChoice => {
            let a = verifyrule(tree, sib1(idx), passed);
            let b = verifyrule(tree, sib2(tree, idx), passed);
            a || b
        }
        TTag::TRule => {
            if passed.len() >= MAXRULES {
                return false;
            }
            passed.push(tree[idx].key);
            verifyrule(tree, sib1(idx), passed)
        }
        TTag::TGrammar => nullable(&tree, idx),
        TTag::TOpenCall => false,
    }
}

fn checkloops(tree: &[TTree], idx: usize) -> bool {
    if idx >= tree.len() {
        return false;
    }
    if tree[idx].tag == TTag::TRep && nullable(&tree, sib1(idx)) {
        return true;
    }
    if tree[idx].tag == TTag::TGrammar {
        return false;
    }
    let nsib = NUM_SIBLINGS[tree[idx].tag as usize];
    match nsib {
        1 => checkloops(tree, sib1(idx)),
        2 => checkloops(tree, sib1(idx)) || checkloops(tree, sib2(tree, idx)),
        _ => false,
    }
}

// ============================================================
// GC Anchor: protects LuaValues from garbage collection
// ============================================================
//
// LuaValues stored only in Rust variables (Vec, locals) are invisible to Lua's
// mark-and-sweep GC.  If a Lua function call triggers a GC cycle while we hold
// such values, the underlying objects (strings, tables, closures) may be freed,
// leaving dangling pointers.
//
// We solve this by creating a Lua table ("anchor") on the stack at the start
// of capture processing.  Every GC-managed LuaValue we need to keep alive is
// inserted into this table via raw_seti (which never triggers GC).  Because
// the table itself sits on the Lua stack, the GC marks it and transitively
// marks everything inside.

/// A table on the Lua stack that keeps GC values alive during capture processing.
struct GcAnchor {
    table: LuaValue,
    count: i64,
}

impl GcAnchor {
    /// Create a new anchor table and push it onto the Lua stack.
    fn new(l: &mut LuaState, initial_capacity: usize) -> LuaResult<Self> {
        let table = l.create_table(initial_capacity, 0)?;
        l.push_value(table)?;
        Ok(GcAnchor { table, count: 0 })
    }

    /// Register a LuaValue so the GC will not collect it.
    /// Only needed for GC-managed types (strings, tables, functions, userdata).
    /// Integers, floats, booleans, and nil are value types and need no anchoring.
    #[inline]
    fn anchor(&mut self, l: &mut LuaState, val: LuaValue) {
        if val.is_nil() || val.is_boolean() || val.is_integer() || val.is_float() {
            return;
        }
        self.count += 1;
        l.raw_seti(&self.table, self.count, val);
    }

    /// Anchor all values in a slice.
    fn anchor_all(&mut self, l: &mut LuaState, vals: &[LuaValue]) {
        for v in vals {
            self.anchor(l, *v);
        }
    }
}

/// Main entry point: process all captures and push results onto Lua stack
fn getcaptures(
    l: &mut LuaState,
    subject: &[u8],
    end_pos: usize,
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
) -> LuaResult<usize> {
    if captures.is_empty() || captures[0].is_close() {
        // No captures: return end position
        l.push_value(LuaValue::integer(end_pos as i64 + 1))?;
        return Ok(1);
    }

    // Create a GC anchor: a Lua table on the stack that keeps all referenced
    // GC objects alive for the duration of capture processing.
    let saved_top = l.get_top();
    let mut anchor = GcAnchor::new(l, ktable.len() + 16)?;

    // Anchor all ktable values (functions, tables, format strings, etc.)
    // These are stored in Pattern.ktable which is invisible to GC.
    anchor.anchor_all(l, ktable);

    // Process captures
    let results = getcaptures_direct(
        l,
        subject,
        captures,
        ktable,
        extra_args,
        &mut 0,
        0,
        &mut anchor,
    )?;

    // Restore the stack (remove anchor table) before pushing results.
    // Between set_top and push_value no GC can trigger (no VM execution).
    l.set_top(saved_top)?;

    if results.is_empty() {
        l.push_value(LuaValue::integer(end_pos as i64 + 1))?;
        return Ok(1);
    }
    let n = results.len();
    for v in results {
        l.push_value(v)?;
    }
    Ok(n)
}

/// Direct capture processing - returns collected values
fn getcaptures_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let mut results = Vec::new();
    while *pos < captures.len() && !captures[*pos].is_close() {
        let mut vals = pushcapture_direct(
            l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
        )?;
        // Anchor results so they survive GC triggered by subsequent iterations
        anchor.anchor_all(l, &vals);
        results.append(&mut vals);
    }
    Ok(results)
}

// ============================================================
// Direct capture helpers (no CapState, uses pos: &mut usize)
// ============================================================

/// Get value from ktable by 1-based index
fn ktable_get(ktable: &[LuaValue], idx: u16) -> LuaValue {
    if idx == 0 || idx as usize > ktable.len() {
        LuaValue::nil()
    } else {
        ktable[idx as usize - 1].clone()
    }
}

/// Skip to next capture at the same nesting level (direct version)
fn nextcap_direct(captures: &[Capture], pos: &mut usize) {
    if captures[*pos].is_open() {
        let mut n = 0u32;
        loop {
            *pos += 1;
            if *pos >= captures.len() {
                return;
            }
            if captures[*pos].is_open() {
                n += 1;
            } else if captures[*pos].is_close() {
                if n == 0 {
                    break;
                }
                n -= 1;
            }
        }
        *pos += 1; // skip the close
    } else {
        let start = *pos;
        *pos += 1;
        while *pos < captures.len() && captures[start].cap_inside(&captures[*pos]) {
            *pos += 1;
        }
    }
}

/// Get the close-size of a capture (distance from open to close index)
fn closesize_direct(captures: &[Capture], head_pos: usize, cur_pos: usize) -> u32 {
    captures[head_pos].cap_size(&captures[cur_pos])
}

/// Find open capture corresponding to a close (searching backwards)
fn findopen_direct(captures: &[Capture], close_pos: usize) -> usize {
    let mut n = 0u32;
    let mut p = close_pos;
    loop {
        p -= 1;
        if captures[p].is_close() {
            n += 1;
        } else if captures[p].is_open() {
            if n == 0 {
                return p;
            }
            n -= 1;
        }
    }
}

/// Push all nested values inside current capture.
/// If `addextra` or no nested values found, push the whole match string.
/// Returns collected values.
fn pushnestedvalues_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
    addextra: bool,
) -> LuaResult<Vec<LuaValue>> {
    let head_pos = *pos;
    let head_index = captures[head_pos].index as usize;
    *pos += 1; // move past head
    let mut results = Vec::new();
    while *pos < captures.len() && captures[head_pos].cap_inside(&captures[*pos]) {
        let mut vals = pushcapture_direct(
            l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
        )?;
        // Anchor results so they survive GC triggered by subsequent iterations
        anchor.anchor_all(l, &vals);
        results.append(&mut vals);
    }
    if addextra || results.is_empty() {
        // Push whole match string
        let size = closesize_direct(captures, head_pos, *pos) as usize;
        let end = (head_index + size).min(subject.len());
        let s = String::from_utf8_lossy(&subject[head_index..end]).to_string();
        let str_val = l.create_string_owned(s)?;
        anchor.anchor(l, str_val);
        results.push(str_val);
    }
    // Skip close if head was open
    if captures[head_pos].is_open() && *pos < captures.len() && captures[*pos].is_close() {
        *pos += 1;
    }
    Ok(results)
}

/// Push only the first nested value
fn pushonenestedvalue_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<LuaValue> {
    let vals = pushnestedvalues_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor, false,
    )?;
    Ok(vals.into_iter().next().unwrap_or(LuaValue::nil()))
}

/// Main direct capture processing - returns captured values as Vec.
fn pushcapture_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    if reclevel > MAXRECLEVEL {
        return Err(l.error("subcapture nesting too deep".to_string()));
    }
    let cap = &captures[*pos];
    match cap.kind {
        CapKind::Cposition => {
            let p = cap.index as i64 + 1;
            *pos += 1;
            Ok(vec![LuaValue::integer(p)])
        }
        CapKind::Cconst => {
            let val = ktable_get(ktable, cap.idx);
            *pos += 1;
            Ok(vec![val])
        }
        CapKind::Carg => {
            let arg_idx = cap.idx as usize;
            *pos += 1;
            if arg_idx == 0 || arg_idx > extra_args.len() {
                return Err(l.error(format!("reference to absent extra argument #{}", arg_idx)));
            }
            Ok(vec![extra_args[arg_idx - 1].clone()])
        }
        CapKind::Csimple => {
            let mut vals = pushnestedvalues_direct(
                l,
                subject,
                captures,
                ktable,
                extra_args,
                pos,
                reclevel + 1,
                anchor,
                true,
            )?;
            // Rotate: whole match (last pushed) should be first
            if vals.len() > 1 {
                let last = vals.pop().unwrap();
                vals.insert(0, last);
            }
            Ok(vals)
        }
        CapKind::Cruntime => {
            let _idx = cap.idx;
            *pos += 1;
            // Runtime capture values are stored elsewhere; for now return nil
            // TODO: integrate with VM runtime capture storage
            Ok(vec![LuaValue::nil()])
        }
        CapKind::Cgroup => {
            if cap.idx == 0 {
                // Anonymous group: push all nested values
                pushnestedvalues_direct(
                    l,
                    subject,
                    captures,
                    ktable,
                    extra_args,
                    pos,
                    reclevel + 1,
                    anchor,
                    false,
                )
            } else {
                // Named group: skip, produce no values
                nextcap_direct(captures, pos);
                Ok(vec![])
            }
        }
        CapKind::Cbackref => backrefcap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Ctable => tablecap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cfunction => functioncap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cacc => acccap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cnum => numcap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cquery => querycap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cstring => stringcap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Csubst => substcap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        CapKind::Cfold => foldcap_direct(
            l,
            subject,
            captures,
            ktable,
            extra_args,
            pos,
            reclevel + 1,
            anchor,
        ),
        _ => {
            *pos += 1;
            Ok(vec![])
        }
    }
}

/// Compare two LuaValues for equality (by identity or string/integer comparison)
fn values_equal(a: &LuaValue, b: &LuaValue) -> bool {
    if a.is_nil() && b.is_nil() {
        return true;
    }
    match (a.as_str(), b.as_str()) {
        (Some(sa), Some(sb)) => return sa == sb,
        _ => {}
    }
    match (a.as_integer(), b.as_integer()) {
        (Some(ia), Some(ib)) => return ia == ib,
        _ => {}
    }
    false
}

/// Back-reference capture (direct)
fn backrefcap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let curr_pos = *pos;
    let name = ktable_get(ktable, captures[curr_pos].idx);
    // Search backwards for matching named group
    let mut p = curr_pos;
    let mut found = None;
    while p > 0 {
        p -= 1;
        let cap = &captures[p];
        if cap.is_close() {
            p = findopen_direct(captures, p);
            continue;
        }
        if cap.cap_inside(&captures[curr_pos]) {
            continue;
        }
        if cap.kind == CapKind::Cgroup {
            let cap_name = ktable_get(ktable, cap.idx);
            if values_equal(&name, &cap_name) {
                found = Some(p);
                break;
            }
        }
    }
    match found {
        Some(back_pos) => {
            let mut bp = back_pos;
            let vals = pushnestedvalues_direct(
                l, subject, captures, ktable, extra_args, &mut bp, reclevel, anchor, false,
            )?;
            *pos = curr_pos + 1;
            Ok(vals)
        }
        None => Err(l.error("back reference not found".to_string())),
    }
}

/// Table capture (direct): create Lua table from nested captures
fn tablecap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let head_pos = *pos;
    *pos += 1;
    let table = l.create_table(0, 0)?;
    anchor.anchor(l, table); // Protect table from GC during nested captures
    let mut n = 0i64;
    while *pos < captures.len() && captures[head_pos].cap_inside(&captures[*pos]) {
        if captures[*pos].kind == CapKind::Cgroup && captures[*pos].idx != 0 {
            // Named group: set as table field
            let name = ktable_get(ktable, captures[*pos].idx);
            let val = pushonenestedvalue_direct(
                l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
            )?;
            l.raw_set(&table, name, val); // raw_set to avoid __newindex triggering GC
        } else {
            let vals = pushcapture_direct(
                l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
            )?;
            for val in vals {
                n += 1;
                l.raw_seti(&table, n, val); // raw_seti to avoid GC
            }
        }
    }
    // Skip close
    if captures[head_pos].is_open() && *pos < captures.len() && captures[*pos].is_close() {
        *pos += 1;
    }
    Ok(vec![table])
}

/// Function capture (direct): call function with nested capture values
fn functioncap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let func = ktable_get(ktable, captures[*pos].idx);
    let args = pushnestedvalues_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor, false,
    )?;
    let results = l.call_function(func, args)?;
    Ok(results)
}

/// Accumulator capture (direct): func(prev_value, nested...)
fn acccap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let func = ktable_get(ktable, captures[*pos].idx);
    // Accumulator capture: not yet supported (requires external state)
    // For now, just get nested values and call function with them
    let nested = pushnestedvalues_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor, false,
    )?;
    let results = l.call_function(func, nested)?;
    Ok(vec![results.into_iter().next().unwrap_or(LuaValue::nil())])
}

/// Number (select) capture (direct)
fn numcap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let idx = captures[*pos].idx as usize;
    if idx == 0 {
        nextcap_direct(captures, pos);
        return Ok(vec![]);
    }
    let vals = pushnestedvalues_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor, false,
    )?;
    if vals.len() < idx {
        return Err(l.error(format!("no capture '{}'", idx)));
    }
    Ok(vec![vals[idx - 1].clone()])
}

/// Query capture (direct): lookup nested value in a table
fn querycap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let table_val = ktable_get(ktable, captures[*pos].idx);
    let key = pushonenestedvalue_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
    )?;
    if let Some(result) = l.table_get(&table_val, &key)? {
        if !result.is_nil() {
            return Ok(vec![result]);
        }
    }
    Ok(vec![])
}

/// String capture (direct): format string with %0-%9 references
fn stringcap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let fmt_val = ktable_get(ktable, captures[*pos].idx);
    let fmt = fmt_val.as_str().unwrap_or("").to_string();
    let head_pos = *pos;
    let head_index = captures[head_pos].index as usize;
    *pos += 1;

    // Collect nested capture strings
    let mut nested: Vec<String> = Vec::new();
    while *pos < captures.len() && captures[head_pos].cap_inside(&captures[*pos]) {
        let vals = pushcapture_direct(
            l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
        )?;
        if let Some(val) = vals.into_iter().next() {
            nested.push(val.as_str().unwrap_or("").to_string());
        }
    }

    let size = closesize_direct(captures, head_pos, *pos) as usize;
    let end = (head_index + size).min(subject.len());
    let whole_match = String::from_utf8_lossy(&subject[head_index..end]).to_string();

    // Skip close
    if captures[head_pos].is_open() && *pos < captures.len() && captures[*pos].is_close() {
        *pos += 1;
    }

    // Process format string: %0=whole, %1-%9=nested capture values
    let mut result = String::new();
    let fb = fmt.as_bytes();
    let mut i = 0;
    while i < fb.len() {
        if fb[i] == b'%' && i + 1 < fb.len() {
            i += 1;
            if fb[i] >= b'0' && fb[i] <= b'9' {
                let idx = (fb[i] - b'0') as usize;
                if idx == 0 {
                    result.push_str(&whole_match);
                } else if idx <= nested.len() {
                    result.push_str(&nested[idx - 1]);
                }
            } else {
                result.push(fb[i] as char);
            }
        } else {
            result.push(fb[i] as char);
        }
        i += 1;
    }
    Ok(vec![l.create_string_owned(result)?])
}

/// Substitution capture (direct): replace matched parts with capture values
fn substcap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let head_pos = *pos;
    let head_index = captures[head_pos].index as usize;
    *pos += 1;
    let mut result = String::new();
    let mut curr = head_index;

    while *pos < captures.len() && captures[head_pos].cap_inside(&captures[*pos]) {
        let cap_start = captures[*pos].index as usize;
        // Add text before this capture
        if cap_start > curr && cap_start <= subject.len() {
            result.push_str(&String::from_utf8_lossy(&subject[curr..cap_start]));
        }
        let inner_start = *pos;
        let vals = pushcapture_direct(
            l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
        )?;
        if let Some(val) = vals.into_iter().next() {
            if let Some(s) = val.as_str() {
                result.push_str(s);
            }
            // Advance curr past the captured region
            let inner_end_idx = if *pos > 0 {
                captures[(*pos).min(captures.len() - 1)].index as usize
            } else {
                cap_start
            };
            let cap = &captures[inner_start];
            if cap.siz > 0 {
                curr = cap_start + (cap.siz as usize - 1);
            } else {
                curr = inner_end_idx;
            }
        } else {
            curr = cap_start;
        }
    }

    // Add remaining text
    let size = closesize_direct(captures, head_pos, *pos) as usize;
    let end = (head_index + size).min(subject.len());
    if curr < end {
        result.push_str(&String::from_utf8_lossy(&subject[curr..end]));
    }
    // Skip close
    if captures[head_pos].is_open() && *pos < captures.len() && captures[*pos].is_close() {
        *pos += 1;
    }
    Ok(vec![l.create_string_owned(result)?])
}

/// Fold capture (direct): fold nested captures with a function
fn foldcap_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
    anchor: &mut GcAnchor,
) -> LuaResult<Vec<LuaValue>> {
    let head_pos = *pos;
    let func = ktable_get(ktable, captures[head_pos].idx);
    *pos += 1;

    // Get first value (initial accumulator)
    if *pos >= captures.len() || captures[*pos].is_close() {
        return Err(l.error("no initial value for fold capture".to_string()));
    }
    let init_vals = pushcapture_direct(
        l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
    )?;
    if init_vals.is_empty() {
        return Err(l.error("no initial value for fold capture".to_string()));
    }
    let mut acc = init_vals.into_iter().next().unwrap();
    anchor.anchor(l, acc); // Protect accumulator from GC

    // For each remaining nested capture, apply func(acc, val...)
    while *pos < captures.len() && captures[head_pos].cap_inside(&captures[*pos]) {
        let nested = pushcapture_direct(
            l, subject, captures, ktable, extra_args, pos, reclevel, anchor,
        )?;
        let mut args = Vec::with_capacity(1 + nested.len());
        args.push(acc);
        args.extend(nested);
        let results = l.call_function(func.clone(), args)?;
        acc = results.into_iter().next().unwrap_or(LuaValue::nil());
        anchor.anchor(l, acc); // Protect new accumulator value
    }

    // Skip close
    if captures[head_pos].is_open() && *pos < captures.len() && captures[*pos].is_close() {
        *pos += 1;
    }
    Ok(vec![acc])
}
