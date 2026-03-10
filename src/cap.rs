// ============================================================
// Capture processing: getcaptures / pushcapture
// ============================================================

use luars::{
    LuaResult, LuaState, LuaUserData, LuaUserdata, LuaValue, impl_simple_userdata, lua_vm::LuaError,
};

use crate::types::{CapKind, Capture, MAXRECLEVEL};

/// Capture evaluation state
struct CapState<'a> {
    l: &'a mut LuaState,
    captures: &'a [Capture],
    pos: usize, // current position in captures
    subject: &'a [u8],
    ktable: &'a [LuaValue],
    extra_args: &'a [LuaValue],
    reclevel: usize,
    /// Values accumulated during capture processing
    values: Vec<LuaValue>,
    /// Runtime capture values (from Cmt)
    runtime_values: &'a [LuaValue],
}

impl<'a> CapState<'a> {
    pub fn new(
        l: &'a mut LuaState,
        captures: &'a [Capture],
        subject: &'a [u8],
        ktable: &'a [LuaValue],
        extra_args: &'a [LuaValue],
        runtime_values: &'a [LuaValue],
    ) -> Self {
        CapState {
            l,
            captures,
            pos: 0,
            subject,
            ktable,
            extra_args,
            reclevel: 0,
            values: Vec::new(),
            runtime_values,
        }
    }

    fn cap(&self) -> &Capture {
        &self.captures[self.pos]
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn from_ktable(&self, idx: u16) -> LuaValue {
        if idx == 0 || idx as usize > self.ktable.len() {
            LuaValue::nil()
        } else {
            self.ktable[idx as usize - 1].clone()
        }
    }
}

/// Skip close capture if head was an open capture
fn skipclose(cs: &mut CapState) {
    if cs.cap().is_open() {
        debug_assert!(cs.captures[cs.pos].is_close());
        cs.advance();
    }
}

/// Go to next capture at same level
fn nextcap(cs: &mut CapState) {
    let cap = cs.cap();
    if cap.is_open() {
        let mut n = 0u32;
        loop {
            cs.advance();
            if cs.cap().is_open() {
                n += 1;
            } else if cs.cap().is_close() {
                if n == 0 {
                    break;
                }
                n -= 1;
            }
        }
        cs.advance(); // skip the close
    } else {
        let start = cs.pos;
        cs.advance();
        while cs.pos < cs.captures.len() && cs.captures[start].cap_inside(&cs.captures[cs.pos]) {
            cs.advance();
        }
    }
}

/// Get size of current capture (using corresponding close if open)
fn closesize(cs: &CapState, head_pos: usize) -> u32 {
    let head = &cs.captures[head_pos];
    head.cap_size(cs.cap())
}

/// Push all nested values; if addextra or no nested values, push the full match
fn pushnestedvalues(cs: &mut CapState, addextra: bool) -> LuaResult<usize> {
    let head_pos = cs.pos;
    let head_index = cs.captures[head_pos].index;
    cs.advance();
    let mut n = 0usize;
    while cs.pos < cs.captures.len() && cs.captures[head_pos].cap_inside(cs.cap()) {
        n += pushcapture(cs)?;
    }
    if addextra || n == 0 {
        let size = closesize(cs, head_pos) as usize;
        let start = head_index as usize;
        let end = (start + size).min(cs.subject.len());
        let s = String::from_utf8_lossy(&cs.subject[start..end]).to_string();
        let s = cs.l.create_string_owned(s)?;
        cs.values.push(s);
        n += 1;
    }
    // Skip close if head was open
    if cs.captures[head_pos].is_open() {
        debug_assert!(cs.pos < cs.captures.len() && cs.captures[cs.pos].is_close());
        cs.advance();
    }
    Ok(n)
}

/// Push only first nested value
fn pushonenestedvalue(cs: &mut CapState) -> LuaResult<()> {
    let before = cs.values.len();
    let n = pushnestedvalues(cs, false)?;
    if n > 1 {
        // Remove extra values, keep only the first
        cs.values.truncate(before + 1);
    }
    Ok(())
}

/// Find open capture corresponding to a close at current position
fn findopen(captures: &[Capture], close_pos: usize) -> usize {
    let mut n = 0u32;
    let mut pos = close_pos;
    loop {
        pos -= 1;
        if captures[pos].is_close() {
            n += 1;
        } else if captures[pos].is_open() {
            if n == 0 {
                return pos;
            }
            n -= 1;
        }
    }
}

/// Find named back reference
fn findback<'a>(cs: &CapState<'a>, ref_pos: usize) -> Option<usize> {
    let ref_cap = &cs.captures[ref_pos];
    let name = cs.from_ktable(ref_cap.idx);
    let mut pos = ref_pos;
    while pos > 0 {
        pos -= 1;
        let cap = &cs.captures[pos];
        if cap.is_close() {
            pos = findopen(cs.captures, pos);
            continue;
        }
        if cap.cap_inside(ref_cap) {
            continue;
        }
        if cap.kind == CapKind::Cgroup {
            let cap_name = cs.from_ktable(cap.idx);
            if values_equal(&name, &cap_name) {
                return Some(pos);
            }
        }
    }
    None
}

fn values_equal(a: &LuaValue, b: &LuaValue) -> bool {
    if a.is_nil() && b.is_nil() {
        return true;
    }
    if let (Some(sa), Some(sb)) = (a.as_str(), b.as_str()) {
        return sa == sb;
    }
    if let (Some(ia), Some(ib)) = (a.as_integer(), b.as_integer()) {
        return ia == ib;
    }
    false
}

/// Main capture evaluation function
fn pushcapture(cs: &mut CapState) -> LuaResult<usize> {
    if cs.reclevel > MAXRECLEVEL {
        return Ok(0); // avoid stack overflow
    }
    cs.reclevel += 1;
    let res = match cs.cap().kind {
        CapKind::Cposition => {
            let pos = cs.cap().index as i64 + 1;
            cs.values.push(LuaValue::integer(pos));
            cs.advance();
            1
        }
        CapKind::Cconst => {
            let val = cs.from_ktable(cs.cap().idx);
            cs.values.push(val);
            cs.advance();
            1
        }
        CapKind::Carg => {
            let arg_idx = cs.cap().idx as usize;
            cs.advance();
            if arg_idx == 0 || arg_idx > cs.extra_args.len() {
                return Err(cs
                    .l
                    .error(format!("reference to absent extra argument #{}", arg_idx)));
            }
            cs.values.push(cs.extra_args[arg_idx - 1].clone());
            1
        }
        CapKind::Csimple => {
            let before = cs.values.len();
            let k = pushnestedvalues(cs, true)?;
            // Rotate: make whole match first result
            if k > 1 {
                let vals: Vec<LuaValue> = cs.values.drain(before..).collect();
                // Last pushed is the whole match, move it to front
                let last = vals.last().unwrap().clone();
                cs.values.push(last);
                for v in &vals[..vals.len() - 1] {
                    cs.values.push(v.clone());
                }
            }
            k
        }
        CapKind::Cruntime => {
            let cap = cs.cap().clone();
            cs.advance();
            // Runtime captures have their value stored by the VM
            // The idx field points to the Lua stack position
            if (cap.idx as usize) > 0 && (cap.idx as usize) <= cs.runtime_values.len() {
                cs.values
                    .push(cs.runtime_values[cap.idx as usize - 1].clone());
            } else {
                cs.values.push(LuaValue::nil());
            }
            1
        }
        CapKind::Cgroup => {
            if cs.cap().idx == 0 {
                // Anonymous group: push all nested values
                pushnestedvalues(cs, false)?
            } else {
                // Named group: skip, produce no values here
                nextcap(cs);
                0
            }
        }
        CapKind::Cbackref => {
            let curr_pos = cs.pos;
            let found = findback(cs, curr_pos);
            match found {
                Some(back_pos) => {
                    let saved_pos = cs.pos;
                    cs.pos = back_pos;
                    let n = pushnestedvalues(cs, false)?;
                    cs.pos = saved_pos;
                    cs.advance(); // skip backref cap
                    n
                }
                None => {
                    return Err(cs.l.error("back reference not found".to_string()));
                }
            }
        }
        CapKind::Ctable => tablecap(cs)?,
        CapKind::Cfunction => functioncap(cs)?,
        CapKind::Cacc => acccap(cs)?,
        CapKind::Cnum => numcap(cs)?,
        CapKind::Cquery => querycap(cs)?,
        CapKind::Cstring => stringcap(cs)?,
        CapKind::Csubst => substcap(cs)?,
        CapKind::Cfold => foldcap(cs)?,
        _ => {
            cs.advance();
            0
        }
    };
    cs.reclevel -= 1;
    Ok(res)
}

/// Table capture: create table from nested captures
fn tablecap(cs: &mut CapState) -> LuaResult<usize> {
    let head_pos = cs.pos;
    cs.advance();
    let mut arr: Vec<LuaValue> = Vec::new();
    let mut hash: Vec<(LuaValue, LuaValue)> = Vec::new();
    let mut n = 0i64;
    while cs.pos < cs.captures.len() && cs.captures[head_pos].cap_inside(cs.cap()) {
        if cs.cap().kind == CapKind::Cgroup && cs.cap().idx != 0 {
            // Named group: set as table field
            let name = cs.from_ktable(cs.cap().idx);
            let before = cs.values.len();
            pushonenestedvalue(cs)?;
            if cs.values.len() > before {
                let val = cs.values.pop().unwrap();
                hash.push((name, val));
            }
        } else {
            let before = cs.values.len();
            let k = pushcapture(cs)?;
            for _ in 0..k {
                if cs.values.len() > before {
                    n += 1;
                    let val = cs.values.pop().unwrap();
                    arr.push(val);
                }
            }
        }
    }
    // Skip close if head was open
    if cs.captures[head_pos].is_open()
        && cs.pos < cs.captures.len()
        && cs.captures[cs.pos].is_close()
    {
        cs.advance();
    }
    // We can't create a real Lua table here since we don't have LuaState.
    // Store as a special marker: we'll handle this in getcaptures.
    // For now, store the table data as a special LuaValue.
    // Actually, we need to return a table LuaValue. We'll store a placeholder
    // and create the table later in getcaptures where we have LuaState access.
    // Use a Vec of (key, value) pairs stored in a wrapper.
    let table_data = cs.l.create_table(arr.len(), hash.len())?;
    for (i, v) in arr.into_iter().enumerate() {
        cs.l.table_seti(&table_data, (i + 1) as i64, v)?;
    }

    for (k, v) in hash {
        cs.l.table_set(&table_data, k, v)?;
    }

    cs.values.push(table_data);
    Ok(1)
}

/// Function capture: call function with nested captures
fn functioncap(cs: &mut CapState) -> LuaResult<usize> {
    let func = cs.from_ktable(cs.cap().idx);
    let before = cs.values.len();
    let n = pushnestedvalues(cs, false)?;
    // Collect the nested values
    let nested: Vec<LuaValue> = cs.values.drain(before..).collect();
    // Store a deferred function call marker
    let call = DeferredCall::Function { func, args: nested };
    let u = cs.l.create_userdata(LuaUserdata::new(call))?;
    cs.values.push(u);
    Ok(1)
}

/// Accumulator capture: call function(prev_value, nested...)
fn acccap(cs: &mut CapState) -> LuaResult<usize> {
    let func = cs.from_ktable(cs.cap().idx);
    let before = cs.values.len();
    // Previous value should be on the value stack
    let prev = if before > 0 {
        cs.values.pop().unwrap()
    } else {
        return Err(cs
            .l
            .error("no previous value for accumulator capture".to_string()));
    };
    let n = pushnestedvalues(cs, false)?;
    let nested: Vec<LuaValue> = cs.values.drain(cs.values.len() - n..).collect();
    let mut args = vec![prev];
    args.extend(nested);
    let call = DeferredCall::Function { func, args };
    let u = cs.l.create_userdata(LuaUserdata::new(call))?;
    cs.values.push(u);
    Ok(0) // accumulator replaces existing value
}

/// Number (select) capture
fn numcap(cs: &mut CapState) -> LuaResult<usize> {
    let idx = cs.cap().idx as usize;
    if idx == 0 {
        nextcap(cs);
        return Ok(0);
    }
    let before = cs.values.len();
    let n = pushnestedvalues(cs, false)?;
    if n < idx {
        return Err(cs.l.error(format!("no capture '{}'", idx)));
    }
    // Keep only the idx-th value
    let vals: Vec<LuaValue> = cs.values.drain(before..).collect();
    cs.values.push(vals[idx - 1].clone());
    Ok(1)
}

/// Query (table) capture: lookup nested value in table
fn querycap(cs: &mut CapState) -> LuaResult<usize> {
    let table_val = cs.from_ktable(cs.cap().idx);
    pushonenestedvalue(cs)?;
    let key = cs.values.pop().unwrap_or(LuaValue::nil());
    // Store deferred query call
    let call = DeferredCall::Query {
        table: table_val,
        key,
    };
    let u = cs.l.create_userdata(LuaUserdata::new(call))?;
    cs.values.push(u);
    Ok(1)
}

/// String capture: format string with %0-%9 capture references
fn stringcap(cs: &mut CapState) -> LuaResult<usize> {
    let fmt_val = cs.from_ktable(cs.cap().idx);
    let fmt = fmt_val.as_str().unwrap_or("").to_string();

    // Collect nested captures
    let head_pos = cs.pos;
    cs.advance();
    let mut nested_strings: Vec<String> = Vec::new();
    // %0 = whole match
    let head_index = cs.captures[head_pos].index as usize;

    while cs.pos < cs.captures.len() && cs.captures[head_pos].cap_inside(cs.cap()) {
        if cs.cap().kind == CapKind::Csimple {
            // Get the string match for this simple capture
            let cap_start = cs.cap().index as usize;
            let before = cs.values.len();
            pushnestedvalues(cs, true)?;
            // The last value pushed should be the match string
            if cs.values.len() > before {
                let val = cs.values.drain(before..).next().unwrap();
                let s = val.as_str().unwrap_or("").to_string();
                nested_strings.push(s);
            }
        } else {
            let before = cs.values.len();
            pushcapture(cs)?;
            if cs.values.len() > before {
                let val = cs.values.drain(before..).next().unwrap();
                let s = val.as_str().unwrap_or("").to_string();
                nested_strings.push(s);
            }
        }
    }

    let size = closesize(cs, head_pos) as usize;
    let end = (head_index + size).min(cs.subject.len());
    let whole_match = String::from_utf8_lossy(&cs.subject[head_index..end]).to_string();

    // Skip close
    if cs.captures[head_pos].is_open()
        && cs.pos < cs.captures.len()
        && cs.captures[cs.pos].is_close()
    {
        cs.advance();
    }

    // Process format string
    let mut result = String::new();
    let fmt_bytes = fmt.as_bytes();
    let mut i = 0;
    while i < fmt_bytes.len() {
        if fmt_bytes[i] == b'%' && i + 1 < fmt_bytes.len() {
            i += 1;
            if fmt_bytes[i] >= b'0' && fmt_bytes[i] <= b'9' {
                let idx = (fmt_bytes[i] - b'0') as usize;
                if idx == 0 {
                    result.push_str(&whole_match);
                } else if idx <= nested_strings.len() {
                    result.push_str(&nested_strings[idx - 1]);
                }
            } else {
                result.push(fmt_bytes[i] as char);
            }
        } else {
            result.push(fmt_bytes[i] as char);
        }
        i += 1;
    }

    let s = cs.l.create_string_owned(result)?;
    cs.values.push(s);
    Ok(1)
}

/// Substitution capture
fn substcap(cs: &mut CapState) -> LuaResult<usize> {
    let head_pos = cs.pos;
    let head_index = cs.captures[head_pos].index as usize;
    cs.advance();
    let mut result = String::new();
    let mut curr = head_index;

    while cs.pos < cs.captures.len() && cs.captures[head_pos].cap_inside(cs.cap()) {
        let cap_start = cs.cap().index as usize;
        // Add text before this capture
        if cap_start > curr && cap_start <= cs.subject.len() {
            result.push_str(&String::from_utf8_lossy(&cs.subject[curr..cap_start]));
        }
        let before = cs.values.len();
        let n = pushcapture(cs)?;
        if n > 0 && cs.values.len() > before {
            let val = cs.values.drain(before..).next().unwrap();
            if let Some(s) = val.as_str() {
                result.push_str(s);
                // Update curr to skip captured region
                let close_pos = if cs.captures[head_pos].is_open() {
                    cs.pos.saturating_sub(1)
                } else {
                    cs.pos.saturating_sub(1)
                };
                curr = cap_start
                    + cs.captures[close_pos.min(cs.captures.len() - 1)]
                        .index
                        .saturating_sub(cs.captures[head_pos].index) as usize;
                continue;
            }
        }
        curr = cap_start;
    }

    // Add remaining text
    let size = closesize(cs, head_pos) as usize;
    let end = (head_index + size).min(cs.subject.len());
    if curr < end {
        result.push_str(&String::from_utf8_lossy(&cs.subject[curr..end]));
    }

    // Skip close
    if cs.captures[head_pos].is_open()
        && cs.pos < cs.captures.len()
        && cs.captures[cs.pos].is_close()
    {
        cs.advance();
    }

    let s = cs.l.create_string_owned(result)?;
    cs.values.push(s);
    Ok(1)
}

/// Fold capture
fn foldcap(cs: &mut CapState) -> LuaResult<usize> {
    let head_pos = cs.pos;
    let func = cs.from_ktable(cs.cap().idx);
    cs.advance();

    // Get first value (initial accumulator)
    if cs.pos >= cs.captures.len() || cs.captures[cs.pos].is_close() {
        return Err(cs.l.error("no initial value for fold capture".to_string()));
    }
    let before = cs.values.len();
    let n = pushcapture(cs)?;
    if n == 0 {
        return Err(cs.l.error("no initial value for fold capture".to_string()));
    }
    // Keep only first value as accumulator
    if n > 1 {
        cs.values.truncate(before + 1);
    }

    // For remaining nested captures, create fold calls
    while cs.pos < cs.captures.len() && cs.captures[head_pos].cap_inside(cs.cap()) {
        let acc = cs.values.pop().unwrap();
        let before2 = cs.values.len();
        let k = pushcapture(cs)?;
        let nested: Vec<LuaValue> = cs.values.drain(before2..).collect();
        let mut args = vec![acc];
        args.extend(nested);
        let call = DeferredCall::Fold {
            func: func.clone(),
            args,
        };
        let u = cs.l.create_userdata(LuaUserdata::new(call))?;
        cs.values.push(u);
    }

    // Skip close
    if cs.captures[head_pos].is_open()
        && cs.pos < cs.captures.len()
        && cs.captures[cs.pos].is_close()
    {
        cs.advance();
    }
    Ok(1)
}

/// Deferred function/query calls — resolved in getcaptures with LuaState access
enum DeferredCall {
    Function { func: LuaValue, args: Vec<LuaValue> },
    Query { table: LuaValue, key: LuaValue },
    Fold { func: LuaValue, args: Vec<LuaValue> },
}

impl_simple_userdata!(DeferredCall, "DeferredCall");

/// Resolve deferred calls: evaluate any Box<dyn Any> values that contain DeferredCall/TableData
fn resolve_value(l: &mut LuaState, val: LuaValue) -> LuaResult<Vec<LuaValue>> {
    // Check if this is a boxed Any (TableData or DeferredCall)
    // LuaValue doesn't directly support Box<dyn Any>, so we need a different approach.
    // Actually, LuaValue::from(Box<dyn Any>) doesn't exist in luars.
    // We need to rethink this approach entirely - can't store arbitrary Rust objects in LuaValue.
    // Instead, we should process captures with LuaState access from the start.
    Ok(vec![val])
}

/// Main entry point: process all captures and push results onto Lua stack
pub fn getcaptures(
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

    // Process captures directly with LuaState access
    let n = getcaptures_direct(l, subject, captures, ktable, extra_args, &mut 0, 0)?;

    if n == 0 {
        l.push_value(LuaValue::integer(end_pos as i64 + 1))?;
        return Ok(1);
    }
    Ok(n)
}

/// Direct capture processing with LuaState access
fn getcaptures_direct(
    l: &mut LuaState,
    subject: &[u8],
    captures: &[Capture],
    ktable: &[LuaValue],
    extra_args: &[LuaValue],
    pos: &mut usize,
    reclevel: usize,
) -> LuaResult<usize> {
    let mut n = 0usize;
    while *pos < captures.len() && !captures[*pos].is_close() {
        n += pushcapture_direct(l, subject, captures, ktable, extra_args, pos, reclevel)?;
    }
    Ok(n)
}
