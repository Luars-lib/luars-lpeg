/// VM pattern matching engine - mirrors lpvm.c
use crate::types::*;

// ============================================================
// UTF-8 decode
// ============================================================

/// Decode one UTF-8 sequence starting at `s[pos]`.
/// Returns (new_pos, codepoint) or None if invalid.
pub fn utf8_decode(s: &[u8], pos: usize) -> Option<(usize, u32)> {
    if pos >= s.len() {
        return None;
    }
    let c = s[pos] as u32;
    if c < 0x80 {
        return Some((pos + 1, c));
    }

    let (count, mut res) = if c & 0xE0 == 0xC0 {
        (1, c & 0x1F)
    } else if c & 0xF0 == 0xE0 {
        (2, c & 0x0F)
    } else if c & 0xF8 == 0xF0 {
        (3, c & 0x07)
    } else {
        return None;
    };

    let limits: [u32; 4] = [0xFF, 0x7F, 0x7FF, 0xFFFF];

    for i in 1..=count {
        if pos + i >= s.len() {
            return None;
        }
        let cc = s[pos + i] as u32;
        if cc & 0xC0 != 0x80 {
            return None;
        }
        res = (res << 6) | (cc & 0x3F);
    }

    if count > 3 || res > 0x10FFFF || res <= limits[count] {
        return None;
    }

    Some((pos + count + 1, res))
}

// ============================================================
// The main match function
// ============================================================

/// Result of VM match: subject position after match, or None on failure.
/// `captures` is filled with captured positions.
pub fn vm_match(
    code: &[Instruction],
    subject: &[u8],
    start: usize,
    captures: &mut Vec<Capture>,
) -> Option<usize> {
    let o = 0usize; // subject origin (always 0 for slices)
    let mut s = start; // current position
    let e = subject.len(); // end of subject
    let mut p: usize = 0; // current instruction index
    let mut captop: usize = 0; // capture stack top
    let _ndyncap: usize = 0; // dynamic captures count (unused in pure impl)

    let mut stack: Vec<StackEntry> = Vec::with_capacity(INITBACK);
    // sentinel entry
    stack.push(StackEntry {
        s: Some(s),
        p: usize::MAX, // IGiveup sentinel
        caplevel: 0,
    });

    // Ensure captures has enough room
    captures.resize(INITCAPSIZE, Capture::new());

    loop {
        if p >= code.len() {
            return None;
        }

        let inst = &code[p];
        match inst.code {
            Opcode::IEnd => {
                // Add terminal close capture
                ensure_cap(captures, captop);
                captures[captop].kind = CapKind::Cclose;
                captures[captop].index = u32::MAX;
                return Some(s);
            }

            Opcode::IGiveup => {
                return None;
            }

            Opcode::IRet => {
                let frame = stack.pop().unwrap();
                assert!(frame.s.is_none()); // must be a call frame
                p = frame.p;
                continue;
            }

            Opcode::IAny => {
                if s < e {
                    p += 1;
                    s += 1;
                } else {
                    p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                }
                continue;
            }

            Opcode::IUTFR => {
                if s >= e {
                    p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                    continue;
                }
                match utf8_decode(subject, s) {
                    Some((new_s, codepoint)) => {
                        let from = inst.offset as u32;
                        let to = inst.utf_to() as u32;
                        if codepoint >= from && codepoint <= to {
                            s = new_s;
                            p += 1;
                        } else {
                            p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                        }
                    }
                    None => {
                        p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                    }
                }
                continue;
            }

            Opcode::ITestAny => {
                if s < e {
                    p += 1; // skip (offset is at p+1 in C, here stored in inst.offset)
                } else {
                    p = (p as i32 + inst.offset) as usize;
                }
                continue;
            }

            Opcode::IChar => {
                if s < e && subject[s] == inst.aux1 {
                    p += 1;
                    s += 1;
                } else {
                    p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                }
                continue;
            }

            Opcode::ITestChar => {
                if s < e && subject[s] == inst.aux1 {
                    p += 1;
                } else {
                    p = (p as i32 + inst.offset) as usize;
                }
                continue;
            }

            Opcode::ISet => {
                if s < e && inst.charinset(subject[s]) {
                    p += 1;
                    s += 1;
                } else {
                    p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                }
                continue;
            }

            Opcode::ITestSet => {
                if s < e && inst.charinset(subject[s]) {
                    p += 1;
                } else {
                    p = (p as i32 + inst.offset) as usize;
                }
                continue;
            }

            Opcode::IBehind => {
                let n = inst.aux1 as usize;
                if n > s - o {
                    p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                } else {
                    s -= n;
                    p += 1;
                }
                continue;
            }

            Opcode::ISpan => {
                while s < e && inst.charinset(subject[s]) {
                    s += 1;
                }
                p += 1;
                continue;
            }

            Opcode::IJmp => {
                p = (p as i32 + inst.offset) as usize;
                continue;
            }

            Opcode::IChoice => {
                stack.push(StackEntry {
                    s: Some(s),
                    p: (p as i32 + inst.offset) as usize,
                    caplevel: captop,
                });
                p += 1;
                continue;
            }

            Opcode::ICall => {
                stack.push(StackEntry {
                    s: None,  // call frame
                    p: p + 1, // return address
                    caplevel: 0,
                });
                p = (p as i32 + inst.offset) as usize;
                continue;
            }

            Opcode::ICommit => {
                stack.pop(); // discard choice point
                p = (p as i32 + inst.offset) as usize;
                continue;
            }

            Opcode::IPartialCommit => {
                let top = stack.last_mut().unwrap();
                top.s = Some(s);
                top.caplevel = captop;
                p = (p as i32 + inst.offset) as usize;
                continue;
            }

            Opcode::IBackCommit => {
                let frame = stack.pop().unwrap();
                s = frame.s.unwrap();
                captop = frame.caplevel;
                p = (p as i32 + inst.offset) as usize;
                continue;
            }

            Opcode::IFailTwice => {
                stack.pop(); // pop one choice point
                // fall through to IFail
                p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                continue;
            }

            Opcode::IFail => {
                p = do_fail(&mut stack, &mut s, captures, &mut captop)?;
                continue;
            }

            Opcode::ICloseRunTime => {
                // Runtime captures require Lua callback - simplified here
                // Full implementation in pattern.rs with LuaState access
                p += 1;
                continue;
            }

            Opcode::ICloseCapture => {
                assert!(captop > 0);
                // Try to turn into full capture
                if let Some(open_idx) = findopen(captures, captop, (s - o) as u32) {
                    let size = (s - o) as u32 - captures[open_idx].index + 1;
                    if size <= 255 {
                        captures[open_idx].siz = size as u8;
                        p += 1;
                        continue;
                    }
                }
                // Must create close capture entry
                ensure_cap(captures, captop);
                captures[captop].siz = 1;
                captures[captop].index = (s - o) as u32;
                captures[captop].kind = inst.getkind();
                captures[captop].idx = inst.key as u16;
                captop += 1;
                p += 1;
                continue;
            }

            Opcode::IOpenCapture => {
                ensure_cap(captures, captop);
                captures[captop].siz = 0; // open
                captures[captop].index = (s - o) as u32;
                captures[captop].kind = inst.getkind();
                captures[captop].idx = inst.key as u16;
                captop += 1;
                p += 1;
                continue;
            }

            Opcode::IFullCapture => {
                let off = inst.getoff() as u32;
                ensure_cap(captures, captop);
                captures[captop].siz = off as u8 + 1;
                captures[captop].index = (s - o) as u32 - off;
                captures[captop].kind = inst.getkind();
                captures[captop].idx = inst.key as u16;
                captop += 1;
                p += 1;
                continue;
            }

            Opcode::IOpenCall | Opcode::IEmpty => {
                // Should not appear in compiled code
                p += 1;
                continue;
            }
        }
    }
}

// ============================================================
// Helper: handle fail/backtrack
// ============================================================

/// Backtrack: pop stack until we find a choice point (s != None).
/// Returns the new instruction pointer, or None if match fails entirely.
fn do_fail(
    stack: &mut Vec<StackEntry>,
    s: &mut usize,
    _captures: &mut Vec<Capture>,
    captop: &mut usize,
) -> Option<usize> {
    loop {
        if stack.is_empty() {
            return None;
        }
        let frame = stack.pop().unwrap();
        match frame.s {
            Some(saved_s) => {
                *s = saved_s;
                *captop = frame.caplevel;
                return Some(frame.p);
            }
            None => {
                // Skip call frames
                continue;
            }
        }
    }
}

/// Find open capture before captop that can be turned into a full capture.
fn findopen(captures: &[Capture], captop: usize, curr_index: u32) -> Option<usize> {
    if captop == 0 {
        return None;
    }
    let mut i = captop - 1;

    // If last capture is not open and starts at current position, can't be full
    if !captures[i].is_open() && captures[i].index == curr_index {
        return None;
    }

    let mut checked = 0;
    loop {
        if checked >= MAXLOP {
            return None;
        }
        if curr_index.wrapping_sub(captures[i].index) >= 255 {
            return None;
        }
        if captures[i].is_open() {
            return Some(i);
        }
        if captures[i].kind == CapKind::Cclose {
            return None;
        }
        if i == 0 {
            return None;
        }
        i -= 1;
        checked += 1;
    }
}

/// Ensure captures vec has room for idx.
fn ensure_cap(captures: &mut Vec<Capture>, idx: usize) {
    while captures.len() <= idx {
        captures.push(Capture::new());
    }
}
