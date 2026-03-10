use luars::lua_vm::SafeOption;
use luars::{LibraryRegistry, LuaVM, Stdlib};

use crate::create_lpeg_lib;

#[allow(unused)]
fn setup_vm() -> Box<LuaVM> {
    let mut vm = LuaVM::new(SafeOption::default());
    vm.open_stdlib(Stdlib::All).unwrap();
    let mut registry = LibraryRegistry::new();
    registry.register(create_lpeg_lib());
    registry.load_all(&mut vm).unwrap();
    vm
}

#[test]
fn test_lpeg_module_loaded() {
    let mut vm = setup_vm();
    let results = vm.execute(r#"return type(lpeg)"#).unwrap();
    assert_eq!(results[0].as_str(), Some("table"));
}

#[test]
fn test_lpeg_p_literal() {
    let mut vm = setup_vm();
    // lpeg.P("hello") should match "hello world" at position 6
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P("hello"), "hello world")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(6));
}

#[test]
fn test_lpeg_p_number() {
    let mut vm = setup_vm();
    // lpeg.P(3) matches any 3 characters
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P(3), "abcdef")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(4));
}

#[test]
fn test_lpeg_p_zero() {
    let mut vm = setup_vm();
    // lpeg.P(0) always matches at position 1
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P(0), "abc")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(1));
}

#[test]
fn test_lpeg_set() {
    let mut vm = setup_vm();
    // lpeg.S("aeiou") matches a single vowel
    let results = vm
        .execute(r#"return lpeg.match(lpeg.S("aeiou"), "apple")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(2));
}

#[test]
fn test_lpeg_range() {
    let mut vm = setup_vm();
    // lpeg.R("az") matches a lowercase letter
    let results = vm
        .execute(r#"return lpeg.match(lpeg.R("az"), "hello")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(2));
}

#[test]
fn test_lpeg_capture_simple() {
    let mut vm = setup_vm();
    // lpeg.C(lpeg.P("hello")) captures the matched string
    let results = vm
        .execute(r#"return lpeg.match(lpeg.C(lpeg.P("hello")), "hello world")"#)
        .unwrap();
    assert_eq!(results[0].as_str(), Some("hello"));
}

#[test]
fn test_lpeg_capture_position() {
    let mut vm = setup_vm();
    // lpeg.Cp() captures the current position
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P("abc") * lpeg.Cp(), "abcdef")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(4));
}

#[test]
fn test_lpeg_capture_const() {
    let mut vm = setup_vm();
    // lpeg.Cc(value) produces a constant capture
    let results = vm
        .execute(r#"return lpeg.match(lpeg.Cc("yes"), "anything")"#)
        .unwrap();
    assert_eq!(results[0].as_str(), Some("yes"));
}

#[test]
fn test_lpeg_sequence() {
    let mut vm = setup_vm();
    // p1 * p2 is sequence
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P("ab") * lpeg.P("cd"), "abcdef")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(5));
}

#[test]
fn test_lpeg_choice() {
    let mut vm = setup_vm();
    // p1 + p2 matches either "xy" or "ab"
    let results = vm
        .execute(
            r#"
            local p = lpeg.P("xy") + lpeg.P("ab")
            return lpeg.match(p, "abcdef"), lpeg.match(p, "xyzzzz"), lpeg.match(p, "qqqqq")
        "#,
        )
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(3)); // matched "ab", pos 3
    assert_eq!(results[1].as_integer(), Some(3)); // matched "xy", pos 3
    assert!(results[2].is_nil()); // no match
}

#[test]
fn test_lpeg_no_match() {
    let mut vm = setup_vm();
    // Non-matching pattern returns nil
    let results = vm
        .execute(r#"return lpeg.match(lpeg.P("xyz"), "abcdef")"#)
        .unwrap();
    assert!(results[0].is_nil());
}

#[test]
fn test_lpeg_type() {
    let mut vm = setup_vm();
    let results = vm.execute(r#"return lpeg.type(lpeg.P("abc"))"#).unwrap();
    assert_eq!(results[0].as_str(), Some("pattern"));
}

#[test]
fn test_lpeg_type_non_pattern() {
    let mut vm = setup_vm();
    let results = vm.execute(r#"return lpeg.type("abc")"#).unwrap();
    assert!(results[0].is_nil());
}

#[test]
fn test_lpeg_not_predicate() {
    let mut vm = setup_vm();
    // -p succeeds if p fails, consuming no input
    let results = vm
        .execute(r#"return lpeg.match(-lpeg.P("x") * lpeg.P("a"), "abc")"#)
        .unwrap();
    assert_eq!(results[0].as_integer(), Some(2));
}

#[test]
fn test_lpeg_multiple_captures() {
    let mut vm = setup_vm();
    // Multiple captures return multiple values
    let results = vm
        .execute(r#"return lpeg.match(lpeg.C(lpeg.P(1)) * lpeg.C(lpeg.P(1)), "ab")"#)
        .unwrap();
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].as_str(), Some("a"));
    assert_eq!(results[1].as_str(), Some("b"));
}
