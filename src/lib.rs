mod cap;
mod charset;
mod code;
mod tests;
mod tree;
mod types;
mod vm;

pub use cap::Pattern;

use luars::lib_registry::LibraryModule;

/// Create the lpeg library module for registration with a luars VM.
///
/// Usage:
/// ```no_run
/// use luars::LibraryRegistry;
/// use luars_lpeg::create_lpeg_lib;
/// let mut registry = LibraryRegistry::new();
/// registry.register(create_lpeg_lib());
/// ```
pub fn create_lpeg_lib() -> LibraryModule {
    luars::lib_module!("lpeg", {
        "match" => cap::lp_match,
        "B" => cap::lp_behind,
        "V" => cap::lp_V,
        "C" => cap::lp_simplecapture,
        "Cc" => cap::lp_constcapture,
        "Cmt" => cap::lp_matchtime,
        "Cb" => cap::lp_backref,
        "Carg" => cap::lp_argcapture,
        "Cp" => cap::lp_poscapture,
        "Cs" => cap::lp_substcapture,
        "Ct" => cap::lp_tablecapture,
        "Cf" => cap::lp_foldcapture,
        "Cg" => cap::lp_groupcapture,
        "P" => cap::lp_P,
        "S" => cap::lp_set,
        "R" => cap::lp_range,
        "utfR" => cap::lp_utfr,
        "locale" => cap::lp_locale,
        "setmaxstack" => cap::lp_setmax,
        "type" => cap::lp_type,
    })
}
