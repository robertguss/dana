//! Zero-crate build script linking the allowlisted system C libraries (`zlib`, `libzstd`,
//! `sqlite3`, and `openssl`) behind the isolated `src/ffi/` boundary.

use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=PKG_CONFIG_PATH");
    println!("cargo:rerun-if-env-changed=HOMEBREW_PREFIX");

    link_system_lib(
        "zlib",
        &["z"],
        None,
        "/usr/include/zlib.h",
        "zlib1g-dev / zlib",
    );
    link_system_lib(
        "libzstd",
        &["zstd"],
        Some("zstd"),
        "/usr/include/zstd.h",
        "libzstd-dev / zstd",
    );
    link_system_lib(
        "sqlite3",
        &["sqlite3"],
        None,
        "/usr/include/sqlite3.h",
        "libsqlite3-dev / sqlite3",
    );
    link_system_lib(
        "openssl",
        &["ssl", "crypto"],
        Some("openssl@3"),
        "/usr/include/openssl/ssl.h",
        "libssl-dev / openssl",
    );
}

fn find_homebrew_lib_dir(formula: &str) -> Option<PathBuf> {
    if let Some(prefix) = std::env::var_os("HOMEBREW_PREFIX") {
        let candidate = PathBuf::from(prefix).join("opt").join(formula).join("lib");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    for prefix in ["/opt/homebrew", "/usr/local"] {
        let candidate = Path::new(prefix).join("opt").join(formula).join("lib");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    None
}

fn link_system_lib(
    pkg_name: &str,
    fallback_libs: &[&str],
    homebrew_formula: Option<&str>,
    header_hint: &str,
    install_pkg: &str,
) {
    if let Ok(out) = Command::new("pkg-config")
        .args(["--libs", pkg_name])
        .output()
        && out.status.success()
    {
        let stdout = String::from_utf8_lossy(&out.stdout);
        let mut emitted = false;
        for token in stdout.split_whitespace() {
            if let Some(dir) = token.strip_prefix("-L") {
                println!("cargo:rustc-link-search=native={dir}");
            } else if let Some(lib) = token.strip_prefix("-l") {
                println!("cargo:rustc-link-lib={lib}");
                emitted = true;
            }
        }
        if emitted {
            return;
        }
    }

    let is_macos = std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos");
    let mut found_homebrew = false;
    if is_macos
        && let Some(formula) = homebrew_formula
        && let Some(lib_dir) = find_homebrew_lib_dir(formula)
    {
        println!("cargo:rustc-link-search=native={}", lib_dir.display());
        found_homebrew = true;
    }

    if !(is_macos && (homebrew_formula.is_none() || found_homebrew))
        && !Path::new(header_hint).exists()
    {
        println!(
            "cargo:warning=Could not locate `{pkg_name}` via pkg-config or `{header_hint}`; \
             install `{install_pkg}` if linking fails."
        );
    }
    for lib in fallback_libs {
        println!("cargo:rustc-link-lib={lib}");
    }
}
