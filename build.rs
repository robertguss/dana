//! Zero-crate build script linking the allowlisted system C libraries (`zlib` and `libzstd`)
//! behind the isolated `src/ffi/` boundary.

use std::path::Path;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=PKG_CONFIG_PATH");

    link_system_lib("zlib", "z", "/usr/include/zlib.h", "zlib1g-dev / zlib");
    link_system_lib(
        "libzstd",
        "zstd",
        "/usr/include/zstd.h",
        "libzstd-dev / zstd",
    );
}

fn link_system_lib(pkg_name: &str, fallback_lib: &str, header_hint: &str, install_pkg: &str) {
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

    if !Path::new(header_hint).exists() {
        println!(
            "cargo:warning=Could not locate `{pkg_name}` via pkg-config or `{header_hint}`; \
             install `{install_pkg}` if linking fails."
        );
    }
    println!("cargo:rustc-link-lib={fallback_lib}");
}
