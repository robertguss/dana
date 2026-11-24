//! Final lowering from [`CheckedProgram`] into a verified [`ExecProgram`], with
//! automatic Core IR v0.1 extraction and `core::check_program` sanity verification
//! whenever the program stays within the Lean-verified Core IR v0.1 subset.

use crate::base::{DiagCode, Diagnostic};
use crate::check::CheckedProgram;
use crate::core::check::check_program;
use crate::core::syntax::Program as CoreProgram;
use crate::runtime::ir::ExecProgram;

/// Lowered output ready for execution (on `--oracle` or the Slice 2C vectorized VM)
/// and optional canonical `(dana-core 0.1 ...)` emission.
#[derive(Clone, Debug)]
pub struct LoweredProgram {
    pub root_name: String,
    pub exec: ExecProgram,
    /// Present when the entire lowered program lies within the Lean-verified Core IR v0.1
    /// subset and has passed `core::check_program` verification.
    pub verified_core: Option<CoreProgram>,
}

/// Lower a [`CheckedProgram`] into a [`LoweredProgram`], verifying the Core IR v0.1
/// representation via `core::check_program` whenever expressible in Core IR v0.1.
///
/// # Errors
/// Returns a [`Diagnostic`] with [`DiagCode::CoreVerifyError`] if a pure Core IR v0.1
/// lowered program fails the internal Core IR verifier (indicating a compiler lowering bug).
pub fn lower_program(checked: CheckedProgram) -> Result<LoweredProgram, Diagnostic> {
    let verified_core = match checked.exec.try_to_core_program() {
        Some(core_prog) => {
            if let Err(err) = check_program(&core_prog) {
                return Err(Diagnostic::error(
                    DiagCode::CoreVerifyError,
                    format!("internal Core IR v0.1 verification failed: {err}"),
                ));
            }
            Some(core_prog)
        }
        None => None,
    };

    Ok(LoweredProgram {
        root_name: checked.root_name,
        exec: checked.exec,
        verified_core,
    })
}
