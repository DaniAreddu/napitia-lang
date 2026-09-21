//! The boundary between raw and verified NIR.
//!
//! [`Module`] is whatever produced it says it is: `nir::lower` builds
//! one, and a test -- or any caller holding the public struct -- can
//! build another by hand, field by field, with nothing checking that
//! the result means anything at all. That is deliberate; lowering needs
//! a mutable, half-built module to work on, and the verifier needs
//! hand-built malformed ones to be worth testing.
//!
//! What must not stay deliberate is letting such a module reach an
//! executor. [`VerifiedModule`] is the one type that says a module
//! passed [`super::verify::verify_module`], and [`verify`] is the only
//! way to obtain one outside this crate's own tests: it takes the
//! module *by value*, checks that exact module, and seals it. Nothing
//! afterwards can reach inside to change it -- the field is private,
//! there is no mutable accessor, and no unsealing conversion -- so the
//! module an interpreter or the native backend receives is byte-for-
//! byte the one the verifier accepted.
//!
//! The wrapper is a claim about structure, not a substitute for runtime
//! care: the interpreter's own defence-in-depth checks (`rfcs/0015`,
//! `X0001`-`X0004`) stay exactly as they are, and remain observable
//! through the `#[cfg(test)]`-only unchecked path
//! ([`VerifiedModule::seal_unchecked`]), which the production library
//! does not compile at all.

use crate::diagnostics::Diagnostic;
use crate::hir::ItemRegistry;
use crate::source::SourceId;
use crate::symbol::Interner;

use super::Module;

/// NIR that [`verify`] accepted, and that nothing has touched since.
///
/// Read-only access to the underlying [`Module`] is intended and
/// unrestricted -- printers, the native backend and the interpreter all
/// need it. What the type withholds is every other kind of access:
/// there is no `&mut Module`, no `into_module`, and no public
/// constructor that skips verification.
#[derive(Debug)]
pub struct VerifiedModule {
    module: Module,
}

impl VerifiedModule {
    /// The verified module itself, borrowed.
    ///
    /// The explicit spelling of the same read-only projection [`Deref`]
    /// provides; used where naming the boundary crossing is clearer
    /// than leaving it to coercion.
    ///
    /// [`Deref`]: std::ops::Deref
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// Seals a module *without* verifying it.
    ///
    /// Compiled only under `cfg(test)`, and `pub(crate)` even there, so
    /// no build of the production library contains it and no caller
    /// outside this crate can name it. It exists for exactly two jobs
    /// the boundary would otherwise make untestable: handing malformed
    /// NIR to the interpreter to prove its runtime defence in depth
    /// still reports `X0004` rather than panicking (`rfcs/0015`), and
    /// handing hand-built NIR to the native backend to prove which
    /// layer owns which refusal.
    #[cfg(test)]
    pub(crate) fn seal_unchecked(module: Module) -> Self {
        VerifiedModule { module }
    }
}

/// Read-only projection to the verified module, so a consumer that only
/// ever reads NIR (`nir::print_module`, the native backend) needs no
/// ceremony at the call site. There is deliberately no `DerefMut`:
/// every way to *change* a sealed module is absent, not merely
/// inconvenient.
impl std::ops::Deref for VerifiedModule {
    type Target = Module;

    fn deref(&self) -> &Module {
        &self.module
    }
}

/// Verifies `module` and, if it passes, seals it.
///
/// This is the whole production path from raw NIR to something
/// executable: the single place [`super::verify::verify_module`] is
/// consulted on behalf of an executor, and the single place a
/// [`VerifiedModule`] comes into existence. `module` is taken by value
/// so that the module that was checked and the module that was sealed
/// cannot be two different values.
///
/// On failure the verifier's own structured diagnostics are returned
/// unchanged -- same codes, same order, no summarising into strings --
/// and no `VerifiedModule` exists, so nothing downstream can run.
pub fn verify(
    module: Module,
    source: SourceId,
    interner: &Interner,
    registry: &ItemRegistry,
) -> Result<VerifiedModule, Vec<Diagnostic>> {
    let diagnostics = super::verify::verify_module(&module, source, interner, registry);
    if diagnostics.is_empty() {
        Ok(VerifiedModule { module })
    } else {
        Err(diagnostics)
    }
}
