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
//! (`VerifiedModule::seal_unchecked`), which the production library
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::render;
    use crate::hir::ItemId;
    use crate::nir::{
        BasicBlock, BlockId, Const, Function, Instruction, RecordLayout, Terminator, ValueId,
        ValueKind,
    };
    use crate::source::SourceMap;
    use crate::types::Ty;

    const MAIN: ItemId = ItemId(1);
    const FILE: ItemId = ItemId(2);

    /// One hand-built module, verified against an empty registry -- the
    /// same footing `nir::verify` itself is tested on, so a diagnostic
    /// here identifies itself by NIR identity alone.
    fn sealing(module: Module, interner: &Interner) -> Result<VerifiedModule, Vec<Diagnostic>> {
        let mut map = SourceMap::new();
        let source = map.add_file("hand-built.npt", "\n");
        verify(module, source, interner, &ItemRegistry::default())
    }

    /// Every code a refusal carried, in the verifier's own order. Empty
    /// means the module sealed.
    fn refusal_codes(module: Module, interner: &Interner) -> Vec<&'static str> {
        match sealing(module, interner) {
            Ok(_) => Vec::new(),
            Err(diagnostics) => diagnostics.iter().map(|d| d.code).collect(),
        }
    }

    /// Exactly what a user would see: every diagnostic rendered against
    /// its own source, in the order the verifier produced them.
    fn rendered_refusal(module: Module, interner: &Interner) -> String {
        let mut map = SourceMap::new();
        let source = map.add_file("hand-built.npt", "\n");
        match verify(module, source, interner, &ItemRegistry::default()) {
            Ok(_) => String::new(),
            Err(diagnostics) => diagnostics.iter().map(|d| render(d, &map)).collect(),
        }
    }

    fn block(id: u32, instructions: Vec<Instruction>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            instructions,
            terminator,
        }
    }

    fn int(result: u32, literal: i128) -> Instruction {
        Instruction::Value {
            result: ValueId(result),
            ty: Ty::I64,
            kind: ValueKind::Const(Const::Int(literal)),
        }
    }

    fn main_function(interner: &mut Interner, blocks: Vec<BasicBlock>) -> Function {
        Function {
            id: MAIN,
            name: interner.intern("main"),
            type_params: Vec::new(),
            requirements: Vec::new(),
            params: Vec::new(),
            return_type: Ty::I64,
            raises: Vec::new(),
            blocks,
        }
    }

    fn module_of(functions: Vec<Function>) -> Module {
        Module {
            functions,
            ..Module::default()
        }
    }

    /// `func main() -> i64 { return 1 }`, the smallest module the
    /// verifier accepts, as a starting point to perturb.
    fn minimal_main(interner: &mut Interner) -> Module {
        module_of(vec![main_function(
            interner,
            vec![block(
                0,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        )])
    }

    #[test]
    fn a_module_the_verifier_accepts_is_sealed_exactly_as_it_was_checked() {
        let mut interner = Interner::new();
        let built = minimal_main(&mut interner);
        let before = crate::nir::print_module(&built, &interner, &ItemRegistry::default());

        let sealed = sealing(built, &interner).expect("the minimal module verifies");

        // The seal holds the module that was checked, unchanged: what it
        // prints is what the verifier saw, not a rebuilt or defaulted
        // approximation.
        assert_eq!(
            crate::nir::print_module(sealed.module(), &interner, &ItemRegistry::default()),
            before
        );
        assert_eq!(sealed.module().functions.len(), 1);
        assert_eq!(sealed.module().functions[0].id, MAIN);
        // The read-only projection and the explicit accessor are the
        // same borrow, not two views that could drift.
        assert_eq!(sealed.functions.len(), sealed.module().functions.len());
    }

    #[test]
    fn a_function_with_no_blocks_at_all_cannot_be_sealed() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(&mut interner, Vec::new())]);
        assert_eq!(refusal_codes(built, &interner), vec!["V0003"]);
    }

    #[test]
    fn a_function_whose_blocks_include_no_entry_block_cannot_be_sealed() {
        let mut interner = Interner::new();
        // Structurally fine in every other way -- it simply has no
        // `BlockId(0)`, so it has no defined place to start.
        let built = module_of(vec![main_function(
            &mut interner,
            vec![block(
                1,
                vec![int(0, 1)],
                Terminator::Return(Some(ValueId(0))),
            )],
        )]);
        assert_eq!(refusal_codes(built, &interner), vec!["V0015"]);
    }

    #[test]
    fn returning_a_value_nothing_defines_cannot_be_sealed() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(
            &mut interner,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(7))))],
        )]);
        assert_eq!(refusal_codes(built, &interner), vec!["V0006"]);
    }

    #[test]
    fn branching_to_a_block_that_does_not_exist_cannot_be_sealed() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(
            &mut interner,
            vec![block(0, Vec::new(), Terminator::Branch(BlockId(9)))],
        )]);
        assert_eq!(refusal_codes(built, &interner), vec!["V0004"]);
    }

    #[test]
    fn a_resource_left_live_at_function_exit_cannot_be_sealed() {
        let mut interner = Interner::new();
        let file = interner.intern("File");
        let field = interner.intern("f");
        let body = vec![block(
            0,
            vec![
                int(0, 1),
                Instruction::Value {
                    result: ValueId(1),
                    ty: Ty::Named(FILE, file),
                    kind: ValueKind::RecordCreate(FILE, Vec::new(), vec![ValueId(0)]),
                },
            ],
            Terminator::Return(None),
        )];
        let mut built = module_of(vec![Function {
            return_type: Ty::Unit,
            ..main_function(&mut interner, body)
        }]);
        built.records = vec![(
            FILE,
            RecordLayout {
                name: file,
                type_params: Vec::new(),
                fields: vec![(field, Ty::I64)],
                affine: true,
            },
        )];
        assert_eq!(refusal_codes(built, &interner), vec!["V0077"]);
    }

    /// A definition in a block nothing can reach does not make a use in
    /// the entry block legitimate: there is a path -- the only path --
    /// from entry to that use on which the value was never produced.
    #[test]
    fn an_unreachable_definition_cannot_validate_a_reachable_use() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(
            &mut interner,
            vec![
                block(0, Vec::new(), Terminator::Return(Some(ValueId(0)))),
                // Nothing jumps here. It defines `%0` and returns it,
                // which on its own is impeccable.
                block(1, vec![int(0, 1)], Terminator::Return(Some(ValueId(0)))),
            ],
        )]);
        assert_eq!(refusal_codes(built, &interner), vec!["V0018"]);
    }

    /// Storage order is not semantics: the same defect reported from a
    /// module whose blocks are stored in the opposite order must render
    /// the same text, code for code and note for note.
    #[test]
    fn reversing_the_block_vector_does_not_change_the_refusal() {
        let mut interner = Interner::new();
        let forward = module_of(vec![main_function(
            &mut interner,
            vec![
                block(0, Vec::new(), Terminator::Return(Some(ValueId(0)))),
                block(1, vec![int(0, 1)], Terminator::Return(Some(ValueId(0)))),
            ],
        )]);
        let mut reversed = forward.clone();
        for function in &mut reversed.functions {
            function.blocks.reverse();
        }

        let forward_text = rendered_refusal(forward, &interner);
        assert!(forward_text.contains("V0018"), "{forward_text}");
        assert_eq!(forward_text, rendered_refusal(reversed, &interner));
    }

    /// Reversing the *function* vector is the same claim one level up.
    #[test]
    fn reversing_the_function_vector_does_not_change_the_refusal() {
        let mut interner = Interner::new();
        let helper = interner.intern("helper");
        let broken = main_function(
            &mut interner,
            vec![block(0, Vec::new(), Terminator::Branch(BlockId(9)))],
        );
        let intact = vec![block(
            0,
            vec![int(0, 1)],
            Terminator::Return(Some(ValueId(0))),
        )];
        let other = Function {
            id: ItemId(3),
            name: helper,
            ..main_function(&mut interner, intact)
        };
        let forward = module_of(vec![broken, other]);
        let mut reversed = forward.clone();
        reversed.functions.reverse();

        let forward_text = rendered_refusal(forward, &interner);
        assert!(forward_text.contains("V0004"), "{forward_text}");
        assert_eq!(forward_text, rendered_refusal(reversed, &interner));
    }

    #[test]
    fn verifying_the_same_module_twice_produces_byte_identical_diagnostics() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(
            &mut interner,
            vec![block(0, Vec::new(), Terminator::Return(Some(ValueId(7))))],
        )]);

        let first = rendered_refusal(built.clone(), &interner);
        assert!(first.contains("V0006"), "{first}");
        assert_eq!(first, rendered_refusal(built.clone(), &interner));
        assert_eq!(first, rendered_refusal(built, &interner));
    }

    /// A refusal is the verifier's own `Diagnostic` values, not a
    /// rendering or a summary of them: a caller can still read the code
    /// and the severity off each one.
    #[test]
    fn a_refusal_carries_the_verifiers_own_structured_diagnostics() {
        let mut interner = Interner::new();
        let built = module_of(vec![main_function(&mut interner, Vec::new())]);

        let diagnostics = sealing(built, &interner).expect_err("an empty function body is refused");
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "V0003");
        assert_eq!(diagnostics[0].severity, crate::diagnostics::Severity::Error);
    }
}
