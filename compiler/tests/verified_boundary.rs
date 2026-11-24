//! The verified execution boundary (`rfcs/0016`) as an embedder outside
//! this crate meets it.
//!
//! The crate's own unit tests prove the seal from the inside, where the
//! `#[cfg(test)]` unchecked path exists. These use only the public API a
//! third-party crate links against: `nir::Module` is public with public
//! fields, so an embedder can take NIR the compiler lowered, change it,
//! and offer it back. Whatever it offers must pass `nir::verify` before
//! any executor will take it, and a refusal must be the verifier's own
//! structured diagnostics with no executor ever built.

use compiler::driver::{self, IrOutput};
use compiler::hir::ItemRegistry;
use compiler::interpreter::{Interpreter, Value};
use compiler::nir::{self, Instruction, Module};
use compiler::source::{SourceId, SourceMap};
use compiler::symbol::Interner;

const PROGRAM: &str = "\
func main() -> i64 {
    value base = 40;
    value answer = base + 2;
    return answer;
}
";

/// Lowers `PROGRAM` through the ordinary driver and hands back what an
/// embedder can get its hands on: a raw copy of the sealed module, plus
/// everything `nir::verify` needs to seal it again.
fn lowered() -> (Module, SourceId, Interner, ItemRegistry) {
    let mut map = SourceMap::new();
    let source = map.add_file("embedder.npt", PROGRAM);
    let mut interner = Interner::new();
    let IrOutput::Ready { nir, registry } = driver::ir(&map, source, &mut interner) else {
        panic!("the fixture program must compile");
    };
    // `Clone` on the projection is the only way back to a raw module,
    // and what it yields is exactly that: raw, and unaccepted by any
    // executor until it is verified again.
    (nir.module().clone(), source, interner, registry)
}

fn main_of(module: &Module, interner: &Interner) -> usize {
    module
        .functions
        .iter()
        .position(|function| interner.resolve(function.name) == "main")
        .expect("the fixture declares `main`")
}

/// The refusal an embedder receives, and the same module's verdict from
/// the borrowed check that does not seal -- they must be one answer.
fn refusal(module: Module, source: SourceId, interner: &Interner, registry: &ItemRegistry) {
    let independent: Vec<&str> = nir::verify_module(&module, source, interner, registry)
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect();
    let diagnostics = match nir::verify(module, source, interner, registry) {
        Ok(_) => panic!("a broken module was sealed; the verifier saw: {independent:?}"),
        Err(diagnostics) => diagnostics,
    };
    let codes: Vec<&str> = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect();
    assert!(!codes.is_empty(), "a refusal must say why");
    assert!(
        codes.iter().all(|code| code.starts_with('V')),
        "a refusal is the verifier's own, got {codes:?}"
    );
    assert_eq!(codes, independent, "sealing must not summarise or reorder");
}

#[test]
fn an_embedder_reseals_lowered_nir_and_runs_it() {
    let (raw, source, interner, registry) = lowered();
    let sealed = nir::verify(raw, source, &interner, &registry)
        .unwrap_or_else(|diagnostics| panic!("lowered NIR must verify: {diagnostics:?}"));
    assert_eq!(
        Interpreter::new(&sealed).run("main", &interner),
        Ok(Value::Int(42))
    );

    // Copying the seal's contents back out and sealing them again is
    // the same module, and runs the same.
    let again = nir::verify(sealed.module().clone(), source, &interner, &registry).unwrap_or_else(
        |diagnostics| panic!("a copy of a sealed module verifies: {diagnostics:?}"),
    );
    assert_eq!(
        Interpreter::new(&again).run("main", &interner),
        Ok(Value::Int(42))
    );
}

#[test]
fn an_emptied_function_is_refused_before_any_executor_exists() {
    let (mut raw, source, interner, registry) = lowered();
    let main = main_of(&raw, &interner);
    raw.functions[main].blocks.clear();
    refusal(raw, source, &interner, &registry);
}

#[test]
fn instructions_reordered_ahead_of_their_operands_are_refused() {
    let (mut raw, source, interner, registry) = lowered();
    let main = main_of(&raw, &interner);
    let entry = &mut raw.functions[main].blocks[0];
    assert!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Value { .. }))
            .count()
            >= 2,
        "the fixture's entry block must define a value from another"
    );
    // The addition now precedes the constants it adds.
    entry.instructions.reverse();
    refusal(raw, source, &interner, &registry);
}

#[test]
fn a_dropped_definition_is_refused() {
    let (mut raw, source, interner, registry) = lowered();
    let main = main_of(&raw, &interner);
    let entry = &mut raw.functions[main].blocks[0];
    let first = entry
        .instructions
        .iter()
        .position(|instruction| matches!(instruction, Instruction::Value { .. }))
        .expect("the fixture's entry block defines a value");
    entry.instructions.remove(first);
    refusal(raw, source, &interner, &registry);
}

/// Values cross the public API too: `Interpreter::call` returns them and
/// accepts them back, and the seal does not cover them. A resource
/// handle one interpreter returned must not be honoured by another --
/// both number their resources from zero, so without a check the
/// handle would resolve to whichever unrelated resource shares its
/// index there.
#[test]
fn a_resource_handle_is_honoured_only_by_the_interpreter_that_minted_it() {
    const RESOURCES: &str = "\
resource File {
    descriptor: i64,
}

func open(descriptor: i64) -> File {
    return File { descriptor: descriptor };
}

func sink(take file: File) -> i64 {
    value d = file.descriptor;
    drop file;
    return d;
}

func main() -> i64 {
    return 0;
}
";
    let mut map = SourceMap::new();
    let source = map.add_file("handles.npt", RESOURCES);
    let mut interner = Interner::new();
    let IrOutput::Ready { nir, .. } = driver::ir(&map, source, &mut interner) else {
        panic!("the fixture program must compile");
    };
    let first = Interpreter::new(&nir);
    let second = Interpreter::new(&nir);
    let _theirs = second
        .call("open", &interner, vec![Value::Int(3)])
        .expect("open in the second interpreter");
    let ours = first
        .call("open", &interner, vec![Value::Int(5)])
        .expect("open in the first interpreter");

    let refused = second
        .call("sink", &interner, vec![ours.clone()])
        .expect_err("a foreign handle must be refused");
    assert_eq!(refused.code(), "X0004");

    // The handle still belongs to, and works in, the interpreter that
    // minted it.
    assert_eq!(first.call("sink", &interner, vec![ours]), Ok(Value::Int(5)));
}

#[test]
fn a_function_with_its_return_type_changed_is_refused() {
    let (mut raw, source, interner, registry) = lowered();
    let main = main_of(&raw, &interner);
    raw.functions[main].return_type = compiler::types::Ty::Bool;
    refusal(raw, source, &interner, &registry);
}
