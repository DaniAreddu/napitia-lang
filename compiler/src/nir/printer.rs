//! Renders NIR as text for debugging, matching `spec/0006`'s format:
//!
//! ```text
//! func @add(%0: i64, %1: i64) -> i64 {
//! bb0:
//!     %2 = add.i64 %0, %1
//!     ret %2
//! }
//! ```
//!
//! Output is deterministic (no pointer- or hash-derived identifiers),
//! which is what makes it usable as golden-output in tests.

use std::collections::HashMap;
use std::fmt::Write as _;

use super::block::{BasicBlock, Terminator};
use super::instruction::{Const, Instruction, ValueId, ValueKind};
use super::{Function, Module};
use crate::hir::{ItemId, ItemRegistry, TypeParamId};
use crate::limits::MAX_GENERIC_DEPTH;
use crate::symbol::{Interner, Symbol};
use crate::types::{CapabilityRequirement, Evidence, Ty, display_ty};

/// Every declaration and reference to `id` renders through this one
/// helper, so the two can never drift into different formats
/// (`rfcs/0007`): the registry's own canonical, module-qualified name
/// (empty module path -> no prefix, matching single-file compilation),
/// suffixed with the bare `ItemId` itself -- which alone already makes
/// two distinct items impossible to confuse, even before the name is
/// considered, and remains stable however a future change reshapes
/// qualified-name formatting.
fn qualified_ref(id: ItemId, registry: &ItemRegistry, interner: &Interner) -> String {
    format!("{}#{}", registry.qualified_name(id, interner), id.0)
}

/// Formats a type for textual NIR. Primitives keep their existing
/// spelling; a nominal `Ty::Named` renders through the same
/// `qualified_ref` every declaration and reference already uses, so two
/// same-named types declared in different modules (`sales.user.User` vs
/// `admin.user.User`) always print distinguishably here too -- in
/// parameter/return positions, allocations, loads, and every other typed
/// instruction -- never as the same ambiguous bare name (`rfcs/0007`).
/// An import alias never appears: the name always comes from the
/// registry's own canonical declared name, exactly like `qualified_ref`.
fn format_ty(ty: &Ty, interner: &Interner, registry: &ItemRegistry) -> String {
    format_ty_at_depth(ty, interner, registry, 0)
}

/// `depth`-bounded the same way every other stage that walks a nested
/// type application is (`crate::limits::MAX_GENERIC_DEPTH`) -- this
/// printer is a public entry point a direct caller can invoke with
/// hand-built NIR that bypasses every earlier stage's own depth guard,
/// so it never trusts them to have already bounded the input
/// (`rfcs/0008`). Past the bound, an application's remaining arguments
/// print as `...` rather than recursing further -- this is textual
/// debug output, not a correctness gate, so a truncated (rather than a
/// panicking) render is the right degradation.
fn format_ty_at_depth(
    ty: &Ty,
    interner: &Interner,
    registry: &ItemRegistry,
    depth: usize,
) -> String {
    if depth > MAX_GENERIC_DEPTH {
        return "...".to_string();
    }
    match ty {
        Ty::Named(item, _) => qualified_ref(*item, registry, interner),
        // A generic instantiation prints its declaration's own qualified
        // reference, then its concrete arguments bracketed the same way
        // a call/construction site's own applied arguments do
        // (`@collections.Box#8[str]`, `rfcs/0008`) -- nested applications
        // (`Box[Maybe[i64]]`) format unambiguously since each argument
        // recurses through this same function.
        Ty::Applied(item, args) => format!(
            "{}{}",
            qualified_ref(*item, registry, interner),
            type_args_suffix_at_depth(args, interner, registry, depth + 1)
        ),
        // A symbolic reference to the *enclosing declaration's own* type
        // parameter (inside a parametric body/layout, before any call
        // site substitutes a concrete argument) prints as its bare
        // declared name -- `T`, never a registry lookup, since a type
        // parameter has no module-qualified identity of its own.
        Ty::Param(_, name) => interner.resolve(*name).to_string(),
        other => display_ty(other, interner),
    }
}

/// `[i64, str]` (or nested `[Maybe[i64]]`) for a list of concrete type
/// arguments -- empty for a non-generic call/construction/type, which
/// prints no brackets at all rather than empty ones.
fn type_args_suffix(args: &[Ty], interner: &Interner, registry: &ItemRegistry) -> String {
    type_args_suffix_at_depth(args, interner, registry, 0)
}

fn type_args_suffix_at_depth(
    args: &[Ty],
    interner: &Interner,
    registry: &ItemRegistry,
    depth: usize,
) -> String {
    if args.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = args
        .iter()
        .map(|a| format_ty_at_depth(a, interner, registry, depth))
        .collect();
    format!("[{}]", parts.join(", "))
}

/// `[T, U]` for a generic declaration's own parameter list, in stable
/// declared order -- printed on the declaration itself
/// (`func @core.identity#12[T](...)`), distinct from
/// [`type_args_suffix`]'s concrete arguments at a use site.
fn declared_type_params_suffix(
    type_params: &[(TypeParamId, Symbol)],
    interner: &Interner,
) -> String {
    if type_params.is_empty() {
        return String::new();
    }
    let parts: Vec<&str> = type_params
        .iter()
        .map(|(_, name)| interner.resolve(*name))
        .collect();
    format!("[{}]", parts.join(", "))
}

pub fn print_module(module: &Module, interner: &Interner, registry: &ItemRegistry) -> String {
    let mut out = String::new();
    for (protocol, layout) in &module.protocols {
        print_protocol(&mut out, *protocol, layout, interner, registry);
        out.push('\n');
    }
    for (extend, layout) in &module.extends {
        print_extend(&mut out, *extend, layout, interner, registry);
        out.push('\n');
    }
    for (i, function) in module.functions.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        print_function(&mut out, function, interner, registry);
    }
    out
}

/// `protocol @Equal#4[T] { func equal(left: T, right: T) -> bool; ... }`
/// (`rfcs/0009`) -- each method printed with its own declaration-order
/// index, since that index (never its name) is what a `protocol.call`
/// instruction actually references.
fn print_protocol(
    out: &mut String,
    protocol: ItemId,
    layout: &super::ProtocolLayout,
    interner: &Interner,
    registry: &ItemRegistry,
) {
    let _ = writeln!(
        out,
        "protocol @{}{} {{",
        qualified_ref(protocol, registry, interner),
        declared_type_params_suffix(&layout.type_params, interner)
    );
    for (index, method) in layout.methods.iter().enumerate() {
        let params = method
            .params
            .iter()
            .map(|t| format_ty(t, interner, registry))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            out,
            "    method[{index}] {}({params}) -> {};",
            interner.resolve(method.name),
            format_ty(&method.return_type, interner, registry)
        );
    }
    out.push_str("}\n");
}

/// `extend @Equal#4[i64] { method[0] = @equal_i64#28; }` (`rfcs/0009`)
/// -- an extend's own method table, mapping each protocol method's own
/// index to the concrete NIR function implementing it. A conditional
/// extend's own `uses` requirements print the same way a function's own
/// do (see `requirements_suffix`).
fn print_extend(
    out: &mut String,
    extend: ItemId,
    layout: &super::ExtendLayout,
    interner: &Interner,
    registry: &ItemRegistry,
) {
    let args = type_args_suffix(&layout.protocol_arguments, interner, registry);
    let _ = writeln!(
        out,
        "extend @{}{} for @{}{}{} {{",
        qualified_ref(extend, registry, interner),
        declared_type_params_suffix(&layout.type_params, interner),
        qualified_ref(layout.protocol, registry, interner),
        args,
        requirements_suffix(&layout.requirements, interner, registry),
    );
    for (index, method) in layout.methods.iter().enumerate() {
        let _ = writeln!(
            out,
            "    method[{index}] = @{};",
            qualified_ref(*method, registry, interner)
        );
    }
    out.push_str("}\n");
}

/// `uses @Equal#4[T], @Ord#5[T]` printed on its own line between a
/// signature and `{` (`rfcs/0009`) -- empty for a declaration with no
/// capability requirements, matching how `type_args_suffix` renders
/// nothing for a non-generic reference.
fn requirements_suffix(
    requirements: &[CapabilityRequirement],
    interner: &Interner,
    registry: &ItemRegistry,
) -> String {
    if requirements.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = requirements
        .iter()
        .map(|r| {
            format!(
                "@{}{}",
                qualified_ref(r.protocol, registry, interner),
                type_args_suffix(&r.arguments, interner, registry)
            )
        })
        .collect();
    format!("\nuses {}", parts.join(", "))
}

fn format_evidence(evidence: &Evidence, interner: &Interner, registry: &ItemRegistry) -> String {
    match evidence {
        Evidence::Forwarded(index) => format!("forwarded[{index}]"),
        Evidence::Extension { extend, nested } => {
            if nested.is_empty() {
                format!("@{}", qualified_ref(*extend, registry, interner))
            } else {
                let parts: Vec<String> = nested
                    .iter()
                    .map(|n| format_evidence(n, interner, registry))
                    .collect();
                format!(
                    "@{}[{}]",
                    qualified_ref(*extend, registry, interner),
                    parts.join(", ")
                )
            }
        }
    }
}

fn evidence_list_suffix(
    evidence: &[Evidence],
    interner: &Interner,
    registry: &ItemRegistry,
) -> String {
    if evidence.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = evidence
        .iter()
        .map(|e| format_evidence(e, interner, registry))
        .collect();
    format!(" evidence [{}]", parts.join(", "))
}

fn print_function(
    out: &mut String,
    function: &Function,
    interner: &Interner,
    registry: &ItemRegistry,
) {
    let params = function
        .params
        .iter()
        .map(|p| format!("%{}: {}", p.value.0, format_ty(&p.ty, interner, registry)))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        out,
        "func @{}{}({params}) -> {}{} {{",
        qualified_ref(function.id, registry, interner),
        declared_type_params_suffix(&function.type_params, interner),
        format_ty(&function.return_type, interner, registry),
        requirements_suffix(&function.requirements, interner, registry)
    );
    // Comparisons produce `bool` but are tagged with their *operand*
    // type (`eq.i64`, not `eq.bool`) per spec/0006; this table lets the
    // printer look that operand type up from the value that produced
    // it, since a comparison instruction's own declared `ty` is `bool`.
    let value_types = collect_value_types(function);
    for block in &function.blocks {
        print_block(out, block, &value_types, interner, registry);
    }
    out.push_str("}\n");
}

fn collect_value_types(function: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for param in &function.params {
        types.insert(param.value, param.ty.clone());
    }
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Instruction::Value { result, ty, .. } = instruction {
                types.insert(*result, ty.clone());
            }
        }
    }
    types
}

fn print_block(
    out: &mut String,
    block: &BasicBlock,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
    registry: &ItemRegistry,
) {
    let _ = writeln!(out, "bb{}:", block.id.0);
    for instruction in &block.instructions {
        let _ = writeln!(
            out,
            "    {}",
            format_instruction(instruction, value_types, interner, registry)
        );
    }
    let _ = writeln!(
        out,
        "    {}",
        format_terminator(&block.terminator, interner, registry)
    );
}

fn format_instruction(
    instruction: &Instruction,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
    registry: &ItemRegistry,
) -> String {
    match instruction {
        Instruction::Value { result, ty, kind } => {
            format!(
                "%{} = {}",
                result.0,
                format_value_kind(kind, ty, value_types, interner, registry)
            )
        }
        Instruction::Store { slot, value } => format!("store %{}, %{}", slot.0, value.0),
    }
}

/// The operand type for a comparison instruction (looked up from
/// whichever operand's producing instruction is known), falling back to
/// the instruction's own declared type if that lookup fails.
fn operand_ty<'a>(a: ValueId, ty: &'a Ty, value_types: &'a HashMap<ValueId, Ty>) -> &'a Ty {
    value_types.get(&a).unwrap_or(ty)
}

fn format_value_kind(
    kind: &ValueKind,
    ty: &Ty,
    value_types: &HashMap<ValueId, Ty>,
    interner: &Interner,
    registry: &ItemRegistry,
) -> String {
    let ty_name = format_ty(ty, interner, registry);
    match kind {
        ValueKind::Alloc => format!("alloc.{ty_name}"),
        ValueKind::Const(c) => format!("const.{ty_name} {}", format_const(c)),
        ValueKind::Load(slot) => format!("load %{}", slot.0),
        ValueKind::Add(a, b) => format!("add.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Sub(a, b) => format!("sub.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Mul(a, b) => format!("mul.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Div(a, b) => format!("div.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Rem(a, b) => format!("rem.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Neg(a) => format!("neg.{ty_name} %{}", a.0),
        ValueKind::Not(a) => format!("not.{ty_name} %{}", a.0),
        ValueKind::And(a, b) => format!("and.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Or(a, b) => format!("or.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Xor(a, b) => format!("xor.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Shl(a, b) => format!("shl.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Shr(a, b) => format!("shr.{ty_name} %{}, %{}", a.0, b.0),
        ValueKind::Eq(a, b) => {
            format!(
                "eq.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Ne(a, b) => {
            format!(
                "ne.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Lt(a, b) => {
            format!(
                "lt.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Le(a, b) => {
            format!(
                "le.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Gt(a, b) => {
            format!(
                "gt.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Ge(a, b) => {
            format!(
                "ge.{} %{}, %{}",
                format_ty(operand_ty(*a, ty, value_types), interner, registry),
                a.0,
                b.0
            )
        }
        ValueKind::Call(function, type_args, args, evidence) => {
            let args = args
                .iter()
                .map(|v: &ValueId| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "call @{}{}({args}){}",
                qualified_ref(*function, registry, interner),
                type_args_suffix(type_args, interner, registry),
                evidence_list_suffix(evidence, interner, registry)
            )
        }
        ValueKind::ProtocolCall {
            protocol,
            arguments,
            method,
            evidence,
            args,
        } => {
            let args = args
                .iter()
                .map(|v: &ValueId| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "protocol.call @{}{}.method[{method}]({args}){}",
                qualified_ref(*protocol, registry, interner),
                type_args_suffix(arguments, interner, registry),
                evidence_list_suffix(std::slice::from_ref(evidence), interner, registry)
            )
        }
        ValueKind::RecordCreate(record, type_args, fields) => {
            let fields = fields
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "record.create @{}{}({fields})",
                qualified_ref(*record, registry, interner),
                type_args_suffix(type_args, interner, registry)
            )
        }
        ValueKind::RecordField {
            base,
            record,
            field,
        } => format!(
            "record.field @{}.{field} %{}",
            qualified_ref(*record, registry, interner),
            base.0
        ),
        ValueKind::VariantCreate {
            variant,
            case,
            type_args,
            payload,
        } => {
            let payload = payload
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "variant.create @{}{}.{case}({payload})",
                qualified_ref(*variant, registry, interner),
                type_args_suffix(type_args, interner, registry)
            )
        }
        ValueKind::VariantPayload {
            base,
            variant,
            case,
            index,
        } => format!(
            "variant.payload @{}.{case}.{index} %{}",
            qualified_ref(*variant, registry, interner),
            base.0
        ),
    }
}

fn format_const(c: &Const) -> String {
    match c {
        Const::Int(v) => v.to_string(),
        Const::Float(v) => v.to_string(),
        Const::Bool(v) => v.to_string(),
        Const::Char(v) => format!("{v:?}"),
        Const::Str(v) => format!("{v:?}"),
        Const::Unit => "unit".to_string(),
    }
}

fn format_terminator(term: &Terminator, interner: &Interner, registry: &ItemRegistry) -> String {
    match term {
        Terminator::Return(Some(v)) => format!("ret %{}", v.0),
        Terminator::Return(None) => "ret".to_string(),
        Terminator::Branch(target) => format!("br bb{}", target.0),
        Terminator::CondBranch {
            condition,
            then_block,
            else_block,
        } => {
            format!(
                "condbr %{}, bb{}, bb{}",
                condition.0, then_block.0, else_block.0
            )
        }
        Terminator::Switch {
            scrutinee,
            variant,
            cases,
        } => {
            let targets = cases
                .iter()
                .map(|b| format!("bb{}", b.0))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "switch %{} : @{} {{{targets}}}",
                scrutinee.0,
                qualified_ref(*variant, registry, interner)
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower_module as lower_hir;
    use crate::lexer::tokenize;
    use crate::nir::lower_module;
    use crate::parser::Parser;
    use crate::source::SourceMap;
    use crate::typeck::check_module;

    fn print(text: &str) -> String {
        let mut map = SourceMap::new();
        let id = map.add_file("t.npt", text);
        let mut interner = Interner::new();
        let (tokens, diags) = tokenize(map.get(id).content(), id, &mut interner);
        assert!(diags.is_empty(), "{diags:?}");
        let (module, diags) = Parser::new(tokens, id, &mut interner).parse_module();
        assert!(diags.is_empty(), "{diags:?}");
        let (hir, diags) = lower_hir(&module, id, &interner);
        assert!(diags.is_empty(), "{diags:?}");
        let typeck_result = check_module(&hir, id, &interner, crate::typeck::EntryMain::ByName);
        assert!(
            typeck_result.diagnostics.is_empty(),
            "{:?}",
            typeck_result.diagnostics
        );
        let nir = lower_module(
            &hir,
            &typeck_result.local_types,
            &typeck_result.expr_types,
            &typeck_result.pattern_case,
            &typeck_result.call_type_args,
            &HashMap::new(),
            &HashMap::new(),
            &interner,
            id,
        )
        .expect("expected lowering to succeed");
        let registry = crate::hir::registry::build(&hir, &HashMap::new());
        print_module(&nir, &interner, &registry)
    }

    #[test]
    fn prints_add_function_matching_the_spec_example() {
        // Single-file compilation has no module path to qualify with
        // (`rfcs/0007`), so the declaration is just its own name plus
        // its `ItemId` (`#0`, the first and only function here) -- the
        // same `#id` suffix a multi-module project's declarations get.
        let text = print("func add(left: i64, right: i64) -> i64 { return left + right }");
        assert!(text.starts_with("func @add#0(%0: i64, %1: i64) -> i64 {\n"));
        assert!(text.contains("bb0:\n"));
        assert!(text.contains("add.i64"));
        assert!(text.contains("ret"));
    }

    #[test]
    fn printer_output_is_deterministic() {
        let a = print("func f() -> i64 { return 1 + 2 }");
        let b = print("func f() -> i64 { return 1 + 2 }");
        assert_eq!(a, b);
    }

    #[test]
    fn prints_multiple_functions_in_declaration_order() {
        let text = print("func a() -> i64 { return 1 } func b() -> i64 { return 2 }");
        let a_pos = text.find("func @a").unwrap();
        let b_pos = text.find("func @b").unwrap();
        assert!(a_pos < b_pos);
    }

    #[test]
    fn prints_conditional_branches_for_if() {
        let text = print("func f(x: bool) -> i64 { if x { return 1 } return 0 }");
        assert!(text.contains("condbr"));
    }

    #[test]
    fn single_file_nir_qualifies_a_nominal_parameter_type_with_just_its_own_id() {
        // Single-file compilation has no project-level module path
        // (`rfcs/0007`) -- a nominal type in a parameter position must
        // still print readably as its bare declared name plus its own
        // `ItemId`, the same `#id` suffix every other item reference
        // gets, never a raw `ItemId` alone and never a module-path
        // prefix that doesn't exist here.
        let text = print(
            "record User { id: i64 }\n\
             func user_id(u: User) -> i64 { return u.id }\n",
        );
        assert!(text.contains("(%0: User#0)"), "{text}");
    }

    #[test]
    fn single_file_nir_qualifies_a_nominal_return_type_and_allocation() {
        let text = print(
            "record User { id: i64 }\n\
             func make() -> User { mutable u = User { id: 1 }; return u }\n",
        );
        assert!(text.contains(") -> User#0 {"), "{text}");
        assert!(text.contains("alloc.User#0"), "{text}");
    }

    // -- Generic textual NIR (`rfcs/0008`) -------------------------------

    #[test]
    fn a_generic_functions_declaration_prints_its_own_type_parameters() {
        let text = print(
            "func identity[T](x: T) -> T { return x } func main() -> i64 { return identity[i64](1) }",
        );
        assert!(
            text.contains("func @identity#") && text.contains("[T](%0: T) -> T {"),
            "{text}"
        );
    }

    #[test]
    fn a_generic_call_prints_its_own_concrete_type_arguments() {
        let text = print(
            "func identity[T](x: T) -> T { return x } func main() -> i64 { return identity[i64](1) }",
        );
        assert!(
            text.contains("identity#") && text.contains("[i64](%"),
            "{text}"
        );
    }

    #[test]
    fn a_generic_record_type_prints_bracketed_concrete_arguments() {
        let text = print(
            "record Box[T] { payload: T } \
             func main() -> i64 { value b = Box[i64] { payload: 1 }; return b.payload }",
        );
        assert!(text.contains("Box#") && text.contains("[i64]("), "{text}");
    }

    #[test]
    fn nested_generic_applications_print_unambiguously() {
        let text = print(
            "record Box[T] { payload: T } \
             variant Maybe[T] { Some(T), None } \
             func f(b: Box[Maybe[i64]]) -> i64 { return 0 }",
        );
        assert!(text.contains("Box#") && text.contains("Maybe#"), "{text}");
        assert!(
            text.contains("[Maybe#"),
            "expected a nested bracket, got: {text}"
        );
    }

    #[test]
    fn generic_textual_nir_output_is_deterministic() {
        let source = "func identity[T](x: T) -> T { return x } \
                      record Box[T] { payload: T } \
                      func main() -> i64 { \
                          value b = Box[i64] { payload: identity[i64](1) }; \
                          return b.payload \
                      }";
        assert_eq!(print(source), print(source));
    }
}
