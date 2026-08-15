//! Lexical scopes for local variable resolution.

use std::collections::HashMap;

use crate::hir::LocalId;
use crate::symbol::Symbol;

/// A stack of lexical scopes mapping names to [`LocalId`]s. Re-defining a
/// name — in the same scope or a nested one — always shadows the
/// previous binding rather than erroring: shadowing is a normal,
/// supported operation (`spec/0002`'s `value`/`mutable` bindings), unlike
/// duplicate *item* definitions at module scope, which the caller
/// tracks separately.
#[derive(Debug, Default)]
pub struct Scopes {
    stack: Vec<HashMap<Symbol, LocalId>>,
}

impl Scopes {
    pub fn new() -> Self {
        Scopes {
            stack: vec![HashMap::new()],
        }
    }

    pub fn push(&mut self) {
        self.stack.push(HashMap::new());
    }

    pub fn pop(&mut self) {
        self.stack.pop();
        debug_assert!(!self.stack.is_empty(), "popped the outermost scope");
    }

    pub fn define(&mut self, name: Symbol, id: LocalId) {
        self.stack
            .last_mut()
            .expect("at least one scope is always active")
            .insert(name, id);
    }

    pub fn lookup(&self, name: Symbol) -> Option<LocalId> {
        self.stack
            .iter()
            .rev()
            .find_map(|scope| scope.get(&name).copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(n: u32) -> Symbol {
        Symbol(n)
    }

    #[test]
    fn lookup_finds_a_binding_in_the_current_scope() {
        let mut scopes = Scopes::new();
        scopes.define(sym(0), LocalId(1));
        assert_eq!(scopes.lookup(sym(0)), Some(LocalId(1)));
    }

    #[test]
    fn lookup_finds_a_binding_in_an_outer_scope() {
        let mut scopes = Scopes::new();
        scopes.define(sym(0), LocalId(1));
        scopes.push();
        assert_eq!(scopes.lookup(sym(0)), Some(LocalId(1)));
    }

    #[test]
    fn inner_scope_shadows_outer_scope() {
        let mut scopes = Scopes::new();
        scopes.define(sym(0), LocalId(1));
        scopes.push();
        scopes.define(sym(0), LocalId(2));
        assert_eq!(scopes.lookup(sym(0)), Some(LocalId(2)));
    }

    #[test]
    fn popping_a_scope_restores_the_outer_binding() {
        let mut scopes = Scopes::new();
        scopes.define(sym(0), LocalId(1));
        scopes.push();
        scopes.define(sym(0), LocalId(2));
        scopes.pop();
        assert_eq!(scopes.lookup(sym(0)), Some(LocalId(1)));
    }

    #[test]
    fn redefining_in_the_same_scope_shadows_without_error() {
        let mut scopes = Scopes::new();
        scopes.define(sym(0), LocalId(1));
        scopes.define(sym(0), LocalId(2));
        assert_eq!(scopes.lookup(sym(0)), Some(LocalId(2)));
    }

    #[test]
    fn unresolved_name_is_none() {
        let scopes = Scopes::new();
        assert_eq!(scopes.lookup(sym(0)), None);
    }
}
