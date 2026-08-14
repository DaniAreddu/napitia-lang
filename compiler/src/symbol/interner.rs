//! The [`Interner`] and [`Symbol`] types.

use std::collections::HashMap;
use std::rc::Rc;

/// A stable, cheap-to-copy handle for an interned string. Two identical
/// source strings interned by the same [`Interner`] always produce equal
/// `Symbol`s, and `Symbol` values are only meaningful relative to the
/// `Interner` that produced them.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(u32);

/// Deduplicates identifier and keyword strings encountered during one
/// compilation session. Owned by the caller (the lexer, or whatever sets
/// up a compilation session) rather than held in any global/static, so
/// multiple independent sessions never share or contend on interner
/// state.
#[derive(Debug, Default)]
pub struct Interner {
    strings: Vec<Rc<str>>,
    lookup: HashMap<Rc<str>, Symbol>,
}

impl Interner {
    pub fn new() -> Self {
        Interner {
            strings: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    /// Interns `text`, returning its existing [`Symbol`] if this exact
    /// string was already interned, or allocating a new one otherwise.
    pub fn intern(&mut self, text: &str) -> Symbol {
        if let Some(symbol) = self.lookup.get(text) {
            return *symbol;
        }

        let symbol = Symbol(self.strings.len() as u32);
        let shared: Rc<str> = Rc::from(text);
        self.strings.push(shared.clone());
        self.lookup.insert(shared, symbol);
        symbol
    }

    /// Resolves a [`Symbol`] back to its string.
    ///
    /// # Panics
    ///
    /// Panics if `symbol` was not produced by this `Interner` — this is
    /// an internal invariant violation (a `Symbol` from one session used
    /// against another), never something user input can trigger.
    pub fn resolve(&self, symbol: Symbol) -> &str {
        &self.strings[symbol.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning_the_same_string_twice_returns_the_same_symbol() {
        let mut interner = Interner::new();
        let a = interner.intern("value");
        let b = interner.intern("value");
        assert_eq!(a, b);
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn interning_distinct_strings_returns_distinct_symbols() {
        let mut interner = Interner::new();
        let a = interner.intern("value");
        let b = interner.intern("mutable");
        assert_ne!(a, b);
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn resolve_returns_the_original_string() {
        let mut interner = Interner::new();
        let symbol = interner.intern("record");
        assert_eq!(interner.resolve(symbol), "record");
    }

    #[test]
    fn repeated_interning_does_not_grow_the_table() {
        let mut interner = Interner::new();
        for _ in 0..100 {
            interner.intern("func");
        }
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn empty_interner_reports_empty() {
        let interner = Interner::new();
        assert!(interner.is_empty());
        assert_eq!(interner.len(), 0);
    }

    #[test]
    fn distinct_interners_can_hand_out_equal_symbol_ids_independently() {
        let mut a = Interner::new();
        let mut b = Interner::new();
        let sym_a = a.intern("value");
        let sym_b = b.intern("value");
        // Same underlying id (both are the first symbol interned), but
        // each interner's table is independent state, not shared global
        // state.
        assert_eq!(sym_a, sym_b);
        assert_eq!(a.resolve(sym_a), b.resolve(sym_b));
    }
}
