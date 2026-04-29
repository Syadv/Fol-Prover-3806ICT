"""
FOL formulae and terms.

Terms are variables, constants, or function applications.
Formulae use Pred for atoms, Top/Bot for true/false, the usual
connectives (Not/And/Or/Imp), and Forall/Exists for quantifiers.

Everything is a frozen dataclass so we can stick them in sets and use
them as dict keys (needed for the visited-sequent cache in improved.py).
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import FrozenSet
import copy


# Terms

@dataclass(frozen=True)
class Var:
    """Variable like x, y, z."""
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Const:
    """Constant - either from input or a fresh one we generated during search."""
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Fun:
    """f(t1, ..., tn) - parser handles this but the search itself never makes new ones."""
    name: str
    args: tuple
    def __repr__(self):
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

Term = Var | Const | Fun


# Formulae

@dataclass(frozen=True)
class Top:
    def __repr__(self): return "⊤"

@dataclass(frozen=True)
class Bot:
    def __repr__(self): return "⊥"

@dataclass(frozen=True)
class Pred:
    """Predicate. If args is empty it's a propositional atom (P, Q, etc)."""
    name: str
    args: tuple = ()
    def __repr__(self):
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

@dataclass(frozen=True)
class Not:
    sub: object
    def __repr__(self): return f"¬{_paren(self.sub)}"

@dataclass(frozen=True)
class And:
    left: object
    right: object
    def __repr__(self): return f"{_paren(self.left)} ∧ {_paren(self.right)}"

@dataclass(frozen=True)
class Or:
    left: object
    right: object
    def __repr__(self): return f"{_paren(self.left)} ∨ {_paren(self.right)}"

@dataclass(frozen=True)
class Imp:
    left: object
    right: object
    def __repr__(self): return f"{_paren(self.left)} → {_paren(self.right)}"

@dataclass(frozen=True)
class Forall:
    var: str
    sub: object
    def __repr__(self): return f"∀{self.var}.{_paren(self.sub)}"

@dataclass(frozen=True)
class Exists:
    var: str
    sub: object
    def __repr__(self): return f"∃{self.var}.{_paren(self.sub)}"

Formula = Top | Bot | Pred | Not | And | Or | Imp | Forall | Exists


def _paren(f) -> str:
    # add parens around compound formulae so output isn't ambiguous
    if isinstance(f, (And, Or, Imp)):
        return f"({f})"
    return str(f)


# Substitution

def subst_term(t: Term, var: str, replacement: Term) -> Term:
    if isinstance(t, Var):
        return replacement if t.name == var else t
    if isinstance(t, Const):
        return t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(subst_term(a, var, replacement) for a in t.args))
    raise TypeError(f"weird term type: {type(t)}")


def subst(f: Formula, var: str, replacement: Term) -> Formula:
    """Replace free occurrences of var with replacement.
    Be careful with bound variables - if we hit a quantifier binding
    the same name, stop substituting inside it. Got bitten by this
    early on."""
    if isinstance(f, (Top, Bot)):
        return f
    if isinstance(f, Pred):
        return Pred(f.name, tuple(subst_term(a, var, replacement) for a in f.args))
    if isinstance(f, Not):
        return Not(subst(f.sub, var, replacement))
    if isinstance(f, And):
        return And(subst(f.left, var, replacement), subst(f.right, var, replacement))
    if isinstance(f, Or):
        return Or(subst(f.left, var, replacement), subst(f.right, var, replacement))
    if isinstance(f, Imp):
        return Imp(subst(f.left, var, replacement), subst(f.right, var, replacement))
    if isinstance(f, Forall):
        if f.var == var:
            return f  # variable bound here, leave it
        return Forall(f.var, subst(f.sub, var, replacement))
    if isinstance(f, Exists):
        if f.var == var:
            return f
        return Exists(f.var, subst(f.sub, var, replacement))
    raise TypeError(f"weird formula type: {type(f)}")


# Free vars + term collection - used by the prover to find what terms
# are available for forall L / exists R instantiation

def free_vars(f: Formula) -> set[str]:
    if isinstance(f, (Top, Bot)):
        return set()
    if isinstance(f, Pred):
        return _term_vars_many(f.args)
    if isinstance(f, Not):
        return free_vars(f.sub)
    if isinstance(f, (And, Or, Imp)):
        return free_vars(f.left) | free_vars(f.right)
    if isinstance(f, (Forall, Exists)):
        return free_vars(f.sub) - {f.var}
    return set()


def _term_vars(t: Term) -> set[str]:
    if isinstance(t, Var):
        return {t.name}
    if isinstance(t, Const):
        return set()
    if isinstance(t, Fun):
        return _term_vars_many(t.args)
    return set()


def _term_vars_many(args) -> set[str]:
    result = set()
    for a in args:
        result |= _term_vars(a)
    return result


def collect_terms(f: Formula) -> set[Term]:
    """Pull out every term that appears in a formula."""
    if isinstance(f, (Top, Bot)):
        return set()
    if isinstance(f, Pred):
        return _collect_terms_many(f.args)
    if isinstance(f, Not):
        return collect_terms(f.sub)
    if isinstance(f, (And, Or, Imp)):
        return collect_terms(f.left) | collect_terms(f.right)
    if isinstance(f, (Forall, Exists)):
        return collect_terms(f.sub)
    return set()


def _collect_terms_term(t: Term) -> set[Term]:
    result = {t}
    if isinstance(t, Fun):
        result |= _collect_terms_many(t.args)
    return result


def _collect_terms_many(args) -> set[Term]:
    result = set()
    for a in args:
        result |= _collect_terms_term(a)
    return result


def collect_terms_sequent(gamma: frozenset, delta: frozenset) -> set[Term]:
    terms = set()
    for f in gamma | delta:
        terms |= collect_terms(f)
    return terms
