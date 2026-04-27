"""
First-Order Logic formula representation.

Syntax (course-style):
  Terms:    variables (x, y, z, ...), constants (a, b, c, ...),
            function application f(t1, ..., tn)
  Formulae: P(t1,...,tn)  — predicate
            ⊤, ⊥          — top, bot
            ¬A             — negation
            A ∧ B          — conjunction
            A ∨ B          — disjunction
            A → B          — implication
            ∀x.A           — universal
            ∃x.A           — existential
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import FrozenSet
import copy


# ── Terms ────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Var:
    """A variable, e.g. x, y, z."""
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Const:
    """A constant (Skolem or domain), e.g. a, b, c."""
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Fun:
    """Function application, e.g. f(a, x)."""
    name: str
    args: tuple  # tuple of Term
    def __repr__(self):
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

Term = Var | Const | Fun


# ── Formulae ─────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Top:
    """⊤ (verum)."""
    def __repr__(self): return "⊤"

@dataclass(frozen=True)
class Bot:
    """⊥ (falsum)."""
    def __repr__(self): return "⊥"

@dataclass(frozen=True)
class Pred:
    """Predicate application, e.g. P(x, a).  Arity-0 for propositions."""
    name: str
    args: tuple = ()  # tuple of Term
    def __repr__(self):
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

@dataclass(frozen=True)
class Not:
    sub: object  # Formula
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
    """Add parens around compound formulae for readability."""
    if isinstance(f, (And, Or, Imp)):
        return f"({f})"
    return str(f)


# ── Substitution ─────────────────────────────────────────────────────

def subst_term(t: Term, var: str, replacement: Term) -> Term:
    """Substitute 'var' with 'replacement' in term t."""
    if isinstance(t, Var):
        return replacement if t.name == var else t
    if isinstance(t, Const):
        return t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(subst_term(a, var, replacement) for a in t.args))
    raise TypeError(f"Unknown term type: {type(t)}")


def subst(f: Formula, var: str, replacement: Term) -> Formula:
    """Substitute free occurrences of 'var' with 'replacement' in formula f."""
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
            return f  # bound variable shadows
        return Forall(f.var, subst(f.sub, var, replacement))
    if isinstance(f, Exists):
        if f.var == var:
            return f  # bound variable shadows
        return Exists(f.var, subst(f.sub, var, replacement))
    raise TypeError(f"Unknown formula type: {type(f)}")


# ── Free variables & terms ──────────────────────────────────────────

def free_vars(f: Formula) -> set[str]:
    """Return set of free variable names in formula f."""
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
    """Collect all terms (Var, Const, Fun) appearing in a formula."""
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
    """Collect all terms from both sides of a sequent."""
    terms = set()
    for f in gamma | delta:
        terms |= collect_terms(f)
    return terms
