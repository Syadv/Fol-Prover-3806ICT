"""
Formula data classes for propositional logic.
Will add FOL terms (Var, Const, Fun) and quantifiers later.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Top:
    def __repr__(self): return "T"

@dataclass(frozen=True)
class Bot:
    def __repr__(self): return "F"

@dataclass(frozen=True)
class Atom:
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Not:
    sub: object
    def __repr__(self): return f"~{self.sub}"

@dataclass(frozen=True)
class And:
    left: object
    right: object
    def __repr__(self): return f"({self.left} & {self.right})"

@dataclass(frozen=True)
class Or:
    left: object
    right: object
    def __repr__(self): return f"({self.left} | {self.right})"

@dataclass(frozen=True)
class Imp:
    left: object
    right: object
    def __repr__(self): return f"({self.left} -> {self.right})"
