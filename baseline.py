"""
Algorithm 2 from Hou (page 67) — propositional only for now.
Refactored to use the formula dataclasses.
"""
from formula import Top, Bot, Atom, Not, And, Or, Imp


def is_closed(gamma, delta):
    if gamma & delta:
        return True
    if Top() in delta: return True
    if Bot() in gamma: return True
    return False


def prove(gamma, delta, depth=0):
    if depth > 100:
        return False
    if is_closed(gamma, delta):
        return True

    # non-branching rules
    for f in gamma:
        if isinstance(f, And):
            return prove((gamma - {f}) | {f.left, f.right}, delta, depth+1)
    for f in delta:
        if isinstance(f, Or):
            return prove(gamma, (delta - {f}) | {f.left, f.right}, depth+1)
    for f in delta:
        if isinstance(f, Imp):
            return prove(gamma | {f.left}, (delta - {f}) | {f.right}, depth+1)
    for f in gamma:
        if isinstance(f, Not):
            return prove(gamma - {f}, delta | {f.sub}, depth+1)
    for f in delta:
        if isinstance(f, Not):
            return prove(gamma | {f.sub}, delta - {f}, depth+1)

    # branching rules
    for f in delta:
        if isinstance(f, And):
            d1 = (delta - {f}) | {f.left}
            d2 = (delta - {f}) | {f.right}
            return prove(gamma, d1, depth+1) and prove(gamma, d2, depth+1)
    for f in gamma:
        if isinstance(f, Or):
            g1 = (gamma - {f}) | {f.left}
            g2 = (gamma - {f}) | {f.right}
            return prove(g1, delta, depth+1) and prove(g2, delta, depth+1)
    for f in gamma:
        if isinstance(f, Imp):
            new_gamma = gamma - {f}
            d1 = delta | {f.left}
            g2 = new_gamma | {f.right}
            return prove(new_gamma, d1, depth+1) and prove(g2, delta, depth+1)

    # TODO: forall/exists for FOL
    return False


def prove_formula(f):
    return prove(frozenset(), frozenset({f}))
