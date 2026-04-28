"""
Trying to improve on the baseline. The baseline doesn't terminate on
invalid FOL formulae because forall L / exists R can keep firing forever.
Adding iterative deepening and loop detection to fix this.
"""
from formula import *
import time


class FreshGen:
    def __init__(self):
        self.n = 0
    def fresh(self):
        c = Const(f"c{self.n}")
        self.n += 1
        return c


def prove(formula, timeout=10.0, max_qd=20):
    """Try iterative deepening on quantifier depth."""
    start = time.time()

    for k in range(1, max_qd + 1):
        visited = set()
        fresh = FreshGen()
        if time.time() - start > timeout:
            return False
        try:
            if _search(frozenset(), frozenset({formula}),
                       0, k, visited, fresh, start, timeout):
                return True
        except TimeoutError:
            return False
    return False


def _search(gamma, delta, qd, qlimit, visited, fresh, start, timeout):
    if time.time() - start > timeout:
        raise TimeoutError()

    # loop detection
    key = (gamma, delta)
    if key in visited:
        return False
    visited.add(key)

    # closure
    if gamma & delta: return True
    if Top() in delta: return True
    if Bot() in gamma: return True

    # non-branching rules (same as baseline)
    for f in gamma:
        if isinstance(f, And):
            return _search((gamma-{f})|{f.left,f.right}, delta, qd, qlimit, visited, fresh, start, timeout)
    for f in delta:
        if isinstance(f, Or):
            return _search(gamma, (delta-{f})|{f.left,f.right}, qd, qlimit, visited, fresh, start, timeout)
    for f in delta:
        if isinstance(f, Imp):
            return _search(gamma|{f.left}, (delta-{f})|{f.right}, qd, qlimit, visited, fresh, start, timeout)
    for f in gamma:
        if isinstance(f, Not):
            return _search(gamma-{f}, delta|{f.sub}, qd, qlimit, visited, fresh, start, timeout)
    for f in delta:
        if isinstance(f, Not):
            return _search(gamma|{f.sub}, delta-{f}, qd, qlimit, visited, fresh, start, timeout)
    for f in delta:
        if isinstance(f, Forall):
            a = fresh.fresh()
            return _search(gamma, (delta-{f})|{subst(f.sub, f.var, a)}, qd, qlimit, visited, fresh, start, timeout)
    for f in gamma:
        if isinstance(f, Exists):
            a = fresh.fresh()
            return _search((gamma-{f})|{subst(f.sub, f.var, a)}, delta, qd, qlimit, visited, fresh, start, timeout)

    # branching rules
    for f in delta:
        if isinstance(f, And):
            d1 = (delta-{f})|{f.left}; d2 = (delta-{f})|{f.right}
            if not _search(gamma, d1, qd, qlimit, visited, fresh, start, timeout): return False
            return _search(gamma, d2, qd, qlimit, visited, fresh, start, timeout)
    for f in gamma:
        if isinstance(f, Or):
            g1 = (gamma-{f})|{f.left}; g2 = (gamma-{f})|{f.right}
            if not _search(g1, delta, qd, qlimit, visited, fresh, start, timeout): return False
            return _search(g2, delta, qd, qlimit, visited, fresh, start, timeout)
    for f in gamma:
        if isinstance(f, Imp):
            ng = gamma-{f}
            if not _search(ng, delta|{f.left}, qd, qlimit, visited, fresh, start, timeout): return False
            return _search(ng|{f.right}, delta, qd, qlimit, visited, fresh, start, timeout)

    # quantifier instantiation - bounded by qlimit (iterative deepening)
    if qd >= qlimit:
        return False

    # collect terms
    all_terms = set()
    for f in gamma | delta:
        all_terms |= collect_terms(f)

    for f in gamma:
        if isinstance(f, Forall):
            for t in all_terms:
                nb = subst(f.sub, f.var, t)
                if nb not in gamma:
                    if _search(gamma|{nb}, delta, qd+1, qlimit, visited, fresh, start, timeout):
                        return True
            # try fresh
            t = fresh.fresh()
            nb = subst(f.sub, f.var, t)
            if _search(gamma|{nb}, delta, qd+1, qlimit, visited, fresh, start, timeout):
                return True

    for f in delta:
        if isinstance(f, Exists):
            for t in all_terms:
                nb = subst(f.sub, f.var, t)
                if nb not in delta:
                    if _search(gamma, delta|{nb}, qd+1, qlimit, visited, fresh, start, timeout):
                        return True
            t = fresh.fresh()
            nb = subst(f.sub, f.var, t)
            if _search(gamma, delta|{nb}, qd+1, qlimit, visited, fresh, start, timeout):
                return True

    return False
