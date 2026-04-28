"""
Improved backward proof search for first-order logic using LK'.

Improvements over the baseline (Algorithm 2):

1. **Iterative deepening on quantifier depth**:
   Limits the number of ∀L/∃R instantiations per branch, incrementally
   increasing the limit. Guarantees termination per iteration while
   maintaining completeness via iterative increase.

2. **Subsumption / loop detection**:
   Caches visited sequents (as frozenset pairs). If we revisit the same
   sequent on the same branch, we prune it immediately.

3. **Smarter term selection for ∀L/∃R**:
   Instead of trying arbitrary terms, we prioritise terms that appear on
   the *opposite* side of the sequent (heuristic: terms in the succedent
   for ∀L, terms in the antecedent for ∃R). This mimics a lightweight
   form of goal-directed instantiation.

4. **Eager rule application**:
   Non-branching invertible rules are applied eagerly in a saturation
   loop before considering branching or quantifier rules. This reduces
   the search tree by decomposing the sequent as much as possible first.

5. **Formula complexity heuristic**:
   When multiple branching rules are applicable, we apply the one on the
   smallest formula first (fewer sub-goals tend to be easier to close).
"""
from __future__ import annotations
from formula import *
import time


class FreshNameGenerator:
    def __init__(self):
        self.counter = 0

    def fresh(self) -> Const:
        name = f"c{self.counter}"
        self.counter += 1
        return Const(name)


class ProofResult:
    def __init__(self, proved: bool, steps: int, time_s: float, depth: int = 0, quant_limit: int = 0):
        self.proved = proved
        self.steps = steps
        self.time_s = time_s
        self.depth = depth
        self.quant_limit = quant_limit

    def __repr__(self):
        status = "PROVED" if self.proved else "NOT PROVED"
        return f"{status} (steps={self.steps}, depth={self.depth}, time={self.time_s:.4f}s, qlimit={self.quant_limit})"


def _formula_size(f: Formula) -> int:
    """Rough measure of formula complexity for ordering heuristics."""
    if isinstance(f, (Top, Bot, Pred)):
        return 1
    if isinstance(f, Not):
        return 1 + _formula_size(f.sub)
    if isinstance(f, (And, Or, Imp)):
        return 1 + _formula_size(f.left) + _formula_size(f.right)
    if isinstance(f, (Forall, Exists)):
        return 1 + _formula_size(f.sub)
    return 1


class ImprovedProver:
    def __init__(self, max_steps: int = 100000, max_depth: int = 200,
                 timeout: float = 30.0, max_quant_limit: int = 20):
        self.max_steps = max_steps
        self.max_depth = max_depth
        self.timeout = timeout
        self.max_quant_limit = max_quant_limit
        self.steps = 0
        self.fresh = FreshNameGenerator()
        self.start_time = 0.0
        self.visited: set = set()

    def prove(self, formula: Formula) -> ProofResult:
        """
        Prove validity of formula using iterative deepening on quantifier depth.
        """
        self.steps = 0
        self.start_time = time.time()
        total_steps = 0

        gamma = frozenset()
        delta = frozenset({formula})

        # Improvement 1: Iterative deepening on quantifier instantiation limit
        for qlimit in range(1, self.max_quant_limit + 1):
            self.fresh = FreshNameGenerator()
            self.steps = 0
            self.visited = set()

            try:
                result = self._search(gamma, delta, 0, 0, qlimit)
            except TimeoutError:
                elapsed = time.time() - self.start_time
                return ProofResult(False, total_steps + self.steps, elapsed,
                                   quant_limit=qlimit)

            total_steps += self.steps

            if result:
                elapsed = time.time() - self.start_time
                return ProofResult(True, total_steps, elapsed, quant_limit=qlimit)

            # Check global timeout
            if time.time() - self.start_time > self.timeout:
                break

        elapsed = time.time() - self.start_time
        return ProofResult(False, total_steps, elapsed, quant_limit=self.max_quant_limit)

    def _check_limits(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise TimeoutError("Step limit exceeded")
        if time.time() - self.start_time > self.timeout:
            raise TimeoutError("Time limit exceeded")

    def _search(self, gamma: frozenset, delta: frozenset,
                depth: int, quant_depth: int, quant_limit: int) -> bool:
        """
        Backward proof search with improvements.
        quant_depth: how many ∀L/∃R instantiations on this branch so far.
        quant_limit: max allowed instantiations per branch (iterative deepening parameter).
        """
        self._check_limits()

        if depth > self.max_depth:
            return False

        # ─── Improvement 2: Subsumption / loop detection ────────────
        seq_key = (gamma, delta)
        if seq_key in self.visited:
            return False
        self.visited.add(seq_key)

        # ─── Improvement 4: Eager saturation of non-branching rules ─
        gamma, delta = self._saturate(gamma, delta)

        # ─── Step 1: Check closure after saturation ─────────────────
        if self._is_closed(gamma, delta):
            return True

        # ─── Step 3: Branching rules (sorted by formula size — Improvement 5) ──

        # Collect all branching candidates
        branch_candidates = []

        for f in delta:
            if isinstance(f, And):
                branch_candidates.append(('andR', f, _formula_size(f)))
        for f in gamma:
            if isinstance(f, Or):
                branch_candidates.append(('orL', f, _formula_size(f)))
        for f in gamma:
            if isinstance(f, Imp):
                branch_candidates.append(('impL', f, _formula_size(f)))

        # Sort by formula size (smallest first — Improvement 5)
        branch_candidates.sort(key=lambda x: x[2])

        for rule, f, _ in branch_candidates:
            if rule == 'andR':
                d1 = (delta - {f}) | {f.left}
                d2 = (delta - {f}) | {f.right}
                if self._search(gamma, d1, depth + 1, quant_depth, quant_limit):
                    if self._search(gamma, d2, depth + 1, quant_depth, quant_limit):
                        return True
                return False  # if a branching rule is applicable, commit

            elif rule == 'orL':
                g1 = (gamma - {f}) | {f.left}
                g2 = (gamma - {f}) | {f.right}
                if self._search(g1, delta, depth + 1, quant_depth, quant_limit):
                    if self._search(g2, delta, depth + 1, quant_depth, quant_limit):
                        return True
                return False

            elif rule == 'impL':
                new_gamma = gamma - {f}
                d1 = delta | {f.left}
                g2 = new_gamma | {f.right}
                if self._search(new_gamma, d1, depth + 1, quant_depth, quant_limit):
                    if self._search(g2, delta, depth + 1, quant_depth, quant_limit):
                        return True
                return False

        # ─── Step 4/5: Quantifier instantiation (with depth limit) ──
        if quant_depth >= quant_limit:
            return False  # reached instantiation limit for this iteration

        # ─── Improvement 3: Smarter term selection ──────────────────
        # For ∀L, prioritise terms from delta (goal-directed)
        # For ∃R, prioritise terms from gamma

        gamma_terms = set()
        delta_terms = set()
        for f in gamma:
            gamma_terms |= collect_terms(f)
        for f in delta:
            delta_terms |= collect_terms(f)
        all_terms = gamma_terms | delta_terms

        # ∀L: try terms from delta first, then gamma-only terms
        prioritised_terms_forallL = list(delta_terms) + [t for t in gamma_terms if t not in delta_terms]

        for f in gamma:
            if isinstance(f, Forall):
                for t in prioritised_terms_forallL:
                    new_body = subst(f.sub, f.var, t)
                    if new_body not in gamma:
                        new_gamma = gamma | {new_body}
                        if self._search(new_gamma, delta, depth + 1,
                                        quant_depth + 1, quant_limit):
                            return True

        # ∃R: try terms from gamma first, then delta-only terms
        prioritised_terms_existsR = list(gamma_terms) + [t for t in delta_terms if t not in gamma_terms]

        for f in delta:
            if isinstance(f, Exists):
                for t in prioritised_terms_existsR:
                    new_body = subst(f.sub, f.var, t)
                    if new_body not in delta:
                        new_delta = delta | {new_body}
                        if self._search(gamma, new_delta, depth + 1,
                                        quant_depth + 1, quant_limit):
                            return True

        # ∀L / ∃R with fresh term
        for f in gamma:
            if isinstance(f, Forall):
                t = self.fresh.fresh()
                new_body = subst(f.sub, f.var, t)
                new_gamma = gamma | {new_body}
                if self._search(new_gamma, delta, depth + 1,
                                quant_depth + 1, quant_limit):
                    return True

        for f in delta:
            if isinstance(f, Exists):
                t = self.fresh.fresh()
                new_body = subst(f.sub, f.var, t)
                new_delta = delta | {new_body}
                if self._search(gamma, new_delta, depth + 1,
                                quant_depth + 1, quant_limit):
                    return True

        return False

    def _is_closed(self, gamma: frozenset, delta: frozenset) -> bool:
        """Check if sequent is axiomatically closed."""
        if gamma & delta:
            return True
        if Top() in delta:
            return True
        if Bot() in gamma:
            return True
        return False

    def _saturate(self, gamma: frozenset, delta: frozenset):
        """
        Improvement 4: Eagerly apply all non-branching invertible rules
        until no more apply. This is sound because these rules are invertible
        in LK' — applying them never loses provability.
        """
        changed = True
        while changed:
            changed = False

            # ∧L
            for f in gamma:
                if isinstance(f, And):
                    gamma = (gamma - {f}) | {f.left, f.right}
                    changed = True
                    break

            # ∨R
            for f in delta:
                if isinstance(f, Or):
                    delta = (delta - {f}) | {f.left, f.right}
                    changed = True
                    break

            # →R
            for f in delta:
                if isinstance(f, Imp):
                    gamma = gamma | {f.left}
                    delta = (delta - {f}) | {f.right}
                    changed = True
                    break

            # ¬L
            for f in gamma:
                if isinstance(f, Not):
                    gamma = gamma - {f}
                    delta = delta | {f.sub}
                    changed = True
                    break

            # ¬R
            for f in delta:
                if isinstance(f, Not):
                    gamma = gamma | {f.sub}
                    delta = delta - {f}
                    changed = True
                    break

            # ∀R (fresh constant)
            for f in delta:
                if isinstance(f, Forall):
                    a = self.fresh.fresh()
                    new_body = subst(f.sub, f.var, a)
                    delta = (delta - {f}) | {new_body}
                    changed = True
                    break

            # ∃L (fresh constant)
            for f in gamma:
                if isinstance(f, Exists):
                    a = self.fresh.fresh()
                    new_body = subst(f.sub, f.var, a)
                    gamma = (gamma - {f}) | {new_body}
                    changed = True
                    break

        return gamma, delta


# ── Convenience ──────────────────────────────────────────────────────

def prove(formula: Formula, **kwargs) -> ProofResult:
    prover = ImprovedProver(**kwargs)
    return prover.prove(formula)


# ── Tests ────────────────────────────────────────────────────────────

if __name__ == "__main__":
    from parser import parse_formula

    test_cases = [
        # Propositional tautologies
        ("A -> A",                                      True),
        ("(A -> B) -> ((~A -> B) -> B)",                True),
        ("A -> (B -> A)",                               True),
        ("(A -> (B -> C)) -> (B -> (A -> C))",          True),
        ("(A -> B) -> ((B -> C) -> (A -> C))",          True),
        ("A | ~A",                                      True),
        ("~~A -> A",                                    True),
        ("A -> ~~A",                                    True),
        ("(A -> B) -> (~B -> ~A)",                      True),   # contrapositive
        ("((A -> B) & (B -> C)) -> (A -> C)",           True),   # hypothetical syllogism

        # Propositional non-tautologies
        ("A -> B",                                      False),
        ("A & B",                                       False),
        ("A | B -> A & B",                              False),

        # FOL valid
        ("forall x. P(x) -> forall x. P(x)",           True),
        ("forall x. P(x) -> exists x. P(x)",           True),
        ("~(forall x. P(x)) -> exists x. ~P(x)",       True),
        ("forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))", True),
        ("exists x. (P(x) & Q(x)) -> (exists x. P(x) & exists x. Q(x))", True),
        ("(forall x. P(x)) & (forall x. Q(x)) -> forall x. (P(x) & Q(x))", True),

        # FOL invalid
        ("exists x. P(x) -> forall x. P(x)",           False),
        ("(exists x. P(x)) & (exists x. Q(x)) -> exists x. (P(x) & Q(x))", False),
    ]

    print("=" * 70)
    print("IMPROVED PROVER — Enhanced Algorithm 2")
    print("=" * 70)

    passed = 0
    for text, expected in test_cases:
        f = parse_formula(text)
        result = prove(f, max_steps=50000, max_depth=100, timeout=5.0)
        ok = "✓" if result.proved == expected else "✗"
        if result.proved == expected:
            passed += 1
        print(f"  {ok}  {text:70s}  {result}")

    print(f"\nPassed: {passed}/{len(test_cases)}")
