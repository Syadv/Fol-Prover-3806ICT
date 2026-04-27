"""
Baseline implementation of Algorithm 2 (Page 67, Hou 2021).

Naïve backward proof search strategy for first-order logic using LK'.

LK' rules (Fig 2.3):
  Zero-premise (close branch):
    id:  Γ, A ⊢ A, Δ
    ⊤R:  Γ ⊢ ⊤, Δ
    ⊥L:  Γ, ⊥ ⊢ Δ

  Non-branching logical:
    ∧L:  Γ, A, B ⊢ Δ  /  Γ, A∧B ⊢ Δ
    ∨R:  Γ ⊢ A, B, Δ  /  Γ ⊢ A∨B, Δ
    →R:  Γ, A ⊢ B, Δ  /  Γ ⊢ A→B, Δ
    ¬L:  Γ ⊢ A, Δ     /  Γ, ¬A ⊢ Δ
    ¬R:  Γ, A ⊢ Δ     /  Γ ⊢ ¬A, Δ
    ∀R:  Γ ⊢ A[a/x], Δ  /  Γ ⊢ ∀x.A, Δ   (a fresh)
    ∃L:  Γ, A[a/x] ⊢ Δ  /  Γ, ∃x.A ⊢ Δ   (a fresh)

  Branching logical:
    ∧R:  Γ ⊢ A, Δ   Γ ⊢ B, Δ  /  Γ ⊢ A∧B, Δ
    ∨L:  Γ, A ⊢ Δ   Γ, B ⊢ Δ  /  Γ, A∨B ⊢ Δ
    →L:  Γ ⊢ A, Δ   Γ, B ⊢ Δ  /  Γ, A→B ⊢ Δ

  Quantifier instantiation (copy formula):
    ∀L:  Γ, ∀x.A, A[t/x] ⊢ Δ  /  Γ, ∀x.A ⊢ Δ
    ∃R:  Γ ⊢ ∃x.A, A[t/x], Δ  /  Γ ⊢ ∃x.A, Δ

Side condition: in ∀R and ∃L, the fresh constant 'a' must not occur in the conclusion.
"""
from __future__ import annotations
from formula import *
import time


class FreshNameGenerator:
    """Generates fresh constant names: c0, c1, c2, ..."""
    def __init__(self):
        self.counter = 0

    def fresh(self) -> Const:
        name = f"c{self.counter}"
        self.counter += 1
        return Const(name)


class ProofResult:
    """Result of a proof search."""
    def __init__(self, proved: bool, steps: int, time_s: float, depth: int = 0):
        self.proved = proved
        self.steps = steps
        self.time_s = time_s
        self.depth = depth

    def __repr__(self):
        status = "PROVED" if self.proved else "NOT PROVED"
        return f"{status} (steps={self.steps}, depth={self.depth}, time={self.time_s:.4f}s)"


class BaselineProver:
    """
    Implements Algorithm 2: naïve backward proof search in LK'.

    A sequent is represented as (gamma, delta) where:
      gamma = frozenset of formulae (antecedent)
      delta = frozenset of formulae (succedent)

    The search explores open branches. For each branch we track which
    (formula, term) pairs have already been used for ∀L / ∃R instantiation.
    """

    def __init__(self, max_steps: int = 50000, max_depth: int = 100, timeout: float = 30.0):
        self.max_steps = max_steps
        self.max_depth = max_depth
        self.timeout = timeout
        self.steps = 0
        self.fresh = FreshNameGenerator()
        self.start_time = 0.0

    def prove(self, formula: Formula) -> ProofResult:
        """Try to prove that 'formula' is valid by searching for a derivation of ⊢ formula."""
        self.steps = 0
        self.fresh = FreshNameGenerator()
        self.start_time = time.time()

        gamma = frozenset()
        delta = frozenset({formula})

        try:
            result = self._search(gamma, delta, dict(), 0)
        except TimeoutError:
            elapsed = time.time() - self.start_time
            return ProofResult(False, self.steps, elapsed)
        except RecursionError:
            elapsed = time.time() - self.start_time
            return ProofResult(False, self.steps, elapsed)

        elapsed = time.time() - self.start_time
        return ProofResult(result, self.steps, elapsed)

    def _check_limits(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise TimeoutError("Step limit exceeded")
        if time.time() - self.start_time > self.timeout:
            raise TimeoutError("Time limit exceeded")

    def _search(self, gamma: frozenset, delta: frozenset,
                inst_history: dict, depth: int) -> bool:
        """
        Backward proof search on a single sequent (branch).

        inst_history: maps (formula, side) -> set of terms already used for instantiation.
                      side is 'L' for ∀L, 'R' for ∃R.

        Returns True if this branch (and all sub-branches) can be closed.
        """
        self._check_limits()

        if depth > self.max_depth:
            return False

        # ─── Step 1: id, ⊤R, ⊥L — close branch ─────────────────────
        # id: if gamma ∩ delta is non-empty
        if gamma & delta:
            return True

        # ⊤R: if Top() in delta
        if Top() in delta:
            return True

        # ⊥L: if Bot() in gamma
        if Bot() in gamma:
            return True

        # ─── Step 2: Non-branching rules ∧L, ∨R, →R, ¬L, ¬R, ∀R, ∃L ──
        # Apply the first applicable non-branching rule and recurse.

        # ∧L: Γ, A∧B ⊢ Δ  =>  Γ, A, B ⊢ Δ
        for f in gamma:
            if isinstance(f, And):
                new_gamma = (gamma - {f}) | {f.left, f.right}
                return self._search(new_gamma, delta, inst_history, depth + 1)

        # ∨R: Γ ⊢ A∨B, Δ  =>  Γ ⊢ A, B, Δ
        for f in delta:
            if isinstance(f, Or):
                new_delta = (delta - {f}) | {f.left, f.right}
                return self._search(gamma, new_delta, inst_history, depth + 1)

        # →R: Γ ⊢ A→B, Δ  =>  Γ, A ⊢ B, Δ
        for f in delta:
            if isinstance(f, Imp):
                new_gamma = gamma | {f.left}
                new_delta = (delta - {f}) | {f.right}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # ¬L: Γ, ¬A ⊢ Δ  =>  Γ ⊢ A, Δ
        for f in gamma:
            if isinstance(f, Not):
                new_gamma = gamma - {f}
                new_delta = delta | {f.sub}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # ¬R: Γ ⊢ ¬A, Δ  =>  Γ, A ⊢ Δ
        for f in delta:
            if isinstance(f, Not):
                new_gamma = gamma | {f.sub}
                new_delta = delta - {f}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # ∀R: Γ ⊢ ∀x.A, Δ  =>  Γ ⊢ A[a/x], Δ  (a fresh, must not occur in conclusion)
        for f in delta:
            if isinstance(f, Forall):
                a = self.fresh.fresh()
                new_body = subst(f.sub, f.var, a)
                new_delta = (delta - {f}) | {new_body}
                return self._search(gamma, new_delta, inst_history, depth + 1)

        # ∃L: Γ, ∃x.A ⊢ Δ  =>  Γ, A[a/x] ⊢ Δ  (a fresh, must not occur in conclusion)
        for f in gamma:
            if isinstance(f, Exists):
                a = self.fresh.fresh()
                new_body = subst(f.sub, f.var, a)
                new_gamma = (gamma - {f}) | {new_body}
                return self._search(new_gamma, delta, inst_history, depth + 1)

        # ─── Step 3: Branching rules ∧R, ∨L, →L ────────────────────

        # ∧R: Γ ⊢ A∧B, Δ  =>  (Γ ⊢ A, Δ) AND (Γ ⊢ B, Δ)
        for f in delta:
            if isinstance(f, And):
                d1 = (delta - {f}) | {f.left}
                d2 = (delta - {f}) | {f.right}
                left_ok = self._search(gamma, d1, dict(inst_history), depth + 1)
                if not left_ok:
                    return False
                right_ok = self._search(gamma, d2, dict(inst_history), depth + 1)
                return right_ok

        # ∨L: Γ, A∨B ⊢ Δ  =>  (Γ, A ⊢ Δ) AND (Γ, B ⊢ Δ)
        for f in gamma:
            if isinstance(f, Or):
                g1 = (gamma - {f}) | {f.left}
                g2 = (gamma - {f}) | {f.right}
                left_ok = self._search(g1, delta, dict(inst_history), depth + 1)
                if not left_ok:
                    return False
                right_ok = self._search(g2, delta, dict(inst_history), depth + 1)
                return right_ok

        # →L: Γ, A→B ⊢ Δ  =>  (Γ ⊢ A, Δ) AND (Γ, B ⊢ Δ)
        for f in gamma:
            if isinstance(f, Imp):
                new_gamma = gamma - {f}
                d1 = delta | {f.left}
                g2 = new_gamma | {f.right}
                left_ok = self._search(new_gamma, d1, dict(inst_history), depth + 1)
                if not left_ok:
                    return False
                right_ok = self._search(g2, delta, dict(inst_history), depth + 1)
                return right_ok

        # ─── Step 4: ∀L / ∃R with existing term ────────────────────
        # Collect all terms currently in the sequent
        all_terms = collect_terms_sequent(gamma, delta)
        if not all_terms:
            # If no terms at all, we might need to create a fresh one (step 5)
            pass
        else:
            # ∀L: Γ, ∀x.A ⊢ Δ  =>  Γ, ∀x.A, A[t/x] ⊢ Δ  (t not yet used)
            for f in gamma:
                if isinstance(f, Forall):
                    key = (f, 'L')
                    used = inst_history.get(key, set())
                    for t in all_terms:
                        if t not in used:
                            new_body = subst(f.sub, f.var, t)
                            if new_body not in gamma:  # avoid no-ops
                                new_gamma = gamma | {new_body}  # keep ∀x.A
                                new_hist = dict(inst_history)
                                new_hist[key] = used | {t}
                                result = self._search(new_gamma, delta, new_hist, depth + 1)
                                if result:
                                    return True
                            else:
                                # Already have this instance, record and skip
                                inst_history[key] = used | {t}

            # ∃R: Γ ⊢ ∃x.A, Δ  =>  Γ ⊢ ∃x.A, A[t/x], Δ  (t not yet used)
            for f in delta:
                if isinstance(f, Exists):
                    key = (f, 'R')
                    used = inst_history.get(key, set())
                    for t in all_terms:
                        if t not in used:
                            new_body = subst(f.sub, f.var, t)
                            if new_body not in delta:
                                new_delta = delta | {new_body}  # keep ∃x.A
                                new_hist = dict(inst_history)
                                new_hist[key] = used | {t}
                                result = self._search(gamma, new_delta, new_hist, depth + 1)
                                if result:
                                    return True
                            else:
                                inst_history[key] = used | {t}

        # ─── Step 5: ∀L / ∃R with fresh term ───────────────────────
        for f in gamma:
            if isinstance(f, Forall):
                t = self.fresh.fresh()
                new_body = subst(f.sub, f.var, t)
                new_gamma = gamma | {new_body}
                key = (f, 'L')
                new_hist = dict(inst_history)
                new_hist[key] = inst_history.get(key, set()) | {t}
                result = self._search(new_gamma, delta, new_hist, depth + 1)
                if result:
                    return True

        for f in delta:
            if isinstance(f, Exists):
                t = self.fresh.fresh()
                new_body = subst(f.sub, f.var, t)
                new_delta = delta | {new_body}
                key = (f, 'R')
                new_hist = dict(inst_history)
                new_hist[key] = inst_history.get(key, set()) | {t}
                result = self._search(gamma, new_delta, new_hist, depth + 1)
                if result:
                    return True

        # ─── Step 6: No rule applicable — stop ─────────────────────
        return False


# ── Convenience function ─────────────────────────────────────────────

def prove(formula: Formula, **kwargs) -> ProofResult:
    prover = BaselineProver(**kwargs)
    return prover.prove(formula)


# ── Quick tests ──────────────────────────────────────────────────────

if __name__ == "__main__":
    from parser import parse_formula

    test_cases = [
        # Propositional tautologies
        ("A -> A",                                      True),
        ("(A -> B) -> ((~A -> B) -> B)",                True),
        ("A -> (B -> A)",                               True),
        ("(A -> (B -> C)) -> (B -> (A -> C))",          True),
        ("(A -> B) -> ((B -> C) -> (A -> C))",          True),
        ("A | ~A",                                      True),   # excluded middle
        ("~~A -> A",                                    True),   # double neg elim
        ("A -> ~~A",                                    True),

        # Propositional non-tautologies
        ("A -> B",                                      False),
        ("A & B",                                       False),
        ("A | B -> A & B",                              False),

        # FOL valid
        ("forall x. P(x) -> forall x. P(x)",           True),
        ("forall x. P(x) -> exists x. P(x)",           True),
        ("~(forall x. P(x)) -> exists x. ~P(x)",       True),
        ("forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))", True),

        # FOL invalid
        ("exists x. P(x) -> forall x. P(x)",           False),
    ]

    print("=" * 70)
    print("BASELINE PROVER — Algorithm 2 (Hou 2021, Page 67)")
    print("=" * 70)

    passed = 0
    for text, expected in test_cases:
        f = parse_formula(text)
        result = prove(f, max_steps=10000, max_depth=50, timeout=5.0)
        ok = "✓" if result.proved == expected else "✗"
        if result.proved == expected:
            passed += 1
        print(f"  {ok}  {text:60s}  {result}")

    print(f"\nPassed: {passed}/{len(test_cases)}")
