"""
Algorithm 2 from Hou (2021), page 67. Backward proof search for
first-order logic in LK'.

LK' rules (from Fig 2.3 in the textbook):

Closing the branch:
    id:   Gamma, A |- A, Delta
    top R: Gamma |- top, Delta
    bot L: Gamma, bot |- Delta

Non-branching logical rules:
    and L: Gamma, A, B |- Delta  /  Gamma, A and B |- Delta
    or R:  Gamma |- A, B, Delta  /  Gamma |- A or B, Delta
    imp R: Gamma, A |- B, Delta  /  Gamma |- A imp B, Delta
    not L: Gamma |- A, Delta     /  Gamma, not A |- Delta
    not R: Gamma, A |- Delta     /  Gamma |- not A, Delta
    forall R: Gamma |- A[a/x], Delta / Gamma |- forall x.A, Delta  (a fresh)
    exists L: Gamma, A[a/x] |- Delta / Gamma, exists x.A |- Delta  (a fresh)

Branching:
    and R: Gamma |- A, Delta   AND   Gamma |- B, Delta
    or L:  Gamma, A |- Delta   AND   Gamma, B |- Delta
    imp L: Gamma |- A, Delta   AND   Gamma, B |- Delta

Quantifier instantiation (the formula stays around):
    forall L: Gamma, forall x.A, A[t/x] |- Delta
    exists R: Gamma |- exists x.A, A[t/x], Delta

Side condition: in forall R and exists L, the fresh constant must not
already appear anywhere in the conclusion.
"""
from __future__ import annotations
from formula import *
import time


class FreshNameGenerator:
    """Just hands out c0, c1, c2, ... each time you ask for a new constant."""
    def __init__(self):
        self.counter = 0

    def fresh(self) -> Const:
        name = f"c{self.counter}"
        self.counter += 1
        return Const(name)


class ProofResult:
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
    Algorithm 2 as written in the textbook.

    Sequents are stored as (gamma, delta) where gamma and delta are both
    frozensets of formulae. Frozensets because we want quick membership
    checks (for the id rule) and they're hashable so they could go in a
    cache - which I don't actually do here, that's the improved version.

    The instantiation history dict tracks which (forall formula, term)
    pairs have already been used so we don't keep instantiating with the
    same term over and over.
    """

    def __init__(self, max_steps: int = 50000, max_depth: int = 100, timeout: float = 30.0):
        self.max_steps = max_steps
        self.max_depth = max_depth
        self.timeout = timeout
        self.steps = 0
        self.fresh = FreshNameGenerator()
        self.start_time = 0.0

    def prove(self, formula: Formula) -> ProofResult:
        """Try to prove the formula by searching for a derivation of |- formula."""
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
            # Python's default recursion limit hits before our depth limit
            # on some really deep proofs - just treat it as a failed search
            elapsed = time.time() - self.start_time
            return ProofResult(False, self.steps, elapsed)

        elapsed = time.time() - self.start_time
        return ProofResult(result, self.steps, elapsed)

    def _check_limits(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise TimeoutError("hit step limit")
        if time.time() - self.start_time > self.timeout:
            raise TimeoutError("hit time limit")

    def _search(self, gamma: frozenset, delta: frozenset,
                inst_history: dict, depth: int) -> bool:
        """
        Search for a proof of this single sequent.

        inst_history is a dict from (formula, side) to a set of terms
        we've already used, so we don't waste time trying the same
        instantiation twice on this branch. Side is 'L' for forall L,
        'R' for exists R.

        Returns True if we managed to close all the branches.
        """
        self._check_limits()

        if depth > self.max_depth:
            return False

        # Step 1: try to close with id, top R, or bot L

        # id: same formula on both sides
        if gamma & delta:
            return True

        # top R: top is on the right
        if Top() in delta:
            return True

        # bot L: bot is on the left
        if Bot() in gamma:
            return True

        # Step 2: non-branching rules
        # Algorithm 2 says "apply the first applicable one" so that's what
        # we do. The order I check them in here is just whatever felt
        # natural - the algorithm doesn't specify an ordering within step 2.

        # and L: Gamma, A and B |- Delta  =>  Gamma, A, B |- Delta
        for f in gamma:
            if isinstance(f, And):
                new_gamma = (gamma - {f}) | {f.left, f.right}
                return self._search(new_gamma, delta, inst_history, depth + 1)

        # or R: Gamma |- A or B, Delta  =>  Gamma |- A, B, Delta
        for f in delta:
            if isinstance(f, Or):
                new_delta = (delta - {f}) | {f.left, f.right}
                return self._search(gamma, new_delta, inst_history, depth + 1)

        # imp R: Gamma |- A -> B, Delta  =>  Gamma, A |- B, Delta
        for f in delta:
            if isinstance(f, Imp):
                new_gamma = gamma | {f.left}
                new_delta = (delta - {f}) | {f.right}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # not L: Gamma, ~A |- Delta  =>  Gamma |- A, Delta
        for f in gamma:
            if isinstance(f, Not):
                new_gamma = gamma - {f}
                new_delta = delta | {f.sub}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # not R: Gamma |- ~A, Delta  =>  Gamma, A |- Delta
        for f in delta:
            if isinstance(f, Not):
                new_gamma = gamma | {f.sub}
                new_delta = delta - {f}
                return self._search(new_gamma, new_delta, inst_history, depth + 1)

        # forall R: Gamma |- forall x.A, Delta  =>  Gamma |- A[a/x], Delta
        # 'a' has to be fresh (not appearing in the conclusion)
        for f in delta:
            if isinstance(f, Forall):
                a = self.fresh.fresh()
                new_body = subst(f.sub, f.var, a)
                new_delta = (delta - {f}) | {new_body}
                return self._search(gamma, new_delta, inst_history, depth + 1)

        # exists L: same idea, opposite side
        for f in gamma:
            if isinstance(f, Exists):
                a = self.fresh.fresh()
                new_body = subst(f.sub, f.var, a)
                new_gamma = (gamma - {f}) | {new_body}
                return self._search(new_gamma, delta, inst_history, depth + 1)

        # Step 3: branching rules
        # Each one creates two subgoals - we need both to close

        # and R: Gamma |- A and B, Delta  =>  (Gamma |- A, Delta) AND (Gamma |- B, Delta)
        for f in delta:
            if isinstance(f, And):
                d1 = (delta - {f}) | {f.left}
                d2 = (delta - {f}) | {f.right}
                left_ok = self._search(gamma, d1, dict(inst_history), depth + 1)
                if not left_ok:
                    return False
                right_ok = self._search(gamma, d2, dict(inst_history), depth + 1)
                return right_ok

        # or L: Gamma, A or B |- Delta  =>  (Gamma, A |- Delta) AND (Gamma, B |- Delta)
        for f in gamma:
            if isinstance(f, Or):
                g1 = (gamma - {f}) | {f.left}
                g2 = (gamma - {f}) | {f.right}
                left_ok = self._search(g1, delta, dict(inst_history), depth + 1)
                if not left_ok:
                    return False
                right_ok = self._search(g2, delta, dict(inst_history), depth + 1)
                return right_ok

        # imp L: Gamma, A -> B |- Delta  =>  (Gamma |- A, Delta) AND (Gamma, B |- Delta)
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

        # Step 4: forall L / exists R using a term we already have
        all_terms = collect_terms_sequent(gamma, delta)
        if not all_terms:
            # nothing to instantiate with - skip ahead to step 5
            pass
        else:
            # forall L: Gamma, forall x.A |- Delta  =>  Gamma, forall x.A, A[t/x] |- Delta
            # The forall x.A stays around (that's why this can run forever
            # if we're not careful)
            for f in gamma:
                if isinstance(f, Forall):
                    key = (f, 'L')
                    used = inst_history.get(key, set())
                    for t in all_terms:
                        if t not in used:
                            new_body = subst(f.sub, f.var, t)
                            if new_body not in gamma:
                                # actually adds something new
                                new_gamma = gamma | {new_body}
                                new_hist = dict(inst_history)
                                new_hist[key] = used | {t}
                                result = self._search(new_gamma, delta, new_hist, depth + 1)
                                if result:
                                    return True
                            else:
                                # we've already got this exact instance, no point retrying
                                inst_history[key] = used | {t}

            # exists R: same idea, other side
            for f in delta:
                if isinstance(f, Exists):
                    key = (f, 'R')
                    used = inst_history.get(key, set())
                    for t in all_terms:
                        if t not in used:
                            new_body = subst(f.sub, f.var, t)
                            if new_body not in delta:
                                new_delta = delta | {new_body}
                                new_hist = dict(inst_history)
                                new_hist[key] = used | {t}
                                result = self._search(gamma, new_delta, new_hist, depth + 1)
                                if result:
                                    return True
                            else:
                                inst_history[key] = used | {t}

        # Step 5: forall L / exists R with a brand new fresh constant
        # This is what makes Algorithm 2 not terminate on invalid formulae 
        # we just keep generating new constants forever
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

        # Step 6: nothing applies, give up on this branch
        return False


def prove(formula: Formula, **kwargs) -> ProofResult:
    """Convenience wrapper - just makes a fresh prover and runs it."""
    prover = BaselineProver(**kwargs)
    return prover.prove(formula)


# Some quick tests to make sure the basic stuff works.
# Run with: python3 baseline.py

if __name__ == "__main__":
    from parser import parse_formula

    test_cases = [
        # propositional tautologies, should all prove
        ("A -> A",                                      True),
        ("(A -> B) -> ((~A -> B) -> B)",                True),
        ("A -> (B -> A)",                               True),
        ("(A -> (B -> C)) -> (B -> (A -> C))",          True),
        ("(A -> B) -> ((B -> C) -> (A -> C))",          True),
        ("A | ~A",                                      True),   # excluded middle
        ("~~A -> A",                                    True),   # double neg
        ("A -> ~~A",                                    True),

        # propositional non-tautologies, should NOT prove
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
    print("Baseline (Algorithm 2 from Hou 2021, p67)")
    print("=" * 70)

    passed = 0
    for text, expected in test_cases:
        f = parse_formula(text)
        result = prove(f, max_steps=10000, max_depth=50, timeout=5.0)
        ok = "OK  " if result.proved == expected else "FAIL"
        if result.proved == expected:
            passed += 1
        print(f"  {ok}  {text:60s}  {result}")

    print(f"\n{passed}/{len(test_cases)} passed")
