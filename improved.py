"""
Improved version of Algorithm 2.

Five things on top of the baseline:

1. Iterative deepening on the number of forall L / exists R
   instantiations per branch. Caps it at k, retries with k+1, etc.
   This is the big one - it's what stops invalid formulae from
   running forever.

2. Visited-sequent cache. If we've already worked on the same
   (gamma, delta) pair on this branch, give up immediately.

3. Smarter term selection. For forall L, try terms from delta
   first, since those are what we're trying to match. Same idea
   for exists R but with gamma. Mostly a guess but it helps.

4. Saturate with non-branching invertible rules before doing
   anything else. They're invertible so it's always safe.

5. When several branching rules apply, pick the one with the
   smallest formula. Tiny effect but doesn't hurt.
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
    """How big is this formula? Just count operators recursively.
    Used for the size heuristic in improvement 5."""
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
        Outer loop - iterative deepening on the quantifier limit.
        Try k=1, then k=2, etc until either we find a proof or hit
        the global timeout.
        """
        self.steps = 0
        self.start_time = time.time()
        total_steps = 0

        gamma = frozenset()
        delta = frozenset({formula})

        # improvement 1: iterative deepening
        for qlimit in range(1, self.max_quant_limit + 1):
            # reset state for each iteration - the visited cache and
            # fresh constants don't carry over between rounds
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

            # quick check before next round
            if time.time() - self.start_time > self.timeout:
                break

        elapsed = time.time() - self.start_time
        return ProofResult(False, total_steps, elapsed, quant_limit=self.max_quant_limit)

    def _check_limits(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise TimeoutError("hit step limit")
        if time.time() - self.start_time > self.timeout:
            raise TimeoutError("hit time limit")

    def _search(self, gamma: frozenset, delta: frozenset,
                depth: int, quant_depth: int, quant_limit: int) -> bool:
        """
        Inner search.
        quant_depth is how many forall L / exists R we've done on this
        branch so far. quant_limit is the cap from iterative deepening.
        """
        self._check_limits()

        if depth > self.max_depth:
            return False

        # improvement 2: have we seen this sequent before, if yes, skip
        seq_key = (gamma, delta)
        if seq_key in self.visited:
            return False
        self.visited.add(seq_key)

        # improvement 4: saturate with invertible rules first
        gamma, delta = self._saturate(gamma, delta)

        # closure check 
        if self._is_closed(gamma, delta):
            return True

        # branching rules - improvement 5: smallest formula first

        # build list of candidates with their sizes
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

        # sort by size, smallest first
        branch_candidates.sort(key=lambda x: x[2])

        for rule, f, _ in branch_candidates:
            if rule == 'andR':
                d1 = (delta - {f}) | {f.left}
                d2 = (delta - {f}) | {f.right}
                if self._search(gamma, d1, depth + 1, quant_depth, quant_limit):
                    if self._search(gamma, d2, depth + 1, quant_depth, quant_limit):
                        return True
                # if a branching rule was applicable but failed, the
                # whole branch fails (we don't try other branchings)
                return False

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

        # quantifier instantiation - capped by quant_limit
        if quant_depth >= quant_limit:
            return False

        # improvement 3: smarter term selection
        # for forall L the goal we're trying to match is on the right,
        # so terms from delta are more likely to lead somewhere useful
        # for exists R it's the opposite

        gamma_terms = set()
        delta_terms = set()
        for f in gamma:
            gamma_terms |= collect_terms(f)
        for f in delta:
            delta_terms |= collect_terms(f)
        all_terms = gamma_terms | delta_terms

        # forall L: delta terms first, then anything else
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

        # exists R: gamma terms first
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

        # last resort: try a fresh constant
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
        """id, top R, bot L all rolled into one check."""
        if gamma & delta:
            return True
        if Top() in delta:
            return True
        if Bot() in gamma:
            return True
        return False

    def _saturate(self, gamma: frozenset, delta: frozenset):
        """
        Improvement 4. Apply every non-branching invertible rule in a
        loop until none of them apply. These rules are all invertible
        so doing them eagerly never costs us a proof.

        I do this by looping with a 'changed' flag and breaking out of
        each inner for-loop after one application, since modifying the
        sets we're iterating over would explode.
        """
        changed = True
        while changed:
            changed = False

            # and L
            for f in gamma:
                if isinstance(f, And):
                    gamma = (gamma - {f}) | {f.left, f.right}
                    changed = True
                    break

            # or R
            for f in delta:
                if isinstance(f, Or):
                    delta = (delta - {f}) | {f.left, f.right}
                    changed = True
                    break

            # imp R
            for f in delta:
                if isinstance(f, Imp):
                    gamma = gamma | {f.left}
                    delta = (delta - {f}) | {f.right}
                    changed = True
                    break

            # not L
            for f in gamma:
                if isinstance(f, Not):
                    gamma = gamma - {f}
                    delta = delta | {f.sub}
                    changed = True
                    break

            # not R
            for f in delta:
                if isinstance(f, Not):
                    gamma = gamma | {f.sub}
                    delta = delta - {f}
                    changed = True
                    break

            # forall R - need a fresh constant
            for f in delta:
                if isinstance(f, Forall):
                    a = self.fresh.fresh()
                    new_body = subst(f.sub, f.var, a)
                    delta = (delta - {f}) | {new_body}
                    changed = True
                    break

            # exists L - same
            for f in gamma:
                if isinstance(f, Exists):
                    a = self.fresh.fresh()
                    new_body = subst(f.sub, f.var, a)
                    gamma = (gamma - {f}) | {new_body}
                    changed = True
                    break

        return gamma, delta


def prove(formula: Formula, **kwargs) -> ProofResult:
    prover = ImprovedProver(**kwargs)
    return prover.prove(formula)


# tests
if __name__ == "__main__":
    from parser import parse_formula

    test_cases = [
        # propositional tautologies
        ("A -> A",                                      True),
        ("(A -> B) -> ((~A -> B) -> B)",                True),
        ("A -> (B -> A)",                               True),
        ("(A -> (B -> C)) -> (B -> (A -> C))",          True),
        ("(A -> B) -> ((B -> C) -> (A -> C))",          True),
        ("A | ~A",                                      True),
        ("~~A -> A",                                    True),
        ("A -> ~~A",                                    True),
        ("(A -> B) -> (~B -> ~A)",                      True),
        ("((A -> B) & (B -> C)) -> (A -> C)",           True),

        # not tautologies
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
    print("Improved prover")
    print("=" * 70)

    passed = 0
    for text, expected in test_cases:
        f = parse_formula(text)
        result = prove(f, max_steps=50000, max_depth=100, timeout=5.0)
        ok = "OK  " if result.proved == expected else "FAIL"
        if result.proved == expected:
            passed += 1
        print(f"  {ok}  {text:70s}  {result}")

    print(f"\n{passed}/{len(test_cases)} passed")
