"""
Benchmark suite: dataset generation, loading, and comparison runner.

Generates multiple datasets of varying difficulty for evaluation.
Also supports loading formulae from text files.
"""
from __future__ import annotations
from formula import *
from parser import parse_formula
from baseline import BaselineProver, ProofResult as BaseResult
from improved import ImprovedProver, ProofResult as ImpResult
import random
import time
import os
import csv


# ── Dataset generators ──────────────────────────────────────────────

def gen_propositional_tautologies(n: int = 30, seed: int = 42) -> list[tuple[str, Formula, bool]]:
    """
    Generate propositional tautologies by construction.
    Each formula is guaranteed valid.
    """
    rng = random.Random(seed)
    atoms = [Pred(c) for c in "ABCDEFGH"]
    results = []

    templates = [
        # p -> p
        lambda p, q: Imp(p, p),
        # p | ~p  (excluded middle)
        lambda p, q: Or(p, Not(p)),
        # ~~p -> p  (double negation elimination)
        lambda p, q: Imp(Not(Not(p)), p),
        # p -> ~~p
        lambda p, q: Imp(p, Not(Not(p))),
        # (p -> q) -> (~q -> ~p)  (contrapositive)
        lambda p, q: Imp(Imp(p, q), Imp(Not(q), Not(p))),
        # (p -> q) -> ((~p -> q) -> q)
        lambda p, q: Imp(Imp(p, q), Imp(Imp(Not(p), q), q)),
        # p -> (q -> p)
        lambda p, q: Imp(p, Imp(q, p)),
        # (p -> (q -> r)) -> (q -> (p -> r))  (needs 3 atoms)
        lambda p, q: (lambda r: Imp(Imp(p, Imp(q, r)), Imp(q, Imp(p, r))))(rng.choice(atoms)),
        # ((p -> q) & (q -> r)) -> (p -> r)  (transitivity)
        lambda p, q: (lambda r: Imp(And(Imp(p, q), Imp(q, r)), Imp(p, r)))(rng.choice(atoms)),
        # (p & q) -> (q & p)  (commutativity)
        lambda p, q: Imp(And(p, q), And(q, p)),
        # (p | q) -> (q | p)
        lambda p, q: Imp(Or(p, q), Or(q, p)),
        # p -> (p | q)
        lambda p, q: Imp(p, Or(p, q)),
        # (p & q) -> p
        lambda p, q: Imp(And(p, q), p),
        # (~p | q) -> (p -> q)  (material implication)
        lambda p, q: Imp(Or(Not(p), q), Imp(p, q)),
        # (p -> q) -> (~p | q)
        lambda p, q: Imp(Imp(p, q), Or(Not(p), q)),
    ]

    for i in range(n):
        p, q = rng.sample(atoms, 2)
        tmpl = templates[i % len(templates)]
        f = tmpl(p, q)
        results.append((str(f), f, True))

    return results


def gen_propositional_non_tautologies(n: int = 20, seed: int = 43) -> list[tuple[str, Formula, bool]]:
    """Generate formulae that are NOT tautologies."""
    rng = random.Random(seed)
    atoms = [Pred(c) for c in "ABCDEFGH"]
    results = []

    templates = [
        lambda p, q: Imp(p, q),                          # p -> q
        lambda p, q: And(p, q),                           # p & q
        lambda p, q: Imp(Or(p, q), And(p, q)),            # p|q -> p&q
        lambda p, q: Imp(Imp(p, q), Imp(q, p)),           # (p->q) -> (q->p)
        lambda p, q: Imp(Imp(p, q), p),                   # (p->q) -> p
        lambda p, q: And(Or(p, q), And(Not(p), Not(q))),  # (p|q) & (~p & ~q)
        lambda p, q: Imp(Not(p), p),                      # ~p -> p
        lambda p, q: And(p, Not(p)),                      # p & ~p  (contradiction)
    ]

    for i in range(n):
        p, q = rng.sample(atoms, 2)
        tmpl = templates[i % len(templates)]
        f = tmpl(p, q)
        results.append((str(f), f, False))

    return results


def gen_fol_valid(n: int = 25, seed: int = 44) -> list[tuple[str, Formula, bool]]:
    """Generate valid FOL formulae."""
    results = []
    texts = [
        "forall x. P(x) -> forall x. P(x)",
        "forall x. P(x) -> exists x. P(x)",
        "~(forall x. P(x)) -> exists x. ~P(x)",
        "~(exists x. P(x)) -> forall x. ~P(x)",
        "forall x. ~P(x) -> ~(exists x. P(x))",
        "exists x. ~P(x) -> ~(forall x. P(x))",
        "forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))",
        "forall x. (P(x) -> Q(x)) -> (exists x. P(x) -> exists x. Q(x))",
        "exists x. (P(x) & Q(x)) -> (exists x. P(x) & exists x. Q(x))",
        "(forall x. P(x)) & (forall x. Q(x)) -> forall x. (P(x) & Q(x))",
        "(exists x. P(x)) | (exists x. Q(x)) -> exists x. (P(x) | Q(x))",
        "forall x. (P(x) & Q(x)) -> (forall x. P(x)) & (forall x. Q(x))",
        "forall x. forall y. R(x, y) -> forall y. forall x. R(x, y)",
        "exists x. exists y. R(x, y) -> exists y. exists x. R(x, y)",
        "forall x. (P(x) | Q(x)) -> (forall x. P(x)) | (exists x. Q(x))",
        "(forall x. P(x)) | (forall x. Q(x)) -> forall x. (P(x) | Q(x))",
        "exists x. forall y. R(x, y) -> forall y. exists x. R(x, y)",
        "forall x. P(x) -> ~~(forall x. P(x))",
        "forall x. (P(x) -> P(x))",
        "exists x. (P(x) | ~P(x))",
        "forall x. forall y. (R(x, y) -> R(x, y))",
        "~(exists x. (P(x) & ~P(x)))",
        "(forall x. P(x) -> Q(x)) -> (~(exists x. Q(x)) -> ~(exists x. P(x)))",
        "forall x. (P(x) -> exists y. R(x, y)) -> (forall x. P(x) -> forall x. exists y. R(x, y))",
        "exists x. P(x) -> ~~(exists x. P(x))",
    ]

    for text in texts[:n]:
        f = parse_formula(text)
        results.append((text, f, True))

    return results


def gen_fol_invalid(n: int = 15, seed: int = 45) -> list[tuple[str, Formula, bool]]:
    """Generate invalid FOL formulae."""
    results = []
    texts = [
        "exists x. P(x) -> forall x. P(x)",
        "forall y. exists x. R(x, y) -> exists x. forall y. R(x, y)",
        "(exists x. P(x)) & (exists x. Q(x)) -> exists x. (P(x) & Q(x))",
        "forall x. (P(x) | Q(x)) -> (forall x. P(x)) | (forall x. Q(x))",
        "(exists x. P(x) -> forall x. Q(x)) -> forall x. (P(x) -> Q(x))",
        "exists x. P(x) -> P(x)",
        "P(x) -> forall x. P(x)",
        "forall x. P(x) | forall x. Q(x) -> forall x. (P(x) & Q(x))",
        "exists x. (P(x) -> forall y. P(y))",  # this is actually valid (Drinker paradox)!
    ]

    # Fix: the drinker paradox IS valid, so let's only keep genuinely invalid ones
    invalid_texts = [
        "exists x. P(x) -> forall x. P(x)",
        "forall y. exists x. R(x, y) -> exists x. forall y. R(x, y)",
        "(exists x. P(x)) & (exists x. Q(x)) -> exists x. (P(x) & Q(x))",
        "forall x. (P(x) | Q(x)) -> (forall x. P(x)) | (forall x. Q(x))",
        "exists x. P(x) & exists x. Q(x) -> forall x. (P(x) & Q(x))",
        "forall x. P(x) | forall x. Q(x) -> forall x. (P(x) & Q(x))",
    ]

    for text in invalid_texts[:n]:
        f = parse_formula(text)
        results.append((text, f, False))

    return results


def gen_hard_fol(seed: int = 46) -> list[tuple[str, Formula, bool]]:
    """
    Hard FOL formulae that stress-test quantifier instantiation.
    These require multiple ∀L / ∃R applications.
    """
    results = []
    hard_valid = [
        # Requires 2+ quantifier instantiations
        "forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))",
        "forall x. (P(x) -> Q(x)) -> (exists x. P(x) -> exists x. Q(x))",
        # Nested quantifiers
        "forall x. forall y. (R(x, y) -> R(x, y))",
        "exists x. forall y. R(x, y) -> forall y. exists x. R(x, y)",
        # Multiple predicates
        "(forall x. (P(x) -> Q(x))) & (forall x. (Q(x) -> R(x))) -> (forall x. (P(x) -> R(x)))",
        # De Morgan for quantifiers
        "~(exists x. P(x)) -> forall x. ~P(x)",
        "~(forall x. P(x)) -> exists x. ~P(x)",
        "forall x. ~P(x) -> ~(exists x. P(x))",
        "exists x. ~P(x) -> ~(forall x. P(x))",
    ]

    hard_invalid = [
        "exists x. P(x) -> forall x. P(x)",
        "forall y. exists x. R(x, y) -> exists x. forall y. R(x, y)",
        "(exists x. P(x)) & (exists x. Q(x)) -> exists x. (P(x) & Q(x))",
    ]

    for text in hard_valid:
        f = parse_formula(text)
        results.append((text, f, True))

    for text in hard_invalid:
        f = parse_formula(text)
        results.append((text, f, False))

    return results


# ── Benchmark runner ─────────────────────────────────────────────────

def run_benchmark(dataset_name: str, dataset: list[tuple[str, Formula, bool]],
                  timeout: float = 10.0, max_steps: int = 50000):
    """Run both provers on a dataset and return comparison results."""

    print(f"\n{'='*80}")
    print(f"Dataset: {dataset_name}  ({len(dataset)} formulae, timeout={timeout}s)")
    print(f"{'='*80}")
    print(f"{'#':>3}  {'Expected':>8}  {'Baseline':>10}  {'BTime':>8}  {'BSteps':>8}  "
          f"{'Improved':>10}  {'ITime':>8}  {'ISteps':>8}  {'Match':>5}")
    print("-" * 95)

    results = []
    b_correct = 0
    i_correct = 0
    b_proved = 0
    i_proved = 0
    b_total_time = 0.0
    i_total_time = 0.0

    for idx, (text, formula, expected) in enumerate(dataset, 1):
        # Baseline
        bp = BaselineProver(max_steps=max_steps, max_depth=100, timeout=timeout)
        br = bp.prove(formula)

        # Improved
        ip = ImprovedProver(max_steps=max_steps * 2, max_depth=200, timeout=timeout)
        ir = ip.prove(formula)

        b_ok = br.proved == expected
        i_ok = ir.proved == expected
        if b_ok: b_correct += 1
        if i_ok: i_correct += 1
        if br.proved: b_proved += 1
        if ir.proved: i_proved += 1
        b_total_time += br.time_s
        i_total_time += ir.time_s

        b_status = "PROVED" if br.proved else "UNKNOWN"
        i_status = "PROVED" if ir.proved else "UNKNOWN"
        match = "✓" if b_ok and i_ok else ("B✗" if not b_ok else "I✗")

        print(f"{idx:3d}  {'valid' if expected else 'invalid':>8}  "
              f"{b_status:>10}  {br.time_s:>7.4f}s  {br.steps:>8d}  "
              f"{i_status:>10}  {ir.time_s:>7.4f}s  {ir.steps:>8d}  {match:>5}")

        results.append({
            'formula': text, 'expected': expected,
            'baseline_proved': br.proved, 'baseline_time': br.time_s, 'baseline_steps': br.steps,
            'improved_proved': ir.proved, 'improved_time': ir.time_s, 'improved_steps': ir.steps,
        })

    print("-" * 95)
    print(f"Summary:")
    print(f"  Baseline — Correct: {b_correct}/{len(dataset)}, Proved: {b_proved}, Time: {b_total_time:.4f}s")
    print(f"  Improved — Correct: {i_correct}/{len(dataset)}, Proved: {i_proved}, Time: {i_total_time:.4f}s")

    if b_total_time > 0:
        speedup = b_total_time / max(i_total_time, 0.0001)
        print(f"  Speedup: {speedup:.2f}x")

    return results


def save_results_csv(all_results: dict, filename: str):
    """Save all benchmark results to CSV."""
    with open(filename, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['dataset', 'formula', 'expected', 'baseline_proved', 'baseline_time',
                         'baseline_steps', 'improved_proved', 'improved_time', 'improved_steps'])
        for ds_name, results in all_results.items():
            for r in results:
                writer.writerow([ds_name, r['formula'], r['expected'],
                                 r['baseline_proved'], f"{r['baseline_time']:.6f}",
                                 r['baseline_steps'], r['improved_proved'],
                                 f"{r['improved_time']:.6f}", r['improved_steps']])
    print(f"\nResults saved to {filename}")


# ── Main ─────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("=" * 80)
    print("BENCHMARK: Baseline (Algorithm 2) vs Improved Prover")
    print("=" * 80)

    datasets = {
        "Propositional Tautologies":      gen_propositional_tautologies(30),
        "Propositional Non-Tautologies":  gen_propositional_non_tautologies(20),
        "FOL Valid":                       gen_fol_valid(25),
        "FOL Invalid":                     gen_fol_invalid(6),
        "Hard FOL (Stress Test)":          gen_hard_fol(),
    }

    all_results = {}
    for name, dataset in datasets.items():
        results = run_benchmark(name, dataset, timeout=10.0, max_steps=50000)
        all_results[name] = results

    save_results_csv(all_results, "/home/claude/prover/benchmark_results.csv")

    # Print overall summary
    print("\n" + "=" * 80)
    print("OVERALL SUMMARY")
    print("=" * 80)
    total_b_correct = 0
    total_i_correct = 0
    total_count = 0
    total_b_time = 0.0
    total_i_time = 0.0

    for name, results in all_results.items():
        count = len(results)
        b_correct = sum(1 for r in results if r['baseline_proved'] == r['expected'])
        i_correct = sum(1 for r in results if r['improved_proved'] == r['expected'])
        b_time = sum(r['baseline_time'] for r in results)
        i_time = sum(r['improved_time'] for r in results)
        total_b_correct += b_correct
        total_i_correct += i_correct
        total_count += count
        total_b_time += b_time
        total_i_time += i_time
        print(f"  {name:40s}  Baseline: {b_correct:3d}/{count}  Improved: {i_correct:3d}/{count}  "
              f"BTime: {b_time:.3f}s  ITime: {i_time:.3f}s")

    print(f"\n  {'TOTAL':40s}  Baseline: {total_b_correct:3d}/{total_count}  "
          f"Improved: {total_i_correct:3d}/{total_count}  "
          f"BTime: {total_b_time:.3f}s  ITime: {total_i_time:.3f}s")
    if total_b_time > 0:
        print(f"  Overall speedup: {total_b_time / max(total_i_time, 0.0001):.2f}x")
