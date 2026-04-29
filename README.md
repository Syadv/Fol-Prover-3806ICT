# 3806ICT Assignment 1 - FOL Prover

Implementation of Algorithm 2 from Hou's *Fundamentals of Logic and Computation* (2021), plus an improved version with five enhancements.

## Files

- `formula.py` - data structures for terms and formulae, substitution, etc
- `parser.py` - reads FOL formulae from text
- `baseline.py` - Algorithm 2 from p.67 of the textbook
- `improved.py` - the improved prover with 5 enhancements
- `benchmark.py` - runs both provers on 5 datasets and writes a CSV
- `main.py` - command-line interface
- `datasets/` - sample formulae files

## Running it

Quick demo:
```
python3 main.py
```

Prove a single formula:
```
python3 main.py --formula "forall x. P(x) -> exists x. P(x)"
```

Compare baseline vs improved:
```
python3 main.py --compare "forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))"
```

Run the full benchmark (writes `benchmark_results.csv`):
```
python3 main.py --benchmark
```

## Syntax

```
~A   or  !A   or  ¬A
A & B  or  A /\ B
A | B  or  A \/ B
A -> B
forall x. A
exists x. A
True / ⊤      False / ⊥
P, Q, R(x, y), ...
```

Implication is right-associative. Lowest precedence is `->`, then `|`, `&`, `~`, then quantifiers.

## What the improvements do

1. **Iterative deepening** on the number of `forall L`/`exists R` instantiations per branch
2. **Visited-sequent cache** to detect loops on the current branch
3. **Goal-directed term selection** for `forall L`/`exists R`
4. **Eager saturation** of all the non-branching invertible rules before doing anything else
5. **Smallest formula first** when multiple branching rules apply

## Reference

Zhe Hou. *Fundamentals of Logic and Computation*. Springer, 2021.
