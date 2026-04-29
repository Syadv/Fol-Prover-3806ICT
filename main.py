"""
CLI entry point. Examples:

  python3 main.py
      runs a quick demo with a handful of formulae

  python3 main.py --formula "A -> A"
      proves a single formula

  python3 main.py --file datasets/fol_benchmark.txt
      proves every formula in the file

  python3 main.py --compare "(forall x. P(x)) -> exists x. P(x)"
      runs both provers and shows the speedup

  python3 main.py --benchmark
      full benchmark across all 5 datasets, writes CSV
"""
import argparse
import sys
from parser import parse_formula, parse_file
from baseline import BaselineProver
from improved import ImprovedProver


def main():
    ap = argparse.ArgumentParser(description="FOL theorem prover (LK' backward search)")
    ap.add_argument("--file", "-f", help="file with one formula per line")
    ap.add_argument("--formula", "-e", help="single formula to prove")
    ap.add_argument("--benchmark", "-b", action="store_true", help="run the full benchmark")
    ap.add_argument("--compare", "-c", help="compare baseline vs improved on one formula")
    ap.add_argument("--mode", choices=["baseline", "improved", "both"], default="improved")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--max-steps", type=int, default=50000)
    args = ap.parse_args()

    if args.benchmark:
        # benchmark mode just delegates to benchmark.py
        from benchmark import run_benchmark, gen_propositional_tautologies, \
            gen_propositional_non_tautologies, gen_fol_valid, gen_fol_invalid, gen_hard_fol, \
            save_results_csv

        datasets = {
            "Propositional Tautologies":     gen_propositional_tautologies(30),
            "Propositional Non-Tautologies": gen_propositional_non_tautologies(20),
            "FOL Valid":                      gen_fol_valid(25),
            "FOL Invalid":                    gen_fol_invalid(6),
            "Hard FOL (Stress Test)":         gen_hard_fol(),
        }
        all_results = {}
        for name, dataset in datasets.items():
            results = run_benchmark(name, dataset, timeout=args.timeout, max_steps=args.max_steps)
            all_results[name] = results
        save_results_csv(all_results, "benchmark_results.csv")
        return

    if args.compare:
        # side-by-side run for one formula
        f = parse_formula(args.compare)
        print(f"Formula: {f}")
        print()

        bp = BaselineProver(max_steps=args.max_steps, timeout=args.timeout)
        br = bp.prove(f)
        print(f"  Baseline:  {br}")

        ip = ImprovedProver(max_steps=args.max_steps * 2, timeout=args.timeout)
        ir = ip.prove(f)
        print(f"  Improved:  {ir}")

        if br.time_s > 0:
            print(f"  Speedup:   {br.time_s / max(ir.time_s, 0.0001):.2f}x")
        return

    # otherwise: prove a formula or a file of them
    if args.formula:
        formulae = [parse_formula(args.formula)]
    elif args.file:
        formulae = parse_file(args.file)
    else:
        # no arguments - demo mode
        demo = [
            "A -> A",
            "(A -> B) -> ((~A -> B) -> B)",
            "A | ~A",
            "forall x. P(x) -> exists x. P(x)",
            "~(forall x. P(x)) -> exists x. ~P(x)",
            "forall x. (P(x) -> Q(x)) -> (forall x. P(x) -> forall x. Q(x))",
            "exists x. P(x) -> forall x. P(x)",
            "A -> B",
        ]
        formulae = [parse_formula(t) for t in demo]

    for f in formulae:
        if args.mode in ("baseline", "both"):
            bp = BaselineProver(max_steps=args.max_steps, timeout=args.timeout)
            br = bp.prove(f)
            print(f"[Baseline]  {f}  =>  {br}")

        if args.mode in ("improved", "both"):
            ip = ImprovedProver(max_steps=args.max_steps * 2, timeout=args.timeout)
            ir = ip.prove(f)
            print(f"[Improved]  {f}  =>  {ir}")

        if args.mode == "both":
            print()


if __name__ == "__main__":
    main()
