r"""Hand-written derivations of the HumanEval pilot problems, checked by the engine and run on the real tests. No model.

``he_refine`` asks the model to find a derivation. Before reading its score it helps to know the ceiling:
for which problems does a derivation exist that this engine accepts step by step, and does the program
it gives pass the real HumanEval and EvalPlus tests? Each entry below is a derivation written by a
person (the same moves a model has to find: which law, which invariant, which middle assertion). The tool
applies it law by law, every step proved by Z3, emits the Python, wraps it as the HumanEval function and
runs the original and the EvalPlus tests.

    python -m benchmarks.datasets.he_oracle                  # every problem that has an entry
    python -m benchmarks.datasets.he_oracle --tasks A B      # by tier, or by task id

A problem without an entry was not derived by hand: ``HumanEval/0`` and ``HumanEval/43`` need two nested loops
with an existential over pairs, ``HumanEval/40`` three over triples. That is not a proof that no derivation exists,
only that none was written.
Three entries (``13``, ``31``, ``77``) are proved correct but are linear searches, too slow for EvalPlus's
largest inputs: they pass the original tests and time out on the EvalPlus ones.

What a model run cannot beat: if a problem is listed here, a failure of the model on it is a failure to
*find* the derivation, not a limit of the engine.
"""
import argparse
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from benchmarks.classic import Derivation, alt, asg, seq               # noqa: E402
from FormalLLM.llm.parser import parse_expr                             # noqa: E402


def loop(d, node, invariant, guard, variant, init, body):
    """``initialised_iteration`` on ``node``, then the derivation trees of its set-up and its body."""
    roles = d._step(node, "initialised_iteration",
                    dict(invariant=parse_expr(invariant), guard=parse_expr(guard), variant=parse_expr(variant)))
    d.tree(roles["init"], init)
    d.tree(roles["body"], body)


def loop_then(d, middle, invariant, guard, variant, init, body, last):
    """A loop that establishes ``middle``, followed by one assignment."""
    roles = d._step(d.graph.root_id, "sequential", {"intermediate": parse_expr(middle)})
    loop(d, roles["part1"], invariant, guard, variant, init, body)
    d.tree(roles["part2"], last)


def t41(d):
    d.tree(d.graph.root_id, asg("r", "n * n"))


def t157(d):
    d.tree(d.graph.root_id, asg(
        "t", "a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a"))


def t138(d):
    d.tree(d.graph.root_id, asg("t", "n >= 8 && n = 2 * (n / 2)"))


def t60(d):
    # the closed form r := n * (n + 1) / 2 needs "one of n, n + 1 is even", which Z3 cannot see; a loop does not
    loop(d, d.graph.root_id, "0 <= i && i <= n && 2 * r = i * (i + 1)", "i < n", "n - i",
         seq("r = 0", asg("r", "0"), asg("i", "0")),
         seq("0 <= i && i < n && n - i = V0 && 2 * r = (i + 1) * (i + 2)", asg("r", "r + i + 1"), asg("i", "i + 1")))


def t102(d):
    d.tree(d.graph.root_id,
           alt("x > y", asg("r", "-1"),
               alt("y = 2 * (y / 2)", asg("r", "y"),
                   alt("y - 1 >= x", asg("r", "y - 1"), asg("r", "-1")))))


def t52(d):
    invariant = ("0 <= i && i <= n && ((b = true && (forall (k:int) (k < 0 \\/ k >= i \\/ l[k] < t))) "
                 "\\/ (b = false && (exists (k:int) (0 <= k /\\ k < i /\\ l[k] >= t))))")
    middle = ("0 <= i && i < n && n - i = V0 && ((b = true && (forall (k:int) (k < 0 \\/ k >= i + 1 \\/ l[k] < t))) "
              "\\/ (b = false && (exists (k:int) (0 <= k /\\ k < i + 1 /\\ l[k] >= t))))")
    loop(d, d.graph.root_id, invariant, "i < n", "n - i",
         seq("b = true", asg("b", "true"), asg("i", "0")),
         seq(middle, asg("b", "b && l[i] < t"), asg("i", "i + 1")))


def t35(d):
    invariant = ("1 <= i && i <= n && (forall (k:int) (k < 0 \\/ k >= i \\/ l[k] <= m)) && "
                 "(exists (k:int) (k >= 0 /\\ k < i /\\ l[k] = m))")
    middle = "m = l[i] && 1 <= i && i < n && n - i = V0 && (forall (k:int) (k < 0 \\/ k >= i \\/ l[k] <= m))"
    loop(d, d.graph.root_id, invariant, "i < n", "n - i",
         seq("m = l[0]", asg("m", "l[0]"), asg("i", "1")),
         alt("l[i] > m", seq(middle, asg("m", "l[i]"), asg("i", "i + 1")), asg("i", "i + 1")))


def t24(d):
    # search downwards from n - 1 for the first divisor
    divisors = "(forall (k:int) (k <= d \\/ k >= n \\/ ~(n = k * (n / k))))"
    loop_then(d, f"1 <= d && d < n && n = d * (n / d) && {divisors}",
              f"1 <= d && d < n && {divisors}", "~(n = d * (n / d))", "d",
              asg("d", "n - 1"), asg("d", "d - 1"), asg("r", "d"))


def t31(d):
    # n < 2 is not prime; otherwise try k = 2, 3, ... until k divides n or reaches n
    below = "(forall (j:int) (j < 2 \\/ j >= k \\/ ~(n = j * (n / j))))"
    roles = d._step(d.graph.root_id, "alternation", {"guard": parse_expr("n < 2")})
    d.tree(roles["then"], asg("t", "false"))
    inner = d._step(roles["else"], "sequential",
                    {"intermediate": parse_expr(f"2 <= k && k <= n && {below} && (k >= n \\/ n = k * (n / k))")})
    loop(d, inner["part1"], f"2 <= k && k <= n && {below}", "k < n && ~(n = k * (n / k))", "n - k",
         asg("k", "2"), asg("k", "k + 1"))
    d.tree(inner["part2"], asg("t", "k >= n"))


def t13(d):
    # search downwards from a for the largest common divisor
    invariant = "1 <= g && g <= a && (forall (d:int) (d <= g \\/ d > a \\/ ~(a = d * (a / d) /\\ b = d * (b / d))))"
    loop(d, d.graph.root_id, invariant, "~(a = g * (a / g) /\\ b = g * (b / g))", "g",
         asg("g", "a"), asg("g", "g - 1"))


def t77(d):
    # search k = 0, 1, 2, ... (or 0, -1, -2, ...) for the first k whose cube reaches a, then compare
    roles = d._step(d.graph.root_id, "alternation", {"guard": parse_expr("a >= 0")})
    below = "(forall (j:int) (j < 0 \\/ j >= k \\/ j * j * j < a))"
    inner = d._step(roles["then"], "sequential",
                    {"intermediate": parse_expr(f"0 <= k && k <= a + 1 && {below} && k * k * k >= a")})
    loop(d, inner["part1"], f"0 <= k && k <= a + 1 && {below}", "k * k * k < a", "a + 1 - k",
         asg("k", "0"), asg("k", "k + 1"))
    d.tree(inner["part2"], asg("t", "k * k * k = a"))
    above = "(forall (j:int) (j > 0 \\/ j <= k \\/ j * j * j > a))"
    inner = d._step(roles["else"], "sequential",
                    {"intermediate": parse_expr(f"k <= 0 && k >= a - 1 && {above} && k * k * k <= a")})
    loop(d, inner["part1"], f"k <= 0 && k >= a - 1 && {above}", "k * k * k > a", "k - a + 1",
         asg("k", "0"), asg("k", "k - 1"))
    d.tree(inner["part2"], asg("t", "k * k * k = a"))


def t53(d):
    d.tree(d.graph.root_id, asg("r", "x + y"))


def t45(d):
    d.tree(d.graph.root_id, asg("r", "a * h / 2"))


def t97(d):
    # the last digit of |a| and of |b|, one sign case per branch
    da, db = "(a - 10 * (a / 10))", "(b - 10 * (b / 10))"
    na, nb = "((0 - a) - 10 * ((0 - a) / 10))", "((0 - b) - 10 * ((0 - b) / 10))"
    d.tree(d.graph.root_id,
           alt("a >= 0", alt("b >= 0", asg("r", f"{da} * {db}"), asg("r", f"{da} * {nb}")),
               alt("b >= 0", asg("r", f"{na} * {db}"), asg("r", f"{na} * {nb}"))))


def t150(d):
    # as is_prime (31): try k = 2, 3, ... until k divides n or reaches n, then choose x or y
    below = "(forall (j:int) (j < 2 \\/ j >= k \\/ ~(n = j * (n / j))))"
    roles = d._step(d.graph.root_id, "alternation", {"guard": parse_expr("n < 2")})
    d.tree(roles["then"], asg("r", "y"))
    inner = d._step(roles["else"], "sequential",
                    {"intermediate": parse_expr(f"2 <= k && k <= n && {below} && (k >= n \\/ n = k * (n / k))")})
    loop(d, inner["part1"], f"2 <= k && k <= n && {below}", "k < n && ~(n = k * (n / k))", "n - k",
         asg("k", "2"), asg("k", "k + 1"))
    d.tree(inner["part2"], alt("k >= n", asg("r", "x"), asg("r", "y")))


def t135(d):
    # scan i = 1 .. n - 1 and remember the last position where the list goes down
    def seen(i):
        return (f"((r = -1 && (forall (k:int) (k < 1 \\/ k >= {i} \\/ arr[k] >= arr[k - 1]))) \\/ "
                f"(1 <= r && r < {i} && arr[r] < arr[r - 1] && "
                f"(forall (k:int) (k <= r \\/ k >= {i} \\/ arr[k] >= arr[k - 1]))))")
    invariant = f"1 <= i && (i <= n \\/ (n <= 1 && i = 1)) && {seen('i')}"
    middle = f"1 <= i && i < n && n - i = V0 && {seen('i + 1')}"
    loop(d, d.graph.root_id, invariant, "i < n", "n - i",
         seq("r = -1", asg("r", "-1"), asg("i", "1")),
         seq(middle, alt("arr[i] < arr[i - 1]", asg("r", "i"), asg("r", "r")), asg("i", "i + 1")))


def t57(d):
    # one pass, two flags: u = "never went down so far", w = "never went up so far"
    def flags(i):
        never_down = f"(forall (k:int) (k < 0 \\/ k >= {i} \\/ l[k] <= l[k + 1]))"
        never_up = f"(forall (k:int) (k < 0 \\/ k >= {i} \\/ l[k] >= l[k + 1]))"
        went_down = f"(exists (k:int) (0 <= k /\\ k < {i} /\\ l[k] > l[k + 1]))"
        went_up = f"(exists (k:int) (0 <= k /\\ k < {i} /\\ l[k] < l[k + 1]))"
        return (f"((u = true && {never_down}) \\/ (u = false && {went_down})) && "
                f"((w = true && {never_up}) \\/ (w = false && {went_up}))")
    invariant = f"0 <= i && (i + 1 <= n \\/ i = 0) && {flags('i')}"
    first = (f"0 <= i && i + 1 < n && n - i = V0 && "
             f"((u = true && (forall (k:int) (k < 0 \\/ k >= i + 1 \\/ l[k] <= l[k + 1]))) \\/ "
             f"(u = false && (exists (k:int) (0 <= k /\\ k < i + 1 /\\ l[k] > l[k + 1])))) && "
             f"((w = true && (forall (k:int) (k < 0 \\/ k >= i \\/ l[k] >= l[k + 1]))) \\/ "
             f"(w = false && (exists (k:int) (0 <= k /\\ k < i /\\ l[k] < l[k + 1]))))")
    second = f"0 <= i && i + 1 < n && n - i = V0 && {flags('i + 1')}"
    loop_then(d, f"{invariant} && i + 1 >= n", invariant, "i + 1 < n", "n - i",
              seq("u = true", asg("u", "true"), seq("u = true && w = true", asg("w", "true"), asg("i", "0"))),
              seq(first, asg("u", "u && l[i] <= l[i + 1]"),
                  seq(second, asg("w", "w && l[i] >= l[i + 1]"), asg("i", "i + 1"))),
              asg("t", "u || w"))


ORACLE = {"HumanEval/41": t41, "HumanEval/157": t157, "HumanEval/138": t138, "HumanEval/60": t60,
          "HumanEval/102": t102, "HumanEval/52": t52, "HumanEval/35": t35, "HumanEval/24": t24,
          "HumanEval/31": t31, "HumanEval/13": t13, "HumanEval/77": t77,
          "HumanEval/53": t53, "HumanEval/45": t45, "HumanEval/97": t97, "HumanEval/150": t150,
          "HumanEval/135": t135, "HumanEval/57": t57}


def check(task_id: str) -> dict:
    """Derive ``task_id`` by hand, emit and test the program; the row says what happened."""
    from benchmarks.datasets import humaneval as he
    from benchmarks.datasets.he_refine import build_solution
    from benchmarks.datasets.he_specs import SPECS
    from FormalLLM.llm.transport import NETWORK  # noqa: F401  (imported only to fail early on a broken checkout)
    from FormalLLM.lpl.typed_python import python_for
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import VerificationError

    entry = SPECS[task_id]
    row = {"task_id": task_id, "name": entry["name"], "tier": entry["tier"], "complete": False,
           "steps": 0, "z3_s": 0.0, "base": None, "plus": None, "python": None, "error": ""}
    d = Derivation(entry["spec"])
    started = time.time()
    try:
        ORACLE[task_id](d)
        row["complete"] = bool(d.graph.is_complete(d.graph.root_id))
    except VerificationError as error:
        row["error"] = " ".join(str(error).split())[:300]
    row["steps"], row["z3_s"] = sum(d.steps.values()), round(d.prove_seconds, 2)
    if row["complete"]:
        row["python"] = python_for(d.graph.reconstruct_program(), parse_spec(entry["spec"]))
        result = he.run_tests(task_id, build_solution(task_id, row["python"]), plus=True)
        row["base"], row["plus"] = result.base, result.plus
    row["wall_s"] = round(time.time() - started, 1)
    return row


def main(argv=None) -> int:
    from benchmarks.datasets.he_specs import SPECS
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--tasks", nargs="*", default=None, help="task ids, tiers (A B C) or 'all'")
    ap.add_argument("--show", action="store_true", help="print the emitted Python of every derivation")
    args = ap.parse_args(argv)
    wanted = [t for t in SPECS if t in ORACLE and (args.tasks in (None, ["all"]) or t in args.tasks
                                                   or SPECS[t]["tier"] in args.tasks)]
    print(f"{'task':14s} {'problem':24s} {'tier':4s} {'steps':>5s} {'Z3 s':>6s}  derived  base  plus")
    failures = 0
    for task_id in wanted:
        row = check(task_id)
        ok = row["complete"] and row["base"] == "pass" and row["plus"] == "pass"
        failures += 0 if ok else 1
        print(f"{task_id:14s} {row['name']:24s} {row['tier']:4s} {row['steps']:5d} {row['z3_s']:6.2f}  "
              f"{'yes' if row['complete'] else 'NO ':7s}  {str(row['base']):4s}  {str(row['plus']):4s}"
              + (f"   {row['error']}" if row["error"] else ""), flush=True)
        if args.show and row["python"]:
            print("    " + row["python"].replace("\n", "\n    "))
    missing = [t for t in SPECS if t not in ORACLE]
    if missing:
        print("no derivation by hand: " + ", ".join(missing))
    print(f"{len(wanted) - failures} of {len(wanted)} derived by hand and passing every test")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
