r"""Formal specifications (L_spec) for a pilot subset of HumanEval, validated against the reference solutions.

The paper's formal HumanEval specifications ("adapted from the BigCode project and manually
checked", section 9.1) are not public, so these were written from the problems' English
descriptions. Each one is *checked*: for every test input of HumanEval and EvalPlus, the
reference solution's output must satisfy the specification
(:func:`validate`, using ``FormalLLM/lspec/evaluator.py``). A specification the reference
solution violates is wrong and is reported as such.

Scope, stated plainly. L_spec has integers, floats, booleans and read-only arrays; L_pl has
scalar assignment, sequencing, ``if`` and ``while``. So a problem is *expressible* here only if
its result is a single number or boolean and its inputs are numbers or lists of numbers --
about 50 of the 164 problems by signature, and fewer once the spec itself is considered
(strings, list results, and ``sum``/``len``/``%`` have no counterpart). This pilot covers the
problems below; the others are a language extension (see Reading Material/16).

Conventions. A problem that needs a loop lists its working variables in the frame (``Frame: m:int,
i:int.``) because the calculus has no local-variable introduction; the postcondition does not
constrain them, and only ``result`` is returned. A list argument ``l`` comes with an explicit length ``n`` (``bind``), because
L_spec has no ``len``; the function wrapper computes it before the derived body runs.
Parity and divisibility use whole-number division (``k = 2 * (k / 2)``). A boolean result is
stated as ``(t = true /\ C) \/ (t = false /\ ~C)``.
"""
from typing import Any, Dict, List, Optional

# task_id -> dict(name, spec, args, bind, result, tier, note)
#   args:   spec names of the HumanEval parameters, in order
#   bind:   extra spec variables, as Python expressions over the arguments
#   result: the frame variable whose final value the function returns
#   tier:   how hard the derivation is expected to be for this engine
SPECS: Dict[str, Dict[str, Any]] = {
    "HumanEval/41": dict(
        name="car_race_collision", tier="A", args=["n"], bind={}, result="r",
        spec=r"""Frame: r:int.
Precondition: (n:int) := n >= 0.
Postcondition: (n:int) := r = n * n.""",
        note="every one of the n left-to-right cars meets every one of the n right-to-left cars",
    ),
    "HumanEval/157": dict(
        name="right_angle_triangle", tier="A", args=["a", "b", "c"], bind={}, result="t",
        spec=r"""Frame: t:bool.
Precondition: (a:int)(b:int)(c:int) := true.
Postcondition: (a:int)(b:int)(c:int) := (t = true /\ (a * a + b * b = c * c \/ a * a + c * c = b * b \/ b * b + c * c = a * a)) \/ (t = false /\ ~(a * a + b * b = c * c \/ a * a + c * c = b * b \/ b * b + c * c = a * a)).""",
        note="Pythagoras with any side as the hypotenuse",
    ),
    "HumanEval/138": dict(
        name="is_equal_to_sum_even", tier="A", args=["n"], bind={}, result="t",
        spec=r"""Frame: t:bool.
Precondition: (n:int) := true.
Postcondition: (n:int) := (t = true /\ (n >= 8 /\ n = 2 * (n / 2))) \/ (t = false /\ ~(n >= 8 /\ n = 2 * (n / 2))).""",
        note="a sum of four positive even numbers is even and at least 8",
    ),
    "HumanEval/60": dict(
        name="sum_to_n", tier="B", args=["n"], bind={}, result="r",
        spec=r"""Frame: r:int, i:int.
Precondition: (n:int) := n >= 0.
Postcondition: (n:int) := 2 * r = n * (n + 1).""",
        note=("1 + 2 + ... + n, stated in closed form (L_spec has no summation). The counter i is in the frame "
              "because the one-line answer r := n * (n + 1) / 2 needs a lemma the prover does not have (one of "
              "n and n + 1 is even), so the derivation to find is a loop"),
    ),
    "HumanEval/102": dict(
        name="choose_num", tier="B", args=["x", "y"], bind={}, result="r",
        spec=r"""Frame: r:int.
Precondition: (x:int)(y:int) := x > 0 /\ y > 0.
Postcondition: (x:int)(y:int) := (r = -1 /\ (forall (k:int) k < x \/ k > y \/ ~(k = 2 * (k / 2)))) \/ (x <= r /\ r <= y /\ r = 2 * (r / 2) /\ (forall (k:int) k <= r \/ k > y \/ ~(k = 2 * (k / 2)))).""",
        note="the biggest even number in [x, y], or -1 if there is none",
    ),
    "HumanEval/52": dict(
        name="below_threshold", tier="B", args=["l", "t"], bind={"n": "len(l)"}, result="b",
        spec=r"""Frame: b:bool, i:int.
Precondition: (l:array int)(n:int)(t:int) := n >= 0.
Postcondition: (l:array int)(n:int)(t:int) := (b = true /\ (forall (k:int) k < 0 \/ k >= n \/ l[k] < t)) \/ (b = false /\ (exists (k:int) 0 <= k /\ k < n /\ l[k] >= t)).""",
        note="every element is below t (linear search for a counter-example)",
    ),
    "HumanEval/35": dict(
        name="max_element", tier="B", args=["l"], bind={"n": "len(l)"}, result="m",
        spec=r"""Frame: m:int, i:int.
Precondition: (l:array int)(n:int) := n >= 1.
Postcondition: (l:array int)(n:int) := (exists (k:int) 0 <= k /\ k < n /\ l[k] = m) /\ (forall (k:int) k < 0 \/ k >= n \/ l[k] <= m).""",
        note="the maximum: it occurs in the list and nothing is larger",
    ),
    "HumanEval/13": dict(
        name="greatest_common_divisor", tier="C", args=["a", "b"], bind={}, result="g",
        spec=r"""Frame: g:int, x:int, y:int.
Precondition: (a:int)(b:int) := a > 0 /\ b > 0.
Postcondition: (a:int)(b:int) := g > 0 /\ a = g * (a / g) /\ b = g * (b / g) /\ (forall (d:int) d <= 0 \/ d > a \/ (~(a = d * (a / d) /\ b = d * (b / d))) \/ d <= g).""",
        note="a common divisor that no larger common divisor exceeds",
    ),
    "HumanEval/31": dict(
        name="is_prime", tier="C", args=["n"], bind={}, result="t",
        spec=r"""Frame: t:bool, k:int.
Precondition: (n:int) := true.
Postcondition: (n:int) := (t = true /\ n >= 2 /\ (forall (k:int) k < 2 \/ k >= n \/ (~(n = k * (n / k))))) \/ (t = false /\ (n < 2 \/ (exists (k:int) 2 <= k /\ k < n /\ n = k * (n / k)))).""",
        note="no divisor between 2 and n - 1",
    ),
    "HumanEval/24": dict(
        name="largest_divisor", tier="C", args=["n"], bind={}, result="r",
        spec=r"""Frame: r:int, d:int.
Precondition: (n:int) := n > 1.
Postcondition: (n:int) := 1 <= r /\ r < n /\ n = r * (n / r) /\ (forall (d:int) d <= r \/ d >= n \/ ~(n = d * (n / d))).""",
        note="the largest divisor of n smaller than n",
    ),
    "HumanEval/77": dict(
        name="iscube", tier="C", args=["a"], bind={}, result="t",
        spec=r"""Frame: t:bool, k:int.
Precondition: (a:int) := true.
Postcondition: (a:int) := (t = true /\ (exists (k:int) k * k * k = a)) \/ (t = false /\ ~(exists (k:int) k * k * k = a)).""",
        note="a is the cube of an integer (possibly negative)",
    ),
    "HumanEval/0": dict(
        name="has_close_elements", tier="C", args=["numbers", "threshold"], bind={"n": "len(numbers)"}, result="b",
        spec=r"""Frame: b:bool, i:int, j:int.
Precondition: (numbers:array float)(n:int)(threshold:float) := n >= 0.
Postcondition: (numbers:array float)(n:int)(threshold:float) := (b = true /\ (exists (i:int) (j:int) 0 <= i /\ i < n /\ 0 <= j /\ j < n /\ i <> j /\ numbers[i] - numbers[j] < threshold /\ numbers[j] - numbers[i] < threshold)) \/ (b = false /\ (~(exists (i:int) (j:int) 0 <= i /\ i < n /\ 0 <= j /\ j < n /\ i <> j /\ numbers[i] - numbers[j] < threshold /\ numbers[j] - numbers[i] < threshold))).""",
        note="some two different positions hold numbers closer than the threshold",
    ),
    # --- added 2026-10-04: the remaining class-A problems that need no sum, length, string or power ---
    "HumanEval/53": dict(
        name="add", tier="A", args=["x", "y"], bind={}, result="r", added="2026-10-04",
        spec=r"""Frame: r:int.
Precondition: (x:int)(y:int) := true.
Postcondition: (x:int)(y:int) := r = x + y.""",
        note="the sum of two integers",
    ),
    "HumanEval/45": dict(
        name="triangle_area", tier="A", args=["a", "h"], bind={}, result="r", added="2026-10-04",
        spec=r"""Frame: r:float.
Precondition: (a:float)(h:float) := true.
Postcondition: (a:float)(h:float) := r = a * h / 2.""",
        note="area of a triangle from a side and its height (exact arithmetic on floats)",
    ),
    "HumanEval/97": dict(
        name="multiply", tier="A", args=["a", "b"], bind={}, result="r", added="2026-10-04",
        spec=r"""Frame: r:int.
Precondition: (a:int)(b:int) := true.
Postcondition: (a:int)(b:int) := (a >= 0 /\ b >= 0 /\ r = (a - 10 * (a / 10)) * (b - 10 * (b / 10))) \/ (a < 0 /\ b >= 0 /\ r = ((0 - a) - 10 * ((0 - a) / 10)) * (b - 10 * (b / 10))) \/ (a >= 0 /\ b < 0 /\ r = (a - 10 * (a / 10)) * ((0 - b) - 10 * ((0 - b) / 10))) \/ (a < 0 /\ b < 0 /\ r = ((0 - a) - 10 * ((0 - a) / 10)) * ((0 - b) - 10 * ((0 - b) / 10))).""",
        note=("product of the last decimal digits, as the reference computes it: int(str(a)[-1]), the last "
              "digit of |a|. The four sign cases spell out |a| and |b| (the language has no abs)"),
    ),
    "HumanEval/150": dict(
        name="x_or_y", tier="C", args=["n", "x", "y"], bind={}, result="r", added="2026-10-04",
        spec=r"""Frame: r:int, k:int.
Precondition: (n:int)(x:int)(y:int) := true.
Postcondition: (n:int)(x:int)(y:int) := (r = x /\ n >= 2 /\ (forall (k:int) k < 2 \/ k >= n \/ ~(n = k * (n / k)))) \/ (r = y /\ (n < 2 \/ (exists (k:int) 2 <= k /\ k < n /\ n = k * (n / k)))).""",
        note="x if n is prime, otherwise y",
    ),
    "HumanEval/57": dict(
        name="monotonic", tier="C", args=["l"], bind={"n": "len(l)"}, result="t", added="2026-10-04",
        spec=r"""Frame: t:bool, i:int, u:bool, w:bool.
Precondition: (l:array int)(n:int) := n >= 0.
Postcondition: (l:array int)(n:int) := (t = true /\ ((forall (k:int) k < 0 \/ k + 1 >= n \/ l[k] <= l[k + 1]) \/ (forall (k:int) k < 0 \/ k + 1 >= n \/ l[k] >= l[k + 1]))) \/ (t = false /\ (exists (k:int) 0 <= k /\ k + 1 < n /\ l[k] > l[k + 1]) /\ (exists (k:int) 0 <= k /\ k + 1 < n /\ l[k] < l[k + 1])).""",
        note="the list never decreases or never increases (two flags in one pass)",
    ),
    "HumanEval/135": dict(
        name="can_arrange", tier="B", args=["arr"], bind={"n": "len(arr)"}, result="r", added="2026-10-04",
        spec=r"""Frame: r:int, i:int.
Precondition: (arr:array int)(n:int) := n >= 0.
Postcondition: (arr:array int)(n:int) := (r = -1 /\ (forall (k:int) k < 1 \/ k >= n \/ arr[k] >= arr[k - 1])) \/ (1 <= r /\ r < n /\ arr[r] < arr[r - 1] /\ (forall (k:int) k <= r \/ k >= n \/ arr[k] >= arr[k - 1])).""",
        note="the last position whose element is smaller than the one before it, or -1",
    ),
    "HumanEval/43": dict(
        name="pairs_sum_to_zero", tier="C", args=["l"], bind={"n": "len(l)"}, result="t", added="2026-10-04",
        spec=r"""Frame: t:bool, i:int, j:int.
Precondition: (l:array int)(n:int) := n >= 0.
Postcondition: (l:array int)(n:int) := (t = true /\ (exists (i:int) (j:int) 0 <= i /\ i < j /\ j < n /\ l[i] + l[j] = 0)) \/ (t = false /\ (~(exists (i:int) (j:int) 0 <= i /\ i < j /\ j < n /\ l[i] + l[j] = 0))).""",
        note="two different positions hold numbers that add up to zero",
    ),
    "HumanEval/40": dict(
        name="triples_sum_to_zero", tier="C", args=["l"], bind={"n": "len(l)"}, result="t", added="2026-10-04",
        spec=r"""Frame: t:bool, i:int, j:int, k:int.
Precondition: (l:array int)(n:int) := n >= 0.
Postcondition: (l:array int)(n:int) := (t = true /\ (exists (i:int) (j:int) (k:int) 0 <= i /\ i < j /\ j < k /\ k < n /\ l[i] + l[j] + l[k] = 0)) \/ (t = false /\ (~(exists (i:int) (j:int) (k:int) 0 <= i /\ i < j /\ j < k /\ k < n /\ l[i] + l[j] + l[k] = 0))).""",
        note="three different positions hold numbers that add up to zero",
    ),
}


def environment(task_id: str, arguments: List[Any]) -> Dict[str, Any]:
    """The values of the spec's input names for one test input of the problem."""
    entry = SPECS[task_id]
    env = dict(zip(entry["args"], arguments))
    for name, expression in entry["bind"].items():
        env[name] = eval(expression, {"len": len}, dict(env))          # trusted: written in this file
    return env


def validate(task_ids: Optional[List[str]] = None, plus: bool = True, limit: Optional[int] = None) -> Dict[str, dict]:
    """Check each specification against the reference solution on every test input.

    Returns ``{task_id: {"checked": n, "failures": [(input, message), ...]}}``.
    """
    from benchmarks.datasets import humaneval as he
    from FormalLLM.lspec.evaluator import check_specification
    from FormalLLM.lspec.parser import parse_spec

    problems, truth = he.load_problems(), he.groundtruth()
    report: Dict[str, dict] = {}
    for task_id in (task_ids or list(SPECS)):
        entry = SPECS[task_id]
        spec = parse_spec(entry["spec"])
        inputs = list(problems[task_id]["base_input"]) + (list(problems[task_id]["plus_input"]) if plus else [])
        expected = list(truth[task_id]["base"]) + (list(truth[task_id]["plus"]) if plus else [])
        if limit:
            inputs, expected = inputs[:limit], expected[:limit]
        failures, inconclusive = [], 0
        for arguments, output in zip(inputs, expected):
            message = check_specification(spec, environment(task_id, arguments), {entry["result"]: output})
            if message and "too many values" in message:
                inconclusive += 1            # a range too large to enumerate: neither confirmed nor refuted
            elif message:
                failures.append((arguments, output, message))
        report[task_id] = {"name": entry["name"], "checked": len(inputs) - inconclusive,
                           "inconclusive": inconclusive, "failures": failures}
    return report


def strength(task_ids: Optional[List[str]] = None, plus: bool = False) -> Dict[str, dict]:
    """How much does each specification actually constrain? (The other half of validation.)

    :func:`validate` shows a specification is not *wrong*; a specification that accepted every
    output would pass it too. Here each reference output is replaced by a wrong one (a boolean
    flipped, a number moved by 1 or doubled) and the specification must reject it. The *kill rate*
    is the fraction of wrong outputs rejected; 1.0 means the specification pins the answer down on
    the inputs tried.
    """
    from benchmarks.datasets import humaneval as he
    from FormalLLM.lspec.evaluator import EvaluationError, check_specification
    from FormalLLM.lspec.parser import parse_spec

    problems, truth = he.load_problems(), he.groundtruth()
    report: Dict[str, dict] = {}
    for task_id in (task_ids or list(SPECS)):
        entry = SPECS[task_id]
        spec = parse_spec(entry["spec"])
        inputs = list(problems[task_id]["base_input"]) + (list(problems[task_id]["plus_input"]) if plus else [])
        expected = list(truth[task_id]["base"]) + (list(truth[task_id]["plus"]) if plus else [])
        tried = killed = 0
        survivors = []
        for arguments, output in zip(inputs, expected):
            env = environment(task_id, arguments)
            if isinstance(output, bool):
                wrong = [not output]
            else:
                wrong = [output + 1, output - 1, output * 2 if output else 7]
            for candidate in wrong:
                if candidate == output:
                    continue
                try:
                    message = check_specification(spec, env, {entry["result"]: candidate})
                except EvaluationError:
                    continue
                if message and "too many values" in message:
                    continue
                tried += 1
                if message:
                    killed += 1
                elif len(survivors) < 3:
                    survivors.append((arguments, candidate))
        report[task_id] = {"name": entry["name"], "tried": tried, "killed": killed,
                           "rate": (killed / tried) if tried else None, "survivors": survivors}
    return report


def main() -> int:
    report = validate()
    bad = 0
    for task_id, row in report.items():
        status = "ok" if not row["failures"] else f"{len(row['failures'])} FAILURES"
        extra = f" (+{row['inconclusive']} too large to enumerate)" if row["inconclusive"] else ""
        print(f"{task_id:14s} {row['name']:26s} {row['checked']:5d} inputs  {status}{extra}")
        for arguments, output, message in row["failures"][:2]:
            print(f"    {message}: input={str(arguments)[:80]} reference output={output}")
        bad += bool(row["failures"])
    print(f"\n{len(report) - bad} of {len(report)} specifications agree with the reference solution on every test input")
    print("\nstrength (wrong outputs rejected, original tests' inputs):")
    for task_id, row in strength().items():
        rate = "n/a" if row["rate"] is None else f"{row['rate']:.0%}"
        print(f"  {task_id:14s} {row['name']:26s} {row['killed']:4d} of {row['tried']:4d} wrong outputs rejected ({rate})")
        for arguments, candidate in row["survivors"][:2]:
            print(f"      accepted wrong output {candidate} for input {str(arguments)[:70]}")
    return 1 if bad else 0


if __name__ == "__main__":
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
    sys.exit(main())
