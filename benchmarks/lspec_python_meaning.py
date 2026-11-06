"""Does L_spec mean what Python means? Each case is evaluated twice: as Python (``eval``) and, translated, by Lean
(``#eval``), on the same concrete values, and the two results are compared.

    python benchmarks/lspec_python_meaning.py

Most cases must agree. The cases marked ``differs`` are the places where L_spec keeps Lean's meaning (natural-number
subtraction, rounding of ``//`` and ``%`` with a negative divisor, an index past the end); there the test checks that
the difference is exactly the one the cheat sheet documents, so the documentation is checked too.

Writes ``benchmarks/results/lspec/python_meaning.jsonl``."""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.dsl import steps  # noqa: E402

I, N, S, C, B = "Int", "Nat", "String", "Char", "Bool"
L_INT, L_NAT, L_STR = "List Int", "List Nat", "List String"

#: (python, L_spec (None: the same text), {name: (value, Lean type)}, expected: "same" | (Lean's value, why))
CASES = [
    ("[x * 2 for x in l if x > 0]", None, {"l": ([3, -1, 4], L_INT)}, "same"),
    ("[x for x in l if x % 2 == 0]", None, {"l": ([1, 2, 3, 4], L_NAT)}, "same"),
    ("[x + 1 for x in l]", None, {"l": ([1, 2], L_NAT)}, "same"),
    ("sum(x * x for x in l)", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("any(x < 0 for x in l)", None, {"l": ([1, -2], L_INT)}, "same"),
    ("any(x < 0 for x in l)", None, {"l": ([1, 2], L_INT)}, "same"),
    ("all(x > 0 for x in l if x != 0)", None, {"l": ([1, 0, 2], L_INT)}, "same"),
    ("list(range(2, n))", "range(2, n)", {"n": (5, N)}, "same"),
    ("list(range(5, n))", "range(5, n)", {"n": (2, N)}, "same"),
    ("list(range(n))", "range(n)", {"n": (4, N)}, "same"),
    ("l[-1]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("l[:-1]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("l[-2:]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("l[1:3]", None, {"l": ([1, 2, 3, 4], L_INT)}, "same"),
    ("l[::-1]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("l[:2]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("l[1:]", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("s[1:3]", "String.mk(list(s)[1:3])", {"s": ("abcd", S)}, "same"),     # a str slice is sliced as a list
    ("0 <= i < len(l)", None, {"i": (1, N), "l": ([5, 6], L_INT)}, "same"),
    ("0 <= i < len(l)", None, {"i": (2, N), "l": ([5, 6], L_INT)}, "same"),
    ('", ".join(ws)', None, {"ws": (["a", "b"], L_STR)}, "same"),
    ('s.split(",")', None, {"s": ("a,,b", S)}, "same"),
    ("s.upper()", None, {"s": ("aB1", S)}, "same"),
    ("s.lower()", None, {"s": ("aB1", S)}, "same"),
    ("s.strip()", None, {"s": ("  ab \n", S)}, "same"),
    ('s.startswith("ab")', None, {"s": ("abc", S)}, "same"),
    ('s.endswith("bc")', None, {"s": ("abc", S)}, "same"),
    ("c.isdigit()", None, {"c": ("5", C)}, "same"),
    ("c.isalpha()", None, {"c": ("5", C)}, "same"),
    ("len(l)", None, {"l": ([3, 1, 2], L_INT)}, "same"),
    ("sum(l)", None, {"l": ([3, 1, 2], L_INT)}, "same"),
    ("sorted(l)", None, {"l": ([3, 1, 2], L_INT)}, "same"),
    ("list(reversed(l))", "reversed(l)", {"l": ([3, 1, 2], L_INT)}, "same"),
    ("abs(x)", None, {"x": (-3, I)}, "same"),
    ("x ** 3", None, {"x": (-2, I)}, "same"),
    ("max(a, b)", None, {"a": (2, I), "b": (5, I)}, "same"),
    ("min(a, b)", None, {"a": (2, I), "b": (5, I)}, "same"),
    ("bool(x > 2)", None, {"x": (3, N)}, "same"),
    ("str(n)", None, {"n": (42, N)}, "same"),
    ("l.count(2)", None, {"l": ([2, 1, 2], L_INT)}, "same"),
    ("l.index(2)", None, {"l": ([1, 2, 3], L_INT)}, "same"),
    ("x in l", None, {"x": (2, I), "l": ([1, 2], L_INT)}, "same"),
    ("x not in l", None, {"x": (2, I), "l": ([1, 2], L_INT)}, "same"),
    ("a + b * c", None, {"a": (1, I), "b": (2, I), "c": (3, I)}, "same"),
    ("a - b - c", None, {"a": (10, I), "b": (3, I), "c": (2, I)}, "same"),
    ("x if x > 0 else -x", None, {"x": (-4, I)}, "same"),
    ("a // b", "a / b", {"a": (7, I), "b": (2, I)}, "same"),
    ("a // b", "a / b", {"a": (-7, I), "b": (2, I)}, "same"),
    ("a % b", None, {"a": (-7, I), "b": (3, I)}, "same"),
    ("a % b", None, {"a": (7, I), "b": (3, I)}, "same"),
    # where L_spec keeps Lean's meaning (the cheat sheet says so)
    ("a - b", None, {"a": (2, N), "b": (5, N)}, ("0", "nat subtraction stops at 0")),
    ("a // b", "a / b", {"a": (7, I), "b": (-2, I)}, ("-3", "negative divisor: Lean rounds the quotient differently")),
    ("a % b", None, {"a": (7, I), "b": (-2, I)}, ("1", "negative divisor: the remainder is never negative in Lean")),
    ("l[5]", None, {"l": ([1, 2], L_INT)}, ("0", "past the end: the default value, not an error")),
    ("a // b", "a / b", {"a": (7, I), "b": (0, I)}, ("0", "division by zero is 0, not an error")),
]


def lean_literal(value, typ: str) -> str:
    if typ.startswith("List "):
        inner = typ[5:]
        return "([" + ", ".join(lean_literal(v, inner) for v in value) + f"] : {typ})"
    if typ == C:
        return f"'{value}'"
    if typ == S:
        return json.dumps(value)
    if typ == B:
        return "true" if value else "false"
    return f"({value} : {typ})"


def lean_shown(value) -> str:
    """A Python value the way Lean's ``#eval`` prints the corresponding Lean value."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(lean_shown(v) for v in value) + "]"
    return str(value)


def main():
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", "python_meaning.jsonl")
    rows = []
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        for python, spec, env, expected in CASES:
            spec = spec or python
            try:
                py = lean_shown(eval(python, {}, {k: v for k, (v, _) in env.items()}))
            except Exception as error:
                py = f"error: {type(error).__name__}"
            try:
                lean_text = steps.to_lean(spec, "case")
            except steps.StepError as error:
                rows.append({"python": python, "lspec": spec, "ok": False, "error": str(error)})
                print(f"FAIL  {spec:32s} does not translate: {error}")
                continue
            lets = "".join(f"let {k} : {t} := {lean_literal(v, t)}; " for k, (v, t) in env.items())
            reply = lean.run(f"#eval ({lets}({lean_text}))\n", timeout=120)
            shown = [i for i in reply.infos if not i.startswith("PANIC")]     # `l[5]!` warns, then is the default
            got = shown[-1].strip() if shown and not reply.errors else "error: " + (reply.errors or ["?"])[0][:200]
            if expected == "same":
                ok, why = got == py, ""
            else:
                ok, why = got == expected[0] and got != py, expected[1]
            rows.append({"python": python, "lspec": spec, "lean": lean_text, "env": {k: v for k, (v, _) in env.items()},
                         "python_value": py, "lean_value": got, "expected": "same" if expected == "same" else "differs",
                         "why": why, "ok": ok})
            print(f"{'ok  ' if ok else 'FAIL'}  {spec:32s} python {py:16s} lean {got:16s} {why}")
    with open(out, "w", encoding="utf8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    same = [r for r in rows if r.get("expected") == "same"]
    differs = [r for r in rows if r.get("expected") == "differs"]
    print(f"{sum(r['ok'] for r in same)}/{len(same)} cases mean the same in Python and Lean; "
          f"{sum(r['ok'] for r in differs)}/{len(differs)} documented differences confirmed; "
          f"{sum(not r['ok'] for r in rows)} failures")


if __name__ == "__main__":
    main()
