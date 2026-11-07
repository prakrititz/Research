"""The L_spec language reference given to the model, generated from the registry (``ops.py``) and from Lean examples
translated by the tooling itself: every example is ``lspec_syntax.show(lean_syntax.parse(lean))`` and must read back to
the same tree, so the sheet cannot disagree with the parser.

    python -m FormalLLM.dsl.cheatsheet            # print it (and check every example)"""
from FormalLLM.dsl import lean_syntax, lspec_syntax, ops
from FormalLLM.dsl.normal import normal

#: (topic, Lean) pairs: the L_spec column is computed
EXAMPLES = [
    ("logic", "a ∧ b ∨ ¬c → d ↔ e"),
    ("comparison", "x ≤ y ∧ y ≠ z ∧ p = q"),
    ("Boolean equality (BEq)", "(c == 'a') = true"),
    ("power, division, modulo", "x ^ 2 / 3 % 5"),
    ("divisibility", "3 ∣ n"),
    ("membership", "x ∈ l ∧ y ∉ l"),
    ("for all, bounded by a list", "∀ x ∈ l, x > 0"),
    ("for all, bounded by a number", "∀ i < l.length, l[i]! ≥ 0"),
    ("for all, typed", "∀ (i j : Nat), i < j → j < n → a[i]! ≤ a[j]!"),
    ("there exists", "∃ k, k < n ∧ l[k]! = x"),
    ("function", "fun x => x * 2"),
    ("function on a pair", "fun acc (s, e) => acc + (e - s)"),
    ("conditional", "if x > 0 then x else -x"),
    ("local definition", "let m := l.length / 2; l.take m"),
    ("indexing (default if out of range)", "l[i]!"),
    ("indexing (Option)", "l[i]?"),
    ("prefix, suffix", "l.take k ++ l.drop k"),
    ("length, sum, reverse", "l.length + l.sum + l.reverse.length"),
    ("sorting", "l.mergeSort (fun a b => decide (a ≤ b))"),
    ("library method", "(l.filter (fun x => x % 2 == 0)).map (fun x => x + 1)"),
    ("ranges, folds", "(List.range n).foldl (fun acc i => acc + i) 0"),
    ("pairs", "(p.1, p.2 + 1)"),
    ("types", "List Int × Option Nat"),
    ("number conversions", "(k : Int) + n.toNat + (x : ℚ)"),
    ("absolute value, floor", "|x - y| + ⌊q⌋₊"),
    ("decide a proposition", "decide (x ∈ l)"),
    ("Booleans", "b = true ∨ c = false"),
    ("characters and strings", "s.toList.filter (fun c => c.isDigit)"),
    ("prime, gcd", "Nat.Prime p ∧ Nat.gcd a b = 1"),
]


def _check(lean: str) -> str:
    tree = lean_syntax.parse(lean)
    spec = lspec_syntax.show(tree)
    back = lspec_syntax.parse(spec)
    if normal(back) != normal(tree):
        raise AssertionError(f"cheat-sheet example does not round-trip: {lean!r} -> {spec!r}")
    return spec


def _table(rows, head=("L_spec", "Lean"), code_first=True) -> str:
    lines = [f"| {head[0]} | {head[1]} |", "|---|---|"]
    lines += [f"| {f'`{a}`' if code_first else a} | `{b}` |" for a, b in rows]
    return "\n".join(lines)


#: where Lean's meaning differs from what the Python spelling suggests
MEANING = [
    "`nat` subtraction stops at zero: `2 - 5 == 0`. Write `(a as int) - b` for a signed difference.",
    "`/` on `nat` and `int` is integer division (`7 / 2 == 3`, `x / 0 == 0`); on `rat` it is exact.",
    "`l[i]` is the element at `i`, or the type's default (`0`, `False`, `\"\"`) when `i >= len(l)`; "
    "`l[i]?` is `some(x)` or `none`.",
    "Slices (`l[a:b]`) are for lists; a `str` slice is a different type: slice its characters and rebuild it, "
    "`String.mk(list(s)[a:b])`.",
    "`//` and `%` with a negative divisor differ from Python: `7 // -2 == -3`, `7 % -2 == 1` (the remainder is never "
    "negative); `x // 0 == 0`.",
        "`==` is equality as a proposition; `===` is the Boolean test (Lean's `==`). "
    "A Boolean `b` used as a condition is written `b == True`.",
    "`forall`/`exists`/`lambda` bodies extend to the end of the expression: parenthesise them inside larger ones.",
]


#: Python forms the parser also reads (never printed): what each one means in Lean
PYTHON_FORMS = [
    ("`[f(x) for x in l if p(x)]`", "`l.filter(p).map(f)` (one `for`, one variable)"),
    ("`sum(f(x) for x in l)`, `any(p(x) for x in l)`, `all(...)`", "the same on the list `[f(x) for x in l]`"),
    ("`range(a, b)`", "`a, a+1, ..., b-1`"),
    ("`l[-1]`, `l[:-1]`, `l[-2:]`, `l[a:b]`, `l[::-1]`", "as in Python (`l[len(l) - 1]`, ..., `reversed(l)`)"),
    ("`a < b <= c`", "`a < b and b <= c`"),
    ("`a // b`", "`a / b` (integer division)"),
    ("`max(l)`, `min(l)` of a list", "the largest / smallest element (the type's default, e.g. `0`, if `l` is empty)"),
    ("`if c then a else b`", "`a if c else b` (Lean's spelling; `else` reaches as far right as it can)"),
    ("`if c then p` (no else)", "`c ==> p` (a statement)"),
    ("`p implies q`", "`p ==> q`"),
    ("`'text'`", "`\"text\"` (one character, `'a'`, is a `char`; as the argument of `split`, `join`, `startswith`, "
     "`endswith` it is a string)"),
    ("`map(f, l)`, `filter(p, l)`", "`l.map(f)`, `l.filter(p)`"),
    ("`s.upper()`, `sep.join(l)`, `s.split(sep)`, `s.strip()`, `s.startswith(t)`", "the string methods"),
    ("`let x := v; body`", "`let x = v; body`"),
]


def sheet() -> str:
    """The reference as Markdown."""
    ops_rows = [(spec, lean) for lean, spec in ops.BINOPS.items()]
    ops_rows += [(spec, lean) for lean, spec in ops.UNOPS.items() if spec != lean]
    same = "+ - * / % < > ++ ::"
    name_rows = [(spec, lean) for spec, lean in ops.NAMES_INV.items()]
    func_rows = [(f"{spec}(x)", f"x.{lean}") for spec, lean in ops.METHOD_FUNCS_INV.items()]
    meth_rows = [(f"x.{spec}(...)", f"x.{lean} ...") for spec, lean in ops.METHODS_INV.items()]
    example_rows = [(topic, _check(lean)) for topic, lean in EXAMPLES]
    parts = [
        "# L_spec reference",
        "Python-like syntax over Lean's meaning. Operators group exactly as in Lean (`a - b - c` is `(a - b) - c`; "
        "`==>` binds weaker than `and`/`or`; a binder's body extends as far right as possible: parenthesise it).",
        "Any Lean library function or method not listed below is written as in Lean, with call syntax: "
        "`l.filter(p)`, `List.zip(a, b)`, `c.isDigit`.",
        f"Operators spelled as in Lean: `{same}`.",
        "## Operators", _table(ops_rows),
        "## Names and types", _table(name_rows),
        "## Methods written as functions", _table(func_rows),
        "## Renamed methods", _table(meth_rows),
        "## Python forms also accepted",
        "\n".join(["| you may write | it means |", "|---|---|"] + [f"| {a} | {b} |" for a, b in PYTHON_FORMS]),
        "## Meaning (Lean's, not Python's)", "\n".join(f"- {m}" for m in MEANING),
        "## Examples", _table(example_rows, head=("what", "L_spec"), code_first=False),
    ]
    return "\n\n".join(parts) + "\n"


if __name__ == "__main__":
    import sys
    sys.stdout.reconfigure(encoding="utf-8")
    print(sheet())
