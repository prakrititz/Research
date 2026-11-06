"""Which Python constructs HumanEval's reference solutions use, and how L_spec stands on each.

    python benchmarks/lspec_constructs.py

L_spec has no statements: a loop, an assignment, an ``if`` statement become refinement laws (loop, term/bind, cases).
What the model writes in L_spec are expressions (values, conditions, invariants), so this counts the *expression*
constructs of the 164 reference solutions (EvalPlus' canonical solutions): builtin functions, methods, operators,
subscripts, comprehensions, literals. Each is classified:

``same``      L_spec has it with Python's meaning
``renamed``   L_spec has it under another spelling (shown)
``meaning``   L_spec has it but Lean's meaning differs from Python's on some inputs (the note says where)
``missing``   no L_spec form yet

Writes ``benchmarks/results/lspec/constructs_humaneval.md``."""
import ast
import collections
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# `benchmarks/datasets` would shadow HuggingFace's `datasets`, which EvalPlus imports
sys.path[:] = [p for p in sys.path if os.path.abspath(p or ".") != os.path.dirname(os.path.abspath(__file__))]
sys.path.insert(0, ROOT)

from FormalLLM.dsl import ops  # noqa: E402

#: builtins and methods: (status, note); anything not listed is ``missing``
KNOWN = {
    "len": ("same", ""), "sum": ("same", ""), "sorted": ("meaning", "`sorted(l)` sorts numbers; a `key=` or `reverse=` "
                                                           "argument has no L_spec form (write a comparison: `sorted(l, c)`)"),
    "reversed": ("same", ""), "abs": ("same", ""), "range": ("meaning", "`range(n)` only; `range(a, b)` and a step "
                                                             "have no direct form"),
    "list": ("same", "`list(s)` of a string is its characters"), "str": ("same", "`str(n)`"), "int": ("missing", "parsing a "
                                                                                                    "string to a number"),
    "bool": ("same", ""), "min": ("missing", "min/max of a list (a binary `min(a, b)` is Lean's `min`)"),
    "max": ("missing", "min/max of a list (a binary `max(a, b)` is Lean's `max`)"),
    "map": ("same", "`map(f, l)`"), "filter": ("same", "`filter(p, l)`"), "any": ("missing", "`any(p(x) for x in l)`: "
                                                                                             "write `exists x in l: p(x)`"),
    "all": ("missing", "`all(...)`: write `forall x in l: p(x)`"), "enumerate": ("missing", "write an index loop"),
    "zip": ("renamed", "`List.zip(a, b)`"), "set": ("missing", "sets: write `dedup(l)` or a membership condition"),
    "dict": ("missing", "dictionaries"), "tuple": ("same", "a tuple literal"), "float": ("meaning", "floats are "
                                                                                         "written as `rat`: exact, no rounding"),
    "round": ("missing", "Python rounds half to even"), "ord": ("renamed", "`c.toNat`"), "chr": ("renamed", "`Char.ofNat(n)`"),
    "isinstance": ("missing", "no dynamic types"), "pow": ("same", "`a ** b`"), "divmod": ("missing", ""),
    "sum_": ("same", ""), "print": ("missing", ""), "hex": ("missing", ""), "bin": ("missing", ""),
    # methods
    ".append": ("renamed", "`l ++ [x]`"), ".count": ("renamed", "`l.count(x)`"), ".index": ("same", "`l.index(x)`"),
    ".lower": ("missing", "string case"), ".upper": ("missing", "string case"), ".split": ("missing", "splitting a string"),
    ".join": ("missing", "joining strings"), ".strip": ("missing", ""), ".replace": ("missing", ""),
    ".startswith": ("missing", ""), ".endswith": ("missing", ""), ".isdigit": ("renamed", "`c.isDigit` (a character)"),
    ".isalpha": ("renamed", "`c.isAlpha` (a character)"), ".isupper": ("renamed", "`c.isUpper`"),
    ".islower": ("renamed", "`c.isLower`"), ".swapcase": ("missing", ""), ".sort": ("renamed", "`sorted(l)`"),
    ".reverse": ("renamed", "`reversed(l)`"), ".pop": ("missing", "mutation"), ".insert": ("missing", "mutation"),
    ".extend": ("renamed", "`l ++ m`"), ".items": ("missing", "dictionaries"), ".keys": ("missing", "dictionaries"),
    ".values": ("missing", "dictionaries"), ".get": ("missing", "dictionaries"), ".add": ("missing", "sets"),
    ".remove": ("missing", "mutation"), ".find": ("missing", ""), ".isspace": ("renamed", "`c.isWhitespace`"),
}

OPERATORS = {
    "Add": ("same", ""), "Sub": ("meaning", "on `nat`, `a - b` is 0 when b > a (Python: negative). Cast to `int` first"),
    "Mult": ("same", ""), "Div": ("meaning", "on `nat`/`int`, `/` is integer division; Python's `/` is a float"),
    "FloorDiv": ("meaning", "`//` is `/` in L_spec; for a negative divisor Lean and Python round differently"),
    "Mod": ("meaning", "`%`: for a negative divisor the sign of the result differs from Python's"),
    "Pow": ("same", "`**`"), "BitAnd": ("renamed", "`&&&`"), "BitOr": ("renamed", "`|||`"), "BitXor": ("renamed", "`xor`"),
    "LShift": ("renamed", "`<<<`"), "RShift": ("renamed", "`>>>`"), "USub": ("same", ""), "Not": ("same", ""),
    "Invert": ("renamed", "`~~~`"), "And": ("same", ""), "Or": ("same", ""), "Eq": ("same", ""), "NotEq": ("same", ""),
    "Lt": ("same", ""), "LtE": ("same", ""), "Gt": ("same", ""), "GtE": ("same", ""), "In": ("same", ""),
    "NotIn": ("same", ""), "Is": ("missing", ""), "IsNot": ("missing", ""), "UAdd": ("same", ""),
}

FORMS = {
    "index": ("meaning", "`l[i]` past the end is a default value (0, False, \"\"), not an error"),
    "negative index": ("missing", "`l[-1]`: write `l[len(l) - 1]`"),
    "slice": ("same", "`l[:k]`, `l[k:]`"), "slice a:b": ("missing", "`l[a:b]`: write `l[a:][:b - a]`"),
    "slice with step": ("missing", "`l[::2]`, `l[::-1]` (write `reversed(l)`)"),
    "list comprehension": ("missing", "`[f(x) for x in l if p(x)]`: write `l.filter(p).map(f)`"),
    "generator": ("missing", "`sum(f(x) for x in l)`: write `sum(l.map(f))`"),
    "dict literal / comprehension": ("missing", "dictionaries"), "set literal / comprehension": ("missing", "sets"),
    "conditional expression": ("same", "`a if c else b`"), "lambda": ("same", ""), "f-string": ("missing", ""),
    "chained comparison": ("missing", "`a < b < c`: write `a < b and b < c`"), "tuple": ("same", ""),
    "float literal": ("meaning", "a `rat`: exact"), "string literal": ("same", ""),
}


def constructs(source: str):
    """(construct, kind) for every expression construct in ``source``."""
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                yield node.func.id, "builtin"
            elif isinstance(node.func, ast.Attribute):
                yield "." + node.func.attr, "method"
        elif isinstance(node, (ast.BinOp, ast.UnaryOp, ast.BoolOp)):
            yield type(node.op).__name__, "operator"
        elif isinstance(node, ast.Compare):
            for op in node.ops:
                yield type(op).__name__, "operator"
            if len(node.ops) > 1:
                yield "chained comparison", "form"
        elif isinstance(node, ast.Subscript):
            s = node.slice
            if isinstance(s, ast.Slice):
                if s.step is not None:
                    yield "slice with step", "form"
                elif s.lower is not None and s.upper is not None:
                    yield "slice a:b", "form"
                else:
                    yield "slice", "form"
            elif isinstance(s, ast.UnaryOp) and isinstance(s.op, ast.USub):
                yield "negative index", "form"
            else:
                yield "index", "form"
        elif isinstance(node, ast.ListComp):
            yield "list comprehension", "form"
        elif isinstance(node, ast.GeneratorExp):
            yield "generator", "form"
        elif isinstance(node, (ast.Dict, ast.DictComp)):
            yield "dict literal / comprehension", "form"
        elif isinstance(node, (ast.Set, ast.SetComp)):
            yield "set literal / comprehension", "form"
        elif isinstance(node, ast.IfExp):
            yield "conditional expression", "form"
        elif isinstance(node, ast.Lambda):
            yield "lambda", "form"
        elif isinstance(node, ast.JoinedStr):
            yield "f-string", "form"
        elif isinstance(node, ast.Constant) and isinstance(node.value, float):
            yield "float literal", "form"


def status(name: str, kind: str):
    table = OPERATORS if kind == "operator" else FORMS if kind == "form" else KNOWN
    if name in table:
        return table[name]
    if kind == "method" and name[1:] in ops.METHODS_INV or name[1:] in ops.METHOD_FUNCS:
        return "same", ""
    return "missing", ""


def main():
    from evalplus.data import get_human_eval_plus
    problems = get_human_eval_plus()
    tasks = collections.defaultdict(set)
    uses = collections.Counter()
    for key, p in problems.items():
        source = p["prompt"] + p["canonical_solution"]
        try:
            found = set(constructs(source))
        except SyntaxError:
            continue
        for item in found:
            tasks[item].add(key)
            uses[item] += 1
    rows = sorted(tasks, key=lambda item: (-len(tasks[item]), item))
    by_status = collections.defaultdict(list)
    for item in rows:
        by_status[status(*item)[0]].append(item)
    lines = ["# Python constructs in HumanEval's reference solutions, and L_spec", "",
             f"{len(problems)} reference solutions (EvalPlus canonical solutions); statements (loops, assignments, `if`) "
             "are refinement laws and not counted. *Tasks*: how many solutions use the construct.", ""]
    for st, title in (("meaning", "Same name, different meaning (the risky ones)"), ("missing", "No L_spec form yet"),
                      ("renamed", "In L_spec under another spelling"), ("same", "In L_spec as in Python")):
        lines += [f"## {title}", "", "| Construct | Kind | Tasks | Note |", "|---|---|---|---|"]
        for name, kind in by_status[st]:
            lines.append(f"| `{name}` | {kind} | {len(tasks[(name, kind)])} | {status(name, kind)[1]} |")
        lines.append("")
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", "constructs_humaneval.md")
    with open(out, "w", encoding="utf8") as handle:
        handle.write("\n".join(lines))
    affected = {st: set().union(*(tasks[i] for i in by_status[st])) if by_status[st] else set() for st in by_status}
    for st in ("meaning", "missing", "renamed", "same"):
        print(f"{st:8s} {len(by_status[st]):3d} constructs, used by {len(affected.get(st, ()))} of {len(problems)} solutions")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
