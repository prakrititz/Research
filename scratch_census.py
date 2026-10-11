"""Census of HumanEval by what an L_spec/L_pl-style language would need."""
import collections
import sys

sys.path.insert(0, r"C:\Users\Prakrititz Borah\Downloads\Work\Research\Symbolic_LLM")
from benchmarks.datasets import humaneval as he

problems = he.load_problems()
truth = he.groundtruth()


def kind_of(v):
    if isinstance(v, bool):
        return "bool"
    if isinstance(v, int):
        return "int"
    if isinstance(v, float):
        return "float"
    if isinstance(v, str):
        return "str"
    if isinstance(v, (list, tuple)):
        inner = {kind_of(x) for x in v}
        inner.discard("list[]")
        if not inner:
            return "list[]"
        if inner <= {"int", "float"}:
            return "list[num]"
        if inner == {"str"}:
            return "list[str]"
        return "list[other]"
    if isinstance(v, dict):
        return "dict"
    return type(v).__name__


def merge(kinds):
    kinds = {k for k in kinds if k != "list[]"} or {"list[]"}
    if len(kinds) == 1:
        return kinds.pop()
    if kinds <= {"int", "float"}:
        return "num"
    if kinds <= {"list[num]"}:
        return "list[num]"
    if kinds <= {"int", "float", "bool"}:
        return "scalar"
    return "mixed"


def bucket(arg_kinds, out_kind):
    scalar = {"int", "float", "bool", "num", "scalar"}
    nums = scalar | {"list[num]"}
    if all(k in nums for k in arg_kinds):
        if out_kind in scalar:
            return "A  scalar result, numeric inputs"
        if out_kind == "list[num]":
            return "B  list result, numeric inputs (needs array building)"
    if any(k in ("str", "list[str]") for k in arg_kinds) or out_kind in ("str", "list[str]"):
        return "C  strings involved"
    return "D  other (dict, tuple, nested, mixed)"


counts = collections.Counter()
members = collections.defaultdict(list)
for tid, p in problems.items():
    inputs = p["base_input"] + p["plus_input"][:100]
    arg_kinds = [merge(kind_of(row[i]) for row in inputs) for i in range(len(inputs[0]))]
    out = truth[tid]["base"]
    out_kind = merge(kind_of(o) for o in out)
    b = bucket(arg_kinds, out_kind)
    counts[b] += 1
    members[b].append(int(tid.split("/")[1]))
for b in sorted(counts):
    print(f"{counts[b]:4d}  {b}")
print()
print("A:", sorted(members["A  scalar result, numeric inputs"]))
