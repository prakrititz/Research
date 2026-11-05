import json, os, re

S = r"C:\Users\PRAKRI~1\AppData\Local\Temp\claude\C--Users-Prakrititz-Borah-Downloads-Work-Research\b020564e-3578-4f9b-a07c-f4f95164f4ca\scratchpad"
S = os.path.realpath(S)
EX = os.path.join(S, "rc", "exports")
VT = os.path.join(S, "vtasks")
OUT = r"C:\Users\Prakrititz Borah\Downloads\Work\Research"


def rd(p):
    return open(p, encoding="utf8").read()


valid = {}
for l in open(os.path.join(S, "rc", "benchmarks", "results", "verina", "validation.jsonl"), encoding="utf8"):
    d = json.loads(l)
    valid[d["id"]] = d


def short(e, n=420):
    e = e.replace("\u00e2\u201e\u2022", "Nat").replace("\u00e2\u201e\u00a4", "Int")
    e = re.sub(r"\n\s*Hint:.*", "", e, flags=re.S)
    e = re.sub(r"\n\s*Note:.*", "", e, flags=re.S)
    return " ".join(e.split())[:n]


def comment_block(lines):
    return "\n".join("-- " + l if l else "--" for l in lines)


def inject(code, ident, msg):
    """Put an '>>> ERROR' comment above the first line that defines `ident`."""
    out, done = [], False
    for ln in code.split("\n"):
        if not done and re.search(r"(def|let rec|partial def|where)\s+" + re.escape(ident) + r"\b", ln):
            ind = re.match(r"\s*", ln).group(0)
            out.append(f"{ind}-- >>> ERROR POINT: {msg}")
            done = True
        out.append(ln)
    return "\n".join(out), done


# ---------------------------------------------------------------- file 1
sections = []


def add(title, tid, kind, status_lines, code, desc=""):
    s = f"### {title}\n\n"
    if desc:
        s += desc.strip() + "\n\n"
    s += "```lean\n"
    s += comment_block([f"TASK: {tid}   ({kind})"] + status_lines) + "\n\n" + code.rstrip() + "\n```\n"
    sections.append(s)


# --- A. HumanEval (5)
he = {
    "he_015_string_sequence": ("`String.splitOn` is used in the postcondition and Lean 4.34 has no lemma relating `splitOn` to list operations, so Lean cannot prove that `String.intercalate \" \" (range.map toString)` splits back into the list.",
                               "WHAT WE MUST DO: a lemma  (s.intercalate sep).splitOn sep = ...  for sep=\" \" and digit strings (which contain no space). Then the derivation is just  `term (String.intercalate \" \" ((List.range (n+1)).map toString))`."),
    "he_019_sort_numbers": ("Same cause: spec uses `String.splitOn` (words of the input), no lemma library for it in Lean 4.34.",
                            "WHAT WE MUST DO: splitOn lemma + a sort-by-key (zero..nine) permutation argument."),
    "he_086_anti_shuffle": ("Same cause: spec uses `String.splitOn` (words), no lemma library for it in Lean 4.34.",
                            "WHAT WE MUST DO: splitOn lemma + per-word sort + re-join lemma."),
    "he_032_find_zero": ("Needs a root bound and a Lipschitz bound for a polynomial over Q (bisection). The derivation (bisection loop) was not attempted.",
                         "WHAT WE MUST DO: loop over an interval [lo,hi] with sign change, invariant f lo * f hi <= 0, variant = fuel / halving; the exit needs |f x| <= eps from the interval width using a bound on the coefficients."),
    "he_039_prime_fib": ("The spec is UNSATISFIABLE for n > 14 and the kernel cannot decide primality of 28-digit Fibonacci numbers, so no derivation can be certified for the whole input range.",
                         "WHAT WE MUST DO (decision, not proof): restrict precond to n <= 14, or change the spec. Possibly a spec bug worth reporting."),
}
add_sec = ["## A. HumanEval — 5 tasks without a derivation\n\n"
           "Source: `exports/humaneval/<id>/spec.lean` (our own Lean specs; the task has no reference program, only the spec + English).\n"]
sections.append(add_sec[0])
for tid, (why, need) in he.items():
    spec = rd(os.path.join(EX, "humaneval", tid, "spec.lean"))
    desc = rd(os.path.join(EX, "humaneval", tid, "description.md")).split("\n", 2)[2]
    st = json.load(open(os.path.join(EX, "humaneval", tid, "status.json")))
    add(tid, tid, "HumanEval, not derived",
        ["WHY NOT DERIVED: " + why, need, f"(spec checks vs tests: {st.get('spec_checks', {})})"],
        spec, desc)

# --- B. Verina blocked (9)
sections.append("## B. Verina — 9 tasks that do not compile on Lean 4.34.1\n\n"
                "Code below is Verina's own `task.lean` (public repo `sunblaze-ucb/verina`, `datasets/verina/<id>/task.lean`), "
                "i.e. the `-- !benchmark` regions with the REFERENCE implementation. Those are the part that breaks. "
                "If you pinned an older Verina commit on your Mac, text may differ slightly. "
                "Lean version used: 4.34.1 + Mathlib. The harness prepends an `Array.mkArray` shim (`Array.replicate`), a `Std.HashSet.empty` shim and a `wit_search` tactic.\n\n"
                "The 7 `let rec` tasks share ONE cause: the automatic termination proof (`decreasing_by`/WF via `simp`) hits "
                "`maximum recursion depth has been reached`; the `let rec` function is then never defined, so every later use fails with "
                "`Unknown identifier <fn>`. What we must do: give an explicit `termination_by` / `decreasing_by omega`, "
                "or turn the `let rec` into a top-level `def` with fuel/structural recursion.\n")
blocked = {
    "verina_basic_23": ("differenceMinMax", "let rec loop", "loop"),
    "verina_basic_52": ("bubbleSort-style", "bubbleInner", "bubbleInner"),
    "verina_basic_57": ("count", "countLessThan", "countLessThan"),
    "verina_basic_74": ("maxArray", "maxArray_aux", "maxArray_aux"),
    "verina_basic_75": ("loop", "loop", "loop"),
    "verina_basic_79": ("findBest", "findBest", "findBest"),
    "verina_basic_86": ("rotate", "rotateAux", "rotateAux"),
    "verina_basic_61": ("String.Iterator", None, None),
    "verina_advanced_68": ("c.isDigit", None, None),
}
for tid, (_, _, ident) in blocked.items():
    code = rd(os.path.join(VT, tid + ".lean"))
    v = valid[tid]
    errs = [short(e) for e in v["errors"][:3]]
    lines = ["WHY BLOCKED: does not compile on Lean 4.34.1", f"tests: {v['tests']}", "RECORDED ERRORS (benchmarks/results/verina/validation.jsonl):"]
    lines += [f"  [{i+1}] {e}" for i, e in enumerate(errs)]
    if tid == "verina_basic_61":
        lines += ["CAUSE: `it.curr` / `it.next` field notation on String.Iterator: the signature changed after Lean 4.18 (iterator no longer a usable explicit param).",
                  "WHAT WE MUST DO: rewrite as `String.Iterator.curr it` / `String.Iterator.next it`, or use `s.toList`/`String.get`. Then also give the recursion a termination proof."]
        msg = "uses `.curr` / `.next` (String.Iterator API changed)"
        code = re.sub(r"^(\s*)(.*\bit\.curr\b.*)$", lambda m: m.group(1) + "-- >>> ERROR POINT: " + msg + "\n" + m.group(1) + m.group(2), code, count=1, flags=re.M)
        code = re.sub(r"^(\s*)(.*\bloop it\.next\b.*)$", lambda m: m.group(1) + "-- >>> ERROR POINT (same): `.next`\n" + m.group(1) + m.group(2), code, count=1, flags=re.M)
    elif tid == "verina_advanced_68":
        lines += ["CAUSE: the SPEC itself does not elaborate: `fun c => c.isDigit` with the type of `c` not yet known (elaboration order changed in newer Lean).",
                  "WHAT WE MUST DO: annotate the binder  `fun (c : Char) => c.isDigit`  or write `Char.isDigit c`. The second error (universe constraint) is probably a consequence."]
        code = re.sub(r"(^.*\.isDigit.*$)", r"-- >>> ERROR POINT: type of `c` unknown, `.isDigit` cannot be resolved\n\1", code, count=1, flags=re.M)
    else:
        lines += ["CAUSE: `let rec` termination proof times out -> function undefined -> `Unknown identifier " + ident + "`.",
                  "WHAT WE MUST DO: explicit `termination_by`/`decreasing_by`, or fuel-based/structural recursion."]
        code, _ok = inject(code, ident, f"`{ident}`: automatic termination proof exceeds maxRecDepth")
        if not _ok:
            lines.append("(could not auto-locate the definition line; search for `" + ident + "`)")
    add(tid, tid, "Verina, BLOCKED by Lean version", lines, code)

# --- C. untestable (14)
sections.append("## C. Verina — 14 'untestable' tasks (the postcondition cannot be RUN by Lean)\n\n"
                "Important: these DO have a derivation and are among the 177 certified. 'Untestable' only means the spec-validation step "
                "(`lean_eval.py validate`) could not evaluate `<f>_postcond result` on the given tests, so we cannot check the spec against the tests "
                "(accepts_expected = 0/N although the reference passes). It is a property of the dataset's spec/harness, not of our derivation.\n\n"
                "Two causes:\n"
                "1. **`failed to synthesize instance of type class Decidable (<f>_postcond ...)`** (10 tasks): the postcondition is a Prop built from "
                "`↔`, `∃` or `∀` over an unbounded domain (e.g. `∃ k, ...`, `∀ x, ... ↔ ...`), so `decide` cannot evaluate it. "
                "What we must do: add `instance : Decidable (f_postcond ...)` by hand, or restate with bounded quantifiers / `List.all` / `List.any`.\n"
                "2. **Harness quirks** (4 tasks, recorded errors `Function expected at ...` / `omega could not prove`): `verina_basic_48`, `verina_advanced_44`, "
                "`verina_advanced_74` state the theorem WITHOUT `h_precond` (function takes no proof arg) but the harness still passed one; "
                "`verina_basic_40` has a precondition whose proof (`omega`) fails for the harness-built argument. "
                "The engine was fixed later (`LeanTask.precond_arg`, `wit_search`, doc 27 §4), so these recorded numbers in validation.jsonl may be stale: re-run `python benchmarks/lean_eval.py validate --dataset verina` to refresh them.\n\n"
                "Other weak spec (NOT in the 14, FYI): `verina_basic_72` accepts a wrong output (rejects_wrong 14/15).\n")
untest = ["verina_advanced_14", "verina_advanced_20", "verina_advanced_23", "verina_advanced_66", "verina_basic_21", "verina_basic_24",
          "verina_basic_3", "verina_basic_45", "verina_basic_66", "verina_basic_9",
          "verina_advanced_44", "verina_advanced_74", "verina_basic_48", "verina_basic_40"]
for tid in untest:
    code = rd(os.path.join(VT, tid + ".lean"))
    v = valid[tid]
    errs = [short(e, 300) for e in v["errors"][:2]]
    lines = ["WHY 'UNTESTABLE': spec validation could not evaluate the postcondition",
             f"tests: {v['tests']}  reference_passes: {v['reference_passes']}/{v['tests']}  undecidable: {v['undecidable']}  accepts_expected: {v['accepts_expected']}",
             "RECORDED ERRORS:"] + [f"  [{i+1}] {e}" for i, e in enumerate(errs)]
    lines.append("STATE: has a certified derivation (is one of the 177); only the spec-vs-tests check is missing.")
    add(tid, tid, "Verina, untestable postcondition", lines, code)

# --- D. Float (2)
sections.append("## D. Verina — 2 Float tasks\n\n"
                "These compile and the reference passes the tests (validation OK). The problem is the CERTIFICATE: `Float` operations are opaque to the kernel, "
                "so proving `x == x` / comparison facts needs the dataset's own `axiom` declarations. Our certificate allows only `propext`, `Classical.choice`, `Quot.sound`, "
                "so a derivation that uses those axioms is refused. Decision for us: either we accept the dataset's axioms as trusted for these two tasks, or we leave them out.\n")
for tid in ["verina_basic_25", "verina_basic_63"]:
    code = rd(os.path.join(VT, tid + ".lean"))
    code = re.sub(r"(^\s*axiom\b.*$)", r"-- >>> ERROR POINT: dataset axiom — the certificate refuses declared axioms\n\1", code, flags=re.M)
    add(tid, tid, "Verina, Float",
        ["WHY NOT DERIVED: postcondition is a Float equality/comparison; Float is opaque; only the dataset's own axioms prove it; certificate refuses axioms.",
         "WHAT WE MUST DO: (a) we allow-list these axioms for these 2 tasks, or (b) we rewrite the spec over Rat/Int, which changes the benchmark."], code)

# --- E. open
sections.append("## E. Verina — 1 open task: `verina_advanced_47` (`mergeIntervals`)\n\n"
                "Compiles, tests pass, spec is fine. The derivation is simply not finished: it needs a long invariant proof. Our plan from doc 27 §7:\n\n"
                "> sort by start and fold with a stack of merged intervals; invariants on the processed prefix `P`:\n"
                "> 1. every result interval has `rs ≤ re`;\n> 2. consecutive result intervals are strictly separated;\n"
                "> 3. every interval of `P` is covered by a result interval;\n> 4. both ends of every result interval come from `P`;\n"
                "> 5. every interval of `P` inside a result interval starts at its start, or has a witness `(s2,e2)` inside it with `s2 < s ≤ e2` (no spurious merge, chain witness);\n"
                "> 6. every interval of `P` that is NOT inside the head result ends before the head starts — the one needed for the merge step and the long one.\n")
code = rd(os.path.join(VT, "verina_advanced_47.lean"))
add("verina_advanced_47", "verina_advanced_47", "Verina, OPEN",
    ["WHY OPEN: five-plus coupled invariants for sort-and-merge; proof of the merge step (invariant 6) not closed.",
     "WHAT WE MUST DO: write a loop over the sorted list; state = (i, stack of merged intervals); variant = len - i.",
     "TIPS FOR US (doc 27 §7): avoid `match` inside a step term (use head?/headD/tail); keep helper facts as `have`s inside ONE lemma, not a long helper-lemma list (cascade tries every helper on every obligation)."],
    code)

head = f"""# Tasks we could NOT derive yet — what we must do

Generated {__import__('datetime').date.today()} from the `lean-specs` branch of prakrititz/Research (docs 27/28 + `exports/` + `benchmarks/results/verina/validation.jsonl`)
and Verina's public `task.lean` files. LOCAL FILE ONLY — nothing was pushed.

## Overview (31 task entries)

| group | count | what is wrong | what we must do |
|---|---|---|---|
| A. HumanEval not derived | 5 | `splitOn` lemma gap (3), bisection (1), unsatisfiable spec (1) | we write the lemmas / the loop proof / fix the spec |
| B. Verina blocked on Lean 4.34.1 | 9 | reference code does not compile (7 termination timeouts, 1 String.Iterator API, 1 spec elaboration) | we patch the Verina Lean code (explicit termination / API rename / type ascription) |
| C. Verina untestable postcondition | 14 | postcondition not `Decidable` (10) or harness quirk (4) — these are ALREADY derived | we add Decidable instances and re-run validation |
| D. Verina Float | 2 | Float is opaque; needs dataset axioms; certificate refuses axioms | we decide the axiom policy |
| E. Verina open | 1 | `mergeIntervals` invariants not closed | we finish the proof |

Counts: 5 + 9 + 2 + 1 = 17 tasks with NO derivation (5 HumanEval + 12 Verina). The 14 in group C are separate and already certified.

How to read each entry: the Lean block starts with a `-- TASK / WHY / ERRORS / FIX HINT` comment, then the code. A line `-- >>> ERROR POINT` marks where the error is (found automatically by name — verify before trusting).

"""
open(os.path.join(OUT, "Underived_Tasks_For_Expert.md"), "w", encoding="utf8").write(head + "\n".join(sections))

# ---------------------------------------------------------------- file 2
def ex(path, title, tid, why, notes):
    dd = os.path.join(EX, path)
    spec = rd(os.path.join(dd, "spec.lean"))
    spec = re.sub(r"^import Mathlib\n+", "", spec)
    desc = rd(os.path.join(dd, "description.md")).split("\n", 2)[2].strip()
    der = rd(os.path.join(dd, "derivation.md"))
    der = der.split("\n", 2)[2].strip()
    return (f"### {title}  (`{tid}`)\n\n**English:** {desc.splitlines()[0] if desc.startswith('`') else desc}\n\n" +
            (desc.split("\n\n", 1)[1] + "\n\n" if desc.startswith('`') and "\n\n" in desc and len(desc.split("\n\n", 1)[1]) < 900 else "") +
            f"**Why it is `{why}`:** {notes[0]}\n\n"
            "**Formal spec (Lean) — this is what must hold of the answer:**\n\n```lean\n" + spec.strip() + "\n```\n\n" +
            "**Reading the spec:**\n" + "\n".join("- " + n for n in notes[1]) + "\n\n"
            "**The derivation the engine certified:**\n\n```\n" + der + "\n```\n\n" +
            "**Reading the derivation:**\n" + "\n".join("- " + n for n in notes[2]) + "\n")


parts = []
parts.append("""# What the derivation kinds look like (loop / restate / definitional)

LOCAL FILE ONLY — not pushed. Each example: English statement, the formal Lean spec with comments, the derivation the engine certified, and a plain-language reading.
Data: `exports/<dataset>/<task>/{spec.lean,derivation.md,description.md}` on the `lean-specs` branch.

## Vocabulary you need first

Every task has the same shape:

```lean
def f_precond  (inputs) : Prop := ...            -- what the INPUT may be (True = anything)
def f_postcond (inputs) (result) (h_precond) := ...  -- what must be true of the OUTPUT. The spec says WHAT, never HOW.
```

A *derivation* is how the engine builds a program `f` together with a proof that `f_postcond (f inputs)` holds. It uses 4 laws:

| law | meaning |
|---|---|
| `term` | "the answer is this expression" — Lean must prove the expression satisfies the postcondition |
| `cases` | split on a condition, handle each branch |
| `bind` | compute an intermediate value, then continue |
| `loop` | loop with a state, a start value, an **invariant** (true before/after every iteration), a **guard** (keep going while true), a **variant** (a number that strictly shrinks, so the loop stops), and a **result** (what to return when the guard fails). The proof obligation: invariant ∧ ¬guard ⟹ postcondition. |

Loop analogy: `isqrt`: `r := 0; while (r+1)*(r+1) <= n do r := r+1; return r`.
The invariant `r*r <= n` stays true; when the guard fails, `(r+1)*(r+1) > n`; together that IS the postcondition.

Kind labels (counts): **loop** — HumanEval 87, classics 4, Verina 65. **restate** — HumanEval 69, classic 1, Verina 112. **definitional** — HumanEval 3.

---

# 1. LOOP — the algorithm lives in an invariant

""")
parts.append(ex("classic/classic_isqrt", "Loop example 1 — integer square root", "classic_isqrt", "loop",
    ["The spec only says what a square root IS (largest r with r*r <= n); it does not say how to find it, so the engine must invent a search.",
     ["`result * result ≤ n`: r is not too big.",
      "`n < (result+1)*(result+1)`: r+1 would be too big — together: r is the FLOOR of the square root.",
      "precondition `True`: any natural number is allowed."],
     ["state `r` starts at 0 and counts up by 1 (`term: r + 1`).",
      "guard `(r+1)*(r+1) ≤ n`: keep going while the next number is still allowed.",
      "invariant `r*r ≤ n`: first half of the postcondition holds all the time.",
      "when the guard is false we have `n < (r+1)*(r+1)`: second half. So `invariant ∧ ¬guard ⟹ postcondition`.",
      "variant `n - r`: shrinks by at least 1 each iteration (as long as the guard holds, r <= n) so the loop terminates."]]))
parts.append("\n")
parts.append(ex("humaneval/he_003_below_zero", "Loop example 2 — bank balance goes below zero", "he_003_below_zero", "loop",
    ["The postcondition quantifies over ALL prefixes (`∃ k, ... take k ... < 0`), but the program can check it incrementally while scanning once — that scan is the loop.",
     ["`(operations.take k).sum < 0`: the balance after the first k operations.",
      "`result = true ↔ ∃ k ≤ length, balance(k) < 0`: answer is true exactly when SOME prefix has negative balance.",
      "This is a spec over every k (unbounded in spirit) — Lean cannot just run it, so the loop is the way to a program."],
     ["state has THREE variables: index `i`, running balance `bal`, flag `neg` (\"have we been below zero so far\"). Start `(0, 0, false)`.",
      "invariant: `bal = (take i).sum` (balance is right) AND `neg = true ↔ ∃ k ≤ i, prefix-sum k < 0` (flag means exactly the postcondition restricted to the first i elements).",
      "step: `(i+1, bal + ops[i], neg || (bal + ops[i] < 0))`: update the balance and OR in the new check.",
      "at exit (i = length) the invariant IS the postcondition, and `neg` is returned.",
      "Typical pattern: **scan with an accumulator** (a family named in doc 27)."]]))
parts.append("\n")
parts.append(ex("classic/classic_reverse", "Loop example 3 — reverse a list", "classic_reverse", "loop",
    ["The spec says \"element i of the result is element (n-1-i) of the input\"; the loop builds the result by consing elements one at a time.",
     ["`result.length = l.length`: same size.",
      "`∀ i < l.length, result[i]! = l[l.length-1-i]!`: position i of the output is the mirrored input position.",
      "`[i]!` is Lean's \"get element, or default if out of range\" (hence the `!`)."],
     ["state `(i, acc)`, start `(0, [])`; step `(i+1, l[i]! :: acc)` — each new element is put in FRONT of acc, which reverses the order.",
      "invariant `acc = (l.take i).reverse` — acc is the reverse of the first i elements. At i = length: `acc = l.reverse`.",
      "`helper lemma rev_getBang`: a small fact (proved by Lean) that `l.reverse[i]! = l[len-1-i]!`, which bridges the invariant to the indexed spec.",
      "Typical pattern: **builder** (map/reverse/filter into a new structure)."]]))
parts.append("""

---

# 2. RESTATE (the non-loop kind) — no iteration; the answer is one expression

Two sub-flavours (the label does not say which): (a) the postcondition is already a computable test, so the program IS that test; (b) the spec enumerates a search space and asks for the best member; the program is a brute-force search over the same enumeration (exponential on purpose).

""")
parts.append(ex("humaneval/he_002_truncate_number", "Restate example 1 — fractional part", "he_002_truncate_number", "restate",
    ["One `term` step: the answer is the formula `number - ⌊number⌋`. No search, no loop.",
     ["precondition `number ≥ 0` (a rational number Q).",
      "`|result - (number - ⌊number⌋)| ≤ 1/1000000`: result must equal number minus its floor, up to a tolerance (the original Python used floats).",
      "The spec nearly spells out the formula; the proof is basically \"the formula equals itself\" (distance 0 ≤ 1e-6)."],
     ["`kind: restate` — a single `term`. This is a 'declarative' case: the spec gave the formula away.",
      "Easy to certify, shows the spec is satisfiable, says nothing about algorithmic cleverness."]]))
parts.append("\n")
parts.append(ex("verina/verina_basic_1", "Restate example 2 — opposite signs (a decidable test)", "verina_basic_1", "restate",
    ["The postcondition is a plain boolean condition on the inputs, so the program is `decide` of that condition.",
     ["Two implications: if `a<0 ∧ b>0` or `a>0 ∧ b<0` then `result` is true; otherwise `result` is false.",
      "Both directions together: `result = true ⟺ (a<0∧b>0) ∨ (a>0∧b<0)`.",
      "Zero is neither positive nor negative (so 0 → false) — which the spec encodes through the strict `<`/`>`."],
     ["`term: decide ((a<0 ∧ b>0) ∨ (a>0 ∧ b<0))`: turn the Prop into a Bool and return it.",
      "Lean proves the postcondition by cases. This is the 'decidable check' flavour of restate."]]))
parts.append("\n")
parts.append(ex("verina/verina_advanced_30", "Restate example 3 — longest increasing streak (brute-force search)", "verina_advanced_30", "restate",
    ["Looks like an algorithm problem (a clever solution is one linear scan), but the derivation is NOT that: it is `foldl max` over ALL (start, length) pairs that qualify. That is the 'brute-force restatement'.",
     ["Case 1: empty list ⟹ result 0.",
      "Case 2: if result > 0 there EXISTS a start such that the window of length `result` is strictly increasing AND cannot be extended left or right (so it is a maximal streak of exactly that length).",
      "Case 3: no streak longer than `result` exists (every window of length result+1 has a non-increase).",
      "Note the bounded quantifiers via `List.range … |>.any/.all`: that makes the postcondition computable, hence testable."],
     ["`term`: take every start `s` in `0..n` and every length `L` with `s+L ≤ n` and 'all consecutive pairs in the window increase', then `foldl max 0` of the lengths. Exponential-ish and naive but obviously correct.",
      "`helper lemma streak30`: the 60-line proof (done by hand) that this expression satisfies all three cases — the actual work.",
      "Lesson: `restate` ≠ easy; here the proof is long but the PROGRAM is a one-liner. A `loop` could be shorter proof-wise (see example 1: 5 lines).",
      "This is why doc 28 asks whether LLM results should be reported separately for `loop` and `restate`."]]))
parts.append("""

---

# 3. DEFINITIONAL — the spec is already a program (3 tasks, all HumanEval)

The postcondition says `result = someRecursiveFunction input`. The answer is that function. These three specs define a helper function in the spec file (`fixSpec`, `romanSpec`, `evalOps`) and equate the result to it.
Because helper definitions live in `spec.lean` *above* the shown part, only the postcondition is shown below. A restate with a true formula is "satisfiable by a formula"; here the formula IS the spec, so the derivation is trivially correct and also tells you nothing about discovering an algorithm.

""")
parts.append(ex("humaneval/he_140_fix_spaces", "Definitional example 1 — fix spaces", "he_140_fix_spaces", "definitional",
    ["`term: String.mk (fixSpec text.length text.toList)`: one line, identical to the right-hand side of the spec.",
     ["`fixSpec` is a recursive helper (in the spec file's preamble) that walks the character list: spaces become `_`, runs longer than 2 become `-`.",
      "The postcondition: `result = String.mk (fixSpec text.length text.toList)` — just the definition applied."],
     ["Nothing to prove beyond reflexivity. The 'derivation' is the spec's own definition."]]))
parts.append("\n")
parts.append(ex("humaneval/he_156_int_to_mini_roman", "Definitional example 2 — integer to lowercase Roman", "he_156_int_to_mini_roman", "definitional",
    ["`romanSpec number number` — the recursive greedy Roman-numeral builder (with fuel = number) is defined IN the spec.",
     ["precondition `1 ≤ number ≤ 1000`.",
      "`result = romanSpec number number`: the first `number` is the remaining value, the second is fuel for the well-founded recursion."],
     ["`term: romanSpec number number` — same expression.",
      "The 'real' work (deciding the Roman-numeral rules) was done when WE WROTE the spec, not in the derivation. This is a place where spec correctness must be validated against tests (done: 11-16 per task)."]]))
parts.append("\n")
parts.append(ex("humaneval/he_160_do_algebra", "Definitional example 3 — evaluate an expression with operators", "he_160_do_algebra", "definitional",
    ["`evalOps operator.length operand operator` — an evaluator for the expression with correct precedence, defined in the spec.",
     ["precondition: operand count = operator count + 1, at least 2 operands, all operands ≥ 0, each operator one of `+ - * // **`.",
      "`result = evalOps operator.length operand operator`: precedence rules (`**` right-assoc, then `* //`, then `+ -`) live inside `evalOps`."],
     ["`term: evalOps operator.length operand operator` — again, the spec's own definition."]]))
parts.append("""

---

# Quick comparison

| | spec says | derivation is | proof effort | shows |
|---|---|---|---|---|
| loop | what a correct answer is (global property) | state machine with invariant | the invariant | the engine found an algorithm shape |
| restate (decidable) | a computable condition | `decide` / a formula | trivial | spec is satisfiable |
| restate (brute-force) | a property over an enumeration | `foldl max` over the same enumeration | can be long (lemmas) | spec reachable, not efficient |
| definitional | `result = g input` | `g input` | none | nothing about discovery |

Counts for the headline: 159 HumanEval = 87 loop + 69 restate + 3 definitional. 177 Verina = 65 loop + 112 restate.
""")
open(os.path.join(OUT, "Derivation_Kinds_Examples.md"), "w", encoding="utf8").write("".join(parts))
print("ok")
