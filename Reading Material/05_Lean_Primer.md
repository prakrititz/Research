# 05 — Lean 4 Primer, From Zero

> **Prerequisites:** `02_Formal_Methods_Primer.md`, `03_Theorem_Provers_Landscape.md` (§4). Reading `04_Coq_Primer.md` first helps — Lean is a close cousin, and I compare them often.
>
> **Honesty note:** **Lean is not installed on this machine** (neither is Coq). I could not execute any Lean here. The snippets below are standard introductory Lean 4 that I believe correct, but treat the first run after installing as the test. Tool details (flags, versions) change quickly; I flag the ones I'm unsure of.

---

## 1. What Lean is

**Lean 4** is, like Coq, simultaneously a **programming language** and a **proof assistant** built on dependent type theory (the Curry–Howard idea from file 03: propositions are types, proofs are values, a small kernel checks them).

What makes it feel different from Coq:

- **Modern, fast, one language for everything.** Tactics, notation, and even the proof automation are written *in Lean itself* — you extend Lean with Lean.
- **Mathlib.** A huge community-maintained library of formalised mathematics. Much of today's "AI proves theorems" work targets Lean + Mathlib.
- **Tooling:** `elan` (version manager), `lake` (build system / package manager), a language server with excellent VS Code integration (the *infoview* panel shows your proof state live).
- **Software verification too.** A recent paper listed in this project's reading (`CACM_LLM_FM.pdf`) mentions the Lean Computer Science Library (CSLib) as a sign of Lean being used beyond pure math.

---

## 2. Writing programs and statements

### Definitions

```lean
def double (n : Nat) : Nat := n + n

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumTo n

#eval sumTo 4        -- prints 10
```

- `def` defines a function. `Nat` is the natural numbers.
- Pattern-matching `| 0 => … | n + 1 => …` is the analogue of Coq's `match`/`Fixpoint`. Recursion must visibly shrink (Lean checks it terminates, same idea as in Coq).
- `#eval` runs a program; `#check` shows a type; `#print` shows a definition.

### Structures (records)

```lean
structure Point where
  x : Nat
  y : Nat

def origin : Point := { x := 0, y := 0 }
```

### Theorems

```lean
theorem add_zero' (n : Nat) : n + 0 = n := by
  simp
```

- `theorem name (args) : statement := by <tactics>`.
- `by` starts a tactic block (alternatively you can write a proof term directly after `:=`).
- `example : … := …` is an unnamed theorem, handy for experiments.

---

## 3. Tactics (the ones you'll meet first)

| Tactic | What it does |
|---|---|
| `intro x` | Same as Coq `intros`: introduce a `∀` variable or hypothesis |
| `exact h` | The term `h` is exactly the goal |
| `apply h` | Use `h : A → B` to reduce goal `B` to `A` |
| `rfl` | Goal is `a = a` (up to computation) |
| `simp` | Simplify using a large database of rewrite lemmas |
| `rw [h]` | Rewrite with equation `h` |
| `omega` | **Decision procedure for linear integer/natural arithmetic** (the Lean counterpart of Coq's `lia`, and the one most like what we need) |
| `induction n with …` | Induction (see below) |
| `cases h` / `rcases` | Case analysis / destructure `∧`, `∨`, `∃` |
| `constructor` | Build `∧` / `↔` / structure goals |
| `decide` | Settle small decidable propositions by computation |
| `simp_all`, `aesop` | Heavier automation (`aesop` from the Mathlib ecosystem) |

### Examples

```lean
-- linear arithmetic: omega just does it
theorem succ_le (a b : Nat) (h : a < b) : a + 1 ≤ b := by
  omega

-- decide: evaluates a closed decidable statement
example : sumTo 3 = 6 := by decide

-- induction syntax (simp alone would also prove this one)
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp
```

> **Common confusion — "`decide` proves anything."**
> Only *closed, decidable* statements small enough to evaluate. `decide` cannot prove "∀ n, …" — that's what induction is for.

> **Common confusion — "`omega` handles `x*x`."**
> `omega` is for *linear* arithmetic (multiplication only by constants). Nonlinear terms like `x*x` are treated as opaque or rejected. That is exactly the same weak spot as Z3's integer solver — see file 06. Mathlib has `nlinarith`/`positivity` for some nonlinear cases (these need Mathlib).

### The sqrt exit obligation in Lean

```lean
theorem sqrt_exit (N x : Int)
    (hI : x * x ≤ N) (hnG : ¬ ((x + 1) * (x + 1) ≤ N)) :
    x * x ≤ N ∧ N < (x + 1) * (x + 1) := by
  constructor
  · exact hI
  · omega     -- the non-linear products appear identically on both sides; if omega
              -- rejects them, state them as named variables or use Mathlib's nlinarith
```

(Unexecuted — see honesty note. Whether `omega` normalises `(x+1)*(x+1)` as an atom is something to try; the fallback is `exact lt_of_not_ge hnG` style lemmas or `Int.not_le.mp hnG`. The lesson is the *shape*, not that exact tactic.)

---

## 4. The toolchain

### 4.1 `elan`: the version manager

`elan` is to Lean what `rustup` is to Rust. It installs and switches Lean versions per project. On Windows the official route is a PowerShell/installer script from the Lean website's install page (https://lean-lang.org — I have not fetched the exact current command; **follow the official "Install" page**). It also supports WSL/Linux.

After installing you should have on PATH: `lean`, `lake`, `elan`.

### 4.2 `lake`: the build tool

```
   lake new myproj          # make a project (creates lakefile, toolchain file, Main.lean …)
   cd myproj
   lake build               # compile
   lake exe myproj          # run the executable
```

A project pins its Lean version in a `lean-toolchain` file; `elan` fetches it automatically. To use Mathlib you declare it as a dependency in the lakefile (Lake manifests/`lakefile.toml` or `lakefile.lean` — format depends on version) and run `lake update`; the first fetch downloads cached compiled Mathlib (large, hundreds of MB to GB).

### 4.3 Calling `lean` directly

For a single file with no dependencies:

```
   lean myfile.lean
```

- **Success:** no errors (it may print `#eval` output and warnings), exit code `0`.
- **Failure:** non-zero exit code and messages like

```
myfile.lean:7:2: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  ...
```

(shape from memory; text varies by version.) Interestingly, **`omega` itself reports a possible counterexample** when it fails — closer to Z3's behaviour than Coq's `lia` — one reason Lean is attractive for an LLM feedback loop. I'm fairly (not fully) sure of this, so verify it on your version.

When a file imports Mathlib or other packages, run through the project: `lake env lean myfile.lean`.

### 4.4 Machine-readable output

Recent Lean 4 versions have a `--json` command-line flag that prints each message as a JSON object (with file, position, severity, text), which is much easier for a program to parse than free text. I believe this exists but I **have not confirmed it on your version — check `lean --help`.** If it is missing, parse the `file:line:col: error:` prefix with a regex.

### 4.5 Interactive and AI-oriented tools

- **Language server / VS Code extension:** shows the goal state next to your cursor.
- **Lean REPL** (a community tool, `leanprover-community/repl`): you send JSON commands over stdin and receive JSON responses including *goal states after each tactic* — designed so programs (including LLMs) can drive Lean step by step. Check its README for the current protocol.
- **LeanDojo:** a research toolkit that extracts proofs/tactic states from Mathlib and provides an environment for ML models to interact with Lean; the position paper in `Dr. Hou's Studies/` mentions retrieval-augmented provers built on it. (It describes LeanDojo as employing retrieval-augmented generation for premise selection.)
- **Lean Copilot / similar:** LLM-assisted tactic suggestions inside Lean (exists; I haven't evaluated current maturity).

---

## 5. Our Python code calling Lean

Same shape as the Coq sketch in file 04, with better feedback possibilities:

```python
# SKETCH ONLY - untested (no Lean installed here).
import subprocess, tempfile, pathlib, json

def check_with_lean(src: str, timeout=30):
    with tempfile.TemporaryDirectory() as d:
        f = pathlib.Path(d) / "Obl.lean"
        f.write_text(src, encoding="utf-8")
        try:
            p = subprocess.run(["lean", "--json", str(f)],
                               capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "UNKNOWN", "timeout"
        msgs = [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")]
        errors = [m for m in msgs if m.get("severity") == "error"]
        if p.returncode == 0 and not errors:
            return "PROVED", ""
        return "FAILED_OR_STUCK", "\n".join(m.get("data", "") for m in errors)
```

(The JSON field names above — `severity`, `data` — are my recollection; verify against real output before building on them.)

Design issues are the same as with Coq: process start-up cost (Lean is usually quick for a single file without Mathlib, slow if Mathlib is imported), translation from L_spec AST to Lean syntax, and the "stuck ≠ false" ambiguity.

---

## 6. Honest comparison: Coq vs Lean as an LLM-driven verification backend

| Criterion | Coq / Rocq | Lean 4 |
|---|---|---|
| Used by the original paper | **Yes** (with CoqHammer) | No |
| L_spec "is a subset of Coq" | **Direct fit** — syntax like `/\`, `\/` already Coq-ish | Needs a translator (`∧`, `∨`, `¬`) |
| LLM familiarity | Large corpus, mostly older | Large and rapidly growing corpus; most current ML-for-theorem-proving research targets Lean |
| Linear arithmetic automation | `lia` (mature) | `omega` (built in, mature for ℕ/ℤ) |
| Nonlinear | `nia` (fragile) | `nlinarith` (needs Mathlib; fragile) |
| "Hammer" | **CoqHammer** (exists, drives 4 ATPs) | No equal-maturity hammer that I can vouch for |
| Failure feedback | Error + goal state; no counterexample | Error + goal state; `omega` can show a possible counterexample |
| Programmatic interface | `coqc`, `coqtop`, `coq-lsp`, SerAPI (older) | `lean`, `lake`, `--json`, REPL, language server |
| Windows story | Installer or WSL/Docker | `elan` supports Windows natively (verify current status); WSL also fine |
| Ecosystem momentum | Strong in software verification | Strong in math + AI research |

**Bottom line for this project (my reasoned opinion, not a measured fact):**

- If the goal is to *reproduce the paper*, Coq + CoqHammer is the faithful choice.
- If the goal is to *add a robust second backend on a Windows dev machine and let an LLM iterate*, Lean 4 is probably the lower-friction choice (native tooling, JSON, `omega` feedback), at the cost of translating L_spec.
- Either way, Z3 should stay: it is the only one of the three that returns **concrete counterexamples cheaply**, and those are what taught the LLM in the project's own measurements. A plausible architecture is **Z3 first (fast refutation) → proof assistant to certify / prove what Z3 returns `unknown` on.** I haven't built or measured it.

---

## 7. Check yourself

1. How does `theorem foo : stmt := by tac` differ from `def`? (What's the "value" of a theorem?)
2. When would you choose `omega` vs `simp` vs `decide`?
3. Why does `omega` struggle with `x*x ≤ N`?
4. What is `elan`? What is `lake`?
5. Why is "stuck" in Lean/Coq not equivalent to Z3's `sat`?
6. Name two programmatic ways to learn *why* a Lean proof failed.

<details><summary>Answers</summary>

1. A theorem's "value" is its proof — a term whose type is the statement. It is checked, not computed with.
2. `omega`: linear integer/natural arithmetic. `simp`: rewriting/simplification with known lemmas. `decide`: small closed decidable props.
3. It supports only linear arithmetic; products of variables are outside its fragment.
4. `elan` manages Lean toolchain versions; `lake` builds projects and manages dependencies (e.g. Mathlib).
5. A failed tactic may just be too weak; `sat` gives an actual falsifying assignment proving the claim false.
6. Parse `lean --json` (if available) / the `file:line:col: error` text; or use the Lean REPL to get goal states.
</details>

---

*Next:* `06_Z3_and_SMT_Primer.md` — the tool the project actually uses today.
