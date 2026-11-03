# 04 — Coq (Rocq) Primer, From Zero

> **Prerequisites:** `02_Formal_Methods_Primer.md`, `03_Theorem_Provers_Landscape.md` (at least §4).
> **Goal:** read a small Coq file, write a few simple proofs, know how to run Coq from the command line, and understand how our Python code could drive it and read its errors.
>
> **Honesty note:** at the time of writing, **this machine has neither `coqc` nor `lean` installed**, and I could not run Coq here. The Coq snippets below are standard textbook-style and I believe them correct, but I did **not** execute them. Where a line might need a small tweak depending on your Coq version, I say so. Treat the first thing you do after installing as "paste these in and see".

---

## 0. Name change: Coq = Rocq

The project that was called **Coq** has been renamed **Rocq** (the rename was announced/rolled out over 2023–2025; Rocq 9.x is the first generation with the new name as I understand it — check the official site for exact version history). Consequences you'll meet:

- The Refine4LLM paper, older tutorials, Stack Overflow answers: all say "Coq".
- Command-line tools historically: `coqc` (compiler), `coqtop` (interactive), `coqide`. In newer releases there is a unified `rocq` command (e.g. `rocq c file.v`) and the old names may remain as compatibility wrappers. **I'm not certain which exist in your version — run `--version` after installing.**
- Standard-library module paths changed in newest versions (older: `From Coq Require Import Lia.`; newest: `From Stdlib Require Import Lia.`). If an `Import` line errors with "cannot find library", try the other prefix.

This document says "Coq" because that's what the paper says, and means the same system.

---

## 1. The mental model

Coq is two things at once:

1. A **functional programming language** (called **Gallina**) — like a small OCaml/Haskell.
2. A **proof environment** where *statements about those programs* are theorems and you prove them interactively.

```
   .v file
   ├── Definitions / Fixpoints      ← programs  (Gallina)
   ├── Theorem statements           ← specifications  (Props)
   └── Proof. tactics... Qed.       ← evidence  (checked by the kernel)
```

Remember from file 03: *propositions are types, proofs are values*. When you write `Proof. … Qed.` you are really (via tactics) constructing a value of the type that is your theorem statement; Coq's kernel type-checks it.

---

## 2. Gallina: data and functions

### 2.1 Inductive types

New data types are declared by listing their **constructors**. Natural numbers:

```coq
Inductive nat : Set :=
  | O : nat            (* zero *)
  | S : nat -> nat.    (* successor: "one more than" *)
```

So `3` is shorthand for `S (S (S O))`. This (it is already built in; you don't write it) is the heart of Coq: a number is *either zero or one more than a smaller number*. That's why **induction** works: to prove something for all numbers, prove it for `O`, and prove "if it holds for `n` then it holds for `S n`".

A list example:

```coq
Inductive list (A : Type) : Type :=
  | nil  : list A
  | cons : A -> list A -> list A.
```

### 2.2 `Definition` and `Fixpoint`

```coq
Definition double (n : nat) : nat := n + n.

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0   => 0
  | S k => n + sum_to k
  end.
```

- `Definition` = non-recursive function.
- `Fixpoint` = recursive function. **Coq insists recursion visibly shrinks** (here `k` is smaller than `S k`), which guarantees termination. This is the "variant" idea from file 02, enforced by the language! Every Coq function is total.

You can evaluate:

```coq
Compute sum_to 4.     (* prints:   = 10 : nat *)
```

---

## 3. Theorems and proofs

```coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
```

Line by line:

| Text | Meaning |
|---|---|
| `Theorem name : statement.` | Declare what we want to prove. `forall n : nat, ...` is `∀`. |
| `Proof.` | Enter proof mode. Coq now shows a **goal**. |
| `intros n.` | "Let `n` be an arbitrary natural number." Moves it into the context. |
| `simpl.` | Compute/simplify. `0 + n` reduces to `n` by the definition of `+`. |
| `reflexivity.` | Close a goal of the form `a = a`. |
| `Qed.` | Done. Kernel re-checks the whole proof. |

### Reading the proof state

In an IDE (CoqIDE, VS Code with the VsCoq or coq-lsp extension, Proof General in Emacs) you see this after `intros n.`:

```
   n : nat
   ============================
   0 + n = n
```

Above the line: **hypotheses** (what you know). Below: the **goal** (what you want). Each tactic transforms the goal until nothing remains. **This goal display is also what an LLM would be shown if it were a proof-writer.**

### A proof by induction

```coq
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| k IH].
  - (* base case: n = 0 *)
    reflexivity.
  - (* step: n = S k, IH : k + 0 = k *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.
```

- `induction n as [| k IH]` splits into two goals: base (`n = 0`) and step (`n = S k`, with an **induction hypothesis** `IH : k + 0 = k`).
- `- … ` are bullets, one per goal.
- `simpl` turns `S k + 0 = S k` into `S (k + 0) = S k`.
- `rewrite IH` replaces `k + 0` with `k` using the hypothesis, leaving `S k = S k`.
- `reflexivity` finishes. (Note `0 + n = n` was free by computation, but `n + 0 = n` needs induction: the definition of `+` recurses on its *first* argument. A famous early lesson.)

> **Common confusion — "`simpl` and `reflexivity` do the same thing."**
> `simpl` *computes* (rewrites with definitions); `reflexivity` *checks* both sides are already syntactically equal after computation. They cooperate.

> **Common confusion — "Qed means I understand it."**
> `Qed` means the kernel accepted it. A proof can be correct and unreadable; correctness and readability are separate.

---

## 4. The tactic cheat-sheet

| Tactic | Use when… |
|---|---|
| `intros x y H` | Goal is `forall x y, P -> Q`; bring `x`, `y`, `H : P` into context |
| `apply H` | You have `H : A -> B` and goal `B`; reduces goal to `A` |
| `exact H` | `H` is exactly the goal |
| `assumption` | Some hypothesis equals the goal |
| `simpl` | Unfold definitions / compute |
| `rewrite H` / `rewrite <- H` | Use equation `H : a = b` to replace `a` by `b` (or reverse) |
| `reflexivity` | Goal is `a = a` |
| `induction n` | Prove by induction on `n` |
| `destruct x` | Case analysis on `x` (e.g. zero vs successor, true vs false) |
| `split` | Goal is `A /\ B`; make two goals |
| `left` / `right` | Goal is `A \/ B`; pick a side |
| `lia` | **Linear Integer Arithmetic** solver — closes goals about `+`, `-`, constants, `<`, `<=`, over `nat`/`Z`. The workhorse for obligations like ours |
| `nia` | like `lia` but attempts some nonlinear (`x*x`) reasoning; less predictable |
| `auto`, `eauto` | Small depth-limited search with hint databases |
| `hammer` / `sauto` | CoqHammer: call external provers (needs the CoqHammer plugin) |

### Arithmetic example with `lia`

```coq
From Coq Require Import Lia.    (* newest versions: From Stdlib Require Import Lia. *)

Theorem succ_le : forall x y : nat, x < y -> x + 1 <= y.
Proof.
  intros x y H.
  lia.
Qed.
```

`lia` is a *decision procedure*: you don't script the proof, it just works (or tells you it can't). This is the Coq tactic most similar in spirit to how our code uses Z3.

---

## 5. How would our project's obligations look in Coq?

Take the integer-sqrt **exit obligation** from file 02: `I ∧ ¬G ⇒ Q`. Over integers (`Z`):

```coq
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Theorem sqrt_exit :
  forall N x : Z,
    x * x <= N ->                    (* invariant I *)
    ~ ((x + 1) * (x + 1) <= N) ->    (* loop exited: not G *)
    x * x <= N /\ N < (x + 1) * (x + 1).   (* postcondition Q *)
Proof.
  intros N x HI HnG.
  split.
  - exact HI.
  - lia.   (* ~(a <= b) gives b < a ; if lia struggles with the products, try nia *)
Qed.
```

Not executed by me — see the honesty note. If `lia` complains about the products, `nia` or first introducing names for `x*x` and `(x+1)*(x+1)` are the standard workarounds. That fragility around nonlinear terms is itself informative: **Coq's automation is not magically better than Z3 at `x*x`**; what Coq adds is (a) the kernel guarantee and (b) the ability to do induction and manual reasoning when automation fails.

---

## 6. Using Coq from the command line

Typical workflow, assuming a working install:

```
   file:   sqrt.v
   run:    coqc sqrt.v          (or, in newer versions, possibly:  rocq c sqrt.v )
```

- **Success:** no output, exit code `0`, and a compiled artifact (`sqrt.vo`) appears.
- **Failure:** non-zero exit code, and an error message on **stderr**, e.g. (shape only; exact text varies by version):

```
File "./sqrt.v", line 12, characters 2-5:
Error: Tactic failure: Cannot find witness.
```

or

```
File "./sqrt.v", line 9, characters 4-10:
Error:
In environment
N, x : Z
HI : x * x <= N
The term "..." has type ... while it is expected to have type ...
```

Useful flags (check your version's `coqc --help`; I'm describing them from memory): `-q` (don't load init files), `-R dir Name` / `-Q dir Name` (map a directory to a library name), `-w` (warning settings).

Interactive: `coqtop` (a REPL where you type commands) — mostly superseded by IDE integration.

---

## 7. Installing on Windows — honest options

State on this machine: **no `coqc`, no `coqtop` found on PATH.** Options, from most to least convenient (I have not verified current download pages; follow the official site, https://rocq-prover.org — formerly coq.inria.fr):

1. **Official Windows installer / "Coq Platform" / Rocq Platform.** A bundled installer providing Coq/Rocq plus common libraries (and CoqIDE). Historically the recommended route for Windows. Check the official site for what's currently offered.
2. **WSL2 (Windows Subsystem for Linux) + `opam`.** Install Ubuntu in WSL, then use OCaml's package manager `opam` to install Coq/Rocq (`opam install coq` or the Rocq equivalent). Most reliable for *scripting*, and Coq's ecosystem (e.g. CoqHammer, which is installed via opam) is best supported on Linux/macOS.
3. **Docker.** An official image exists historically (`coqorg/coq`); useful for reproducible runs. You have Docker on this machine (its binary was on PATH in the environment listing).

Recommendation for *this project*: **WSL2 or Docker**, because our Python code needs to call a command and parse text, and CoqHammer is easiest on Linux. Then call it from Windows via `wsl coqc file.v`.

Editor: VS Code with the **VsCoq** or **coq-lsp** extension gives you the goal display.

---

## 8. How our Python code could call Coq and read errors

The idea: for each proof obligation, generate a small `.v` file, run Coq, interpret the exit status.

```python
# SKETCH ONLY - not part of the repo, not tested here (no Coq installed).
import subprocess, tempfile, pathlib

def check_with_coq(theorem_src: str, timeout=30):
    with tempfile.TemporaryDirectory() as d:
        f = pathlib.Path(d) / "obl.v"
        f.write_text(theorem_src, encoding="utf-8")
        try:
            p = subprocess.run(["coqc", str(f)], capture_output=True,
                               text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "UNKNOWN", "timeout"
        if p.returncode == 0:
            return "PROVED", ""
        return "FAILED_OR_STUCK", p.stderr      # parse this
```

Design points that matter (and why this is harder than Z3):

1. **Three outcomes, not two.** Coq won't say "here's a counterexample." A failing tactic means *either* the statement is false *or* the tactic is too weak. So `FAILED` in Z3's sense (a falsifying model) does **not** exist; you only get "stuck". That's closer to Z3's `unknown`. A hybrid design would **use Z3 first to find counterexamples** (cheap, informative) and Coq to certify.
2. **Fixed tactic script.** The LLM could propose the proof, but a robust baseline is a fixed script: `intros; lia.` or `intros; nia.` or `hammer.`, tried in order.
3. **Error parsing.** stderr has file/line/character ranges and a free-text message. Extract the `Error:` block; show the unsolved goal if present. The shape changes between versions — write tolerant regexes and keep the raw text as a fallback.
4. **Cost.** Each call spawns a process and loads libraries — expect it to be far slower than `z3.Solver().check()`. Cache results; batch obligations in one file.
5. **Translation.** Our L_spec AST (`FormalLLM/lspec/ast.py`) would need a printer into Coq syntax (precedence, `Z` vs `nat` vs `R`, `/\` is already Coq's conjunction spelling — see §9).
6. **Encodings of arrays/real numbers** are non-trivial (Coq's `R` reals are axiomatic; automation like `lra` helps but is not decision-complete the way Z3's real arithmetic is).

---

## 9. Why the Refine4LLM paper chose Coq

From the paper (Section on the specification language and Section 9.1.3 "Implementation"):

- *"Our specification language L_spec extends first-order logic (FOL) and is a subset of the language of Coq. Most LLMs are familiar with both FOL and Coq grammar."* — i.e. LLMs have seen lots of Coq text, so writing specs and parameters in Coq-flavoured syntax is something they do well. That is why this repo's L_spec uses spellings like `/\` and `\/`.
- *"We implement our approach based on Coq, CoqHammer, and GPT-4. The automatic verification is based on CoqHammer… incorporate four automated theorem provers, including cvc4, vampire, Eprover and Z3."*
- Prior art in the related-work section: refinement calculus embedded in Coq (Swierstra & Alpuim), and the Fiat system (built on Coq).

Then, in *this* repository the author implemented a **Z3-only** backend (a "personal, independent implementation", per the README). That is a deliberate simplification — and also the reason Lean/Coq backends are interesting *future* work, not current code. There is no Coq or Lean code in the repo today.

---

## 10. Check yourself

1. What are the two things Coq "is" at once?
2. Why is `0 + n = n` provable with just `simpl; reflexivity` but `n + 0 = n` needs induction?
3. What does `Qed.` do?
4. What does `lia` do, and which Z3-concept is it closest to?
5. Give two reasons a Coq backend couldn't simply "return a counterexample" like Z3 does.
6. Why did the paper say L_spec is a subset of Coq's language?
7. On this machine, what must you do before any of the snippets run?

<details><summary>Answers</summary>

1. A functional programming language (Gallina) and a proof environment.
2. `+` is defined by recursion on its first argument, so `0 + n` computes away but `n + 0` doesn't without knowing `n`'s shape.
3. Ends the proof; the kernel re-checks the whole constructed proof term and records the theorem.
4. Decides linear integer arithmetic goals automatically; closest to an SMT solver's arithmetic theory.
5. A failed tactic doesn't mean the statement is false (the tactic could be too weak), and Coq has no built-in model finder for arbitrary goals.
6. LLMs have seen a lot of Coq/FOL text, so they generate and read it reliably.
7. Install Coq/Rocq (see §7); neither `coqc` nor `lean` is present now.
</details>

---

*Next:* `05_Lean_Primer.md` (the newer alternative), then `06_Z3_and_SMT_Primer.md`.
