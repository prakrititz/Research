r"""Hand-written derivations ("oracles") for the Lean specification library, run through the Lean engine.

An oracle is a derivation tree (the JSON of ``FormalLLM/lean/laws.py``) that a person wrote for a specification. Running it
measures two things that no model is involved in:

* whether the **specification is derivable at all** with the four laws (term, cases, bind, loop): an oracle that the engine
  accepts and certifies proves the task is within reach, and the program it yields passes the task's tests;
* where **Lean's tactic cascade is too weak**: every obligation that the cascade cannot close is listed with its goal state, and
  those are the lemmas the engine's library has to supply (``FormalLLM/lean/lemmas.py``).

    python benchmarks/datasets/lean_oracle.py [--only ID ...] [--imports full]   # -> benchmarks/results/lean_specs/oracle.json
"""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
LIBRARY = os.path.join(ROOT, "benchmarks", "datasets", "lean_specs")
RESULTS = os.path.join(ROOT, "benchmarks", "results", "lean_specs")


def loop(state, init, invariant, guard, variant, result, body):
    return {"law": "loop", "state": state, "init": init, "invariant": invariant, "guard": guard, "variant": variant,
            "result": result, "children": [body]}


def term(expr):
    return {"law": "term", "expr": expr, "children": []}


def cases(cond, yes, no):
    return {"law": "cases", "cond": cond, "children": [yes, no]}


def with_lemmas(tree, lemmas):
    """The same step, bringing helper lemmas (name, statement, proof) that Lean proves first."""
    return {**tree, "lemmas": lemmas}


def bind(var, type_, prop, first, second):
    return {"law": "bind", "var": var, "type": type_, "prop": prop, "children": [first, second]}


ORACLES = {
    # --- one step: the answer is an expression ---
    "he_023_strlen": term("s.length"),
    "he_041_car_race_collision": term("n * n"),
    "he_097_multiply": term("((a.natAbs % 10 : Nat) : Int) * ((b.natAbs % 10 : Nat) : Int)"),
    "he_138_is_equal_to_sum_even": term("decide (n ≥ 8 ∧ n % 2 = 0)"),
    "he_157_right_angle_triangle": term("decide (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a)"),
    # --- a loop over a counter ---
    "he_060_sum_to_n": loop([["i", "Nat"], ["s", "Nat"]], ["0", "0"], "s * 2 = i * (i + 1) ∧ i ≤ n", "i < n", "n - i", "s",
                            term("(i + 1, s + (i + 1))")),
    "he_100_make_a_pile": loop([["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
                               "acc.length = i ∧ i ≤ n ∧ ∀ k, k < i → acc[k]! = n + 2 * k", "i < n", "n - i", "acc",
                               term("(i + 1, acc ++ [n + 2 * i])")),
    "he_042_incr_list": loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
                             "acc.length = i ∧ i ≤ l.length ∧ ∀ k, k < i → acc[k]! = l[k]! + 1", "i < l.length",
                             "l.length - i", "acc", term("(i + 1, acc ++ [l[i]! + 1])")),
    # --- a loop that decides by scanning ---
    "he_052_below_threshold": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                   "i ≤ l.length ∧ (ok = true ↔ ∀ k, k < i → l[k]! < t)", "i < l.length", "l.length - i",
                                   "ok", term("(i + 1, ok && decide (l[i]! < t))")),
    "he_057_monotonic": bind("up", "Bool", "up = true ↔ ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!",
                             loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                  "i ≤ l.length - 1 ∧ (ok = true ↔ ∀ k, k < i → l[k]! ≤ l[k + 1]!)", "i < l.length - 1",
                                  "l.length - 1 - i", "ok", term("(i + 1, ok && decide (l[i]! ≤ l[i + 1]!))")),
                             bind("down", "Bool", "down = true ↔ ∀ i, i < l.length - 1 → l[i]! ≥ l[i + 1]!",
                                  loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                       "i ≤ l.length - 1 ∧ (ok = true ↔ ∀ k, k < i → l[k]! ≥ l[k + 1]!)", "i < l.length - 1",
                                       "l.length - 1 - i", "ok", term("(i + 1, ok && decide (l[i]! ≥ l[i + 1]!))")),
                                  term("up || down"))),
    "he_043_pairs_sum_to_zero": loop([["j", "Nat"], ["found", "Bool"]], ["0", "false"],
                                     "j ≤ l.length ∧ (found = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ l[a]! + l[b]! = 0)",
                                     "j < l.length", "l.length - j", "found",
                                     bind("hit", "Bool", "hit = true ↔ ∃ a, a < j ∧ l[a]! + l[j]! = 0",
                                          loop([["i", "Nat"], ["seen", "Bool"]], ["0", "false"],
                                               "i ≤ j ∧ (seen = true ↔ ∃ a, a < i ∧ l[a]! + l[j]! = 0)", "i < j", "j - i",
                                               "seen", term("(i + 1, seen || decide (l[i]! + l[j]! = 0))")),
                                          term("(j + 1, found || hit)"))),
    # --- a loop that searches for the extreme value ---
    "he_035_max_element": loop([["i", "Nat"], ["m", "Int"]], ["1", "l.head!"],
                               "1 ≤ i ∧ i ≤ l.length ∧ (∃ k, k < i ∧ l[k]! = m) ∧ ∀ k, k < i → l[k]! ≤ m", "i < l.length",
                               "l.length - i", "m", term("(i + 1, max m l[i]!)")),
    # --- a loop on a number that decides divisibility facts ---
    "he_031_is_prime": cases("n < 2", term("false"),
                             loop([["d", "Nat"], ["ok", "Bool"]], ["2", "true"],
                                  "2 ≤ d ∧ d ≤ n ∧ (ok = true ↔ ∀ k, k < d → k ≥ 2 → n % k ≠ 0)", "d < n", "n - d", "ok",
                                  term("(d + 1, ok && decide (n % d ≠ 0))"))),
    "he_024_largest_divisor": loop([["d", "Nat"]], ["n - 1"], "1 ≤ d ∧ d < n ∧ ∀ k, k < n → d < k → n % k ≠ 0",
                                   "n % d ≠ 0", "d", "d", term("d - 1")),
    # --- a loop that builds a list ---
    "he_030_get_positive": loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
                                "i ≤ l.length ∧ acc = (l.take i).filter (fun x => x > 0)", "i < l.length", "l.length - i",
                                "acc", term("(i + 1, if l[i]! > 0 then acc ++ [l[i]!] else acc)")),
    "he_062_derivative": loop([["k", "Nat"], ["acc", "List Int"]], ["0", "[]"],
                              "k ≤ xs.length - 1 ∧ acc.length = k ∧ ∀ m, m < k → acc[m]! = xs[m + 1]! * ((m : Int) + 1)",
                              "k < xs.length - 1", "xs.length - 1 - k", "acc",
                              term("(k + 1, acc ++ [xs[k + 1]! * ((k : Int) + 1)])")),
    "he_152_compare": loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
                           "i ≤ game.length ∧ acc.length = i ∧ ∀ k, k < i → acc[k]! = ((game[k]! - guess[k]!).natAbs : Int)",
                           "i < game.length", "game.length - i", "acc",
                           term("(i + 1, acc ++ [((game[i]! - guess[i]!).natAbs : Int)])")),
    # --- loops with a sum or a count over the prefix read so far ---
    "he_003_below_zero": loop([["i", "Nat"], ["bal", "Int"], ["neg", "Bool"]], ["0", "0", "false"],
                              "i ≤ operations.length ∧ bal = (operations.take i).sum ∧ "
                              "(neg = true ↔ ∃ k, k ≤ i ∧ (operations.take k).sum < 0)",
                              "i < operations.length", "operations.length - i", "neg",
                              term("(i + 1, bal + operations[i]!, neg || decide (bal + operations[i]! < 0))")),
    "he_121_solution": loop([["i", "Nat"], ["s", "Int"]], ["0", "0"],
                            "i ≤ lst.length ∧ s = (((List.range i).filter (fun j => j % 2 = 0 ∧ lst[j]! % 2 = 1)).map "
                            "(fun j => lst[j]!)).sum",
                            "i < lst.length", "lst.length - i", "s",
                            term("(i + 1, if i % 2 = 0 ∧ lst[i]! % 2 = 1 then s + lst[i]! else s)")),
    "he_085_add_even_at_odd": loop([["i", "Nat"], ["s", "Int"]], ["0", "0"],
                                   "i ≤ lst.length ∧ s = (((List.range i).filter (fun j => j % 2 = 1 ∧ lst[j]! % 2 = 0)).map "
                                   "(fun j => lst[j]!)).sum",
                                   "i < lst.length", "lst.length - i", "s",
                                   term("(i + 1, if i % 2 = 1 ∧ lst[i]! % 2 = 0 then s + lst[i]! else s)")),
    # --- loops whose specification is a recursive function ---
    "he_055_fib": loop([["i", "Nat"], ["a", "Nat"], ["b", "Nat"]], ["0", "0", "1"],
                       "i ≤ n ∧ a = fibSpec i ∧ b = fibSpec (i + 1)", "i < n", "n - i", "a", term("(i + 1, b, a + b)")),
    "he_139_special_factorial": loop([["i", "Nat"], ["fact", "Nat"], ["total", "Nat"]], ["0", "1", "1"],
                                     "i ≤ n ∧ fact = factSpec i ∧ total = ((List.range i).map (fun j => factSpec (j + 1))).prod",
                                     "i < n", "n - i", "total", term("(i + 1, fact * (i + 1), total * (fact * (i + 1)))")),
    # --- a check on a string, a bind of two parts ---
    "he_048_is_palindrome": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                 "i ≤ text.length ∧ (ok = true ↔ ∀ k, k < i → text.toList[k]! = text.toList[text.length - 1 - k]!)",
                                 "i < text.length", "text.length - i", "ok",
                                 term("(i + 1, ok && decide (text.toList[i]! = text.toList[text.length - 1 - i]!))")),
    "he_072_will_it_fly": bind("pal", "Bool", "pal = true ↔ ∀ i, i < q.length → q[i]! = q[q.length - 1 - i]!",
                               loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                    "i ≤ q.length ∧ (ok = true ↔ ∀ k, k < i → q[k]! = q[q.length - 1 - k]!)", "i < q.length",
                                    "q.length - i", "ok", term("(i + 1, ok && decide (q[i]! = q[q.length - 1 - i]!))")),
                               term("pal && decide (q.sum ≤ w)")),
    # --- string and list builders over a counter ---
    "he_028_concatenate": loop([["i", "Nat"], ["acc", "String"]], ["0", "\"\""],
                               "i ≤ strings.length ∧ acc = String.join (strings.take i)", "i < strings.length",
                               "strings.length - i", "acc", term("(i + 1, acc ++ strings[i]!)")),
    "he_029_filter_by_prefix": loop([["i", "Nat"], ["acc", "List String"]], ["0", "[]"],
                                    "i ≤ strings.length ∧ acc = (strings.take i).filter (fun s => s.startsWith prefix_)",
                                    "i < strings.length", "strings.length - i", "acc",
                                    term("(i + 1, if strings[i]!.startsWith prefix_ then acc ++ [strings[i]!] else acc)")),
    "he_066_digit_sum": loop([["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
                             "i ≤ s.length ∧ acc = (((s.toList.take i).filter Char.isUpper).map Char.toNat).sum",
                             "i < s.length", "s.length - i", "acc",
                             term("(i + 1, if s.toList[i]!.isUpper then acc + s.toList[i]!.toNat else acc)")),
    "he_098_count_upper": loop([["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
                               "i ≤ s.length ∧ acc = ((List.range i).filter (fun j => j % 2 = 0 ∧ s.toList[j]! ∈ "
                               "['A', 'E', 'I', 'O', 'U'])).length",
                               "i < s.length", "s.length - i", "acc",
                               term("(i + 1, if i % 2 = 0 ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'] then acc + 1 else acc)")),
    "he_061_correct_bracketing": loop(
        [["i", "Nat"], ["d", "Int"], ["ok", "Bool"]], ["0", "0", "true"],
        "i ≤ brackets.length ∧ d = ((brackets.toList.take i).count '(' : Int) - ((brackets.toList.take i).count ')' : Int) ∧ "
        "(ok = true ↔ ∀ k, k ≤ i → (brackets.toList.take k).count '(' ≥ (brackets.toList.take k).count ')')",
        "i < brackets.length", "brackets.length - i", "ok && decide (d = 0)",
        term("(i + 1, d + (if brackets.toList[i]! = '(' then 1 else if brackets.toList[i]! = ')' then -1 else 0), "
             "ok && decide (d + (if brackets.toList[i]! = '(' then 1 else if brackets.toList[i]! = ')' then -1 else 0) ≥ 0))")),
    "he_126_is_sorted": bind("a", "Bool", "a = true ↔ ∀ i, i < lst.length - 1 → lst[i]! ≤ lst[i + 1]!",
                             loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                  "i ≤ lst.length - 1 ∧ (ok = true ↔ ∀ k, k < i → lst[k]! ≤ lst[k + 1]!)", "i < lst.length - 1",
                                  "lst.length - 1 - i", "ok", term("(i + 1, ok && decide (lst[i]! ≤ lst[i + 1]!))")),
                             bind("b", "Bool", "b = true ↔ ∀ x ∈ lst, lst.count x ≤ 2",
                                  loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                                       "i ≤ lst.length ∧ (ok = true ↔ ∀ k, k < i → lst.count lst[k]! ≤ 2)", "i < lst.length",
                                       "lst.length - i", "ok", term("(i + 1, ok && decide (lst.count lst[i]! ≤ 2))")),
                                  term("a && b"))),
    # --- classic algorithms; the helper lemmas are the facts a person would cite from a textbook ---
    "classic_isqrt": loop([["r", "Nat"]], ["0"], "r * r ≤ n", "(r + 1) * (r + 1) ≤ n", "n - r", "r", term("r + 1")),
    "classic_sqrt_approx": with_lemmas(
        loop([["k", "Nat"]], ["0"], "((k : ℚ) * e) * ((k : ℚ) * e) ≤ N", "(((k : ℚ) + 1) * e) * (((k : ℚ) + 1) * e) ≤ N",
             "⌊(N + 1) / e⌋₊ + 1 - k", "(k : ℚ) * e", term("k + 1")),
        [{"name": "floor_bound", "statement": "∀ (N e : ℚ) (k : ℕ), 0 ≤ N → 0 < e → ((k + 1 : ℚ) * e) * ((k + 1 : ℚ) * e) ≤ N → "
                                             "⌊(N + 1) / e⌋₊ + 1 - (k + 1) < ⌊(N + 1) / e⌋₊ + 1 - k",
          "proof": "by intro N e k hN he h\n  have h1 : ((k + 1 : ℚ) * e) ≤ N + 1 := by\n    by_cases hle : ((k + 1 : ℚ) * e) ≤ 1\n"
                   "    · linarith\n    · push_neg at hle; nlinarith\n  have h2 : ((k + 1 : ℕ) : ℚ) ≤ (N + 1) / e := by\n"
                   "    rw [le_div_iff₀ he]; push_cast; exact h1\n  have h3 : k + 1 ≤ ⌊(N + 1) / e⌋₊ := Nat.le_floor h2\n  omega"}]),
    "classic_fast_power": with_lemmas(
        loop([["acc", "Int"], ["base", "Int"], ["k", "Nat"]], ["1", "b", "e"], "acc * base ^ k = b ^ e", "k > 0", "k", "acc",
             cases("k % 2 = 1", term("(acc * base, base * base, k / 2)"), term("(acc, base * base, k / 2)"))),
        [{"name": "pow_odd_split", "statement": "∀ (base : Int) (k : Nat), k % 2 = 1 → base ^ k = base * (base * base) ^ (k / 2)",
          "proof": "by intro base k h\n  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩\n  have : (2 * m + 1) / 2 = m := by omega\n"
                   "  rw [this, pow_succ, pow_mul]; ring"},
         {"name": "pow_even_split", "statement": "∀ (base : Int) (k : Nat), k % 2 = 0 → base ^ k = (base * base) ^ (k / 2)",
          "proof": "by intro base k h\n  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩\n  have : (2 * m) / 2 = m := by omega\n"
                   "  rw [this, pow_mul]; ring"}]),
    "classic_sort_list": with_lemmas(
        term("l.mergeSort (fun a b => a ≤ b)"),
        [{"name": "sort_ok", "statement": "∀ (l : List Int), (∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 → "
                                          "(l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ "
                                          "(l.mergeSort (fun a b => decide (a ≤ b))).isPerm l = true",
          "proof": "by intro l\n  have hp : (l.mergeSort (fun a b => decide (a ≤ b))).Perm l := List.mergeSort_perm l _\n"
                   "  refine ⟨?_, List.isPerm_iff.mpr hp⟩\n  intro i hi\n"
                   "  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (l.mergeSort (fun a b => decide (a ≤ b))) :=\n"
                   "    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) l\n"
                   "  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (l.mergeSort (fun a b => decide (a ≤ b))).length := by omega\n"
                   "  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"}]),
    "classic_reverse": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"], "i ≤ l.length ∧ acc = (l.take i).reverse", "i < l.length",
             "l.length - i", "acc", term("(i + 1, l[i]! :: acc)")),
        [{"name": "rev_getBang", "statement": "∀ (l : List Int) (i : Nat), i < l.length → l.reverse[i]! = l[l.length - 1 - i]!",
          "proof": "by intro l i h\n  rw [getElem!_pos l.reverse i (by simpa using h), getElem!_pos l (l.length - 1 - i) (by omega)]\n"
                   "  simp [List.getElem_reverse]"}]),
    "he_150_x_or_y": bind("p", "Bool", "p = true ↔ primeSpec n",
                          cases("n < 2", term("false"),
                                loop([["d", "Nat"], ["ok", "Bool"]], ["2", "true"],
                                     "2 ≤ d ∧ d ≤ n ∧ (ok = true ↔ ∀ k, k < d → k ≥ 2 → n % k ≠ 0)", "d < n", "n - d", "ok",
                                     term("(d + 1, ok && decide (n % d ≠ 0))"))),
                          cases("p = true", term("x"), term("y"))),
}


def run(only=None, imports=None, oracles=None, library=None):
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import DEFAULT_IMPORTS, FULL_IMPORTS, LeanSession
    from FormalLLM.lean.task import LeanTask
    rows = []
    with LeanSession(imports=FULL_IMPORTS if imports == "full" else DEFAULT_IMPORTS, startup_timeout=1200) as lean:
        for task_id, tree in (oracles or ORACLES).items():
            if only and task_id not in only:
                continue
            started = time.time()
            row = {"id": task_id, "laws": 0, "accepted": False, "certified": False, "tests": 0, "passed": 0,
                   "failed_obligations": [], "seconds": 0.0}
            rows.append(row)
            try:
                task = LeanTask.from_dir(os.path.join(library or LIBRARY, task_id))
                derivation = Derivation(task, lean)
                steps = derivation.apply_tree(tree)
            except Exception as error:                      # e.g. the task needs imports this session lacks
                row["failed_obligations"].append({"kind": "setup", "why": str(error)[:300]})
                print(f"{task_id:32s} SETUP {str(error)[:90]!r}", flush=True)
                continue
            row["laws"] = derivation.laws_used
            bad = [s for s in steps if not s.ok]
            if bad:
                for verdict in bad[0].verdicts:
                    if not verdict.proved:
                        row["failed_obligations"].append({"kind": verdict.obligation.kind, "status": verdict.status,
                                                          "statement": verdict.obligation.statement[:300],
                                                          "unsolved": [g[:600] for g in verdict.unsolved[:2]],
                                                          "message": verdict.message[:300],
                                                          "counterexample": verdict.counterexample})
                if not bad[0].verdicts:
                    row["failed_obligations"].append({"kind": "step", "why": bad[0].message})
            row["accepted"] = derivation.complete
            if derivation.complete:
                certificate = derivation.certify()
                row.update(certified=certificate.verified, tests=certificate.tests, passed=certificate.passed)
                if not certificate.sound:
                    row["failed_obligations"].append({"kind": "certificate", "why": " | ".join(certificate.errors)[:400]})
            row["seconds"] = round(time.time() - started, 1)
            state = "CERTIFIED" if row["certified"] else ("accepted, not certified" if row["accepted"] else "REJECTED")
            first = row["failed_obligations"][0] if row["failed_obligations"] else {}
            print(f"{task_id:32s} {state:24s} laws {row['laws']}  tests {row['passed']}/{row['tests']}  {row['seconds']:5.1f}s  "
                  f"{first.get('kind', '')} {first.get('statement', first.get('why', ''))[:70]!r}", flush=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--imports", default="default", choices=["default", "full"])
    args = ap.parse_args()
    rows = run(args.only, args.imports)
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "oracle.json"), "w", encoding="utf8") as handle:
        json.dump(rows, handle, indent=1, ensure_ascii=False)
    print(f"\n{sum(r['certified'] for r in rows)} of {len(rows)} oracle derivations certified "
          f"({sum(r['accepted'] for r in rows)} accepted by the engine)")


if __name__ == "__main__":
    main()
