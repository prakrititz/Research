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


from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas  # noqa: E402,F401


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


# --- HumanEval 133-163 (the specifications added on 2026-10-11) -------------------------------------------------------------
# Three kinds: a real loop with an invariant; a ``term``/``cases`` that restates a decidable specification (the derivation is
# one step, the obligation is that the two readings agree); and a *definitional* one, where the specification is itself a
# recursive definition (``fixSpec``, ``evalOps``, ``romanSpec``, ``md5Hex``) and the answer is that definition. The last kind
# shows the task is reachable, not that a search found anything.
ORACLES.update({
    "he_133_sum_squares": loop([["i", "Nat"], ["acc", "Int"]], ["0", "0"],
                               "i ≤ lst.length ∧ acc = ((lst.take i).map (fun x => (⌈x⌉ : Int) * (⌈x⌉ : Int))).sum",
                               "i < lst.length", "lst.length - i", "acc",
                               term("(i + 1, acc + (⌈lst[i]!⌉ : Int) * (⌈lst[i]!⌉ : Int))")),
    "he_134_check_if_last_char_is_a_letter": term(
        "decide (txt.length ≥ 1 ∧ txt.toList[txt.length - 1]!.isAlpha = true ∧ (txt.length = 1 ∨ txt.toList[txt.length - 2]! = ' '))"),
    "he_135_can_arrange": with_lemmas(
        loop([["i", "Nat"]], ["arr.length - 1"],
             "i ≤ arr.length - 1 ∧ ∀ m, m < arr.length → i < m → arr[m - 1]! ≤ arr[m]!",
             "1 ≤ i ∧ arr[i - 1]! ≤ arr[i]!", "i", "if i = 0 then (-1 : Int) else (i : Int)", term("i - 1")),
        # the exit: a disjunction with a witness, which the cascade does not construct on its own
        [{"name": "canArrange_exit",
          "statement": "∀ (arr : List Int) (i : Nat), i ≤ arr.length - 1 → (∀ m, m < arr.length → i < m → arr[m - 1]! ≤ arr[m]!) → "
                       "¬ (1 ≤ i ∧ arr[i - 1]! ≤ arr[i]!) → "
                       "(((if i = 0 then (-1 : Int) else (i : Int)) = -1 ∧ ∀ j, j < arr.length → 1 ≤ j → arr[j - 1]! ≤ arr[j]!) ∨ "
                       "(∃ j, j < arr.length ∧ 1 ≤ j ∧ (if i = 0 then (-1 : Int) else (i : Int)) = (j : Int) ∧ arr[j]! < arr[j - 1]! ∧ "
                       "∀ m, m < arr.length → j < m → arr[m - 1]! ≤ arr[m]!))",
          "proof": "by intro arr i hi hall hg\n  by_cases h0 : i = 0\n  · subst h0\n    left\n    refine ⟨by simp, ?_⟩\n"
                   "    intro j hj hj1\n    exact hall j hj (by omega)\n  · right\n"
                   "    have hn : ¬ (arr[i - 1]! ≤ arr[i]!) := fun h => hg ⟨by omega, h⟩\n"
                   "    refine ⟨i, by omega, by omega, by simp [h0], by omega, hall⟩"}]),
    "he_137_compare_one": cases("valQ a = valQ b", term("none"), cases("valQ b < valQ a", term("some a"), term("some b"))),
    "he_141_file_name_check": cases(
        "(file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧ ∃ i, i < file_name.length ∧ "
        "file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧ "
        "(file_name.toList.drop (i + 1) = \"txt\".toList ∨ file_name.toList.drop (i + 1) = \"exe\".toList ∨ "
        "file_name.toList.drop (i + 1) = \"dll\".toList)",
        term("\"Yes\""), term("\"No\"")),
    "he_142_sum_squares": loop([["i", "Nat"], ["acc", "Int"]], ["0", "0"],
                               "i ≤ lst.length ∧ acc = ((List.range i).map (fun k => if k % 3 = 0 then lst[k]! ^ 2 else "
                               "if k % 4 = 0 then lst[k]! ^ 3 else lst[k]!)).sum",
                               "i < lst.length", "lst.length - i", "acc",
                               term("(i + 1, acc + (if i % 3 = 0 then lst[i]! ^ 2 else if i % 4 = 0 then lst[i]! ^ 3 else lst[i]!))")),
    "he_144_simplify": term("decide ((numOf x * numOf n) % (denOf x * denOf n) = 0)"),
    "he_146_special_filter": loop([["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
                                  "i ≤ nums.length ∧ acc = ((nums.take i).filter (fun x => x > 10 ∧ firstDigit x.natAbs % 2 = 1 ∧ "
                                  "x.natAbs % 10 % 2 = 1)).length",
                                  "i < nums.length", "nums.length - i", "acc",
                                  term("(i + 1, if nums[i]! > 10 ∧ firstDigit nums[i]!.natAbs % 2 = 1 ∧ nums[i]!.natAbs % 10 % 2 = 1 "
                                       "then acc + 1 else acc)")),
    "he_151_double_the_difference": loop(
        [["i", "Nat"], ["acc", "Int"]], ["0", "0"],
        "i ≤ lst.length ∧ acc = ((lst.take i).map (Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) "
        "(fun (_ : ℚ) => 0))).sum",
        "i < lst.length", "lst.length - i", "acc",
        term("(i + 1, acc + Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0) lst[i]!)")),
    "he_153_strongest_extension": loop(
        [["k", "Nat"], ["b", "Nat"]], ["1", "0"],
        "1 ≤ k ∧ k ≤ extensions.length ∧ b < k ∧ (∀ j, j < k → strength extensions[j]! ≤ strength extensions[b]!) ∧ "
        "∀ j, j < b → strength extensions[j]! < strength extensions[b]!",
        "k < extensions.length", "extensions.length - k", "class_name ++ \".\" ++ extensions[b]!",
        term("(k + 1, if strength extensions[b]! < strength extensions[k]! then k else b)")),
    "he_154_cycpattern_check": loop(
        [["i", "Nat"], ["found", "Bool"]], ["0", "false"],
        "i ≤ b.length ∧ (found = true ↔ ∃ k, k < i ∧ (b.toList.drop k ++ b.toList.take k) <:+: a.toList)",
        "i < b.length", "b.length - i", "decide (b.length = 0) || found",
        term("(i + 1, found || decide ((b.toList.drop i ++ b.toList.take i) <:+: a.toList))")),
    "he_155_even_odd_count": bind(
        "ds", "List Char", "ds = (toString num.natAbs).toList", term("(toString num.natAbs).toList"),
        loop([["i", "Nat"], ["e", "Nat"], ["o", "Nat"]], ["0", "0", "0"],
             "i ≤ ds.length ∧ e = ((ds.take i).filter (fun c => (c.toNat - 48) % 2 = 0)).length ∧ "
             "o = ((ds.take i).filter (fun c => (c.toNat - 48) % 2 = 1)).length",
             "i < ds.length", "ds.length - i", "(e, o)",
             term("(i + 1, if (ds[i]!.toNat - 48) % 2 = 0 then e + 1 else e, "
                  "if (ds[i]!.toNat - 48) % 2 = 1 then o + 1 else o)"))),
    "he_158_find_max": cases(
        "words = []", term("\"\""),
        bind("m", "String", "m ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars m) ∧ "
                            "∀ w ∈ words, uniqChars w = uniqChars m → ¬ (w < m)",
             loop([["k", "Nat"], ["b", "Nat"]], ["1", "0"],
                  "1 ≤ k ∧ k ≤ words.length ∧ b < k ∧ (∀ j, j < k → uniqChars words[j]! ≤ uniqChars words[b]!) ∧ "
                  "∀ j, j < k → uniqChars words[j]! = uniqChars words[b]! → ¬ (words[j]! < words[b]!)",
                  "k < words.length", "words.length - k", "words[b]!",
                  term("(k + 1, if uniqChars words[k]! > uniqChars words[b]! ∨ (uniqChars words[k]! = uniqChars words[b]! ∧ "
                       "words[k]! < words[b]!) then k else b)")),
             term("m"))),
    "he_159_eat": cases("need ≤ remaining", term("[number + need, remaining - need]"), term("[number + remaining, 0]")),
    "he_161_solve": cases("s.toList.any Char.isAlpha = true", term("String.mk (s.toList.map swapCase)"),
                          term("String.mk s.toList.reverse")),
    "he_162_string_to_md5": cases("text = \"\"", term("none"), term("some (md5Hex text)")),
    # definitional: the specification is the recursive definition itself
    "he_140_fix_spaces": term("String.mk (fixSpec text.length text.toList)"),
    "he_160_do_algebra": term("evalOps operator.length operand operator"),
    "he_156_int_to_mini_roman": term("romanSpec number number"),
})


# --- the remaining new HumanEval specifications: sorting with a stability / order lemma, witnesses, the Option-valued pair ----
# Helper lemmas are stated for any input and proved by Lean before the step is accepted (a false one is refused).
_ORDER_BY_POINTS = {
    "name": "order_ok",
    "statement": "∀ (nums : List Int), (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length = nums.length ∧ (∀ i, i < (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length - 1 → digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i]! ≤ digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i + 1]!) ∧ ∀ x ∈ nums, (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)",
    "proof": "by\n  intro nums\n  have htrans : ∀ (a b c : Int), decide (digitWeight a ≤ digitWeight b) = true → decide (digitWeight b ≤ digitWeight c) = true →\n      decide (digitWeight a ≤ digitWeight c) = true := by\n    intro a b c h1 h2; simp at *; omega\n  have htotal : ∀ (a b : Int), (decide (digitWeight a ≤ digitWeight b) || decide (digitWeight b ≤ digitWeight a)) = true := by\n    intro a b; simp; omega\n  have hp : (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).Perm nums := List.mergeSort_perm nums _\n  have hs : List.Pairwise (fun a b => decide (digitWeight a ≤ digitWeight b) = true)\n      (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))) := List.pairwise_mergeSort htrans htotal nums\n  refine ⟨List.length_mergeSort .., ?_, ?_⟩\n  · intro i hi\n    rw [List.pairwise_iff_getElem] at hs\n    have hi' : i + 1 < (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length := by omega\n    have := hs i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    simpa using this\n  · intro x hx\n    set p : Int → Bool := fun y => digitWeight y == digitWeight x with hpdef\n    set s := nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)) with hsdef\n    have hc : (nums.filter p).Pairwise (fun a b => decide (digitWeight a ≤ digitWeight b) = true) := by\n      apply List.pairwise_of_forall_mem_list\n      intro a ha b hb\n      simp [hpdef] at ha hb\n      simp; omega\n    have hsub : (nums.filter p).Sublist s := List.sublist_mergeSort htrans htotal hc (List.filter_sublist)\n    have hself : (nums.filter p).filter p = nums.filter p := by\n      rw [List.filter_filter]; simp\n    have hsub2 : (nums.filter p).Sublist (s.filter p) := by\n      have := hsub.filter p\n      rwa [hself] at this\n    have hlen : (nums.filter p).length = (s.filter p).length := (List.Perm.filter p hp).length_eq.symm\n    exact (hsub2.eq_of_length hlen).symm"
}
_SORTED_LIST_SUM = {
    "name": "sorted_ok",
    "statement": "∀ (L : List String), (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).Perm L ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).length - 1 → ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!.length < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]!.length ∨ ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!.length = (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]!.length ∧ ¬ ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]! < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!)))",
    "proof": "by\n  intro L\n  have htrans : ∀ (a b c : String), (decide (a.length < b.length) || (a.length == b.length && !decide (b < a))) = true →\n      (decide (b.length < c.length) || (b.length == c.length && !decide (c < b))) = true →\n      (decide (a.length < c.length) || (a.length == c.length && !decide (c < a))) = true := by\n    intro a b c h1 h2\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at *\n    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩\n    · left; omega\n    · left; omega\n    · left; omega\n    · right\n      refine ⟨by omega, ?_⟩\n      intro hca\n      exact h2' (Std.lt_of_lt_of_le hca h1')\n  have htotal : ∀ (a b : String), ((decide (a.length < b.length) || (a.length == b.length && !decide (b < a))) ||\n      (decide (b.length < a.length) || (b.length == a.length && !decide (a < b)))) = true := by\n    intro a b\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]\n    by_cases h : a.length < b.length\n    · left; left; exact h\n    · by_cases h' : b.length < a.length\n      · right; left; exact h'\n      · have he : a.length = b.length := by omega\n        by_cases hl : b < a\n        · right; right; exact ⟨he.symm, String.lt_asymm hl⟩\n        · left; right; exact ⟨he, hl⟩\n  have hp : (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).Perm L :=\n    List.mergeSort_perm L _\n  have hs := List.pairwise_mergeSort htrans htotal L\n  refine ⟨hp, ?_⟩\n  intro i hi\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] using this"
}
_GENERATE_OK = {
    "name": "generate_ok",
    "statement": "∀ (a b : Nat), (∀ i, i < ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))).length - 1 → ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))[i]! < ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))[i + 1]!) ∧ (∀ d ∈ ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))), d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b ∧ d < 10) ∧ ∀ d, d < 10 → d % 2 = 0 → min a b ≤ d → d ≤ max a b → d ∈ ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))",
    "proof": "by intro a b\n  have hs : List.Pairwise (· < ·) ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))) :=\n    (List.pairwise_lt_range).filter _\n  refine ⟨?_, ?_, ?_⟩\n  · intro i hi\n    rw [List.pairwise_iff_getElem] at hs\n    have hi' : i + 1 < ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))).length := by omega\n    have := hs i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    exact this\n  · intro d hd\n    simp at hd\n    omega\n  · intro d hd h2 h3 h4\n    simp\n    omega"
}
_PLANET_WITNESS = {
    "name": "planet_witness",
    "statement": "∀ (p1 p2 : String), p1 ∈ solarPlanets → p2 ∈ solarPlanets → ∃ i, i < 8 ∧ solarPlanets[i]! = p1 ∧ ∃ j, j < 8 ∧ solarPlanets[j]! = p2 ∧ (solarPlanets.drop (min (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) + 1)).take (max (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) - min (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) - 1) = (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1)",
    "proof": "by intro p1 p2 h1 h2\n  have e1 : solarPlanets.idxOf p1 < solarPlanets.length := List.idxOf_lt_length_of_mem h1\n  have e2 : solarPlanets.idxOf p2 < solarPlanets.length := List.idxOf_lt_length_of_mem h2\n  have hl : solarPlanets.length = 8 := rfl\n  refine ⟨solarPlanets.idxOf p1, by omega, ?_, solarPlanets.idxOf p2, by omega, ?_, rfl⟩\n  · rw [getElem!_pos solarPlanets _ e1]; exact List.getElem_idxOf e1\n  · rw [getElem!_pos solarPlanets _ e2]; exact List.getElem_idxOf e2"
}


_NEG_EXIT = {
    "name": "neg_exit",
    "statement": "∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! < 0) → "
                 "(f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < lst.length → lst[k]! < 0 → lst[k]! ≤ m) → "
                 "(((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ "
                 "(∃ y ∈ lst, (if f = true then some m else none) = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y))",
    "proof": "by intro lst m f h1 h2\n  by_cases hf : f = true\n  · right\n    obtain ⟨⟨k, hk, hkm⟩, hm, hall⟩ := h2 hf\n"
             "    refine ⟨m, ?_, by simp [hf], hm, ?_⟩\n    · rw [← hkm]; exact Refine.getElem_bang_mem lst k hk\n"
             "    · intro x hx hx0\n      obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n      exact hall j hj hx0\n"
             "  · left\n    refine ⟨by simp [hf], ?_⟩\n    intro x hx\n    obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n"
             "    by_contra hneg\n    exact hf (h1.mpr ⟨j, hj, by omega⟩)"}
_POS_EXIT = {
    "name": "pos_exit",
    "statement": "∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! > 0) → "
                 "(f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < lst.length → lst[k]! > 0 → m ≤ lst[k]!) → "
                 "(((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ "
                 "(∃ y ∈ lst, (if f = true then some m else none) = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x))",
    "proof": "by intro lst m f h1 h2\n  by_cases hf : f = true\n  · right\n    obtain ⟨⟨k, hk, hkm⟩, hm, hall⟩ := h2 hf\n"
             "    refine ⟨m, ?_, by simp [hf], hm, ?_⟩\n    · rw [← hkm]; exact Refine.getElem_bang_mem lst k hk\n"
             "    · intro x hx hx0\n      obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n      exact hall j hj hx0\n"
             "  · left\n    refine ⟨by simp [hf], ?_⟩\n    intro x hx\n    obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n"
             "    by_contra hpos\n    exact hf (h1.mpr ⟨j, hj, by omega⟩)"}


def _extreme_scan(order, bound):
    """Scan ``lst`` keeping the best element so far (``order`` is ``m < lst[i]!`` or ``lst[i]! < m``) among those with the sign
    ``bound`` (``< 0`` or ``> 0``); the result is ``some m`` once one was seen."""
    sign = "lst[k]! < 0" if bound == "neg" else "lst[k]! > 0"
    better = "lst[i]! < 0" if bound == "neg" else "lst[i]! > 0"
    best = "lst[k]! ≤ m" if bound == "neg" else "m ≤ lst[k]!"
    return loop([["i", "Nat"], ["m", "Int"], ["f", "Bool"]], ["0", "0", "false"],
                f"i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ {sign}) ∧ "
                f"(f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ {'m < 0' if bound == 'neg' else '0 < m'} ∧ ∀ k, k < i → {sign} → {best})",
                "i < lst.length", "lst.length - i", "if f = true then some m else none",
                term(f"(i + 1, if {better} ∧ (f = false ∨ {order}) then lst[i]! else m, f || decide ({better}))"))


ORACLES.update({
    "he_136_largest_smallest_integers": bind(
        "a", "Option Int", "(a = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, a = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y)",
        with_lemmas(_extreme_scan("m < lst[i]!", "neg"), [_NEG_EXIT]),
        bind("b", "Option Int", "(b = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, b = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x)",
             with_lemmas(_extreme_scan("lst[i]! < m", "pos"), [_POS_EXIT]), term("(a, b)"))),
    "he_143_words_in_sentence": term('" ".intercalate ((sentence.splitOn " ").filter (fun w => decide (Nat.Prime w.length)))'),
    "he_145_order_by_points": with_lemmas(term("nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))"),
                                          [_ORDER_BY_POINTS]),
    "he_147_get_max_triples": term(
        "((List.range n).map (fun i => ((List.range n).map (fun j => ((List.range n).filter (fun k => i < j ∧ j < k ∧ "
        "(seqA (i + 1) + seqA (j + 1) + seqA (k + 1)) % 3 = 0)).length)).sum)).sum"),
    "he_148_bf": with_lemmas(
        cases("planet1 ∈ solarPlanets ∧ planet2 ∈ solarPlanets",
              term("(solarPlanets.drop (min (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) + 1)).take "
                   "(max (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) - "
                   "min (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) - 1)"),
              term("[]")),
        [_PLANET_WITNESS]),
    "he_149_sorted_list_sum": with_lemmas(
        term("(lst.filter (fun s => decide (s.length % 2 = 0))).mergeSort "
             "(fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))"),
        [_SORTED_LIST_SUM]),
    "he_163_generate_integers": with_lemmas(
        term("(List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))"), [_GENERATE_OK]),
})


# --- further batches live in their own modules (they import only derivation_dsl) ---
for _module in ("lean_oracle_he_a", "lean_oracle_he_b"):
    try:
        import importlib
        ORACLES.update(importlib.import_module(f"benchmarks.datasets.{_module}").ORACLES_MORE)
    except ModuleNotFoundError as _error:
        if _error.name != f"benchmarks.datasets.{_module}":
            raise


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
