r"""Hand-written derivations for tasks of the Verina benchmark (not ours: written by its authors, in their style).

The Lean library of ``lean_specs.py`` is stated by us, so a derivation engine that works on it could be fitted to how we write.
Verina's specifications were written by other people for a different purpose (verified program synthesis from Lean
specifications), with their idioms (``(hi : i < a.size) → a[i]`` with proofs in the index, ``result - x = 0`` for equality in
``Nat``, helper definitions in ``postcond_aux``). Running derivations on them says whether the engine reads someone else's specification.

    python benchmarks/datasets/verina_oracle.py [--only verina_basic_5 ...]    # -> benchmarks/results/lean_specs/verina_oracle.json
"""
import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
from benchmarks.datasets.lean_oracle import RESULTS, bind, cases, loop, run, term, with_lemmas

DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")

ORACLES = {
    "verina_basic_1": term("decide ((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0))"),
    "verina_basic_5": term("a * b"),
    "verina_basic_11": term("n % 10"),
    "verina_basic_12": term("6 * size * size"),
    "verina_basic_26": term("decide (n % 2 = 0)"),
    "verina_basic_50": cases("x ≥ 0", term("x"), term("-x")),
    "verina_basic_55": term("decide (a = b)"),
    "verina_basic_100": term("3 * x"),
    "verina_basic_107": term("(a + b) / 2"),
    "verina_basic_53": loop([["i", "Nat"], ["s", "Nat"]], ["0", "0"], "s * 2 = i * (i + 1) ∧ i ≤ N", "i < N", "N - i", "s",
                            term("(i + 1, s + (i + 1))")),
    "verina_basic_13": loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                            "i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → acc[k]! = a[k]! * a[k]! * a[k]!", "i < a.size",
                            "a.size - i", "acc", term("(i + 1, acc.push (a[i]! * a[i]! * a[i]!))")),
    "verina_basic_19": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                            "i ≤ a.size - 1 ∧ (ok = true ↔ ∀ k, k < i → a[k]! ≤ a[k + 1]!)", "i < a.size - 1",
                            "a.size - 1 - i", "ok", term("(i + 1, ok && decide (a[i]! ≤ a[i + 1]!))")),
    "verina_basic_10": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                            "i ≤ a.size ∧ (ok = true ↔ ∀ k, k < i → n > a[k]!)", "i < a.size", "a.size - i", "ok",
                            term("(i + 1, ok && decide (n > a[i]!))")),
    # --- a second batch: arrays built or scanned with the task's own helper definitions ---
    "verina_basic_105": loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                             "i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → a[k]! * b[k]! = acc[k]!", "i < a.size", "a.size - i",
                             "acc", term("(i + 1, acc.push (a[i]! * b[i]!))")),
    "verina_basic_106": loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                             "i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → a[k]! + b[k]! = acc[k]!", "i < a.size", "a.size - i",
                             "acc", term("(i + 1, acc.push (a[i]! + b[i]!))")),
    "verina_basic_30": loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                            "i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → acc[k]! = a[k]! % b[k]!", "i < a.size", "a.size - i",
                            "acc", term("(i + 1, acc.push (a[i]! % b[i]!))")),
    # the task defines sumTo by a recursion that simp cannot unfold safely, so the step brings two facts about it
    "verina_basic_47": with_lemmas(
        loop([["i", "Nat"], ["acc", "Int"]], ["0", "0"], "i ≤ a.size ∧ acc = sumTo a i", "i < a.size",
             "a.size - i", "acc", term("(i + 1, acc + a[i]!)")),
        [{"name": "sumTo_zero", "statement": "∀ (a : Array Int), sumTo a 0 = 0", "proof": "by intro a; rw [sumTo]; simp"},
         {"name": "sumTo_succ", "statement": "∀ (a : Array Int) (i : Nat), sumTo a (i + 1) = sumTo a i + a[i]!",
          "proof": "by intro a i; rw [sumTo]; simp"}]),
    "verina_basic_44": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                            "i ≤ a.size ∧ (ok = true ↔ ∀ k, k < i → isOdd k → isOdd a[k]!)", "i < a.size", "a.size - i", "ok",
                            term("(i + 1, ok && (!isOdd i || isOdd a[i]!))")),
    # --- advanced tasks (richer specifications, still one idea each) ---
    "verina_advanced_41": bind("m", "Int", "m ≥ a ∧ m ≥ b ∧ (m = a ∨ m = b)",
                               cases("a ≥ b", term("a"), term("b")), cases("m ≥ c", term("m"), term("c"))),
    "verina_advanced_39": loop([["i", "Nat"], ["m", "Nat"]], ["1", "lst[0]!"],
                               "1 ≤ i ∧ i ≤ lst.length ∧ (∃ k, k < i ∧ lst[k]! = m) ∧ ∀ k, k < i → lst[k]! ≤ m",
                               "i < lst.length", "lst.length - i", "m", term("(i + 1, max m lst[i]!)")),
    "verina_advanced_40": loop([["i", "Nat"], ["m", "Nat"]], ["1", "lst[0]!"],
                               "1 ≤ i ∧ i ≤ lst.length ∧ (∃ k, k < i ∧ lst[k]! = m) ∧ ∀ k, k < i → lst[k]! ≤ m",
                               "i < lst.length", "lst.length - i", "m", term("(i + 1, max m lst[i]!)")),
    "verina_advanced_16": with_lemmas(
        term("xs.mergeSort (fun a b => a ≤ b)"),
        [{"name": "sorted_perm", "statement": "∀ (xs : List Int), List.Pairwise (· ≤ ·) (xs.mergeSort (fun a b => decide (a ≤ b))) ∧ "
                                              "List.isPerm xs (xs.mergeSort (fun a b => decide (a ≤ b))) = true",
          "proof": "by intro xs\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) xs, List.isPerm_iff.mpr (List.mergeSort_perm xs _).symm⟩"}]),
    "verina_advanced_17": with_lemmas(
        term("l.mergeSort (fun a b => a ≤ b)"),
        [{"name": "sorted_perm", "statement": "∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort (fun a b => decide (a ≤ b))) ∧ "
                                              "List.isPerm l (l.mergeSort (fun a b => decide (a ≤ b))) = true",
          "proof": "by intro l\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) l, List.isPerm_iff.mpr (List.mergeSort_perm l _).symm⟩"}]),
    "verina_basic_4": term("arr[k - 1]!"),
    "verina_basic_2": cases("s.size = 0", term("none"),
                           loop([["i", "Nat"], ["m", "Nat"]], ["1", "s[0]!"],
                                "1 ≤ i ∧ i ≤ s.size ∧ (∃ j, j < i ∧ s[j]! = m) ∧ ∀ j, j < i → m ≤ s[j]!", "i < s.size",
                                "s.size - i", "some m", term("(i + 1, min m s[i]!)"))),
}


# --- further batches (their own modules; they import only derivation_dsl) ---
for _module in ("verina_oracle_b", "verina_oracle_c", "verina_oracle_d", "verina_oracle_e", "verina_oracle_f", "verina_oracle_g", "verina_oracle_h", "verina_oracle_i", "verina_oracle_j", "verina_oracle_k", "verina_oracle_l", "verina_oracle_m"):
    try:
        import importlib
        ORACLES.update(importlib.import_module(f"benchmarks.datasets.{_module}").ORACLES_MORE)
    except ModuleNotFoundError as _error:
        if _error.name != f"benchmarks.datasets.{_module}":
            raise


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--imports", default="default", choices=["default", "full"])
    args = ap.parse_args()
    rows = run(args.only, args.imports, oracles=ORACLES, library=DATASET)
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "verina_oracle.json"), "w", encoding="utf8") as handle:
        json.dump(rows, handle, indent=1, ensure_ascii=False)
    print(f"\n{sum(r['certified'] for r in rows)} of {len(rows)} derivations of Verina tasks certified")


if __name__ == "__main__":
    main()
