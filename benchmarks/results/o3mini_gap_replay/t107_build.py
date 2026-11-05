"""Write a Lean file: he_107's task environment and its gap goal tried with each portfolio piece separately."""
import os, sys
root, out = sys.argv[1], sys.argv[2]
sys.path.insert(0, root)
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
task = datasets.resolve("he_107_even_odd_palindrome").load("he_107_even_odd_palindrome")
der = E.Derivation(task, None, counterexamples=False)
goal = """(n : ℕ) (h_precond : evenOddPalindrome_precond n) : (List.foldl
        (fun acc i =>
          if 1 ≤ i ∧ isPal (toString i).toList then if i % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)
          else acc)
        (0, 0) (List.range (n + 1))).1 =
    (List.filter (fun i => decide (1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0)) (List.range (n + 1))).length"""
tacs = ["lib_apply_grind", "(try unfold_local); (try lib_simp); lib_apply_grind", "lib_apply",
        "(apply Refine.foldl_pair_count_fst; all_goals first | assumption | (simp_all; done) | omega | grind)",
        "refine_portfolio"]
with open(out, "w", encoding="utf8") as f:
    f.write("import LeanEnv.Hammer\n" + der.lemmas + "\n" + task.prelude + "\n")
    for k, t in enumerate(tacs):
        f.write(f"\nset_option maxHeartbeats 600000 in\ntheorem t{k} {goal} := by\n  {t}\n")
