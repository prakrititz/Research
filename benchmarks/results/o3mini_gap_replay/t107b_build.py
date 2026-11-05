"""he_107's postcondition obligation for o3-mini's fold, by the engine's hammer prep + refine_portfolio (and _debug)."""
import os, sys
root, out = sys.argv[1], sys.argv[2]
sys.path.insert(0, root)
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
task = datasets.resolve("he_107_even_odd_palindrome").load("he_107_even_odd_palindrome")
der = E.Derivation(task, None, counterexamples=False)
expr = "((List.range (n + 1)).foldl (fun acc i => if 1 ≤ i ∧ isPal (toString i).toList then if i % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1) else acc) (0, 0))"
prep = (f"(try unfold {task.post_name} {task.pre_name} at *); (try dsimp only at *); (try intros); "
        "(try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> ")
with open(out, "w", encoding="utf8") as f:
    f.write("import LeanEnv.Hammer\n" + der.lemmas + "\n" + task.prelude + "\n")
    for k, t in enumerate(["refine_portfolio_debug"]):
        f.write(f"\nset_option maxHeartbeats 0 in\ntheorem t{k} (n : Nat) (h_precond : evenOddPalindrome_precond n) : "
                f"evenOddPalindrome_postcond n {expr} h_precond := by\n  {prep}{t}\n")
