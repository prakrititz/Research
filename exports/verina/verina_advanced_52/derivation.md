# Derivation of verina_advanced_52

kind: **loop**

- **loop** over state (r : Nat), start (0)
  - invariant: `r ≤ nums.length ∧ ∀ r', r' < r → ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r')) = true)`
  - guard: `r < nums.length ∧ ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r)) = true)`
  - variant: `nums.length - r`
  - result: `r`
  - helper lemma `exit52`: `∀ (nums : List Nat) (k : Nat) (h : minOperations_precond nums k) (r : Nat), (r ≤ nums.length ∧ ∀ r', r' < r → ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r')) = true)) → ¬ (r < nums.length ∧ ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r)) = true)) → minOperations_postcond nums k r h`
  - helper lemma `step52`: `∀ (nums : List Nat) (k : Nat) (r : Nat), (r ≤ nums.length ∧ ∀ r', r' < r → ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r')) = true)) → (r < nums.length ∧ ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r)) = true)) → (r + 1 ≤ nums.length ∧ ∀ r', r' < r + 1 → ¬ (((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r')) = true))`
  - **term**: `r + 1`
