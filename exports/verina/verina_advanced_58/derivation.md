# Derivation of verina_advanced_58

kind: **loop**

- **loop** over state (x : Nat, c : Nat), start (0, 0)
  - invariant: `x ≤ 2 ^ (n - 1) ∧ c = ((List.range x).filter (fun i => isUgly i)).length ∧ c < n`
  - guard: `x < 2 ^ (n - 1) ∧ ¬ (isUgly x = true ∧ c + 1 = n)`
  - variant: `2 ^ (n - 1) - x`
  - result: `x`
  - helper lemma `step58`: `∀ (n x c : Nat), (x ≤ 2 ^ (n - 1) ∧ c = ((List.range x).filter (fun i => isUgly i)).length ∧ c < n) → (x < 2 ^ (n - 1) ∧ ¬ (isUgly x = true ∧ c + 1 = n)) → (x + 1 ≤ 2 ^ (n - 1) ∧ (if isUgly x = true then c + 1 else c) = ((List.range (x + 1)).filter (fun i => isUgly i)).length ∧ (if isUgly x = true then c + 1 else c) < n)`
  - helper lemma `init58`: `∀ (n : Nat), nthUglyNumber_precond n → (0 ≤ 2 ^ (n - 1) ∧ 0 = ((List.range 0).filter (fun i => isUgly i)).length ∧ 0 < n)`
  - helper lemma `exit58`: `∀ (n : Nat) (h : nthUglyNumber_precond n) (x c : Nat), (x ≤ 2 ^ (n - 1) ∧ c = ((List.range x).filter (fun i => isUgly i)).length ∧ c < n) → ¬ (x < 2 ^ (n - 1) ∧ ¬ (isUgly x = true ∧ c + 1 = n)) → nthUglyNumber_postcond n x h`
  - **term**: `(x + 1, if isUgly x = true then c + 1 else c)`
