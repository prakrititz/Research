# Derivation of verina_advanced_53

kind: **loop**

- **cases** on `nums.length ≤ 1`
  - _then_:
    - **term**: `0`
      - helper lemma `nil53`: `∀ (nums : List Int) (h : minimumRightShifts_precond nums), nums.length ≤ 1 → minimumRightShifts_postcond nums 0 h`
  - _else_:
    - **loop** over state (j : Nat), start (0)
      - invariant: `j ≤ nums.length ∧ ∀ k, k < j → ¬ List.Pairwise (· ≤ ·) (nums.rotateRight k)`
      - guard: `j < nums.length ∧ ¬ List.Pairwise (· ≤ ·) (nums.rotateRight j)`
      - variant: `nums.length - j`
      - result: `if j < nums.length then (j : Int) else -1`
      - helper lemma `exit53`: `∀ (nums : List Int) (h : minimumRightShifts_precond nums) (j : Nat), ¬ nums.length ≤ 1 → (j ≤ nums.length ∧ ∀ k, k < j → ¬ List.Pairwise (· ≤ ·) (nums.rotateRight k)) → ¬ (j < nums.length ∧ ¬ List.Pairwise (· ≤ ·) (nums.rotateRight j)) → minimumRightShifts_postcond nums (if j < nums.length then (j : Int) else -1) h`
      - **term**: `j + 1`
