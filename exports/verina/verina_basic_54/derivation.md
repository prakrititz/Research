# Derivation of verina_basic_54

kind: **loop**

- **loop** over state (i : Nat, best : Nat), start (0, (a[0]! - b[0]!).natAbs)
  - invariant: `i ≤ a.size ∧ (∃ ii, ii < a.size ∧ ∃ jj, jj < b.size ∧ best = (a[ii]! - b[jj]!).natAbs) ∧ ∀ k, k < i → ∀ j, j < b.size → best ≤ (a[k]! - b[j]!).natAbs`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `best`
  - helper lemma `exit54`: `∀ (a b : Array Int) (i best : Nat) (h : CanyonSearch_precond a b), (i ≤ a.size ∧ (∃ ii, ii < a.size ∧ ∃ jj, jj < b.size ∧ best = (a[ii]! - b[jj]!).natAbs) ∧ ∀ k, k < i → ∀ j, j < b.size → best ≤ (a[k]! - b[j]!).natAbs) → ¬ i < a.size → CanyonSearch_postcond a b best h`
  - **bind** `row : Nat` with property `(∃ jj, jj < b.size ∧ row = (a[i]! - b[jj]!).natAbs) ∧ ∀ jj, jj < b.size → row ≤ (a[i]! - b[jj]!).natAbs`
    - _value_:
      - **loop** over state (j : Nat, row : Nat), start (1, (a[i]! - b[0]!).natAbs)
        - invariant: `1 ≤ j ∧ j ≤ b.size ∧ (∃ jj, jj < j ∧ row = (a[i]! - b[jj]!).natAbs) ∧ ∀ jj, jj < j → row ≤ (a[i]! - b[jj]!).natAbs`
        - guard: `j < b.size`
        - variant: `b.size - j`
        - result: `row`
        - **term**: `(j + 1, min row (a[i]! - b[j]!).natAbs)`
    - _continuation_:
      - **term**: `(i + 1, min best row)`
