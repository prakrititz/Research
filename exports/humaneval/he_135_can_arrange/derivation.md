# Derivation of he_135_can_arrange

kind: **loop**

- **loop** over state (i : Nat), start (arr.length - 1)
  - invariant: `i ≤ arr.length - 1 ∧ ∀ m, m < arr.length → i < m → arr[m - 1]! ≤ arr[m]!`
  - guard: `1 ≤ i ∧ arr[i - 1]! ≤ arr[i]!`
  - variant: `i`
  - result: `if i = 0 then (-1 : Int) else (i : Int)`
  - helper lemma `canArrange_exit`: `∀ (arr : List Int) (i : Nat), i ≤ arr.length - 1 → (∀ m, m < arr.length → i < m → arr[m - 1]! ≤ arr[m]!) → ¬ (1 ≤ i ∧ arr[i - 1]! ≤ arr[i]!) → (((if i = 0 then (-1 : Int) else (i : Int)) = -1 ∧ ∀ j, j < arr.length → 1 ≤ j → arr[j - 1]! ≤ arr[j]!) ∨ (∃ j, j < arr.length ∧ 1 ≤ j ∧ (if i = 0 then (-1 : Int) else (i : Int)) = (j : Int) ∧ arr[j]! < arr[j - 1]! ∧ ∀ m, m < arr.length → j < m → arr[m - 1]! ≤ arr[m]!))`
  - **term**: `i - 1`
