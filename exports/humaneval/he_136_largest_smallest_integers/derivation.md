# Derivation of he_136_largest_smallest_integers

kind: **loop**

- **bind** `a : Option Int` with property `(a = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, a = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y)`
  - _value_:
    - **loop** over state (i : Nat, m : Int, f : Bool), start (0, 0, false)
      - invariant: `i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! < 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < i → lst[k]! < 0 → lst[k]! ≤ m)`
      - guard: `i < lst.length`
      - variant: `lst.length - i`
      - result: `if f = true then some m else none`
      - helper lemma `neg_exit`: `∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! < 0) → (f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < lst.length → lst[k]! < 0 → lst[k]! ≤ m) → (((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, (if f = true then some m else none) = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y))`
      - **term**: `(i + 1, if lst[i]! < 0 ∧ (f = false ∨ m < lst[i]!) then lst[i]! else m, f || decide (lst[i]! < 0))`
  - _continuation_:
    - **bind** `b : Option Int` with property `(b = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, b = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x)`
      - _value_:
        - **loop** over state (i : Nat, m : Int, f : Bool), start (0, 0, false)
          - invariant: `i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! > 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < i → lst[k]! > 0 → m ≤ lst[k]!)`
          - guard: `i < lst.length`
          - variant: `lst.length - i`
          - result: `if f = true then some m else none`
          - helper lemma `pos_exit`: `∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! > 0) → (f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < lst.length → lst[k]! > 0 → m ≤ lst[k]!) → (((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, (if f = true then some m else none) = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x))`
          - **term**: `(i + 1, if lst[i]! > 0 ∧ (f = false ∨ lst[i]! < m) then lst[i]! else m, f || decide (lst[i]! > 0))`
      - _continuation_:
        - **term**: `(a, b)`
