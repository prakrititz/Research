# Derivation of he_090_next_smallest

kind: **loop**

- **cases** on `lst = []`
  - _then_:
    - **term**: `none`
  - _else_:
    - **bind** `m : Int` with property `(∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!`
      - helper lemma `ns_some`: `∀ (lst : List Int) (m : Int) (p : Bool × Int), ((∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!) → ((p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ (p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)) → p.1 = true → (p.2 ∈ lst ∧ (∃ m2 ∈ lst, m2 < p.2) ∧ ∀ x ∈ lst, (∃ m2 ∈ lst, m2 < x) → p.2 ≤ x)`
      - helper lemma `ns_none`: `∀ (lst : List Int) (m : Int) (p : Bool × Int), ((∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!) → ((p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ (p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)) → ¬ p.1 = true → ∀ x ∈ lst, ∀ y ∈ lst, x = y`
      - _value_:
        - **loop** over state (i : Nat, m : Int), start (1, lst[0]!)
          - invariant: `1 ≤ i ∧ i ≤ lst.length ∧ (∃ k, k < i ∧ lst[k]! = m) ∧ ∀ k, k < i → m ≤ lst[k]!`
          - guard: `i < lst.length`
          - variant: `lst.length - i`
          - result: `m`
          - **term**: `(i + 1, min m lst[i]!)`
      - _continuation_:
        - **bind** `p : Bool × Int` with property `(p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ (p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)`
          - _value_:
            - **loop** over state (i : Nat, f : Bool, r : Int), start (0, false, 0)
              - invariant: `i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ m < lst[k]!) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = r ∧ m < r) ∧ ∀ k, k < i → m < lst[k]! → r ≤ lst[k]!)`
              - guard: `i < lst.length`
              - variant: `lst.length - i`
              - result: `(f, r)`
              - **term**: `(i + 1, f || decide (m < lst[i]!), if m < lst[i]! ∧ (f = false ∨ lst[i]! < r) then lst[i]! else r)`
          - _continuation_:
            - **cases** on `p.1 = true`
              - _then_:
                - **term**: `some p.2`
              - _else_:
                - **term**: `none`
