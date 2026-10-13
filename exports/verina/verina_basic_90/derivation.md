# Derivation of verina_basic_90

kind: **loop**

- **loop** over state (i : Nat, mm : Int, nn : Int), start (0, -1, -1)
  - invariant: `i ≤ a.size ∧ ((0 ≤ mm ∧ mm < a.size ∧ 0 ≤ nn ∧ nn < (a[0]!).size ∧ get2d a mm nn = key) ∨ (mm = -1 ∧ nn = -1 ∧ ∀ k, k < i → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key))`
  - guard: `i < a.size ∧ mm = -1`
  - variant: `a.size - i`
  - result: `(mm, nn)`
  - helper lemma `exit90`: `∀ (a : Array (Array Int)) (key : Int) (h : SlopeSearch_precond a key) (i : Nat) (mm nn : Int), (i ≤ a.size ∧ ((0 ≤ mm ∧ mm < a.size ∧ 0 ≤ nn ∧ nn < (a[0]!).size ∧ get2d a mm nn = key) ∨ (mm = -1 ∧ nn = -1 ∧ ∀ k, k < i → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key))) → ¬ (i < a.size ∧ mm = -1) → SlopeSearch_postcond a key (mm, nn) h`
  - **bind** `jr : Int` with property `((jr = -1 ∧ ∀ j, j < (a[i]!).size → (a[i]!)[j]! ≠ key) ∨ (0 ≤ jr ∧ jr < (a[0]!).size ∧ (a[i]!)[jr.toNat]! = key))`
    - _value_:
      - **loop** over state (j : Nat), start (0)
        - invariant: `j ≤ (a[i]!).size ∧ ∀ j', j' < j → (a[i]!)[j']! ≠ key`
        - guard: `j < (a[i]!).size ∧ (a[i]!)[j]! ≠ key`
        - variant: `(a[i]!).size - j`
        - result: `if j < (a[i]!).size then (j : Int) else -1`
        - helper lemma `width90`: `∀ (a : Array (Array Int)) (key : Int), SlopeSearch_precond a key → ∀ i, i < a.size → (a[i]!).size = (a[0]!).size`
        - helper lemma `inner90`: `∀ (a : Array (Array Int)) (key : Int), SlopeSearch_precond a key → ∀ (i : Nat), i < a.size → ∀ (j : Nat), (j ≤ (a[i]!).size ∧ ∀ j', j' < j → (a[i]!)[j']! ≠ key) → ¬ (j < (a[i]!).size ∧ (a[i]!)[j]! ≠ key) → ((((if j < (a[i]!).size then (j : Int) else -1)) = -1 ∧ ∀ j', j' < (a[i]!).size → (a[i]!)[j']! ≠ key) ∨ (0 ≤ (if j < (a[i]!).size then (j : Int) else -1) ∧ (if j < (a[i]!).size then (j : Int) else -1) < (a[0]!).size ∧ (a[i]!)[(if j < (a[i]!).size then (j : Int) else -1).toNat]! = key))`
        - **term**: `j + 1`
    - _continuation_:
      - **term**: `(i + 1, if jr = -1 then -1 else (i : Int), jr)`
        - helper lemma `step90`: `∀ (a : Array (Array Int)) (key : Int) (i : Nat) (mm nn jr : Int), (i ≤ a.size ∧ ((0 ≤ mm ∧ mm < a.size ∧ 0 ≤ nn ∧ nn < (a[0]!).size ∧ get2d a mm nn = key) ∨ (mm = -1 ∧ nn = -1 ∧ ∀ k, k < i → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key))) → (i < a.size ∧ mm = -1) → ((jr = -1 ∧ ∀ j, j < (a[i]!).size → (a[i]!)[j]! ≠ key) ∨ (0 ≤ jr ∧ jr < (a[0]!).size ∧ (a[i]!)[jr.toNat]! = key)) → (i + 1 ≤ a.size ∧ ((0 ≤ (if jr = -1 then -1 else (i : Int)) ∧ (if jr = -1 then -1 else (i : Int)) < a.size ∧ 0 ≤ jr ∧ jr < (a[0]!).size ∧ get2d a (if jr = -1 then -1 else (i : Int)) jr = key) ∨ ((if jr = -1 then -1 else (i : Int)) = -1 ∧ jr = -1 ∧ ∀ k, k < i + 1 → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key)))`
