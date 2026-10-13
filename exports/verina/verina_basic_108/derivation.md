# Derivation of verina_basic_108

kind: **loop**

- **bind** `s : Array Int` with property `s.size = operations.length + 1 ∧ s[0]! = 0 ∧ ∀ i, i < operations.length → s[i+1]! = s[i]! + operations[i]!`
  - helper lemma `exit108`: `∀ (ops : List Int) (s : Array Int) (h : below_zero_precond ops), (s.size = ops.length + 1 ∧ s[0]! = 0 ∧ ∀ i, i < ops.length → s[i+1]! = s[i]! + ops[i]!) → below_zero_postcond ops (s, (List.range ops.length).any (fun i => decide (s[i+1]! < 0))) h`
  - _value_:
    - **loop** over state (i : Nat, acc : Array Int), start (0, #[0])
      - invariant: `i ≤ operations.length ∧ acc.size = i + 1 ∧ acc[0]! = 0 ∧ ∀ j, j < i → acc[j+1]! = acc[j]! + operations[j]!`
      - guard: `i < operations.length`
      - variant: `operations.length - i`
      - result: `acc`
      - **term**: `(i + 1, acc.push (acc[i]! + operations[i]!))`
  - _continuation_:
    - **term**: `(s, (List.range operations.length).any (fun i => decide (s[i+1]! < 0)))`
