# Derivation of verina_basic_60

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven`
  - guard: `i < arr.size`
  - variant: `arr.size - i`
  - result: `acc`
  - helper lemma `exit60`: `∀ (arr acc : Array Int) (i : Nat) (h : FindEvenNumbers_precond arr), (i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven) → ¬ i < arr.size → FindEvenNumbers_postcond arr acc h`
  - **term**: `(i + 1, if isEven arr[i]! then acc.push arr[i]! else acc)`
