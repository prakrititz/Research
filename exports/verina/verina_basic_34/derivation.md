# Derivation of verina_basic_34

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven`
  - guard: `i < arr.size`
  - variant: `arr.size - i`
  - result: `acc`
  - helper lemma `idxOf_filter_mono`: `∀ (p : Int → Bool) (l : List Int) (x y : Int), p x = true → p y = true → l.idxOf x ≤ l.idxOf y → (l.filter p).idxOf x ≤ (l.filter p).idxOf y`
  - helper lemma `fen_exit`: `∀ (arr result : Array Int) (h : findEvenNumbers_precond arr), result.toList = arr.toList.filter isEven → findEvenNumbers_postcond arr result h`
  - helper lemma `exit34`: `∀ (arr acc : Array Int) (i : Nat) (h : findEvenNumbers_precond arr), (i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven) → ¬ i < arr.size → findEvenNumbers_postcond arr acc h`
  - **term**: `(i + 1, if isEven arr[i]! then acc.push arr[i]! else acc)`
