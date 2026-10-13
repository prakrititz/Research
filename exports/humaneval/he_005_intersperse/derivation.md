# Derivation of he_005_intersperse

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ numbers.length ∧ acc.length = (if i = 0 then 0 else 2 * i - 1) ∧ (∀ k, k < i → acc[2 * k]! = numbers[k]!) ∧ ∀ k, k + 1 < i → acc[2 * k + 1]! = delimeter`
  - guard: `i < numbers.length`
  - variant: `numbers.length - i`
  - result: `acc`
  - helper lemma `append_pair_idx`: `∀ (a : List Int) (d x : Int) (j : Nat), (a ++ [d, x])[j]! = (if j < a.length then a[j]! else if j = a.length then d else if j = a.length + 1 then x else default)`
  - **term**: `(i + 1, if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])`
