# Derivation of he_151_double_the_difference

kind: **loop**

- **loop** over state (i : Nat, acc : Int), start (0, 0)
  - invariant: `i ≤ lst.length ∧ acc = ((lst.take i).map (Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0))).sum`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc + Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0) lst[i]!)`
