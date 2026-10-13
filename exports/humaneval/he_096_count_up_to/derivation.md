# Derivation of he_096_count_up_to

kind: **loop**

- **loop** over state (i : Nat, acc : List Nat), start (0, [])
  - invariant: `i ≤ n ∧ acc = (List.range i).filter (fun p => decide (Nat.Prime p))`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - helper lemma `count_up_to_exit`: `∀ (n : Nat) (acc : List Nat), (n ≤ n ∧ acc = (List.range n).filter (fun p => decide (Nat.Prime p))) → (∀ p ∈ acc, p < n ∧ Nat.Prime p) ∧ (∀ p, p < n → Nat.Prime p → p ∈ acc) ∧ ∀ i, i < acc.length - 1 → acc[i]! < acc[i + 1]!`
  - **term**: `(i + 1, if Nat.Prime i then acc ++ [i] else acc)`
