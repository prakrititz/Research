# Derivation of he_107_even_odd_palindrome

kind: **loop**

- **loop** over state (i : Nat, e : Nat, o : Nat), start (0, 0, 0)
  - invariant: `i ≤ n + 1 ∧ e = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ o = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length`
  - guard: `i < n + 1`
  - variant: `n + 1 - i`
  - result: `(e, o)`
  - helper lemma `len_filter_range_succ`: `∀ (p : Nat → Bool) (i : Nat), ((List.range (i + 1)).filter p).length = ((List.range i).filter p).length + (if p i = true then 1 else 0)`
  - helper lemma `palin_step`: `∀ (n i e o : Nat), i < n + 1 → (i ≤ n + 1 ∧ e = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ o = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length) → (i + 1 ≤ n + 1 ∧ (if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0 then e + 1 else e) = ((List.range (i + 1)).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ (if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1 then o + 1 else o) = ((List.range (i + 1)).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length)`
  - **term**: `(i + 1, if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0 then e + 1 else e, if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1 then o + 1 else o)`
