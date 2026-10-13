# Derivation of verina_basic_41

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ a.size ∧ (ok = true ↔ ∀ k, k < i → a[k]! = a[0]!)`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `ok`
  - helper lemma `allsame_arr_pairwise`: `∀ (a : Array Int), (∀ k, k < a.size → a[k]! = a[0]!) → List.Pairwise (· = ·) a.toList`
  - helper lemma `allsame_arr_not`: `∀ (a : Array Int), 0 < a.size → ¬ (∀ k, k < a.size → a[k]! = a[0]!) → a.toList.any (fun x => decide (x ≠ a.toList[0]!)) = true`
  - **term**: `(i + 1, ok && decide (a[i]! = a[0]!))`
