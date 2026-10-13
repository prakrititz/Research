# Derivation of verina_basic_38

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ s.toList.length ∧ (ok = true ↔ ∀ k, k < i → s.toList[k]! = s.toList[0]!)`
  - guard: `i < s.toList.length`
  - variant: `s.toList.length - i`
  - result: `ok`
  - helper lemma `allsame_pairwise`: `∀ (l : List Char), (∀ k, k < l.length → l[k]! = l[0]!) → List.Pairwise (· = ·) l`
  - helper lemma `allsame_not`: `∀ (l : List Char), ¬ (∀ k, k < l.length → l[k]! = l[0]!) → l ≠ [] ∧ l.any (fun x => decide (x ≠ l[0]!)) = true`
  - **term**: `(i + 1, ok && decide (s.toList[i]! = s.toList[0]!))`
