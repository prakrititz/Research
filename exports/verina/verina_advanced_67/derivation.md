# Derivation of verina_advanced_67

kind: **loop**

- **loop** over state (i : Nat, acc : List (Char × Nat)), start (0, [])
  - invariant: `i ≤ s.toList.length ∧ decodeRLE acc.reverse = String.mk (s.toList.take i) ∧ (∀ p ∈ acc, 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) acc`
  - guard: `i < s.toList.length`
  - variant: `s.toList.length - i`
  - result: `acc.reverse`
  - helper lemma `str_mk_append`: `∀ (a b : List Char), String.mk (a ++ b) = String.mk a ++ String.mk b`
  - helper lemma `dec_append`: `∀ (xs ys : List (Char × Nat)), decodeRLE (xs ++ ys) = decodeRLE xs ++ decodeRLE ys`
  - helper lemma `dec_single`: `∀ (c : Char) (n : Nat), decodeRLE [(c, n)] = String.mk (List.replicate n c)`
  - helper lemma `dec_rev_cons`: `∀ (c : Char) (n : Nat) (rest : List (Char × Nat)), decodeRLE ((c, n) :: rest).reverse = decodeRLE rest.reverse ++ String.mk (List.replicate n c)`
  - helper lemma `rle_step2`: `∀ (cs : List Char) (i : Nat) (acc : List (Char × Nat)), i < cs.length → (i ≤ cs.length ∧ decodeRLE acc.reverse = String.mk (cs.take i) ∧ (∀ p ∈ acc, 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) acc) → (i + 1 ≤ cs.length ∧ decodeRLE (if (acc.head?.map Prod.fst) = some cs[i]! then (cs[i]!, (acc.headD (cs[i]!, 0)).2 + 1) :: acc.tail else (cs[i]!, 1) :: acc).reverse = String.mk (cs.take (i + 1)) ∧ (∀ p ∈ (if (acc.head?.map Prod.fst) = some cs[i]! then (cs[i]!, (acc.headD (cs[i]!, 0)).2 + 1) :: acc.tail else (cs[i]!, 1) :: acc), 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) (if (acc.head?.map Prod.fst) = some cs[i]! then (cs[i]!, (acc.headD (cs[i]!, 0)).2 + 1) :: acc.tail else (cs[i]!, 1) :: acc))`
  - helper lemma `exit67`: `∀ (s : String) (h : runLengthEncode_precond s) (i : Nat) (acc : List (Char × Nat)), (i ≤ s.toList.length ∧ decodeRLE acc.reverse = String.mk (s.toList.take i) ∧ (∀ p ∈ acc, 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) acc) → ¬ i < s.toList.length → runLengthEncode_postcond s acc.reverse h`
  - **term**: `(i + 1, (if (acc.head?.map Prod.fst) = some s.toList[i]! then (s.toList[i]!, (acc.headD (s.toList[i]!, 0)).2 + 1) :: acc.tail else (s.toList[i]!, 1) :: acc))`
