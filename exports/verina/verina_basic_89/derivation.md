# Derivation of verina_basic_89

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ s.length ∧ (∀ x, x ∈ acc ↔ x ∈ s.take i) ∧ acc.Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) acc`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `acc`
  - helper lemma `idxOf_le_of_getElem`: `∀ (s : List Int) (k : Nat) (a : Int), s[k]? = some a → s.idxOf a ≤ k`
  - helper lemma `idxOf_take_lt`: `∀ (s : List Int) (i : Nat) (a : Int), a ∈ s.take i → s.idxOf a < i`
  - helper lemma `idxOf_ge_of_not_mem_take`: `∀ (s : List Int) (i : Nat) (x : Int), s[i]? = some x → x ∉ s.take i → i ≤ s.idxOf x`
  - helper lemma `step89`: `∀ (s : List Int) (i : Nat) (acc : List Int), (i ≤ s.length ∧ (∀ x, x ∈ acc ↔ x ∈ s.take i) ∧ acc.Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) acc) → i < s.length → (i + 1 ≤ s.length ∧ (∀ x, x ∈ (if acc.contains s[i]! then acc else acc ++ [s[i]!]) ↔ x ∈ s.take (i + 1)) ∧ ((if acc.contains s[i]! then acc else acc ++ [s[i]!])).Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) (if acc.contains s[i]! then acc else acc ++ [s[i]!]))`
  - helper lemma `exit89`: `∀ (s : List Int) (h : SetToSeq_precond s) (i : Nat) (acc : List Int), (i ≤ s.length ∧ (∀ x, x ∈ acc ↔ x ∈ s.take i) ∧ acc.Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) acc) → ¬ i < s.length → SetToSeq_postcond s acc h`
  - **term**: `(i + 1, (if acc.contains s[i]! then acc else acc ++ [s[i]!]))`
