# Derivation of he_068_pluck

kind: **loop**

- **loop** over state (i : Nat, f : Bool, v : Nat, ix : Nat), start (0, false, 0, 0)
  - invariant: `i ≤ arr.length ∧ (f = true ↔ ∃ k, k < i ∧ arr[k]! % 2 = 0) ∧ (f = true → ix < i ∧ arr[ix]! = v ∧ v % 2 = 0 ∧ (∀ k, k < i → arr[k]! % 2 = 0 → v ≤ arr[k]!) ∧ ∀ j, j < ix → arr[j]! ≠ v)`
  - guard: `i < arr.length`
  - variant: `arr.length - i`
  - result: `if f = true then [v, ix] else []`
  - helper lemma `pluck_exit`: `∀ (arr : List Nat) (f : Bool) (v ix : Nat), (arr.length ≤ arr.length ∧ (f = true ↔ ∃ k, k < arr.length ∧ arr[k]! % 2 = 0) ∧ (f = true → ix < arr.length ∧ arr[ix]! = v ∧ v % 2 = 0 ∧ (∀ k, k < arr.length → arr[k]! % 2 = 0 → v ≤ arr[k]!) ∧ ∀ j, j < ix → arr[j]! ≠ v)) → (((if f = true then [v, ix] else []) = [] ↔ ∀ x ∈ arr, x % 2 = 1) ∧ ((if f = true then [v, ix] else []) ≠ [] → (if f = true then [v, ix] else []).length = 2 ∧ (if f = true then [v, ix] else [])[1]! < arr.length ∧ arr[(if f = true then [v, ix] else [])[1]!]! = (if f = true then [v, ix] else [])[0]! ∧ (if f = true then [v, ix] else [])[0]! % 2 = 0 ∧ (∀ x ∈ arr, x % 2 = 0 → (if f = true then [v, ix] else [])[0]! ≤ x) ∧ ∀ j, j < (if f = true then [v, ix] else [])[1]! → arr[j]! ≠ (if f = true then [v, ix] else [])[0]!))`
  - **term**: `(i + 1, f || decide (arr[i]! % 2 = 0), if arr[i]! % 2 = 0 ∧ (f = false ∨ arr[i]! < v) then arr[i]! else v, if arr[i]! % 2 = 0 ∧ (f = false ∨ arr[i]! < v) then i else ix)`
