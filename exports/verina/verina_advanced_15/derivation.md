# Derivation of verina_advanced_15

kind: **restate**

- **term**: `(let nums' := nums.zipIdx; nums'.any (fun (x, i) => nums'.any (fun (y, j) => nums'.any (fun (z, k) => decide (i < j ∧ j < k ∧ x < y ∧ y < z)))))`
  - helper lemma `trip15`: `∀ (nums : List Int) (h : increasingTriplet_precond nums), increasingTriplet_postcond nums (let nums' := nums.zipIdx; nums'.any (fun (x, i) => nums'.any (fun (y, j) => nums'.any (fun (z, k) => decide (i < j ∧ j < k ∧ x < y ∧ y < z))))) h`
