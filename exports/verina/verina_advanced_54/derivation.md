# Derivation of verina_advanced_54

kind: **restate**

- **term**: `((List.range (nums.length + 1)).find? (fun x => decide (x ∉ nums))).getD 0`
  - helper lemma `missing54`: `∀ (nums : List Nat) (h : missingNumber_precond nums), missingNumber_postcond nums (((List.range (nums.length + 1)).find? (fun x => decide (x ∉ nums))).getD 0) h`
