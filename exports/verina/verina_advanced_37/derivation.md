# Derivation of verina_advanced_37

kind: **restate**

- **term**: `(nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0`
  - helper lemma `maj37`: `∀ (nums : List Int) (h : majorityElement_precond nums), majorityElement_postcond nums ((nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0) h`
