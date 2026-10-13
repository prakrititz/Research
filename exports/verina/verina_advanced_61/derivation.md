# Derivation of verina_advanced_61

kind: **restate**

- **term**: `((List.range nums.length).map (fun i => (nums.take i).myprod * (nums.drop (i + 1)).myprod))`
  - helper lemma `prod61`: `∀ (nums : List Int) (h : productExceptSelf_precond nums), productExceptSelf_postcond nums ((List.range nums.length).map (fun i => (nums.take i).myprod * (nums.drop (i + 1)).myprod)) h`
