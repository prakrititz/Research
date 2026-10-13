# Derivation of verina_advanced_43

kind: **restate**

- **term**: `(let sublists := nums.sublists.filter (· ≠ []); let products := sublists.map (List.foldl (· * ·) 1); products.foldl max (products.headD 0))`
  - helper lemma `ms43`: `∀ (nums : List Int) (h : maxStrength_precond nums), maxStrength_postcond nums (let sublists := nums.sublists.filter (· ≠ []); let products := sublists.map (List.foldl (· * ·) 1); products.foldl max (products.headD 0)) h`
