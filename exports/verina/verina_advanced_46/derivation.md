# Derivation of verina_advanced_46

kind: **restate**

- **term**: `(let subArraySums := List.range (numbers.length + 1) |>.flatMap (fun start => List.range (numbers.length - start + 1) |>.map (fun len => numbers.drop start |>.take len |>.sum)); subArraySums.foldl max (subArraySums.headD 0))`
  - helper lemma `maxSubarraySum_ok`: `∀ (numbers : List Int) (h : maxSubarraySum_precond numbers), maxSubarraySum_postcond numbers (let subArraySums := List.range (numbers.length + 1) |>.flatMap (fun start => List.range (numbers.length - start + 1) |>.map (fun len => numbers.drop start |>.take len |>.sum)); subArraySums.foldl max (subArraySums.headD 0)) h`
