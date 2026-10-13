# Derivation of verina_advanced_45

kind: **restate**

- **cases** on `xs = []`
  - _then_:
    - **term**: `0`
      - helper lemma `ms45_nil`: `∀ (xs : List Int) (h : maxSubarraySum_precond xs), xs = [] → maxSubarraySum_postcond xs (0) h`
  - _else_:
    - **term**: `(let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start => List.range' 1 (xs.length - start) |>.map (fun len => ((xs.drop start).take len).sum)); subarray_sums.foldl max (subarray_sums.headD 0))`
      - helper lemma `ms45_ne`: `∀ (xs : List Int) (h : maxSubarraySum_precond xs), xs ≠ [] → maxSubarraySum_postcond xs (let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start => List.range' 1 (xs.length - start) |>.map (fun len => ((xs.drop start).take len).sum)); subarray_sums.foldl max (subarray_sums.headD 0)) h`
