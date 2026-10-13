# Derivation of verina_advanced_29

kind: **restate**

- **cases** on `nums = []`
  - _then_:
    - **term**: `0`
      - helper lemma `lg29_nil`: `∀ (nums : List Nat) (k : Nat) (h : longestGoodSubarray_precond nums k), nums = [] → longestGoodSubarray_postcond nums k (0) h`
  - _else_:
    - **term**: `(let subArrays := List.range (nums.length + 1) |>.flatMap (fun start => List.range (nums.length - start + 1) |>.map (fun len => nums.drop start |>.take len)); let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x)); let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k)); (validSubArrays.map (·.length)).foldl max 0)`
      - helper lemma `lg29_ne`: `∀ (nums : List Nat) (k : Nat) (h : longestGoodSubarray_precond nums k), ¬ nums = [] → longestGoodSubarray_postcond nums k (let subArrays := List.range (nums.length + 1) |>.flatMap (fun start => List.range (nums.length - start + 1) |>.map (fun len => nums.drop start |>.take len)); let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x)); let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k)); (validSubArrays.map (·.length)).foldl max 0) h`
