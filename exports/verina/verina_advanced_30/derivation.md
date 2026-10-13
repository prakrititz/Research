# Derivation of verina_advanced_30

kind: **restate**

- **term**: `(((List.range (nums.length + 1)).flatMap (fun s => (List.range (nums.length + 1)).filter (fun L => decide (s + L ≤ nums.length ∧ (List.range L).all (fun i => decide (i + 1 < L → nums[s + i]! < nums[s + i + 1]!)) = true)))).foldl max 0)`
  - helper lemma `streak30`: `∀ (nums : List Int) (h : longestIncreasingStreak_precond nums), longestIncreasingStreak_postcond nums (((List.range (nums.length + 1)).flatMap (fun s => (List.range (nums.length + 1)).filter (fun L => decide (s + L ≤ nums.length ∧ (List.range L).all (fun i => decide (i + 1 < L → nums[s + i]! < nums[s + i + 1]!)) = true)))).foldl max 0) h`
