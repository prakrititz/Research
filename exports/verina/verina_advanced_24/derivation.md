# Derivation of verina_advanced_24

kind: **restate**

- **term**: `(let allIncreasing := lengthOfLIS_postcond.subsequences nums |>.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l); (((allIncreasing.map List.length).foldl max 0 : Nat) : Int))`
  - helper lemma `sub_nil24`: `∀ (xs : List Int), [] ∈ lengthOfLIS_postcond.subsequences xs`
  - helper lemma `lis24`: `∀ (nums : List Int) (h : lengthOfLIS_precond nums), lengthOfLIS_postcond nums (let allIncreasing := lengthOfLIS_postcond.subsequences nums |>.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l); (((allIncreasing.map List.length).foldl max 0 : Nat) : Int)) h`
