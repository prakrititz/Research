# Derivation of he_114_min_sub_array_sum

kind: **restate**

- **term**: `List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))`
  - helper lemma `foldl_min_facts`: `∀ (l : List Int) (m : Int), (List.foldl min m l = m ∨ List.foldl min m l ∈ l) ∧ List.foldl min m l ≤ m ∧ ∀ x ∈ l, List.foldl min m l ≤ x`
  - helper lemma `minsub_ok`: `∀ (nums : List Int), nums ≠ [] → (∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum))) ≤ ((nums.drop i).take (j - i)).sum`
