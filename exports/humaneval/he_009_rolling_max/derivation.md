# Derivation of he_009_rolling_max

kind: **restate**

- **term**: `(List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)`
  - helper lemma `foldl_max_facts`: `∀ (l : List Int) (m : Int), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l`
  - helper lemma `rolling_ok`: `∀ (numbers : List Int), ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)).length = numbers.length ∧ ∀ i, i < numbers.length → ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]!`
