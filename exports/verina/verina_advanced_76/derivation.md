# Derivation of verina_advanced_76

kind: **restate**

- **term**: `((nums.eraseDups.mergeSort (fun x y => decide (nums.count y ≤ nums.count x))).take k)`
  - helper lemma `nodup_eraseDups_aux`: `∀ (n : Nat) (l : List Int), l.length ≤ n → l.eraseDups.Nodup`
  - helper lemma `nodup_eraseDups`: `∀ (l : List Int), l.eraseDups.Nodup`
  - helper lemma `topk76`: `∀ (nums : List Int) (k : Nat) (h : topKFrequent_precond nums k), topKFrequent_postcond nums k ((nums.eraseDups.mergeSort (fun x y => decide (nums.count y ≤ nums.count x))).take k) h`
