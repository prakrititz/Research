# Derivation of verina_advanced_1

kind: **restate**

- **term**: `(nums.find? (fun x => decide (nums.count x = 1))).getD 0`
  - helper lemma `fl_eq`: `∀ (x : Int) (l : List Int), filterlist x l = l.filter (fun y => decide (y = x))`
  - helper lemma `fl_count`: `∀ (l : List Int) (y : Int), (l.filter (fun z => decide (z = y))).length = l.count y`
  - helper lemma `pair_le_countP`: `∀ (l : List Int) (p : Int → Bool) (x r : Int), x ≠ r → p x = true → p r = true → (l.filter (fun y => decide (y = x))).length + (l.filter (fun y => decide (y = r))).length ≤ l.countP p`
  - helper lemma `single1`: `∀ (nums : List Int) (h : FindSingleNumber_precond nums), FindSingleNumber_postcond nums ((nums.find? (fun x => decide (nums.count x = 1))).getD 0) h`
