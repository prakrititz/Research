# Derivation of verina_advanced_62

kind: **restate**

- **term**: `(if heights.length < 3 then 0 else rain_postcond.sum_water heights (fun i => max 0 (min (rain_postcond.ml heights i 0 0) (rain_postcond.mr heights i 0) - heights[i]!)) 0 0)`
  - helper lemma `nonneg_sw`: `∀ (heights : List Int) (w : Nat → Int), (∀ i, 0 ≤ w i) → ∀ (n i : Nat) (acc : Int), heights.length - i ≤ n → 0 ≤ acc → 0 ≤ rain_postcond.sum_water heights w i acc`
  - helper lemma `rain62`: `∀ (heights : List Int) (h : rain_precond heights), rain_postcond heights (if heights.length < 3 then 0 else rain_postcond.sum_water heights (fun i => max 0 (min (rain_postcond.ml heights i 0 0) (rain_postcond.mr heights i 0) - heights[i]!)) 0 0) h`
