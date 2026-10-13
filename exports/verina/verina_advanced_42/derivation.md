# Derivation of verina_advanced_42

kind: **restate**

- **term**: `(((List.range prices.length).flatMap (fun i => (List.range prices.length).map (fun j => if i < j then prices[j]! - prices[i]! else 0))).foldl max 0)`
  - helper lemma `profit42`: `∀ (prices : List Nat) (h : maxProfit_precond prices), maxProfit_postcond prices (((List.range prices.length).flatMap (fun i => (List.range prices.length).map (fun j => if i < j then prices[j]! - prices[i]! else 0))).foldl max 0) h`
