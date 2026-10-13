# Derivation of verina_advanced_8

kind: **loop**

- **loop** over state (s : Nat), start (0)
  - invariant: `s ≤ gas.length ∧ ∀ k, k < s → ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(k + j) % gas.length]! - cost[(k + j) % gas.length]!) 0 ≥ 0)) = true)`
  - guard: `s < gas.length ∧ ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(s + j) % gas.length]! - cost[(s + j) % gas.length]!) 0 ≥ 0)) = true)`
  - variant: `gas.length - s`
  - result: `if s < gas.length then (s : Int) else -1`
  - helper lemma `exit8`: `∀ (gas cost : List Int) (h : canCompleteCircuit_precond gas cost) (s : Nat), (s ≤ gas.length ∧ ∀ k, k < s → ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(k + j) % gas.length]! - cost[(k + j) % gas.length]!) 0 ≥ 0)) = true)) → ¬ (s < gas.length ∧ ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(s + j) % gas.length]! - cost[(s + j) % gas.length]!) 0 ≥ 0)) = true)) → canCompleteCircuit_postcond gas cost (if s < gas.length then (s : Int) else -1) h`
  - helper lemma `step8`: `∀ (gas cost : List Int) (s : Nat), (s ≤ gas.length ∧ ∀ k, k < s → ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(k + j) % gas.length]! - cost[(k + j) % gas.length]!) 0 ≥ 0)) = true)) → (s < gas.length ∧ ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(s + j) % gas.length]! - cost[(s + j) % gas.length]!) 0 ≥ 0)) = true)) → (s + 1 ≤ gas.length ∧ ∀ k, k < s + 1 → ¬ ((List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => t + gas[(k + j) % gas.length]! - cost[(k + j) % gas.length]!) 0 ≥ 0)) = true))`
  - **term**: `s + 1`
