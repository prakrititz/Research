r"""Hand-written derivations for Verina tasks, batch AE (advanced: the n-th ugly number with a proved search bound).

The auxiliary facts (``divideOut 1 p = 1``, ``isUgly (2^k)``, the count of powers of two below ``2^m``) are ``have``s inside the
lemma that needs them: the cascade tries *every* helper lemma of a step on every obligation, and a long list exhausts the
heartbeats of one obligation (found here)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_INV = 'x ≤ 2 ^ (n - 1) ∧ c = ((List.range x).filter (fun i => isUgly i)).length ∧ c < n'
_GUARD = 'x < 2 ^ (n - 1) ∧ ¬ (isUgly x = true ∧ c + 1 = n)'
_STEP = {"name": "step58",
         "statement": "∀ (n x c : Nat), (" + _INV + ") → (" + _GUARD + ") → "
                      "(x + 1 ≤ 2 ^ (n - 1) ∧ (if isUgly x = true then c + 1 else c) = ((List.range (x + 1)).filter (fun i => isUgly i)).length ∧ "
                      "(if isUgly x = true then c + 1 else c) < n)",
         "proof": 'by\n  intro n x c hinv hg\n  have count_succ : ∀ (p : Nat → Bool) (x : Nat), ((List.range (x + 1)).filter p).length = ((List.range x).filter p).length + (if p x = true then 1 else 0) := by\n    intro p x\n    rw [List.range_succ, List.filter_append, List.length_append]\n    by_cases h : p x = true <;> simp [h]\n  obtain ⟨hx, hc, hlt⟩ := hinv\n  obtain ⟨hxlt, hg⟩ := hg\n  have hcs := count_succ (fun i => isUgly i) x\n  refine ⟨by omega, ?_, ?_⟩\n  · rw [hcs]\n    by_cases hu : isUgly x = true\n    · simp [hu, hc]\n    · simp [hu, hc]\n  · by_cases hu : isUgly x = true\n    · rw [if_pos hu]\n      have : c + 1 ≠ n := fun e => hg ⟨hu, e⟩\n      omega\n    · rw [if_neg hu]; exact hlt\n'}
_INIT = {"name": "init58",
         "statement": "∀ (n : Nat), nthUglyNumber_precond n → (0 ≤ 2 ^ (n - 1) ∧ 0 = ((List.range 0).filter (fun i => isUgly i)).length ∧ 0 < n)",
         "proof": "by intro n hn\n  exact ⟨Nat.zero_le _, by simp, hn⟩"}
_EXIT = {"name": "exit58",
         "statement": "∀ (n : Nat) (h : nthUglyNumber_precond n) (x c : Nat), (" + _INV + ") → ¬ (" + _GUARD + ") → nthUglyNumber_postcond n x h",
         "proof": "by\n  intro n h x c hinv hng\n  have dO_one : ∀ (p : Nat), divideOut 1 p = 1 := by\n    intro p\n    rw [divideOut]\n    split_ifs with h\n    · obtain ⟨h1, _, h3⟩ := h\n      rw [Nat.mod_eq_of_lt h1] at h3; omega\n    · rfl\n  have dO_pow2 : ∀ (k : Nat), divideOut (2 ^ k) 2 = 1 := by\n    intro k\n    induction k with\n    | zero => simpa using dO_one 2\n    | succ k ih =>\n      rw [divideOut]\n      have hc : 2 > 1 ∧ 2 ^ (k + 1) > 0 ∧ 2 ^ (k + 1) % 2 = 0 := by\n        refine ⟨by omega, by positivity, ?_⟩\n        rw [pow_succ]; simp\n      rw [dif_pos hc]\n      have : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; simp\n      show divideOut (2 ^ (k + 1) / 2) 2 = 1\n      rw [this]; exact ih\n  have ugly_pow2 : ∀ (k : Nat), isUgly (2 ^ k) = true := by\n    intro k\n    unfold isUgly\n    have hne : 2 ^ k ≠ 0 := by positivity\n    rw [if_neg hne]\n    simp only [dO_pow2, dO_one]\n    decide\n  have count_pow2 : ∀ (m : Nat), m ≤ ((List.range (2 ^ m)).filter (fun i => isUgly i)).length := by\n    intro m\n    have hsub : (List.range m).map (fun k => 2 ^ k) ⊆ (List.range (2 ^ m)).filter (fun i => isUgly i) := by\n      intro x hx\n      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx\n      refine List.mem_filter.mpr ⟨List.mem_range.mpr ?_, by simpa using ugly_pow2 k⟩\n      exact Nat.pow_lt_pow_right (by omega) (List.mem_range.mp hk)\n    have hnd : ((List.range m).map (fun k => 2 ^ k)).Nodup :=\n      List.Nodup.map (Nat.pow_right_injective (le_refl 2)) List.nodup_range\n    have := (hnd.subperm hsub).length_le\n    simpa using this\n  obtain ⟨hx, hc, hlt⟩ := hinv\n  have hg : isUgly x = true ∧ c + 1 = n := by\n    by_cases hlt' : x < 2 ^ (n - 1)\n    · by_contra hcon\n      exact hng ⟨hlt', hcon⟩\n    · have hxe : x = 2 ^ (n - 1) := by omega\n      have h1 := count_pow2 (n - 1)\n      rw [← hxe] at h1\n      refine ⟨by rw [hxe]; exact ugly_pow2 _, ?_⟩\n      omega\n  unfold nthUglyNumber_postcond\n  exact ⟨hg.1, by rw [← hc]; omega⟩\n"}

ORACLES_MORE = {
    "verina_advanced_58": with_lemmas(
        loop([["x", "Nat"], ["c", "Nat"]], ["0", "0"], _INV, _GUARD, "2 ^ (n - 1) - x", "x",
             term("(x + 1, if isUgly x = true then c + 1 else c)")),
        [_STEP, _INIT, _EXIT]),
}
