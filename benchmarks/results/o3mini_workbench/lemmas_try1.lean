namespace Refine

theorem getElem_bang_map_range {α : Type} [Inhabited α] (f : Nat → α) (n i : Nat) (h : i < n) :
    ((List.range n).map f)[i]! = f i := by
  have hl : i < ((List.range n).map f).length := by simp; exact h
  rw [getElem!_pos _ i hl]
  simp

theorem getElem_bang_append {α : Type} [Inhabited α] (a b : List α) (j : Nat) :
    (a ++ b)[j]! = if j < a.length then a[j]! else b[j - a.length]! := by
  by_cases h : j < a.length
  · rw [if_pos h, getElem!_pos (a ++ b) j (by simp; omega), getElem!_pos a j h]
    simp [List.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : j < (a ++ b).length
    · have h3 : j - a.length < b.length := by simp at h2; omega
      rw [getElem!_pos (a ++ b) j h2, getElem!_pos b (j - a.length) h3]
      simp [List.getElem_append_right (by omega : a.length ≤ j)]
    · have h3 : ¬ (j - a.length < b.length) := by simp at h2; omega
      rw [getElem!_neg (a ++ b) j h2, getElem!_neg b (j - a.length) h3]

theorem pairwise_le_nodup_lt (s : List Int) (hs : s.Pairwise (· ≤ ·)) (hn : s.Nodup) :
    ∀ i, i < s.length - 1 → s[i]! < s[i + 1]! := by
  intro i hi
  have h1 : i < s.length := by omega
  have h2 : i + 1 < s.length := by omega
  rw [getElem!_pos s i h1, getElem!_pos s (i + 1) h2]
  have hle : s[i] ≤ s[i + 1] := List.pairwise_iff_getElem.mp hs i (i + 1) h1 h2 (by omega)
  have hne : s[i] ≠ s[i + 1] := by
    intro heq
    have := (List.Nodup.getElem_inj_iff hn).mp heq
    omega
  omega

theorem dedup_mergeSort_strict (l : List Int) :
    ∀ i, i < (l.dedup.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i]! < (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  apply pairwise_le_nodup_lt
  · have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l.dedup
    simpa using this
  · exact (List.mergeSort_perm l.dedup _).nodup_iff.mpr (List.nodup_dedup l)

theorem mem_dedup_mergeSort (l : List Int) (x : Int) :
    x ∈ l.dedup.mergeSort (fun a b => decide (a ≤ b)) ↔ x ∈ l := by
  rw [(List.mergeSort_perm l.dedup _).mem_iff, List.mem_dedup]

end Refine

example (l : List Int) : (∀ i, i < (l.dedup.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i]! < (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧
    (∀ x ∈ l.dedup.mergeSort (fun a b => decide (a ≤ b)), x ∈ l) ∧ (∀ x ∈ l, x ∈ l.dedup.mergeSort (fun a b => decide (a ≤ b))) := by
  refine ⟨Refine.dedup_mergeSort_strict l, ?_, ?_⟩ <;> simp [Refine.mem_dedup_mergeSort]
