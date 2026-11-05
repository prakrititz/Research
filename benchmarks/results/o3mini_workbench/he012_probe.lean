example (strings : List String) (h_precond : longest_precond strings) (h : ¬strings = []) (b : Nat)
    (hb : b < strings.length ∧ (∀ j, j < strings.length → strings[j]!.length ≤ strings[b]!.length) ∧ ∀ j, j < b → strings[j]!.length < strings[b]!.length) :
    longest_postcond strings (some strings[b]!) h_precond := by
  unfold longest_postcond
  refine ⟨b, ?_⟩
  (repeat' apply And.intro) <;> (first | omega | rfl | (simp_all; done) | (rw [Refine.forall_mem_iff_idx]; intros; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (intros; grind))
