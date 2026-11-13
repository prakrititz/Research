/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond nums1 nums2) :
    nextGreaterElement_postcond nums1 nums2 (nums1.map (fun val => match nums2.findIdx? (fun x => x == val) with | none => -1 | some idx => let nextGreater := (List.range ((nums2.length - idx) - 1)).find? (fun k => let pos := (idx + k) + 1; nums2[pos]! > val); match nextGreater with | none => -1 | some offset => nums2[(idx + offset) + 1]!)) h_precond := by
  sorry
