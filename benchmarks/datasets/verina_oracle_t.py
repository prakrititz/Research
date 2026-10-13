r"""Hand-written derivations for Verina tasks, batch T (advanced: next greater element)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_BODY = 'match nums2.findIdx? (fun x => x == val) with | none => -1 | some idx => let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k => let pos := idx + k + 1; nums2[pos]! > val); match nextGreater with | none => -1 | some offset => nums2[idx + offset + 1]!'
_E57 = "nums1.map (fun val => " + _BODY + ")"
_KEY = {"name": "next57_key",
        "statement": "∀ (nums1 nums2 : List Int) (h : nextGreaterElement_precond nums1 nums2) (ng : Int → Int), (∀ val, ng val = (" + _BODY + ")) → "
                     "nextGreaterElement_postcond nums1 nums2 (nums1.map ng) h",
        "proof": "by\n  intro nums1 nums2 h ng hng\n  obtain ⟨_, _, hsub⟩ := h\n  unfold nextGreaterElement_postcond\n  refine ⟨by simp, ?_, ?_⟩\n  · rw [List.all_eq_true]\n    intro i hi\n    have hi' := List.mem_range.mp hi\n    simp only [decide_eq_true_eq]\n    have hv : nums1[i]! ∈ nums2 := by\n      have := List.all_eq_true.mp hsub nums1[i]! (by rw [getElem!_pos nums1 i hi']; exact List.getElem_mem hi')\n      simpa using this\n    have hres : (nums1.map ng)[i]! = ng nums1[i]! := by\n      rw [getElem!_pos _ i (by simpa using hi'), getElem!_pos nums1 i hi']; simp\n    rw [hres]\n    rw [hng]\n    generalize nums1[i]! = val at hv ⊢\n    dsimp only\n    split\n    · rename_i hf\n      exfalso\n      have := List.findIdx?_eq_none_iff.mp hf val hv\n      simp at this\n    · rename_i idx hf\n      dsimp only\n      have hm : ∀ g : Option Nat, (match g with\n          | none => decide ((match g with | none => (-1 : Int) | some o => nums2[idx + o + 1]!) = -1)\n          | some o => decide ((match g with | none => (-1 : Int) | some o => nums2[idx + o + 1]!) = nums2[idx + o + 1]!)) = true := by\n        intro g; cases g <;> simp\n      exact hm _\n  · rw [List.all_eq_true]\n    intro v hv\n    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv\n    simp only [decide_eq_true_eq]\n    show ng a = -1 ∨ ng a ∈ nums2\n    rw [hng]\n    split\n    · left; rfl\n    · rename_i idx hf\n      simp only []\n      split\n      · left; rfl\n      · rename_i off hg\n        right\n        have hmem := List.mem_of_find?_eq_some hg\n        have hlt := List.mem_range.mp hmem\n        have : idx + off + 1 < nums2.length := by omega\n        rw [getElem!_pos nums2 _ this]\n        exact List.getElem_mem this\n"}
_L57 = {"name": "next57", "statement": "∀ (nums1 nums2 : List Int) (h : nextGreaterElement_precond nums1 nums2), nextGreaterElement_postcond nums1 nums2 (" + _E57 + ") h",
        "proof": "by intro nums1 nums2 h\n  exact next57_key nums1 nums2 h _ (fun val => rfl)"}

ORACLES_MORE = {
    "verina_advanced_57": with_lemmas(term("(" + _E57 + ")"), [_KEY, _L57]),
}
