# Derivation of verina_advanced_57

kind: **restate**

- **term**: `(nums1.map (fun val => match nums2.findIdx? (fun x => x == val) with | none => -1 | some idx => let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k => let pos := idx + k + 1; nums2[pos]! > val); match nextGreater with | none => -1 | some offset => nums2[idx + offset + 1]!))`
  - helper lemma `next57_key`: `∀ (nums1 nums2 : List Int) (h : nextGreaterElement_precond nums1 nums2) (ng : Int → Int), (∀ val, ng val = (match nums2.findIdx? (fun x => x == val) with | none => -1 | some idx => let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k => let pos := idx + k + 1; nums2[pos]! > val); match nextGreater with | none => -1 | some offset => nums2[idx + offset + 1]!)) → nextGreaterElement_postcond nums1 nums2 (nums1.map ng) h`
  - helper lemma `next57`: `∀ (nums1 nums2 : List Int) (h : nextGreaterElement_precond nums1 nums2), nextGreaterElement_postcond nums1 nums2 (nums1.map (fun val => match nums2.findIdx? (fun x => x == val) with | none => -1 | some idx => let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k => let pos := idx + k + 1; nums2[pos]! > val); match nextGreater with | none => -1 | some offset => nums2[idx + offset + 1]!)) h`
