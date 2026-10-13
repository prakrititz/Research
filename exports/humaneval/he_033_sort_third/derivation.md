# Derivation of he_033_sort_third

kind: **restate**

- **term**: `(List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)`
  - helper lemma `filter_mod_3`: `∀ (n : Nat), (List.range n).filter (fun i => decide (i % 3 = 0)) = (List.range (((n + 2) / 3))).map (fun t => t * 3)`
  - helper lemma `sort_third_ok`: `∀ (l : List Int), ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)).length = l.length ∧ (∀ i, i < l.length → i % 3 ≠ 0 → ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))[i]! = l[i]!) ∧ (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))).isPerm (atMod 3 l) = true ∧ ∀ i, i < (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))).length - 1 → (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)))[i]! ≤ (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)))[i + 1]!`
