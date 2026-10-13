# Derivation of he_037_sort_even

kind: **restate**

- **term**: `(List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)`
  - helper lemma `filter_mod_2`: `∀ (n : Nat), (List.range n).filter (fun i => decide (i % 2 = 0)) = (List.range (((n + 1) / 2))).map (fun t => t * 2)`
  - helper lemma `sort_even_ok`: `∀ (l : List Int), ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)).length = l.length ∧ (∀ i, i < l.length → i % 2 ≠ 0 → ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))[i]! = l[i]!) ∧ (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))).isPerm (atMod 2 l) = true ∧ ∀ i, i < (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))).length - 1 → (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)))[i]! ≤ (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)))[i + 1]!`
