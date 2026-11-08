/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case right.right.right
l : List ℤ
h_precond : sortThird_precond l
⊢ ∀
    i <
      (atMod 3
            (List.map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort fun a b => decide (a ≤ b))[i / 3]! else l[i]!)
              (List.range l.length))).length -
        1,
    (atMod 3
          (List.map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort fun a b => decide (a ≤ b))[i / 3]! else l[i]!)
            (List.range l.length)))[i]! ≤
      (atMod 3
          (List.map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort fun a b => decide (a ≤ b))[i / 3]! else l[i]!)
            (List.range l.length)))[i + 1]!
-/
theorem probe (l : List Int) (h_precond : sortThird_precond l) :
    sortThird_postcond l ((List.range l.length).map (fun i => if (i % 3) = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)) h_precond := by
  sorry
