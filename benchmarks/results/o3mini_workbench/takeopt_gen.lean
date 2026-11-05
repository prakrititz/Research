namespace Refine
theorem take_succ_getElem? {α : Type} (l : List α) (i : Nat) : l.take (i + 1) = l.take i ++ l[i]?.toList := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih => cases i with
    | zero => simp
    | succ n => simp [List.take_succ_cons, ih]
end Refine
example (values : List PyVal) (i : Nat) (acc : List Int)
    (h1i : i ≤ values.length ∧ acc = (values.take i).filterMap (fun v => match v with | PyVal.int n => some n | _ => none))
    (h1g : i < values.length) :
    (match values[i]? with | some (PyVal.int n) => acc ++ [n] | _ => acc) =
      (values.take (i + 1)).filterMap (fun v => match v with | PyVal.int n => some n | _ => none) := by
  (try intros); (try casesm* _ ∧ _); (try simp only [Refine.take_succ_getElem?, List.filterMap_append, List.map_append, List.filter_append, List.flatMap_append] at *); (try subst_vars); (try split) <;> simp_all
