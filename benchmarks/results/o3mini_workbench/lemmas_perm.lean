namespace Refine
theorem mergeSort_perm' {α : Type} (l : List α) (f : α → α → Bool) : (l.mergeSort f).Perm l := List.mergeSort_perm l f
theorem perm_mergeSort' {α : Type} (l : List α) (f : α → α → Bool) : l.Perm (l.mergeSort f) := (List.mergeSort_perm l f).symm
theorem filter_mergeSort_perm {α : Type} (l : List α) (f : α → α → Bool) (p : α → Bool) :
    ((l.filter p).mergeSort f).Perm (l.filter p) := List.mergeSort_perm _ f
end Refine
example (lst : List String) : ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b => decide (a.length < b.length) || a.length == b.length && !decide (b < a)).Perm (List.filter (fun s => decide (s.length % 2 = 0)) lst) := by
  solve_by_elim [Refine.mergeSort_perm']
