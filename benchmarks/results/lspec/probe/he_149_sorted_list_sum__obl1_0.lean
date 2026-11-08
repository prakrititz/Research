/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case right
lst : List String
h_precond : sortedListSum_precond lst
⊢ ∀
    i <
      ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
            decide (a.length < b.length) || a.length == b.length && !decide (b < a)).length -
        1,
    ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
              decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i]!.length <
        ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
              decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i + 1]!.length ∨
      ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
                decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i]!.length =
          ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
                decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i + 1]!.length ∧
        ¬((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
                decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i + 1]! <
            ((List.filter (fun s => decide (s.length % 2 = 0)) lst).mergeSort fun a b =>
                decide (a.length < b.length) || a.length == b.length && !decide (b < a))[i]!
-/
theorem probe (lst : List String) (h_precond : sortedListSum_precond lst) :
    sortedListSum_postcond lst ((lst.filter (fun s => decide ((s.length % 2) = 0))).mergeSort (fun a b => (decide (a.length < b.length)) || ((a.length == b.length) && (!(decide (b < a)))))) h_precond := by
  sorry
