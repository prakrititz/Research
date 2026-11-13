/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
a b : Array ℤ
h_precond : LongestCommonSubsequence_precond a b
⊢ (List.map (fun x => ↑x.length)
          (List.filter
            (fun l =>
              ((fun arr =>
                      List.map List.reverse
                        ((fun init => Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) init arr)
                          [[]]))
                    b).contains
                l)
            ((fun arr =>
                List.map List.reverse
                  ((fun init => Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) init arr) [[]]))
              a))).contains
      (List.map (fun _c1 => ↑_c1.length)
            (List.filter
              (fun l =>
                (List.map List.reverse
                      (Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] b)).contains
                  l)
              (List.map List.reverse
                (Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] a)))).max?.get! =
    true

case right
a b : Array ℤ
h_precond : LongestCommonSubsequence_precond a b
⊢ ((List.map (fun x => ↑x.length)
          (List.filter
            (fun l =>
              ((fun arr =>
                      List.map List.reverse
                        ((fun init => Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) init arr)
                          [[]]))
                    b).contains
                l)
            ((fun arr =>
                List.map List.reverse
                  ((fun init => Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) init arr) [[]]))
              a))).all
      fun x =>
      decide
        (x ≤
          (List.map (fun _c1 => ↑_c1.length)
                (List.filter
                  (fun l =>
                    (List.map List.reverse
                          (Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] b)).contains
                      l)
                  (List.map List.reverse
                    (Array.foldl (fun acc x => acc ++ List.map (fun sub => x :: sub) acc) [[]] a)))).max?.get!)) =
    true
-/
theorem probe (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond a b) :
    LongestCommonSubsequence_postcond a b (let allSubseq := fun arr => (arr.foldl (fun acc x => acc ++ (acc.map (fun sub => x :: sub))) [[]]).map List.reverse; let subseqA := allSubseq a; let subseqB := allSubseq b; let commonSubseqLens := (subseqA.filter (fun l => subseqB.contains l)).map (fun _c1 => _c1.length); (commonSubseqLens.max?.get! : Int)) h_precond := by
  sorry
