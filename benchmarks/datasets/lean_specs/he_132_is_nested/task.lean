-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isBalancedSq (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ']' ≤ (l.take k).count '[') ∧ l.count '[' = l.count ']'
-- !benchmark @end precond_aux

@[reducible, simp]
def isNested_precond (string : String) : Prop :=
  -- !benchmark @start precond
  string.toList.all (fun c => c == '[' || c == ']') = true
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isNested (string : String) (h_precond : isNested_precond (string)) : Bool :=
  -- !benchmark @start code
  Id.run do
    let l := string.toList
    for i in [0:l.length] do
      if l[i]! == ']' then continue
      let mut cnt : Int := 0
      let mut maxNest : Int := 0
      for j in [i:l.length] do
        if l[j]! == '[' then cnt := cnt + 1 else cnt := cnt - 1
        maxNest := max maxNest cnt
        if cnt == 0 then
          if maxNest ≥ 2 then return true
          break
    return false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isNested_postcond (string : String) (result: Bool) (h_precond : isNested_precond (string)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧
      isBalancedSq ((string.toList.drop i).take len) ∧ ∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isNested_spec_satisfied (string : String) (h_precond : isNested_precond (string)) :
    isNested_postcond (string) (isNested (string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
