-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')
-- !benchmark @end precond_aux

@[reducible, simp]
def solve84_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def solve84 (N : Nat) (h_precond : solve84_precond (N)) : String :=
  -- !benchmark @start code
  Id.run do
    let total := ((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum
    let mut m := total
    let mut bits := ""
    while m != 0 do
      bits := toString (m % 2) ++ bits
      m := m / 2
    return (if total == 0 then "0" else bits)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def solve84_postcond (N : Nat) (result: String) (h_precond : solve84_precond (N)) :=
  -- !benchmark @start postcond
  isBinary result.toList (((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem solve84_spec_satisfied (N : Nat) (h_precond : solve84_precond (N)) :
    solve84_postcond (N) (solve84 (N) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
