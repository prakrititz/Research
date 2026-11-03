-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')

def roundedHalfEven (s : Nat) : Nat := if s % 2 = 0 then s / 2 else (if (s / 2) % 2 = 0 then s / 2 else s / 2 + 1)
-- !benchmark @end precond_aux

@[reducible, simp]
def roundedAvg_precond (n : Nat) (m : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def roundedAvg (n : Nat) (m : Nat) (h_precond : roundedAvg_precond (n) (m)) : Option String :=
  -- !benchmark @start code
  if n > m then none else
    let avg := roundedHalfEven (n + m)
    let bits := Id.run do
      let mut k := avg
      let mut acc := ""
      while k != 0 do
        acc := toString (k % 2) ++ acc
        k := k / 2
      return (if avg == 0 then "0" else acc)
    some ("0b" ++ bits)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def roundedAvg_postcond (n : Nat) (m : Nat) (result: Option String) (h_precond : roundedAvg_precond (n) (m)) :=
  -- !benchmark @start postcond
  match result with
  | none => n > m
  | some b => n ≤ m ∧ b.length ≥ 3 ∧ b.toList.take 2 = ['0', 'b'] ∧ isBinary (b.toList.drop 2) (roundedHalfEven (n + m))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem roundedAvg_spec_satisfied (n : Nat) (m : Nat) (h_precond : roundedAvg_precond (n) (m)) :
    roundedAvg_postcond (n) (m) (roundedAvg (n) (m) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
