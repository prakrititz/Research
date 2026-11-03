-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def isVowelC (c : Char) : Bool := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c
@[reducible, simp] def goodAt (w : List Char) (i : Nat) : Prop :=
  1 ≤ i ∧ i + 1 < w.length ∧ isVowelC w[i]! = true ∧ isVowelC w[i - 1]! = false ∧ isVowelC w[i + 1]! = false
-- !benchmark @end precond_aux

@[reducible, simp]
def getClosestVowel_precond (word : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def getClosestVowel (word : String) (h_precond : getClosestVowel_precond (word)) : String :=
  -- !benchmark @start code
  let w := word.toList
  match ((List.range w.length).reverse.find? (fun i => 1 ≤ i && i + 1 < w.length && isVowelC w[i]! && !isVowelC w[i - 1]! && !isVowelC w[i + 1]!)) with
  | some i => String.singleton w[i]!
  | none => ""
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def getClosestVowel_postcond (word : String) (result: String) (h_precond : getClosestVowel_precond (word)) :=
  -- !benchmark @start postcond
  let w := word.toList
  (result = "" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧
  (result ≠ "" → ∃ i, i < w.length ∧ goodAt w i ∧ result = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem getClosestVowel_spec_satisfied (word : String) (h_precond : getClosestVowel_precond (word)) :
    getClosestVowel_postcond (word) (getClosestVowel (word) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
