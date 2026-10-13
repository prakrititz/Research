import Mathlib

@[reducible, simp]
def stringXor_precond (a : String) (b : String) : Prop :=
  a.length = b.length ∧ a.toList.all (fun c => c == '0' || c == '1') ∧ b.toList.all (fun c => c == '0' || c == '1')

@[reducible, simp]
def stringXor_postcond (a : String) (b : String) (result: String) (h_precond : stringXor_precond (a) (b)) :=
  result.length = a.length ∧ ∀ i, i < a.length → result.toList[i]! = (if a.toList[i]! = b.toList[i]! then '0' else '1')
