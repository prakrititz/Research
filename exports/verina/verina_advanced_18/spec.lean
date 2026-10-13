import Mathlib
namespace Array
def mkArray {α : Type} (n : Nat) (v : α) : Array α := Array.replicate n v
end Array
namespace Std.HashSet
def empty {α : Type} [BEq α] [Hashable α] : Std.HashSet α := {}
end Std.HashSet
syntax "wit_search" : tactic
macro_rules
  | `(tactic| wit_search) => `(tactic| first
      | decide
      | (refine ⟨?_, ?_⟩ <;> wit_search)
      | (refine ⟨0, ?_⟩; wit_search) | (refine ⟨1, ?_⟩; wit_search) | (refine ⟨2, ?_⟩; wit_search)
      | (refine ⟨3, ?_⟩; wit_search) | (refine ⟨4, ?_⟩; wit_search) | (refine ⟨5, ?_⟩; wit_search))

def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)

@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  True

@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))
