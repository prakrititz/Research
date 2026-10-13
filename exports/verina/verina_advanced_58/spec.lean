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

@[reducible, simp]
def nthUglyNumber_precond (n : Nat) : Prop :=
  n > 0

def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1  -- n > 0
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)  -- 1 < p, so 2 ≤ p
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1

@[reducible, simp]
def nthUglyNumber_postcond (n : Nat) (result: Nat) (h_precond : nthUglyNumber_precond (n)) : Prop :=
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1
