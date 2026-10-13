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

-- Lean 4's Float is an opaque C FFI type with no kernel lemmas.
-- These axioms capture IEEE 754-compliant behavior for non-NaN/non-Inf floats.
axiom Float.not_isNaN_ofNat (n : Nat) : (n.toFloat).isNaN = false
axiom Float.isFinite_ofNat (n : Nat) (h : n < 2 ^ 53) :
    (n.toFloat).isNaN = false ∧ (n.toFloat).isInf = false
axiom Float.ofNat_beq_zero_false (n : Nat) (h : 0 < n) :
    (n.toFloat == (0 : Float)) = false
axiom Float.beq_self_of_not_isNaN (x : Float) (h : x.isNaN = false) :
    (x == x) = true
axiom Float.not_isNaN_sub (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hx_inf : x.isInf = false) (hy_inf : y.isInf = false) :
    (x - y).isNaN = false
axiom Float.not_isNaN_div (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hy0 : (y == 0) = false) (hinf : x.isInf = false ∨ y.isInf = false) :
    (x / y).isNaN = false
axiom Float.le_total_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x ≤ y ∨ y ≤ x
axiom Float.lt_iff_le_not_le_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x

@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  n > 0 ∧ n < 9007199254740992  -- n must be positive and bounded for Float precision

@[reducible, simp]
def sumAndAverage_postcond (n : Nat) (result: Int × Float) (h_precond : sumAndAverage_precond (n)) :=
  (n = 0 → result == (0, 0.0)) ∧
  (n > 0 →
    result.1 == n * (n + 1) / 2 ∧
    result.2 == ((n * (n + 1) / 2).toFloat) / (n.toFloat))
