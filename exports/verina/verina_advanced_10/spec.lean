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

def removePrimeFactor (n : Nat) (p : Nat) : Nat :=
  if h : p > 1 ∧ n > 0 then
    if n % p = 0 then
      have : n / p < n := Nat.div_lt_self h.2 h.1
      removePrimeFactor (n / p) p
    else n
  else n
termination_by n

def removeAllPrimeFactors (n : Nat) (primes : List Nat) : Nat :=
  primes.foldl removePrimeFactor n

@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
  primes.length > 0 ∧
  primes.all (fun p => Nat.Prime p) ∧
  List.Nodup primes ∧
  removeAllPrimeFactors n primes = 1

@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))
