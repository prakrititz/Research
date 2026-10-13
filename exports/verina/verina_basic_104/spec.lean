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

structure Map (K V : Type) [BEq K] [BEq V] where
  entries : List (K × V)
deriving Inhabited

instance  (K V : Type) [BEq K] [BEq V] : BEq (Map K V) where
  beq m1 m2 := List.length m1.entries = List.length m2.entries ∧ List.beq m1.entries m2.entries

def empty {K V : Type} [BEq K] [BEq V] : Map K V := ⟨[]⟩

def insert {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) (v : V) : Map K V :=
  let entries := m.entries.filter (fun p => ¬(p.1 == k)) ++ [(k, v)]
  ⟨entries⟩

@[reducible, simp]
def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  -- Both maps must have unique keys
  List.Nodup (m1.entries.map Prod.fst) ∧ List.Nodup (m2.entries.map Prod.fst)

def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)

@[reducible, simp]
def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Prop :=
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )
