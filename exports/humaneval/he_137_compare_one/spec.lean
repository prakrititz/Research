import Mathlib

def parseQ (s : String) : ℚ :=
  match (s.map (fun c => if c == ',' then '.' else c)).splitOn "." with
  | [w] => (w.toNat! : ℚ)
  | [w, f] => (w.toNat! : ℚ) + (f.toNat! : ℚ) / ((10 : ℚ) ^ f.length)
  | _ => 0
def valQ : ℚ ⊕ String → ℚ
  | Sum.inl q => q
  | Sum.inr s => parseQ s

@[reducible, simp]
def compareOne_precond (a : ℚ ⊕ String) (b : ℚ ⊕ String) : Prop :=
  True

@[reducible, simp]
def compareOne_postcond (a : ℚ ⊕ String) (b : ℚ ⊕ String) (result: Option (ℚ ⊕ String)) (h_precond : compareOne_precond (a) (b)) :=
  (valQ a = valQ b → result = none) ∧ (valQ b < valQ a → result = some a) ∧ (valQ a < valQ b → result = some b)
