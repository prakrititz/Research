import LeanEnv.Hammer
def greatestCommonDivisor_precond (a : Nat) (b : Nat) : Prop := a > 0 ∧ b > 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#eval show IO Unit from do
  let found : Option String := Id.run do
    for a in ([0, 1, 2, 3] : List (ℕ)) do
      for b in ([0, 1, 2, 3] : List (ℕ)) do
        if h_precond : (greatestCommonDivisor_precond a b) then
          if !(decide ((a > 0) ∧ (∀ d, d < 4 → (d > 0 → (a % d = 0 ∧ b % d = 0) ↔ (a % d = 0 ∧ b % d = 0))))) then
            return some ("a := " ++ toString (repr a) ++ ", " ++ "b := " ++ toString (repr b))
    return none
  IO.println ("SMALLSCOPE: " ++ found.getD "none")
