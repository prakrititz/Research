example (numbers : List Int) (P : Int → Prop) (h : P (numbers[0]?.getD 0)) : P numbers[0]! := by
  simp? at *
  exact h

example (a : Array Int) (i : Nat) (P : Int → Prop) (h : P (a[i]?.getD 0)) : P a[i]! := by
  simp? at *
  exact h
