# Derivation of he_044_change_base

kind: **restate**

- **term**: `String.mk (Nat.toDigits base x)`
  - helper lemma `digit_val`: `∀ (d : Nat), d < 10 → (Nat.digitChar d).isDigit = true ∧ (Nat.digitChar d).toNat - '0'.toNat = d`
  - helper lemma `toDigits_single`: `∀ (b d : Nat), 1 < b → d < b → Nat.toDigits b d = [Nat.digitChar d]`
  - helper lemma `core_ne_nil`: `∀ (b fuel n : Nat) (acc : List Char), Nat.toDigitsCore b (fuel + 1) n acc ≠ []`
  - helper lemma `toDigits_ne_nil`: `∀ (b n : Nat), Nat.toDigits b n ≠ []`
  - helper lemma `change_base_ok`: `∀ (base v : Nat), 2 ≤ base → base < 10 → ((String.mk (Nat.toDigits base v)).toList.all (fun c => c.isDigit && c.toNat - '0'.toNat < base) = true ∧ (String.mk (Nat.toDigits base v)).toList.foldl (fun acc c => acc * base + (c.toNat - '0'.toNat)) 0 = v ∧ (v = 0 → String.mk (Nat.toDigits base v) = "0") ∧ (v > 0 → (String.mk (Nat.toDigits base v)).toList.head! ≠ '0'))`
