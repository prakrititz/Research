# Derivation of he_152_compare

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ game.length ∧ acc.length = i ∧ ∀ k, k < i → acc[k]! = ((game[k]! - guess[k]!).natAbs : Int)`
  - guard: `i < game.length`
  - variant: `game.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [((game[i]! - guess[i]!).natAbs : Int)])`
