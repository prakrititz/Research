# Derivation of he_017_parse_music

kind: **loop**

- **bind** `notes : List String` with property `notes = (if music_string = "" then [] else music_string.splitOn " ")`
  - _value_:
    - **term**: `if music_string = "" then [] else music_string.splitOn " "`
  - _continuation_:
    - **loop** over state (i : Nat, acc : List Nat), start (0, [])
      - invariant: `i ≤ notes.length ∧ acc = (notes.take i).map (fun n => if n = "o" then 4 else if n = "o|" then 2 else 1)`
      - guard: `i < notes.length`
      - variant: `notes.length - i`
      - result: `acc`
      - **term**: `(i + 1, acc ++ [if notes[i]! = "o" then 4 else if notes[i]! = "o|" then 2 else 1])`
