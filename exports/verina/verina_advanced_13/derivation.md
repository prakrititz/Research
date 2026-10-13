# Derivation of verina_advanced_13

kind: **restate**

- **term**: `(let sortedChords := chords.map (fun chord => let a := chord[0]!; let b := chord[1]!; if a > b then [b, a] else [a, b]); sortedChords.any (fun x => sortedChords.any (fun y => hasChordIntersection_postcond.hasIntersection x y)))`
  - helper lemma `has_symm13`: `∀ (x y : List Nat), hasChordIntersection_postcond.hasIntersection x y = hasChordIntersection_postcond.hasIntersection y x`
  - helper lemma `has_irr13`: `∀ (x : List Nat), hasChordIntersection_postcond.hasIntersection x x = false`
  - helper lemma `chord13`: `∀ (N : Nat) (chords : List (List Nat)) (h : hasChordIntersection_precond N chords), hasChordIntersection_postcond N chords (let sortedChords := chords.map (fun chord => let a := chord[0]!; let b := chord[1]!; if a > b then [b, a] else [a, b]); sortedChords.any (fun x => sortedChords.any (fun y => hasChordIntersection_postcond.hasIntersection x y))) h`
