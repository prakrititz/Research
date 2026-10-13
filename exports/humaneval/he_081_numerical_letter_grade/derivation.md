# Derivation of he_081_numerical_letter_grade

kind: **loop**

- **loop** over state (i : Nat, acc : List String), start (0, [])
  - invariant: `i ≤ grades.length ∧ acc = (List.range i).map (fun k => letterGrade grades[k]!)`
  - guard: `i < grades.length`
  - variant: `grades.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [letterGrade grades[i]!])`
