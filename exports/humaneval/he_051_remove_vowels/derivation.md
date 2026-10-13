# Derivation of he_051_remove_vowels

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ text.length ∧ acc = (text.toList.take i).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))`
  - guard: `i < text.length`
  - variant: `text.length - i`
  - result: `String.mk acc`
  - helper lemma `vowel_step`: `∀ (text : String) (i : Nat) (acc : List Char), i < text.length → acc = (text.toList.take i).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)) → (if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains text.toList[i]! then acc else acc ++ [text.toList[i]!]) = (text.toList.take (i + 1)).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))`
  - **term**: `(i + 1, if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains text.toList[i]! then acc else acc ++ [text.toList[i]!])`
