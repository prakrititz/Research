# Derivation of verina_advanced_26

kind: **restate**

- **term**: `if digits.isEmpty then [] else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then [] else digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]`
  - helper lemma `lc26`: `∀ (digits : String) (h : letterCombinations_precond digits), letterCombinations_postcond digits (if digits.isEmpty then [] else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then [] else digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [""]) h`
