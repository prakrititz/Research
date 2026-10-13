# Derivation of verina_advanced_66

kind: **restate**

- **term**: `String.intercalate " " (((words_str.splitOn " ").filter (fun w => w ≠ "")).reverse)`
  - helper lemma `rev66`: `∀ (words_str : String) (h : reverseWords_precond words_str), reverseWords_postcond words_str (String.intercalate " " (((words_str.splitOn " ").filter (fun w => w ≠ "")).reverse)) h`
