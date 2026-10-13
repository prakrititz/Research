# Derivation of he_117_select_words

kind: **restate**

- **term**: `(s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains ch))).length == n)`
