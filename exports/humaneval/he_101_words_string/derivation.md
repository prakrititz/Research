# Derivation of he_101_words_string

kind: **restate**

- **term**: `((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")`
