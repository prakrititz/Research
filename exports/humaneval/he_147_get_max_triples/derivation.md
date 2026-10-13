# Derivation of he_147_get_max_triples

kind: **restate**

- **term**: `((List.range n).map (fun i => ((List.range n).map (fun j => ((List.range n).filter (fun k => i < j ∧ j < k ∧ (seqA (i + 1) + seqA (j + 1) + seqA (k + 1)) % 3 = 0)).length)).sum)).sum`
