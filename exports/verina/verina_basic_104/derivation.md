# Derivation of verina_basic_104

kind: **restate**

- **term**: `(Map.mk (((m1.entries.filter (fun p => !(m2.entries.any (fun q => q.1 == p.1)))) ++ m2.entries).mergeSort (fun a b => decide (a.1 ≤ b.1))))`
  - helper lemma `find_key`: `∀ (l : List (Int × Int)), (l.map Prod.fst).Nodup → ∀ (p : Int × Int), p ∈ l → l.find? (fun q => q.1 == p.1) = some p`
  - helper lemma `upd104`: `∀ (m1 m2 : Map Int Int) (h : update_map_precond m1 m2), update_map_postcond m1 m2 (Map.mk (((m1.entries.filter (fun p => !(m2.entries.any (fun q => q.1 == p.1)))) ++ m2.entries).mergeSort (fun a b => decide (a.1 ≤ b.1)))) h`
