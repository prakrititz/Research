# Derivation of verina_advanced_11

kind: **restate**

- **term**: `(lst.find? (fun x => decide ((lst.filter (fun y => y = x)).length > lst.length / 2))).getD (-1)`
  - helper lemma `maj11`: `∀ (lst : List Int) (h : findMajorityElement_precond lst) (res : Int), (((∀ x, x ∈ lst → (lst.filter (fun y => y = x)).length ≤ lst.length / 2) ∧ res = -1) ∨ (lst.filter (fun y => y = res)).length > lst.length / 2) → findMajorityElement_postcond lst res h`
  - helper lemma `find11`: `∀ (lst : List Int) (h : findMajorityElement_precond lst), findMajorityElement_postcond lst ((lst.find? (fun x => decide ((lst.filter (fun y => y = x)).length > lst.length / 2))).getD (-1)) h`
