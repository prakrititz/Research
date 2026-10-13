# Derivation of he_092_any_int

kind: **restate**

- **term**: `(fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z)`
  - helper lemma `anyint_post`: `∀ (x y z : PyVal) (h : anyInt_precond x y z), anyInt_postcond x y z ((fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z)) h`
