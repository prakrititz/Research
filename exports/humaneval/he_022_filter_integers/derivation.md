# Derivation of he_022_filter_integers

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ values.length ∧ acc = (values.take i).filterMap (fun v => match v with | PyVal.int n => some n | _ => none)`
  - guard: `i < values.length`
  - variant: `values.length - i`
  - result: `acc`
  - helper lemma `pyval_take_succ`: `∀ (l : List PyVal) (i : Nat), l.take (i + 1) = l.take i ++ l[i]?.toList`
  - **term**: `(i + 1, match values[i]? with | some (PyVal.int n) => acc ++ [n] | _ => acc)`
