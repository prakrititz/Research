# Derivation of verina_advanced_10

kind: **restate**

- **term**: `(primes.map (fun p => (p, padicValNat p n)))`
  - helper lemma `rpf_eq`: `∀ (p : Nat), p.Prime → ∀ (n : Nat), 0 < n → removePrimeFactor n p = n / p ^ (padicValNat p n)`
  - helper lemma `rpf_dvd`: `∀ (p : Nat), p.Prime → ∀ (n : Nat), 0 < n → p ^ padicValNat p n * removePrimeFactor n p = n`
  - helper lemma `fold_mul`: `∀ (l : List (Nat × Nat)) (a : Nat), l.foldl (fun acc (x : Nat × Nat) => acc * x.1 ^ x.2) a = a * l.foldl (fun acc (x : Nat × Nat) => acc * x.1 ^ x.2) 1`
  - helper lemma `fe_main`: `∀ (ps : List Nat) (n : Nat), 0 < n → (∀ p ∈ ps, p.Prime) → ps.Nodup → ps.foldl removePrimeFactor n = 1 → n = (ps.map (fun p => (p, padicValNat p n))).foldl (fun acc (x : Nat × Nat) => acc * x.1 ^ x.2) 1`
  - helper lemma `exps10`: `∀ (n : Nat) (primes : List Nat) (h : findExponents_precond n primes), findExponents_postcond n primes (primes.map (fun p => (p, padicValNat p n))) h`
