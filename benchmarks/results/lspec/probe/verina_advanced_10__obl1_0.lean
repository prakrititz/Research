/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
n : ℕ
primes : List ℕ
h_precond : findExponents_precond n primes
⊢ n =
    List.foldl
      (fun acc x =>
        match x with
        | (p, e) => acc * p ^ e)
      1 (List.map (fun p => (p, padicValNat p n)) primes)
-/
theorem probe (n : Nat) (primes : List Nat) (h_precond : findExponents_precond n primes) :
    findExponents_postcond n primes (primes.map (fun p => (p, padicValNat p n))) h_precond := by
  sorry
