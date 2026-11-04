# applies the spec_small closer to Hammer.lean (run after the replay: the replay's Lean env is in use)
import sys
p = sys.argv[1]; s = open(p, encoding="utf-8").read()
anchor = "syntax (name := smallCasesTac) \"small_cases\" : tactic\n@[tactic smallCasesTac] def evalSmallCases : Tactic := fun _ => smallCases\n"
assert anchor in s
s = s.replace(anchor, anchor + '''
/-- Hypotheses `∀ k : ℕ, ...` instantiated at `0`, `1` and `2`, then arithmetic: the case that refutes a bad value is often a
small one (he_024's `∀ k, d < k ∧ k < n → n % k ≠ 0` at `k = 1` rules out `d = 0`, so `d - 1 < d`). -/
def specSmall : TacticM Unit := do
  nameInaccessibles
  let mut added := 0
  for (h, t) in ← namedLocals do
    let .forallE _ ty _ _ := t | continue
    unless ty.isConstOf ``Nat do continue
    for v in [0, 1, 2] do
      if ← tryTactic (runText s!"have := {h} {v}") then added := added + 1
  if added == 0 then throwError "spec_small: no hypothesis over all natural numbers"
  runText "first | omega | (simp_all; done) | (simp_all; omega)"

syntax (name := specSmallTac) "spec_small" : tactic
@[tactic specSmallTac] def evalSpecSmall : Tactic := fun _ => specSmall
''', 1)
old = '(400, "small_cases"),'
assert old in s
s = s.replace(old, old + ' (300, "spec_small"),', 1)
open(p, "w", encoding="utf-8").write(s)
