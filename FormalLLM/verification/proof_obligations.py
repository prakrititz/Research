from dataclasses import dataclass, field
from typing import List, Optional
from FormalLLM.lspec.ast import Expr, Param

@dataclass
class ProofObligation:
    assumptions: List[Expr]
    goal: Expr
    # Declared parameters of the originating specification. Laws hand these
    # through so the SMT backend can give names their declared sort instead of
    # defaulting every unbound name to Real.
    params: List[Param] = field(default_factory=list)
    #: What this obligation checks, in the law's own terms -- e.g.
    #: "the loop body must preserve the invariant and decrease the variant".
    #: Without it a rejection reaches the model as a bare counterexample and it
    #: cannot tell which of its choices was at fault.
    description: Optional[str] = None
    #: What the author of the failing step should change, in the law's own terms.
    #: One generic sentence ("strengthen the invariant") is right for some
    #: obligations and the opposite of right for others -- the set-up check needs a
    #: *weaker* invariant -- so each law says what applies to its own obligations.
    advice: Optional[str] = None
    #: The longest this obligation is worth waiting for, in milliseconds (advisory checks
    #: only). Z3 is incomplete on quantifiers and answers `unknown` only after its whole
    #: timeout, so a necessary-condition check over a quantified specification is given a
    #: short allowance: a quick answer is welcome, a slow one is not worth the search's time.
    budget_ms: Optional[int] = None
