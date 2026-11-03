"""Refinement laws for Lean: a goal becomes Lean obligations and smaller goals, and a finished tree becomes a Lean term.

A *goal* asks for a value of type ``ret`` that satisfies ``post`` (a Lean proposition in which ``⟪r⟫`` stands for the
value) in a context of variables and hypotheses. In Lean that is the subtype ``{ ρ : ret // post[ρ] }``. A law solves a
goal either outright (``term``) or by pointing at smaller goals (``cases``, ``bind``, ``loop``); the Lean term for the
whole tree is built from the sub-terms, so the Lean kernel checks the entire derivation and the result is a program
together with a proof that it meets the specification (the paper's "correct by construction", with Lean as the judge).

    law          paper's law              what it asks Lean for
    term         assignment / skip        ``hyps → post[E]``
    cases        alternation              nothing (``if`` is total); the condition must be decidable
    bind         sequential composition   nothing; the intermediate property is the post of the first sub-goal
    loop         iteration                invariant holds initially, and on exit implies the post; the body is a
                                          sub-goal that must keep the invariant and strictly decrease a ℕ variant

Substitution is done by Lean, not by this module: a property of "the new state" is a ``fun`` applied to the hole, and
the obligation text keeps the redex (the tactic cascade begins with ``dsimp only``, which reduces it).
"""
import re
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

HOLE = "⟪r⟫"
RESULT = "ρ"

Binder = Tuple[str, str]


class IllFormed(ValueError):
    """The step cannot even be stated (a name is already used, a field is empty)."""


@dataclass(frozen=True)
class Goal:
    id: int
    ctx: Tuple[Binder, ...]
    hyps: Tuple[Binder, ...]
    ret: str
    post: str

    def binders(self, ctx: Tuple[Binder, ...] = (), hyps: Tuple[Binder, ...] = ()) -> str:
        parts = [f"({n} : {t})" for n, t in self.ctx + tuple(ctx)]
        parts += [f"({n} : {p})" for n, p in self.hyps + tuple(hyps)]
        return " ".join(parts)

    @property
    def names(self) -> List[str]:
        return [n for n, _ in self.ctx]

    @property
    def spec_type(self) -> str:
        return "{ %s : %s // %s }" % (RESULT, self.ret, self.post.replace(HOLE, RESULT))

    def post_with(self, expression: str) -> str:
        return self.post.replace(HOLE, f"({expression})")

    def call(self) -> str:
        """The arguments that bring this goal's context into scope: ``a h_precond``."""
        return " ".join([n for n, _ in self.ctx] + [n for n, _ in self.hyps])


def with_bound(tactic: str, bound: Optional[Tuple[str, str]]) -> str:
    """On exit from a loop whose guard is ``v < e`` the invariant (``v ≤ e``) and the negated guard give ``v = e``; try the
    cascade after substituting it, then without (substituting is what lets ``simp`` see that ``∀ k < v`` is ``∀ k < e``)."""
    if bound is None:
        return tactic
    var, expr = bound
    return f"first | (have hEq : {var} = ({expr}) := (by omega); subst hEq; {tactic}) | ({tactic})"


@dataclass(frozen=True)
class Obligation:
    """A statement Lean must accept. With ``body`` it is checked by elaboration (``example … : statement := body``);
    without, it is a theorem proved by the tactic cascade."""
    kind: str
    description: str
    binders: str
    statement: str
    body: Optional[str] = None
    bound: Optional[Tuple[str, str]] = None              # (variable, bound) for a loop exit, see ``with_bound``

    def source(self, name: str, tactic: str) -> str:
        if self.body is not None:
            return f"example {self.binders} : {self.statement} := {self.body}\n"
        return (f"set_option maxHeartbeats 200000 in\ntheorem {name} {self.binders} :\n    {self.statement} := by\n"
                f"  {with_bound(tactic, self.bound)}\n")


@dataclass
class Expansion:
    obligations: List[Obligation] = field(default_factory=list)
    subgoals: List[Goal] = field(default_factory=list)


@dataclass
class Rendered:
    term: str
    aux: List[str] = field(default_factory=list)           # top-level definitions the term uses (loops), dependencies first


NewId = Callable[[], int]


def _require(value: str, what: str):
    if not str(value).strip():
        raise IllFormed(f"{what} is empty")


def _fresh_names(goal: Goal, names: List[str]):
    clash = [n for n in names if n in goal.names]
    if clash:
        raise IllFormed(f"the name {clash[0]} is already a variable of the goal ({', '.join(goal.names)}); choose another")
    if len(set(names)) != len(names):
        raise IllFormed("a name is used twice")


class Law:
    kind = ""

    def expand(self, goal: Goal, new_id: NewId) -> Expansion:
        raise NotImplementedError

    def render(self, goal: Goal, children: List[Goal], parts: List[Rendered], tactic: str) -> Rendered:
        raise NotImplementedError

    def to_json(self) -> dict:
        raise NotImplementedError


@dataclass(frozen=True)
class Term(Law):
    """Solve the goal with the Lean expression ``expr`` (the paper's assignment and skip)."""
    expr: str
    kind = "term"

    def expand(self, goal, new_id):
        _require(self.expr, "the expression")
        return Expansion([Obligation("term", "the value satisfies the postcondition under the hypotheses",
                                     goal.binders(), goal.post_with(self.expr))])

    def render(self, goal, children, parts, tactic):
        return Rendered(f"⟨({self.expr}), by {tactic}⟩")

    def to_json(self):
        return {"law": "term", "expr": self.expr}


@dataclass(frozen=True)
class Cases(Law):
    """``if cond then (goal 1) else (goal 2)``: the paper's alternation. The two sub-goals learn ``cond`` and ``¬ cond``."""
    cond: str
    kind = "cases"

    def expand(self, goal, new_id):
        _require(self.cond, "the condition")
        hyp = f"h{goal.id}"
        decidable = Obligation("wellformed", "the condition is a decidable proposition (it can run)",
                               goal.binders(), f"Decidable ({self.cond})", body="inferInstance")
        yes = Goal(new_id(), goal.ctx, goal.hyps + ((hyp, f"({self.cond})"),), goal.ret, goal.post)
        no = Goal(new_id(), goal.ctx, goal.hyps + ((hyp, f"¬ ({self.cond})"),), goal.ret, goal.post)
        return Expansion([decidable], [yes, no])

    def render(self, goal, children, parts, tactic):
        return Rendered(f"(if h{goal.id} : ({self.cond}) then {parts[0].term} else {parts[1].term})",
                        parts[0].aux + parts[1].aux)

    def to_json(self):
        return {"law": "cases", "cond": self.cond}


@dataclass(frozen=True)
class Bind(Law):
    """Introduce ``var : type`` with the property ``prop``: first find such a value, then continue with it.

    The paper's sequential composition with an intermediate assertion. ``prop`` mentions ``var``."""
    var: str
    type: str
    prop: str
    kind = "bind"

    def expand(self, goal, new_id):
        for value, what in ((self.var, "the variable"), (self.type, "the type"), (self.prop, "the property")):
            _require(value, what)
        _fresh_names(goal, [self.var])
        wellformed = Obligation("wellformed", "the intermediate property is a proposition",
                                goal.binders(ctx=((self.var, self.type),)), "Prop", body=f"({self.prop})")
        first = Goal(new_id(), goal.ctx, goal.hyps, self.type, f"(fun ({self.var} : {self.type}) => {self.prop}) {HOLE}")
        second = Goal(new_id(), goal.ctx + ((self.var, self.type),), goal.hyps + ((f"h{goal.id}", f"({self.prop})"),),
                      goal.ret, goal.post)
        return Expansion([wellformed], [first, second])

    def render(self, goal, children, parts, tactic):
        return Rendered(f"(match ({parts[0].term} : {{ {self.var} : {self.type} // {self.prop} }}) with "
                        f"| ⟨{self.var}, h{goal.id}⟩ => {parts[1].term})", parts[0].aux + parts[1].aux)

    def to_json(self):
        return {"law": "bind", "var": self.var, "type": self.type, "prop": self.prop}


@dataclass(frozen=True)
class Loop(Law):
    """A loop over ``state``: start at ``init``, keep ``invariant``, run while ``guard``, return ``result``.

    The body is the sub-goal "find the next state"; it must keep the invariant and strictly decrease ``variant`` (a
    natural number, so it cannot decrease for ever: termination is by well-founded recursion on it)."""
    state: Tuple[Binder, ...]
    init: Tuple[str, ...]
    invariant: str
    guard: str
    variant: str
    result: str
    kind = "loop"

    # --- helpers --------------------------------------------------------------------------------------------------

    def _lam(self, body: str) -> str:
        return "(fun " + " ".join(f"({n} : {t})" for n, t in self.state) + f" => {body})"

    def _args(self, value: str) -> str:
        """The components of a state value ``value`` as separate arguments: ``(v).1 (v).2`` (nested pairs for 3+)."""
        count = len(self.state)
        if count == 1:
            return f"({value})"
        out, rest = [], f"({value})"
        for k in range(count):
            if k == count - 1:
                out.append(rest)
            else:
                out.append(f"{rest}.1")
                rest = f"{rest}.2"
        return " ".join(out)

    @property
    def state_type(self) -> str:
        return " × ".join(f"({t})" if " " in t else t for _, t in self.state)

    def _exit_bound(self) -> Optional[Tuple[str, str]]:
        """``(v, e)`` when the guard is ``v < e`` for a state variable ``v`` that ``e`` does not mention."""
        found = re.fullmatch(r"\s*\(?\s*([A-Za-z_][\w']*)\s*<\s*(.+?)\s*\)?\s*", self.guard)
        if not found:
            return None
        var, expr = found.group(1), found.group(2)
        if var not in [n for n, _ in self.state] or re.search(rf"(?<![\w']){re.escape(var)}(?![\w'])", expr):
            return None
        return var, expr

    def _pattern(self, names: List[str]) -> str:
        return names[0] if len(names) == 1 else "(" + ", ".join(names) + ")"

    # --- the law --------------------------------------------------------------------------------------------------

    def expand(self, goal, new_id):
        if not self.state:
            raise IllFormed("a loop needs at least one state variable")
        if len(self.init) != len(self.state):
            raise IllFormed(f"{len(self.state)} state variables but {len(self.init)} initial values")
        for value, what in ((self.invariant, "the invariant"), (self.guard, "the guard"), (self.variant, "the variant"),
                            (self.result, "the result")):
            _require(value, what)
        _fresh_names(goal, [n for n, _ in self.state])
        names = [n for n, _ in self.state]
        hyp_inv, hyp_guard = f"h{goal.id}i", f"h{goal.id}g"
        inside = tuple(self.state)
        wellformed = [
            Obligation("wellformed", "the guard is decidable (the loop can run)", goal.binders(ctx=inside),
                       f"Decidable ({self.guard})", body="inferInstance"),
            Obligation("wellformed", "the variant is a natural number", goal.binders(ctx=inside), "Nat",
                       body=f"({self.variant})"),
        ]
        init = Obligation("init", "the invariant holds before the first iteration", goal.binders(),
                          f"{self._lam(self.invariant)} " + " ".join(f"({e})" for e in self.init))
        exit_ = Obligation("exit", "on exit the invariant and the negated guard imply the postcondition",
                           goal.binders(ctx=inside, hyps=((hyp_inv, f"({self.invariant})"),
                                                          (hyp_guard, f"¬ ({self.guard})"))),
                           goal.post_with(self.result), bound=self._exit_bound())
        body_post =(f"{self._lam(self.invariant)} {self._args(HOLE)} ∧ "
                     f"{self._lam(self.variant)} {self._args(HOLE)} < ({self.variant})")
        body = Goal(new_id(), goal.ctx + inside, goal.hyps + ((hyp_inv, f"({self.invariant})"), (hyp_guard, f"({self.guard})")),
                    self.state_type, body_post)
        return Expansion(wellformed + [init, exit_], [body])

    def render(self, goal, children, parts, tactic):
        body_goal = children[0]
        name = f"loop{goal.id}"
        # the definition takes the goal's context and hypotheses first (as ``goal.call()`` passes them), then the state
        state_binders = " ".join(f"({n} : {t})" for n, t in self.state)
        binders = f"{goal.binders()} {state_binders} (h{goal.id}i : ({self.invariant}))"
        names = [n for n, _ in self.state]
        primed = [f"{n}'" for n in names]
        call_next = f"{name} {goal.call()} {' '.join(primed)} h{goal.id}b.1"
        definition = (
            f"def {name} {binders} : {goal.spec_type} :=\n"
            f"  if h{goal.id}g : ({self.guard}) then\n"
            f"    match ({parts[0].term} : {body_goal.spec_type}) with\n"
            f"    | ⟨{self._pattern(primed)}, h{goal.id}b⟩ => {call_next}\n"
            f"  else ⟨({self.result}), by {with_bound(tactic, self._exit_bound())}⟩\n"
            f"termination_by {self.variant}\n"
            f"decreasing_by\n"
            f"  all_goals (try simp_wf)\n"
            f"  all_goals (first | exact h{goal.id}b.2 | omega)\n")
        start = f"{name} {goal.call()} " + " ".join(f"({e})" for e in self.init) + f" (by {tactic})"
        return Rendered(f"({start})", parts[0].aux + [definition])

    def to_json(self):
        return {"law": "loop", "state": [list(b) for b in self.state], "init": list(self.init),
                "invariant": self.invariant, "guard": self.guard, "variant": self.variant, "result": self.result}


def law_from_json(data: dict) -> Law:
    kind = data.get("law")
    try:
        if kind == "term":
            return Term(str(data["expr"]))
        if kind == "cases":
            return Cases(str(data["cond"]))
        if kind == "bind":
            return Bind(str(data["var"]), str(data["type"]), str(data["prop"]))
        if kind == "loop":
            return Loop(tuple((str(n), str(t)) for n, t in data["state"]), tuple(str(e) for e in data["init"]),
                        str(data["invariant"]), str(data["guard"]), str(data["variant"]), str(data["result"]))
    except KeyError as missing:
        raise IllFormed(f"the {kind} law needs the field {missing}")
    raise IllFormed(f"unknown law {kind!r}; the laws are term, cases, bind, loop")
