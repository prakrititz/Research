"""A small, general leaf solver: close sub-goals the prover can settle with one line.

Why this exists
---------------
In a refinement tree most nodes are not creative. After a loop is introduced
correctly, the set-up node is ``x := 0`` and the body is ``x := x + e``. Asking a
language model to rediscover those, one two-call round trip each, is where runs
go wrong: on the paper's square-root example a model that had just chosen the
right loop was asked to refine its set-up node and answered with *another loop*,
and the budget was gone before the body was reached.

The creative decisions -- which law, which invariant, guard and variant -- stay
with the model. This module only tries a fixed family of short assignments built
from the specification's own names (plus an expression read off an equation of the
postcondition, ``r := n - q * d``), ``skip``, and two such assignments in a row for
a set-up or a loop body that changes two variables. Every assignment goes through
exactly the same engine, laws and prover as a model's proposal, so nothing it
accepts is any less verified; it just costs no LLM call.

It is **off by default** (the paper's pipeline has no such step) and is reported
as a separate arm in every study, so its effect can be read off rather than assumed.
"""

import copy
import re
import time
from typing import Dict, List, Optional, Tuple

from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import ASTNode, BinaryOp, Const, Definition, Number, UnaryOp, Variable
from FormalLLM.lspec.substitution import get_free_vars, substitute
from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm import spec_render as sr
from FormalLLM.refinement.engine import RefinementEngine, VerificationError, VerificationUnknown
from FormalLLM.refinement.frame import (derive, frame_names, join_conjunction, obligation_params,
                                        split_conjunction)
from FormalLLM.verification.proof_obligations import ProofObligation
from FormalLLM.verification.backends import Z3Backend
from FormalLLM.verification.z3_backend import VerificationResult, check_implication


def _names(spec) -> List[str]:
    """Names usable in a candidate: the spec's own variables and constants.

    The loop laws' bookkeeping constants (V0, V1 ...) and previous-state twins
    are not useful operands for a one-line program, so they are left out.
    """
    found = set()

    def visit(node):
        if isinstance(node, (Variable, Const)):
            found.add(node.name)
        for child in walk.children(node):
            visit(child)

    visit(spec.precondition.expr)
    visit(spec.postcondition.expr)
    found |= {p.name for p in list(spec.precondition.params) + list(spec.postcondition.params)}
    found |= frame_names(spec.frame)
    return sorted(n for n in found if not sr._VARIANT_NAME.match(n))


def spec_subterm_updates(spec, variable: str) -> List[str]:
    """Sums and differences of two atoms that the specification itself writes, and that mention ``variable``.

    A postcondition such as ``N < (x + e) * (x + e)`` already contains the update
    the author had in mind (``x + e``); trying the specification's own subterms
    first is both cheap and the most likely to be right.
    """
    found: List[str] = []

    def atom(node) -> bool:
        return isinstance(node, (Variable, Const, Number))

    def visit(node):
        if (isinstance(node, BinaryOp) and node.op in ("+", "-") and atom(node.left) and atom(node.right)
                and variable in {getattr(node.left, "name", None), getattr(node.right, "name", None)}):
            text = sr.render_expr(node)
            if text not in found and not sr._VARIANT_NAME.search(text):
                found.append(text)
        for child in walk.children(node):
            visit(child)

    visit(spec.precondition.expr)
    visit(spec.postcondition.expr)
    return found


def _occurrences(node, name: str) -> int:
    """How many times the variable ``name`` occurs in ``node``."""
    own = 1 if isinstance(node, (Variable, Const)) and node.name == name else 0
    return own + sum(_occurrences(child, name) for child in walk.children(node))


def _isolate(node, name: str, other):
    """The expression for ``name`` when ``node = other``, where ``name`` occurs once in ``node``.

    Undoes ``+``, ``-`` and negation only. A product (``q * d`` solved for ``q``) or anything
    else returns ``None``: dividing is not a step this solver takes on trust.
    """
    if isinstance(node, (Variable, Const)) and node.name == name:
        return other
    if isinstance(node, UnaryOp) and node.op == "-":
        return _isolate(node.expr, name, UnaryOp("-", other))
    if isinstance(node, BinaryOp) and node.op in ("+", "-"):
        in_left = _occurrences(node.left, name) == 1
        if node.op == "+":
            if in_left:
                return _isolate(node.left, name, BinaryOp(other, "-", node.right))
            return _isolate(node.right, name, BinaryOp(other, "-", node.left))
        if in_left:
            return _isolate(node.left, name, BinaryOp(other, "+", node.right))
        return _isolate(node.right, name, BinaryOp(node.left, "-", other))
    return None


def solved_for(spec, variable: str) -> List[str]:
    """Expressions for ``variable`` read off an equation of the postcondition, simplest first.

    ``q * d + r = n`` solved for ``r`` is ``n - q * d``. The short families in
    :func:`candidate_expressions` never contain an expression with three names in it, which is
    exactly the shape of the second half of a division set-up (``r := n - q * d``); measured on
    integer division, a model that had chosen the right loop could not get past that step.
    Only an equation in which ``variable`` occurs once, on one side, is used.
    """
    found: List[str] = []
    for conjunct in split_conjunction(spec.postcondition.expr):
        if not (isinstance(conjunct, BinaryOp) and conjunct.op == "="):
            continue
        for mine, rest in ((conjunct.left, conjunct.right), (conjunct.right, conjunct.left)):
            if _occurrences(mine, variable) == 1 and _occurrences(rest, variable) == 0:
                expr = _isolate(mine, variable, rest)
                if expr is None:
                    continue
                text = sr.render_expr(expr)
                if text not in found and not sr._VARIANT_NAME.search(text):
                    found.append(text)
    return found


def _array_names(spec) -> List[str]:
    from FormalLLM.lspec.ast import ArrayType
    params = list(spec.precondition.params) + list(spec.postcondition.params)
    return sorted({p.name for p in params if isinstance(p.type_, ArrayType)})


def _array_reads(spec, kinds) -> List[str]:
    """``a[v]`` for every array of the specification and every whole-number name ``v`` (and ``a[0]``)."""
    arrays = _array_names(spec)
    indices = [n for n in _names(spec) if kinds.get(n) == "Z" and n not in arrays]
    return [f"{a}[{v}]" for a in arrays for v in ["0"] + indices]


def candidate_expressions(spec, variable: str, limit: int = 120) -> List[str]:
    """Short expressions for ``variable := E``, simplest first, from the spec's own names.

    A Boolean variable gets ``true``, ``false``, the other Boolean names and any test an equation of
    the postcondition gives it (``t = (a < b)``): a number is not a truth value (the engine refuses
    ``b := 0``). A numeric variable also gets reads of the specification's arrays at its whole-number
    names (``m := l[i]``), the usual body of a scan.
    """
    from FormalLLM.lpl.typed_python import declared_kinds
    kinds = declared_kinds(spec)
    others = [n for n in _names(spec) if n != variable]
    if kinds.get(variable) == "B":
        truth = ["true", "false"] + [n for n in others if kinds.get(n) == "B"]
        try:
            truth += [text for text in solved_for(spec, variable) if text not in truth]
        except Exception:                         # an optional helper must never end a trial
            pass
        return truth[:limit]
    arrays = set(_array_names(spec))
    numeric = [n for n in others if kinds.get(n) != "B" and n not in arrays]
    out: List[str] = ["0", "1"]
    out += spec_subterm_updates(spec, variable)
    out += numeric
    out += [f"{variable} + 1", f"{variable} - 1"]
    out += [f"{variable} + {a}" for a in numeric]
    out += [f"{variable} - {a}" for a in numeric]
    out += [f"{a} + 1" for a in numeric] + [f"{a} - 1" for a in numeric]
    out += _array_reads(spec, kinds)
    others = numeric
    try:
        out += solved_for(spec, variable)         # after the short families, so the plainer program wins
    except Exception:                             # an optional helper must never end a trial
        pass
    for i, a in enumerate(others):
        for b in others[i + 1:]:
            out += [f"{a} + {b}", f"{a} - {b}", f"{b} - {a}", f"{a} * {b}", f"({a} + {b}) / 2"]
    out += [f"({variable} + {a}) / 2" for a in others]
    out += [f"2 * {a}" for a in others] + [f"2 * {variable}"]
    seen, unique = set(), []
    for text in out:
        if text not in seen:
            seen.add(text)
            unique.append(text)
    return unique[:limit]


def candidate_facts(spec, variable: str, limit: int = 40) -> List[str]:
    """Simple facts a precondition might be missing, about the frame variables, simplest first.

    Signs (``x >= 0``) before bounds against another name (``x <= N``), the variable
    being assigned before the other frame variables. Facts about constants alone are
    left out on purpose: a step cannot add a fact about a name the program never
    changes, only about the state it is building.
    """
    from FormalLLM.lpl.typed_python import declared_kinds
    kinds, arrays = declared_kinds(spec), set(_array_names(spec))
    # Only numbers can be compared with <=; truth values and whole arrays cannot.
    frame = sorted(v for v in frame_names(spec.frame) if kinds.get(v) != "B" and v not in arrays)
    names = [n for n in _names(spec) if kinds.get(n) != "B" and n not in arrays]
    if variable not in frame:
        return []
    order = [variable] + [v for v in frame if v != variable]
    out: List[str] = []
    for v in order:
        out += [f"{v} >= 0", f"{v} > 0", f"{v} <= 0"]
    for v in order:
        for other in names:
            if other != v:
                out += [f"{v} <= {other}", f"{v} >= {other}"]
    seen, unique = set(), []
    for text in out:
        if text not in seen:
            seen.add(text)
            unique.append(text)
    return unique[:limit]


class LeafSolver:
    """Tries ``skip`` and short assignments on a specification."""

    def __init__(self, engine: RefinementEngine, timeout_ms: int = 1500, max_candidates: int = 120,
                 pair_seconds: float = 20.0, pair_queries: int = 1000):
        self.engine = engine
        #: Candidates are screened with Z3 alone, whatever backend the run uses. Z3 answers in
        #: milliseconds; a fallback backend would send every "unknown" to a proof assistant (about
        #: ten seconds each, over hundreds of candidates). A candidate Z3 cannot decide is simply
        #: not taken here; the model's own proposals still get the full backend.
        self.screen = engine if isinstance(engine.backend, Z3Backend) else self._z3_view(engine)
        self.timeout_ms = timeout_ms
        self.max_candidates = max_candidates
        #: The two-assignment search (:meth:`solve_pair`) is limited by the number of prover queries,
        #: not by time: a time limit made the outcome depend on how busy the machine was (measured on
        #: integer division: the same replies solved the node in 2 LLM calls with a 4 s limit and
        #: exhausted all 30 calls when the limit was tightened to simulate a slower machine). The division
        #: body needs 221 queries (under a second); 1000 leaves a wide margin. The wall clock only
        #: remains as a safety net, far above the normal one or two seconds.
        self.pair_queries = pair_queries
        self.pair_seconds = pair_seconds
        #: After ``solve`` returned a split: how each part is finished, ``{role: (law, parameters)}``.
        self.plan: Optional[Dict[str, Tuple[str, Dict[str, object]]]] = None
        #: After a failed ``solve``: ``(law, parameters, message)`` of the most informative
        #: rejected candidate, or ``None``. "Informative" means an update of the variable
        #: in terms of itself (``x := x + e``) that the prover refuted with a counterexample:
        #: when even the obvious step fails, the cause is usually upstream.
        self.near_miss: Optional[Tuple[str, Dict[str, object], str]] = None
        #: After a failed ``solve``: a fact (``"x >= 0"``) which, added to the precondition,
        #: makes ``near_miss`` valid, or ``None``. The precondition of a sub-specification is
        #: whatever the step above it established, so this is the fact that step left out.
        self.missing_fact: Optional[str] = None

    @staticmethod
    def _z3_view(engine: RefinementEngine) -> RefinementEngine:
        """The same laws and checks as ``engine``, decided by Z3 only."""
        view = RefinementEngine(backend=Z3Backend(), check_feasibility=engine.check_feasibility)
        view.laws = dict(engine.laws)
        return view

    def missing_fact_for(self, spec, near_miss) -> Optional[str]:
        """The simplest fact whose addition to the precondition makes the refuted assignment valid.

        This is abduction over a small generic family (:func:`candidate_facts`), checked by
        the same prover. It answers the question the model could not: *which* assumption
        was missing when even the obvious step failed. Measured on the paper's square-root
        example: with an invariant that left out ``x >= 0`` the loop body ``x := x + e`` was
        refuted at ``x = -3``; the model, seeing only that, started nested loops instead of
        repairing the invariant, and the search ran out of budget. A fact is only returned if
        the strengthened precondition is still satisfiable, so it cannot succeed vacuously.
        """
        law, parameters, _message = near_miss
        variable = parameters.get("variable")
        if law != "assignment" or variable is None:
            return None
        pre = spec.precondition
        for text in candidate_facts(spec, variable):
            try:
                fact = parse_expr(text)
            except Exception:
                continue
            stronger = derive(
                spec,
                precondition=Definition(None, copy.deepcopy(pre.params),
                                        BinaryOp(copy.deepcopy(pre.expr), "/\\", fact)),
                postcondition=copy.deepcopy(spec.postcondition))
            try:
                self.screen.apply(stronger, law, parameters, timeout_ms=self.timeout_ms)
            except (VerificationError, ValueError):
                continue
            if self._satisfiable(stronger):
                return text
        return None

    def _follows(self, spec, goal) -> bool:
        """Does the precondition of ``spec`` imply ``goal``? (``False`` when the prover cannot tell.)"""
        obligation = ProofObligation(assumptions=[copy.deepcopy(spec.precondition.expr)],
                                     goal=copy.deepcopy(goal), params=obligation_params(spec))
        status, _ = check_implication(obligation, timeout_ms=self.timeout_ms)
        return status == VerificationResult.PROVED

    def _satisfiable(self, spec) -> bool:
        """Is there any state satisfying the precondition? (Not vacuous truth.)"""
        obligation = ProofObligation(assumptions=[copy.deepcopy(spec.precondition.expr)],
                                     goal=parse_expr("false"), params=obligation_params(spec))
        status, _ = check_implication(obligation, timeout_ms=self.timeout_ms)
        return status != VerificationResult.PROVED

    def solve_pair(self, spec) -> Optional[Tuple[str, Dict[str, object], object]]:
        """Two assignments to two different frame variables in a row: ``a := E1 ; b := E2``.

        A set-up such as ``q, r : [n >= 0 /\\ d > 0, q * d + r = n /\\ r >= 0]`` needs both
        variables set, so no single assignment closes it. Measured on integer division, the
        model asked next tends to answer with another loop, or with a middle assertion from
        which the second half cannot be finished, and the budget goes there.

        The search works backwards. The second assignment ``b := E2`` comes from the usual short
        candidates and from solving an equation of the postcondition (``r := n - q * d``). The
        middle assertion is the weakest precondition of that assignment, ``Q[b := E2]``, so the
        second part holds by construction; the first assignment is then searched among the same
        short candidates. Nothing is trusted: both assignments go through the engine and the
        prover, exactly as a model's proposal would. The split itself has no obligation.

        Returns ``("sequential", {"intermediate": R}, result)`` and sets :attr:`plan`, or ``None``.
        """
        frame = sorted(frame_names(spec.frame))
        if len(frame) < 2 or "sequential" not in self.screen.laws or "assignment" not in self.screen.laws:
            return None
        deadline = time.monotonic() + self.pair_seconds
        queries = [0]

        def out_of_budget() -> bool:
            queries[0] += 1
            return queries[0] > self.pair_queries or time.monotonic() > deadline

        post = spec.postcondition.expr
        # The split is built with the law itself, not through ``engine.apply``. Sequential
        # composition has no proof obligation of its own; what the engine adds is a feasibility
        # check on each half ("some state satisfies the post-condition"), which is quantified and,
        # on nonlinear goals, runs to its 3-second limit. Here that question is already answered
        # by a stronger fact: each half is closed by an assignment the prover has just accepted.
        splitter = self.screen.laws["sequential"]()
        for last in frame:
            # the plain short candidates first; an equation's solution is always kept, even when the
            # list is long enough to cut it off
            tail: List[str] = candidate_expressions(spec, last, 30)
            tail += [text for text in solved_for(spec, last) if text not in tail]
            for text2 in tail:
                if out_of_budget():
                    return None
                try:
                    e2 = parse_expr(text2)
                    middle = substitute(copy.deepcopy(post), last, e2)
                    split = splitter.apply(spec, {"intermediate": middle})
                    part1, part2 = split.sub_specs
                except Exception:
                    continue
                mentioned = get_free_vars(middle)
                for first in (v for v in frame if v != last and v in mentioned):
                    # An assignment to ``first`` cannot change a conjunct of the middle assertion
                    # that does not mention it, so those must already follow from the
                    # precondition. One query settles it for every candidate below.
                    fixed = join_conjunction([c for c in split_conjunction(middle)
                                              if first not in get_free_vars(c)])
                    if fixed is not None and not self._follows(spec, fixed):
                        continue
                    for text1 in candidate_expressions(part1, first, 60):
                        if out_of_budget():
                            return None
                        try:
                            e1 = parse_expr(text1)
                        except Exception:
                            continue
                        step1 = {"variable": first, "expr": e1}
                        step2 = {"variable": last, "expr": e2}
                        try:
                            self.screen.apply(part1, "assignment", step1, timeout_ms=self.timeout_ms)
                            self.screen.apply(part2, "assignment", step2, timeout_ms=self.timeout_ms)
                        except (VerificationError, ValueError):
                            continue
                        self.plan = {"part1": ("assignment", step1), "part2": ("assignment", step2)}
                        return "sequential", {"intermediate": middle}, split
        return None

    def solve(self, spec) -> Optional[Tuple[str, Dict[str, object], object]]:
        """``(law, parameters, result)`` for the first accepted candidate, or ``None``."""
        self.near_miss = None
        self.missing_fact = None
        self.plan = None
        for law in ("skip", "initialized_skip"):
            if law in self.screen.laws:
                try:
                    return law, {}, self.screen.apply(spec, law, {}, timeout_ms=self.timeout_ms)
                except (VerificationError, ValueError):
                    pass

        if "assignment" not in self.screen.laws:
            return None
        refuted = []                      # (violated parts, not-incremental, order, entry)
        order = 0
        for variable in sorted(frame_names(spec.frame)):
            for text in candidate_expressions(spec, variable, self.max_candidates):
                try:
                    expr: ASTNode = parse_expr(text)
                except Exception:
                    continue
                params = {"variable": variable, "expr": expr}
                order += 1
                try:
                    result = self.screen.apply(spec, "assignment", params, timeout_ms=self.timeout_ms)
                except VerificationUnknown:
                    continue
                except (VerificationError, ValueError) as error:
                    message = str(error)
                    if "Counterexample" not in message:
                        continue
                    own = 0 if text in spec_subterm_updates(spec, variable) else 1
                    refuted.append((own, _candidate_class(variable, text), order,
                                    ("assignment", params, message)))
                    continue
                self.near_miss = None
                return "assignment", params, result
        try:
            pair = self.solve_pair(spec)
        except Exception:                         # an optional helper must never end a trial
            pair = None
        if pair is not None:
            return pair
        if refuted:
            # The most informative miss: an update of the variable in terms of itself and
            # another name of the specification (x + e) before one built from a number
            # (x + 1) before anything else; then fewest broken parts of the goal; then the
            # earliest candidate. (The counterexample, and so the count, varies by model, so
            # it only breaks ties.)
            best = min(refuted, key=lambda r: r[:3])
            self.near_miss = best[3]
            # A missing fact is only worth reporting for an update that is plausibly *the*
            # step (the specification's own subterm, or the variable moved by another name);
            # for an arbitrary candidate almost any assumption can be made to fit.
            if best[0] == 0 or best[1] == 0:
                self.missing_fact = self.missing_fact_for(spec, self.near_miss)
        return None


def _candidate_class(variable: str, text: str) -> int:
    """0: variable updated using another name (x + e); 1: using only numbers (x + 1); 2: other."""
    names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", text))
    if variable in names:
        return 0 if len(names) >= 2 else 1
    return 2


def _violated_parts(message: str) -> int:
    """How many conjuncts of the goal a refuted candidate breaks, read from the message."""
    marker = "For these values the following part of the goal is false:"
    if marker not in message:
        return 99
    count = 0
    for line in message.split(marker, 1)[1].splitlines()[1:]:
        if line.startswith("    - "):
            count += 1
        else:
            break
    return count or 99
