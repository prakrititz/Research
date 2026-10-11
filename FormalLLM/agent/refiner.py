from typing import List, Optional, Dict
from FormalLLM.refinement.engine import RefinementEngine, VerificationError, VerificationUnknown
from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.refinement.graph.status import AttemptStatus, NodeStatus
from FormalLLM.llm.provider import LLMProvider, LLMBudgetExhausted
from FormalLLM.llm.prompts import generate_state_prompt, to_string
from FormalLLM.llm.parser import parse_llm_response
from FormalLLM.llm import spec_render as sr
from FormalLLM.llm.law_cards import MASSAGING_LAWS
from FormalLLM.lspec.ast import ASTNode
from FormalLLM.agent.assist import LeafSolver
from FormalLLM.refinement.vocabulary import unknown_names, unknown_name_message

class RefinementExhausted(Exception):
    pass


class _SubtreeExhausted(Exception):
    """Internal: the subtree rooted at ``node_id`` has used its allowance of LLM calls."""

    def __init__(self, node_id: str):
        super().__init__(node_id)
        self.node_id = node_id


def spec_key(spec) -> str:
    """Canonical string form of a specification, used for progress checking."""
    return to_string(spec)


def render_parameters(parameters) -> str:
    """Parameters as a person would read them, not as a dataclass repr.

    The history sent back to the model used to print ``{'guard': BinaryOp(left=
    Variable(...), ...)}``, which is noise it then had to decode.
    """
    if not parameters:
        return "(none)"
    shown = []
    for key, value in parameters.items():
        text = sr.render_expr(value) if isinstance(value, ASTNode) else str(value)
        shown.append(f'{key} = {text}')
    return "; ".join(shown)


def summarize_rejection(message: str) -> str:
    """The parts of a prover rejection a reader needs: what failed, the values, what is false.

    The full message also lists every assumption, which is useful once but too
    long to repeat for every ancestor of a failed node.
    """
    keep, in_violated = [], False
    for line in (message or "").splitlines():
        stripped = line.strip()
        if stripped.startswith("The obligation that failed"):
            keep.append(stripped)
            in_violated = False
        elif stripped.startswith("Counterexample"):
            keep.append(stripped)
            in_violated = False
        elif stripped.startswith("For these values"):
            keep.append(stripped)
            in_violated = True
        elif in_violated and stripped.startswith("- "):
            keep.append("  " + stripped)
        else:
            in_violated = False
    return "\n".join(keep) if keep else (message or "").strip()[:300]


class AutomatedRefiner:
    def __init__(self, engine: RefinementEngine, llm: LLMProvider,
                 max_retries: int = 5, max_depth: int = 6, use_multi_turn: bool = False,
                 assist: bool = False, subtree_budget: Optional[int] = 10):
        self.engine = engine
        # A step whose parts have consumed this many LLM calls without finishing is almost
        # certainly off track (measured: 26 calls inside one loop body that could never
        # succeed because the loop's invariant was too weak; 21 more below a split on a
        # variable whose starting value was arbitrary). The step is then abandoned and its
        # owner told why. 10 is above what any derivation measured here needs below one step
        # (a square root needs 5 in total). The root is bounded by the caller's own budget.
        self.subtree_budget = subtree_budget
        self.calls_made = 0
        self._active: list = []         # (node id, calls made when it began, is the root)
        # Off by default: the paper's pipeline has no such step. When on, a node
        # the prover can settle with skip or one short assignment is closed without
        # an LLM call (see agent/assist.py); the creative choices stay with the model.
        self.assist = assist
        self.assist_discharges = 0
        self._leaf_solver = LeafSolver(engine) if assist else None
        self.llm = llm
        self.max_retries = max_retries
        self.use_multi_turn = use_multi_turn
        # Structural laws that emit no proof obligations (alternation, sequential)
        # can always be applied again, each time producing a syntactically new
        # sub-specification. Nothing in the calculus bounds that descent, so the
        # search needs an explicit depth limit; past it, only terminal laws
        # (assignment / skip) may be used.
        self.max_depth = max_depth
        self.blacklisted_laws_per_node: Dict[str, List[str]] = {}
        # Derive dynamically so this can't drift when new laws are registered
        self.TOTAL_LAWS = len(engine.laws)
        # How many times each (node, law) pair has been tried with parameters
        # that failed somewhere below. A law is only abandoned once several
        # *different* parameter choices have failed -- see refine_node.
        self.param_failures_per_node: Dict[tuple, int] = {}
        # A law whose parameters failed below is given this many chances to be
        # re-proposed with better parameters before it is blacklisted outright.
        # The paper falls back only after more than five failures on a
        # specification (Algorithm 1, line 15); two was harsher than that.
        self.max_param_attempts = 3
        # (law, parameters) pairs that already failed at a node: proposing the
        # same thing again can only fail the same way, so it is turned away
        # without spending a proof or hiding the model's repeat from itself.
        self._failed_proposals: Dict[str, Dict[tuple, str]] = {}

    def _generate(self, prompt: str, **kwargs) -> str:
        if self.subtree_budget is not None:
            for node_id, started, is_root in self._active:        # outermost first
                if not is_root and self.calls_made - started >= self.subtree_budget:
                    raise _SubtreeExhausted(node_id)
        self.calls_made += 1
        return self.llm.generate(prompt, **kwargs)

    # --- feedback ----------------------------------------------------------

    def _build_history_context(self, graph: RefinementGraph, node_id: str, law: Optional[str] = None) -> str:
        failures = []
        node = graph.nodes[node_id]
        for attempt_id in node.attempts:
            attempt = graph.attempts[attempt_id]
            if law is not None and attempt.law != law:
                continue

            params = render_parameters(attempt.parameters)
            if attempt.status == AttemptStatus.REJECTED and attempt.source == "assist":
                # A quick test the system ran. It is evidence about this specification, not
                # a mistake of the model's, and it must not be answered as if it were one.
                evidence = "\n".join("    " + line for line in
                                     summarize_rejection(attempt.counterexample or "").splitlines())
                failures.append(f"- Law '{attempt.law}', Parameters: {params}\n"
                                f"  Not your proposal: the system tried this as a quick test and the "
                                f"prover refuted it:\n{evidence}")
            elif attempt.status == AttemptStatus.REJECTED:
                reason = attempt.counterexample or "Verification failed."
                failures.append(f"- Law '{attempt.law}', Parameters: {params}\n  Failed: {reason}")
            elif attempt.status == AttemptStatus.INCONCLUSIVE:
                failures.append(f"- Law '{attempt.law}', Parameters: {params}\n  Failed: Z3 Verification was INCONCLUSIVE (timeout or non-linear arithmetic complexity).")
            elif attempt.status == AttemptStatus.ERROR:
                reason = attempt.error_message or "System Error."
                failures.append(f"- Law '{attempt.law}', Parameters: {params}\n  Failed: {reason}")
            elif attempt.status == AttemptStatus.ABORTED:
                reason = attempt.error_message or "Sub-specification could not be refined further."
                failures.append(f"- Law '{attempt.law}', Parameters: {params}\n  Failed: The step was accepted by the prover, but the resulting tree failed.\n  {reason}")

        if not failures:
            return ""

        header = "Previous failed attempts with '" + law + "':\n" if law else "Previous failed attempts:\n"
        return header + "\n\n".join(failures)

    #: Where a sub-specification's precondition comes from, per parent law, and so what the
    #: parent has to change to give it a missing fact.
    _PRECONDITION_FIX = {
        "initialised_iteration": ("That precondition is built from the loop invariant of the step above: add "
                                  "{fact} to the invariant (it must then also hold after the set-up step)."),
        "iteration": ("That precondition is the loop's own precondition, used as its invariant: use "
                      "initialised_iteration with an invariant that also contains {fact}."),
        "sequential": "That precondition is the intermediate assertion R of the step above: add {fact} to R.",
        "flexible_sequential": "That precondition is a middle condition of the step above: make it include {fact}.",
        "weaken_pre": "That precondition is the R of the step above: keep {fact} in R.",
        "alternation": ("That precondition is the original one plus the test of the step above: choose a "
                        "test that guarantees {fact}."),
    }

    #: How far down a failed chain the digest follows a step that was accepted but whose parts failed.
    _DIGEST_DEPTH = 4

    @staticmethod
    def _probes(graph: RefinementGraph, node_id: str) -> list:
        """The system's own refuted quick tests at a node (see agent/assist.py)."""
        return [graph.attempts[a] for a in graph.nodes[node_id].attempts
                if graph.attempts[a].source == "assist" and graph.attempts[a].status == AttemptStatus.REJECTED]

    def _repair_probe(self, graph: RefinementGraph, node_id: str, depth: int = 0):
        """The refuted probe that names a missing fact, here or along the failed chain below."""
        for probe in self._probes(graph, node_id):
            if probe.repair:
                return probe
        if depth >= self._DIGEST_DEPTH:
            return None
        for attempt_id in graph.nodes[node_id].attempts:
            attempt = graph.attempts[attempt_id]
            if attempt.status == AttemptStatus.ABORTED:
                for child_id in attempt.destination_roles.values():
                    if graph.nodes[child_id].status == NodeStatus.FAILED:
                        found = self._repair_probe(graph, child_id, depth + 1)
                        if found is not None:
                            return found
        return None

    @staticmethod
    def _step_text(attempt) -> str:
        """``x := x + e`` for an assignment, the law with its parameters otherwise."""
        if attempt.law == "assignment" and {"variable", "expr"} <= set(attempt.parameters or {}):
            expr = attempt.parameters["expr"]
            return (f"{attempt.parameters['variable']} := "
                    f"{sr.render_expr(expr) if isinstance(expr, ASTNode) else expr}")
        return f"{attempt.law} with {render_parameters(attempt.parameters)}"

    def _failure_digest(self, graph: RefinementGraph, node_id: str, role: Optional[str] = None,
                        owner=None, depth: int = 0) -> str:
        """Why ``node_id`` could not be refined, written for the node that created it.

        A parent used to learn only "Child node 'N4' exhausted all options".
        That hides the one fact it can act on: the child's specification was
        unprovable *because of a choice the parent made* (a loop invariant that
        omitted a sign condition, say). The digest names the child, shows its
        specification, and says which earlier choice to change:

        1. If a quick test found a fact the child's precondition lacks, that is
           the evidence, stated as the change to make. (On the paper's square-root
           example the digest used to quote an unrelated test of the root's and
           blamed the root's intermediate assertion for a flaw in the loop's
           invariant, two levels down.)
        2. Else the first proof of the *model's own* that the prover rejected there.
        3. Else a step that was accepted but whose own parts failed, followed down.
        4. Else the system's refuted tests, then the bare fact that nothing applied.

        ``owner`` is the attempt whose step created this node, i.e. the step whose
        parameters decide this node's precondition.
        """
        node = graph.nodes[node_id]
        label = f"'{role}' ({node_id})" if role else node_id
        where = f"Sub-specification {label}  {sr.render_spec_compact(node.specification)}"

        # 1. A missing fact, found here or below.
        probe = self._repair_probe(graph, node_id, depth)
        if probe is not None and probe.source_node_id == node_id:
            evidence = "\n".join("    " + line for line in summarize_rejection(probe.counterexample or "").splitlines())
            fix = self._PRECONDITION_FIX.get(owner.law if owner is not None else "",
                                             "That precondition was fixed by the step above: change that "
                                             "step so that it guarantees {fact}.").format(fact=probe.repair)
            return (f"{where} could not be refined. Its simplest candidate, {self._step_text(probe)}, is "
                    f"refuted:\n{evidence}\n  The same step would be valid if the precondition of this "
                    f"sub-specification also guaranteed {probe.repair}. {fix}")
        if probe is not None:
            for attempt_id in node.attempts:
                attempt = graph.attempts[attempt_id]
                if attempt.status == AttemptStatus.ABORTED:
                    for child_role, child_id in attempt.destination_roles.items():
                        if graph.nodes[child_id].status == NodeStatus.FAILED and \
                                self._repair_probe(graph, child_id, depth + 1) is not None:
                            deeper = self._failure_digest(graph, child_id, child_role, owner=attempt, depth=depth + 1)
                            return (f"{where} could not be refined: it was split by law '{attempt.law}' "
                                    f"({render_parameters(attempt.parameters)}) and a part of that split failed.\n  {deeper}")

        # 2. The earliest proof of the model's own that was rejected at this node.
        for attempt_id in node.attempts:
            attempt = graph.attempts[attempt_id]
            if (attempt.status == AttemptStatus.REJECTED and attempt.source != "assist" and attempt.counterexample
                    and attempt.counterexample.startswith("Refinement invalid")):
                evidence = summarize_rejection(attempt.counterexample)
                indented = "\n".join("    " + line for line in evidence.splitlines())
                return (f"{where} could not be refined. The first proof that failed there was law "
                        f"'{attempt.law}' with {render_parameters(attempt.parameters)}:\n{indented}\n"
                        f"  Such a failure usually comes from the parameters chosen at THIS step "
                        f"(for example an invariant or intermediate assertion that is too weak or too "
                        f"strong for that sub-specification), not from the sub-specification itself.")

        # 3. Otherwise follow a step that was accepted but whose own subtree failed.
        if depth < self._DIGEST_DEPTH:
            for attempt_id in node.attempts:
                attempt = graph.attempts[attempt_id]
                if attempt.status == AttemptStatus.ABORTED:
                    for child_role, child_id in attempt.destination_roles.items():
                        if graph.nodes[child_id].status == NodeStatus.FAILED:
                            deeper = self._failure_digest(graph, child_id, child_role, owner=attempt, depth=depth + 1)
                            return (f"{where} could not be refined: it was split by law '{attempt.law}' and "
                                    f"a part of that split failed.\n  {deeper}")

        # 4. The system's own refuted tests, or nothing at all.
        for probe in self._probes(graph, node_id):
            evidence = "\n".join("    " + line for line in summarize_rejection(probe.counterexample or "").splitlines())
            return (f"{where} could not be refined. Even the simplest candidate, {self._step_text(probe)}, "
                    f"is refuted:\n{evidence}")
        errors = [graph.attempts[a].error_message for a in node.attempts
                  if graph.attempts[a].status == AttemptStatus.ERROR and graph.attempts[a].error_message]
        detail = f" Last error: {errors[-1][:200]}" if errors else ""
        return f"{where} could not be refined: no proposal for it could be applied.{detail}"

    # --- guards ------------------------------------------------------------

    @staticmethod
    def _chain_violation(law: str, parent_law: Optional[str]) -> Optional[str]:
        """Two spec-massaging steps in a row can always be merged, and never help.

        ``strengthen_post`` and ``weaken_pre`` only reshape a specification.
        Measured on the paper's square-root example: after the loop was
        correctly introduced, the body was met with sequential, strengthen_post,
        weaken_pre, weaken_pre ... until the depth limit, 27 of 40 LLM calls in
        a subtree that could not succeed.
        """
        if law in MASSAGING_LAWS and parent_law in MASSAGING_LAWS:
            return (f"'{law}' was applied directly to the result of '{parent_law}'. Two specification-"
                    f"reshaping steps in a row cannot make progress; choose a structural law "
                    f"(sequential, alternation, a loop) or finish with assignment or skip.")
        return None

    def _reject_without_engine(self, graph: RefinementGraph, node_id: str, law: str,
                               parameters, message: str) -> None:
        attempt_id = graph.record_attempt(node_id, law, parameters)
        attempt_obj = graph.attempts[attempt_id]
        attempt_obj.update_status(AttemptStatus.REJECTED)
        attempt_obj.counterexample = message

    @staticmethod
    def _proposal_key(law: str, parameters) -> tuple:
        return (law, tuple(sorted(
            (k, sr.render_expr(v) if isinstance(v, ASTNode) else str(v))
            for k, v in (parameters or {}).items())))

    def _auto_discharge(self, graph: RefinementGraph, node_id: str, path: tuple = ()) -> bool:
        """Close ``node_id`` with skip, one short assignment or two in a row, if the prover accepts them."""
        node = graph.nodes[node_id]
        found = self._leaf_solver.solve(node.specification)
        if found is None:
            near = self._leaf_solver.near_miss
            if near is not None:
                # The prover refuted the obvious update. Keep that as a rejected attempt:
                # the model sees it in this node's history, and the parent sees it in the
                # digest if this node cannot be finished.
                law, parameters, message = near
                attempt_id = graph.record_attempt(node_id, law, parameters)
                attempt = graph.attempts[attempt_id]
                attempt.update_status(AttemptStatus.REJECTED)
                attempt.counterexample = message
                attempt.source = "assist"
                attempt.repair = self._leaf_solver.missing_fact
                self._failed_proposals.setdefault(node_id, {})[self._proposal_key(law, parameters)] = \
                    summarize_rejection(message).replace("\n", " ")[:240]
            return False
        law, parameters, result = found
        if result.program is None:
            return self._close_split(graph, node_id, path, law, parameters, result)
        attempt_id = graph.record_attempt(node_id, law, parameters)
        attempt = graph.attempts[attempt_id]
        attempt.update_status(AttemptStatus.ACCEPTED)
        attempt.source = "assist"
        node.status = NodeStatus.REFINED
        node.program = result.program
        self.assist_discharges += 1
        print(f"[assist] closed node {node_id} with {law} {render_parameters(parameters)} (no LLM call)")
        return True

    def _close_split(self, graph: RefinementGraph, node_id: str, path: tuple, law: str,
                     parameters, result) -> bool:
        """Close ``node_id`` with a split whose parts the solver has already finished.

        The solver only offers a split after the prover accepted a short assignment for each of
        its parts (see ``LeafSolver.solve_pair``); here they are re-applied through the engine
        and recorded like any other step, so the derivation, its program and its certificate
        are built exactly as for a model's proposal.
        """
        node = graph.nodes[node_id]
        plan = self._leaf_solver.plan or {}
        if (len(path) > self.max_depth or set(plan) != set(result.by_role())
                or any(spec_key(s) in path for s in result.sub_specs)):
            return False
        finished = {}
        try:
            for role, sub_spec in result.by_role().items():
                step_law, step_params = plan[role]
                finished[role] = (step_law, step_params, self.engine.apply(sub_spec, step_law, step_params))
        except (VerificationError, ValueError):
            return False                    # cannot happen after the solver's own check; the model is asked instead
        attempt_id = graph.record_attempt(node_id, law, parameters)
        attempt = graph.attempts[attempt_id]
        roles = {role: graph.create_node(sub_spec) for role, sub_spec in result.by_role().items()}
        attempt.destination_roles = roles
        attempt.update_status(AttemptStatus.ACCEPTED)
        attempt.source = "assist"
        node.status = NodeStatus.DELEGATED
        for role, child_id in roles.items():
            step_law, step_params, step_result = finished[role]
            child_attempt = graph.attempts[graph.record_attempt(child_id, step_law, step_params)]
            child_attempt.update_status(AttemptStatus.ACCEPTED)
            child_attempt.source = "assist"
            graph.nodes[child_id].status = NodeStatus.REFINED
            graph.nodes[child_id].program = step_result.program
        self.assist_discharges += 1 + len(roles)
        steps = "; ".join(f"{p['variable']} := {sr.render_expr(p['expr'])}" for _, p, _ in finished.values())
        print(f"[assist] closed node {node_id} with {law}: {steps} (no LLM call)")
        return True

    # --- the search --------------------------------------------------------

    def refine_node(self, graph: RefinementGraph, node_id: str,
                    ancestry: tuple = (), parent_law: Optional[str] = None) -> bool:
        """Refine ``node_id`` (see :meth:`_refine_node_inner`), enforcing the subtree call cap.

        Every active node is on ``self._active`` with the call count at which it began;
        :meth:`_generate` raises :class:`_SubtreeExhausted` for the *outermost* ancestor
        whose subtree has used up its allowance, and each node on the way unwinds, so a
        long chain of nodes that are each under the cap cannot hide a doomed branch.
        """
        self._active.append((node_id, self.calls_made, node_id == graph.root_id))
        try:
            return self._refine_node_inner(graph, node_id, ancestry, parent_law)
        except _SubtreeExhausted as stop:
            self._abandon(graph, node_id)
            if stop.node_id == node_id:
                print(f"\n---> [Node '{node_id}' used {self.calls_made - self._active[-1][1]} LLM calls "
                      f"without finishing; returning to its parent]")
                return False
            raise
        finally:
            self._active.pop()

    def _renew_allowance(self, node_id: str) -> None:
        """Start a fresh allowance for ``node_id``: its next proposal gets the same room as its first."""
        self._active = [(n, self.calls_made, root) if n == node_id else (n, started, root)
                        for n, started, root in self._active]

    @staticmethod
    def _abandon(graph: RefinementGraph, node_id: str) -> None:
        """Mark a node left unfinished by an unwinding search as failed, with its split aborted.

        The aborted split matters: the failure digest follows aborted steps down to the
        part that failed, and a step left "accepted" would hide the chain from it.
        """
        node = graph.nodes[node_id]
        node.status = NodeStatus.FAILED
        for attempt_id in node.attempts:
            attempt = graph.attempts[attempt_id]
            if attempt.status == AttemptStatus.ACCEPTED and attempt.destination_roles:
                attempt.update_status(AttemptStatus.ABORTED)

    def _refine_node_inner(self, graph: RefinementGraph, node_id: str,
                           ancestry: tuple = (), parent_law: Optional[str] = None) -> bool:
        """
        Recursively attempts to refine a node in the graph.
        Returns True if successful, False if it needs to fallback to parent.
        Raises RefinementExhausted if it's the root node and all attempts are exhausted.

        `ancestry` carries the canonical spec strings of this node's ancestors so
        that a step which reproduces an ancestor specification can be rejected as
        making no progress. Without it, identity-refinable laws such as
        strengthen_post (with R = Q) or weaken_pre (with R = P) discharge their
        obligations trivially and the search descends forever.

        `parent_law` is the law that created this node, used to refuse chains of
        specification-reshaping steps.
        """
        node = graph.nodes[node_id]
        path = ancestry + (spec_key(node.specification),)

        if node_id not in self.blacklisted_laws_per_node:
            self.blacklisted_laws_per_node[node_id] = []
        failed_here = self._failed_proposals.setdefault(node_id, {})

        if self.assist and node_id != graph.root_id:
            if self._auto_discharge(graph, node_id, path):
                return True
            # The closest simple step fails only for want of a fact that this node cannot
            # establish: its precondition came from the parent's step. Spending LLM calls
            # here (measured: 16 of them, on nested loops) cannot help; the parent can,
            # and is told what is missing (see _failure_digest).
            missing = next((p.repair for p in self._probes(graph, node_id) if p.repair), None)
            if missing:
                print(f"\n---> [Node '{node_id}': its closest simple step is valid only if the precondition "
                      f"also guaranteed {missing}; returning to its parent]")
                node.status = NodeStatus.FAILED
                return False

        for attempt in range(self.max_retries):
            print(f"\n---> [Refining Node '{node_id}' | Depth: {len(path)-1} | Attempt: {attempt+1}/{self.max_retries}]")
            # Check if all possible laws are blacklisted
            if len(self.blacklisted_laws_per_node[node_id]) >= self.TOTAL_LAWS:
                break

            law = None
            try:
                if not self.use_multi_turn:
                    # 1. Prompt LLM (Single-Turn)
                    history_context = self._build_history_context(graph, node_id, None)
                    prompt = generate_state_prompt(
                        node,
                        blacklisted_laws=self.blacklisted_laws_per_node[node_id],
                        history_context=history_context,
                        available_laws=list(self.engine.laws)
                    )
                    response = self._generate(prompt)
                    law, parameters = parse_llm_response(response)

                    if law in self.blacklisted_laws_per_node[node_id]:
                        continue
                else:
                    from FormalLLM.llm.prompts import generate_law_selection_prompt, generate_parameter_synthesis_prompt
                    from FormalLLM.llm.parser import parse_law_response, parse_parameters_response

                    # Turn 1: Law Selection (with what already failed here, as in the
                    # paper's fall-back: "detailed feedback about the failures")
                    prompt = generate_law_selection_prompt(
                        node,
                        blacklisted_laws=self.blacklisted_laws_per_node[node_id],
                        available_laws=list(self.engine.laws),
                        history_context=self._build_history_context(graph, node_id, None),
                    )
                    response = self._generate(prompt)
                    law = parse_law_response(response)

                    if law in self.blacklisted_laws_per_node[node_id]:
                        continue

                chain_message = self._chain_violation(law, parent_law)
                if chain_message:
                    self._reject_without_engine(graph, node_id, law,
                                                parameters if not self.use_multi_turn else {},
                                                chain_message)
                    # The node's context will not change, so this law cannot work here.
                    self.blacklisted_laws_per_node[node_id].append(law)
                    continue

                # Evaluation loop (Turn 2 sub-loop if multi-turn, else 1 iteration)
                max_evals = self.max_param_attempts if self.use_multi_turn else 1
                turn2_completed = False

                for eval_idx in range(max_evals):
                    if self.use_multi_turn:
                        # Turn 2: Synthesize parameters
                        history_context = self._build_history_context(graph, node_id, law)
                        p_prompt = generate_parameter_synthesis_prompt(node, law, history_context=history_context)
                        # Give Turn 2 extra headroom since reasoning for parameter synthesis is often much longer
                        p_response = self._generate(p_prompt, max_tokens=8192)
                        parameters = parse_parameters_response(p_response, law)

                    # A formula may only use the specification's own names. An invented one
                    # (the model named a quantity: `V = N - ...`) would be read by the prover
                    # as an arbitrary constant and the step judged on something else.
                    invented = unknown_names(node.specification, parameters)
                    if invented:
                        self._reject_without_engine(graph, node_id, law, parameters,
                                                    unknown_name_message(node.specification, invented))
                        continue

                    # A proposal identical to one that already failed here cannot succeed.
                    proposal = self._proposal_key(law, parameters)
                    if proposal in failed_here:
                        self._reject_without_engine(
                            graph, node_id, law, parameters,
                            "These are exactly the parameters of an earlier attempt at this "
                            "specification, which failed: " + failed_here[proposal] +
                            " Propose different parameters.")
                        continue

                    # 3. Create attempt in graph
                    attempt_id = graph.record_attempt(node_id, law, parameters)
                    attempt_obj = graph.attempts[attempt_id]

                    # 4. Apply engine
                    try:
                        result = self.engine.apply(node.specification, law, parameters)

                        # 5. Handle Terminal vs Recursive success branches
                        if result.program is not None:
                            # Terminal branch (e.g. Assignment, Skip)
                            attempt_obj.update_status(AttemptStatus.ACCEPTED)
                            node.status = NodeStatus.REFINED
                            node.program = result.program
                            return True
                        else:
                            # Progress guard
                            if len(path) > self.max_depth:
                                attempt_obj.update_status(AttemptStatus.REJECTED)
                                attempt_obj.counterexample = (
                                    f"Maximum refinement depth ({self.max_depth}) reached. "
                                    f"'{law}' would split the specification further. You must "
                                    f"now discharge it directly with 'assignment' or 'skip'."
                                )
                                continue

                            repeats = [spec_key(s) for s in result.sub_specs if spec_key(s) in path]
                            if repeats:
                                attempt_obj.update_status(AttemptStatus.REJECTED)
                                attempt_obj.counterexample = (
                                    f"The law '{law}' made no progress: it produced a "
                                    f"sub-specification identical to one already being "
                                    f"refined ({repeats[0]}). Choose parameters that "
                                    f"strictly change the specification, or a different law."
                                )
                                continue

                            # Recursive branch
                            roles = {role: graph.create_node(sub_spec) for role, sub_spec in result.by_role().items()}

                            attempt_obj.destination_roles = roles
                            attempt_obj.update_status(AttemptStatus.ACCEPTED)
                            node.status = NodeStatus.DELEGATED

                            # Recursively refine all children
                            all_success = True
                            failed_role = None
                            allowance_used = False
                            for role, child_id in roles.items():
                                try:
                                    refined = self.refine_node(graph, child_id, path, parent_law=law)
                                except _SubtreeExhausted as stop:
                                    if stop.node_id != node_id:
                                        raise
                                    # This step's parts used up the allowance. That is a verdict on
                                    # THIS step, which should be told why and may try again -- not
                                    # a reason to abandon the whole node.
                                    refined, allowance_used = False, True
                                if not refined:
                                    all_success = False
                                    failed_role = (role, child_id)
                                    break

                            if all_success:
                                return True
                            else:
                                key = (node_id, law)
                                self.param_failures_per_node[key] = self.param_failures_per_node.get(key, 0) + 1

                                attempt_obj.update_status(AttemptStatus.ABORTED)
                                node.status = NodeStatus.OPEN

                                # Tell the parent which child failed and why, not merely that it did.
                                reason = self._failure_digest(graph, failed_role[1], failed_role[0], owner=attempt_obj)
                                if allowance_used:
                                    reason = (f"The parts below this step used their allowance of "
                                              f"{self.subtree_budget} LLM calls without finishing. " + reason)
                                    self._renew_allowance(node_id)
                                attempt_obj.error_message = reason
                                failed_here[proposal] = ("its sub-specification could not be refined: "
                                                         + " ".join(reason.split())[:400])

                                if self.param_failures_per_node[key] >= self.max_param_attempts:
                                    self.blacklisted_laws_per_node[node_id].append(law)
                                    turn2_completed = True
                                    break
                                else:
                                    continue

                    except VerificationError as e:
                        msg = str(e)
                        if isinstance(e, VerificationUnknown):
                            attempt_obj.update_status(AttemptStatus.INCONCLUSIVE)
                            failed_here[proposal] = "the prover could not decide it."
                        else:
                            attempt_obj.update_status(AttemptStatus.REJECTED)
                            attempt_obj.counterexample = msg
                            failed_here[proposal] = summarize_rejection(msg).replace("\n", " ")[:240]

                        continue

                # End of Turn 2 loop
                if self.use_multi_turn and not turn2_completed:
                    # If we exhausted Turn 2 iterations via VerificationErrors/progress guards
                    key = (node_id, law)
                    if law is not None:
                        self.param_failures_per_node[key] = self.param_failures_per_node.get(key, 0) + max_evals
                        if law not in self.blacklisted_laws_per_node[node_id]:
                            self.blacklisted_laws_per_node[node_id].append(law)

            except (LLMBudgetExhausted, _SubtreeExhausted):
                # LLMBudgetExhausted is a statement about the whole run, and
                # _SubtreeExhausted about an ancestor: neither is a failed attempt of
                # this node, so record nothing here and let it unwind to its owner.
                raise
            except Exception as e:
                # Parsing or other errors, create a dummy attempt to record the error
                err_law = law if law is not None else 'unknown'
                attempt_id = graph.record_attempt(node_id, err_law, {})
                attempt_obj = graph.attempts[attempt_id]
                attempt_obj.update_status(AttemptStatus.ERROR)
                attempt_obj.error_message = str(e)

        # If we exit the loop, max_retries exhausted or all laws blacklisted.
        node.status = NodeStatus.FAILED
        if node_id == graph.root_id:
            exhausted = self.blacklisted_laws_per_node.get(node_id, [])
            raise RefinementExhausted(f"Refinement exhausted at root node. Failed to refine specification. Blacklisted laws: {exhausted}")

        return False
