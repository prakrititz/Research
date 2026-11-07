"""Counter-examples by running the loop: the part of Z3's job that random sampling of a *single step* cannot do.

``plausible`` tests one obligation by drawing values for every variable of it, so for a step of a loop it must draw a state that
already satisfies the invariant (``ok = true ↔ ∀ k < i, …``, ``acc = (l.take i).filter p``): random values almost never do, and
it gives up (174 of 312 rejected mutants in doc 22 got no counter-example). Here the loop is *run*: draw only the task's inputs
(whose preconditions are usually weak), start from ``init``, and apply the candidate body, checking at every iteration that the
invariant holds, that the variant decreases, and, when the guard fails, that the postcondition holds for the result. Every state
reached from real inputs satisfies a correct invariant, so a violation is a real fault of the invariant, the initial value or the
step, and the run is a trace a person can read.

    finding = loop_finding(derivation, loop_goal, loop_law, step_expression)      # None when nothing could be shown
    finding.inputs   -> "operations := [0]"
    finding.trace    -> ["state (i = 0, bal = 0, neg = false)  invariant true  guard true", "  your step gives (i = 1, ...)", ...]

The harness is generated Lean (definitions for invariant, guard, variant, step; a fuel-bounded runner; a ``plausible`` theorem over
the inputs) and is allowed to fail to elaborate (an invariant that cannot be decided, a type without ``ToString``): then there is no
finding and the caller keeps the unsolved goal state, which is always reported.
"""
import re
from dataclasses import dataclass, field
from typing import List, Optional

from FormalLLM.lean.laws import Goal, Loop

FUEL = 16
PLAUSIBLE_CONFIG = "(config := { randomSeed := some 20261008, numInst := 200 })"     # fixed seed: replayable
OPTIONS = "set_option synthInstance.maxSize 100000 in\nset_option synthInstance.maxHeartbeats 0 in\n"


PART = "false part of the invariant: "      # a line ``feedback.describe`` shows in L_spec (the part is Lean text)


@dataclass
class Finding:
    inputs: str                       # ``operations := [0]`` as ``plausible`` prints it
    trace: List[str] = field(default_factory=list)
    kind: str = ""                    # init | step | exit
    failing: List[str] = field(default_factory=list)    # the top-level conjuncts of the invariant that are false

    def text(self) -> str:
        lines = [f"counter-example (found by running the loop): {self.inputs}"]
        lines += ["    " + line for line in self.trace[:12]]
        lines += ["    " + PART + part for part in self.failing[:3]]
        return "\n".join(lines)


_OPEN, _CLOSE = "([{⟨", ")]}⟩"
_LOOSE = re.compile(r"∀|∃|\bfun\b|λ|→|↔|∨|\bif\b|\blet\b|\bmatch\b|<\||\$|\|\||&&|=>|,")


def _depth0(text: str) -> str:
    """``text`` with everything inside brackets or string literals blanked: what is left is the top level."""
    out, depth, quoted = [], 0, False
    for k, ch in enumerate(text):
        if quoted:
            quoted = not (ch == '"' and text[k - 1] != "\\")
            out.append(" ")
            continue
        if ch == '"':
            quoted = True
            out.append(" ")
            continue
        if ch in _OPEN:
            depth += 1
            out.append(" ")
            continue
        if ch in _CLOSE:
            depth -= 1
            out.append(" ")
            continue
        out.append(ch if depth == 0 else " ")
    return "".join(out)


def _closer(text: str, start: int) -> int:
    """The index of the bracket closing the one at ``start`` (-1 if unbalanced); string literals are skipped."""
    depth, quoted = 0, False
    for k in range(start, len(text)):
        ch = text[k]
        if quoted:
            quoted = not (ch == '"' and text[k - 1] != "\\")
        elif ch == '"':
            quoted = True
        elif ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
            if depth == 0:
                return k
    return -1


def _unwrap(text: str) -> str:
    """Drop parentheses around the whole of ``text`` (not those of ``(a) ∧ (b)``)."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")") and _closer(text, 0) == len(text) - 1:
        text = text[1:-1].strip()
    return text


def conjuncts(prop: str) -> List[str]:
    """The top-level ``∧`` parts of a Lean proposition, nested conjunctions flattened. A part is split off only when
    nothing at the top level binds looser than ``∧`` (a binder, an implication, a disjunction, a lambda): otherwise the
    proposition is one part."""
    text = _unwrap(prop)
    top = _depth0(text)
    if "∧" not in top or _LOOSE.search(top):
        return [text]
    cuts = [k for k, ch in enumerate(top) if ch == "∧"]
    pieces = [text[a + 1:b] for a, b in zip([-1] + cuts, cuts + [len(text)])]
    return [part for piece in pieces for part in conjuncts(piece)]


def _false_parts(goal: Goal, law: Loop) -> str:
    """``dyn_false``: the 1-based numbers of the invariant's conjuncts that are false in a state (empty: one part)."""
    ctx = " ".join(f"({n} : {t})" for n, t in goal.ctx)
    parts = conjuncts(law.invariant)
    body = (" ++ ".join(f"(if decide ({p}) then [] else [{k + 1}])" for k, p in enumerate(parts))
            if len(parts) > 1 else "[]")
    return f"def dyn_false {ctx} {_state_binders(law)} : List Nat := {body}"


def _falses(goal: Goal, law: Loop, args: str) -> str:
    names = " ".join(n for n, _ in goal.ctx)
    return f'"; false parts: " ++ toString (dyn_false {names} {args})'


_FALSE_PARTS = re.compile(r";? false parts: \[([0-9, ]*)\]")


def _read_parts(trace: List[str], law: Loop):
    """Strip the ``false parts: [2]`` markers from the trace; the conjuncts they name (at the first failure)."""
    parts, failing, out = conjuncts(law.invariant), [], []
    for line in trace:
        match = _FALSE_PARTS.search(line)
        if match:
            if not failing and len(parts) > 1:
                failing = [parts[int(k) - 1] for k in match.group(1).replace(" ", "").split(",")
                           if k and 0 < int(k) <= len(parts)]
            line = line[:match.start()] + line[match.end():]
        out.append(line)
    return out, failing


def _state_binders(law: Loop) -> str:
    return " ".join(f"({n} : {t})" for n, t in law.state)


def _format_state(law: Loop, var: str) -> str:
    """Lean source for ``i = 1, bal = 3`` from the state value ``var``."""
    parts = [f'"{name} = " ++ toString {_nested(var, k, len(law.state))}' for k, (name, _t) in enumerate(law.state)]
    return ' ++ ", " ++ '.join(parts)


def _nested(var: str, k: int, count: int) -> str:
    if count == 1:
        return var
    if k == count - 1:
        return var + ".2" * k
    return var + ".2" * k + ".1"


def _args(law: Loop, var: str) -> str:
    return " ".join(_nested(var, k, len(law.state)) for k in range(len(law.state)))


def source(goal: Goal, law: Loop, step: Optional[str], with_post: bool) -> str:
    """The harness: definitions, runner, and the ``plausible`` theorem. ``step`` is the candidate body (``None``: only check ``init``)."""
    ctx = " ".join(f"({n} : {t})" for n, t in goal.ctx)
    names = " ".join(n for n, _ in goal.ctx)
    state = _state_binders(law)
    st = law.state_type
    init = "(" + ", ".join(f"({e})" for e in law.init) + ")" if len(law.init) > 1 else f"({law.init[0]})"
    s_args = _args(law, "s")
    r_args = _args(law, "r")
    hyps = " ".join(f"({n} : {p})" for n, p in goal.hyps)
    hyp_names = " ".join(n for n, _ in goal.hyps)
    result_of_s = f"({law._lam(law.result)} {s_args})"
    exit_check = (f"decide ({goal.post_with(result_of_s)})" if with_post else "true")
    lines = [
        f"def dyn_inv {ctx} {state} : Bool := decide ({law.invariant})",
        f"def dyn_guard {ctx} {state} : Bool := decide ({law.guard})",
        f"def dyn_var {ctx} {state} : Nat := {law.variant}",
    ]
    if step is not None:
        lines.append(f"def dyn_step {ctx} {state} : {st} := {step}")
        lines += [
            f"def dyn_ok {ctx} {hyps} : Bool :=",
            f"  let rec go : Nat → {st} → Bool",
            f"    | 0, _ => true",
            f"    | fuel + 1, s =>",
            f"      if !(dyn_inv {names} {s_args}) then false",
            f"      else if dyn_guard {names} {s_args} then",
            f"        let r := dyn_step {names} {s_args}",
            f"        dyn_inv {names} {r_args} && decide (dyn_var {names} {r_args} < dyn_var {names} {s_args}) && go fuel r",
            f"      else {exit_check}",
            f"  go {FUEL} {init}",
        ]
    else:
        lines.append(f"def dyn_ok {ctx} {hyps} : Bool := dyn_inv {names} " + " ".join(f"({e})" for e in law.init))
    lines += [OPTIONS.rstrip("\n"),
              f"theorem dyn_cex {goal.binders()} : dyn_ok {names} {hyp_names} = true := by\n  plausible {PLAUSIBLE_CONFIG}"]
    return "\n".join(lines) + "\n"


def trace_source(goal: Goal, law: Loop, step: str, inputs: str) -> Optional[str]:
    """``#eval`` of a trace of the run on the inputs ``plausible`` found (``operations := [0]``, one per line or comma separated)."""
    values = parse_inputs(inputs, [n for n, _ in goal.ctx])
    if values is None:
        return None
    ctx = " ".join(f"({n} : {t})" for n, t in goal.ctx)
    names = " ".join(n for n, _ in goal.ctx)
    st = law.state_type
    init = "(" + ", ".join(f"({e})" for e in law.init) + ")" if len(law.init) > 1 else f"({law.init[0]})"
    s_args, r_args = _args(law, "s"), _args(law, "r")
    fmt_s, fmt_r = _format_state(law, "s"), _format_state(law, "r")
    return "\n".join([
        f"def dyn_trace {ctx} : List String :=",
        f"  let rec go : Nat → {st} → List String",
        f"    | 0, _ => [\"(stopped after {FUEL} iterations)\"]",
        f"    | fuel + 1, s =>",
        f"      let head := \"state (\" ++ ({fmt_s}) ++ \")  invariant \" ++ toString (dyn_inv {names} {s_args}) ++ \"  guard \" ++ toString (dyn_guard {names} {s_args})",
        f"      if !(dyn_inv {names} {s_args}) then [head ++ \"   <- the invariant is false here\" ++ {_falses(goal, law, s_args)}]",
        f"      else if dyn_guard {names} {s_args} then",
        f"        let r := dyn_step {names} {s_args}",
        f"        let next := \"  your step gives (\" ++ ({fmt_r}) ++ \")  invariant \" ++ toString (dyn_inv {names} {r_args}) ++ \"  variant \" ++ toString (dyn_var {names} {s_args}) ++ \" -> \" ++ toString (dyn_var {names} {r_args})",
        f"        if dyn_inv {names} {r_args} && decide (dyn_var {names} {r_args} < dyn_var {names} {s_args}) then head :: next :: go fuel r",
        f"        else [head, next ++ (if !(dyn_inv {names} {r_args}) then \"   <- the invariant is false after your step\" ++ {_falses(goal, law, r_args)} else \"   <- the variant does not decrease\")]",
        f"      else [head, \"  the loop exits\"]",
        f"  go {FUEL} {init}",
        f"#eval (dyn_trace {' '.join('(' + v + ')' for v in values)}).foldl (fun acc line => acc ++ line ++ \"\\n\") \"\"",
    ]) + "\n"


def parse_inputs(text: str, names: List[str]) -> Optional[List[str]]:
    """Values of ``name := value`` pairs in the order of ``names``; ``None`` if one is missing."""
    found = {}
    for name in names:
        match = re.search(rf"(?:^|[\s,]){re.escape(name)} := (.*?)(?=(?:,\s+\w[\w']* := )|$)", text, re.S)
        if not match:
            return None
        found[name] = match.group(1).strip()
    return [found[n] for n in names]


def loop_finding(derivation, goal: Goal, law: Loop, step: Optional[str]) -> Optional[Finding]:
    """Run the loop with the candidate body on inputs drawn by ``plausible``; ``None`` if no fault was shown."""
    for with_post in (True, False):                # the postcondition may not be decidable: then test the invariant and variant only
        reply = derivation._run(source(goal, law, step, with_post))
        if reply.errors and not reply.counterexample:
            if with_post and step is not None:
                continue
            return None
        if reply.counterexample:
            finding = Finding(inputs=reply.counterexample, kind="step" if step is not None else "init")
            code = (trace_source(goal, law, step, reply.counterexample) if step is not None
                    else init_source(goal, law, reply.counterexample))
            if code:
                shown = derivation._run(_definitions(goal, law, step) + code)
                if not shown.infos:              # a part that does not elaborate alone: the trace without the parts
                    shown = derivation._run(_definitions(goal, law, step, parts=False) + code)
                if shown.infos:
                    lines = [line for line in shown.infos[0].replace("\\n", "\n").strip('"').splitlines() if line.strip()]
                    finding.trace, finding.failing = _read_parts(lines, law)
            return finding
        return None
    return None


def init_source(goal: Goal, law: Loop, inputs: str) -> Optional[str]:
    """``#eval`` of the initial state on the inputs ``plausible`` found, and which parts of the invariant it breaks."""
    values = parse_inputs(inputs, [n for n, _ in goal.ctx])
    if values is None:
        return None
    ctx = " ".join(f"({n} : {t})" for n, t in goal.ctx)
    names = " ".join(n for n, _ in goal.ctx)
    init = "(" + ", ".join(f"({e})" for e in law.init) + ")" if len(law.init) > 1 else f"({law.init[0]})"
    s_args = _args(law, "s")
    return "\n".join([
        f"def dyn_initial {ctx} : String :=",
        f"  let s : {law.state_type} := {init}",
        f"  \"initial state (\" ++ ({_format_state(law, 's')}) ++ \")  invariant \" ++ toString (dyn_inv {names} {s_args})"
        f" ++ {_falses(goal, law, s_args)}",
        f"#eval dyn_initial {' '.join('(' + v + ')' for v in values)}",
    ]) + "\n"


def _definitions(goal: Goal, law: Loop, step: Optional[str], parts: bool = True) -> str:
    ctx = " ".join(f"({n} : {t})" for n, t in goal.ctx)
    state = _state_binders(law)
    return "\n".join([
        f"def dyn_inv {ctx} {state} : Bool := decide ({law.invariant})",
        f"def dyn_guard {ctx} {state} : Bool := decide ({law.guard})",
        f"def dyn_var {ctx} {state} : Nat := {law.variant}",
        _false_parts(goal, law) if parts else f"def dyn_false {ctx} {state} : List Nat := []",
        *([f"def dyn_step {ctx} {state} : {law.state_type} := {step}"] if step is not None else []), ""])
