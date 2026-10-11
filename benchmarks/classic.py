"""The paper's Table 7 type of experiment: classic refinement problems, core vs extended laws.

Table 7 of the paper compares, on a set of classic programs, the number of
refinement steps and the proof time of (a) CorC, (b) Refine4LLM with only the
core laws ("Initial"), and (c) Refine4LLM with the extended laws. This module
reproduces the *type* of comparison with our own engine:

* each problem is stated in L_spec (functions such as ``fact`` or ``pow`` are
  modelled as array variables with defining axioms in the precondition);
* each is derived **twice** with a hand-written reference derivation, once with the
  core laws only (``sequential`` + ``iteration``) and once with the extended law
  ``initialised_iteration`` that the paper learns (section 6);
* every step is checked by the prover, and optionally the finished derivation is
  certified by Coq/Lean.

What this is *not*: the paper's numbers come from GPT-4 driving the refinement and
from CorC's own step granularity, and cannot be reproduced exactly. These are
deterministic derivations (no LLM), so the table shows what the **calculus** gives
(depth and proof effort of the extended laws), not what a model finds.

    python benchmarks/classic.py [--certify coq lean]
"""
import argparse
import json
import os
import sys
import time
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from FormalLLM.llm.parser import parse_expr                                   # noqa: E402
from FormalLLM.lspec.parser import parse_spec                                 # noqa: E402
from FormalLLM.refinement.engine import RefinementEngine, VerificationError   # noqa: E402
from FormalLLM.refinement.graph.graph import RefinementGraph                  # noqa: E402
from FormalLLM.refinement.graph.status import AttemptStatus, NodeStatus       # noqa: E402

# --- derivation trees ----------------------------------------------------------
# ("asg", variable, expr)                        one assignment
# ("seq", middle, [first, second])               sequential composition
# ("alt", guard, then_tree, else_tree)           if / else


def asg(variable, expr):
    return ("asg", variable, expr)


def seq(middle, first, second):
    return ("seq", middle, [first, second])


def alt(guard, then_tree, else_tree):
    return ("alt", guard, then_tree, else_tree)


# Paper Table 7 reference values: (steps CorC, Initial, Refine4LLM), (proof s CorC, Initial, Refine4LLM)
PAPER_TABLE_7 = {
    "Factorial": ((5, 5, 3), (3.6, 1.5, 0.4)),
    "Exponentiation": ((7, 7, 5), (15.2, 14.4, 10.4)),
    "Linear Search": ((5, 5, 4), (0.4, 0.2, 0.1)),
    "Max Element": ((9, 10, 5), (1.2, 1.0, 0.2)),
}

PROBLEMS = {
    "Factorial": dict(
        paper_row="Factorial",
        spec=("Frame: f:int, i:int.\n"
              "Precondition: (n:int)(fact:array int) := n >= 0 /\\ fact[0] = 1 /\\ "
              "forall (k:int) (k < 0 \\/ fact[(k+1)] = (k+1) * fact[k]).\n"
              "Postcondition: (n:int)(fact:array int) := f = fact[n]."),
        invariant="f = fact[i] && 0 <= i && i <= n", guard="i < n", variant="n - i",
        init=seq("f = 1", asg("f", "1"), asg("i", "0")),
        body=seq("f = fact[(i + 1)] && 0 <= i && i < n && n - i = V0",
                 asg("f", "f * (i + 1)"), asg("i", "i + 1")),
        note="fact is an array with fact[0] = 1 and fact[k+1] = (k+1) * fact[k]",
    ),
    "Exponentiation": dict(
        paper_row="Exponentiation",
        spec=("Frame: z:int, i:int.\n"
              "Precondition: (a:int)(n:int)(pw:array int) := n >= 0 /\\ pw[0] = 1 /\\ "
              "forall (k:int) (k < 0 \\/ pw[(k+1)] = a * pw[k]).\n"
              "Postcondition: (a:int)(n:int)(pw:array int) := z = pw[n]."),
        invariant="z = pw[i] && 0 <= i && i <= n", guard="i < n", variant="n - i",
        init=seq("z = 1", asg("z", "1"), asg("i", "0")),
        body=seq("z = pw[(i + 1)] && 0 <= i && i < n && n - i = V0",
                 asg("z", "z * a"), asg("i", "i + 1")),
        note=("repeated multiplication, not the paper's squaring: squaring needs pow with a "
              "changing base, i.e. a function symbol L_spec does not have"),
    ),
    "Linear Search": dict(
        paper_row="Linear Search",
        spec=("Frame: found:int, i:int.\n"
              "Precondition: (n:int)(key:int)(a:array int) := n >= 0.\n"
              "Postcondition: (n:int)(key:int)(a:array int) := (found = 1 /\\ 0 <= i /\\ i < n /\\ a[i] = key) \\/ "
              "(found = 0 /\\ (forall (k:int) (k < 0 \\/ k >= n \\/ ~(a[k] = key))))."),
        invariant=("0 <= i && i <= n && ((found = 0 && (forall (k:int) (k < 0 \\/ k >= i \\/ ~(a[k] = key)))) "
                   "\\/ (found = 1 && i < n && a[i] = key))"),
        guard="i < n && found = 0", variant="(n - i) + (1 - found)",
        init=seq("found = 0", asg("found", "0"), asg("i", "0")),
        body=alt("a[i] = key", asg("found", "1"), asg("i", "i + 1")),
        note="found is an integer flag (0/1): boolean variables are not supported by the proof assistants' translators",
    ),
    "Max Element": dict(
        paper_row="Max Element",
        spec=("Frame: m:int, i:int.\n"
              "Precondition: (n:int)(a:array int) := n > 0.\n"
              "Postcondition: (n:int)(a:array int) := (forall (k:int) (k < 0 \\/ k >= n \\/ a[k] <= m)) /\\ "
              "(exists (k:int) (k >= 0 /\\ k < n /\\ a[k] = m))."),
        invariant=("1 <= i && i <= n && (forall (k:int) (k < 0 \\/ k >= i \\/ a[k] <= m)) && "
                   "(exists (k:int) (k >= 0 /\\ k < i /\\ a[k] = m))"),
        guard="i < n", variant="n - i",
        init=seq("m = a[0]", asg("m", "a[0]"), asg("i", "1")),
        body=alt("a[i] > m",
                 seq("m = a[i] && 1 <= i && i < n && n - i = V0 && (forall (k:int) (k < 0 \\/ k >= i \\/ a[k] <= m))",
                     asg("m", "a[i]"), asg("i", "i + 1")),
                 asg("i", "i + 1")),
        note="",
    ),
}

#: Stated but not derived: Z3 answers `unknown` (quantified axioms plus non-linear integers).
OPEN_PROBLEMS = {
    "Logarithm": ("floor(log2 N) with 2^l as an axiomatised array and `n / 2` in the body: "
                  "Z3 returns `unknown` (incomplete quantifiers). Candidate for a Coq/Lean proof with "
                  "hand-instantiated axioms."),
    "Dutch Flag Sort": "needs assignment to array elements (swap), which L_pl does not have",
    "Pattern Matching": "needs strings and nested loops over them; not expressible in L_spec today",
}


class Derivation:
    """Applies a derivation tree to a graph, counting steps and prover time."""

    def __init__(self, spec_text):
        self.engine = RefinementEngine()
        self.graph = RefinementGraph(parse_spec(spec_text))
        self.steps = Counter()
        self.prove_seconds = 0.0
        self.obligations = 0

    def _step(self, node_id, law, params):
        node = self.graph.nodes[node_id]
        t0 = time.time()
        result = self.engine.apply(node.specification, law, params)
        self.prove_seconds += time.time() - t0
        self.obligations += len(result.obligations)
        attempt = self.graph.attempts[self.graph.record_attempt(node_id, law, params)]
        attempt.update_status(AttemptStatus.ACCEPTED)
        self.steps[law] += 1
        if result.program is not None:
            node.program, node.status = result.program, NodeStatus.REFINED
            return {}
        roles = {r: self.graph.create_node(s) for r, s in result.by_role().items()}
        attempt.destination_roles = roles
        node.status = NodeStatus.DELEGATED
        return roles

    def tree(self, node_id, t):
        kind = t[0]
        if kind == "asg":
            self._step(node_id, "assignment", {"variable": t[1], "expr": parse_expr(t[2])})
        elif kind == "seq":
            roles = self._step(node_id, "sequential", {"intermediate": parse_expr(t[1])})
            self.tree(roles["part1"], t[2][0])
            self.tree(roles["part2"], t[2][1])
        elif kind == "alt":
            roles = self._step(node_id, "alternation", {"guard": parse_expr(t[1])})
            self.tree(roles["then"], t[2])
            self.tree(roles["else"], t[3])
        else:
            raise ValueError(kind)


def derive(problem: dict, calculus: str) -> dict:
    """Derive ``problem`` with ``calculus`` in ('core', 'extended'); return its metrics."""
    d = Derivation(problem["spec"])
    root = d.graph.root_id
    loop = {"guard": parse_expr(problem["guard"]), "variant": parse_expr(problem["variant"])}
    if calculus == "extended":
        roles = d._step(root, "initialised_iteration",
                        dict(loop, invariant=parse_expr(problem["invariant"])))
        d.tree(roles["init"], problem["init"])
        d.tree(roles["body"], problem["body"])
    else:
        roles = d._step(root, "sequential", {"intermediate": parse_expr(problem["invariant"])})
        d.tree(roles["part1"], problem["init"])
        loop_roles = d._step(roles["part2"], "iteration", loop)
        d.tree(loop_roles["body"], problem["body"])
    return {"calculus": calculus, "steps": sum(d.steps.values()), "laws": dict(d.steps),
            "obligations": d.obligations, "z3_seconds": round(d.prove_seconds, 3),
            "complete": d.graph.is_complete(root), "graph": d.graph, "engine": d.engine}


def run_all(certify=None, names=None):
    from FormalLLM.verification.backends import get_backend
    from FormalLLM.verification.certify import certify_derivation
    rows = []
    for name, problem in PROBLEMS.items():
        if names and name not in names:
            continue
        row = {"problem": name, "note": problem["note"]}
        for calculus in ("core", "extended"):
            try:
                m = derive(problem, calculus)
            except VerificationError as e:
                row[calculus] = {"error": str(e).splitlines()[0][:200]}
                continue
            graph, engine = m.pop("graph"), m.pop("engine")
            if certify and m["complete"]:
                m["certificate"] = certify_derivation(graph, engine, {n: get_backend(n) for n in certify})
            row[calculus] = m
        rows.append(row)
    return rows


def render(rows) -> str:
    out = ["| Problem | Steps core / extended | Obligations | Z3 time core / extended (s) | Paper steps CorC / Initial / Refine4LLM |",
           "|---|---|---|---|---|"]
    for r in rows:
        c, e = r["core"], r["extended"]
        if "error" in c or "error" in e:
            out.append(f"| {r['problem']} | {c.get('error') or e.get('error')} | | | |")
            continue
        paper = PAPER_TABLE_7.get(r["problem"])
        paper_text = " / ".join(str(x) for x in paper[0]) if paper else "-"
        out.append(f"| {r['problem']} | {c['steps']} / {e['steps']} | {c['obligations']} / {e['obligations']} "
                   f"| {c['z3_seconds']} / {e['z3_seconds']} | {paper_text} |")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--certify", nargs="*", default=None, choices=("coq", "lean"))
    ap.add_argument("--out", default=os.path.join(ROOT, "benchmarks", "results", "classic.json"))
    args = ap.parse_args()
    rows = run_all(args.certify)
    print(render(rows))
    for r in rows:
        for calculus in ("core", "extended"):
            cert = r[calculus].get("certificate")
            if cert:
                print(f"  {r['problem']} ({calculus}): " + ", ".join(
                    f"{n} {cert[n]['certified']}/{cert['obligations']}" for n in cert if n != "obligations"))
    print("\nstated but not derived:")
    for name, why in OPEN_PROBLEMS.items():
        print(f"  - {name}: {why}")
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf8") as fh:
        json.dump({"rows": rows, "open": OPEN_PROBLEMS, "paper_table_7": PAPER_TABLE_7}, fh, indent=1)
    print("->", args.out)


if __name__ == "__main__":
    main()
