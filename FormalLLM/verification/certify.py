"""Certify a finished refinement with Coq and/or Lean.

The search loop uses Z3: it is fast and it produces counterexamples, which are
what a model needs to repair a wrong choice. A proof assistant is slow (Lean
imports Mathlib on every run) and says nothing useful when it fails. So the
efficient arrangement is the one the paper's final output implies: search with
Z3, and when a derivation is complete, ask the proof assistants to check every
proof obligation of the steps that were actually used.

``certify_derivation`` re-derives those obligations by re-applying each accepted
step's law to its node, so what is certified is exactly what the engine proved.
"""

import time
from typing import Dict, List, Optional

from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.refinement.graph.status import AttemptStatus


def derivation_obligations(graph: RefinementGraph, engine) -> List[dict]:
    """``[{node, law, obligation}]`` for every accepted, live step of the derivation."""
    out = []
    inbound = graph._inbound_map()
    for node_id in sorted(graph.nodes, key=lambda n: int(n[1:])):
        if not graph.is_live(node_id, inbound):
            continue
        attempt = graph.accepted_attempt(node_id)
        if attempt is None or attempt.status != AttemptStatus.ACCEPTED:
            continue
        law = engine.laws[attempt.law]()
        result = law.apply(graph.nodes[node_id].specification, attempt.parameters)
        for obligation in result.obligations:
            out.append({"node": node_id, "law": attempt.law, "obligation": obligation})
    return out


def certify_derivation(graph: RefinementGraph, engine, backends: Dict[str, object],
                       timeout_ms: Optional[int] = None) -> dict:
    """Check each obligation of the final derivation with every backend in ``backends``.

    Returns a JSON-friendly report::

        {"obligations": 6,
         "coq":  {"certified": 6, "seconds": 3.2, "failures": []},
         "lean": {"certified": 5, "seconds": 41.0,
                  "failures": [{"node": "N2", "law": "assignment", "reason": "..."}]}}
    """
    items = derivation_obligations(graph, engine)
    report: Dict[str, object] = {"obligations": len(items)}
    for name, backend in backends.items():
        started = time.time()
        certified, failures = 0, []
        # A backend that can check several obligations in one process (Lean: one Mathlib load,
        # not one per obligation) is asked to; the others are asked one at a time.
        if hasattr(backend, "verify_many"):
            verdicts = backend.verify_many([item["obligation"] for item in items], timeout_ms)
        else:
            verdicts = [backend.verify(item["obligation"], timeout_ms) for item in items]
        for item, (status, message) in zip(items, verdicts):
            if status == "PROVED":
                certified += 1
            else:
                failures.append({"node": item["node"], "law": item["law"],
                                 "status": status, "reason": message.splitlines()[0][:200]})
        report[name] = {"certified": certified, "seconds": round(time.time() - started, 2),
                        "failures": failures}
    return report


def render_report(report: dict) -> str:
    lines = [f"{report['obligations']} proof obligations in the final derivation"]
    for name, data in report.items():
        if name == "obligations":
            continue
        lines.append(f"  {name}: {data['certified']} of {report['obligations']} certified "
                     f"({data['seconds']} s)")
        for failure in data["failures"]:
            lines.append(f"    - {failure['node']} ({failure['law']}): {failure['reason']}")
    return "\n".join(lines)
