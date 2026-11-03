from typing import Dict, Optional, Any, List
from FormalLLM.refinement.graph.status import AttemptStatus

class RefinementAttempt:
    def __init__(self, id: str, source_node_id: str, law: str, parameters: Dict[str, Any]):
        self.id = id
        self.source_node_id = source_node_id
        self.law = law
        self.parameters = parameters
        self.status = AttemptStatus.PENDING
        self.status_history: List[AttemptStatus] = [self.status]
        
        # e.g. {"then": "N2", "else": "N3"} or {"part1": "N4", "part2": "N5"}
        self.destination_roles: Dict[str, str] = {} 
        
        self.counterexample: Optional[str] = None
        self.error_message: Optional[str] = None

        #: Who proposed it: "model", or "assist" for a candidate the system's own leaf
        #: solver tried (see agent/assist.py). A refuted probe is evidence about a node,
        #: not a mistake the model made, and is reported to it as such.
        self.source: str = "model"
        #: For a refuted probe: a fact that, if the node's precondition also guaranteed it,
        #: would make the probe valid. The precondition came from the parent's step, so this
        #: is what the parent has to add (to its invariant, say).
        self.repair: Optional[str] = None

    def update_status(self, new_status: AttemptStatus):
        self.status = new_status
        self.status_history.append(new_status)
