"""The datasets the Lean pipeline runs on, behind one interface.

Verina's tasks and our HumanEval tasks are stored in the same directory format (``task.json``, ``description.txt``, ``task.lean``
with ``-- !benchmark`` regions, ``test.json``), and are read by the same loader (:class:`FormalLLM.lean.task.LeanTask`). What used to differ was
everything around the loader: each script carried its own path and its own ``verina_`` prefix test. This module is the only place
that knows where a dataset lives, so a script takes ``--dataset NAME`` and nothing else changes:

    from FormalLLM.lean.dataset import get, resolve
    ds = get("humaneval")            # or "verina", "classic", "lean_specs" (humaneval + classic)
    ds.ids()                         # task ids, sorted
    task = ds.load("he_060_sum_to_n")
    ds.oracles()                     # {task id: hand-written derivation tree}
    ds.results_dir                   # benchmarks/results/<name>
    resolve("verina_basic_5")        # the dataset that owns an id, from its prefix

To add a dataset, add one :class:`Dataset` to :data:`REGISTRY`; nothing else needs to know.
"""
import importlib
import os
from dataclasses import dataclass
from typing import Dict, List, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HOME = os.path.join(os.path.expanduser("~"), ".formalllm")

VERINA_ROOT = os.environ.get("FORMALLLM_VERINA_DIR") or os.path.join(HOME, "verina", "datasets", "verina")
OWN_ROOT = os.path.join(ROOT, "benchmarks", "datasets", "lean_specs")
RESULTS = os.path.join(ROOT, "benchmarks", "results")


@dataclass(frozen=True)
class Dataset:
    name: str
    root: str                                   # the directory holding one sub-directory per task
    prefixes: Tuple[str, ...]                   # a task directory belongs to this dataset when its name starts with one
    oracle_module: str = ""                     # module whose ORACLES maps task id -> derivation tree
    results_name: str = ""                      # sub-directory of benchmarks/results (default: the dataset's name)
    description: str = ""
    input_encoding: str = "lean"                # how test.json writes inputs: "lean" (ours) or "json" (Verina's); see LeanTask
    compat: str = ""                            # Lean source defining names the task files use but this Lean has renamed

    # --- tasks ----------------------------------------------------------------------------------------------------

    def owns(self, task_id: str) -> bool:
        return task_id.startswith(self.prefixes)

    def ids(self) -> List[str]:
        if not os.path.isdir(self.root):
            return []
        return sorted(d for d in os.listdir(self.root)
                      if self.owns(d) and os.path.isfile(os.path.join(self.root, d, "task.json")))

    def path(self, task_id: str) -> str:
        return os.path.join(self.root, task_id)

    def load(self, task_id: str):
        from FormalLLM.lean.task import LeanTask
        task = LeanTask.from_dir(self.path(task_id), encoding=self.input_encoding)
        task.compat = self.compat
        return task

    def family(self, task_id: str) -> str:
        """``basic`` / ``advanced`` for Verina; the HumanEval problem number's hundred for ours; ``classic``."""
        parts = task_id.split("_")
        if task_id.startswith("verina_"):
            return parts[1]
        if task_id.startswith("he_"):
            return f"he_{int(parts[1]) // 20 * 20:03d}"
        return parts[0]

    # --- derivations ----------------------------------------------------------------------------------------------

    def oracles(self) -> Dict[str, dict]:
        """The hand-written derivations of this dataset's tasks (empty if there is no module)."""
        if not self.oracle_module:
            return {}
        table = importlib.import_module(self.oracle_module).ORACLES
        return {k: v for k, v in table.items() if self.owns(k)}

    # --- outputs --------------------------------------------------------------------------------------------------

    @property
    def results_dir(self) -> str:
        return os.path.join(RESULTS, self.results_name or self.name)

    def result_path(self, filename: str) -> str:
        os.makedirs(self.results_dir, exist_ok=True)
        return os.path.join(self.results_dir, filename)


#: Verina pins Lean 4.18 (4.24 for ``grind``); this project runs 4.34.1. Two constants its reference code uses were renamed.
#: Defining them again (same meaning) makes those tasks usable without editing any of Verina's files.
VERINA_COMPAT = """namespace Array
def mkArray {α : Type} (n : Nat) (v : α) : Array α := Array.replicate n v
end Array
namespace Std.HashSet
def empty {α : Type} [BEq α] [Hashable α] : Std.HashSet α := {}
end Std.HashSet"""

REGISTRY: Dict[str, Dataset] = {d.name: d for d in (
    Dataset("verina", VERINA_ROOT, ("verina_",), "benchmarks.datasets.verina_oracle",
            input_encoding="json", compat=VERINA_COMPAT,
            description="Verina (sunblaze-ucb/verina): 189 tasks, 108 basic and 81 advanced; clone it into ~/.formalllm/verina"),
    Dataset("humaneval", OWN_ROOT, ("he_",), "benchmarks.datasets.lean_oracle",
            description="HumanEval's 164 problems specified in Lean (benchmarks/datasets/lean_specs.py and he_lean/)"),
    Dataset("classic", OWN_ROOT, ("classic_",), "benchmarks.datasets.lean_oracle", results_name="classic",
            description="Five classic algorithms written for this project, among them the paper's square root"),
    Dataset("lean_specs", OWN_ROOT, ("he_", "classic_"), "benchmarks.datasets.lean_oracle", results_name="lean_specs",
            description="Everything we wrote: humaneval + classic"),
)}


def get(name: str) -> Dataset:
    try:
        return REGISTRY[name]
    except KeyError:
        raise KeyError(f"unknown dataset {name!r}; known: {', '.join(REGISTRY)}") from None


def resolve(task_id: str) -> Dataset:
    """The dataset that owns ``task_id`` (the most specific one: ``lean_specs`` is only a union)."""
    for name in ("verina", "humaneval", "classic"):
        if REGISTRY[name].owns(task_id):
            return REGISTRY[name]
    raise KeyError(f"no dataset owns task id {task_id!r}")


def names() -> List[str]:
    return list(REGISTRY)
