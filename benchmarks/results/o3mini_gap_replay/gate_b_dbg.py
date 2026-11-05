"""gate_b.py with the falsifier's input and Lean reply logged (to SMALLSCOPE_LOG)."""
import os, runpy, sys
sys.path.insert(0, sys.argv[1])
from FormalLLM.lean import engine as E, smallscope
log = open(os.environ["SMALLSCOPE_LOG"], "a", encoding="utf8")
def _small_scope(self, obligation):
    source = smallscope.falsifier(obligation.binders, obligation.statement)
    log.write(f"=== {obligation.description}\nBINDERS {obligation.binders}\nSTATEMENT {obligation.statement}\nSOURCE {source}\n")
    if source is None:
        return None
    reply = self._run(source, timeout=60.0)
    log.write(f"TIMED_OUT {reply.timed_out}\nERRORS {reply.errors[:2]}\nINFOS {reply.infos[:2]}\n"); log.flush()
    if reply.timed_out or reply.errors:
        return None
    found = smallscope.parse("\n".join(reply.infos))
    return f"the statement is false for {found}" if found else None
E.Derivation._small_scope = _small_scope
runpy.run_path(os.path.join(os.path.dirname(__file__), "gate_b.py"), run_name="__main__")
