"""The engine's lemma library compiled into a module of the Lean project (``LeanEnv/RefineLib.lean``), shared by the
fresh-process check (each task's file imports it instead of elaborating ~140k characters) and by the REPL (a restarted
REPL imports it instead of elaborating the library again: ``LeanSession.library_env``).

The module is rebuilt by ``lake build`` only when the library text changes; Lean's kernel checks it when it is built, and
``#print axioms`` follows dependencies across modules, so a check that imports it is as strict as one that spells it out."""
import os
import subprocess
from typing import Dict, Optional

MODULE = "LeanEnv.RefineLib"
_BUILT: Dict[int, Optional[str]] = {}


def ensure(lemmas: str) -> Optional[str]:
    """The module's name once it is built with exactly ``lemmas`` (after ``FULL_IMPORTS``); ``None`` if it does not build
    (callers then send the library text as before)."""
    from FormalLLM.lean.session import FULL_IMPORTS, Toolchain, short_path
    text = f"{FULL_IMPORTS}\n{lemmas}\n"
    key = hash(text)
    if key in _BUILT:
        return _BUILT[key]
    tool = Toolchain()
    package = MODULE.split(".")[0]
    lakefile = os.path.join(tool.project, "lakefile.toml")
    try:
        lakefile_text = open(lakefile, encoding="utf8").read() if os.path.exists(lakefile) else ""
        if os.path.exists(lakefile) and f'name = "{package}"' not in lakefile_text:
            # a Lean project made before the module existed has no library target to build it in: add one
            with open(lakefile, "a", encoding="utf8", newline="\n") as handle:
                handle.write(f'\n[[lean_lib]]\nname = "{package}"\n')
        path = os.path.join(tool.project, *MODULE.split(".")) + ".lean"       # LeanEnv/RefineLib.lean
        os.makedirs(os.path.dirname(path), exist_ok=True)
        old = open(path, encoding="utf8").read() if os.path.exists(path) else None
        if old != text:                                   # unchanged text keeps lake's trace: no rebuild
            with open(path, "w", encoding="utf8", newline="\n") as handle:
                handle.write(text)
        done = subprocess.run([tool.lake, "build", MODULE], cwd=short_path(tool.project), env=tool.env(),
                              capture_output=True, text=True, encoding="utf8", timeout=3600)
        _BUILT[key] = MODULE if done.returncode == 0 else None
        if done.returncode != 0:
            print("the library module did not build; the library text is sent instead:",
                  ((done.stdout or "") + (done.stderr or ""))[-300:], flush=True)
    except (subprocess.TimeoutExpired, OSError) as error:
        print(f"the library module did not build ({error}); the library text is sent instead", flush=True)
        _BUILT[key] = None
    return _BUILT[key]
