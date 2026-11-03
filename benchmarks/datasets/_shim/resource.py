"""Windows stand-in for the Unix-only ``resource`` module.

EvalPlus' sandbox (``evalplus.eval.utils.reliability_guard``) calls
``resource.setrlimit`` to cap memory.  Windows has no ``resource`` module, so
without this file every EvalPlus check crashes in the child process and is
reported as a timeout.

This file is put on ``sys.path`` (at the END, so it can never shadow the real
module) by ``benchmarks/datasets/humaneval.py`` and only when ``import
resource`` fails.  ``multiprocessing`` on Windows uses *spawn* and forwards the
parent's ``sys.path`` to the child, which is why a real file is needed rather
than an entry in ``sys.modules``.

Effect: the memory limit is NOT enforced on Windows (the time limit is).  Run
under WSL/Linux for the full sandbox.
"""

RLIMIT_AS = 9
RLIMIT_DATA = 2
RLIMIT_STACK = 3
RLIM_INFINITY = -1


def setrlimit(*_args, **_kwargs):  # noqa: D401 - deliberate no-op
    return None


def getrlimit(*_args, **_kwargs):
    return (RLIM_INFINITY, RLIM_INFINITY)
