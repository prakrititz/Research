"""A cache of the prover's verdicts on obligations, shared by every run on this machine.

Runs prove the same obligations again and again (gold runs, ablations, repeated trials, a model that writes the same step
twice). The key is a hash of everything the verdict depends on: the lemma library and macros, the task's definitions, the
helper lemmas accepted so far, the obligation with the tactic that judged it (theorem names normalised), and the Lean
toolchain. A change to any of them is a different key, so an entry never goes stale; ``FORMALLLM_CACHE=0`` turns it off.

A cached "proved" is only a shortcut for the search: the finished derivation is still compiled from scratch in a fresh
process (``benchmarks/lspec_run.file_check``), so a wrong entry could never produce a wrong SOLVED. Timeouts are not
cached (they depend on the machine's load)."""
import hashlib
import json
import os
import sqlite3
import threading
from typing import Optional

VERSION = "1"
_LOCK = threading.Lock()
_CONN = None


def enabled() -> bool:
    return os.environ.get("FORMALLLM_CACHE", "1") != "0"


def _path() -> str:
    return os.environ.get("FORMALLLM_CACHE_PATH", os.path.join(os.path.expanduser("~"), ".formalllm", "cache",
                                                                "obligations.sqlite"))


def _conn():
    global _CONN
    if _CONN is None:
        path = _path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        _CONN = sqlite3.connect(path, timeout=30, check_same_thread=False)
        _CONN.execute("CREATE TABLE IF NOT EXISTS verdicts (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
        _CONN.commit()
    return _CONN


def _toolchain() -> str:
    try:
        from FormalLLM.lean.session import Toolchain
        path = os.path.join(Toolchain().project, "lean-toolchain")
        return open(path, encoding="utf8").read().strip()
    except Exception:
        return "?"


_TOOLCHAIN = None


def key(*parts: str) -> str:
    global _TOOLCHAIN
    if _TOOLCHAIN is None:
        _TOOLCHAIN = _toolchain()
    digest = hashlib.sha256()
    for part in (VERSION, _TOOLCHAIN) + parts:
        digest.update(part.encode("utf8"))
        digest.update(b"\x00")
    return digest.hexdigest()


def get(k: str) -> Optional[dict]:
    if not enabled():
        return None
    try:
        with _LOCK:
            row = _conn().execute("SELECT value FROM verdicts WHERE key = ?", (k,)).fetchone()
        return json.loads(row[0]) if row else None
    except (sqlite3.Error, ValueError):
        return None


def put(k: str, value: dict) -> None:
    if not enabled():
        return
    try:
        with _LOCK:
            _conn().execute("INSERT OR REPLACE INTO verdicts (key, value) VALUES (?, ?)", (k, json.dumps(value)))
            _conn().commit()
    except sqlite3.Error:
        pass
