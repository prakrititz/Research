"""Lean-native refinement: tasks written in Lean, laws that produce Lean obligations, Lean as the only judge.

The earlier engine (``FormalLLM/refinement``) works on its own specification language and asks Z3. This package keeps the
paper's method (a specification is refined by laws whose side conditions are proved) but states everything in Lean 4. A goal is the
subtype ``{ρ : T // post ρ}``; a derivation is a Lean term of that type; Lean checks the whole thing, so the result is a program
together with a proof that it meets the specification.

* ``session``   a managed Lean REPL (Mathlib imported once, a timeout on every command, kept environments);
* ``task``      a programming task = Lean definitions of the precondition and postcondition (Verina's file format);
* ``laws``      term, cases, bind and loop: each turns a goal into sub-goals and Lean obligations, and builds the Lean term;
* ``lemmas``    proved facts the tactic cascade may use (list and array members versus indices, a prefix plus one element);
* ``engine``    ``Derivation``: applies a law, has Lean prove its obligations, reports failures, certifies a finished derivation;
* ``dynamic``   counter-examples by running the loop on random inputs;
* ``agent``     a model-driven loop around the engine (prompt from Lean's own goal, feedback, withdrawing a failed step).

    python -m FormalLLM.lean show|check|oracle|solve ...       # command line, see ``__main__``

Design, measurements and open questions: ``Reading Material/22`` (log), ``23`` (design), ``24`` (the specification library).
"""
from FormalLLM.lean.engine import Certificate, Derivation, HelperLemma, Step, Verdict
from FormalLLM.lean.laws import Bind, Cases, Goal, IllFormed, Loop, Term, law_from_json
from FormalLLM.lean.session import DEFAULT_IMPORTS, FULL_IMPORTS, LeanReply, LeanSession, LeanUnavailable
from FormalLLM.lean.task import LeanTask

__all__ = ["Bind", "Cases", "Certificate", "DEFAULT_IMPORTS", "Derivation", "FULL_IMPORTS", "Goal", "HelperLemma", "IllFormed",
           "LeanReply", "LeanSession", "LeanTask", "LeanUnavailable", "Loop", "Step", "Term", "Verdict", "law_from_json"]
