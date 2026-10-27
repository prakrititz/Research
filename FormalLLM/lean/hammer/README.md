# External hammer (`refine_hammer`)

The counterpart of the paper's CoqHammer: premise selection, an external prover, and a proof rebuilt in Lean.

1. Premise selection: Lean's Sine Qua Non suggestions, re-ranked by symbol overlap with the goal.
2. Search: lean-auto translates the goal to TPTP, and Zipperposition looks for a proof.
3. Reconstruction: Duper (else `grind`) re-proves the original goal from only the facts that proof used.

The Lean kernel checks every proof. Nothing from Zipperposition is trusted.

## Setup

Make a copy of the Lean project `~/.formalllm/lean-env-parent/lean-env` as `lean-env-hammer`. Then:

1. Use `lakefile.toml` from this folder. It adds Duper v4.34.1 (which brings lean-auto) and the `zipwrap` executable.
2. Copy `Hammer.lean` to `LeanEnv/Hammer.lean` and `ZipWrap.lean` to the project root.
3. Run `lake update Duper`. Building lean-auto downloads Zipperposition 2.1.
4. Apply `lean-auto-windows-kill.patch` inside `.lake/packages/auto`, and `hide-placeholder-axioms.patch` inside
   `.lake/packages`. The second hides three axioms that prove any goal (`Duper.skSorryAx`, `autoTPTPSorry`,
   `autoSMTSorry`) from library search; otherwise `try?` closes goals with them.
5. Run `lake build LeanEnv.Hammer zipwrap`.
6. Run with:

   ```
   FORMALLLM_LEAN_PROJECT=~/.formalllm/lean-env-parent/lean-env-hammer
   FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer"
   ```

   The engine then adds `refine_hammer` as its last prover stage (`ATP` in `engine.py`).

## Windows fixes

- `zipwrap` works around two problems in Zipperposition's Windows build:
  - its `-t` time limit uses a Unix signal (`Sys.signal: unavailable signal`), so `zipwrap` enforces the limit itself;
  - it writes CRLF line endings, which lean-auto's parser rejects, so `zipwrap` strips them.
- The patch handles lean-auto killing a prover that has already exited. On Windows that fails with error 5 (access denied), and the bare "5" used to abort every call.
