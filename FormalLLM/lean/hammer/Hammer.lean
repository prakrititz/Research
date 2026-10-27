import Mathlib
import Duper
import Duper.TPTP

/-!
# `refine_hammer`: a CoqHammer-style hammer for proof obligations

1. premise selection: Lean's library-suggestions engine (Sine Qua Non), re-ranked by symbol overlap with the goal;
2. external prover: lean-auto translates goal + hypotheses + premises to TPTP and Zipperposition searches for a
   proof; its proof names the facts it used;
3. reconstruction: Duper (else `grind`) re-proves the original goal from just those facts inside Lean, so the
   kernel checks every proof. Nothing from the external prover is trusted.

This is LeanHammer's design (Zipperposition for the search, Duper for the proof); `duper_hammer` skips step 2.
-/

open Lean Elab Tactic Meta

namespace Refine

/-- The library facts behind the last facts lean-auto handed to its native prover. -/
initialize usedFacts : IO.Ref (Option (Array String)) ← IO.mkRef none

/-- The library names in a lean-auto derivation (user facts are recorded as leaves `❰name❱`). -/
partial def factNames : Auto.DTr → Array String
  | .leaf s =>
    -- lean-auto prints an identifier hint as syntax, with a leading backtick
    if s.startsWith "❰" && s.endsWith "❱" then #[String.ofList (((s.toList.drop 1).dropLast).dropWhile (· == '`'))]
    else #[]
  | .node _ children => children.foldl (fun acc c => acc ++ factNames c) #[]

end Refine

/-- lean-auto's native prover, rebound: after Zipperposition's search it receives the facts the proof used (premise
selection by unsat core); record their names and stop, so that the proof is rebuilt on the original goal. -/
@[rebind Auto.Native.solverFunc]
def Refine.recordUsedFacts (lemmas _inhLemmas : Array Auto.Lemma) : MetaM Expr := do
  let names := lemmas.foldl (fun acc l => acc ++ (Refine.factNames l.deriv).filter (!acc.contains ·)) #[]
  Refine.usedFacts.set (some names)
  throwError "refine_hammer: facts recorded"

namespace Refine

/-- A statement lean-auto can use: no induction motive and no quantifier over `Sort u` (which includes `Prop`);
type variables `α : Type u` and predicates `p : α → Prop` are fine (lean-auto instantiates and translates them). -/
def firstOrder (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs _ => xs.allM fun x => do
    let t ← inferType x
    if (← x.fvarId!.getUserName).toString.startsWith "motive" then return false
    match (← whnf t) with
    | .sort u => return u.dec.isSome
    | _ => return true

def runText (text : String) : TacticM Unit := do
  match Parser.runParserCategory (← getEnv) `tactic text with
  | .ok stx => evalTactic stx
  | .error e => throwError "refine_hammer: could not parse {text}: {e}"

/-- Premises already checked in this session: `true` when lean-auto's preprocessing accepts them. -/
initialize translatableCache : IO.Ref (NameMap Bool) ← IO.mkRef {}

/-- Whether lean-auto can translate this premise (some statements, e.g. with `∃ x ∈ l` binders or an induction motive,
fail its monomorphisation, and one such premise sinks the whole call). Checked once, with no prover run. -/
def translatable (name : Name) : TacticM Bool := do
  if let some ok := (← translatableCache.get).find? name then return ok
  let saved ← saveState
  let ok ← try
      runText s!"set_option auto.tptp false in set_option auto.native false in auto [{name}]"
      pure true
    catch e => pure ((← e.toMessageData.toString).startsWith "Auto failed")
  saved.restore
  translatableCache.modify (·.insert name ok)
  return ok

/-- The names of the `n` library facts most relevant to the main goal, as hint text. -/
def premiseHints (n : Nat) : TacticM String := do
  let goal ← getMainGoal
  -- Sine Qua Non is fast but ranks hundreds of candidates equally (then by name), so the pool is taken wide and re-ranked
  let suggestions ← Lean.LibrarySuggestions.select goal { maxSuggestions := 1500 }
  let self? ← Term.getDeclName?
  -- the symbols of the goal and its hypotheses
  let mut wanted : NameSet := (← instantiateMVars (← goal.getType)).getUsedConstantsAsSet
  for d in (← getLCtx) do
    if !d.isImplementationDetail then
      wanted := wanted.append (← instantiateMVars d.type).getUsedConstantsAsSet
  -- only theorems, whose statements lean-auto can translate; one recursor or definition in the list sinks the whole call
  let mut scored : Array (Float × Name) := #[]
  for s in suggestions do
    if self? == some s.name || s.name.isInternalDetail then continue
    let some (.thmInfo info) := (← getEnv).find? s.name | continue
    unless ← firstOrder info.type do continue
    -- relevance: shared symbols, discounted by symbols the goal does not mention (Sledgehammer's MePo idea)
    let used := info.type.getUsedConstants
    let shared := (used.filter wanted.contains).size.toFloat
    let foreign := (used.filter (!wanted.contains ·)).size.toFloat
    scored := scored.push (shared / (1.0 + foreign), s.name)
  let ranked := scored.qsort (fun a b => a.1 > b.1)
  let mut chosen : Array Name := #[]
  for (_, name) in ranked do
    if chosen.size ≥ n then break
    if !chosen.contains name && (← translatable name) then
      chosen := chosen.push name
  return ", ".intercalate (chosen.toList.map toString)


/-- `zipwrap` (this project's `ZipWrap.lean`): Zipperposition under a time limit that also works on Windows. -/
def zipwrap : IO String := do
  let exe := if System.Platform.isWindows then "zipwrap.exe" else "zipwrap"
  return ((← IO.currentDir) / ".lake" / "build" / "bin" / exe).toString.replace "\\" "/"

def hintList (hints : String) : String :=
  if hints.isEmpty then "*" else s!"*, {hints}"

syntax (name := refineHammer) "refine_hammer" (ppSpace num)? : tactic
syntax (name := duperHammer) "duper_hammer" (ppSpace num)? : tactic

/-- Whether Zipperposition reported a proof in the traces collected since `start`. -/
def provedSince (start : Nat) : CoreM Bool := do
  let traces := (← getTraceState).traces.toArray
  traces[start:].toArray.anyM fun t => return ((← t.msg.toString).splitOn "SZS status Unsatisfiable").length ≥ 2

@[tactic refineHammer] def evalRefineHammer : Tactic := fun stx => withMainContext do
  let n := (stx[1].getOptional?.map (·.isNatLit?.getD 16)).getD 16
  let hints ← premiseHints n
  usedFacts.set none
  let saved ← saveState
  let oldTraces ← getTraceState
  let start := oldTraces.traces.size
  try
    runText s!"set_option auto.tptp true in set_option auto.tptp.premiseSelection true in       set_option auto.tptp.zipperposition.useDefault false in       set_option auto.tptp.zipperposition.customPath \"{← zipwrap}\" in       set_option trace.auto.tptp.result true in       set_option auto.native true in set_option auto.tptp.timeout 10 in auto [{hintList hints}]"
  catch _ => pure ()
  let proved ← provedSince start
  saved.restore
  modifyTraceState fun _ => oldTraces
  let some used ← usedFacts.get | throwError "refine_hammer: lean-auto could not translate the goal"
  unless proved do throwError "refine_hammer: Zipperposition found no proof"
  let facts := ", ".intercalate used.toList
  let grind := if used.isEmpty then "grind" else s!"grind [{facts}]"
  runText s!"first | duper [{hintList facts}] | {grind}"

@[tactic duperHammer] def evalDuperHammer : Tactic := fun stx => withMainContext do
  let n := (stx[1].getOptional?.map (·.isNatLit?.getD 16)).getD 16
  let hints ← premiseHints n
  runText s!"duper [{hintList hints}]"

end Refine
