/-!
`zipwrap`: runs Zipperposition with lean-auto's arguments, minus `-t=N`, and enforces that time limit itself.

The Windows build of Zipperposition implements `-t` with a Unix alarm signal and stops with
`Sys.signal: unavailable signal`; without `-t` it proves normally but may never return, so the limit
is kept here: after N seconds (plus one) the prover is killed and whatever it printed is passed on.
It also ends lines with CRLF, which lean-auto's TPTP parser rejects, so line ends are normalised.
-/

def zipperposition : System.FilePath :=
  ".lake" / "packages" / "auto" / ".lake" / "build" / "zipperposition.exe"

/-- Write the problem to the prover; the stdin handle is dropped on return, which closes it (end of input). -/
def feed (child : IO.Process.Child ⟨.piped, .piped, .null⟩) (input : String) :
    IO (IO.Process.Child ⟨.null, .piped, .null⟩) := do
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  return child

def main (args : List String) : IO UInt32 := do
  let limit := (args.findSome? (fun a =>
    if a.startsWith "-t=" then (String.ofList (a.toList.drop 3)).toNat? else none)).getD 10
  let exe ← match (← IO.getEnv "FORMALLLM_ZIPPERPOSITION") with
    | some path => pure (System.FilePath.mk path)
    | none => pure ((← IO.appDir) / ".." / ".." / ".." / zipperposition)
  let input ← (← IO.getStdin).readToEnd
  let child ← IO.Process.spawn { cmd := exe.toString, args := (args.filter (!·.startsWith "-t=")).toArray,
                                 stdin := .piped, stdout := .piped, stderr := .null }
  let child ← feed child input
  -- read the output on its own thread, so a long proof never fills the pipe while we wait
  let output ← IO.asTask child.stdout.readToEnd .dedicated
  let deadline := (← IO.monoMsNow) + (limit + 1) * 1000
  let mut finished := false
  while !finished do
    if (← child.tryWait).isSome then
      finished := true
    else if (← IO.monoMsNow) > deadline then
      child.kill
      finished := true
    else
      IO.sleep 50
  match ← IO.wait output with
  | .ok text => IO.print (String.ofList (text.toList.filter (· != '\r')))
  | .error _ => pure ()
  return 0
