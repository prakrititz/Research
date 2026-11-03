"""Probe a dumped obligation (dump_exact.py): run each top-level alternative of its cascade's `first | ...` separately, on
each goal, under the cascade's heartbeat budget; log time and closed / failed / resource limit per alternative.
    python probe.py <dumped.lean> <out.lean>"""
import json, re, sys

src = open(sys.argv[1], encoding="utf8").read()
head, _, obl = src.rpartition("set_option maxHeartbeats 200000 in\n")
stmt, _, tactic = obl.partition(":= by\n")
tactic = tactic.strip()


def split_top(t, sep=" | "):
    parts, depth, cur, k = [], 0, "", 0
    while k < len(t):
        ch = t[k]
        depth += ch in "([{"
        depth -= ch in ")]}"
        if depth == 0 and t.startswith(sep, k):
            parts.append(cur); cur = ""; k += len(sep); continue
        cur += ch; k += 1
    return parts + [cur]


# `(try dsimp only at *); (repeat' apply And.intro); all_goals (first | A | B | ...)` then possibly `| more` groups
m = re.match(r"(.*?all_goals \()first \| (.*)\)\s*$", tactic, re.S)
prefix, body = m.group(1)[:-len("all_goals (")], m.group(2)
alts = [a.strip() for a in split_top(body)]
# an alternative of the form `first | x) | (y` would be broken by the regex; keep it simple: report what we got
probe = r'''
open Lean Elab Tactic Meta in
elab "probe_alts" alts:str* : tactic => do
  let goals ← getGoals
  let mut g : Nat := 0
  for goal in goals do
    let mut k : Nat := 0
    for a in alts do
      setGoals [goal]
      let saved ← saveState
      let t0 ← IO.monoMsNow
      let r ← tryCatchRuntimeEx
        (do withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000 * 1000 }) <|
              focusAndDone (Refine.runText a.getString)
            pure "CLOSED")
        (fun e => do pure s!"fail: {((← e.toMessageData.toString).replace "\n" " ").take 160}")
      saved.restore
      logInfo m!"goal {g} alt {k} ({(← IO.monoMsNow) - t0} ms): {r}"
      k := k + 1
    g := g + 1
  for goal in goals do goal.admit
  setGoals []
'''
lits = " ".join(json.dumps(a, ensure_ascii=False) for a in alts)
with open(sys.argv[2], "w", encoding="utf8") as f:
    f.write(head + probe + "\nset_option maxHeartbeats 0 in\n" + stmt + ":= by\n  " + prefix + "probe_alts " + lits + "\n")
for k, a in enumerate(alts):
    print(k, a[:110])
