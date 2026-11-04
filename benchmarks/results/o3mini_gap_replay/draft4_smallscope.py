# applies the bounded-forall weakening to smallscope.py (run after the replay: each replay round reloads the code)
import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()

anchor = '''def falsifier(binders: str, statement: str) -> Optional[str]:'''
assert anchor in s
s = s.replace(anchor, '''#: ``∀ d, P d`` (a goal, or a conjunct of one) has no ``Decidable`` instance; ``∀ d, d < 4 → P d`` has one when ``d`` is a
#: natural number, and is implied by it: where the bounded form is false, so is the goal (he_013's invariant
#: ``∀ d, d > 0 → (a % d = 0 ∧ b % d = 0) ↔ ...``, which reads ``(d > 0 → ...) ↔ ...``, fails at ``d = 0``). A binder of
#: another type makes the command fail to elaborate, and the falsifier reports nothing, as before.
BOUND = 4
_FORALL = re.compile(r"∀\\s*\\(?\\s*((?:\\w+\\s*)+?)\\s*(:\\s*(?:ℕ|Nat)\\s*)?\\)?\\s*,")
_WEAK = "→↔∨¬∀∃λ"


def _bounded(t: str) -> str:
    t = _strip(t)
    m = _FORALL.match(t)
    if m:
        names = m.group(1).split()
        return f"∀ {' '.join(names)}{' : ℕ' if m.group(2) else ''}, " + "".join(f"{n} < {BOUND} → " for n in names) + \\
            "(" + t[m.end():].strip() + ")"
    parts = _split_top(t, "∧")
    depth, top = 0, ""
    for ch in t:
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            top += ch
    # only a plain conjunction: under `→`, `↔`, `∨` or `¬` the weakening would not be implied by the goal
    if len(parts) > 1 and not any(c in top for c in _WEAK):
        return " ∧ ".join("(" + _bounded(q) + ")" for q in parts)
    return t


''' + anchor, 1)

old = '''    binders, statement = _decidable_form(binders), _decidable_form(statement)
    parsed = _binders(binders)
    if not parsed:
        return None
    text = binders + " " + statement
'''
assert old in s
s = s.replace(old, '''    binders, statement = _decidable_form(binders), _decidable_form(statement)
    parsed = _binders(binders)
    if not parsed:
        return None
    text = binders + " " + statement          # the domains: from the statement as written, not the bound
    statement = _bounded(statement)
''', 1)
open(p, "w", encoding="utf-8").write(s)
