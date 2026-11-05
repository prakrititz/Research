# smallscope: the bound is a natural number written out (Decidable needs the type at elaboration), a `∀` already bounded
# is left alone, and `_precond`/`_postcond` definitions are unfolded for instance search
import sys
p = sys.argv[1]
s = open(p, encoding="utf-8", newline="").read()
nl = "\r\n" if "\r\n" in s else "\n"
s = s.replace("\r\n", "\n")

old = '''    if m:
        names = m.group(1).split()
        return f"∀ {' '.join(names)}{' : ℕ' if m.group(2) else ''}, " + "".join(f"{n} < {BOUND} → " for n in names) + \
            "(" + t[m.end():].strip() + ")"
'''
assert old in s
s = s.replace(old, '''    if m:
        names, body = m.group(1).split(), t[m.end():].strip()
        # `∀ i, i < n → ...` or `∀ x, x ∈ l → ...` is decidable as it stands (and `x` need not be a number)
        if re.match(r"\(?\s*" + re.escape(names[0]) + r"\s*(<|≤|∈)", body):
            return t
        # the type written out: `∀ d, d < 4 → ...` leaves it to numeral defaulting, after instance search has failed
        return f"∀ {' '.join(names)} : ℕ, " + "".join(f"{n} < {BOUND} → " for n in names) + "(" + body + ")"
''', 1)

old = '''    lines, ind = [], "    "
    for n, typ, values in data:'''
assert old in s
s = s.replace(old, '''    # `h_precond : f_precond a b` (and a postcondition in the statement) is decidable once its definition unfolds
    defs = sorted(set(_SPEC_DEF.findall(binders + " " + statement)))
    unfold = (f"set_option allowUnsafeReducibility true in\nattribute [local reducible] {' '.join(defs)} in\n"
              if defs else "")
    lines, ind = [], "    "
    for n, typ, values in data:''', 1)

old = '''    return (f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"'''
assert old in s
s = s.replace(old, '''    return (unfold + f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"''', 1)

old = '''_WEAK = "→↔∨¬∀∃λ"
'''
assert old in s
s = s.replace(old, old + '''_SPEC_DEF = re.compile(r"\b(\w+_(?:precond|postcond))\b")
''', 1)
open(p, "w", encoding="utf-8", newline="").write(s.replace("\n", nl))
