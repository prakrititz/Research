"""The registry: every name and operator of L_spec, with its Lean counterpart. One row per entry; the parser, the printers
and the prompt's cheat sheet are all generated from these tables, so adding an operation is adding a row.

Precedences are Lean's (``lean_syntax.INFIX``): L_spec changes how an operator is spelled, never how it groups, so a
tree prints back to the same Lean."""

#: Lean operator -> L_spec spelling (operators not listed are spelled as in Lean: `+ - * / % < > ++ ::`; a product
#: type `A × B × C` is written `tuple[A, B, C]`)
BINOPS = {
    "∧": "and", "∨": "or", "→": "==>", "↔": "<==>", "=": "==", "≠": "!=", "≤": "<=", "≥": ">=",
    "∈": "in", "∉": "not in", "^": "**", "==": "===", "!=": "!==",
    "∣": "divides", "<:+:": "is_infix", "^^^": "xor",
}
UNOPS = {"¬": "not", "!": "!", "-": "-", "↑": "↑", "~~~": "~~~"}

#: Lean global (a constant, function or type) -> L_spec name
NAMES = {
    "true": "True", "false": "False", "True": "true_prop", "False": "false_prop",     # Bool values; propositions
    "Nat": "nat", "ℕ": "nat", "Int": "int", "ℤ": "int", "Bool": "bool", "Char": "char", "String": "str",
    "List": "list", "Array": "array", "Option": "option", "Rat": "rat", "ℚ": "rat", "Float": "float", "Prop": "prop",
    "List.range": "range", "String.mk": "string", "Int.ofNat": "int_of_nat",
    "Nat.Prime": "is_prime", "Nat.toDigits": "digits", "Nat.sqrt": "isqrt", "Nat.gcd": "gcd", "Int.toNat": "to_nat_of",
    "List.Pairwise": "pairwise", "List.foldl": "foldl", "List.elem": "elem", "List.isPerm": "is_perm",
    "String.singleton": "string1", "List.replicate": "replicate",
}

#: a type name that, applied, is a conversion (as in Python): `bool` is `Bool` and `bool(p)` is `decide p`; `str` is
#: `String` and `str(x)` is `toString x`
CALL_NAMES = {"decide": "bool", "toString": "str"}

#: Lean method (`x.f`) written as a function in L_spec: `x.length` -> `len(x)`, `l.mergeSort c` -> `sorted(l, c)`
METHOD_FUNCS = {
    "length": "len", "size": "size", "toList": "list", "sum": "sum", "prod": "product", "reverse": "reversed",
    "mergeSort": "sorted", "toNat": "to_nat", "natAbs": "abs_nat", "dedup": "dedup", "toArray": "array_of",
}
#: Lean method renamed but still a method: `l.idxOf x` -> `l.index(x)`
METHODS = {"idxOf": "index", "headD": "head_or", "getD": "get_or", "flatMap": "flat_map", "countP": "count_if",
           # Python's string and character methods (`sep.join(l)` is `sep.intercalate l`; `s.split(",")` splits on ",")
           "intercalate": "join", "splitOn": "split", "startsWith": "startswith", "endsWith": "endswith", "trim": "strip",
           "toUpper": "upper", "toLower": "lower", "isDigit": "isdigit", "isAlpha": "isalpha", "isUpper": "isupper",
           "isLower": "islower", "isWhitespace": "isspace"}

#: method spellings from other languages, read as the L_spec method (`l.indexOf(x)` is `l.index(x)`, `l.sort()` is
#: `sorted(l)`); only read, never printed
METHOD_ALIASES = {"indexOf": "idxOf", "sort": "mergeSort", "toUpperCase": "toUpper", "toLowerCase": "toLower"}

#: L_spec reserved words (an L_spec name that would collide with one of these is written `` `name` ``)
KEYWORDS = {"lambda", "forall", "exists", "if", "else", "let", "match", "with", "and", "or", "not", "in", "as", "for", "then", "implies",
            "divides", "is_infix", "xor"}


def _inverse(table):
    out = {}
    for lean, spec in table.items():
        out.setdefault(spec, lean)                 # `nat` reads back as `Nat` (the first listed), not `ℕ`
    return out


BINOPS_INV = _inverse(BINOPS)
UNOPS_INV = _inverse(UNOPS)
NAMES_INV = _inverse(NAMES)
METHOD_FUNCS_INV = _inverse(METHOD_FUNCS)
METHODS_INV = _inverse(METHODS)
CALL_NAMES_INV = _inverse(CALL_NAMES)
#: every name L_spec gives a meaning to: a Lean name equal to one of these is escaped when printed
RESERVED = set(NAMES_INV) | set(METHOD_FUNCS_INV) | KEYWORDS | {"floor", "ceil", "floor_nat", "ceil_nat", "abs", "tuple"}
