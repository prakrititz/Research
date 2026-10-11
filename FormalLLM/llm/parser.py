import json
import re
from typing import Tuple, Dict, Any

from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.laws.registry import law_named


# L_spec writes conjunction as /\ and disjunction as \/. Inside a JSON string a
# single backslash starts an escape, so a model that writes "a /\ b" without
# doubling the backslash sends us `/` followed by a newline (from \n) or `/"`
# (from \"). The result is a parse error that says nothing about whether the
# model chose a sensible refinement. Measured on qwen3.5 against the sqrt
# specification: 3 of its 4 proposals were destroyed this way.
#
# These aliases contain no backslash, so they survive JSON intact. They are a
# convenience of the model-facing parser only; L_spec itself is unchanged and
# still accepts /\ and \/.
#
# The word forms are anchored with \b so an identifier that merely contains one
# -- band, x_or_y, nota -- is left alone. Replacements are plain (non-raw)
# strings because re.sub reads a backslash in the replacement as a group
# reference.
# Quantifier binders as models usually write them: `forall k:int body`, `forall k body`, `forall (k) body`,
# `forall k:int. body`, `exists (k:int), body`. L_spec's own form is `forall (k:int) body`.
_BINDER = re.compile(r"\b(forall|exists)\b\s*\(?\s*([A-Za-z_]\w*)\s*"
                     r"(?::\s*(int|nat|bool|float|char|array\s+(?:int|nat|bool|float|char)))?\s*\)?\s*[.,]?")
_QUANTIFIER_WORD = re.compile(r"\b(forall|exists)\b")


def normalise_binders(text: str) -> str:
    """Rewrite ``forall k:int ...`` and similar spellings as ``forall (k:int) ...``."""
    def fix(match):
        type_text = " ".join((match.group(3) or "int").split())
        return f"{match.group(1)} ({match.group(2)}:{type_text}) "
    return _BINDER.sub(fix, text)


def syntax_hint(text: str) -> str:
    """What to tell a model whose formula did not parse, when the usual cause is known."""
    hints = []
    if _QUANTIFIER_WORD.search(text):
        hints.append("A quantifier is written  forall (k:int) formula  or  exists (k:int) formula: the binder in "
                     "parentheses, then the formula, with no colon, dot or comma after the binder.")
    if re.search(r"->|=>|<=>|\bimplies\b|\biff\b", text):
        hints.append("There is no implication operator (-> => implies). Write 'A implies B' as !(A) || B.")
    return " ".join(hints)


OPERATOR_ALIASES = (
    (r"==", "="),
    (r"!=", "<>"),             # before the `!` rule below
    (r"&&", "/\\\\"),
    (r"\|\|", "\\\\/"),
    (r"\band\b", "/\\\\"),
    (r"\bor\b", "\\\\/"),
)

# `!` and `not` are handled by _wrap_negations below, not by a plain rewrite.
# L_spec's `~` extends as far right as it can (`~a /\ b` is `~(a /\ b)`), so
# turning `!(x < 0) && y > 1` into `~(x < 0) /\ y > 1` silently changed its
# meaning to "not both". Each negation is wrapped as `(~operand)` instead.
_NEGATION = re.compile(r"!(?!=)|\bnot\b")
_OPERAND = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\[[^\]]*\])?|-?\d+(?:\.\d+)?")


def _wrap_negations(text: str) -> str:
    """Rewrite ``!X`` / ``not X`` as ``(~X)`` so ``~`` binds to ``X`` only."""
    while True:
        matches = list(_NEGATION.finditer(text))
        if not matches:
            return text
        m = matches[-1]                      # innermost/rightmost first
        i = m.end()
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text):
            return text                      # dangling: let the parser reject it
        if text[i] == "(":
            depth, j = 0, i
            while j < len(text):
                if text[j] == "(":
                    depth += 1
                elif text[j] == ")":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
            else:
                return text                  # unbalanced: let the parser reject it
        else:
            mm = _OPERAND.match(text, i)
            if not mm:
                return text
            j = mm.end()
        text = text[:m.start()] + f"(~{text[i:j]})" + text[j:]

# `/` immediately followed by a newline, carriage return, tab or quote: what an
# undoubled /\ becomes once JSON has decoded the escape.
_MANGLED = re.compile("/[\n\r\t\"]")


def normalise_operators(expr_str: str) -> str:
    """Rewrite backslash-free operator spellings into L_spec syntax."""
    for pattern, replacement in OPERATOR_ALIASES:
        expr_str = re.sub(pattern, replacement, expr_str)
    return _wrap_negations(normalise_binders(expr_str))


def looks_json_mangled(expr_str: str) -> bool:
    """True if this expression carries the signature of an unescaped ``/\\``.

    Reported rather than silently repaired: dividing by a parenthesised
    comparison is meaningless, so this is almost certainly a lost operator, but
    guessing the author's intent is worse than telling them what went wrong and
    which spelling avoids it.
    """
    return bool(_MANGLED.search(expr_str))


def parse_expr(expr_str: str):
    if looks_json_mangled(expr_str):
        raise ValueError(
            "this expression looks like a conjunction whose backslash was "
            "eaten by JSON escaping. Use && for /\\ and || for \\/ -- they "
            f"need no backslash and survive JSON intact. Got: {expr_str!r}"
        )
    expr_str = normalise_operators(expr_str)
    # Wrap the expression in a dummy specification to parse it using the existing grammar
    dummy_spec_str = f"Precondition: := {expr_str}.\nPostcondition: := true."
    try:
        spec = parse_spec(dummy_spec_str)
    except Exception as error:
        hint = syntax_hint(expr_str)
        if not hint:
            raise
        raise ValueError(f"{error}\n{hint}") from error
    return spec.precondition.expr


def _load_json_key(text: str, key: str) -> Dict[str, Any]:
    """Parse the reply as JSON, or recover the JSON object embedded in prose.

    A reasoning model can spend its whole token budget thinking and return an
    empty `content`, in which case the provider falls back to the reasoning
    channel -- which is prose with the answer somewhere inside it. Rather than
    score that as a malformed reply, find the first balanced {...} that parses
    and has a specific key.
    """
    try:
        candidate = json.loads(text)
        if isinstance(candidate, dict) and key in candidate:
            return candidate
    except json.JSONDecodeError:
        pass

    for start in (i for i, ch in enumerate(text) if ch == "{"):
        depth, in_str, escaped = 0, False, False
        for end in range(start, len(text)):
            ch = text[end]
            if in_str:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    try:
                        candidate = json.loads(text[start:end + 1])
                    except json.JSONDecodeError:
                        break
                    if isinstance(candidate, dict) and key in candidate:
                        return candidate
                    break
                    
    # Tolerant Fallback: The JSON might be truncated mid-rationale.
    # Since we moved "law" and "parameters" to the top of the prompt schema, 
    # the data we care about should already be fully formed.
    import re
    if key == "law":
        # Extract "law": "some_law_name"
        match = re.search(r'"law"\s*:\s*"([^"]+)"', text)
        if match:
            return {"law": match.group(1)}
    elif key == "parameters":
        # Extract "parameters": { ... } by finding the start and counting braces
        match = re.search(r'"parameters"\s*:\s*\{', text)
        if match:
            start_idx = match.end() - 1  # Index of the opening '{'
            depth, in_str, escaped = 0, False, False
            for i in range(start_idx, len(text)):
                ch = text[i]
                if in_str:
                    if escaped: escaped = False
                    elif ch == "\\": escaped = True
                    elif ch == '"': in_str = False
                else:
                    if ch == '"': in_str = True
                    elif ch == "{": depth += 1
                    elif ch == "}":
                        depth -= 1
                        if depth == 0:
                            # We found the matching closing brace!
                            try:
                                params_dict = json.loads(text[start_idx:i+1])
                                return {"parameters": params_dict}
                            except json.JSONDecodeError:
                                break
                            
    raise ValueError(
        f'no JSON object with a "{key}" key found in the reply: {text[:200]!r}'
    )

def _load_json(text: str) -> Dict[str, Any]:
    return _load_json_key(text, "law")


# Keys a model may use for a law's parameters instead of the declared names.
# Measured: given the schema example {"invariant": "I", "guard": "G", "variant":
# "V"}, gpt-oss-120b answered with the keys "I", "G", "V" -- a correct loop that
# was discarded because the parser demanded the exact spelling. Matching is
# case- and punctuation-insensitive on top of this table, and a declared name
# always wins over an alias.
PARAM_ALIASES = {
    "assignment": {"variable": ("var", "target", "lhs", "name"),
                   "expr": ("e", "value", "rhs", "expression")},
    "sequential": {"intermediate": ("mid", "middle", "r", "m",
                                    "intermediate_condition",
                                    "intermediate_assertion")},
    "alternation": {"guard": ("g", "cond", "condition")},
    "iteration": {"guard": ("g", "cond", "condition"),
                  "variant": ("v", "measure")},
    "initialised_iteration": {"invariant": ("i", "inv"),
                              "guard": ("g", "cond", "condition"),
                              "variant": ("v", "measure")},
    "strengthen_post": {"intermediate_post": ("r", "post", "new_post",
                                              "strengthened_post")},
    "weaken_pre": {"intermediate_pre": ("r", "pre", "new_pre",
                                        "weakened_pre")},
    "flexible_sequential": {"pre1": ("a",), "post1": ("b",),
                            "pre2": ("c",), "post2": ("d",)},
}

_NON_PARAM_KEYS = {"law", "rationale", "reasoning", "explanation", "parameters"}


def _canon(key) -> str:
    return re.sub(r"[^a-z0-9]", "", str(key).lower())


def resolve_param_keys(law: str, law_cls, raw_params: Dict[str, Any]):
    """Map the keys of ``raw_params`` onto the law's declared parameter names.

    Returns ``(resolved, unrecognised)``. Pure; raises nothing.
    """
    table: Dict[str, str] = {}
    for name, _kind, _default in law_cls.PARAMS:
        table[_canon(name)] = name
    for name, aliases in PARAM_ALIASES.get(law, {}).items():
        for alias in aliases:
            table.setdefault(_canon(alias), name)

    resolved: Dict[str, Any] = {}
    unrecognised = []
    for key, value in raw_params.items():
        target = table.get(_canon(key))
        if target is None:
            unrecognised.append(key)
        elif target not in resolved or _canon(key) == _canon(target):
            resolved[target] = value
    return resolved, unrecognised


def _expr_text(raw) -> str:
    """A parameter value as expression text (models sometimes send 0 or true)."""
    if isinstance(raw, bool):
        return "true" if raw else "false"
    if isinstance(raw, (int, float)):
        return str(raw)
    return raw


def _parameters_from_raw(law: str, raw_params: Dict[str, Any]) -> Dict[str, Any]:
    law_cls = law_named(law)
    if law_cls.PARAMS is None:
        raise ValueError(
            f"{law_cls.__name__} is registered as {law!r} but declares no "
            f"PARAMS, so its parameters cannot be parsed"
        )

    declared = [name for name, _kind, _default in law_cls.PARAMS]
    resolved, unrecognised = resolve_param_keys(law, law_cls, raw_params or {})
    # Keys we could not place, while a declared parameter is left unset, almost
    # certainly mean the model misspelt a key; silently filling in a default
    # (alternation's guard defaults to `true`) would hide that.
    not_provided = [name for name in declared if resolved.get(name) is None]
    if unrecognised and not_provided:
        raise ValueError(
            f"unrecognised parameter key(s) {unrecognised} for law {law!r}; "
            f"use exactly these keys: {declared}"
        )

    parsed_params: Dict[str, Any] = {}
    for name, kind, default in law_cls.PARAMS:
        raw = resolved.get(name, default)
        if raw is None and default is None:
            continue
        if kind == "name":
            parsed_params[name] = raw
        elif kind == "expr":
            parsed_params[name] = parse_expr(_expr_text(raw) if raw is not None else "true")
        else:
            raise ValueError(
                f"{law_cls.__name__}.PARAMS declares unknown kind {kind!r} "
                f"for parameter {name!r}"
            )
    return parsed_params


def _strip_fences(response: str) -> str:
    response = response.strip()
    if response.startswith("```json"):
        response = response[7:]
    elif response.startswith("```"):
        response = response[3:]
    if response.endswith("```"):
        response = response[:-3]
    return response.strip()


def _first_json_object(text: str):
    """The first balanced ``{...}`` in ``text`` that parses as a JSON object."""
    for start in (i for i, ch in enumerate(text) if ch == "{"):
        depth, in_str, escaped = 0, False, False
        for end in range(start, len(text)):
            ch = text[end]
            if in_str:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    try:
                        candidate = json.loads(text[start:end + 1])
                    except json.JSONDecodeError:
                        break
                    if isinstance(candidate, dict):
                        return candidate
                    break
    return None


def parse_llm_response(response: str) -> Tuple[str, Dict[str, Any]]:
    """Turn one LLM reply into a (law name, parameters) pair."""
    response = _strip_fences(response)

    data = _load_json(response)
    law = data.get("law")
    raw_params = data.get("parameters") or {}
    if not raw_params:
        # Some replies put the parameters beside "law" instead of inside "parameters".
        raw_params = {k: v for k, v in data.items() if k not in _NON_PARAM_KEYS}

    law_named(law)          # raises UnknownLawError (a ValueError)
    return law, _parameters_from_raw(law, raw_params)


def parse_law_response(response: str) -> str:
    """Turn one LLM reply into a law name."""
    response = _strip_fences(response)

    data = _load_json_key(response, "law")
    law = data.get("law")

    # Validate that it exists in the registry
    law_named(law)

    return law


def parse_parameters_response(response: str, law: str) -> Dict[str, Any]:
    """Turn one LLM reply into a parameters dict for a specific law."""
    response = _strip_fences(response)

    try:
        data = _load_json_key(response, "parameters")
        raw_params = data.get("parameters", {}) or {}
    except ValueError:
        # No "parameters" key: accept a bare object whose keys are the parameters.
        bare = _first_json_object(response)
        if bare is None:
            raise
        raw_params = {k: v for k, v in bare.items() if k not in _NON_PARAM_KEYS}
        if not raw_params and law_named(law).PARAMS:
            raise

    return _parameters_from_raw(law, raw_params)
