"""The five constructors a hand-written derivation is made of (the JSON of ``FormalLLM/lean/laws.py``)."""


def loop(state, init, invariant, guard, variant, result, body):
    return {"law": "loop", "state": state, "init": init, "invariant": invariant, "guard": guard, "variant": variant,
            "result": result, "children": [body]}


def term(expr):
    return {"law": "term", "expr": expr, "children": []}


def cases(cond, yes, no):
    return {"law": "cases", "cond": cond, "children": [yes, no]}


def with_lemmas(tree, lemmas):
    """The same step, bringing helper lemmas (name, statement, proof) that Lean proves first."""
    return {**tree, "lemmas": lemmas}


def bind(var, type_, prop, first, second):
    return {"law": "bind", "var": var, "type": type_, "prop": prop, "children": [first, second]}
