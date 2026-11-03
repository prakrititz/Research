"""The prompt renderer must be readable *and* mean what the original formula meant."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm import spec_render as sr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.verification.proof_obligations import ProofObligation
from FormalLLM.verification.z3_backend import verify_obligation

SQRT = (
    "Frame: x.\n"
    "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0.\n"
    "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e)."
)

# Names are Real by default in the solver, so connectives are applied to
# comparisons here, never to bare names.
FORMULAS = [
    "x*x <= N && N < (x+e)*(x+e)",
    "a - (b - c) > 0 || a / (b * c) <= 1",
    "!(x < 0) && y > 1",
    "!(p > 0) || c > 1",
    "(a > 0 || b > 0) && (c > 0 || d > 0)",
    "a > 0 && (b > 0 || c > 0) && !(d > 0 && e > 0)",
    "(-(x + 1)) * 2 < y - -3",
    "(-x) < y",
    "x - y - z = 0",
    "x / (y / z) >= 1",
    "!(!(a > 1))",
]


def equivalent(a, b) -> bool:
    forward = verify_obligation(ProofObligation([a], b))[0]
    backward = verify_obligation(ProofObligation([b], a))[0]
    return forward == "PROVED" and backward == "PROVED"


@pytest.mark.parametrize("text", FORMULAS)
def test_rendering_is_re_parseable_and_equivalent(text):
    original = parse_expr(text)
    rendered = sr.render_expr(original)
    assert equivalent(original, parse_expr(rendered)), rendered


def test_minimal_parentheses_and_model_facing_spellings():
    assert sr.render_expr(parse_expr("x*x <= N && N < (x+e)*(x+e)")) == \
        "x * x <= N && N < (x + e) * (x + e)"
    assert sr.render_expr(parse_expr("a != 3")) == "a != 3"


def test_negation_inside_a_conjunction_is_parenthesised():
    """In L_spec `~a /\\ b` means `~(a /\\ b)`, so a bare `!a && b` would lie."""
    text = sr.render_expr(parse_expr("!(a > 1) && b > 2"))
    assert text == "(!(a > 1)) && b > 2"


def test_model_written_negation_keeps_its_own_scope():
    """`!(x < 0) && y > 1` must not become `~((x < 0) /\\ (y > 1))`."""
    parsed = parse_expr("!(x < 0) && y > 1")
    assert parsed.op == "/\\"            # a conjunction at the top, not a negation


def test_conjunction_renders_as_bullets():
    spec = parse_spec(SQRT)
    block = sr.render_spec(spec)
    assert "  - N >= 0" in block and "  - e > 0" in block
    assert "Frame (the only names the program may assign): x" in block
    assert "Constants (never assigned): N:float, e:float" in block


def test_variant_start_is_abbreviated_to_a_named_constant():
    """The loop-body spec used to show N0, x0, e0 -- copies of constants."""
    engine = RefinementEngine()
    spec = parse_spec(SQRT)
    result = engine.apply(spec, "initialised_iteration", {
        "invariant": parse_expr("x*x <= N && x >= 0"),
        "guard": parse_expr("N >= (x+e)*(x+e)"),
        "variant": parse_expr("N - x*x"),
    })
    body = result.by_role()["body"]
    block = sr.render_spec(body)
    assert "V0" in block
    for stale in ("N0", "x0", "e0"):
        assert stale not in block, f"{stale} leaked into:\n{block}"
    assert "V0 is the value of N - x * x when the loop body starts" in block
    # V0 is a real named constant in the specification itself (not a display trick),
    # so a model that writes V0 in its own formula refers to the prover's symbol.
    assert "Const(name='V0')" in repr(body) or "Variable(name='V0')" in repr(body)
    assert "VariablePreviousState" not in repr(body)


def test_a_spec_without_a_variant_is_rendered_unchanged():
    spec = parse_spec(SQRT)
    names = sr.abbreviate_variant_starts([spec.precondition.expr])[1]
    assert names == {}


# --- what the model reads must mean what the prover checks --------------------------------------

def _value(node, env):
    """Whole-number arithmetic as the prover reads it ("/" on integers is floor division)."""
    from FormalLLM.lspec.ast import Const, Number, Variable
    if isinstance(node, Number):
        return int(node.value)
    if isinstance(node, (Variable, Const)):
        return env[node.name]
    left, right = _value(node.left, env), _value(node.right, env)
    return {"+": lambda: left + right, "-": lambda: left - right, "*": lambda: left * right,
            "/": lambda: left // right}[node.op]()


def test_parentheses_that_change_the_value_are_kept():
    """Measured: ``n = 2 * (n / 2)`` ("n is even") was shown to the model as ``n = 2 * n / 2``, which reads
    as (2 * n) / 2 = n, always true. On the HumanEval pilot this misled the model on every parity problem."""
    from FormalLLM.llm import spec_render as sr
    from FormalLLM.llm.parser import parse_expr
    assert sr.render_expr(parse_expr("n = 2 * (n / 2)")) == "n = 2 * (n / 2)"
    assert sr.render_expr(parse_expr("a - (b + c)")) == "a - (b + c)"
    assert sr.render_expr(parse_expr("a / (b * c)")) == "a / (b * c)"
    assert sr.render_expr(parse_expr("a * (b / c)")) == "a * (b / c)"
    assert sr.render_expr(parse_expr("a / b * c")) == "a / b * c"            # left to right needs none


def test_rendering_then_reading_back_never_changes_the_value():
    import random
    from FormalLLM.llm import spec_render as sr
    from FormalLLM.llm.parser import parse_expr
    from FormalLLM.lspec.ast import BinaryOp, Number, Variable
    rng = random.Random(7)

    def build(depth):
        if depth == 0 or rng.random() < 0.25:
            return Variable(rng.choice("abc")) if rng.random() < 0.6 else Number(str(rng.randint(1, 5)))
        return BinaryOp(build(depth - 1), rng.choice("+-*/"), build(depth - 1))

    checked = 0
    for _ in range(300):
        tree = build(3)
        again = parse_expr(sr.render_expr(tree))
        for _ in range(5):
            env = {name: rng.randint(1, 9) for name in "abc"}
            try:
                want = _value(tree, env)
            except ZeroDivisionError:
                continue
            assert _value(again, env) == want, (sr.render_expr(tree), tree)
            checked += 1
    assert checked > 500
