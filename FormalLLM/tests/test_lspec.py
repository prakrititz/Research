"""L_spec: the printer, the parser and the step translation, without Lean (the Lean checks are the benchmarks
``lspec_steps.py``, ``lspec_equiv.py`` and ``lspec_specs.py``)."""
import pytest

from FormalLLM.dsl import feedback, lean_syntax, lspec_syntax, steps


def to_lspec(lean: str) -> str:
    return lspec_syntax.show(lean_syntax.parse(lean))


def round_trip(lean: str) -> str:
    return lean_syntax.show(lspec_syntax.parse(to_lspec(lean)))


# --- printing ------------------------------------------------------------------------------------------------------

@pytest.mark.parametrize("lean, spec", [
    ("i ≤ l.length ∧ s = (l.take i).sum", "i <= len(l) and s == sum(l[:i])"),
    ("a - b - c", "a - b - c"),
    ("a - (b - c)", "a - (b - c)"),
    ("(a ∧ b) ∧ c", "(a and b) and c"),
    ("a ∧ b ∧ c", "a and b and c"),
    ("(a ∨ b) ∧ c", "(a or b) and c"),
    ("a + b * c", "a + b * c"),
    ("(a + b) * c", "(a + b) * c"),
    ("2 ^ 3 ^ 2", "2 ** 3 ** 2"),
    ("(2 ^ 3) ^ 2", "(2 ** 3) ** 2"),
    ("decide (a < b)", "bool(a < b)"),
    ("toString n", "str(n)"),
    ("(x : Bool) = true", "(x as bool) == True"),
])
def test_printer(lean, spec):
    assert to_lspec(lean) == spec


@pytest.mark.parametrize("lean", [
    "a - b - c", "a - (b - c)", "(a ∧ b) ∧ c", "a ∧ b ∧ c", "(a ∨ b) ∧ c", "a → b → c", "(a → b) → c",
    "a ↔ b ∧ c", "(a ↔ b) ∧ c", "¬ a ∧ b", "¬ (a ∧ b)", "2 ^ 3 ^ 2", "(2 ^ 3) ^ 2", "a :: b ++ c",
    "decide (a < b) && c", "(fun x => x + 1) 2", "∀ i < n, l[i]! ≥ 0", "∃ k, k ≤ i ∧ (l.take k).sum < 0",
])
def test_round_trip_keeps_the_tree(lean):
    """Lean -> L_spec -> Lean gives the same tree (the printer's parentheses are exactly the needed ones)."""
    assert lean_syntax.parse(round_trip(lean)) == lean_syntax.parse(lean)


def test_bool_type_and_conversion_read_back():
    assert lean_syntax.show(lspec_syntax.parse("bool")) == "Bool"
    assert lean_syntax.show(lspec_syntax.parse("bool(a < b)")) == "decide (a < b)"
    assert lean_syntax.show(lspec_syntax.parse("str")) == "String"


# --- steps ---------------------------------------------------------------------------------------------------------

LOOP = {"law": "loop", "state": [["i", "Nat"], ["s", "Int"]], "init": ["0", "0"],
        "invariant": "i ≤ l.length ∧ s = (l.take i).sum", "guard": "i < l.length", "variant": "l.length - i",
        "result": "s"}


def test_step_round_trip():
    written = steps.from_engine(LOOP)
    assert written["state"] == [["i", "nat", "0"], ["s", "int", "0"]]
    back = steps.to_engine(written)
    assert lean_syntax.parse(back["invariant"]) == lean_syntax.parse(LOOP["invariant"])
    assert back["state"] == [["i", "Nat"], ["s", "Int"]] and back["init"] == ["0", "0"]


@pytest.mark.parametrize("step, field", [
    ({"law": "term"}, "expr"),
    ({"law": "loopy", "expr": "0"}, "law"),
    ({"law": "term", "expr": "a +"}, "expr"),
    ({"law": "bind", "var": "2x", "type": "int", "prop": "True"}, "var"),
    ({"law": "loop", "state": [["i", "nat"]], "invariant": "true_prop", "guard": "False", "variant": "0",
      "result": "0"}, "state[0]"),
])
def test_step_errors_name_the_field(step, field):
    with pytest.raises(steps.StepError) as caught:
        steps.to_engine(step)
    assert caught.value.field == field


def test_fields_for_unknown_law():
    with pytest.raises(steps.StepError):
        steps.fields_for("induction")


# --- goals ---------------------------------------------------------------------------------------------------------

class Goal:                                       # the fields of ``laws.Goal`` that rendering reads
    def __init__(self, ctx, hyps, ret, post):
        self.ctx, self.hyps, self.ret, self.post = ctx, hyps, ret, post


def test_goal_in_lspec_and_back():
    goal = Goal((("l", "List Int"),), (("h", "l ≠ []"),), "Int", "⟪r⟫ = l.sum")
    shown = steps.goal_to_lspec(goal)
    assert shown["find"] == ["result", "int"] and shown["such_that"] == "result == sum(l)"
    binders, statement = steps.goal_from_lspec(shown)
    assert binders == "(l : List Int) (h : l ≠ [])" and statement == "∃ result : Int, result = l.sum"


def test_loop_body_goal_names_the_next_state():
    post = ("(fun (i : Nat) (s : Int) => i ≤ n ∧ s = i) (⟪r⟫).1 (⟪r⟫).2 ∧ "
            "(fun (i : Nat) (s : Int) => n - i) (⟪r⟫).1 (⟪r⟫).2 < (n - i)")
    goal = Goal((("n", "Nat"), ("i", "Nat"), ("s", "Int")), (), "Nat × Int", post)
    shown = steps.goal_to_lspec(goal, ["i", "s"])
    assert shown["find"][0] == "(i_next, s_next)"
    assert shown["such_that"] == "(i_next <= n and s_next == i_next) and n - i_next < n - i"
    _, statement = steps.goal_from_lspec(shown)
    assert "result.1" in statement and "i_next" not in statement


def test_result_name_avoids_names_in_use():
    goal = Goal((("result", "Nat"),), (), "Nat", "⟪r⟫ = result")
    assert steps.result_name(goal) == "result_"


# --- feedback ------------------------------------------------------------------------------------------------------

def test_recipient():
    assert feedback.recipient(feedback.UNREADABLE, 1) == "applier"
    assert feedback.recipient(feedback.FALSE, 1) == "applier"
    assert feedback.recipient(feedback.UNPROVED, 1) == "selector"
    assert feedback.recipient(feedback.FALSE, 2) == "selector"
