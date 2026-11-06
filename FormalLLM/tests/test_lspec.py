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


# --- what models actually write ------------------------------------------------------------------------------------

def test_json_values_are_accepted():
    back = steps.to_engine({"law": "loop", "state": [["i", "nat", 0], ["found", "bool", False], ["acc", "list[int]", []]],
                            "invariant": "i <= len(l)", "guard": "i < len(l)", "variant": "len(l) - i",
                            "result": "found"})
    assert back["init"] == ["0", "false", "[]"]


def test_bind_with_a_value():
    back = steps.to_engine({"law": "bind", "var": "m", "type": "rat", "value": "sum(l) / (len(l) as rat)"})
    assert lean_syntax.parse(back["prop"]) == lean_syntax.parse("m = (l.sum / (l.length : Rat))")


def test_lean_style_let_and_python_map_filter():
    assert lean_syntax.show(lspec_syntax.parse("let s := len(l); s + 1")) == lean_syntax.show(
        lspec_syntax.parse("let s = len(l); s + 1"))
    assert lean_syntax.show(lspec_syntax.parse("map(lambda x: x + 1, l)")) == "l.map (fun x => x + 1)"
    assert lean_syntax.show(lspec_syntax.parse("filter(lambda x: x > 0, l)")) == "l.filter (fun x => x > 0)"


def test_lean_error_in_lspec_names():
    assert feedback.lean_error("type mismatch: Nat expected, List.length l") == "type mismatch: nat expected, len l"


@pytest.mark.parametrize("spec, lean", [
    ("[x * 2 for x in l if x > 0]", "(l.filter (fun x => x > 0)).map (fun x => x * 2)"),
    ("[x for x in l if x > 0]", "l.filter (fun x => x > 0)"),
    ("sum(x * x for x in l)", "(l.map (fun x => x * x)).sum"),
    ("any(x < 0 for x in l)", "l.any (fun x => x < 0)"),
    ("range(2, n)", "List.range' 2 (n - 2)"),
    ("l[-1]", "l[l.length - 1]!"),
    ("l[:-1]", "l.take (l.length - 1)"),
    ("l[1:3]", "(l.drop 1).take (3 - 1)"),
    ("l[::-1]", "l.reverse"),
    ("0 <= i < len(l)", "(0 ≤ i) ∧ (i < l.length)"),
    ("a // b", "a / b"),
    ('", ".join(ws)', '", ".intercalate ws'),
    ('s.split(",")', 's.splitOn ","'),
    ("s.upper()", "s.toUpper"),
])
def test_python_forms(spec, lean):
    assert lean_syntax.parse(lean_syntax.show(lspec_syntax.parse(spec))) == lean_syntax.parse(lean)


def test_comparison_inside_comparison_is_not_a_chain():
    assert to_lspec("(a = b) = c") == "(a == b) == c"
    assert lean_syntax.parse(round_trip("(a < b) = c")) == lean_syntax.parse("(a < b) = c")


@pytest.mark.parametrize("spec", ["[x for (a, b) in l]", "[x for x in l for y in m]", "l[::2]", "range(0, n, 2)"])
def test_unsupported_python_forms_say_so(spec):
    with pytest.raises(lean_syntax.Unsupported):
        lspec_syntax.parse(spec)


def test_a_variable_is_never_a_builtin():
    """A goal's input called `string` (or a loop variable called `sum`) is that variable."""
    assert steps.to_lean("len(string)", "x", ["string"]) == "string.length"
    assert steps.to_lean("string(l)", "x") == "String.mk l"
    back = steps.to_engine({"law": "loop", "state": [["sum", "int", "0"]], "invariant": "sum == 0", "guard": "False",
                            "variant": "0", "result": "sum"}, ["l"])
    assert back["invariant"] == "sum = 0" and back["result"] == "sum"


@pytest.mark.parametrize("lean, scope", [
    ("String.mk (string.toList.take 2)", ["string"]),     # `string(...)` would be the input
    ("∀ (l : List Int), l.length = list.length", ["list"]),  # `list[int]` would index the input
    ("decide (bool = true) ∧ len.length = 0", ["bool", "len"]),
])
def test_printing_avoids_names_that_are_variables(lean, scope):
    """Printed for a scope, the text reads back to the same tree in that scope (`he_014`, `verina_advanced_48`)."""
    shown = steps.to_lspec(lean, "x", scope)
    assert lean_syntax.parse(steps.to_lean(shown, "x", scope)) == lean_syntax.parse(lean), shown
    assert "`" not in shown                                 # a variable in scope needs no escape
