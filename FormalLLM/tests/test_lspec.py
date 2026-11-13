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


@pytest.mark.parametrize("spec, lean", [
    ("if x > 0 then x else -x + 1", "if x > 0 then x else -x + 1"),            # Lean's `else` reaches right
    ("p and (if n > 0 then q else True)", "p ∧ (if n > 0 then q else true)"),
    ("if h := i < len(l) then l[i] else 0", "if h : i < l.length then l[i]! else 0"),
])
def test_lean_style_conditional(spec, lean):
    assert lean_syntax.parse(steps.to_lean(spec, "x", ["x", "p", "n", "q", "i", "l"])) == lean_syntax.parse(lean)


def test_max_and_min_of_a_list_round_trip():
    lean = steps.to_lean("max(l[:3]) + min(l)", "x", ["l"])
    assert lean_syntax.parse(lean) == lean_syntax.parse("(l.take 3).max?.get! + l.min?.get!")
    assert steps.to_lspec(lean, "x", ["l"]) == "max(l[:3]) + min(l)"
    assert lean_syntax.parse(steps.to_lean("max(a, b)", "x", ["a", "b"])) == lean_syntax.parse("max a b")


def test_a_reused_name_shadows_the_goal_variable():
    """A loop's state named like an input is a new variable inside the loop; its initial value is the input."""
    back = steps.to_engine({"law": "loop", "state": [["found", "bool", "found"]], "invariant": "found == True",
                            "guard": "False", "variant": "0", "result": "found"}, ["l", "found"])
    assert back["state"] == [["found2", "Bool"]] and back["init"] == ["found"]
    assert back["result"] == "found2" and "found2" in back["invariant"]
    bind = steps.to_engine({"law": "bind", "var": "lo", "type": "int", "value": "lo + 1"}, ["lo"])
    assert bind["var"] == "lo2" and lean_syntax.parse(bind["prop"]) == lean_syntax.parse("lo2 = (lo + 1)")


@pytest.mark.parametrize("message, table, expected", [
    ("Unsupported: trailing '?'", feedback.SYNTAX_HINTS, "a if c else b"),
    ("failed to synthesize instance of type class HAdd str str ?m.3", feedback.TYPE_HINTS, "++"),
    ("Type mismatch x has type list rat but is expected to have type prop", feedback.TYPE_HINTS, "\"value\""),
    ("failed to synthesize instance of type class GetElem? (list int) int ?m.1", feedback.TYPE_HINTS, "to_nat"),
    ("unknown identifier `foo`", feedback.TYPE_HINTS, None),
])
def test_hints_name_the_usual_fix(message, table, expected):
    found = feedback.hints(message, table)
    assert (expected in found) if expected else found == ""


@pytest.mark.parametrize("spec, lean", [
    ("s.split(' ').filter(lambda g: g !== '')", "(s.splitOn \" \").filter (fun g => g != \"\")"),
    ("','.join(ws)", "\",\".intercalate ws"),
    ("x == 'o|' or c == 'o'", "x = \"o|\" ∨ c = 'o'"),                     # one character is a char
    ("p and (if n > 1 then q)", "p ∧ (n > 1 → q)"),                        # if without else: a statement
    ("p implies q", "p → q"),
])
def test_more_python_spellings(spec, lean):
    assert lean_syntax.parse(steps.to_lean(spec, "x", ["s", "ws", "x", "c", "p", "n", "q"])) == lean_syntax.parse(lean)


def test_missing_field_names_the_law_fields():
    with pytest.raises(steps.StepError, match="`expr`"):
        steps.to_engine({"law": "term", "var": "x", "type": "int", "prop": "x == 1"})
    assert "`string` is a value here" in feedback.hints("Function expected at\n  string\nbut this term", feedback.TYPE_HINTS)


@pytest.mark.parametrize("spec, lean", [
    ("forall j: nat, j < i ==> l[j] >= 0", "∀ (j : Nat), j < i → l[j]! ≥ 0"),       # Lean's typed binder
    ("exists k: int, k * k == n", "∃ (k : Int), k * k = n"),
    ("(lambda x: x + 1, 2)", "(fun x => x + 1, 2)"),                              # a lambda in a tuple is not
    ("¬ (a ≤ b) ∧ (p → q) ∨ a ≠ b", "¬ (a ≤ b) ∧ (p → q) ∨ a ≠ b"),               # Lean's symbols
])
def test_lean_binders_and_symbols(spec, lean):
    assert lean_syntax.parse(steps.to_lean(spec, "x", ["i", "l", "n", "a", "b", "p", "q"])) == lean_syntax.parse(lean)


@pytest.mark.parametrize("message, table, expected", [
    ("Unsupported: trailing '='", feedback.SYNTAX_HINTS, "`==`"),
    ("failed to synthesize instance of type class GetElem? str nat ?m.5", feedback.TYPE_HINTS, "list(s)[i]"),
    ("Unknown identifier `result.length`", feedback.TYPE_HINTS, "`result` is not defined"),
])
def test_more_hints(message, table, expected):
    assert expected in feedback.hints(message, table)


# --- conversions the translator inserts (repair.py) ------------------------------------------------------------------

def _repaired(step, error):
    from FormalLLM.dsl import repair
    return [({k: v for k, v in new.items() if new.get(k) != step.get(k)}, why) for new, why in repair.repairs(step, error)]


def test_repair_closing_brace_typo_only_when_unambiguous():
    from FormalLLM.dsl import repair
    he_070 = {"law": "term",
              "expr": "range(len(lst)).map(lambda k: s[k / 2] if k % 2 == 0 else s[len(lst) - 1 - k / 2]}"}
    with pytest.raises(steps.StepError):
        steps.to_engine(he_070, ["lst", "s"])
    fixed, why = repair.text_repairs(he_070)
    assert fixed["expr"].endswith("k / 2])") and "`}` read as `)`" in why
    steps.to_engine(fixed, ["lst", "s"])                                   # now it reads
    assert repair.text_repairs({"law": "term", "expr": "f({1: 2}"}) is None          # a `{` exists: not a typo
    assert repair.text_repairs({"law": "term", "expr": "f(x}}"}) is None             # counts do not match
    loop = {"law": "loop", "state": [["i", "nat", "len(l}"]], "invariant": "True"}
    assert repair.text_repairs(loop)[0]["state"][0][2] == "len(l)"


def test_a_cut_off_reply_is_told_so():
    from FormalLLM.dsl import prompts
    with pytest.raises(steps.StepError, match="cut off"):
        prompts.parse_reply('{"law": "loop", "state": [["i", "nat", "0"], ["m", "')      # probe v6, he_020
    with pytest.raises(steps.StepError, match="no JSON object found"):
        prompts.parse_reply("I think the loop should count down.")
    assert prompts.parse_reply('{"law": "term", "expr": "\\"}\\""}')["expr"] == '"}"'  # a brace in a string


def test_repair_bind_value_read_as_equation():
    step = {"law": "bind", "var": "j_next", "type": "Nat", "prop": "if found = true then j + 1 else l.length"}
    found = _repaired(step, "Type mismatch\n  if found = true then j + 1 else l.length\nhas type\n  ℕ : Type\n"
                            "but is expected to have type\n  Prop : Type")
    assert lean_syntax.parse(found[0][0]["prop"]) == lean_syntax.parse("j_next = (if found = true then j + 1 else l.length)")
    # a prop that mentions the variable is a statement about it: never read as its value (`lo = lo` says nothing)
    assert _repaired({"law": "bind", "var": "lo", "type": "Rat", "prop": "lo"},
                     "Type mismatch\n  lo\nhas type\n  ℚ\nbut is expected to have type\n  Prop") == []


@pytest.mark.parametrize("expr, error, expected", [
    ("List.drop 1 s.toList ++ List.take 1 s.toList",
     "Type mismatch\n  List.drop 1 s.toList ++ List.take 1 s.toList\nhas type\n  List Char : Type\nbut is expected to have "
     "type\n  String : Type", "String.mk (List.drop 1 s.toList ++ List.take 1 s.toList)"),
    ("if p then strings[i]! else []",
     "Application type mismatch: The argument\n  []\nhas type\n  List ?m.52 : Type ?u\nbut is expected to have type\n"
     "  String : Type\nin the application", 'if p then strings[i]! else ""'),
    ("List.foldl (fun acc c => acc + (c ∈ ['a', 'e'])) 0 s.toList",
     "failed to synthesize instance of type class\n  HAdd ℕ Prop ?m.118",
     "List.foldl (fun acc c => acc + (if c ∈ ['a', 'e'] then 1 else 0)) 0 s.toList"),
    ("(lst[i]!).toNat + 1", "Invalid field `toNat`: The environment does not contain `Nat.toNat`, so it is not "
     "possible to project the field `toNat` from an expression\n  lst[i]!\nof type `ℕ`", "lst[i]! + 1"),
])
def test_repair_conversions(expr, error, expected):
    found = _repaired({"law": "term", "expr": expr}, error)
    assert lean_syntax.parse(found[0][0]["expr"]) == lean_syntax.parse(expected)


def test_repair_char_one_occurrence_offered():
    step = {"law": "term", "expr": "(s.splitOn 'o').length + s.toList.count 'o'"}
    found = _repaired(step, "Type mismatch\n  'o'\nhas type\n  Char\nbut is expected to have type\n  String")
    shown = [f["expr"] for f, _ in found]
    assert len(shown) == 3                                  # both, the first only, the second only
    assert lean_syntax.parse(shown[1]) == lean_syntax.parse("(s.splitOn \"o\").length + s.toList.count 'o'")


def test_repair_needs_a_rejection():
    from FormalLLM.dsl import repair
    assert repair.repairs({"law": "term", "expr": "s ++ t"}, "unknown identifier `t`") == []


@pytest.mark.parametrize("spec, lean", [
    ("l.sorted()", "l.mergeSort"),                         # a function written as a method
    ("l.len()", "l.length"),
    ("l.indexOf(x)", "l.idxOf x"),                         # another language's spelling
])
def test_method_spellings(spec, lean):
    assert lean_syntax.parse(steps.to_lean(spec, "x", ["l", "x"])) == lean_syntax.parse(lean)


def test_text_repairs_juxtaposed_call():
    """Lean's `x.m a` and `f (x)` read as calls (gpt-5.4-mini on Verina); keywords before `(` are kept."""
    from FormalLLM.dsl import repair
    fixed, why = repair.text_repairs({"law": "term", "expr": "l.find?(lambda x: x > 0).getD 0"})
    assert fixed["expr"] == "l.find?(lambda x: x > 0).getD(0)" and "f(x)" in why
    assert repair.text_repairs({"law": "term", "expr": "o.getD nums[0]"})[0]["expr"] == "o.getD(nums[0])"
    assert repair.text_repairs({"law": "term", "expr": "decide (x)"})[0]["expr"] == "decide(x)"
    for kept in ("a and (b or c)", "not (x in l)", "exists (m: nat): m < n"):
        assert repair.text_repairs({"law": "term", "expr": kept}) is None
