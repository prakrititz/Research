"""The Lean-native refinement core: laws, engine, certification.

Tests of the text the laws generate need no toolchain. Tests that run Lean share one session (Mathlib is imported once,
about 10 s) and are skipped when Lean or the REPL is not installed.
"""
import os

import pytest

from benchmarks.datasets.lean_taskfile import write_task
from FormalLLM.lean.engine import CASCADE, Certificate, Derivation
from FormalLLM.lean.laws import (Bind, Cases, Goal, HOLE, IllFormed, Loop, Term, law_from_json)
from FormalLLM.lean.task import LeanTask, render

VERINA = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")


@pytest.fixture(scope="module")
def tasks(tmp_path_factory):
    root = str(tmp_path_factory.mktemp("lean_tasks"))
    sum_to = write_task(root, "t_sum", "sumTo", [("n", "Nat")], "Nat", "Sum of 0..n.", "True", "2 * result = n * (n + 1)",
                        "(List.range (n + 1)).sum",
                        tests=[{"input": {"n": "0"}, "expected": 0, "unexpected": [1]},
                               {"input": {"n": "10"}, "expected": 55, "unexpected": [54]}])
    max3 = write_task(root, "t_max3", "maxOfThree", [("a", "Int"), ("b", "Int"), ("c", "Int")], "Int", "Largest of three.",
                      "True", "result ≥ a ∧ result ≥ b ∧ result ≥ c ∧ (result = a ∨ result = b ∨ result = c)",
                      "max a (max b c)",
                      tests=[{"input": {"a": "1", "b": "5", "c": "3"}, "expected": 5, "unexpected": [3]},
                             {"input": {"a": "-1", "b": "-5", "c": "-3"}, "expected": -1, "unexpected": [-5]}])
    return {"sum": LeanTask.from_dir(sum_to), "max3": LeanTask.from_dir(max3)}


@pytest.fixture
def lean(lean_session):
    return lean_session


SUM_LOOP = {"law": "loop", "state": [["i", "Nat"], ["s", "Nat"]], "init": ["0", "0"],
            "invariant": "s * 2 = i * (i + 1) ∧ i ≤ n", "guard": "i < n", "variant": "n - i", "result": "s",
            "children": [{"law": "term", "expr": "(i + 1, s + (i + 1))"}]}
MAX3 = {"law": "bind", "var": "m", "type": "Int", "prop": "m ≥ a ∧ m ≥ b ∧ (m = a ∨ m = b)",
        "children": [
            {"law": "cases", "cond": "a ≥ b", "children": [{"law": "term", "expr": "a"}, {"law": "term", "expr": "b"}]},
            {"law": "cases", "cond": "m ≥ c", "children": [{"law": "term", "expr": "m"}, {"law": "term", "expr": "c"}]}]}


# --- the task file -------------------------------------------------------------------------------------------------

def test_task_reads_signature_and_keeps_only_the_specification_in_the_prelude(tasks):
    task = tasks["max3"]
    assert (task.name, task.ret) == ("maxOfThree", "Int")
    assert task.params == [("a", "Int"), ("b", "Int"), ("c", "Int")]
    assert "def maxOfThree_precond" in task.prelude and "def maxOfThree_postcond" in task.prelude
    assert "max a (max b c)" not in task.prelude            # the reference code is not leaked to the engine
    assert "sorry" not in task.prelude and "theorem" not in task.prelude
    assert task.root_post == f"maxOfThree_postcond a b c {HOLE} h_precond"


def test_tests_are_rendered_as_lean_literals(tasks):
    assert render(True, "Bool") == "true" and render(-3, "Int") == "(-3)"
    assert render("abc", "String") == '"abc"' and render("some 2", "Option Int") == "some 2"
    assert render([1, -2], "Array Int") == "#[1, (-2)]"
    commands = tasks["max3"].test_commands()
    assert len(commands) == 2 and "#eval (((maxOfThree (1) (5) (3)" in commands[0]  # preceded by a heartbeat option


# --- laws: the text they generate ----------------------------------------------------------------------------------

def goal():
    return Goal(1, (("a", "Int"), ("n", "Nat")), (("h_precond", "pre a n"),), "Int", f"post a n {HOLE}")


def test_term_states_the_postcondition_at_the_expression():
    expansion = Term("a + 1").expand(goal(), iter(range(2, 9)).__next__)
    assert [o.kind for o in expansion.obligations] == ["term"] and expansion.subgoals == []
    assert expansion.obligations[0].statement == "post a n (a + 1)"
    assert "(a : Int) (n : Nat) (h_precond : pre a n)" in expansion.obligations[0].binders


def test_cases_gives_each_branch_the_condition_or_its_negation():
    expansion = Cases("a ≥ 0").expand(goal(), iter(range(2, 9)).__next__)
    yes, no = expansion.subgoals
    assert ("h1", "(a ≥ 0)") in yes.hyps and ("h1", "¬ (a ≥ 0)") in no.hyps
    assert yes.post == no.post == goal().post
    assert expansion.obligations[0].statement == "Decidable (a ≥ 0)"


def test_bind_names_the_intermediate_value_and_refuses_a_name_in_use():
    expansion = Bind("m", "Int", "m ≥ a").expand(goal(), iter(range(2, 9)).__next__)
    first, second = expansion.subgoals
    assert first.ret == "Int" and first.post == f"(fun (m : Int) => m ≥ a) {HOLE}"
    assert ("m", "Int") in second.ctx and ("h1", "(m ≥ a)") in second.hyps and second.post == goal().post
    with pytest.raises(IllFormed, match="already a variable"):
        Bind("a", "Int", "a ≥ 0").expand(goal(), iter(range(2, 9)).__next__)


def test_loop_obligations_and_body_goal():
    law = law_from_json(SUM_LOOP)
    expansion = law.expand(goal(), iter(range(2, 9)).__next__)
    assert [o.kind for o in expansion.obligations] == ["wellformed", "wellformed", "init", "exit"]
    body, = expansion.subgoals
    assert body.ret == "Nat × Nat"
    assert body.post.count("(ρ)") == 0 and body.post.count(HOLE) == 4          # the hole stands for the next state
    assert ".1" in body.post and ".2" in body.post and "< (n - i)" in body.post
    assert [n for n, _ in body.ctx][-2:] == ["i", "s"]                           # the state is in scope in the body


def test_loop_with_three_state_variables_projects_nested_pairs():
    law = Loop((("i", "Nat"), ("s", "Nat"), ("b", "Bool")), ("0", "0", "false"), "True", "i < n", "n - i", "s")
    assert law._args("x") == "(x).1 (x).2.1 (x).2.2"
    assert law.state_type == "Nat × Nat × Bool"
    single = Loop((("i", "Nat"),), ("0",), "True", "i < n", "n - i", "i")
    assert single._args("x") == "(x)" and single.state_type == "Nat"


def test_loop_refuses_bad_shapes():
    for law in (Loop((), (), "True", "g", "v", "r"),
                Loop((("i", "Nat"),), ("0", "1"), "True", "i < n", "n - i", "i"),
                Loop((("n", "Nat"),), ("0",), "True", "n < 3", "3 - n", "n"),                 # n is already a variable
                Loop((("i", "Nat"),), ("0",), "True", "", "n - i", "i")):
        with pytest.raises(IllFormed):
            law.expand(goal(), iter(range(2, 9)).__next__)


def test_laws_round_trip_through_json_and_unknown_laws_are_refused():
    for data in (SUM_LOOP, MAX3, {"law": "term", "expr": "a"}, {"law": "cases", "cond": "a > 0"}):
        data = {k: v for k, v in data.items() if k != "children"}
        assert law_from_json(data).to_json() == data
    with pytest.raises(IllFormed, match="unknown law"):
        law_from_json({"law": "magic"})
    with pytest.raises(IllFormed, match="needs the field"):
        law_from_json({"law": "bind", "var": "m"})


# --- the engine, with Lean -----------------------------------------------------------------------------------------

def test_a_loop_derivation_is_certified(lean, tasks):
    derivation = Derivation(tasks["sum"], lean)
    steps = derivation.apply_tree(SUM_LOOP)
    assert [s.status for s in steps] == ["applied", "applied"] and derivation.complete
    assert derivation.laws_used == 2
    certificate = derivation.certify()
    assert certificate.verified, certificate
    assert "sorryAx" not in certificate.axioms and certificate.tests == 2 and certificate.passed == 2
    assert derivation.to_tree()["children"][0]["expr"] == "(i + 1, s + (i + 1))"


def test_bind_and_cases_derivation_is_certified(lean, tasks):
    derivation = Derivation(tasks["max3"], lean)
    assert all(s.ok for s in derivation.apply_tree(MAX3))
    assert derivation.certify().verified


def test_wrong_step_is_rejected_with_the_open_goal_and_a_counter_example(lean, tasks):
    derivation = Derivation(tasks["sum"], lean)
    wrong = dict(SUM_LOOP, children=[{"law": "term", "expr": "(i + 1, s + i)"}])
    steps = derivation.apply_tree(wrong)
    assert [s.status for s in steps] == ["applied", "unproved"]
    verdict = steps[-1].verdicts[0]
    assert verdict.status == "UNPROVED" and "(s + i) * 2 = (i + 1) * (i + 1 + 1)" in verdict.unsolved[0]
    # the step is a loop body, so the counter-example is a run of the loop (dynamic.py): inputs and the states it passes through
    assert verdict.counterexample and "n :=" in verdict.counterexample and "invariant false" in verdict.counterexample
    assert not derivation.complete and "counter-example" in steps[-1].feedback()


def test_a_wrong_answer_outside_a_loop_gets_a_counter_example_from_plausible(lean, tasks):
    derivation = Derivation(tasks["max3"], lean)
    step = derivation.apply(derivation.root.goal.id, Term("a"))                   # the largest of three is not always a
    assert not step.ok and step.status == "unproved"
    verdict = step.verdicts[0]
    assert verdict.counterexample and "b :=" in verdict.counterexample and "found by running" not in verdict.counterexample
    again = Derivation(tasks["max3"], lean).apply(1, Term("a")).verdicts[0].counterexample
    assert again == verdict.counterexample                                        # the seed is fixed: the same wrong step, the same values


def test_a_wrong_invariant_is_rejected_at_the_loop(lean, tasks):
    derivation = Derivation(tasks["sum"], lean)
    step = derivation.apply_tree(dict(SUM_LOOP, invariant="s = 5 ∧ i ≤ n"))[0]
    assert step.status == "unproved" and any(v.obligation.kind == "init" and not v.proved for v in step.verdicts)


def test_a_missing_exit_implication_is_rejected(lean, tasks):
    derivation = Derivation(tasks["sum"], lean)
    step = derivation.apply_tree(dict(SUM_LOOP, guard="i < n - 1"))[0]        # on exit i may be n - 1: s*2 = i*(i+1) is not enough
    assert step.status == "unproved" and any(v.obligation.kind == "exit" and not v.proved for v in step.verdicts)


def test_ill_formed_text_is_reported_in_leans_words(lean, tasks):
    derivation = Derivation(tasks["sum"], lean)
    step = derivation.apply_tree(dict(SUM_LOOP, guard="i <"))[0]
    assert step.status == "ill_formed" and "expected term" in step.feedback()
    unknown = Derivation(tasks["sum"], lean).apply_tree(dict(SUM_LOOP, variant="mystery i"))[0]
    assert unknown.status == "ill_formed"


def test_variant_must_be_a_natural_number(lean, tasks):
    step = Derivation(tasks["sum"], lean).apply_tree(dict(SUM_LOOP, variant="(n : Int) - i"))[0]
    assert step.status == "ill_formed"


def test_certificate_refuses_a_specification_theorem_that_rests_on_sorry(lean, tasks):
    derivation = Derivation(tasks["max3"], lean)
    derivation.apply_tree(MAX3)
    real = derivation.source
    derivation.source = lambda: real().replace("(maxOfThree_derived a b c h_precond).property", "sorry")
    certificate = derivation.certify(run_tests=False)
    assert certificate.compiles and "sorryAx" in certificate.axioms and not certificate.sound


def test_open_goals_block_certification(lean, tasks):
    derivation = Derivation(tasks["max3"], lean)
    assert derivation.open_goals()[0].id == 1
    assert derivation.certify() == Certificate(False, ["1 goals are still open"])


def test_a_solved_goal_cannot_be_solved_twice(lean, tasks):
    derivation = Derivation(tasks["max3"], lean)
    assert derivation.apply(1, Term("max a (max b c)")).ok
    again = derivation.apply(1, Term("a"))
    assert not again.ok and "already solved" in again.message
    assert not derivation.apply(99, Term("a")).ok


def test_session_recovers_from_a_command_that_never_returns(lean):
    reply = lean.run("partial def spin (n : Nat) : Nat := spin (n + 1)\n#eval spin 0", timeout=5)
    assert reply.timed_out and lean.restarts >= 1
    assert lean.run("theorem t (a : Int) (h : a > 0) : a + 1 > 1 := by omega").ok


@pytest.mark.skipif(not os.path.isdir(VERINA), reason="the Verina dataset is not installed")
def test_a_verina_task_with_an_existential_invariant_is_derived(lean):
    task = LeanTask.from_dir(os.path.join(VERINA, "verina_basic_15"))
    tree = {"law": "loop", "state": [["i", "Nat"], ["found", "Bool"]], "init": ["0", "false"],
            "invariant": "i ≤ a.size ∧ (found = true ↔ ∃ j, j < i ∧ j < a.size - 1 ∧ a[j]! + 1 = a[j + 1]!)",
            "guard": "i < a.size", "variant": "a.size - i", "result": "found",
            "children": [{"law": "term", "expr": "(i + 1, found || (i + 1 < a.size && a[i]! + 1 == a[i + 1]!))"}]}
    derivation = Derivation(task, lean)
    assert all(s.ok for s in derivation.apply_tree(tree))
    certificate = derivation.certify()
    assert certificate.verified and certificate.tests == 8


# --- helper lemmas brought by a step -------------------------------------------------------------------------------

@pytest.fixture(scope="module")
def prefix_sum_task(tmp_path_factory):
    root = str(tmp_path_factory.mktemp("lemma_tasks"))
    directory = write_task(
        root, "t_prefix", "arrayTotal", [("a", "Array Int")], "Int", "Sum of the elements.", "True", "result = prefixSum a a.size",
        "a.foldl (· + ·) 0", post_aux="def prefixSum (a : Array Int) (n : Nat) : Int :=\n  if n = 0 then 0 else prefixSum a (n - 1) + a[n - 1]!",
        tests=[{"input": {"a": "#[1, 2, 3]"}, "expected": 6, "unexpected": [7]}, {"input": {"a": "#[]"}, "expected": 0, "unexpected": [1]}])
    return LeanTask.from_dir(directory)


PREFIX_LOOP = {"law": "loop", "state": [["i", "Nat"], ["acc", "Int"]], "init": ["0", "0"],
               "invariant": "i ≤ a.size ∧ acc = prefixSum a i", "guard": "i < a.size", "variant": "a.size - i", "result": "acc",
               "children": [{"law": "term", "expr": "(i + 1, acc + a[i]!)"}]}
PREFIX_LEMMAS = [
    {"name": "prefixSum_zero", "statement": "∀ (a : Array Int), prefixSum a 0 = 0", "proof": "by intro a; rw [prefixSum]; simp"},
    {"name": "prefixSum_succ", "statement": "∀ (a : Array Int) (i : Nat), prefixSum a (i + 1) = prefixSum a i + a[i]!",
     "proof": "by intro a i; rw [prefixSum]; simp"}]


def test_a_recursive_helper_in_the_specification_needs_a_lemma_and_gets_one(lean, prefix_sum_task):
    without = Derivation(prefix_sum_task, lean).apply_tree(PREFIX_LOOP)
    assert not without[-1].ok and without[-1].status == "unproved"          # the cascade cannot unfold the recursion safely
    derivation = Derivation(prefix_sum_task, lean)
    steps = derivation.apply_tree(dict(PREFIX_LOOP, lemmas=PREFIX_LEMMAS))
    assert all(s.ok for s in steps), steps[-1].feedback()
    assert [h.name for h in derivation.helpers] == ["prefixSum_zero", "prefixSum_succ"]
    certificate = derivation.certify()
    assert certificate.verified and "theorem prefixSum_succ" in derivation.source()


def test_a_false_lemma_is_refused_by_lean_and_does_not_enter_the_environment(lean, prefix_sum_task):
    derivation = Derivation(prefix_sum_task, lean)
    false = [{"name": "bad", "statement": "∀ (a : Array Int) (i : Nat), prefixSum a (i + 1) = prefixSum a i", "proof": "by intro a i; rw [prefixSum]; simp"}]
    step = derivation.apply_tree(dict(PREFIX_LOOP, lemmas=false))[0]
    assert not step.ok and step.status == "lemma_unproved" and "bad" in step.message
    assert derivation.helpers == [] and derivation.laws_used == 0


def test_lemma_names_must_be_usable_and_new(lean, prefix_sum_task):
    derivation = Derivation(prefix_sum_task, lean)
    assert derivation.apply_tree(dict(PREFIX_LOOP, lemmas=[{"name": "no good", "statement": "True", "proof": "by trivial"}]))[0].status == "ill_formed"
    assert derivation.apply_tree(dict(PREFIX_LOOP, lemmas=[{"name": "x"}]))[0].status == "ill_formed"
    assert derivation.apply_tree(dict(PREFIX_LOOP, lemmas=PREFIX_LEMMAS + PREFIX_LEMMAS[:1]))[0].status == "ill_formed"       # duplicate


def test_only_the_three_standard_axioms_are_accepted():
    ok = Certificate(True, [], "propext, Classical.choice, Quot.sound", tests=2, passed=2)
    assert ok.sound and ok.verified
    assert Certificate(True, [], "", tests=1, passed=1).sound                                # no axiom at all
    for axioms in ("propext, sorryAx", "Lean.ofReduceBool", "Quot.sound, my_axiom"):
        assert not Certificate(True, [], axioms, tests=1, passed=1).sound, axioms
    assert not Certificate(True, [], None, tests=1, passed=1).sound                          # #print axioms printed nothing
    assert not Certificate(False, ["error"], "propext", tests=1, passed=1).sound
