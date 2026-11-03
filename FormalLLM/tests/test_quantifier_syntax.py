"""Quantifiers as models write them: accepted when unambiguous, explained when not."""
import pytest

from FormalLLM.llm import law_cards
from FormalLLM.llm import spec_render as sr
from FormalLLM.llm.parser import parse_expr, syntax_hint


@pytest.mark.parametrize("written,canonical", [
    ("forall k:int (k < 0 || l[k] <= m)", "forall (k:int) k < 0 || l[k] <= m"),
    ("forall k (k < 0 || l[k] <= m)", "forall (k:int) k < 0 || l[k] <= m"),
    ("forall (k:int). k < 0", "forall (k:int) k < 0"),
    ("exists k:int, k > 0 && k < n", "exists (k:int) k > 0 && k < n"),
    ("forall (k:int) k < 0 || l[k] <= m", "forall (k:int) k < 0 || l[k] <= m"),
    ("forall (a:int)(b:int) a < b || b <= a", "forall (a:int)(b:int) a < b || b <= a"),
])
def test_binder_spellings_are_read_as_the_specification_language_does(written, canonical):
    assert sr.render_expr(parse_expr(written)) == canonical


def test_an_implication_arrow_is_explained_not_reported_as_a_parser_crash():
    with pytest.raises(ValueError) as raised:
        parse_expr("forall (k:int) (k < i -> l[k] <= m)")
    assert "no implication operator" in str(raised.value) and "!(A) || B" in str(raised.value)


def test_other_syntax_errors_stay_unchanged():
    assert syntax_hint("x + * 3") == ""


def test_the_prompt_shows_the_quantifier_form_and_the_implication_rewrite():
    assert "forall (k:int)" in law_cards.LANGUAGE and "!(A) || B" in law_cards.LANGUAGE


@pytest.mark.parametrize("text", ["exists_flag = 1", "forall_x > 0", "x_exists = 1"])
def test_a_name_that_merely_starts_with_a_quantifier_word_is_left_alone(text):
    from FormalLLM.llm.parser import normalise_binders
    assert normalise_binders(text) == text


@pytest.mark.parametrize("text", ["forall (c:char) c = c", "exists (a:array int) a[0] > 0"])
def test_binders_of_other_types_keep_their_type(text):
    """Found in review: the rewrite only knew int/nat/bool/float and broke (c:char) and (a:array int)."""
    from FormalLLM.llm.parser import normalise_binders
    assert normalise_binders(text) == text.replace(") ", ") ", 1)
    parse_expr(text)
