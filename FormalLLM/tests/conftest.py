import pytest


@pytest.fixture(scope="session")
def lean_session():
    """One Lean REPL (Mathlib imported once, about 10 s) shared by every test that needs Lean; skipped when it is not installed."""
    from FormalLLM.lean.session import LeanSession, LeanUnavailable
    try:
        session = LeanSession()
    except LeanUnavailable as error:
        pytest.skip(str(error))
    yield session
    session.close()
