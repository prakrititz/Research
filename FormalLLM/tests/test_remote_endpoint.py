"""Any OpenAI-compatible server can stand in for the hosted model: URL, model id and credentials come from the environment."""
import base64
from FormalLLM.llm.provider import OpenAIChatProvider


def test_a_local_server_needs_no_credentials():
    headers = OpenAIChatProvider("m", "http://localhost:11434/v1", auth="none")._headers()
    assert "Authorization" not in headers


def test_basic_and_bearer_credentials_are_both_understood():
    basic = OpenAIChatProvider("m", "http://x/v1", auth="user:pass")._headers()["Authorization"]
    assert basic == "Basic " + base64.b64encode(b"user:pass").decode()
    assert OpenAIChatProvider("m", "http://x/v1", auth="sk-abc")._headers()["Authorization"] == "Bearer sk-abc"
    assert OpenAIChatProvider("m", "http://x/v1", auth="Bearer sk-abc")._headers()["Authorization"] == "Bearer sk-abc"


def test_the_model_id_can_be_overridden(monkeypatch):
    from FormalLLM.llm.provider import remote_model_id
    monkeypatch.delenv("FORMALLLM_REMOTE_MODEL", raising=False)
    assert remote_model_id("gpt-oss:120b") == "gpt-oss:120b"
    monkeypatch.setenv("FORMALLLM_REMOTE_MODEL", "openai/gpt-oss-120b")
    assert remote_model_id("gpt-oss:120b") == "openai/gpt-oss-120b"
