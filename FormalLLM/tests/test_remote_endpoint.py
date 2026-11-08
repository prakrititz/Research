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


def test_each_host_gets_only_its_own_credentials(monkeypatch, tmp_path):
    """The OpenAI key never goes to a remote server, and the remote login never goes to OpenAI."""
    home = tmp_path / ".formalllm"
    home.mkdir()
    (home / "openai_key").write_text("sk-openai-secret")
    (home / "remote_auth").write_text("user:pass")
    monkeypatch.setattr("os.path.expanduser", lambda p: str(tmp_path) if p == "~" else p)
    for name in ("FORMALLLM_REMOTE_AUTH", "OPENAI_API_KEY"):
        monkeypatch.delenv(name, raising=False)
    remote = OpenAIChatProvider("m", "https://example.ngrok-free.dev/v1")
    assert remote.auth == "user:pass"
    assert remote._headers()["Authorization"] == "Basic " + base64.b64encode(b"user:pass").decode()
    assert OpenAIChatProvider("m", "https://api.openai.com/v1").auth == "sk-openai-secret"
    monkeypatch.setenv("OPENAI_API_KEY", "sk-env-secret")
    assert OpenAIChatProvider("m", "https://example.ngrok-free.dev/v1").auth == "user:pass"
    assert OpenAIChatProvider("m", "https://evil.example/openai.com/v1").auth == "user:pass"   # the host decides


def test_only_a_local_or_tunnelled_server_counts_as_free():
    from FormalLLM.llm.provider import is_self_hosted
    assert is_self_hosted("https://broodless-alethia-nipping.ngrok-free.dev/v1")
    assert is_self_hosted("http://localhost:11434/v1") and is_self_hosted("http://127.0.0.1:8000/v1")
    assert not is_self_hosted("https://api.openai.com/v1")
    assert not is_self_hosted("https://openrouter.ai/api/v1")
    assert not is_self_hosted("https://ngrok-free.dev.evil.com/v1")


def test_the_model_id_can_be_overridden(monkeypatch):
    from FormalLLM.llm.provider import remote_model_id
    monkeypatch.delenv("FORMALLLM_REMOTE_MODEL", raising=False)
    assert remote_model_id("gpt-oss:120b") == "gpt-oss:120b"
    monkeypatch.setenv("FORMALLLM_REMOTE_MODEL", "openai/gpt-oss-120b")
    assert remote_model_id("gpt-oss:120b") == "openai/gpt-oss-120b"
