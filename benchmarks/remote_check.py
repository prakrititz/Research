"""Is the remote model server up? Lists its models, with the credentials of ``~/.formalllm/remote_auth`` (never printed).

    python benchmarks/remote_check.py                       # FORMALLLM_REMOTE_URL, else the default ngrok address
    python benchmarks/remote_check.py --url http://localhost:11434/v1

Answers one of: offline (ngrok ERR_NGROK_3200: no tunnel at that address), the login was refused (401/403), or up with
the model ids the server offers (pass one to the runners with ``FORMALLLM_REMOTE_MODEL`` if it differs from the config).
"""
import argparse
import json
import os
import sys
import urllib.error
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def check(url: str, timeout: float = 20) -> str:
    from FormalLLM.llm.provider import OpenAIChatProvider
    provider = OpenAIChatProvider("probe", url)
    try:
        headers = provider._headers()
    except Exception as error:
        return f"no credentials: {error}"
    request = urllib.request.Request(provider.base_url + "/models", headers=headers)
    try:
        with urllib.request.urlopen(request, timeout=timeout) as reply:
            data = json.loads(reply.read().decode("utf8"))
    except urllib.error.HTTPError as error:
        body = error.read().decode("utf8", "replace")
        if "ERR_NGROK_3200" in body:
            return "offline: no tunnel is running at that address (ngrok ERR_NGROK_3200)"
        if error.code in (401, 403):
            return f"up, but the login was refused (HTTP {error.code}): check ~/.formalllm/remote_auth (user:password)"
        return f"HTTP {error.code}: {body[:200]}"
    except (urllib.error.URLError, OSError) as error:
        return f"unreachable: {error}"
    ids = [m.get("id") for m in data.get("data", []) if isinstance(m, dict)]
    return "up; models: " + (", ".join(ids) if ids else "(none listed)")


def main():
    from benchmarks.run_bench import REMOTE_BASE_URL
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--url", default=REMOTE_BASE_URL)
    print(check(ap.parse_args().url))


if __name__ == "__main__":
    main()
