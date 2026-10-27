from abc import ABC, abstractmethod
import base64
import json
import socket
import sys
import time
import threading
import itertools
import urllib.request
import urllib.error
import os

if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

#: seconds of silence after a streamed answer has started before the connection is taken for dead
STREAM_IDLE_S = 120

class Spinner:
    def __init__(self, message="Waiting for LLM..."):
        self.spinner = itertools.cycle(['-', '\\', '|', '/'])
        self.busy = False
        self.spinner_thread = None
        self.message = message

    def spinner_task(self):
        if not sys.stdout.isatty():
            sys.stdout.write(f"{self.message}\n")
            sys.stdout.flush()
            return
            
        try:
            while self.busy:
                sys.stdout.write(f"\r{next(self.spinner)} {self.message}")
                sys.stdout.flush()
                time.sleep(0.1)
            sys.stdout.write('\r' + ' ' * (len(self.message) + 2) + '\r')
        except Exception:
            pass

    def __enter__(self):
        self.busy = True
        self.spinner_thread = threading.Thread(target=self.spinner_task)
        self.spinner_thread.start()

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.busy = False
        if self.spinner_thread:
            self.spinner_thread.join()


class LLMBudgetExhausted(Exception):
    """The run's allowance of LLM calls is spent.

    This is a signal about the *whole run*, not a failed refinement attempt, so
    the refiner must let it propagate. Before it had its own type the refiner's
    blanket ``except Exception`` caught it, logged it as a failed attempt at
    every level of the tree, and the harness then reported the run as
    ``EXHAUSTED`` ("the model ran out of options") when it had in fact stopped
    on its budget.
    """


class LLMProvider(ABC):
    @abstractmethod
    def generate(self, prompt: str, max_tokens: int = None) -> str:
        """
        Takes a prompt string and returns the generated text from the LLM.
        """
        pass

class MockProvider(LLMProvider):
    """
    A mock provider for testing. 
    It can be configured to return specific responses or a sequence of responses.
    """
    def __init__(self, responses=None):
        self.responses = responses or []
        self.call_count = 0
        self.prompts_received = []

    def generate(self, prompt: str, max_tokens: int = None) -> str:
        self.prompts_received.append(prompt)
        if self.call_count < len(self.responses):
            response = self.responses[self.call_count]
            self.call_count += 1
            return response
        
        # Default fallback if run out of responses
        return json.dumps({"law": "skip", "parameters": {}})

class OllamaProvider(LLMProvider):
    """
    Connects to a local Ollama instance (default: localhost:11434).
    Expects the model to output JSON that matches the Refine4LLM format.

    Reasoning ("thinking") models such as qwen3.5 emit their JSON inside the
    separate `thinking` channel when `format: json` is requested, leaving
    `response` empty. We therefore fall back to the thinking channel so that
    such models are not silently scored as producing no output at all.
    """
    def __init__(self,
                 model_name: str = "llama3",
                 base_url: str = "http://localhost:11434",
                 think: bool = None,
                 options: dict = None,
                 response_format: str = "json",
                 timeout: int = 600,
                 keep_alive: str = "30m"):
        self.model_name = model_name
        self.base_url = base_url.rstrip("/")
        self.think = think
        self.options = options or {}
        # "json" constrains output to a JSON object (used by the refinement
        # loop); None leaves the model free, which is what code generation needs.
        self.response_format = response_format
        self.timeout = timeout
        self.keep_alive = keep_alive
        self.last_meta = {}

    def generate(self, prompt: str, max_tokens: int = None) -> str:
        print("\n" + "="*50)
        print("=== LLM PROMPT ===")
        print("="*50)
        print(prompt)
        print("="*50 + "\n")
        
        url = f"{self.base_url}/api/generate"

        # We explicitly request JSON format to help the model adhere to our schema
        data = {
            "model": self.model_name,
            "prompt": prompt,
            "stream": False,
            "keep_alive": self.keep_alive,
        }
        if self.response_format:
            data["format"] = self.response_format
        options = self.options.copy() if self.options else {}
        if max_tokens is not None:
            options["num_predict"] = max_tokens
        if options:
            data["options"] = options
        if self.think is not None:
            data["think"] = self.think

        req = urllib.request.Request(
            url,
            data=json.dumps(data).encode('utf-8'),
            headers={'Content-Type': 'application/json'},
            method='POST'
        )

        try:
            with Spinner(f"Waiting for Ollama ({self.model_name})..."):
                with urllib.request.urlopen(req, timeout=self.timeout) as response:
                    result = json.loads(response.read().decode('utf-8'))
        except urllib.error.URLError as e:
            raise Exception(f"Failed to connect to Ollama at {self.base_url}. Is Ollama running? Error: {e}")

        self.last_meta = {
            "prompt_eval_count": result.get("prompt_eval_count"),
            "eval_count": result.get("eval_count"),
            "total_duration": result.get("total_duration"),
            "used_thinking_channel": False,
        }

        text = result.get('response', '') or ''
        if not text.strip():
            # Reasoning model: the structured answer landed in the thinking channel.
            thinking = result.get('thinking', '') or ''
            if thinking.strip():
                self.last_meta["used_thinking_channel"] = True
                text = thinking
                
        print("\n" + "="*50)
        print("=== LLM RESPONSE ===")
        print("="*50)
        print(text)
        print("="*50 + "\n")
        
        return text


def remote_model_id(default: str) -> str:
    """The model id to send to the OpenAI-compatible server: ``FORMALLLM_REMOTE_MODEL`` if set, else ``default``. The same
    model has different ids on different hosts (``gpt-oss:120b`` on Ollama, ``openai/gpt-oss-120b`` on OpenRouter or Groq)."""
    return os.environ.get("FORMALLLM_REMOTE_MODEL") or default


class OpenAIChatProvider(LLMProvider):
    """Connects to any OpenAI-compatible ``/v1/chat/completions`` endpoint.

    Used for the hosted high-end models (gpt-oss:120b, qwen3-coder-next), which
    are served behind an authenticating proxy rather than a local Ollama
    socket. The refinement loop only ever needs one turn, so each call sends a
    single user message and reads one choice back.

    Like :class:`OllamaProvider`, this falls back to the reasoning channel:
    gpt-oss returns its chain of thought in ``message.reasoning`` and, when the
    visible content comes back empty, the structured answer is in there. A
    model scored as "produced no output" when it in fact answered would quietly
    corrupt every rate in the benchmark.

    Credentials are read from the environment (``FORMALLLM_REMOTE_AUTH``, in
    ``user:password`` form) rather than baked in, so the endpoint's password
    does not end up in the repository or in a results file.
    """

    #: Fields that have carried the reasoning text on the endpoints we use.
    REASONING_FIELDS = ("reasoning", "reasoning_content", "thinking")

    CUMULATIVE_COST_USD = 0.0
    MAX_BUDGET_USD = float(os.environ.get("FORMALLLM_MAX_BUDGET_USD", "100.0"))
    MODEL_RATES = {
        "gpt-4o": (2.50 / 1e6, 10.00 / 1e6),
        "gpt-4o-mini": (0.15 / 1e6, 0.60 / 1e6),
        "gpt-4o-2024-08-06": (2.50 / 1e6, 10.00 / 1e6),
        "gpt-4o-2024-11-20": (2.50 / 1e6, 10.00 / 1e6),
        "o3-mini": (1.10 / 1e6, 4.40 / 1e6),
        "o4-mini": (1.10 / 1e6, 4.40 / 1e6),
        "o1-mini": (1.10 / 1e6, 4.40 / 1e6),
        "o1": (15.00 / 1e6, 60.00 / 1e6),
        # list prices per million tokens (input, output), checked 2026-10-26; re-check before budgeting a large run
        "gpt-5.4-mini": (0.75 / 1e6, 4.50 / 1e6),
        "gpt-5.4": (2.50 / 1e6, 15.00 / 1e6),
        "gpt-5.4-nano": (0.20 / 1e6, 1.25 / 1e6),
        "gpt-5.5": (5.00 / 1e6, 30.00 / 1e6),
    }
    #: a model not in the table is charged at a high rate, so that the spending cap errs on the side of stopping early
    UNKNOWN_RATE = (5.00 / 1e6, 30.00 / 1e6)

    def __init__(self,
                 model_name: str,
                 base_url: str,
                 auth: str = None,
                 auth_env: str = "FORMALLLM_REMOTE_AUTH",
                 temperature: float = 0.2,
                 max_tokens: int = 4096,
                 response_format: str = "json_object",
                 timeout: int = 900,
                 stream: bool = True,
                 max_transport_retries: int = 8,
                 extra_body: dict = None,
                 reasoning_effort: str = None,
                 background: bool = False):
        self.model_name = model_name
        # OpenAI's Responses API in background mode: the request is queued on the server and polled with short GETs, so
        # no connection has to stay open (silent) while the model thinks. On 2026-10-27 such silent connections were
        # reset after ~60 s or stalled mid-answer, which stopped two capped runs with nothing wrong in the framework.
        self.background = background
        self.reasoning_effort = reasoning_effort
        self.base_url = base_url.rstrip("/")
        
        # Resolve authentication: explicit -> env auth_env -> OPENAI_API_KEY -> ~/.formalllm credentials
        resolved_auth = auth if auth is not None else os.environ.get(auth_env)
        if not resolved_auth:
            resolved_auth = os.environ.get("OPENAI_API_KEY")
        if not resolved_auth:
            for candidate in ("openai_key", "remote_auth"):
                cred_path = os.path.join(os.path.expanduser("~"), ".formalllm", candidate)
                if os.path.exists(cred_path):
                    try:
                        with open(cred_path, "r", encoding="utf-8") as f:
                            c = f.read().strip()
                            if c:
                                resolved_auth = c
                                break
                    except Exception:
                        pass
        self.auth = resolved_auth
        self.auth_env = auth_env
        self.temperature = temperature
        self.max_tokens = max_tokens
        self.response_format = response_format
        self.timeout = timeout
        # Streaming is the default because the tunnel in front of these models
        # resets a connection that produces no bytes for ~90s, and a cold load
        # of a 120B model takes longer than that. Streaming starts the response
        # immediately and keeps data flowing, so nothing idles out. A
        # non-streaming request is otherwise identical and is kept for
        # endpoints that do not support SSE.
        self.stream = stream
        self.max_transport_retries = max_transport_retries
        self.extra_body = dict(extra_body or {})
        # gpt-oss style models spend most of a call's time reasoning; the
        # endpoint honours `reasoning_effort` ("low" | "medium" | "high"),
        # which measured 7 s / 12 s / 24 s for the same prompt.
        if reasoning_effort:
            self.extra_body.setdefault("reasoning_effort", reasoning_effort)
        self.last_meta = {}

    def _track_usage_cost(self, usage: dict):
        p_tokens = usage.get("prompt_tokens") or 0
        c_tokens = usage.get("completion_tokens") or 0
        p_rate, c_rate = self.MODEL_RATES.get(self.model_name, self.UNKNOWN_RATE)
        call_cost = (p_tokens * p_rate) + (c_tokens * c_rate)
        OpenAIChatProvider.CUMULATIVE_COST_USD += call_cost
        print(f"\n[Usage: {p_tokens} prompt + {c_tokens} completion tokens | Call: ${call_cost:.5f} | "
              f"Cumulative Total: ${OpenAIChatProvider.CUMULATIVE_COST_USD:.4f} / ${OpenAIChatProvider.MAX_BUDGET_USD:.2f}]", flush=True)
        if OpenAIChatProvider.CUMULATIVE_COST_USD >= OpenAIChatProvider.MAX_BUDGET_USD:
            raise LLMBudgetExhausted(
                f"Global budget ceiling reached (${OpenAIChatProvider.CUMULATIVE_COST_USD:.2f} >= ${OpenAIChatProvider.MAX_BUDGET_USD:.2f})"
            )

    def _headers(self) -> dict:
        headers = {"Content-Type": "application/json"}
        if (self.auth or "").strip().lower() == "none":
            return headers                        # a local server (Ollama /v1, llama.cpp, vLLM) that takes no credentials
        if not self.auth:
            raise Exception(
                f"No credentials for {self.base_url}. Set {self.auth_env} or OPENAI_API_KEY, "
                f"or save key in ~/.formalllm/openai_key before running."
            )
        if self.auth.startswith("sk-") or self.auth.lower().startswith("bearer "):
            token = self.auth.split(" ", 1)[-1]
            headers["Authorization"] = f"Bearer {token}"
        elif ":" in self.auth:
            token = base64.b64encode(self.auth.encode("utf-8")).decode("ascii")
            headers["Authorization"] = f"Basic {token}"
        else:
            token = self.auth.split(" ", 1)[-1]
            headers["Authorization"] = f"Bearer {token}"
        return headers

    def generate(self, prompt: str, max_tokens: int = None) -> str:
        try:
            print("\n" + "="*50)
            print("=== LLM PROMPT ===")
            print("="*50)
            print(prompt)
            print("="*50 + "\n")
        except Exception:
            pass
        if self.background:
            return self._generate_background(prompt, max_tokens)

        url = f"{self.base_url}/chat/completions"

        is_reasoning = self.model_name.startswith(("o1", "o3", "o4", "gpt-5"))

        data = {
            "model": self.model_name,
            "messages": [{"role": "user", "content": prompt}],
            "stream": self.stream,
        }
        if not is_reasoning:
            data["temperature"] = self.temperature
            data["max_tokens"] = max_tokens if max_tokens is not None else self.max_tokens
        else:
            # Reasoning tokens count toward completion tokens. If caller passes a small max_tokens
            # (e.g. 1024), reasoning will consume all of it before outputting anything.
            # Ensure at least 8192 completion tokens.
            comp_tokens = max(max_tokens or 0, self.max_tokens or 0)
            data["max_completion_tokens"] = max(comp_tokens, 8192)

        if self.response_format:
            data["response_format"] = {"type": self.response_format}
        if self.stream:
            # Without this, a streaming response carries no usage block and the
            # per-trial token counts in the benchmark silently become null.
            data.setdefault("stream_options", {"include_usage": True})
        data.update(self.extra_body)

        req = urllib.request.Request(
            url,
            data=json.dumps(data).encode("utf-8"),
            headers=self._headers(),
            method="POST",
        )

        # A long refinement makes one HTTPS connection per call, and Windows
        # intermittently refuses an outbound socket under that churn
        # (WinError 10013) or the tunnel drops a connection mid-flight. Both are
        # transient and unrelated to the model, but they abort a whole trial and
        # get recorded as a refinement failure -- three runs were lost this way
        # before this retry existed.
        last_error = None
        answered_and_lost = 0            # failures after the server had started answering: those tokens may be billed
        for attempt in range(self.max_transport_retries):
            started = False
            sent_at = time.time()
            try:
                if self.stream:
                    print(f"\n[{self.model_name} is thinking (Live Stream)...]")
                    with urllib.request.urlopen(req, timeout=self.timeout) as response:
                        started = True
                        return self._read_stream(response)
                else:
                    with Spinner(f"Waiting for OpenAI-compatible endpoint ({self.model_name}), attempt {attempt+1}..."):
                        with urllib.request.urlopen(req, timeout=self.timeout) as response:
                            body = response.read().decode("utf-8")
                break
            except urllib.error.HTTPError as e:
                detail = e.read().decode("utf-8", "replace")[:500]
                if e.code == 429:
                    wait_s = 20
                    # Try to extract "Please try again in Xs" from error detail if present
                    import re
                    m = re.search(r"try again in ([\d\.]+)s", detail)
                    if m:
                        wait_s = int(float(m.group(1))) + 2
                    retry_after = e.headers.get("retry-after") if hasattr(e, "headers") else None
                    if retry_after and retry_after.isdigit():
                        wait_s = max(wait_s, int(retry_after))
                    print(f"\n[HTTP 429 Rate limit: waiting {wait_s}s before retry (attempt {attempt+1}/{self.max_transport_retries})...]", flush=True)
                    time.sleep(wait_s)
                    continue
                raise Exception(f"{self.base_url} returned HTTP {e.code}: {detail}")
            except (urllib.error.URLError, socket.error, OSError) as e:
                last_error = e
                waited = time.time() - sent_at
                # A reasoning model sends nothing while it thinks, so a connection cut after a long wait (a proxy or VPN
                # dropping an idle connection: "Remote end closed connection without response") was also being worked on
                # by the server, and may be billed, although no byte of the answer arrived
                started = started or waited > 20
                # Never retry silently: an answer lost after the server started generating it is (probably) billed, so
                # such a call is repeated at most once; a connection that never got through costs nothing and is retried
                print(f"\n[{self.model_name}: connection failed after {waited:.0f}s, "
                      f"{'the server was probably working on it (may be billed)' if started else 'before the request got through'}"
                      f" ({type(e).__name__}: {str(e)[:120]}); attempt {attempt + 1}/{self.max_transport_retries}]", flush=True)
                if started:
                    answered_and_lost += 1
                    if answered_and_lost > 1:
                        raise Exception(
                            f"Failed to reach {self.base_url}: the answer was lost twice after it had started "
                            f"(not retried again, to avoid paying for more lost answers). Error: {e}"
                        )
                if attempt == self.max_transport_retries - 1:
                    raise Exception(
                        f"Failed to reach {self.base_url} after "
                        f"{self.max_transport_retries} attempts. Error: {e}"
                    )
                # Back off long enough for a refused ephemeral port to be released, and to ride out a short loss of the
                # internet connection (DNS "getaddrinfo failed"): 5, 10, 20, 40, 60 ... s, about 4 minutes in all
                time.sleep(min(60, 5 * 2 ** attempt))

        if not body.strip():
            raise Exception(
                f"{self.base_url} returned an empty body for model "
                f"{self.model_name!r} (timeout was {self.timeout}s)"
            )

        result = json.loads(body)
        choices = result.get("choices") or []
        message = (choices[0].get("message") or {}) if choices else {}

        usage = result.get("usage") or {}
        self._track_usage_cost(usage)
        self.last_meta = {
            "prompt_eval_count": usage.get("prompt_tokens"),
            "eval_count": usage.get("completion_tokens"),
            "total_duration": None,
            "used_thinking_channel": False,
            "finish_reason": choices[0].get("finish_reason") if choices else None,
        }

        text = message.get("content") or ""
        if not text.strip():
            for field in self.REASONING_FIELDS:
                reasoning = message.get(field) or ""
                if reasoning.strip():
                    self.last_meta["used_thinking_channel"] = True
                    text = reasoning
                    break
                    
        print("\n" + "="*50)
        print("=== LLM RESPONSE ===")
        print("="*50)
        print(text)
        print("="*50 + "\n")
        return text

    # --- background mode (OpenAI Responses API) ---------------------------------------------------------------------

    def _json_request(self, method: str, url: str, data: dict = None, timeout: int = 60) -> dict:
        body = json.dumps(data).encode("utf-8") if data is not None else None
        req = urllib.request.Request(url, data=body, headers=self._headers(), method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as response:
                return json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "replace")[:500]
            raise Exception(f"{self.base_url} returned HTTP {e.code}: {detail}")

    def _generate_background(self, prompt: str, max_tokens: int = None) -> str:
        data = {
            "model": self.model_name,
            "input": prompt,
            "background": True,
            "store": True,                       # required by background mode
            "max_output_tokens": max(max_tokens or 0, self.max_tokens or 0, 8192),
        }
        if self.reasoning_effort:
            data["reasoning"] = {"effort": self.reasoning_effort}
        if self.response_format == "json_object":
            data["text"] = {"format": {"type": "json_object"}}
        # Creating the response is one short request. Only a failure that leaves us without the id after the server may
        # have accepted it can cost money (an orphaned response), so such a failure is retried at most once.
        job, last_error, maybe_created = None, None, 0
        for attempt in range(self.max_transport_retries):
            sent_at = time.time()
            try:
                job = self._json_request("POST", f"{self.base_url}/responses", data, timeout=60)
                break
            except (urllib.error.URLError, socket.error, OSError) as e:
                last_error = e
                waited = time.time() - sent_at
                accepted = waited > 5 and not isinstance(getattr(e, "reason", None), socket.gaierror)
                print(f"\n[{self.model_name}: submitting failed after {waited:.0f}s "
                      f"({'may have been accepted' if accepted else 'not sent'}; {type(e).__name__}: {str(e)[:120]}); "
                      f"attempt {attempt + 1}/{self.max_transport_retries}]", flush=True)
                maybe_created += accepted
                if maybe_created > 1:
                    raise Exception(f"Failed to reach {self.base_url}: submitting failed twice after it may have been "
                                    f"accepted (not retried again). Error: {e}")
                time.sleep(min(60, 5 * 2 ** attempt))
        if job is None:
            raise Exception(f"Failed to reach {self.base_url} after {self.max_transport_retries} attempts. Error: {last_error}")

        # Polling costs nothing and loses nothing: a failed poll is simply repeated, for up to `timeout` seconds in all
        job_id, started, failures = job["id"], time.time(), 0
        print(f"\n[{self.model_name} is thinking (background {job_id[:16]}...)]", flush=True)
        while job.get("status") in ("queued", "in_progress"):
            if time.time() - started > self.timeout:
                try:
                    self._json_request("POST", f"{self.base_url}/responses/{job_id}/cancel", {}, timeout=30)
                except Exception:
                    pass
                raise Exception(f"{self.base_url}: response {job_id} not finished after {self.timeout}s (cancelled)")
            time.sleep(2 if time.time() - started < 30 else 5)
            try:
                job = self._json_request("GET", f"{self.base_url}/responses/{job_id}", timeout=60)
                failures = 0
            except (urllib.error.URLError, socket.error, OSError) as e:
                failures += 1
                print(f"\n[{self.model_name}: polling failed ({type(e).__name__}: {str(e)[:100]}); retrying]", flush=True)
                time.sleep(min(60, 5 * failures))

        usage = job.get("usage") or {}
        self._track_usage_cost({"prompt_tokens": usage.get("input_tokens"), "completion_tokens": usage.get("output_tokens")})
        status = job.get("status")
        if status not in ("completed", "incomplete"):
            error = job.get("error") or {}
            raise Exception(f"{self.base_url}: response {job_id} {status}: {error.get('code')} {error.get('message')}")
        text = "".join(part.get("text") or ""
                       for item in job.get("output") or [] if item.get("type") == "message"
                       for part in item.get("content") or [] if part.get("type") == "output_text")
        self.last_meta = {
            "prompt_eval_count": usage.get("input_tokens"),
            "eval_count": usage.get("output_tokens"),
            "total_duration": round(time.time() - started, 1),
            "used_thinking_channel": False,
            "finish_reason": (job.get("incomplete_details") or {}).get("reason") or "stop",
        }
        print("\n" + "=" * 50 + "\n=== LLM RESPONSE ===\n" + "=" * 50 + f"\n{text}\n" + "=" * 50 + "\n")
        return text

    def _read_stream(self, response) -> str:
        """Consume a server-sent-event stream into one response string.

        Content and reasoning are accumulated separately so the same
        "answer landed in the reasoning channel" fallback applies as in the
        non-streaming path.
        """
        content_parts, reasoning_parts = [], []
        usage, finish_reason = {}, None
        idle_set = False

        for raw_line in response:
            if not idle_set:
                # Once the answer streams, a silence of minutes means a dead connection (the internet dropped mid-answer
                # and the read waited the full 900 s twice in one run): fail fast so the retry logic takes over
                idle_set = True
                try:
                    response.fp.raw._sock.settimeout(STREAM_IDLE_S)
                except AttributeError:
                    pass
            line = raw_line.decode("utf-8", "replace").strip()
            if not line or not line.startswith("data:"):
                continue
            payload = line[len("data:"):].strip()
            if payload == "[DONE]":
                break
            try:
                chunk = json.loads(payload)
            except json.JSONDecodeError:
                continue

            usage = chunk.get("usage") or usage
            for choice in chunk.get("choices") or []:
                finish_reason = choice.get("finish_reason") or finish_reason
                delta = choice.get("delta") or {}
                if delta.get("content"):
                    content = delta["content"]
                    content_parts.append(content)
                    try:
                        sys.stdout.write(content)
                        sys.stdout.flush()
                    except Exception:
                        pass
                for field in self.REASONING_FIELDS:
                    if delta.get(field):
                        reason = delta[field]
                        reasoning_parts.append(reason)
                        try:
                            sys.stdout.write(reason)
                            sys.stdout.flush()
                        except Exception:
                            pass

        self._track_usage_cost(usage)
        self.last_meta = {
            "prompt_eval_count": usage.get("prompt_tokens"),
            "eval_count": usage.get("completion_tokens"),
            "total_duration": None,
            "used_thinking_channel": False,
            "finish_reason": finish_reason,
        }

        text = "".join(content_parts)
        if not text.strip() and reasoning_parts:
            self.last_meta["used_thinking_channel"] = True
            text = "".join(reasoning_parts)
            
        try:
            print("\n" + "="*50)
            print("=== LLM STREAM RESPONSE ===")
            print("="*50)
            print(text)
            print("="*50 + "\n")
        except Exception:
            pass
        return text
