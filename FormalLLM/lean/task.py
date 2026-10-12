"""A programming task in Lean: Verina's file format, shared by Verina and by our own Lean specifications.

A task directory holds ``task.json`` (signature, source), ``description.txt``, ``task.lean`` (the precondition and
postcondition as Lean definitions, ground-truth code and proof, with ``-- !benchmark @start/@end`` markers) and
``test.json`` (inputs as Lean literals, expected values). The *prelude* is what a refinement may rely on: the helper
definitions, ``f_precond`` and ``f_postcond``. It deliberately excludes the ground-truth code, its helpers and its proof.

    task = LeanTask.from_dir(".../verina_basic_15")
    task.define("a.size")        # Lean source: the prelude and  def f ... := a.size
"""
import json
import os
import re
from dataclasses import dataclass, field
from typing import Dict, List, Tuple

CODE = re.compile(r"(-- !benchmark @start code\n)(.*?)(\n\s*-- !benchmark @end code)", re.S)
AUX = re.compile(r"(-- !benchmark @start code_aux\n)(.*?)(\n?-- !benchmark @end code_aux)", re.S)
PROOF = re.compile(r"(-- !benchmark @start proof\n).*?(\s*-- !benchmark @end proof)", re.S)
HOLE = "⟪r⟫"                                    # the placeholder for the term being derived: ⟪r⟫


#: Tolerance for numbers that were Python floats (the one EvalPlus uses).
TOLERANCE = "(1 / 1000000 : ℚ)"


def precondition_proof(pre_name: str) -> str:
    """A proof of the precondition for an ``#eval`` of the function on concrete inputs. ``native_decide`` is a convenience of this
    test harness only (the proof argument is not computed); certificates never use it (the axiom check refuses it)."""
    # each alternative must close the goal (``; done``): ``simp`` that only makes progress would otherwise end the ``first``
    # ``native_decide`` runs the compiled decision procedure: instant, where ``norm_num``/``simp``/``decide`` evaluate a precondition
    # on a nine-element list of rationals symbolically in over a minute
    # ``trivial`` comes after it: it tries ``decide``, which evaluates the precondition by kernel reduction (69 s on nine rationals)
    return (f"(by first | native_decide | trivial | (norm_num [{pre_name}]; done) | (simp [{pre_name}]; done) | decide | omega)")


def same_expr(ret: str, left: str, right: str) -> str:
    """Lean for "``left`` is the expected value ``right``": ``==``, except that rationals (Python floats) agree up to TOLERANCE."""
    t = " ".join(ret.split())
    close = lambda a, b: f"decide (|{a} - {b}| ≤ {TOLERANCE})"
    if t == "ℚ":
        return close(left, right)
    if t == "List ℚ":
        return f"(({left}).length == ({right}).length && (({left}).zip ({right})).all (fun p => {close('p.1', 'p.2')}))"
    if t == "Array ℚ":
        return f"(({left}).size == ({right}).size && (({left}).toList.zip ({right}).toList).all (fun p => {close('p.1', 'p.2')}))"
    if t == "ℚ × ℚ":
        return f"({close(f'({left}).1', f'({right}).1')} && {close(f'({left}).2', f'({right}).2')})"
    if t == "ℚ × ℚ × ℚ":
        return (f"({close(f'({left}).1', f'({right}).1')} && {close(f'({left}).2.1', f'({right}).2.1')} && "
                f"{close(f'({left}).2.2', f'({right}).2.2')})")
    return f"(({left}) == ({right}))"


def lean_string(text: str) -> str:
    """A Lean string literal for ``text``: the escapes Lean knows (newline, tab, return, backslash, quote), ``\\xHH`` for other control
    characters (JSON's ``\\f`` and ``\\b`` are not Lean escapes), everything else as it is."""
    out = []
    for c in text:
        if c == "\\":
            out.append("\\\\")
        elif c == '"':
            out.append('\\"')
        elif c == "\n":
            out.append("\\n")
        elif c == "\t":
            out.append("\\t")
        elif c == "\r":
            out.append("\\r")
        elif ord(c) < 32 or ord(c) == 127:
            out.append(f"\\x{ord(c):02x}")
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def lean_char(c: str) -> str:
    escapes = {"\n": "\\n", "\t": "\\t", "\r": "\\r", "\\": "\\\\", "'": "\\'", '"': '\\"'}
    if c in escapes:
        return f"'{escapes[c]}'"
    if ord(c) < 32 or ord(c) == 127:
        return f"'\\x{ord(c):02x}'"
    return f"'{c}'"


def strip_imports(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not re.match(r"\s*import\s", line))


def render(value, type_text: str) -> str:
    """A JSON value of ``test.json`` as a Lean literal of type ``type_text``."""
    t = type_text.strip()
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return f"({value})" if value < 0 else str(value)
    if isinstance(value, str):
        # the dataset stores non-String expected values as Lean literals ("some 2", "#[1, 2]"): use them as written
        if t == "String":
            return lean_string(value)
        if t == "Char" and len(value) == 1:
            return lean_char(value)
        return value
    if isinstance(value, list):
        inner = re.match(r"(?:Array|List)\s+(.*)", t)
        elem = inner.group(1) if inner else ""
        body = ", ".join(render(v, elem) for v in value)
        return f"#[{body}]" if t.startswith("Array") else f"[{body}]"
    if value is None:
        return "none"
    return json.dumps(value, ensure_ascii=False)


@dataclass
class LeanTask:
    id: str
    name: str                                   # the function's name, e.g. containsConsecutiveNumbers
    params: List[Tuple[str, str]]               # [(name, Lean type)]
    ret: str                                    # the result type
    description: str
    prelude: str                                # helper definitions, f_precond, f_postcond (no imports, no code, no proof)
    tests: List[dict] = field(default_factory=list)
    directory: str = ""
    #: How ``test.json`` writes the *inputs*. ``"lean"``: every input is Lean source as it is (ours: ``"abc"`` with its quotes,
    #: ``[1, 2]``). ``"json"``: Verina's: numbers and strings are JSON values (``abc`` is the String ``"abc"``, ``,`` the Char
    #: ``','``) and only compound values are Lean source. Expected values are written the same way in both.
    encoding: str = "lean"
    #: Lean source that a task file of this dataset needs on this Lean version (a renamed constant): put before the file.
    compat: str = ""

    # --- names ----------------------------------------------------------------------------------------------------

    @property
    def pre_name(self) -> str:
        return f"{self.name}_precond"

    @property
    def post_name(self) -> str:
        return f"{self.name}_postcond"

    def binders(self, with_precondition: bool = True) -> str:
        """``(a : Array Int) (h_precond : f_precond a)``, as in Verina's own definitions."""
        text = " ".join(f"({n} : {t})" for n, t in self.params)
        if with_precondition:
            text += f" (h_precond : {self.pre_name} {self.args})"
        return text

    @property
    def args(self) -> str:
        return " ".join(f"({n})" if " " in n else n for n, _ in self.params)

    @property
    def root_post(self) -> str:
        """The root postcondition with the hole for the result."""
        return f"{self.post_name} {self.args} {HOLE} h_precond"

    # --- loading --------------------------------------------------------------------------------------------------

    def input_literal(self, case: dict, name: str) -> str:
        """The Lean literal of parameter ``name`` in test ``case``."""
        value = case["input"][name]
        if self.encoding == "json":
            return render(value, dict(self.params)[name])
        return str(value)

    def call_args(self, case: dict) -> str:
        """``(a) (b) ...`` the arguments of one test, parenthesised."""
        return " ".join(f"({self.input_literal(case, n)})" for n, _ in self.params)

    @classmethod
    def from_dir(cls, directory: str, encoding: str = "") -> "LeanTask":
        meta = json.load(open(os.path.join(directory, "task.json"), encoding="utf8"))
        lean = open(os.path.join(directory, "task.lean"), encoding="utf8").read()
        name = meta["signature"]["name"]
        params = [(p["param_name"], p["param_type"]) for p in meta["signature"]["parameters"]]
        description = open(os.path.join(directory, "description.txt"), encoding="utf8").read().strip()
        tests_path = os.path.join(directory, "test.json")
        tests = json.load(open(tests_path, encoding="utf8")) if os.path.exists(tests_path) else []
        encoding = encoding or meta.get("input_encoding") or "lean"
        return cls(id=meta["id"], name=name, params=params, ret=meta["signature"]["return_type"],
                   description=description, prelude=cls._prelude(lean, name), tests=tests, directory=directory,
                   encoding=encoding)

    @staticmethod
    def _prelude(lean: str, name: str) -> str:
        text = re.sub(r"(?:@\[[^\]]*\]\s*)?(?:partial\s+)?def\s+%s\b.*?-- !benchmark @end code\n" % re.escape(name), "", lean,
                      flags=re.S)
        text = AUX.sub(lambda m: m.group(1) + m.group(3), text)          # the code's helpers are part of the solution
        text = text.split("-- !benchmark @start proof_aux")[0]            # no proof, no theorem
        text = "\n".join(line for line in text.splitlines() if not re.match(r"\s*-- !benchmark ", line))
        text = re.sub(r"\n{3,}", "\n\n", strip_imports(text)).strip()      # the region markers are noise for a reader
        return text + "\n"

    # --- Lean source ----------------------------------------------------------------------------------------------

    def define(self, program: str, aux: str = "") -> str:
        """The prelude, optional helpers, and ``def f ... := program`` (the program may use ``h_precond``)."""
        body = program if "\n" not in program else "\n".join("  " + line for line in program.splitlines()).lstrip()
        return (f"{self.compat}\n{self.prelude}\n{aux}\n"
                f"def {self.name} {self.binders()} : {self.ret} :=\n  {body}\n")

    def test_commands(self) -> List[str]:
        """``#eval`` checks of the defined function on the tests of ``test.json``."""
        commands = []
        for case in self.tests:
            args = self.call_args(case)
            proof = precondition_proof(self.pre_name)
            commands.append(f"set_option maxHeartbeats 2000000 in\n#eval {same_expr(self.ret, f'({self.name} {args} {proof})', render(case['expected'], self.ret))}")
        return commands
