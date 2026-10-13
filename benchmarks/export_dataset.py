r"""Write the specifications and derivations of a dataset as plain, readable files: ``exports/``.

    python benchmarks/export_dataset.py                 # every dataset
    python benchmarks/export_dataset.py --dataset humaneval verina

For each task ``exports/<dataset>/<task_id>/`` holds

``spec.lean``        the formal specification: helper definitions, precondition, postcondition (no code, no proof)
``description.md``   the English statement
``derivation.json``  the hand-written derivation tree (the JSON of ``FormalLLM/lean/laws.py``), if there is one
``derivation.md``    the same tree as text: law, condition/invariant, guard, variant, helper lemmas
``program.lean``     the finished, verified Lean file (from ``verify_derivations.py``), if there is one
``status.json``      kind, laws used, certified, independently verified, tests, why a task has none

``exports/<dataset>/index.md`` and ``index.csv`` list the tasks; ``exports/all_specs.json`` and ``all_derivations.json`` are the
same content for programs; ``exports/README.md`` explains it all. It reads results already on disk; it runs no Lean.
"""
import argparse
import csv
import json
import os
import shutil
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "exports")

DEFINITIONAL = ("fixSpec", "evalOps", "romanSpec", "md5Hex")

#: why a task has no certified derivation (filled in by hand; everything else is measured)
BLOCKED = {
    "he_015_string_sequence": "its specification is about String.splitOn, and Lean 4.34 has no lemma relating the legacy "
                              "String.splitOn to list operations (the proof would need a theory of splitOnAux)",
    "he_019_sort_numbers": "its specification is about String.splitOn (same gap as he_015)",
    "he_086_anti_shuffle": "its specification is about String.splitOn (same gap as he_015)",
    "he_032_find_zero": "needs a root bound and a Lipschitz bound for polynomials over the rationals (bisection); not attempted",
    "he_039_prime_fib": "the specification is unsatisfiable for n > 14 (it asks for a Fibonacci index below 300) and the primality "
                        "of Fibonacci numbers of 28 digits cannot be decided by the kernel; the precondition would need n <= 14",
    "verina_basic_23": "reference code does not compile on Lean 4.34.1 (automatic termination proof of a `let rec` times out)",
    "verina_basic_52": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_57": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_74": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_75": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_79": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_86": "reference code does not compile on Lean 4.34.1 (same cause as verina_basic_23)",
    "verina_basic_61": "reference code uses String.Iterator.curr/next whose signature changed after Lean 4.18",
    "verina_advanced_68": "the specification does not elaborate on Lean 4.34.1 (`c.isDigit` with `c`'s type not yet known)",
}


def read_json(path, default=None):
    if os.path.exists(path):
        with open(path, encoding="utf8") as handle:
            return json.load(handle)
    return default


def walk(tree):
    yield tree
    for child in tree.get("children", []):
        yield from walk(child)


def kind_of(tree):
    laws = [node["law"] for node in walk(tree)]
    exprs = " ".join(node.get("expr", "") for node in walk(tree))
    if "loop" in laws:
        return "loop"
    if len(laws) == 1 and any(word in exprs for word in DEFINITIONAL):
        return "definitional"
    return "restate"


def render(tree, depth=0):
    pad = "  " * depth
    law = tree["law"]
    lines = []
    if law == "term":
        lines.append(f"{pad}- **term**: `{tree['expr']}`")
    elif law == "cases":
        lines.append(f"{pad}- **cases** on `{tree['cond']}`")
    elif law == "bind":
        lines.append(f"{pad}- **bind** `{tree['var']} : {tree['type']}` with property `{tree['prop']}`")
    elif law == "loop":
        names = ", ".join(f"{n} : {t}" for n, t in tree["state"])
        lines.append(f"{pad}- **loop** over state ({names}), start ({', '.join(tree['init'])})")
        lines.append(f"{pad}  - invariant: `{tree['invariant']}`")
        lines.append(f"{pad}  - guard: `{tree['guard']}`")
        lines.append(f"{pad}  - variant: `{tree['variant']}`")
        lines.append(f"{pad}  - result: `{tree['result']}`")
    else:
        lines.append(f"{pad}- **{law}**")
    for lemma in tree.get("lemmas", []):
        lines.append(f"{pad}  - helper lemma `{lemma['name']}`: `{lemma['statement']}`")
    labels = {"cases": ("then", "else"), "bind": ("value", "continuation")}.get(law)
    for number, child in enumerate(tree.get("children", [])):
        if labels and number < len(labels):
            lines.append(f"{pad}  - _{labels[number]}_:")
            lines.extend(render(child, depth + 2))
        else:
            lines.extend(render(child, depth + 1))
    return lines


def export_dataset(name):
    from FormalLLM.lean.dataset import get
    from FormalLLM.lean.evaluate import task_source
    ds = get(name)
    trees = ds.oracles()
    results = os.path.dirname(ds.results_dir)
    oracle_rows, verification = {}, {}
    # ours were run together (``--dataset lean_specs``); Verina has its own results directory
    for directory in (os.path.join(results, "lean_specs"), ds.results_dir):
        for row in read_json(os.path.join(directory, "oracle.json"), []) or []:
            oracle_rows[row["id"]] = row
        for filename in ("verification_lean_specs.json", f"verification_{name}.json"):
            for row in read_json(os.path.join(directory, filename), []) or []:
                verification[row["id"]] = row
    validation = {}
    path = os.path.join(ds.results_dir, "validation.jsonl")
    if os.path.exists(path):
        for line in open(path, encoding="utf8"):
            if line.strip():
                row = json.loads(line)
                validation[row["id"]] = row
    out_dir = os.path.join(OUT, name)
    if os.path.isdir(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)
    rows, specs, derivations = [], {}, {}
    for task_id in ds.ids():
        task = ds.load(task_id)
        directory = os.path.join(out_dir, task_id)
        os.makedirs(directory)
        spec = (f"import Mathlib\n{task.compat + chr(10) if task.compat.strip() else ''}\n{task.prelude}")
        with open(os.path.join(directory, "spec.lean"), "w", encoding="utf8", newline="\n") as handle:
            handle.write(spec)
        with open(os.path.join(directory, "description.md"), "w", encoding="utf8", newline="\n") as handle:
            handle.write(f"# {task_id}\n\n`{task.name}({', '.join(f'{n} : {t}' for n, t in task.params)}) : {task.ret}`\n\n"
                         f"{task.description}\n")
        tree = trees.get(task_id)
        row = {"id": task_id, "dataset": name, "family": ds.family(task_id), "function": task.name, "tests": len(task.tests),
               "has_derivation": tree is not None, "kind": "", "laws": 0, "helper_lemmas": 0, "certified": False,
               "independently_verified": False, "tests_passed": None, "blocked_reason": BLOCKED.get(task_id, "")}
        specs[task_id] = {"name": task.name, "params": task.params, "ret": task.ret, "description": task.description,
                          "spec_lean": spec}
        if tree is not None:
            with open(os.path.join(directory, "derivation.json"), "w", encoding="utf8", newline="\n") as handle:
                json.dump(tree, handle, indent=2, ensure_ascii=False)
            with open(os.path.join(directory, "derivation.md"), "w", encoding="utf8", newline="\n") as handle:
                handle.write(f"# Derivation of {task_id}\n\nkind: **{kind_of(tree)}**\n\n" + "\n".join(render(tree)) + "\n")
            derivations[task_id] = tree
            row["kind"] = kind_of(tree)
            row["laws"] = sum(1 for _ in walk(tree))
            row["helper_lemmas"] = sum(len(node.get("lemmas", [])) for node in walk(tree))
            produced = oracle_rows.get(task_id)
            if produced:
                row["certified"] = bool(produced.get("certified"))
                row["tests_passed"] = f"{produced.get('passed')}/{produced.get('tests')}"
            check = verification.get(task_id)
            if check:
                row["independently_verified"] = bool(check.get("verified"))
                source = next((q for q in (os.path.join(results, "lean_specs", "verified", f"{task_id}.lean"),
                                           os.path.join(ds.results_dir, "verified", f"{task_id}.lean")) if os.path.exists(q)), None)
                if source:
                    shutil.copy(source, os.path.join(directory, "program.lean"))
        if task_id in validation:
            v = validation[task_id]
            row["spec_checks"] = {"compiles": v["compiles"], "reference_passes": f"{v['reference_passes']}/{v['tests']}",
                                  "accepts_expected": f"{v['accepts_expected']}/{v['tests']}",
                                  "rejects_wrong": f"{v['rejects_wrong']}/{v['wrong_total']}"}
        with open(os.path.join(directory, "status.json"), "w", encoding="utf8", newline="\n") as handle:
            json.dump(row, handle, indent=2, ensure_ascii=False)
        rows.append(row)
    with open(os.path.join(out_dir, "index.csv"), "w", encoding="utf8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["id", "family", "tests", "has_derivation", "kind", "laws", "helper_lemmas", "certified",
                         "independently_verified", "blocked_reason"])
        for r in rows:
            writer.writerow([r["id"], r["family"], r["tests"], r["has_derivation"], r["kind"], r["laws"], r["helper_lemmas"],
                             r["certified"], r["independently_verified"], r["blocked_reason"]])
    with open(os.path.join(out_dir, "index.md"), "w", encoding="utf8", newline="\n") as handle:
        handle.write(f"# {name}: {len(rows)} tasks\n\n| task | kind | laws | lemmas | certified | verified independently | note |\n"
                     "|---|---|---|---|---|---|---|\n")
        for r in rows:
            handle.write(f"| [{r['id']}]({r['id']}/) | {r['kind'] or '-'} | {r['laws'] or '-'} | {r['helper_lemmas'] or '-'} | "
                         f"{'yes' if r['certified'] else 'no'} | {'yes' if r['independently_verified'] else 'no'} | "
                         f"{r['blocked_reason']} |\n")
    return rows, specs, derivations


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", nargs="*", default=["humaneval", "classic", "verina"])
    args = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    all_specs, all_derivations, summary = {}, {}, {}
    for name in args.dataset:
        rows, specs, derivations = export_dataset(name)
        all_specs[name], all_derivations[name] = specs, derivations
        kinds = {}
        for r in rows:
            if r["has_derivation"]:
                kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
        summary[name] = {"tasks": len(rows), "with_derivation": sum(r["has_derivation"] for r in rows),
                         "certified": sum(r["certified"] for r in rows),
                         "independently_verified": sum(r["independently_verified"] for r in rows),
                         "kinds": kinds, "blocked_listed": sum(bool(r["blocked_reason"]) for r in rows)}
    # a partial export must not drop the datasets exported earlier
    for key, filename in (("specs", "all_specs.json"), ("derivations", "all_derivations.json")):
        path = os.path.join(OUT, filename)
        merged = read_json(path, {}) or {}
        merged.update(all_specs if key == "specs" else all_derivations)
        with open(path, "w", encoding="utf8", newline="\n") as handle:
            json.dump(merged, handle, indent=1, ensure_ascii=False)
    old = read_json(os.path.join(OUT, "summary.json"), {}) or {}
    old.update(summary)
    with open(os.path.join(OUT, "summary.json"), "w", encoding="utf8", newline="\n") as handle:
        json.dump(old, handle, indent=2)
    write_readme(old)
    print(json.dumps(summary, indent=2))


def write_readme(summary):
    lines = ["# Formal specifications and verified derivations (exported)", "",
             "Plain-file copy of the Lean specifications and the hand-written refinement derivations of the FormalLLM project, "
             "so they can be read, diffed and reused without running anything. Generated by "
             "`python benchmarks/export_dataset.py` from `benchmarks/datasets/lean_specs/` (HumanEval and the classics), the "
             "Verina clone, `benchmarks/datasets/lean_oracle*.py` / `verina_oracle.py` (derivations) and `benchmarks/results/`.", "",
             "## What is in here", "",
             "| dataset | tasks | with a derivation | certified by the engine | re-verified in a fresh Lean process |", "|---|---|---|---|---|"]
    for name, s in summary.items():
        lines.append(f"| {name} | {s['tasks']} | {s['with_derivation']} | {s['certified']} | {s['independently_verified']} |")
    lines += ["", "Kinds of derivation (what the derivation actually contains):", ""]
    for name, s in summary.items():
        lines.append(f"* **{name}**: " + ", ".join(f"{k} {v}" for k, v in sorted(s["kinds"].items())))
    lines += ["", "* `loop`: an invariant-based loop (the algorithmic content);",
              "* `restate`: one `term`/`cases` step for a specification that is already decidable (the derivation shows that "
              "the task is reachable and that the two readings agree; nothing was searched);",
              "* `definitional`: the specification is itself a recursive definition and the answer is that definition.", "",
              "## How to read one task", "",
              "`exports/<dataset>/<task_id>/`:", "",
              "| file | content |", "|---|---|",
              "| `spec.lean` | the specification: helper definitions, `<f>_precond`, `<f>_postcond` |",
              "| `description.md` | the English statement |",
              "| `derivation.md` / `derivation.json` | the derivation: the laws `term`, `cases`, `bind`, `loop` with their conditions, "
              "invariants, variants and helper lemmas |",
              "| `program.lean` | the finished Lean file: the program as a subtype value `{ρ // postcond ρ}`, the plain function, "
              "`<f>_spec_satisfied` and `#print axioms` |",
              "| `status.json` | kind, laws, helper lemmas, certified, independently verified, tests passed |", "",
              "## What the guarantee is", "",
              "A derivation is *certified* when the whole term type-checks in Lean, `#print axioms` lists only `propext`, "
              "`Classical.choice` and `Quot.sound`, and the program passes the task's tests. It is *independently verified* when "
              "the generated file also compiles in a fresh `lake env lean` process with the dataset's own precondition and "
              "postcondition text (`benchmarks/verify_derivations.py`). The specification itself is checked against test data only "
              "(`benchmarks/lean_eval.py validate`): it accepts the expected outputs and rejects the wrong ones; that is evidence "
              "that it says what the English says, not a proof of it.", "",
              "## Tasks without a derivation", "",
              "Listed with the reason in each `index.md` (column *note*) and in `status.json`. Verina tasks that do not compile on "
              "Lean 4.34.1 are blocked by the Lean version, not by the method.", "",
              "## Re-running", "",
              "```", "python benchmarks/lean_eval.py oracles --dataset humaneval     # derive and certify",
              "python benchmarks/verify_derivations.py --dataset lean_specs         # re-verify in fresh Lean processes",
              "python benchmarks/export_dataset.py                                  # regenerate this folder", "```", ""]
    with open(os.path.join(OUT, "README.md"), "w", encoding="utf8", newline="\n") as handle:
        handle.write("\n".join(lines))


if __name__ == "__main__":
    main()
