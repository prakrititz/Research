r"""Hand-written derivations for Verina tasks, batch P: the four two-sum searches (basic_102, advanced_78, 79, 80).

All four are the same program: an outer loop over ``i`` whose body is an inner search for the first ``j > i`` with
``nums[i] + nums[j] = target`` (a ``bind`` over the inner loop). The invariants say what has been excluded, so the first
pair in lexicographic order falls out; the generic step lemmas are ``Refine.ts_*``."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas


def _gen(n, elem, typ, binders, args):
    """The derivation tree and the generic lemma wrappers of a two-sum search over ``elem`` (``nums[i]!`` accessors)."""
    S = lambda a, b: f"{elem}[{a}]! + {elem}[{b}]!"
    T = "target"

    def inner(i, j, jb, ok):
        return (f"{i} + 1 ≤ {j} ∧ {j} ≤ {n} ∧ ({ok} = true → {i} < {jb} ∧ {jb} < {n} ∧ {S(i, jb)} = {T} ∧ "
                f"∀ j', {i} < j' → j' < {jb} → {S(i, chr(106) + chr(39))} ≠ {T}) ∧ "
                f"({ok} = false → ∀ j', {i} < j' → j' < {j} → {S(i, chr(106) + chr(39))} ≠ {T})")

    def outer(i, a, b, f):
        return (f"{i} ≤ {n} ∧ ({f} = true → {a} < {b} ∧ {b} < {n} ∧ {S(a, b)} = {T} ∧ "
                f"(∀ i' j', i' < {a} → i' < j' → j' < {n} → {S(chr(105) + chr(39), chr(106) + chr(39))} ≠ {T}) ∧ "
                f"∀ j', {a} < j' → j' < {b} → {S(a, chr(106) + chr(39))} ≠ {T}) ∧ "
                f"({f} = false → ∀ i' j', i' < {i} → i' < j' → j' < {n} → {S(chr(105) + chr(39), chr(106) + chr(39))} ≠ {T})")

    def prop(jr):
        return (f"({jr}.2 = true → i < {jr}.1 ∧ {jr}.1 < {n} ∧ {S('i', jr + '.1')} = {T} ∧ "
                f"∀ j', i < j' → j' < {jr}.1 → {S('i', chr(106) + chr(39))} ≠ {T}) ∧ "
                f"({jr}.2 = false → ∀ j', i < j' → j' < {n} → {S('i', chr(106) + chr(39))} ≠ {T})")

    hit = f"{S('i', 'j')} = {T}"
    new_jb = f"(if {hit} then j else jb)"
    new_ok = f"(decide ({hit}) || ok)"
    ex = f"(fun a b => {elem}[a]! + {elem}[b]!)"
    jr_b = "(if jr.2 = true then i else a)"
    jr_e = "(if jr.2 = true then jr.1 else b)"
    lemmas = [
        {"name": "ts_in_init", "statement": f"∀ {binders} (i : Nat), i < {n} → {inner('i', '(i + 1)', '0', 'false')}",
         "proof": f"by intro {args} i hi\n  exact Refine.ts_inner_init {ex} {T} {n} i hi"},
        {"name": "ts_in_step",
         "statement": f"∀ {binders} (i j jb : Nat) (ok : Bool), ({inner('i', 'j', 'jb', 'ok')}) → (j < {n} ∧ ok = false) → "
                      f"({inner('i', '(j + 1)', new_jb, new_ok)})",
         "proof": f"by intro {args} i j jb ok hinv hg\n  exact Refine.ts_inner_step {ex} {T} {n} i j jb ok hinv hg"},
        {"name": "ts_in_exit",
         "statement": f"∀ {binders} (i j jb : Nat) (ok : Bool), ({inner('i', 'j', 'jb', 'ok')}) → ¬ (j < {n} ∧ ok = false) → "
                      f"{prop('(jb, ok)')}",
         "proof": f"by intro {args} i j jb ok hinv hn\n  exact Refine.ts_inner_exit {ex} {T} {n} i j jb ok hinv hn"},
        {"name": "ts_out_init", "statement": f"∀ {binders}, {outer('0', '0', '0', 'false')}",
         "proof": f"by intro {args}\n  exact Refine.ts_outer_init {ex} {T} {n}"},
        {"name": "ts_out_step",
         "statement": f"∀ {binders} (i a b : Nat) (found : Bool) (jr : Nat × Bool), ({outer('i', 'a', 'b', 'found')}) → "
                      f"(i < {n} ∧ found = false) → ({prop('jr')}) → "
                      f"({outer('(i + 1)', jr_b, jr_e, '(jr.2 || found)')})",
         "proof": f"by intro {args} i a b found jr hinv hg hjr\n  exact Refine.ts_outer_step {ex} {T} {n} i a b found jr hinv hg hjr"},
    ]
    inner_loop = loop([["j", "Nat"], ["jb", "Nat"], ["ok", "Bool"]], ["i + 1", "0", "false"], inner("i", "j", "jb", "ok"),
                      f"j < {n} ∧ ok = false", f"{n} - j", "(jb, ok)",
                      term(f"(j + 1, if {hit} then j else jb, decide ({hit}) || ok)"))
    return S, outer, lemmas, inner_loop, prop


def two_sum(n, elem, typ, binders, args, result_expr, exit_lemmas):
    S, outer, lemmas, inner_loop, prop = _gen(n, elem, typ, binders, args)
    body = bind("jr", "Nat × Bool", prop("jr"), inner_loop,
                term("(i + 1, if jr.2 = true then i else a, if jr.2 = true then jr.1 else b, jr.2 || found)"))
    tree = loop([["i", "Nat"], ["a", "Nat"], ["b", "Nat"], ["found", "Bool"]], ["0", "0", "0", "false"],
                outer("i", "a", "b", "found"), f"i < {n} ∧ found = false", f"{n} - i", result_expr, body)
    return with_lemmas(tree, lemmas + exit_lemmas), outer


# --- advanced_79: Option (Nat × Nat), lexicographically first -----------------------------------------------------------------
def _task79():
    n, elem = "nums.length", "nums"
    binders, args = "(nums : List Int) (target : Int)", "nums target"
    S = lambda a, b: f"nums[{a}]! + nums[{b}]!"
    _, outer0, *_ = _gen(n, elem, "List Int", binders, args)
    inv = outer0("i", "a", "b", "found")
    exit_l = {
        "name": "exit79",
        "statement": f"∀ {binders} (h : twoSum_precond nums target) (i a b : Nat) (found : Bool), ({inv}) → ¬ (i < {n} ∧ found = false) → "
                     "twoSum_postcond nums target (if found = true then some (a, b) else none) h",
        "proof": f"by intro {args} h i a b found hinv hn\n  obtain ⟨hi, hf1, hf2⟩ := hinv\n  unfold twoSum_postcond\n"
                 "  by_cases hf : found = true\n  · rw [if_pos hf]\n    obtain ⟨hab, hb, hs, h1, h2⟩ := hf1 hf\n"
                 "    obtain ⟨l1, l2⟩ := Refine.ts_lex_all nums target a b hb h1 h2\n    exact ⟨hab, hb, hs, l1, l2⟩\n"
                 "  · have hff : found = false := by simpa using hf\n    rw [if_neg hf]\n"
                 "    have hin : i = nums.length := by\n      by_contra hne\n      exact hn ⟨by omega, hff⟩\n    subst hin\n"
                 "    exact Refine.ts_pairwise_none nums target (fun i' j' hij hj => hf2 hff i' j' (by omega) hij hj)"}
    return two_sum(n, elem, "List Int", binders, args, "if found = true then some (a, b) else none", [exit_l])[0]


# --- advanced_78: Nat × Nat, a pair is guaranteed by the precondition ----------------------------------------------------------
def _task78():
    n, elem = "nums.length", "nums"
    binders, args = "(nums : List Int) (target : Int)", "nums target"
    _, outer0, *_ = _gen(n, elem, "List Int", binders, args)
    inv = outer0("i", "a", "b", "found")
    exists_l = {
        "name": "exists78",
        "statement": "∀ (nums : List Int) (target : Int), (let pairwiseSum := List.range nums.length |>.flatMap (fun i => "
                     "nums.drop (i + 1) |>.map (fun y => nums[i]! + y)); nums.length > 1 ∧ pairwiseSum.count target = 1) → "
                     "∃ i j, i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target",
        "proof": "by intro nums target h\n  obtain ⟨_, hc⟩ := h\n"
                 "  have hmem : target ∈ ((List.range nums.length).flatMap (fun i => (nums.drop (i + 1)).map (fun y => nums[i]! + y))) :=\n"
                 "    List.count_pos_iff.mp (by omega)\n"
                 "  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hmem\n  obtain ⟨y, hy1, hy2⟩ := List.mem_map.mp hy\n"
                 "  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy1\n  simp only [List.length_drop] at hk\n"
                 "  have hi' := List.mem_range.mp hi\n  refine ⟨i, i + 1 + k, by omega, by omega, ?_⟩\n"
                 "  rw [List.getElem_drop] at hy2\n  rw [getElem!_pos nums (i + 1 + k) (by omega)]\n  exact hy2"}
    exit_l = {
        "name": "exit78",
        "statement": f"∀ {binders} (h : twoSum_precond nums target) (i a b : Nat) (found : Bool), ({inv}) → ¬ (i < {n} ∧ found = false) → "
                     "twoSum_postcond nums target (a, b) h",
        "proof": f"by intro {args} h i a b found hinv hn\n  obtain ⟨hi, hf1, hf2⟩ := hinv\n  unfold twoSum_postcond\n"
                 "  by_cases hf : found = true\n  · obtain ⟨hab, hb, hs, _, _⟩ := hf1 hf\n    exact ⟨hab, by omega, hb, hs⟩\n"
                 "  · exfalso\n    have hff : found = false := by simpa using hf\n"
                 "    have hin : i = nums.length := by\n      by_contra hne\n      exact hn ⟨by omega, hff⟩\n"
                 "    obtain ⟨i', j', hij, hj, hs⟩ := exists78 nums target h\n"
                 "    exact hf2 hff i' j' (by omega) hij hj hs"}
    return two_sum(n, elem, "List Int", binders, args, "(a, b)", [exists_l, exit_l])[0]


# --- advanced_80: Array result #[a, b] ------------------------------------------------------------------------------------------
def _task80():
    n, elem = "nums.size", "nums"
    binders, args = "(nums : Array Int) (target : Int)", "nums target"
    _, outer0, *_ = _gen(n, elem, "Array Int", binders, args)
    inv = outer0("i", "a", "b", "found")
    exit_l = {
        "name": "exit80",
        "statement": f"∀ {binders} (h : twoSum_precond nums target) (i a b : Nat) (found : Bool), ({inv}) → ¬ (i < {n} ∧ found = false) → "
                     "twoSum_postcond nums target #[a, b] h",
        "proof": f"by intro {args} h i a b found hinv hn\n  obtain ⟨hi, hf1, hf2⟩ := hinv\n  unfold twoSum_postcond\n"
                 "  by_cases hf : found = true\n  · obtain ⟨hab, hb, hs, _, _⟩ := hf1 hf\n"
                 "    exact ⟨by simp, by simpa using (by omega : a < nums.size), by simpa using hb, by simpa using hab, by simpa using hs⟩\n"
                 "  · exfalso\n    have hff : found = false := by simpa using hf\n"
                 "    have hin : i = nums.size := by\n      by_contra hne\n      exact hn ⟨by omega, hff⟩\n"
                 "    obtain ⟨_, hany, _⟩ := h\n    obtain ⟨i', hi', hj⟩ := List.any_eq_true.mp hany\n"
                 "    obtain ⟨j', hj', hs⟩ := List.any_eq_true.mp hj\n"
                 "    have hi'' := List.mem_range.mp hi'\n    have hj'' := List.mem_range.mp hj'\n"
                 "    have hs' : nums[i']! + nums[j']! = target := by simpa using hs\n"
                 "    exact hf2 hff j' i' (by omega) hj'' hi'' (by omega)"}
    return two_sum(n, elem, "Array Int", binders, args, "#[a, b]", [exit_l])[0]


# --- basic_102: Array nums, the pair is guaranteed by the precondition (not Pairwise) -----------------------------------------------
def _task102():
    n, elem = "nums.size", "nums"
    binders, args = "(nums : Array Int) (target : Int)", "nums target"
    _, outer0, *_ = _gen(n, elem, "Array Int", binders, args)
    inv = outer0("i", "a", "b", "found")
    exit_l = {
        "name": "exit102",
        "statement": f"∀ {binders} (h : twoSum_precond nums target) (i a b : Nat) (found : Bool), ({inv}) → ¬ (i < {n} ∧ found = false) → "
                     "twoSum_postcond nums target (a, b) h",
        "proof": f"by intro {args} h i a b found hinv hn\n  obtain ⟨hi, hf1, hf2⟩ := hinv\n  unfold twoSum_postcond\n"
                 "  by_cases hf : found = true\n  · obtain ⟨hab, hb, hs, h1, h2⟩ := hf1 hf\n"
                 "    have hb' : b < nums.toList.length := by simpa using hb\n"
                 "    have hab' : a < nums.size := by omega\n"
                 "    obtain ⟨l1, l2⟩ := Refine.ts_lex_all nums.toList target a b hb'\n"
                 "      (fun i' j' hi' hij hj => by\n"
                 "        have hj' : j' < nums.size := by simpa using hj\n"
                 "        rw [Refine.toList_getElem_bang nums i' (by omega), Refine.toList_getElem_bang nums j' hj']\n"
                 "        exact h1 i' j' hi' hij hj')\n"
                 "      (fun j' ha hjb => by\n"
                 "        rw [Refine.toList_getElem_bang nums a hab', Refine.toList_getElem_bang nums j' (by omega)]\n"
                 "        exact h2 j' ha hjb)\n"
                 "    rw [Refine.toList_getElem_bang nums a hab'] at l2\n"
                 "    exact ⟨hab, hb, hs, l1, l2⟩\n"
                 "  · exfalso\n    have hff : found = false := by simpa using hf\n"
                 "    have hin : i = nums.size := by\n      by_contra hne\n      exact hn ⟨by omega, hff⟩\n"
                 "    apply h.2\n"
                 "    exact Refine.ts_pairwise_none nums.toList target (fun i' j' hij hj => by\n"
                 "      have hj' : j' < nums.size := by simpa using hj\n"
                 "      rw [Refine.toList_getElem_bang nums i' (by omega), Refine.toList_getElem_bang nums j' hj']\n"
                 "      exact hf2 hff i' j' (by omega) hij hj')"}
    return two_sum(n, elem, "Array Int", binders, args, "(a, b)", [exit_l])[0]


ORACLES_MORE = {
    "verina_basic_102": _task102(),
    "verina_advanced_79": _task79(),
    "verina_advanced_78": _task78(),
    "verina_advanced_80": _task80(),
}
