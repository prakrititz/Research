r"""Hand-written derivations for Verina tasks, batch I (advanced, family 1: "the maximum over an enumerated list").

The specification of these tasks enumerates all subsequences (or subarrays) and demands a result that is *a member of* the list of their
lengths/sums and *at least* every member. The derivation is the brute force the specification describes: ``foldl max`` over the same
list, with the lemma that the maximum of a non-empty list is a member and an upper bound. They are labelled ``restate`` in the exports."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

R = "Refine."


def allsub(var: str) -> str:
    return f"({var}.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse"


def lis_lets(var: str) -> str:
    return (f"let allSubseq := {allsub(var)}; "
            "let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); ")


def lemma(name, fn, binders, args, expr, proof_tail, hyp=None):
    """``∀ binders (h : fn_precond args), [hyp →] fn_postcond args (expr) h`` proved by ``intro; unfold; <tail>``."""
    intro = " ".join(args)
    cond = f"{hyp} → " if hyp else ""
    hx = " hx" if hyp else ""
    return {"name": name,
            "statement": f"∀ {binders} (h : {fn}_precond {intro}), {cond}{fn}_postcond {intro} ({expr}) h",
            "proof": f"by intro {intro} h{hx}\n  unfold {fn}_postcond\n  {proof_tail}"}


def lis(task, fn, var, typ, result_nat=True):
    expr = lis_lets(var) + "increasingSubseqLens.foldl max 0"
    inner = f"Refine.allsub_rev_nil_mem {var}" if typ != "Array Int" else f"List.mem_map.mpr ⟨[], Refine.allsub_nil_mem_arr {var}, rfl⟩"
    nonempty = (f"(List.ne_nil_of_mem (a := 0) (List.mem_map.mpr ⟨[], List.mem_filter.mpr ⟨{inner}, by simp⟩, rfl⟩))")
    tail = f"exact Refine.maxlist_nat _ {nonempty}"
    return with_lemmas(term(f"({expr})"), [lemma(f"{fn}_ok", fn, f"({var} : {typ})", [var], expr, tail)])


def lis_int(fn, var, typ):
    """Same, for the tasks whose result is an ``Int`` (the lengths are ``Int`` there)."""
    expr = lis_lets(var) + "increasingSubseqLens.foldl max (increasingSubseqLens.headD 0)"
    inner = f"Refine.allsub_rev_nil_mem {var}" if typ != "Array Int" else f"List.mem_map.mpr ⟨[], Refine.allsub_nil_mem_arr {var}, rfl⟩"
    nonempty = f"(List.ne_nil_of_mem (a := 0) (List.mem_map.mpr ⟨[], List.mem_filter.mpr ⟨{inner}, by simp⟩, rfl⟩))"
    return with_lemmas(term(f"({expr})"), [lemma(f"{fn}_ok", fn, f"({var} : {typ})", [var], expr, f"exact Refine.maxlist_int _ {nonempty}")])


def lcs(fn):
    lets = ("let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; "
            "let subseqA := allSubseq a; let subseqB := allSubseq b; "
            "let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length); ")
    expr = lets + "commonSubseqLens.foldl max (commonSubseqLens.headD 0)"
    mem = lambda v: f"(List.mem_map.mpr ⟨[], Refine.allsub_nil_mem_arr {v}, rfl⟩)"
    nonempty = (f"(List.ne_nil_of_mem (a := 0) (List.mem_map.mpr ⟨[], List.mem_filter.mpr ⟨{mem('a')}, "
                f"List.contains_iff_mem.mpr {mem('b')}⟩, rfl⟩))")
    return with_lemmas(term(f"({expr})"), [lemma(f"{fn}_ok", fn, "(a b : Array Int)", ["a", "b"], expr,
                                                 f"exact Refine.maxlist_int _ {nonempty}")])


def post_lemma(name, fn, binders, args, expr, tail):
    return lemma(name, fn, binders, args, expr, tail)


_LCS_STR_LETS = ("let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; "
                 "let subseqA := allSubseq s1.toList; let subseqB := allSubseq s2.toList; "
                 "let commonSubseq := subseqA.filter (fun l => subseqB.contains l); ")
_LCS_STR_EXPR = _LCS_STR_LETS + "String.mk (commonSubseq.foldl (fun best l => if best.length < l.length then l else best) [])"
_LCS_STR_TAIL = (
    "intro allSubseq subseqA subseqB commonSubseq\n"
    "  have hnil : [] ∈ commonSubseq := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨[], Refine.allsub_nil_mem s1.toList [[]] (by simp), rfl⟩, "
    "List.contains_iff_mem.mpr (List.mem_map.mpr ⟨[], Refine.allsub_nil_mem s2.toList [[]] (by simp), rfl⟩)⟩\n"
    "  exact lcs_str_spec commonSubseq hnil")
_LCS_STR_SPEC = {
    "name": "lcs_str_spec",
    "statement": "∀ (L : List (List Char)), [] ∈ L → "
                 "L.contains (String.mk (L.foldl (fun best l => if best.length < l.length then l else best) [])).toList = true ∧ "
                 "L.all (fun l => decide (l.length ≤ (String.mk (L.foldl (fun best l => if best.length < l.length then l else best) [])).length)) = true",
    "proof": "by intro L hn\n  have hs := Refine.longest_spec L hn\n  rw [Refine.string_toList_mk, Refine.string_length_mk]\n  exact hs"}

_SUM = "(fun len => numbers.drop start |>.take len |>.sum)"
_SUMS46 = ("let subArraySums := List.range (numbers.length + 1) |>.flatMap (fun start => "
           f"List.range (numbers.length - start + 1) |>.map {_SUM}); ")


def maxsum(fn, var, lets, name, nonempty):
    expr = lets + f"{name}.foldl max ({name}.headD 0)"
    return with_lemmas(term(f"({expr})"), [lemma(f"{fn}_ok", fn, f"({var} : List Int)", [var], expr,
                                                 f"exact Refine.maxlist_int _ {nonempty}")])


_S45 = ("let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start => "
        "List.range' 1 (xs.length - start) |>.map (fun len => ((xs.drop start).take len).sum)); ")
_S75 = ("let subArrays := List.range (sequence.length + 1) |>.flatMap (fun start => "
        "List.range (sequence.length - start + 1) |>.map (fun len => sequence.drop start |>.take len)); "
        "let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum); ")
_S43 = "let sublists := nums.sublists.filter (· ≠ []); let products := sublists.map (List.foldl (· * ·) 1); "
_S44 = ("let subarrays := List.range (arr.size) |>.flatMap (fun start => "
        "List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len))); "
        "let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k.toNat = 0 && subarray.size > 0); "
        "let subarraySums := divisibleSubarrays.map (fun subarray => subarray.toList.sum); ")
_S29 = ("let subArrays := List.range (nums.length + 1) |>.flatMap (fun start => "
        "List.range (nums.length - start + 1) |>.map (fun len => nums.drop start |>.take len)); "
        "let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x)); "
        "let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k)); ")
_S28 = ("let sorted_nums := nums.mergeSort; "
        "let consec_sublist_lens := List.range nums.length |>.flatMap (fun start => "
        "List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) "
        "|>.filter isConsecutive |>.map (·.length); ")
_S38 = ("(fun (i : Nat) => let remaining := List.eraseIdx intervals i; "
        "let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1); "
        "let merged := sorted.foldl (fun acc curr => match acc with | [] => [curr] | (s, e) :: rest => "
        "if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc) []; "
        "merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0)")

ORACLES_MORE = {
    "verina_advanced_45": cases(
        "xs = []", with_lemmas(term("0"), [lemma("ms45_nil", "maxSubarraySum", "(xs : List Int)", ["xs"], "0",
                                                  "subst hx; simp", hyp="xs = []")]),
        with_lemmas(term(f"({_S45}subarray_sums.foldl max (subarray_sums.headD 0))"),
                    [lemma("ms45_ne", "maxSubarraySum", "(xs : List Int)", ["xs"],
                           f"{_S45}subarray_sums.foldl max (subarray_sums.headD 0)",
                           "obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hx\n  "
                           "exact Refine.maxlist_int_any _ (List.ne_nil_of_mem (a := ((([x] ++ t).drop 0).take 1).sum) "
                           "(List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by simp), "
                           "List.mem_map.mpr ⟨1, by simp [List.mem_range'_1], rfl⟩⟩))", hyp="xs ≠ []")])),
    "verina_advanced_75": with_lemmas(
        term(f"({_S75}subArraySums.foldl max (subArraySums.headD 0))"),
        [lemma("ms75", "task_code", "(sequence : List Int)", ["sequence"], f"{_S75}subArraySums.foldl max (subArraySums.headD 0)",
               "exact Refine.maxlist_int _ (List.ne_nil_of_mem (a := ((sequence.drop 0).take 1).sum) "
               "(List.mem_map.mpr ⟨(sequence.drop 0).take 1, List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨0, "
               "List.mem_range.mpr (by omega), List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩⟩, "
               "by rcases sequence with _ | ⟨x, t⟩ <;> simp_all⟩, rfl⟩))")]),
    "verina_advanced_43": with_lemmas(
        term(f"({_S43}products.foldl max (products.headD 0))"),
        [lemma("ms43", "maxStrength", "(nums : List Int)", ["nums"], f"{_S43}products.foldl max (products.headD 0)",
               "obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h\n  "
               "exact Refine.maxlist_int _ (List.ne_nil_of_mem (a := List.foldl (· * ·) 1 [x]) "
               "(List.mem_map.mpr ⟨[x], List.mem_filter.mpr ⟨List.mem_sublists.mpr (by simp), by simp⟩, rfl⟩))")]),
}

_UNUSED = {
    "verina_advanced_27": with_lemmas(
        term(f"({_LCS_STR_EXPR})"),
        [_LCS_STR_SPEC, lemma("lcs_str_ok", "longestCommonSubsequence", "(s1 s2 : String)", ["s1", "s2"], _LCS_STR_EXPR, _LCS_STR_TAIL)]),
    "verina_advanced_46": maxsum(
        "maxSubarraySum", "numbers", _SUMS46, "subArraySums",
        "(List.ne_nil_of_mem (a := 0) (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by omega), "
        "List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩⟩))"),
    "verina_advanced_34": lis_int("longestIncreasingSubsequence", "nums", "List Int"),
    "verina_advanced_4": lis_int("LongestIncreasingSubsequence", "a", "Array Int"),
    "verina_advanced_2": lcs("LongestCommonSubsequence"),
    "verina_advanced_3": lcs("LongestCommonSubsequence"),
    "verina_advanced_25": lis("25", "lengthOfLIS", "nums", "List Int"),
    "verina_advanced_31": lis("31", "longestIncreasingSubseqLength", "xs", "List Int"),
    "verina_advanced_32": lis("32", "longestIncreasingSubsequence", "numbers", "List Int"),
    "verina_advanced_33": lis("33", "longestIncreasingSubsequence", "nums", "List Int"),
}

ORACLES_MORE.update(_UNUSED)
