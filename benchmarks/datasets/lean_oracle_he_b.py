r"""Hand-written derivations for HumanEval problems that needed a heavier invariant or a lemma (batch file B)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_ROLL = [
    {
        "name": "foldl_max_facts",
        "statement": "∀ (l : List Int) (m : Int), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l",
        "proof": "by\n  intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n    obtain ⟨h1, h2, h3⟩ := ih (max m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n    · rcases h1 with h | h\n      · by_cases hm : m ≤ a\n        · right; rw [max_eq_right hm] at h ⊢; rw [h]; simp\n        · left\n          have hmx : max m a = m := max_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans (le_max_left m a) h2\n    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans (le_max_right m x) h2\n      · exact h3 x hx'"
    },
    {
        "name": "rolling_ok",
        "statement": "∀ (numbers : List Int), ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)).length = numbers.length ∧ ∀ i, i < numbers.length → ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]!",
        "proof": "by\n  intro numbers\n  refine ⟨by simp, ?_⟩\n  intro i hi\n  have hget : ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]! =\n      (numbers.take (i + 1)).foldl max numbers[0]! := by\n    rw [getElem!_pos _ i (by simpa using hi)]\n    simp\n  rw [hget]\n  obtain ⟨h1, h2, h3⟩ := foldl_max_facts (numbers.take (i + 1)) numbers[0]!\n  refine ⟨?_, h3⟩\n  rcases h1 with h | h\n  · rw [h]\n    have : numbers[0]! ∈ numbers.take (i + 1) := by\n      rw [getElem!_pos numbers 0 (by omega)]\n      exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩\n    exact this\n  · exact h"
    }
]
_INTER = [
    {
        "name": "append_pair_idx",
        "statement": "∀ (a : List Int) (d x : Int) (j : Nat), (a ++ [d, x])[j]! = (if j < a.length then a[j]! else if j = a.length then d else if j = a.length + 1 then x else default)",
        "proof": "by\n  intro a d x j\n  by_cases h : j < a.length\n  · rw [if_pos h]; exact Refine.getElem_bang_append_lt a [d, x] j h\n  · rw [if_neg h]\n    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega : a.length ≤ j)]\n    by_cases h2 : j = a.length\n    · subst h2; simp\n    · rw [if_neg h2]\n      by_cases h3 : j = a.length + 1\n      · subst h3; simp\n      · rw [if_neg h3]\n        have : j - a.length ≥ 2 := by omega\n        simp [List.getElem?_eq_none (by simp; omega : [d, x].length ≤ j - a.length)]"
    }
]

_SORT116 = [
    {
        "name": "sort116_ok",
        "statement": "∀ (L : List Int), (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).length - 1 → (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! < ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∨ (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! = ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∧ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! ≤ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]!))",
        "proof": "by\n  intro L\n  have htrans : ∀ (a b c : Int), (decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))) = true →\n      (decide (ones b < ones c) || (ones b == ones c && decide (b ≤ c))) = true →\n      (decide (ones a < ones c) || (ones a == ones c && decide (a ≤ c))) = true := by\n    intro a b c h1 h2\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *\n    omega\n  have htotal : ∀ (a b : Int), ((decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))) ||\n      (decide (ones b < ones a) || (ones b == ones a && decide (b ≤ a)))) = true := by\n    intro a b\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]\n    omega\n  have hp : (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).Perm L :=\n    List.mergeSort_perm L _\n  have hs := List.pairwise_mergeSort htrans htotal L\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] using this"
    }
]
_SORT_NAT_ASC = [
    {
        "name": "sortNat_ok",
        "statement": "∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!",
        "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≤ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (L.mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≤ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
    }
]
_SORT_NAT_DESC = [
    {
        "name": "sortNatDesc_ok",
        "statement": "∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≥ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≥ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (L.mergeSort (fun a b => decide (a ≥ b)))[i + 1]!",
        "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≥ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≥ b) = true) (L.mergeSort (fun a b => decide (a ≥ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≥ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
    }
]

_MINSUB = [
    {
        "name": "foldl_min_facts",
        "statement": "∀ (l : List Int) (m : Int), (List.foldl min m l = m ∨ List.foldl min m l ∈ l) ∧ List.foldl min m l ≤ m ∧ ∀ x ∈ l, List.foldl min m l ≤ x",
        "proof": "by\n  intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n    obtain ⟨h1, h2, h3⟩ := ih (min m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n    · rcases h1 with h | h\n      · by_cases hm : a ≤ m\n        · right; rw [min_eq_right hm] at h ⊢; rw [h]; simp\n        · left\n          have hmx : min m a = m := min_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans h2 (min_le_left m a)\n    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans h2 (min_le_right m x)\n      · exact h3 x hx'"
    },
    {
        "name": "minsub_ok",
        "statement": "∀ (nums : List Int), nums ≠ [] → (∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum))) ≤ ((nums.drop i).take (j - i)).sum",
        "proof": "by\n  intro nums hne\n  obtain ⟨h1, h2, h3⟩ := foldl_min_facts ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum))) nums[0]!\n  refine ⟨?_, ?_⟩\n  · rcases h1 with h | h\n    · have hlen : 0 < nums.length := List.length_pos_iff.mpr hne\n      refine ⟨1, by omega, 0, by omega, ?_⟩\n      rw [h]\n      cases nums with\n      | nil => exact absurd rfl hne\n      | cons a t => simp\n    · rw [List.mem_flatMap] at h\n      obtain ⟨j, hj, hi⟩ := h\n      rw [List.mem_map] at hi\n      obtain ⟨i, hi', hs⟩ := hi\n      rw [List.mem_range] at hj hi'\n      exact ⟨j, by omega, i, hi', hs⟩\n  · intro j hj i hi\n    apply h3\n    rw [List.mem_flatMap]\n    exact ⟨j, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩"
    }
]
_ANYINT = [
    {
        "name": "anyint_post",
        "statement": "∀ (x y z : PyVal) (h : anyInt_precond x y z), anyInt_postcond x y z ((fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z)) h",
        "proof": "by\n  intro x y z h\n  unfold anyInt_postcond\n  cases x <;> cases y <;> cases z <;> simp"
    }
]
_VOWEL_STEP = [
    {
        "name": "vowel_step",
        "statement": "∀ (w : List Char) (i : Nat) (b : Option Nat), (i ≤ w.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt w j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt w c ∧ ∀ j, j < i → c < j → ¬ goodAt w j))) → i < w.length → (i + 1 ≤ w.length ∧ (((if goodAt w i then some i else b) = none ∧ ∀ j, j < i + 1 → ¬ goodAt w j) ∨ (∃ c, (if goodAt w i then some i else b) = some c ∧ c < i + 1 ∧ goodAt w c ∧ ∀ j, j < i + 1 → c < j → ¬ goodAt w j)))",
        "proof": "by\n  intro w i b h hi\n  obtain ⟨_, hb⟩ := h\n  refine ⟨by omega, ?_⟩\n  by_cases hg : goodAt w i\n  · right\n    refine ⟨i, by rw [if_pos hg], by omega, hg, ?_⟩\n    intro j hj hij; omega\n  · rw [if_neg hg]\n    rcases hb with ⟨rfl, hn⟩ | ⟨c, rfl, hc, hgc, hmax⟩\n    · left\n      refine ⟨rfl, ?_⟩\n      intro j hj\n      by_cases hji : j < i\n      · exact hn j hji\n      · have : j = i := by omega\n        subst this; exact hg\n    · right\n      refine ⟨c, rfl, by omega, hgc, ?_⟩\n      intro j hj hcj\n      by_cases hji : j < i\n      · exact hmax j hji hcj\n      · have : j = i := by omega\n        subst this; exact hg"
    },
    {
        "name": "vowel_none",
        "statement": "∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → last = none → ((\"\" = \"\" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ (\"\" ≠ \"\" → ∃ i, i < w.length ∧ goodAt w i ∧ \"\" = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))",
        "proof": "by\n  intro w last h hn\n  rcases h with ⟨_, hnone⟩ | ⟨b, hb, _⟩\n  · exact ⟨⟨fun _ => hnone, fun _ => rfl⟩, fun h => absurd rfl h⟩\n  · rw [hn] at hb; exact absurd hb (by simp)"
    },
    {
        "name": "vowel_some",
        "statement": "∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → ¬ last = none → ((String.singleton w[last.getD 0]! = \"\" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ (String.singleton w[last.getD 0]! ≠ \"\" → ∃ i, i < w.length ∧ goodAt w i ∧ String.singleton w[last.getD 0]! = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))",
        "proof": "by\n  intro w last h hn\n  rcases h with ⟨hnone, _⟩ | ⟨b, rfl, hb, hg, hmax⟩\n  · exact absurd hnone hn\n  · have hne : String.singleton w[b]! ≠ \"\" := by\n      intro h\n      have := congrArg String.length h\n      simp at this\n    exact ⟨⟨fun h => absurd h hne, fun hn => absurd hg (hn b hb)⟩, fun _ => ⟨b, hb, hg, rfl, hmax⟩⟩"
    }
]

_PLUCK = [
    {
        "name": "pluck_exit",
        "statement": "∀ (arr : List Nat) (f : Bool) (v ix : Nat), (arr.length ≤ arr.length ∧ (f = true ↔ ∃ k, k < arr.length ∧ arr[k]! % 2 = 0) ∧ (f = true → ix < arr.length ∧ arr[ix]! = v ∧ v % 2 = 0 ∧ (∀ k, k < arr.length → arr[k]! % 2 = 0 → v ≤ arr[k]!) ∧ ∀ j, j < ix → arr[j]! ≠ v)) → (((if f = true then [v, ix] else []) = [] ↔ ∀ x ∈ arr, x % 2 = 1) ∧ ((if f = true then [v, ix] else []) ≠ [] → (if f = true then [v, ix] else []).length = 2 ∧ (if f = true then [v, ix] else [])[1]! < arr.length ∧ arr[(if f = true then [v, ix] else [])[1]!]! = (if f = true then [v, ix] else [])[0]! ∧ (if f = true then [v, ix] else [])[0]! % 2 = 0 ∧ (∀ x ∈ arr, x % 2 = 0 → (if f = true then [v, ix] else [])[0]! ≤ x) ∧ ∀ j, j < (if f = true then [v, ix] else [])[1]! → arr[j]! ≠ (if f = true then [v, ix] else [])[0]!))",
        "proof": "by\n  intro arr f v ix h\n  obtain ⟨_, hf, hd⟩ := h\n  by_cases hfl : f = true\n  · obtain ⟨hix, hv, hev, hmin, hj⟩ := hd hfl\n    rw [if_pos hfl]\n    refine ⟨⟨fun h => absurd h (by simp), fun h => ?_⟩, fun _ => ⟨by simp, by simpa using hix, by simpa using hv, by simpa using hev, ?_, by simpa using hj⟩⟩\n    · obtain ⟨k, hk, hek⟩ := hf.mp hfl\n      have := h arr[k]! (by rw [getElem!_pos arr k hk]; exact List.getElem_mem hk)\n      omega\n    · intro x hx hxe\n      obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx arr x).mp hx\n      simpa using hmin k hk hxe\n  · rw [if_neg hfl]\n    refine ⟨⟨fun _ => ?_, fun _ => by simp⟩, fun h => absurd rfl h⟩\n    intro x hx\n    obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx arr x).mp hx\n    by_contra hne\n    exact hfl (hf.mpr ⟨k, hk, by omega⟩)"
    }
]
_SKJ = [
    {
        "name": "skj_exit",
        "statement": "∀ (lst : List Nat) (best : Nat), (∃ x ∈ lst, Nat.Prime x) → (lst.length ≤ lst.length ∧ (best = 0 ∨ ∃ k, k < lst.length ∧ lst[k]! = best ∧ Nat.Prime best) ∧ ∀ k, k < lst.length → Nat.Prime lst[k]! → lst[k]! ≤ best) → ∃ p ∈ lst, Nat.Prime p ∧ (∀ x ∈ lst, Nat.Prime x → x ≤ p) ∧ ((toString best).toList.map (fun c => c.toNat - '0'.toNat)).sum = ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum",
        "proof": "by\n  intro lst best hex h\n  obtain ⟨_, hb, hmax⟩ := h\n  obtain ⟨x, hx, hxp⟩ := hex\n  obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n  have hle := hmax k hk hxp\n  have h2 : 2 ≤ lst[k]! := hxp.two_le\n  rcases hb with h0 | ⟨j, hj, hjb, hbp⟩\n  · omega\n  · refine ⟨best, ?_, hbp, ?_, rfl⟩\n    · rw [← hjb]; rw [getElem!_pos lst j hj]; exact List.getElem_mem hj\n    · intro y hy hyp\n      obtain ⟨m, hm, rfl⟩ := (Refine.mem_iff_idx lst y).mp hy\n      exact hmax m hm hyp"
    }
]
_LPF = [
    {
        "name": "lpf_exit",
        "statement": "∀ (n q : Nat), n > 1 → (1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False) → ¬ (1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)) → (Nat.Prime q ∧ q ∣ n ∧ ∀ q2, q2 < n + 1 → Nat.Prime q2 → q2 ∣ n → q2 ≤ q)",
        "proof": "by\n  intro n q hn h hg\n  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)\n  have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpd\n  by_cases h1 : 1 < q\n  · have hpq : Nat.Prime q ∧ n % q = 0 := by\n      by_contra hc\n      exact hg ⟨h1, hc⟩\n    refine ⟨hpq.1, Nat.dvd_of_mod_eq_zero hpq.2, ?_⟩\n    intro r hr hrp hrd\n    by_contra hlt\n    exact h.2.2 r hr (by omega) hrp hrd\n  · exfalso\n    exact h.2.2 p (by omega) (by have := hp.two_le; omega) hp hpd"
    },
    {
        "name": "lpf_step",
        "statement": "∀ (n q : Nat), (1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False) → (1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)) → (1 ≤ q - 1 ∧ q - 1 ≤ n ∧ ∀ r, r < n + 1 → q - 1 < r → Nat.Prime r → r ∣ n → False)",
        "proof": "by\n  intro n q h hg\n  refine ⟨by omega, by omega, ?_⟩\n  intro r hr hqr hrp hrd\n  by_cases hrq : r = q\n  · subst hrq\n    exact hg.2 ⟨hrp, Nat.mod_eq_zero_of_dvd hrd⟩\n  · exact h.2.2 r hr (by omega) hrp hrd"
    }
]
_SEARCH = [
    {
        "name": "search_exit",
        "statement": "∀ (lst : List Nat) (best : Int), (lst.length ≤ lst.length ∧ ((best = -1 ∧ ∀ k, k < lst.length → lst.count lst[k]! < lst[k]!) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ lst.count best.toNat ≥ best.toNat ∧ ∀ k, k < lst.length → lst.count lst[k]! ≥ lst[k]! → lst[k]! ≤ best.toNat))) → ((best = -1 ∧ ∀ x ∈ lst, lst.count x < x) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ lst.count best.toNat ≥ best.toNat ∧ ∀ x ∈ lst, lst.count x ≥ x → x ≤ best.toNat))",
        "proof": "by\n  intro lst best h\n  obtain ⟨_, h⟩ := h\n  rcases h with ⟨hb, hall⟩ | ⟨hb, hm, hc, hmax⟩\n  · left\n    refine ⟨hb, ?_⟩\n    intro x hx\n    obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n    exact hall k hk\n  · right\n    refine ⟨hb, hm, hc, ?_⟩\n    intro x hx hxc\n    obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n    exact hmax k hk hxc"
    }
]

_BIN079 = [
    {
        "name": "toDigits2_binary",
        "statement": "∀ (v : Nat), isBinary (Nat.toDigits 2 v) v",
        "proof": "by\n  intro v\n  induction v using Nat.strong_induction_on with\n  | _ v ih =>\n    by_cases h0 : v = 0\n    · subst h0\n      simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n    · by_cases h1 : v / 2 = 0\n      · have hv : v = 1 := by omega\n        subst hv\n        simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n      · have hlt : v / 2 < v := by omega\n        have ihv := ih (v / 2) hlt\n        have hsplit : Nat.toDigits 2 v = Nat.toDigits 2 (v / 2) ++ Nat.toDigits 2 (v % 2) := by\n          rw [Nat.toDigits_append_toDigits (by norm_num) (by omega) (by omega)]\n          congr 1; omega\n        have hbit : Nat.toDigits 2 (v % 2) = [if v % 2 = 1 then '1' else '0'] := by\n          rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, Nat.toDigits, Nat.toDigitsCore]\n        rw [hsplit, hbit]\n        obtain ⟨ha, hf, _, hh⟩ := ihv\n        refine ⟨?_, ?_, ?_, ?_⟩\n        · simp only [List.all_append, Bool.and_eq_true] \n          refine ⟨ha, ?_⟩\n          split <;> simp\n        · rw [List.foldl_append, hf]\n          simp only [List.foldl_cons, List.foldl_nil]\n          split <;> simp_all <;> omega\n        · intro hz; omega\n        · intro _\n          have hh' := hh (by omega)\n          cases hA : Nat.toDigits 2 (v / 2) with\n          | nil => rw [hA] at hh'; simp at hh'\n          | cons a t => rw [hA] at hh'; simpa using hh'"
    },
    {
        "name": "toDigits2_ne_nil",
        "statement": "∀ (v : Nat), Nat.toDigits 2 v ≠ []",
        "proof": "by\n  intro v h\n  obtain ⟨_, _, h0, hh⟩ := toDigits2_binary v\n  by_cases hv : v = 0\n  · have := h0 hv; rw [h] at this; simp at this\n  · have := hh (by omega); rw [h] at this; simp at this"
    },
    {
        "name": "db_ok",
        "statement": "∀ (v : Nat), ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length ≥ 5 ∧ (String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.take 2 = ['d', 'b'] ∧ (String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.drop ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length - 2) = ['d', 'b'] ∧ isBinary (((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.drop 2).take ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length - 4)) v)",
        "proof": "by\n  intro v\n  rw [Refine.string_toList_mk]\n  have hne := toDigits2_ne_nil v\n  have hlen : 0 < (Nat.toDigits 2 v).length := List.length_pos_iff.mpr hne\n  have hb := toDigits2_binary v\n  refine ⟨by simp <;> omega, by simp, ?_, ?_⟩\n  · have : (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b']).length - 2 = 2 + (Nat.toDigits 2 v).length := by simp <;> omega\n    rw [this]\n    have h := List.drop_left (l₁ := ['d', 'b'] ++ Nat.toDigits 2 v) (l₂ := ['d', 'b'])\n    have hl : (['d', 'b'] ++ Nat.toDigits 2 v).length = 2 + (Nat.toDigits 2 v).length := by simp <;> omega\n    rw [hl] at h\n    exact h\n  · have h1 : (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b']).length - 4 = (Nat.toDigits 2 v).length := by simp <;> omega\n    rw [h1]\n    simpa using hb"
    }
]
_BIN084 = [
    {
        "name": "toDigits2_binary",
        "statement": "∀ (v : Nat), isBinary (Nat.toDigits 2 v) v",
        "proof": "by\n  intro v\n  induction v using Nat.strong_induction_on with\n  | _ v ih =>\n    by_cases h0 : v = 0\n    · subst h0\n      simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n    · by_cases h1 : v / 2 = 0\n      · have hv : v = 1 := by omega\n        subst hv\n        simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n      · have hlt : v / 2 < v := by omega\n        have ihv := ih (v / 2) hlt\n        have hsplit : Nat.toDigits 2 v = Nat.toDigits 2 (v / 2) ++ Nat.toDigits 2 (v % 2) := by\n          rw [Nat.toDigits_append_toDigits (by norm_num) (by omega) (by omega)]\n          congr 1; omega\n        have hbit : Nat.toDigits 2 (v % 2) = [if v % 2 = 1 then '1' else '0'] := by\n          rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, Nat.toDigits, Nat.toDigitsCore]\n        rw [hsplit, hbit]\n        obtain ⟨ha, hf, _, hh⟩ := ihv\n        refine ⟨?_, ?_, ?_, ?_⟩\n        · simp only [List.all_append, Bool.and_eq_true] \n          refine ⟨ha, ?_⟩\n          split <;> simp\n        · rw [List.foldl_append, hf]\n          simp only [List.foldl_cons, List.foldl_nil]\n          split <;> simp_all <;> omega\n        · intro hz; omega\n        · intro _\n          have hh' := hh (by omega)\n          cases hA : Nat.toDigits 2 (v / 2) with\n          | nil => rw [hA] at hh'; simp at hh'\n          | cons a t => rw [hA] at hh'; simpa using hh'"
    },
    {
        "name": "binary_string_ok",
        "statement": "∀ (s : Nat), isBinary (String.mk (Nat.toDigits 2 s)).toList s",
        "proof": "by\n  intro s\n  rw [Refine.string_toList_mk]\n  exact toDigits2_binary s"
    }
]
_BIN103 = [
    {
        "name": "toDigits2_binary",
        "statement": "∀ (v : Nat), isBinary (Nat.toDigits 2 v) v",
        "proof": "by\n  intro v\n  induction v using Nat.strong_induction_on with\n  | _ v ih =>\n    by_cases h0 : v = 0\n    · subst h0\n      simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n    · by_cases h1 : v / 2 = 0\n      · have hv : v = 1 := by omega\n        subst hv\n        simp [isBinary, Nat.toDigits, Nat.toDigitsCore]\n      · have hlt : v / 2 < v := by omega\n        have ihv := ih (v / 2) hlt\n        have hsplit : Nat.toDigits 2 v = Nat.toDigits 2 (v / 2) ++ Nat.toDigits 2 (v % 2) := by\n          rw [Nat.toDigits_append_toDigits (by norm_num) (by omega) (by omega)]\n          congr 1; omega\n        have hbit : Nat.toDigits 2 (v % 2) = [if v % 2 = 1 then '1' else '0'] := by\n          rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, Nat.toDigits, Nat.toDigitsCore]\n        rw [hsplit, hbit]\n        obtain ⟨ha, hf, _, hh⟩ := ihv\n        refine ⟨?_, ?_, ?_, ?_⟩\n        · simp only [List.all_append, Bool.and_eq_true] \n          refine ⟨ha, ?_⟩\n          split <;> simp\n        · rw [List.foldl_append, hf]\n          simp only [List.foldl_cons, List.foldl_nil]\n          split <;> simp_all <;> omega\n        · intro hz; omega\n        · intro _\n          have hh' := hh (by omega)\n          cases hA : Nat.toDigits 2 (v / 2) with\n          | nil => rw [hA] at hh'; simp at hh'\n          | cons a t => rw [hA] at hh'; simpa using hh'"
    },
    {
        "name": "toDigits2_ne_nil",
        "statement": "∀ (v : Nat), Nat.toDigits 2 v ≠ []",
        "proof": "by\n  intro v h\n  obtain ⟨_, _, h0, hh⟩ := toDigits2_binary v\n  by_cases hv : v = 0\n  · have := h0 hv; rw [h] at this; simp at this\n  · have := hh (by omega); rw [h] at this; simp at this"
    },
    {
        "name": "ob_ok",
        "statement": "∀ (w : Nat), ((String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).length ≥ 3 ∧ (String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).toList.take 2 = ['0', 'b'] ∧ isBinary ((String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).toList.drop 2) w)",
        "proof": "by\n  intro w\n  have hlen : 0 < (Nat.toDigits 2 w).length := List.length_pos_iff.mpr (toDigits2_ne_nil w)\n  rw [Refine.string_length_mk, Refine.string_toList_mk]\n  refine ⟨by simp <;> omega, by simp, ?_⟩\n  simpa using toDigits2_binary w"
    }
]

_BASE044 = [
    {
        "name": "digit_val",
        "statement": "∀ (d : Nat), d < 10 → (Nat.digitChar d).isDigit = true ∧ (Nat.digitChar d).toNat - '0'.toNat = d",
        "proof": "by\n  intro d hd\n  interval_cases d <;> decide"
    },
    {
        "name": "toDigits_single",
        "statement": "∀ (b d : Nat), 1 < b → d < b → Nat.toDigits b d = [Nat.digitChar d]",
        "proof": "by\n  intro b d hb hd\n  simp [Nat.toDigits, Nat.toDigitsCore, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd]"
    },
    {
        "name": "core_ne_nil",
        "statement": "∀ (b fuel n : Nat) (acc : List Char), Nat.toDigitsCore b (fuel + 1) n acc ≠ []",
        "proof": "by\n  intro b fuel\n  induction fuel with\n  | zero => intro n acc; simp [Nat.toDigitsCore]\n  | succ f ih =>\n    intro n acc\n    rw [Nat.toDigitsCore]\n    split\n    · simp\n    · exact ih _ _"
    },
    {
        "name": "toDigits_ne_nil",
        "statement": "∀ (b n : Nat), Nat.toDigits b n ≠ []",
        "proof": "by\n  intro b n\n  simp only [Nat.toDigits]\n  exact core_ne_nil b n n []"
    },
    {
        "name": "change_base_ok",
        "statement": "∀ (base v : Nat), 2 ≤ base → base < 10 → ((String.mk (Nat.toDigits base v)).toList.all (fun c => c.isDigit && c.toNat - '0'.toNat < base) = true ∧ (String.mk (Nat.toDigits base v)).toList.foldl (fun acc c => acc * base + (c.toNat - '0'.toNat)) 0 = v ∧ (v = 0 → String.mk (Nat.toDigits base v) = \"0\") ∧ (v > 0 → (String.mk (Nat.toDigits base v)).toList.head! ≠ '0'))",
        "proof": "by\n  intro base v hb2 hb10\n  rw [Refine.string_toList_mk]\n  induction v using Nat.strong_induction_on with\n  | _ v ih =>\n    by_cases h0 : v = 0\n    · subst h0\n      rw [toDigits_single base 0 (by omega) (by omega)]\n      obtain ⟨hd0, hval0⟩ := digit_val 0 (by omega)\n      refine ⟨?_, ?_, fun _ => ?_, fun h => absurd h (by omega)⟩\n      · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hd0, true_and, decide_eq_true_eq, hval0]\n        omega\n      · simp only [List.foldl_cons, List.foldl_nil, hval0]\n        omega\n      · show String.mk ['0'] = \"0\"\n        rfl\n    · by_cases h1 : v / base = 0\n      · have hv : v < base := Nat.lt_of_div_eq_zero (by omega) h1\n        rw [toDigits_single base v (by omega) hv]\n        obtain ⟨hd, hval⟩ := digit_val v (by omega)\n        refine ⟨?_, ?_, fun h => absurd h h0, ?_⟩\n        · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hd, true_and, decide_eq_true_eq, hval]\n          exact hv\n        · simp only [List.foldl_cons, List.foldl_nil, hval]\n          omega\n        · intro _\n          have : Nat.digitChar v ≠ '0' := by\n            intro h\n            have h2 := hval\n            rw [h] at h2\n            simp at h2\n            omega\n          simpa using this\n      · have hlt : v / base < v := Nat.div_lt_self (by omega) (by omega)\n        obtain ⟨ha, hf, _, hh⟩ := ih (v / base) hlt\n        have hsplit : Nat.toDigits base v = Nat.toDigits base (v / base) ++ Nat.toDigits base (v % base) := by\n          have := Nat.toDigits_append_toDigits (b := base) (n := v / base) (d := v % base) (by omega) (by omega) (Nat.mod_lt _ (by omega))\n          rw [this]\n          congr 1\n          have h3 := Nat.div_add_mod v base\n          first | exact h3 | exact h3.symm\n        rw [hsplit, toDigits_single base (v % base) (by omega) (Nat.mod_lt _ (by omega))]\n        have hmod : v % base < base := Nat.mod_lt v (by omega)\n        obtain ⟨hd, hval⟩ := digit_val (v % base) (by omega)\n        refine ⟨?_, ?_, fun h => absurd h h0, ?_⟩\n        · rw [List.all_append]\n          simp only [Bool.and_eq_true]\n          refine ⟨ha, ?_⟩\n          simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hd, true_and, decide_eq_true_eq, hval]\n          exact hmod\n        · rw [List.foldl_append, hf]\n          simp only [List.foldl_cons, List.foldl_nil, hval]\n          exact Nat.div_add_mod' v base\n        · intro _\n          have hh' := hh (by omega)\n          cases hA : Nat.toDigits base (v / base) with\n          | nil => exact absurd hA (toDigits_ne_nil base (v / base))\n          | cons a t => rw [hA] at hh'; simpa using hh'"
    }
]

_SHIFT050 = [
    {
        "name": "decode_shift_string",
        "statement": "∀ (s : String), s.toList.all (fun c => c.isLower) = true → ((String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))).toList.all (fun c => c.isLower) = true ∧ (String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))).toList.map shiftChar = s.toList)",
        "proof": "by\n  have shift_roundtrip : ∀ (c : Char), c.isLower = true →\n      (Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)).isLower = true ∧\n      shiftChar (Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)) = c := by\n    intro c h\n    have ha : ('a' : Char).val.toNat = 97 := by decide\n    have hz : ('z' : Char).val.toNat = 122 := by decide\n    have hl : 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by\n      unfold Char.isLower at h\n      simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h\n      obtain ⟨h1, h2⟩ := h\n      rw [UInt32.le_iff_toNat_le] at h1 h2\n      rw [ha] at h1\n      rw [hz] at h2\n      exact ⟨h1, h2⟩\n    have hcn : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm\n    generalize c.toNat = n at hl hcn ⊢\n    subst hcn\n    obtain ⟨h1, h2⟩ := hl\n    interval_cases n <;> decide\n  have decode_shift_ok : ∀ (l : List Char), l.all (fun c => c.isLower) = true →\n      ((l.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97))).all (fun c => c.isLower) = true ∧\n        (l.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97))).map shiftChar = l) := by\n    intro l\n    induction l with\n    | nil => intro _; simp\n    | cons a t ih =>\n      intro h\n      simp only [List.all_cons, Bool.and_eq_true] at h\n      obtain ⟨ha, ht⟩ := h\n      obtain ⟨h1, h2⟩ := shift_roundtrip a ha\n      obtain ⟨ih1, ih2⟩ := ih ht\n      simp only [List.map_cons, List.all_cons, Bool.and_eq_true]\n      refine ⟨⟨h1, ih1⟩, ?_⟩\n      rw [h2, ih2]\n  intro s h\n  rw [Refine.string_toList_mk]\n  exact decode_shift_ok s.toList h"
    }
]
_NS090 = [
    {
        "name": "ns_some",
        "statement": "∀ (lst : List Int) (m : Int) (p : Bool × Int), ((∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!) → ((p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ (p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)) → p.1 = true → (p.2 ∈ lst ∧ (∃ m2 ∈ lst, m2 < p.2) ∧ ∀ x ∈ lst, (∃ m2 ∈ lst, m2 < x) → p.2 ≤ x)",
        "proof": "by\n  intro lst m p ⟨⟨k0, hk0, hm⟩, hmin⟩ ⟨hiff, hd⟩ hp\n  obtain ⟨⟨k, hk, hkr, hmr⟩, hmax⟩ := hd hp\n  refine ⟨?_, ?_, ?_⟩\n  · rw [← hkr]; rw [getElem!_pos lst k hk]; exact List.getElem_mem hk\n  · refine ⟨m, ?_, hmr⟩\n    rw [← hm, getElem!_pos lst k0 hk0]; exact List.getElem_mem hk0\n  · intro x hx ⟨m2, hm2, hlt⟩\n    obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n    obtain ⟨j2, hj2, rfl⟩ := (Refine.mem_iff_idx lst m2).mp hm2\n    have := hmin j2 hj2\n    exact hmax j hj (by omega)"
    },
    {
        "name": "ns_none",
        "statement": "∀ (lst : List Int) (m : Int) (p : Bool × Int), ((∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!) → ((p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ (p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)) → ¬ p.1 = true → ∀ x ∈ lst, ∀ y ∈ lst, x = y",
        "proof": "by\n  intro lst m p ⟨⟨k0, hk0, hm⟩, hmin⟩ ⟨hiff, hd⟩ hp x hx y hy\n  obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx\n  obtain ⟨j2, hj2, rfl⟩ := (Refine.mem_iff_idx lst y).mp hy\n  have h1 : ¬ m < lst[j]! := fun h => hp (hiff.mpr ⟨j, hj, h⟩)\n  have h2 : ¬ m < lst[j2]! := fun h => hp (hiff.mpr ⟨j2, hj2, h⟩)\n  have := hmin j hj\n  have := hmin j2 hj2\n  omega"
    }
]

_HIST = [
    {
        "name": "foldl_max_nat",
        "statement": "∀ (l : List Nat) (m : Nat), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l",
        "proof": "by\n  intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n    obtain ⟨h1, h2, h3⟩ := ih (max m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n    · rcases h1 with h | h\n      · by_cases hm : m ≤ a\n        · right; rw [max_eq_right hm] at h ⊢; rw [h]; simp\n        · left\n          have hmx : max m a = m := max_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans (le_max_left m a) h2\n    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans (le_max_right m x) h2\n      · exact h3 x hx'"
    },
    {
        "name": "hist_ok",
        "statement": "∀ (ws : List String), ((ws = [] → ((ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w))) = []) ∧ (ws ≠ [] → (∀ p ∈ (ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w)), p.1 ∈ ws ∧ p.2 = ws.count p.1 ∧ ∀ w ∈ ws, ws.count w ≤ p.2) ∧ (∀ w ∈ ws, (∀ v ∈ ws, ws.count v ≤ ws.count w) → ∃ p ∈ (ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w)), p.1 = w) ∧ (((ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w))).map Prod.fst).Nodup))",
        "proof": "by\n  intro ws\n  refine ⟨fun h => by subst h; simp, ?_⟩\n  intro hne\n  obtain ⟨h1, h2, h3⟩ := foldl_max_nat (ws.map (fun w => ws.count w)) 0\n  have hnd : (ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).Nodup :=\n    (List.nodup_dedup ws).filter _\n  refine ⟨?_, ?_, ?_⟩\n  · intro p hp\n    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp\n    rw [List.mem_filter] at hw\n    obtain ⟨hwd, hwb⟩ := hw\n    have hwm : w ∈ ws := List.mem_dedup.mp hwd\n    have hbeq : ws.count w = (ws.map (fun w => ws.count w)).foldl max 0 := by simpa using hwb\n    refine ⟨hwm, rfl, ?_⟩\n    intro v hv\n    rw [hbeq]\n    exact h3 _ (List.mem_map.mpr ⟨v, hv, rfl⟩)\n  · intro w hw hmax\n    have hbest : (ws.map (fun w => ws.count w)).foldl max 0 = ws.count w := by\n      apply le_antisymm\n      · rcases h1 with h | h\n        · rw [h]; exact Nat.zero_le _\n        · obtain ⟨v, hv, hveq⟩ := List.mem_map.mp h\n          rw [← hveq]; exact hmax v hv\n      · exact h3 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)\n    refine ⟨(w, ws.count w), List.mem_map.mpr ⟨w, ?_, rfl⟩, rfl⟩\n    rw [List.mem_filter]\n    exact ⟨List.mem_dedup.mpr hw, by simpa [hbest]⟩\n  · rw [List.map_map]\n    have hc : (Prod.fst ∘ fun w => (w, ws.count w)) = fun w => w := rfl\n    rw [hc, List.map_id']\n    exact hnd"
    }
]

_ROUND = [
    {
        "name": "round_away_ok",
        "statement": "∀ (q : ℚ), |q - (((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)| < 1 / 2 ∨ (|q - (((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)| = 1 / 2 ∧ |q| < |(((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)|)",
        "proof": "by\n  intro q\n  by_cases hq : q ≥ 0\n  · rw [if_pos hq]\n    have h1 : ((⌊q + 1 / 2⌋ : Int) : ℚ) ≤ q + 1 / 2 := Int.floor_le _\n    have h2 : q + 1 / 2 < ((⌊q + 1 / 2⌋ : Int) : ℚ) + 1 := Int.lt_floor_add_one _\n    have h3 : (0 : ℚ) ≤ ((⌊q + 1 / 2⌋ : Int) : ℚ) := by\n      have : (0 : Int) ≤ ⌊q + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)\n      exact_mod_cast this\n    set r : ℚ := ((⌊q + 1 / 2⌋ : Int) : ℚ) with hr\n    by_cases hlt : q - r > -(1 / 2)\n    · left\n      rw [abs_lt]\n      constructor <;> linarith\n    · right\n      have heq : q - r = -(1 / 2) := by linarith\n      refine ⟨?_, ?_⟩\n      · rw [heq]; norm_num\n      · rw [abs_of_nonneg hq, abs_of_nonneg h3]; linarith\n  · rw [if_neg hq]\n    push_neg at hq\n    have h1 : ((⌊-q + 1 / 2⌋ : Int) : ℚ) ≤ -q + 1 / 2 := Int.floor_le _\n    have h2 : -q + 1 / 2 < ((⌊-q + 1 / 2⌋ : Int) : ℚ) + 1 := Int.lt_floor_add_one _\n    have h3 : (0 : ℚ) ≤ ((⌊-q + 1 / 2⌋ : Int) : ℚ) := by\n      have : (0 : Int) ≤ ⌊-q + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)\n      exact_mod_cast this\n    set r : ℚ := ((⌊-q + 1 / 2⌋ : Int) : ℚ) with hr\n    have hcast : (((-⌊-q + 1 / 2⌋ : Int)) : ℚ) = -r := by push_cast; rfl\n    rw [hcast]\n    by_cases hlt : (-q) - r > -(1 / 2)\n    · left\n      rw [abs_lt]\n      constructor <;> linarith\n    · right\n      have heq : (-q) - r = -(1 / 2) := by linarith\n      refine ⟨?_, ?_⟩\n      · rw [show q - -r = -((-q) - r) by ring, abs_neg, heq]; norm_num\n      · rw [abs_of_neg hq, abs_neg, abs_of_nonneg h3]; linarith"
    }
]

_MKPAL = [
    {
        "name": "mp_exit",
        "statement": "∀ (s : String) (i : Nat), (i ≤ s.length ∧ ∀ j, j < i → ¬ isPal (s.toList.drop j)) → ¬ (i < s.length ∧ ¬ isPal (s.toList.drop i)) → ∃ i2, i2 ≤ s.length ∧ isPal (s.toList.drop i2) ∧ (∀ j, j < i2 → ¬ isPal (s.toList.drop j)) ∧ (String.mk (s.toList ++ (s.toList.take i).reverse)).toList = s.toList ++ (s.toList.take i2).reverse",
        "proof": "by\n  intro s i ⟨hi, hj⟩ hg\n  refine ⟨i, hi, ?_, hj, by rw [Refine.string_toList_mk]⟩\n  by_cases h : i < s.length\n  · by_contra hn\n    exact hg ⟨h, hn⟩\n  · have : i = s.length := by omega\n    subst this\n    have h0 : s.toList.drop s.length = [] := by\n      apply List.drop_of_length_le\n      exact le_of_eq rfl\n    rw [h0]\n    rfl"
    }
]

_FACT = [
    {
        "name": "fact_div",
        "statement": "∀ (N n d : Nat) (acc : List Nat), (1 ≤ n ∧ 2 ≤ d ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n) ∧ (n = 1 ∨ d ≤ n)) → 1 < n → n % d = 0 → ((1 ≤ (n / d) ∧ 2 ≤ d ∧ ((acc ++ [d])).prod * (n / d) = N ∧ (∀ p ∈ (acc ++ [d]), Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < ((acc ++ [d])).length - 1 → ((acc ++ [d]))[i]! ≤ ((acc ++ [d]))[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ (n / d)) ∧ ((n / d) = 1 ∨ d ≤ (n / d))) ∧ ((n / d + n / d - d) < (n + n - d)))",
        "proof": "by\n  intro N n d acc ⟨h1, h2, hprod, hprime, hsort, hno, hle⟩ hn hd\n  have hdd : d ∣ n := Nat.dvd_of_mod_eq_zero hd\n  have hdpos : 0 < d := by omega\n  have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdd\n  have hdprime : Nat.Prime d := by\n    rw [Nat.prime_def_lt]\n    refine ⟨h2, ?_⟩\n    intro m hm hmd\n    by_contra hm1\n    have hm2 : 2 ≤ m := by\n      have : m ≠ 0 := by\n        intro h0; subst h0; simp at hmd; omega\n      omega\n    exact hno m hm2 hm (Nat.dvd_trans hmd hdd)\n  have hq : n / d < n := Nat.div_lt_self (by omega) (by omega)\n  have hqpos : 1 ≤ n / d := by\n    have := Nat.div_pos hdn hdpos\n    omega\n  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdd\n  refine ⟨⟨hqpos, h2, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩\n  · rw [List.prod_append]\n    simp only [List.prod_cons, List.prod_nil, Nat.mul_one]\n    calc acc.prod * d * (n / d) = acc.prod * (d * (n / d)) := by rw [Nat.mul_assoc]\n      _ = N := by rw [hmul]; exact hprod\n  · intro p hp\n    rcases List.mem_append.mp hp with hp | hp\n    · exact hprime p hp\n    · have : p = d := by simpa using hp\n      subst this\n      exact ⟨hdprime, by omega⟩\n  · intro i hi\n    have hlen : (acc ++ [d]).length = acc.length + 1 := by simp\n    rw [hlen] at hi\n    by_cases hlast : i + 1 < acc.length\n    · rw [getElem!_pos (acc ++ [d]) i (by simp; omega), getElem!_pos (acc ++ [d]) (i + 1) (by simp; omega)]\n      simp only [List.getElem_append_left (by omega : i < acc.length), List.getElem_append_left hlast]\n      have := hsort i (by omega)\n      rwa [getElem!_pos acc i (by omega), getElem!_pos acc (i + 1) hlast] at this\n    · have hi' : i + 1 = acc.length := by omega\n      rw [getElem!_pos (acc ++ [d]) i (by simp; omega), getElem!_pos (acc ++ [d]) (i + 1) (by simp; omega)]\n      have hmem : (acc ++ [d])[i]'(by simp; omega) ∈ acc := by\n        rw [List.getElem_append_left (by omega)]; exact List.getElem_mem _\n      have hlt := (hprime _ hmem).2\n      have hlast' : (acc ++ [d])[i + 1]'(by simp; omega) = d := by\n        rw [List.getElem_append_right (by omega)]; simp [hi']\n      rw [hlast']\n      omega\n  · intro k hk2 hkd hkq\n    exact hno k hk2 hkd (Nat.dvd_trans hkq (Nat.div_dvd_of_dvd hdd))\n  · by_cases hq1 : n / d = 1\n    · left; exact hq1\n    · right\n      obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1\n      have hpn : p ∣ n := Nat.dvd_trans hpq (Nat.div_dvd_of_dvd hdd)\n      have hpd : d ≤ p := by\n        by_contra hlt\n        exact hno p hp.two_le (by omega) hpn\n      exact le_trans hpd (Nat.le_of_dvd (by omega) hpq)"
    },
    {
        "name": "fact_nodiv",
        "statement": "∀ (N n d : Nat) (acc : List Nat), (1 ≤ n ∧ 2 ≤ d ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n) ∧ (n = 1 ∨ d ≤ n)) → 1 < n → ¬ n % d = 0 → ((1 ≤ n ∧ 2 ≤ (d + 1) ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < (d + 1) + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < (d + 1) → ¬ k ∣ n) ∧ (n = 1 ∨ (d + 1) ≤ n)) ∧ ((n + n - (d + 1)) < (n + n - d)))",
        "proof": "by\n  intro N n d acc ⟨h1, h2, hprod, hprime, hsort, hno, hle⟩ hn hd\n  have hdn : d ≤ n := by omega\n  have hdne : d ≠ n := by\n    intro h; subst h; simp at hd\n  refine ⟨⟨h1, by omega, hprod, ?_, hsort, ?_, ?_⟩, by omega⟩\n  · intro p hp\n    obtain ⟨a, b⟩ := hprime p hp\n    exact ⟨a, by omega⟩\n  · intro k hk2 hkd hkn\n    by_cases hkdd : k = d\n    · subst hkdd; exact hd (Nat.mod_eq_zero_of_dvd hkn)\n    · exact hno k hk2 (by omega) hkn\n  · right; omega"
    }
]

_CLOSEST = [
    {
        "name": "maxmin_abs",
        "statement": "∀ (x y : ℚ), max x y - min x y = |x - y|",
        "proof": "by\n  intro x y\n  rcases le_total x y with h | h\n  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]; ring\n  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]"
    },
    {
        "name": "closest_yes",
        "statement": "∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), i < j → j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → |numbers[i]! - numbers[j]!| < hi - lo → (((min numbers[i]! numbers[j]!) ≤ (max numbers[i]! numbers[j]!) ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ (((min numbers[i]! numbers[j]!) = numbers[a]! ∧ (max numbers[i]! numbers[j]!) = numbers[b]!) ∨ ((min numbers[i]! numbers[j]!) = numbers[b]! ∧ (max numbers[i]! numbers[j]!) = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → (max numbers[i]! numbers[j]!) - (min numbers[i]! numbers[j]!) ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < (i + 1) → (max numbers[i]! numbers[j]!) - (min numbers[i]! numbers[j]!) ≤ |numbers[a]! - numbers[j]!|)) ∧ i + 1 ≤ j)",
        "proof": "by\n  intro numbers i j lo hi hij hj ⟨⟨hle, hex, hbest, hall⟩, hi'⟩ hc\n  have hm := maxmin_abs numbers[i]! numbers[j]!\n  have hmle : min numbers[i]! numbers[j]! ≤ max numbers[i]! numbers[j]! := le_trans (min_le_left _ _) (le_max_left _ _)\n  refine ⟨⟨hmle, ?_, ?_, ?_⟩, by omega⟩\n  · refine ⟨j, by omega, i, hij, ?_⟩\n    rcases le_total numbers[i]! numbers[j]! with h | h\n    · left; exact ⟨min_eq_left h, max_eq_right h⟩\n    · right; exact ⟨min_eq_right h, max_eq_left h⟩\n  · intro b hb a ha\n    have := hbest b hb a ha\n    linarith\n  · intro a ha\n    by_cases hai : a < i\n    · have := hall a hai\n      linarith\n    · have : a = i := by omega\n      subst this\n      linarith"
    },
    {
        "name": "closest_no",
        "statement": "∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), i < j → j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → ¬ |numbers[i]! - numbers[j]!| < hi - lo → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < (i + 1) → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i + 1 ≤ j)",
        "proof": "by\n  intro numbers i j lo hi hij hj ⟨⟨hle, hex, hbest, hall⟩, hi'⟩ hc\n  push_neg at hc\n  refine ⟨⟨hle, hex, hbest, ?_⟩, by omega⟩\n  intro a ha\n  by_cases hai : a < i\n  · exact hall a hai\n  · have : a = i := by omega\n    subst this\n    exact hc"
    },
    {
        "name": "closest_inner_init",
        "statement": "∀ (numbers : List ℚ) (j : Nat) (lo hi : ℚ), ((lo ≤ hi ∧ (∃ b, b < j ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j ∧ j ≤ numbers.length) → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < 0 → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ 0 ≤ j)",
        "proof": "by\n  intro numbers j lo hi ⟨⟨hle, hex, hbest⟩, _, _⟩\n  refine ⟨⟨hle, ?_, hbest, ?_⟩, by omega⟩\n  · obtain ⟨b, hb, a, ha, h⟩ := hex\n    exact ⟨b, by omega, a, ha, h⟩\n  · intro a ha; omega"
    },
    {
        "name": "closest_outer",
        "statement": "∀ (numbers : List ℚ) (j : Nat) (lo hi : ℚ), j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ j ≤ j) → 2 ≤ j → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < (j + 1) → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j + 1 ∧ j + 1 ≤ numbers.length)",
        "proof": "by\n  intro numbers j lo hi hj ⟨⟨hle, hex, hbest, hall⟩, _⟩ h2\n  refine ⟨⟨hle, hex, ?_⟩, by omega, by omega⟩\n  intro b hb a ha\n  by_cases hbj : b < j\n  · exact hbest b hbj a ha\n  · have : b = j := by omega\n    subst this\n    exact hall a ha"
    },
    {
        "name": "closest_init",
        "statement": "∀ (numbers : List ℚ), numbers.length ≥ 2 → (((min numbers[0]! numbers[1]!) ≤ (max numbers[0]! numbers[1]!) ∧ (∃ b, b < 2 ∧ ∃ a, a < b ∧ (((min numbers[0]! numbers[1]!) = numbers[a]! ∧ (max numbers[0]! numbers[1]!) = numbers[b]!) ∨ ((min numbers[0]! numbers[1]!) = numbers[b]! ∧ (max numbers[0]! numbers[1]!) = numbers[a]!))) ∧ (∀ b, b < 2 → ∀ a, a < b → (max numbers[0]! numbers[1]!) - (min numbers[0]! numbers[1]!) ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ 2 ∧ 2 ≤ numbers.length)",
        "proof": "by\n  intro numbers hl\n  have hm := maxmin_abs numbers[0]! numbers[1]!\n  have hmle : min numbers[0]! numbers[1]! ≤ max numbers[0]! numbers[1]! := le_trans (min_le_left _ _) (le_max_left _ _)\n  refine ⟨⟨hmle, ?_, ?_⟩, by omega, by omega⟩\n  · refine ⟨1, by omega, 0, by omega, ?_⟩\n    rcases le_total numbers[0]! numbers[1]! with h | h\n    · left; exact ⟨min_eq_left h, max_eq_right h⟩\n    · right; exact ⟨min_eq_right h, max_eq_left h⟩\n  · intro b hb a ha\n    have : b = 1 := by omega\n    subst this\n    have : a = 0 := by omega\n    subst this\n    linarith"
    },
    {
        "name": "closest_inner_exit",
        "statement": "∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → ¬ i < j → (lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → hi - lo ≤ |numbers[a]! - numbers[j]!|))",
        "proof": "by\n  intro numbers i j lo hi ⟨⟨hle, hex, hbest, hall⟩, hij⟩ hn\n  have : i = j := by omega\n  subst this\n  exact ⟨hle, hex, hbest, hall⟩"
    }
]
_GETROW = [
    {
        "name": "get_row_ok",
        "statement": "∀ (lst : List (List Int)) (x : Int), (∀ p ∈ (List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))), p.1 < lst.length ∧ p.2 < lst[p.1]!.length ∧ (lst[p.1]!)[p.2]! = x) ∧ (∀ i, i < lst.length → ∀ j, j < lst[i]!.length → (lst[i]!)[j]! = x → (i, j) ∈ (List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j)))) ∧ ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j)))).Nodup ∧ (∀ k, k < ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j)))).length - 1 → ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k]!.1 < ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k + 1]!.1 ∨ (((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k]!.1 = ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k + 1]!.1 ∧ ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k + 1]!.2 < ((List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))))[k]!.2))",
        "proof": "by\n  intro lst x\n  set T := (List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j))) with hT\n  have hmem : ∀ p, p ∈ T ↔ p.1 < lst.length ∧ p.2 < lst[p.1]!.length ∧ (lst[p.1]!)[p.2]! = x := by\n    intro p\n    rw [hT, List.mem_flatMap]\n    constructor\n    · rintro ⟨i, hi, hp⟩\n      rw [List.mem_map] at hp\n      obtain ⟨j, hj, rfl⟩ := hp\n      rw [List.mem_reverse, List.mem_filter, List.mem_range] at hj\n      rw [List.mem_range] at hi\n      exact ⟨hi, hj.1, by simpa using hj.2⟩\n    · rintro ⟨h1, h2, h3⟩\n      refine ⟨p.1, List.mem_range.mpr h1, ?_⟩\n      rw [List.mem_map]\n      refine ⟨p.2, ?_, rfl⟩\n      rw [List.mem_reverse, List.mem_filter, List.mem_range]\n      exact ⟨h2, by simpa using h3⟩\n  have hR : T.Pairwise (fun p q : Nat × Nat => p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)) := by\n    rw [hT, List.pairwise_flatMap]\n    constructor\n    · intro i _\n      rw [List.pairwise_map, List.pairwise_reverse]\n      have hs : List.Pairwise (· < ·) ((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)) :=\n        (List.pairwise_lt_range).filter _\n      exact hs.imp (by intro a b h; right; exact ⟨rfl, h⟩)\n    · exact (List.pairwise_lt_range).imp (by\n        intro a b hab p hp q hq\n        rw [List.mem_map] at hp hq\n        obtain ⟨j1, _, rfl⟩ := hp\n        obtain ⟨j2, _, rfl⟩ := hq\n        left; exact hab)\n  refine ⟨fun p hp => (hmem p).mp hp, fun i hi j hj hx => (hmem (i, j)).mpr ⟨hi, hj, hx⟩, ?_, ?_⟩\n  · exact hR.imp (by\n      intro p q h hpq\n      subst hpq\n      omega)\n  · intro k hk\n    have hk' : k + 1 < T.length := by omega\n    have hpw := hR\n    rw [List.pairwise_iff_getElem] at hpw\n    have := hpw k (k + 1) (by omega) hk' (by omega)\n    rw [getElem!_pos T k (by omega), getElem!_pos T (k + 1) hk']\n    exact this"
    }
]

_SORT3 = [
    {
        "name": "filter_mod_3",
        "statement": "∀ (n : Nat), (List.range n).filter (fun i => decide (i % 3 = 0)) = (List.range (((n + 2) / 3))).map (fun t => t * 3)",
        "proof": "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ n ih =>\n    rw [List.range_succ, List.filter_append, ih]\n    by_cases h : n % 3 = 0\n    · have hk : (n + 1 + 2) / 3 = (n + 2) / 3 + 1 := by omega\n      rw [hk, List.range_succ, List.map_append]\n      have : (n + 2) / 3 * 3 = n := by omega\n      simp [h, this]\n    · have hk : (n + 1 + 2) / 3 = (n + 2) / 3 := by omega\n      rw [hk]\n      simp [h]"
    },
    {
        "name": "sort_third_ok",
        "statement": "∀ (l : List Int), ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)).length = l.length ∧ (∀ i, i < l.length → i % 3 ≠ 0 → ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))[i]! = l[i]!) ∧ (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))).isPerm (atMod 3 l) = true ∧ ∀ i, i < (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!))).length - 1 → (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)))[i]! ≤ (atMod 3 ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)))[i + 1]!",
        "proof": "by\n  intro l\n  set S := ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b))) with hS\n  have hSlen : S.length = (atMod 3 l).length := List.length_mergeSort ..\n  have hatl : atMod 3 l = (List.range ((l.length + 2) / 3)).map (fun t => l[t * 3]!) := by\n    unfold atMod\n    rw [filter_mod_3, List.map_map]\n    rfl\n  have hlenA : (atMod 3 l).length = (l.length + 2) / 3 := by rw [hatl]; simp\n  set T := ((List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)) with hT\n  have hTlen : T.length = l.length := by simp [hT]\n  have hatT : atMod 3 T = S := by\n    unfold atMod\n    rw [hTlen, filter_mod_3, List.map_map]\n    apply List.ext_getElem\n    · rw [List.length_map, List.length_range]; omega\n    · intro t h1 h2\n      have ht : t < (l.length + 2) / 3 := by rw [List.length_map, List.length_range] at h1; exact h1\n      have hlt : t * 3 < T.length := by rw [hTlen]; omega\n      have hval : T[t * 3] = S[t]! := by\n        simp only [hT, List.getElem_map, List.getElem_range]\n        simp\n        all_goals rfl\n      rw [List.getElem_map, List.getElem_range]\n      rw [getElem!_pos S t h2] at hval\n      rw [← hval]\n      exact getElem!_pos T (t * 3) hlt\n  refine ⟨hTlen, ?_, ?_, ?_⟩\n  · intro i hi hm\n    rw [getElem!_pos T i (by rw [hTlen]; exact hi)]\n    simp [hT, hi, hm]\n    all_goals (try rw [getElem!_pos l i hi])\n  · rw [hatT]\n    exact List.isPerm_iff.mpr (List.mergeSort_perm _ _)\n  · rw [hatT]\n    intro i hi\n    have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) S :=\n      List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) _\n    rw [List.pairwise_iff_getElem] at hs\n    have hi' : i + 1 < S.length := by omega\n    have := hs i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    simpa using this"
    }
]
_SORT2 = [
    {
        "name": "filter_mod_2",
        "statement": "∀ (n : Nat), (List.range n).filter (fun i => decide (i % 2 = 0)) = (List.range (((n + 1) / 2))).map (fun t => t * 2)",
        "proof": "by\n  intro n\n  induction n with\n  | zero => simp\n  | succ n ih =>\n    rw [List.range_succ, List.filter_append, ih]\n    by_cases h : n % 2 = 0\n    · have hk : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega\n      rw [hk, List.range_succ, List.map_append]\n      have : (n + 1) / 2 * 2 = n := by omega\n      simp [h, this]\n    · have hk : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega\n      rw [hk]\n      simp [h]"
    },
    {
        "name": "sort_even_ok",
        "statement": "∀ (l : List Int), ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)).length = l.length ∧ (∀ i, i < l.length → i % 2 ≠ 0 → ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))[i]! = l[i]!) ∧ (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))).isPerm (atMod 2 l) = true ∧ ∀ i, i < (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!))).length - 1 → (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)))[i]! ≤ (atMod 2 ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)))[i + 1]!",
        "proof": "by\n  intro l\n  set S := ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b))) with hS\n  have hSlen : S.length = (atMod 2 l).length := List.length_mergeSort ..\n  have hatl : atMod 2 l = (List.range ((l.length + 1) / 2)).map (fun t => l[t * 2]!) := by\n    unfold atMod\n    rw [filter_mod_2, List.map_map]\n    rfl\n  have hlenA : (atMod 2 l).length = (l.length + 1) / 2 := by rw [hatl]; simp\n  set T := ((List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)) with hT\n  have hTlen : T.length = l.length := by simp [hT]\n  have hatT : atMod 2 T = S := by\n    unfold atMod\n    rw [hTlen, filter_mod_2, List.map_map]\n    apply List.ext_getElem\n    · rw [List.length_map, List.length_range]; omega\n    · intro t h1 h2\n      have ht : t < (l.length + 1) / 2 := by rw [List.length_map, List.length_range] at h1; exact h1\n      have hlt : t * 2 < T.length := by rw [hTlen]; omega\n      have hval : T[t * 2] = S[t]! := by\n        simp only [hT, List.getElem_map, List.getElem_range]\n        simp\n        all_goals rfl\n      rw [List.getElem_map, List.getElem_range]\n      rw [getElem!_pos S t h2] at hval\n      rw [← hval]\n      exact getElem!_pos T (t * 2) hlt\n  refine ⟨hTlen, ?_, ?_, ?_⟩\n  · intro i hi hm\n    rw [getElem!_pos T i (by rw [hTlen]; exact hi)]\n    simp [hT, hi, hm]\n    all_goals (try rw [getElem!_pos l i hi])\n  · rw [hatT]\n    exact List.isPerm_iff.mpr (List.mergeSort_perm _ _)\n  · rw [hatT]\n    intro i hi\n    have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) S :=\n      List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) _\n    rw [List.pairwise_iff_getElem] at hs\n    have hi' : i + 1 < S.length := by omega\n    have := hs i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    simpa using this"
    }
]

_TRI = [
    {
        "name": "round_sqrt_ok",
        "statement": "∀ (A : ℚ), 0 ≤ A → ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 ≥ 0 ∧ (((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100) * 100).den = 1 ∧ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 < 1 / 200 ∨ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 - 1 / 200) ^ 2 ≤ A) ∧ A ≤ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 + 1 / 200) ^ 2)",
        "proof": "by\n  intro A hA\n  set N := ⌊40000 * A⌋₊ with hN\n  set m := Nat.sqrt N with hm\n  set k := (m + 1) / 2 with hk\n  have h1 : (m : ℚ) ^ 2 ≤ 40000 * A := by\n    have hsq : m * m ≤ N := Nat.sqrt_le N\n    have hfl : (N : ℚ) ≤ 40000 * A := Nat.floor_le (by positivity)\n    have : ((m * m : Nat) : ℚ) ≤ (N : ℚ) := by exact_mod_cast hsq\n    push_cast at this\n    nlinarith\n  have h2 : 40000 * A < ((m : ℚ) + 1) ^ 2 := by\n    have hsq : N < (m + 1) * (m + 1) := Nat.lt_succ_sqrt N\n    have hfl : 40000 * A < (N : ℚ) + 1 := Nat.lt_floor_add_one _\n    have : ((N + 1 : Nat) : ℚ) ≤ (((m + 1) * (m + 1) : Nat) : ℚ) := by exact_mod_cast hsq\n    push_cast at this\n    nlinarith\n  have hk1 : 2 * k ≤ m + 1 := by omega\n  have hk2 : m ≤ 2 * k := by omega\n  have hk1' : (2 * (k : ℚ)) ≤ (m : ℚ) + 1 := by exact_mod_cast hk1\n  have hk2' : (m : ℚ) ≤ 2 * (k : ℚ) := by exact_mod_cast hk2\n  refine ⟨by positivity, ?_, ?_, ?_⟩\n  · have : ((k : ℚ) / 100) * 100 = (k : ℚ) := by ring\n    rw [this]\n    exact Rat.den_natCast k\n  · by_cases hk0 : k = 0\n    · left; rw [hk0]; norm_num\n    · right\n      have hkpos : (1 : ℚ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0\n      have hm1 : 2 * (k : ℚ) - 1 ≤ (m : ℚ) := by linarith\n      have hm0 : 0 ≤ 2 * (k : ℚ) - 1 := by linarith\n      have : (2 * (k : ℚ) - 1) ^ 2 ≤ (m : ℚ) ^ 2 := by nlinarith\n      have : ((k : ℚ) / 100 - 1 / 200) ^ 2 = (2 * (k : ℚ) - 1) ^ 2 / 40000 := by ring\n      rw [this]\n      linarith\n  · have : (m : ℚ) + 1 ≤ 2 * (k : ℚ) + 1 := by linarith\n    have hm0 : 0 ≤ (m : ℚ) + 1 := by positivity\n    have : ((m : ℚ) + 1) ^ 2 ≤ (2 * (k : ℚ) + 1) ^ 2 := by nlinarith\n    have e : ((k : ℚ) / 100 + 1 / 200) ^ 2 = (2 * (k : ℚ) + 1) ^ 2 / 40000 := by ring\n    rw [e]\n    linarith"
    },
    {
        "name": "area2_nonneg",
        "statement": "∀ (a b c : ℚ), a > 0 → b > 0 → c > 0 → ¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → 0 ≤ area2 a b c",
        "proof": "by\n  intro a b c ha hb hc h\n  push_neg at h\n  obtain ⟨h1, h2, h3⟩ := h\n  unfold area2\n  have hp : 0 < (a + b + c) / 2 := by linarith\n  have e1 : 0 < (a + b + c) / 2 - a := by linarith\n  have e2 : 0 < (a + b + c) / 2 - b := by linarith\n  have e3 : 0 < (a + b + c) / 2 - c := by linarith\n  have := mul_pos (mul_pos (mul_pos hp e1) e2) e3\n  exact le_of_lt this"
    },
    {
        "name": "tri_no",
        "statement": "∀ (a b c : ℚ), a > 0 → b > 0 → c > 0 → ¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → ((a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a → ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100) = -1) ∧ (¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 ≥ 0 ∧ (((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100) * 100).den = 1 ∧ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 < 1 / 200 ∨ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 - 1 / 200) ^ 2 ≤ area2 a b c) ∧ area2 a b c ≤ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 + 1 / 200) ^ 2)))",
        "proof": "by\n  intro a b c ha hb hc h\n  refine ⟨fun h' => absurd h' h, fun _ => round_sqrt_ok _ (area2_nonneg a b c ha hb hc h)⟩"
    }
]

ORACLES_MORE = {
    "he_005_intersperse": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
             "i ≤ numbers.length ∧ acc.length = (if i = 0 then 0 else 2 * i - 1) ∧ (∀ k, k < i → acc[2 * k]! = numbers[k]!) ∧ "
             "∀ k, k + 1 < i → acc[2 * k + 1]! = delimeter",
             "i < numbers.length", "numbers.length - i", "acc",
             term("(i + 1, if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])")), _INTER),
    "he_009_rolling_max": with_lemmas(
        term("(List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)"), _ROLL),
    "he_038_decode_cyclic": with_lemmas(
        term("String.mk (encodeGroups (encodeGroups s.toList))"),
        [{"name": "encode_three", "statement": "∀ (l : List Char), encodeGroups (encodeGroups (encodeGroups l)) = l",
          "proof": "by intro l\n  induction l using encodeGroups.induct with\n  | case1 a b c rest ih => simp [encodeGroups, ih]\n"
                   "  | case2 l h => cases l with\n    | nil => simp [encodeGroups]\n    | cons a t => cases t with\n      | nil => simp [encodeGroups]\n"
                   "      | cons b t2 => cases t2 with\n        | nil => simp [encodeGroups]\n        | cons c rest => exact absurd rfl (h a b c rest)"}]),

    "he_132_is_nested": term(
        "decide (∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧ isBalancedSq ((string.toList.drop i).take len) ∧ "
        "∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k))"),
    "he_116_sort_array": with_lemmas(
        term("arr.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))"), _SORT116),
    "he_088_sort_array": with_lemmas(
        cases("array ≠ [] ∧ (array.head! + array.getLast!) % 2 = 0",
              term("array.mergeSort (fun a b => decide (a ≥ b))"), term("array.mergeSort (fun a b => decide (a ≤ b))")),
        _SORT_NAT_ASC + _SORT_NAT_DESC),
    "he_092_any_int": with_lemmas(term(
        "(fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => "
        "decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z)"), _ANYINT),
    "he_130_tri": loop(
        [["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
        "i ≤ n + 1 ∧ acc.length = i ∧ (0 < i → acc[0]! = 1) ∧ (1 < i → acc[1]! = 3) ∧ "
        "∀ k, k < i → 2 ≤ k → acc[k]! = (if k % 2 = 0 then 1 + k / 2 else acc[k - 1]! + acc[k - 2]! + (1 + (k + 1) / 2))",
        "i < n + 1", "n + 1 - i", "acc",
        term("(i + 1, acc ++ [if i = 0 then 1 else if i = 1 then 3 else if i % 2 = 0 then 1 + i / 2 else "
             "acc[i - 1]! + acc[i - 2]! + (1 + (i + 1) / 2)])")),
    "he_114_min_sub_array_sum": with_lemmas(
        term("List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))"),
        _MINSUB),

    "he_118_get_closest_vowel": with_lemmas(
        bind("last", "Option Nat",
             "(last = none ∧ ∀ i, i < word.toList.length → ¬ goodAt word.toList i) ∨ (∃ b, last = some b ∧ b < word.toList.length ∧ goodAt word.toList b ∧ ∀ j, j < word.toList.length → b < j → ¬ goodAt word.toList j)",
             loop([["i", "Nat"], ["b", "Option Nat"]], ["0", "none"],
                  "i ≤ word.toList.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt word.toList j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt word.toList c ∧ ∀ j, j < i → c < j → ¬ goodAt word.toList j))",
                  "i < word.toList.length", "word.toList.length - i", "b",
                  term("(i + 1, if goodAt word.toList i then some i else b)")),
             cases("last = none", term('""'), term("String.singleton word.toList[last.getD 0]!"))),
        _VOWEL_STEP),

    "he_068_pluck": with_lemmas(
        loop([["i", "Nat"], ["f", "Bool"], ["v", "Nat"], ["ix", "Nat"]], ["0", "false", "0", "0"],
             "i ≤ arr.length ∧ (f = true ↔ ∃ k, k < i ∧ arr[k]! % 2 = 0) ∧ "
             "(f = true → ix < i ∧ arr[ix]! = v ∧ v % 2 = 0 ∧ (∀ k, k < i → arr[k]! % 2 = 0 → v ≤ arr[k]!) ∧ ∀ j, j < ix → arr[j]! ≠ v)",
             "i < arr.length", "arr.length - i", "if f = true then [v, ix] else []",
             term("(i + 1, f || decide (arr[i]! % 2 = 0), if arr[i]! % 2 = 0 ∧ (f = false ∨ arr[i]! < v) then arr[i]! else v, "
                  "if arr[i]! % 2 = 0 ∧ (f = false ∨ arr[i]! < v) then i else ix)")), _PLUCK),
    "he_094_skjkasdkd": with_lemmas(
        loop([["i", "Nat"], ["best", "Nat"]], ["0", "0"],
             "i ≤ lst.length ∧ (best = 0 ∨ ∃ k, k < i ∧ lst[k]! = best ∧ Nat.Prime best) ∧ ∀ k, k < i → Nat.Prime lst[k]! → lst[k]! ≤ best",
             "i < lst.length", "lst.length - i", "((toString best).toList.map (fun c => c.toNat - '0'.toNat)).sum",
             term("(i + 1, if Nat.Prime lst[i]! ∧ best < lst[i]! then lst[i]! else best)")), _SKJ),
    "he_059_largest_prime_factor": with_lemmas(
        loop([["q", "Nat"]], ["n"], "1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False",
             "1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)", "q", "q", term("q - 1")), _LPF),
    "he_069_search": with_lemmas(
        loop([["i", "Nat"], ["best", "Int"]], ["0", "-1"],
             "i ≤ lst.length ∧ ((best = -1 ∧ ∀ k, k < i → lst.count lst[k]! < lst[k]!) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ "
             "lst.count best.toNat ≥ best.toNat ∧ ∀ k, k < i → lst.count lst[k]! ≥ lst[k]! → lst[k]! ≤ best.toNat))",
             "i < lst.length", "lst.length - i", "best",
             term("(i + 1, if lst.count lst[i]! ≥ lst[i]! ∧ (best = -1 ∨ best < (lst[i]! : Int)) then (lst[i]! : Int) else best)")),
        _SEARCH),

    "he_079_decimal_to_binary": with_lemmas(term("String.mk (['d', 'b'] ++ Nat.toDigits 2 decimal ++ ['d', 'b'])"), _BIN079),
    "he_084_solve": with_lemmas(
        term("String.mk (Nat.toDigits 2 (((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum))"), _BIN084),
    "he_103_rounded_avg": with_lemmas(
        cases("n > m", term("none"), term("some (String.mk (['0', 'b'] ++ Nat.toDigits 2 (roundedHalfEven (n + m))))")), _BIN103),
    "he_044_change_base": with_lemmas(term("String.mk (Nat.toDigits base x)"), _BASE044),

    "he_050_decode_shift": with_lemmas(
        term("String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))"), _SHIFT050),
    "he_090_next_smallest": cases(
        "lst = []", term("none"),
        with_lemmas(
            bind("m", "Int", "(∃ k, k < lst.length ∧ lst[k]! = m) ∧ ∀ k, k < lst.length → m ≤ lst[k]!",
                 loop([["i", "Nat"], ["m", "Int"]], ["1", "lst[0]!"],
                      "1 ≤ i ∧ i ≤ lst.length ∧ (∃ k, k < i ∧ lst[k]! = m) ∧ ∀ k, k < i → m ≤ lst[k]!",
                      "i < lst.length", "lst.length - i", "m", term("(i + 1, min m lst[i]!)")),
                 bind("p", "Bool × Int",
                      "(p.1 = true ↔ ∃ k, k < lst.length ∧ m < lst[k]!) ∧ "
                      "(p.1 = true → (∃ k, k < lst.length ∧ lst[k]! = p.2 ∧ m < p.2) ∧ ∀ k, k < lst.length → m < lst[k]! → p.2 ≤ lst[k]!)",
                      loop([["i", "Nat"], ["f", "Bool"], ["r", "Int"]], ["0", "false", "0"],
                           "i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ m < lst[k]!) ∧ "
                           "(f = true → (∃ k, k < i ∧ lst[k]! = r ∧ m < r) ∧ ∀ k, k < i → m < lst[k]! → r ≤ lst[k]!)",
                           "i < lst.length", "lst.length - i", "(f, r)",
                           term("(i + 1, f || decide (m < lst[i]!), if m < lst[i]! ∧ (f = false ∨ lst[i]! < r) then lst[i]! else r)")),
                      cases("p.1 = true", term("some p.2"), term("none")))),
            _NS090)),
    "he_111_histogram": with_lemmas(
        term("(WS.dedup.filter (fun w => WS.count w == (WS.map (fun w => WS.count w)).foldl max 0)).map (fun w => (w, WS.count w))".replace("WS", '((test.splitOn " ").filter (fun w => w != ""))')),
        _HIST),
    "he_099_closest_integer": with_lemmas(
        term("if parseDec value ≥ 0 then ⌊parseDec value + 1 / 2⌋ else -⌊-parseDec value + 1 / 2⌋"), _ROUND),
    "he_010_make_palindrome": with_lemmas(
        loop([["i", "Nat"]], ["0"], "i ≤ string.length ∧ ∀ j, j < i → ¬ isPal (string.toList.drop j)",
             "i < string.length ∧ ¬ isPal (string.toList.drop i)", "string.length - i",
             "String.mk (string.toList ++ (string.toList.take i).reverse)", term("i + 1")),
        _MKPAL),
    "he_025_factorize": with_lemmas(
        loop([["n2", "Nat"], ["d", "Nat"], ["acc", "List Nat"]], ["n", "2", "[]"], '(1 ≤ n2 ∧ 2 ≤ d ∧ (acc).prod * n2 = n ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n2) ∧ (n2 = 1 ∨ d ≤ n2))', "1 < n2", "n2 + n2 - d", "acc",
             cases("n2 % d = 0", term("(n2 / d, d, acc ++ [d])"), term("(n2, d + 1, acc)"))),
        _FACT),
    "he_020_find_closest_elements": with_lemmas(
        loop([["j", "Nat"], ["lo", "ℚ"], ["hi", "ℚ"]], ["2", "min numbers[0]! numbers[1]!", "max numbers[0]! numbers[1]!"],
             '(lo ≤ hi ∧ (∃ b, b < j ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j ∧ j ≤ numbers.length', "j < numbers.length", "numbers.length - j", "(lo, hi)",
             bind("p", "ℚ × ℚ", '(p.1 ≤ p.2 ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((p.1 = numbers[a]! ∧ p.2 = numbers[b]!) ∨ (p.1 = numbers[b]! ∧ p.2 = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → p.2 - p.1 ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → p.2 - p.1 ≤ |numbers[a]! - numbers[j]!|))',
                  loop([["i", "Nat"], ["lo2", "ℚ"], ["hi2", "ℚ"]], ["0", "lo", "hi"], '(lo2 ≤ hi2 ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo2 = numbers[a]! ∧ hi2 = numbers[b]!) ∨ (lo2 = numbers[b]! ∧ hi2 = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi2 - lo2 ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi2 - lo2 ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j', "i < j", "j - i", "(lo2, hi2)",
                       cases("|numbers[i]! - numbers[j]!| < hi2 - lo2", term("(i + 1, min numbers[i]! numbers[j]!, max numbers[i]! numbers[j]!)"),
                             term("(i + 1, lo2, hi2)"))),
                  term("(j + 1, p.1, p.2)"))),
        _CLOSEST),
    "he_087_get_row": with_lemmas(
        term("(List.range lst.length).flatMap (fun i => (((List.range (lst[i]!).length).filter (fun j => (lst[i]!)[j]! == x)).reverse).map (fun j => (i, j)))"),
        _GETROW),
    "he_033_sort_third": with_lemmas(term('(List.range l.length).map (fun i => if i % 3 = 0 then ((atMod 3 l).mergeSort (fun a b => decide (a ≤ b)))[i / 3]! else l[i]!)'), _SORT3),
    "he_037_sort_even": with_lemmas(term('(List.range l.length).map (fun i => if i % 2 = 0 then ((atMod 2 l).mergeSort (fun a b => decide (a ≤ b)))[i / 2]! else l[i]!)'), _SORT2),
    "he_071_triangle_area": with_lemmas(
        cases("a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a", term("-1"),
              term("(((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100")),
        _TRI),
}
