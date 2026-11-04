
def isEven (n : Int) : Bool := n % 2 == 0
@[reducible, simp] def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) :=
  result.all (fun x => isEven x ∧ x ∈ arr.toList ∧ result.toList.count x = arr.toList.count x) ∧
  arr.all (fun x => isEven x → x ∈ result.toList) ∧
  arr.all (fun x => arr.all (fun y =>
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y))
@[reducible, simp] def MoveZeroesToEnd_postcond (arr : Array Int) (result: Array Int) :=
  let firstResZeroIdx := result.toList.idxOf 0
  List.isPerm result.toList arr.toList ∧
  result.toList.take firstResZeroIdx = arr.toList.filter (· ≠ 0) ∧
  result.toList.drop firstResZeroIdx = arr.toList.filter (· = 0)
@[reducible, simp] def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop := result ↔ ∃ i : Nat, i * i = n

-- verina_basic_41 exit
example (a : Array ℤ) (i : ℕ) (r : Bool) (h_precond : a.size > 0)
    (h1i : ((r = true) = ∀ j < i, a[j]! = a[0]!) ∧ i ≤ a.size) (h1g : ¬(i < a.size ∧ r = true)) :
    r = true → List.Pairwise (fun x1 x2 => x1 = x2) a.toList := by
  intro hr; apply Refine.pairwise_eq_of_all_eq_head_arr; all_goals first | assumption | (simp_all; done) | omega | grind
-- verina_basic_48 exit, as the portfolio's `lib_simp; lib_apply`
example (n i : ℕ) (h1i : ∀ j < i, j * j ≠ n) (h1g : ¬i * i ≤ n) :
    isPerfectSquare_postcond n (if i * i = n then true else false) := by
  simp_all; apply Refine.sq_search_exit; all_goals first | assumption | (simp_all; done) | omega
-- verina_basic_51 step
example (a : Array ℤ) (key : ℤ) (lo hi : ℕ) (h_precond : List.Pairwise (· ≤ ·) a.toList)
    (h1i : lo ≤ hi ∧ hi ≤ a.size ∧ ((a.take lo).all fun x => decide (x < key)) = true ∧ ((a.drop hi).all fun x => decide (x ≥ key)) = true)
    (h1g : lo < hi) (h3 : a[(lo + hi) / 2]'(by omega) < key) :
    ((a.take ((lo + hi) / 2 + 1)).all fun x => decide (x < key)) = true := by
  apply Refine.sorted_take_succ_all_lt <;> first | assumption | (simp_all; done) | omega
-- verina_basic_34 term: Bool `all` / `decide` as `∀` / `→` first, then each goal
example (arr : Array ℤ) : findEvenNumbers_postcond arr (Array.foldl (fun acc x => if isEven x = true then acc.push x else acc) #[] arr) := by
  simp only [findEvenNumbers_postcond]
  repeat' apply And.intro
  all_goals ((simp only [← Array.all_toList, List.all_eq_true, decide_eq_true_eq, Refine.arr_foldl_push_filter] at *); (try intros))
  all_goals first | (simp_all; done) | (apply Refine.idxOf_filter_le; all_goals first | assumption | (simp_all; done) | omega) | (simp_all [List.mem_filter, List.count_filter]; done)
-- verina_basic_35 term
example (arr : Array ℤ) : MoveZeroesToEnd_postcond arr (Array.mk (arr.toList.filter (fun x => x ≠ 0) ++ arr.toList.filter (fun x => x = 0))) := by
  simp [Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm]
@[reducible, simp] def ifPowerOfFour_postcond (n : Nat) (result: Bool) : Prop := result ↔ (∃ m:Nat, n=4^m)
@[reducible, simp] def greatestCommonDivisor_postcond (a : Nat) (b : Nat) (result: Nat) :=
  result > 0 ∧ a % result = 0 ∧ b % result = 0 ∧ ∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ result
-- verina_advanced_14 exit, as `lib_apply` would
example (n curr : ℕ) (h1 : ¬n = 0) (h3i : ∃ m, n = curr * 4 ^ m) (h3g : ¬(curr ≠ 1 ∧ curr % 4 = 0)) :
    ifPowerOfFour_postcond n (decide (curr = 1)) := by
  simp only [ifPowerOfFour_postcond, decide_eq_true_eq]
  apply Refine.pow_iff_of_factor; all_goals first | assumption | (simp_all; done) | omega
example (n curr : ℕ) (h1 : ¬n = 0) (h3i : ∃ m, n = curr * 4 ^ m) (h3g : ¬(curr ≠ 1 ∧ curr % 4 = 0)) :
    ifPowerOfFour_postcond n (decide (curr = 1)) := by
  simp_all
  apply Refine.pow_iff_of_factor; all_goals first | assumption | (simp_all; done) | omega
-- he_013 exit, after the portfolio's prep
example (a b a' b' : ℕ) (h1 : a' > 0) (h2 : ∀ d, d > 0 → (a % d = 0 ∧ b % d = 0 ↔ a' % d = 0 ∧ b' % d = 0)) (h1g : ¬b' ≠ 0) :
    a % a' = 0 := by
  apply Refine.mod_left_of_common_divisors
  trace_state
  all_goals first | assumption | (simp_all; done) | omega
example (a b a' b' : ℕ) (h1 : a' > 0) (h2 : ∀ d, d > 0 → (a % d = 0 ∧ b % d = 0 ↔ a' % d = 0 ∧ b' % d = 0)) (h1g : ¬b' ≠ 0) :
    ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a' := by
  apply Refine.le_of_common_divisors; all_goals first | assumption | (simp_all; done) | omega
