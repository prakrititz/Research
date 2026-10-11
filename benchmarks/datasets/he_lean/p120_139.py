r"""HumanEval problems 120-139 (those not already in ``lean_specs.py``) specified in Lean."""
import math

from benchmarks.datasets.he_lean.p000_019 import PAREN_AUX


def _is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def _grid_ok(a):
    grid, k = a
    n = len(grid)
    if n < 2 or any(len(r) != n for r in grid) or sorted(v for r in grid for v in r) != list(range(1, n * n + 1)):
        return False
    return n <= 4 and k <= 9


def _date_ok(a):
    return a[0].isascii()


def _split_ok(a):
    return a[0].isascii() and not any(c in a[0] for c in "\x0b\x0c")


ENTRIES = [
    dict(id="he_120_maximum", name="maximum", source="HumanEval/120",
         params=[("arr", "List Int"), ("k", "Nat")], ret="List Int",
         description="Given an array arr of integers and a non-negative integer k, return a sorted list of length k with the maximum k numbers in arr.",
         pre="k ≤ arr.length",
         post="result.isPerm ((arr.mergeSort (fun a b => a ≥ b)).take k) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!",
         code="((arr.mergeSort (fun a b => a ≥ b)).take k).mergeSort (fun a b => a ≤ b)", valid=lambda a: a[1] <= len(a[0]),
         tags=("list", "declarative")),

    dict(id="he_122_add_elements", name="addElements", source="HumanEval/122",
         params=[("arr", "List Int"), ("k", "Nat")], ret="Int",
         description="Given a non-empty array of integers arr and an integer k, return the sum of the elements with at most two digits from the first k elements of arr.",
         pre="arr ≠ [] ∧ 1 ≤ k ∧ k ≤ arr.length", post="result = ((arr.take k).filter (fun x => x.natAbs < 100)).sum",
         code="(arr.take k).foldl (fun acc x => if x.natAbs < 100 then acc + x else acc) 0",
         valid=lambda a: len(a[0]) >= 1 and 1 <= a[1] <= len(a[0]), tags=("list", "declarative")),

    dict(id="he_123_get_odd_collatz", name="getOddCollatz", source="HumanEval/123",
         params=[("n", "Nat")], ret="List Nat",
         description="Given a positive integer n, return a sorted list that has the odd numbers in the Collatz sequence (if the previous term is even, the next term is half of it; if it is odd, the next term is 3 times it plus 1; the sequence ends at 1). Collatz(1) is [1].",
         pre_aux="""def collatzSeq : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x ≤ 1 then [1] else x :: collatzSeq fuel (if x % 2 = 0 then x / 2 else 3 * x + 1)""",
         pre="n ≥ 1",
         post="result.isPerm ((collatzSeq 5000 n).filter (fun x => x % 2 = 1)) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!",
         code="((collatzSeq 5000 n).filter (fun x => x % 2 = 1)).mergeSort (fun a b => a ≤ b)", valid=lambda a: a[0] >= 1,
         int_limit=100000, tags=("scalar", "list", "declarative"),
         note="the sequence is followed for at most 5000 steps (the longest start below 10^5 needs 350)"),

    dict(id="he_124_valid_date", name="validDate", source="HumanEval/124",
         params=[("date", "String")], ret="Bool",
         description="Validate a given date string and return true if the date is valid. The date is valid if: it is not empty; the number of days is not less than 1 or higher than 31 for months 1,3,5,7,8,10,12, not higher than 30 for months 4,6,9,11 and not higher than 29 for month 2; the month is between 1 and 12; and the format is mm-dd-yyyy.",
         pre_aux="""def natOf (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
def daysIn (m : Nat) : Nat := [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]!""",
         post="""let l := date.toList
result = true ↔ (l.length = 10 ∧ l[2]! = '-' ∧ l[5]! = '-' ∧ (l.take 2).all Char.isDigit = true ∧ ((l.drop 3).take 2).all Char.isDigit = true ∧
  (l.drop 6).all Char.isDigit = true ∧ 1 ≤ natOf (l.take 2) ∧ natOf (l.take 2) ≤ 12 ∧ 1 ≤ natOf ((l.drop 3).take 2) ∧
  natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))""",
         code="""let l := date.toList
decide (l.length = 10) && l[2]! == '-' && l[5]! == '-' && (l.take 2).all Char.isDigit && ((l.drop 3).take 2).all Char.isDigit &&
  (l.drop 6).all Char.isDigit && decide (1 ≤ natOf (l.take 2)) && decide (natOf (l.take 2) ≤ 12) &&
  decide (1 ≤ natOf ((l.drop 3).take 2)) && decide (natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))""",
         valid=_date_ok, size_limit=20, tags=("string", "declarative")),

    dict(id="he_125_split_words", name="splitWords", source="HumanEval/125",
         params=[("txt", "String")], ret="List String ⊕ Nat",
         description="Given a string of words, return a list of words split on whitespace; if no whitespace exists in the text, split on commas ','; if no commas exist, return the number of lower-case letters with odd order in the alphabet (ord('a') = 0, ord('b') = 1, ... ord('z') = 25).",
         pre_aux="""def splitWhite (txt : String) : List String :=
  ((txt.map (fun c => if c == '\\n' || c == '\\r' || c == '\\t' then ' ' else c)).splitOn " ").filter (fun w => w != "")""",
         post="""let hasWhite := txt.toList.any (fun c => c == ' ' || c == '\\n' || c == '\\r' || c == '\\t')
result = (if hasWhite then Sum.inl (splitWhite txt)
  else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",")
  else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 = 1)).length))""",
         code="""let hasWhite := txt.toList.any (fun c => c == ' ' || c == '\\n' || c == '\\r' || c == '\\t')
if hasWhite then Sum.inl (splitWhite txt)
else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",")
else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 == 1)).length)""",
         valid=_split_ok, size_limit=40, tags=("string", "list", "sum", "declarative")),

    dict(id="he_127_intersection", name="intersection", source="HumanEval/127",
         params=[("interval1", "Int × Int"), ("interval2", "Int × Int")], ret="String",
         description="You are given two closed intervals, each a pair of integers (start, end) with start <= end. Determine whether the length of the intersection of these two intervals is a prime number. If it is, return \"YES\", otherwise \"NO\". If the two intervals don't intersect, return \"NO\".",
         pre="interval1.1 ≤ interval1.2 ∧ interval2.1 ≤ interval2.2",
         post="""let len := min interval1.2 interval2.2 - max interval1.1 interval2.1
(result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (len ≥ 2 ∧ Nat.Prime len.toNat))""",
         code="""let len := min interval1.2 interval2.2 - max interval1.1 interval2.1
if len ≥ 2 && decide (Nat.Prime len.toNat) then "YES" else "NO"
""", valid=lambda a: a[0][0] <= a[0][1] and a[1][0] <= a[1][1], tags=("scalar", "declarative")),

    dict(id="he_128_prod_signs", name="prodSigns", source="HumanEval/128",
         params=[("arr", "List Int")], ret="Option Int",
         description="Given an array arr of integers, return the sum of the magnitudes of the integers multiplied by the product of all the signs of each number in the array, represented by 1, -1 or 0. Return none for an empty array.",
         post="""match result with
| none => arr = []
| some r => arr ≠ [] ∧ r = (arr.map (fun (x : Int) => (x.natAbs : Int))).sum * (arr.map Int.sign).prod""",
         code="""if arr = [] then none else some ((arr.foldl (fun (s : Int) (x : Int) => s + (x.natAbs : Int)) 0) * (arr.foldl (fun (p : Int) (x : Int) => p * x.sign) 1))""",
         tags=("list", "option", "declarative")),

    dict(id="he_129_min_path", name="minPath", source="HumanEval/129",
         params=[("grid", "List (List Nat)"), ("k", "Nat")], ret="List Nat",
         description="Given a grid with N rows and N columns (N >= 2) and a positive integer k, each cell of the grid contains a value. Every integer in the range [1, N * N] inclusive appears exactly once on the cells of the grid. Find the minimum path of length k in the grid: you can start from any cell, and in each step you can move to any of the neighbour cells (cells that share an edge with the current cell); a path of length k visits exactly k cells (not necessarily distinct). A path A is less than a path B if the ordered list of the values on the cells of A is lexicographically less than that of B. Return the ordered list of the values on the cells that the minimum path goes through.",
         pre_aux="""def gridCells (n : Nat) : List (Nat × Nat) := (List.range n).flatMap (fun i => (List.range n).map (fun j => (i, j)))

def stepsFrom (n : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  (gridCells n).filter (fun q => (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ q.2 + 1 = p.2)) ∨ (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ q.1 + 1 = p.1)))

def walksOf (n : Nat) : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | 1 => (gridCells n).map (fun c => [c])
  | k + 2 => (walksOf n (k + 1)).flatMap (fun w => (stepsFrom n w.getLast!).map (fun q => w ++ [q]))

def cellAt (g : List (List Nat)) (p : Nat × Nat) : Nat := (g[p.1]!)[p.2]!""",
         pre="""grid.length ≥ 2 ∧ (∀ r ∈ grid, r.length = grid.length) ∧ grid.flatten.isPerm (List.range' 1 (grid.length * grid.length)) ∧ k ≥ 1""",
         post="""(∃ w ∈ walksOf grid.length k, w.map (cellAt grid) = result) ∧ ∀ w ∈ walksOf grid.length k, ¬ (w.map (cellAt grid) < result)""",
         code="""let n := grid.length
let walks := (walksOf n k).map (fun w => w.map (cellAt grid))
walks.foldl (fun best w => if w < best then w else best) walks.head!""",
         valid=_grid_ok, size_limit=5, tags=("list", "grid", "declarative"),
         note="stated as the problem states it: the lexicographically least among all walks of length k (evaluated on grids up to 4x4 and k <= 9)"),

    dict(id="he_130_tri", name="tri", source="HumanEval/130",
         params=[("n", "Nat")], ret="List Nat",
         description="Tribonacci sequence: tri(1) = 3, tri(n) = 1 + n / 2 if n is even, tri(n) = tri(n - 1) + tri(n - 2) + tri(n + 1) if n is odd. Given a non-negative integer n, return a list of the first n + 1 numbers of the Tribonacci sequence (tri(0) = 1).",
         post="""result.length = n + 1 ∧ result[0]! = 1 ∧ (n ≥ 1 → result[1]! = 3) ∧
  ∀ i, i < n + 1 → 2 ≤ i → result[i]! = (if i % 2 = 0 then 1 + i / 2 else result[i - 1]! + result[i - 2]! + (1 + (i + 1) / 2))""",
         code="""Id.run do
  let mut ans : List Nat := [1, 3]
  if n == 0 then return [1]
  for i in [2:n + 1] do
    if i % 2 == 0 then ans := ans ++ [1 + i / 2]
    else ans := ans ++ [ans[i - 1]! + ans[i - 2]! + 1 + (i + 1) / 2]
  return ans""", adapt_out=lambda out: [int(v) for v in out], int_limit=60, tags=("scalar", "list", "declarative"),
         note="the values are integers (Python prints some of them as floats)"),

    dict(id="he_131_digits", name="digits", source="HumanEval/131",
         params=[("n", "Nat")], ret="Nat",
         description="Given a positive integer n, return the product of the odd digits. Return 0 if all digits are even.",
         pre="n ≥ 1",
         post="""let ds := (toString n).toList.map (fun c => c.toNat - 48)
result = (if ds.any (fun d => d % 2 = 1) then (ds.filter (fun d => d % 2 = 1)).prod else 0)""",
         code="""let ds := (toString n).toList.map (fun c => c.toNat - 48)
if ds.any (fun d => d % 2 == 1) then (ds.filter (fun d => d % 2 == 1)).foldl (fun a d => a * d) 1 else 0""",
         valid=lambda a: a[0] >= 1, int_limit=10 ** 9, tags=("scalar", "declarative")),

    dict(id="he_132_is_nested", name="isNested", source="HumanEval/132",
         params=[("string", "String")], ret="Bool",
         description="Create a function that takes a string which contains only square brackets. The function should return true if and only if there is a valid group of brackets (a balanced run of brackets that is not split into smaller balanced runs) in which at least one bracket is nested.",
         pre_aux="""@[reducible, simp] def isBalancedSq (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ']' ≤ (l.take k).count '[') ∧ l.count '[' = l.count ']'""",
         pre="string.toList.all (fun c => c == '[' || c == ']') = true",
         post="""result = true ↔ ∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧
    isBalancedSq ((string.toList.drop i).take len) ∧ ∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k)""",
         code="""Id.run do
  let l := string.toList
  for i in [0:l.length] do
    if l[i]! == ']' then continue
    let mut cnt : Int := 0
    let mut maxNest : Int := 0
    for j in [i:l.length] do
      if l[j]! == '[' then cnt := cnt + 1 else cnt := cnt - 1
      maxNest := max maxNest cnt
      if cnt == 0 then
        if maxNest ≥ 2 then return true
        break
  return false""", valid=lambda a: set(a[0]) <= set("[]"), size_limit=20, tags=("string", "declarative"),
         note="a nested pair inside a balanced group: a run that is balanced, has no balanced proper prefix, and is longer than []"),
]
