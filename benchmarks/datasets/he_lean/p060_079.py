r"""HumanEval problems 63-79 (those not already in ``lean_specs.py``) specified in Lean."""

TOL = "(1 / 1000000 : ℚ)"

# a string of binary digits that stands for the number v (no leading zeros; "0" for zero)
BINARY_AUX = """@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')"""


def _is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def _fruit_ok(a):
    words = a[0].split(" ")
    return len(words) >= 4 and words[0].isdigit() and words[3].isdigit() and int(words[0]) + int(words[3]) <= a[1]


def _is_nat_list(xs):
    return isinstance(xs, list) and all(isinstance(x, int) and not isinstance(x, bool) and x >= 0 for x in xs)


ENTRIES = [
    dict(id="he_063_fibfib", name="fibfib", source="HumanEval/63",
         params=[("n", "Nat")], ret="Nat",
         description="The FibFib number sequence is defined as: fibfib(0) = 0, fibfib(1) = 0, fibfib(2) = 1, and fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3). Compute the n-th element of the fibfib number sequence efficiently.",
         pre_aux="""def fibfibSpec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => fibfibSpec (n + 2) + fibfibSpec (n + 1) + fibfibSpec n""",
         post="result = fibfibSpec n",
         code="""Id.run do
  if n == 0 then return 0
  if n == 1 then return 0
  let mut a := 0
  let mut b := 0
  let mut c := 1
  for _ in [3:n + 1] do
    (a, b, c) := (b, c, a + b + c)
  return c""", int_limit=28, tags=("scalar", "recursive-spec", "declarative")),

    dict(id="he_064_vowels_count", name="vowelsCount", source="HumanEval/64",
         params=[("s", "String")], ret="Nat",
         description="Count the vowels in a word: 'a', 'e', 'i', 'o', 'u' (in either case); 'y' is also a vowel, but only when it is at the end of the word.",
         post="""result = (s.toList.filter (fun c => ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)).length +
    (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0)""",
         code="""(s.toList.foldl (fun acc c => if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c then acc + 1 else acc) 0) +
  (if s.toList.getLast? == some 'y' || s.toList.getLast? == some 'Y' then 1 else 0)""",
         size_limit=40, tags=("string", "declarative")),

    dict(id="he_065_circular_shift", name="circularShift", source="HumanEval/65",
         params=[("x", "Nat"), ("shift", "Nat")], ret="String",
         description="Circular shift the digits of the integer x: shift the digits right by `shift` and return the result as a string. If shift is greater than the number of digits, return the digits reversed.",
         post="""let d := (toString x).toList
let n := d.length
result.toList = (if shift > n then d.reverse else d.drop (n - shift % n) ++ d.take (n - shift % n))""",
         code="""let d := (toString x).toList
let n := d.length
String.mk (if shift > n then d.reverse else d.drop (n - shift % n) ++ d.take (n - shift % n))""",
         valid=lambda a: a[0] >= 0 and a[1] >= 0, int_limit=10 ** 7, tags=("scalar", "string", "declarative")),

    dict(id="he_067_fruit_distribution", name="fruitDistribution", source="HumanEval/67",
         params=[("s", "String"), ("n", "Nat")], ret="Nat",
         description="Given a string that represents the number of apples and oranges in a basket of fruit (it also contains mangoes), and an integer that is the total number of fruits in the basket, return the number of mango fruits in the basket.",
         pre="""let w := s.splitOn " "
w.length ≥ 4 ∧ w[0]! ≠ "" ∧ w[3]! ≠ "" ∧ w[0]!.all Char.isDigit = true ∧ w[3]!.all Char.isDigit = true ∧ w[0]!.toNat! + w[3]!.toNat! ≤ n""",
         post="""let w := s.splitOn " "
result = n - w[0]!.toNat! - w[3]!.toNat!""",
         code="""let w := s.splitOn " "
n - w[0]!.toNat! - w[3]!.toNat!""", valid=_fruit_ok, size_limit=40, int_limit=10 ** 6, tags=("string", "scalar", "declarative")),

    dict(id="he_068_pluck", name="pluck", source="HumanEval/68",
         params=[("arr", "List Nat")], ret="List Nat",
         description="Given an array representing a branch of a tree that has non-negative integer nodes, pluck one of the nodes and return it: the node with the smallest even value (the one with the smallest index among equal ones), returned in a list [smallest value, its index]. If there are no even values or the array is empty, return [].",
         post="""(result = [] ↔ ∀ x ∈ arr, x % 2 = 1) ∧
  (result ≠ [] → result.length = 2 ∧ result[1]! < arr.length ∧ arr[result[1]!]! = result[0]! ∧ result[0]! % 2 = 0 ∧
    (∀ x ∈ arr, x % 2 = 0 → result[0]! ≤ x) ∧ ∀ j, j < result[1]! → arr[j]! ≠ result[0]!)""",
         code="""let evens := arr.filter (fun x => x % 2 == 0)
if evens.isEmpty then [] else
  let m := evens.foldl min evens.head!
  [m, arr.idxOf m]""", valid=lambda a: _is_nat_list(a[0]), tags=("list", "declarative")),

    dict(id="he_069_search", name="search", source="HumanEval/69",
         params=[("lst", "List Nat")], ret="Int",
         description="Given a non-empty list of positive integers, return the greatest integer that is greater than zero and has a frequency greater than or equal to the value of the integer itself (the frequency is the number of times it appears in the list). If no such value exists, return -1.",
         pre="lst ≠ [] ∧ ∀ x ∈ lst, x > 0",
         post="""(result = -1 ∧ ∀ x ∈ lst, lst.count x < x) ∨
  (result > 0 ∧ result.toNat ∈ lst ∧ lst.count result.toNat ≥ result.toNat ∧ ∀ x ∈ lst, lst.count x ≥ x → x ≤ result.toNat)""",
         code="lst.foldl (fun best x => if lst.count x ≥ x && (x : Int) > best then (x : Int) else best) (-1)",
         valid=lambda a: _is_nat_list(a[0]) and len(a[0]) > 0 and all(x > 0 for x in a[0]), tags=("list", "declarative")),

    dict(id="he_070_strange_sort_list", name="strangeSortList", source="HumanEval/70",
         params=[("lst", "List Int")], ret="List Int",
         description="Given a list of integers, return the list in strange order: start with the minimum value, then the maximum of the remaining integers, then the minimum, and so on.",
         post="""let s := lst.mergeSort (fun a b => a ≤ b)
result = (List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)""",
         code="""let s := lst.mergeSort (fun a b => a ≤ b)
(List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)""", tags=("list", "declarative")),

    dict(id="he_071_triangle_area", name="triangleArea71", source="HumanEval/71",
         params=[("a", "ℚ"), ("b", "ℚ"), ("c", "ℚ")], ret="ℚ",
         description="Given the lengths of the three sides of a triangle, return the area of the triangle rounded to 2 decimal points if the three sides form a valid triangle (the sum of any two sides is greater than the third side). Otherwise return -1.",
         pre_aux="""def area2 (a b c : ℚ) : ℚ :=
  let p := (a + b + c) / 2
  p * (p - a) * (p - b) * (p - c)""",
         pre="a > 0 ∧ b > 0 ∧ c > 0",
         post="""(a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a → result = -1) ∧
  (¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) →
    result ≥ 0 ∧ (result * 100).den = 1 ∧ (result < 1 / 200 ∨ (result - 1 / 200) ^ 2 ≤ area2 a b c) ∧
      area2 a b c ≤ (result + 1 / 200) ^ 2)""",
         code="""if a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a then -1 else
  let q := area2 a b c * 10000
  let m := Nat.sqrt (q.num.toNat / q.den)
  let r := if ((m : ℚ) + 1 / 2) ^ 2 ≤ q then m + 1 else m
  (r : ℚ) / 100""", valid=lambda a: all(v > 0 for v in a), tags=("scalar", "float", "declarative"),
         note="the area is the root of a rational, so the postcondition says that the result is a multiple of 1/100 within 1/200 of it"),

    dict(id="he_073_smallest_change", name="smallestChange", source="HumanEval/73",
         params=[("arr", "List Int")], ret="Nat",
         description="Given an array of integers, find the minimum number of elements that need to be changed to make the array palindromic (it reads the same backwards and forwards). In one change, you can change one element to any other element.",
         post="result = ((List.range (arr.length / 2)).filter (fun i => arr[i]! ≠ arr[arr.length - 1 - i]!)).length",
         code="(List.range (arr.length / 2)).foldl (fun acc i => if arr[i]! != arr[arr.length - 1 - i]! then acc + 1 else acc) 0",
         tags=("list", "declarative")),

    dict(id="he_074_total_match", name="totalMatch", source="HumanEval/74",
         params=[("lst1", "List String"), ("lst2", "List String")], ret="List String",
         description="Accept two lists of strings and return the list that has the smaller total number of characters over all its strings; if the two lists have the same number of characters, return the first list.",
         post="result = (if (lst1.map String.length).sum ≤ (lst2.map String.length).sum then lst1 else lst2)",
         code="if (lst1.foldl (fun a s => a + s.length) 0) ≤ (lst2.foldl (fun a s => a + s.length) 0) then lst1 else lst2",
         size_limit=8, tags=("list", "string", "declarative")),

    dict(id="he_075_is_multiply_prime", name="isMultiplyPrime", source="HumanEval/75",
         params=[("a", "Nat")], ret="Bool",
         description="Return true if the given number is the multiplication of 3 prime numbers (not necessarily distinct) and false otherwise. Knowing that the number is less than 100.",
         pre="a < 100",
         post="""result = true ↔ ∃ p, p < a + 1 ∧ ∃ q, q < a + 1 ∧ ∃ r, r < a + 1 ∧ p * q * r = a ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r""",
         code="""Id.run do
  let mut m := a
  let mut count := 0
  let mut i := 2
  while i ≤ m do
    if m % i == 0 then
      m := m / i
      count := count + 1
    else
      i := i + 1
  return a > 1 && count == 3""", valid=lambda a: 0 <= a[0] < 100, int_limit=100, tags=("scalar", "declarative")),

    dict(id="he_076_is_simple_power", name="isSimplePower", source="HumanEval/76",
         params=[("x", "Int"), ("n", "Int")], ret="Bool",
         description="Return true if a number x is a simple power of n and false in other cases. x is a simple power of n if n**k = x for an integer k.",
         post="result = true ↔ (x = 1 ∨ ∃ k, k < x.natAbs + 3 ∧ 1 ≤ k ∧ n ^ k = x)",
         code="""if x == 1 then true
else if n == 0 then x == 0
else if n == 1 then false
else if n == -1 then x.natAbs == 1
else Id.run do
  let mut p := n
  while p.natAbs ≤ x.natAbs do
    if p == x then return true
    p := p * n
  return false""", int_limit=3000, tags=("scalar", "declarative"),
         note="the exponent is searched below |x| + 3, which covers every case (for |n| >= 2 a solution has k <= |x|; n in {0, 1, -1} need k <= 2)"),

    dict(id="he_077_iscube", name="iscube", source="HumanEval/77",
         params=[("a", "Int")], ret="Bool",
         description="Return true if the integer a is a cube of some integer number.",
         post="result = true ↔ ∃ k, k < a.natAbs + 2 ∧ k ^ 3 = a.natAbs",
         code="(List.range (a.natAbs + 2)).any (fun k => k ^ 3 == a.natAbs)", int_limit=100000, tags=("scalar", "declarative")),

    dict(id="he_078_hex_key", name="hexKey", source="HumanEval/78",
         params=[("num", "String")], ret="Nat",
         description="Receive a hexadecimal number as a string and count the number of hexadecimal digits that are primes: 2, 3, 5, 7, B (decimal 11), D (decimal 13). The input is correct or empty, and the symbols A-F are uppercase.",
         post="result = (num.toList.filter (fun c => ['2', '3', '5', '7', 'B', 'D'].contains c)).length",
         code="num.toList.foldl (fun acc c => if ['2', '3', '5', '7', 'B', 'D'].contains c then acc + 1 else acc) 0",
         size_limit=40, tags=("string", "declarative")),

    dict(id="he_079_decimal_to_binary", name="decimalToBinary", source="HumanEval/79",
         params=[("decimal", "Nat")], ret="String",
         description="Convert a number in decimal form to binary format. Return a string in which each character is '0' or '1', with an extra couple of characters 'db' at the beginning and at the end of the string.",
         pre_aux=BINARY_AUX,
         post="""let l := result.toList
l.length ≥ 5 ∧ l.take 2 = ['d', 'b'] ∧ l.drop (l.length - 2) = ['d', 'b'] ∧ isBinary ((l.drop 2).take (l.length - 4)) decimal""",
         code="""Id.run do
  let mut m := decimal
  let mut bits := ""
  while m != 0 do
    bits := toString (m % 2) ++ bits
    m := m / 2
  return "db" ++ (if decimal == 0 then "0" else bits) ++ "db"
""",
         valid=lambda a: a[0] >= 0, int_limit=10 ** 6, tags=("scalar", "string", "declarative")),
]
