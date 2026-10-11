r"""HumanEval problems 20-39 (those not already in ``lean_specs.py``) specified in Lean."""

TOL = "(1 / 1000000 : ℚ)"

# values of any Python type, for the problems whose input is a list of "anything"
PYVAL_AUX = """inductive PyVal where
  | int (n : Int)
  | bool (b : Bool)
  | float (q : ℚ)
  | str (s : String)
  | none
  | list (l : List PyVal)
  | dict (d : List (PyVal × PyVal))"""

THIRDS_AUX = """def atMod (m : Nat) (x : List Int) : List Int := ((List.range x.length).filter (fun i => i % m = 0)).map (fun i => x[i]!)"""

ENCODE_AUX = """def encodeGroups : List Char → List Char
  | a :: b :: c :: rest => b :: c :: a :: encodeGroups rest
  | l => l"""


def _poly_ok(a):
    xs = a[0]
    return len(xs) > 0 and len(xs) % 2 == 0 and xs[-1] != 0 and all(isinstance(c, int) and not isinstance(c, bool) for c in xs)


ENTRIES = [
    dict(id="he_020_find_closest_elements", name="findClosestElements", source="HumanEval/20",
         params=[("numbers", "List ℚ")], ret="ℚ × ℚ",
         description="From a supplied list of numbers (of length at least two) select and return two that are the closest to each other, in order (smaller number, larger number).",
         pre="numbers.length ≥ 2",
         post="""(∃ j, j < numbers.length ∧ ∃ i, i < j ∧
    ((result.1 = numbers[i]! ∧ result.2 = numbers[j]!) ∨ (result.1 = numbers[j]! ∧ result.2 = numbers[i]!))) ∧
  result.1 ≤ result.2 ∧
  ∀ j, j < numbers.length → ∀ i, i < j → result.2 - result.1 ≤ |numbers[i]! - numbers[j]!|""",
         code="""let sorted := numbers.mergeSort (fun a b => a ≤ b)
let pairs := sorted.zip sorted.tail
pairs.foldl (fun best p => if p.2 - p.1 < best.2 - best.1 then p else best) pairs.head!""",
         valid=lambda a: len(a[0]) >= 2, tags=("list", "float", "declarative"),
         note="any closest pair is accepted (the canonical solution returns the first in sorted order)"),

    dict(id="he_021_rescale_to_unit", name="rescaleToUnit", source="HumanEval/21",
         params=[("numbers", "List ℚ")], ret="List ℚ",
         description="Given a list of numbers (of at least two elements), apply a linear transform to the list so that the smallest number becomes 0 and the largest becomes 1.",
         pre="numbers.length ≥ 2 ∧ numbers.foldl min numbers[0]! < numbers.foldl max numbers[0]!",
         post=f"""result.length = numbers.length ∧ ∀ i, i < numbers.length →
    |result[i]! - (numbers[i]! - numbers.foldl min numbers[0]!) / (numbers.foldl max numbers[0]! - numbers.foldl min numbers[0]!)| ≤ {TOL}""",
         code="""let mi := numbers.foldl min numbers[0]!
let ma := numbers.foldl max numbers[0]!
numbers.map (fun x => (x - mi) / (ma - mi))""",
         valid=lambda a: len(a[0]) >= 2 and max(a[0]) > min(a[0]), tags=("list", "float")),

    dict(id="he_022_filter_integers", name="filterIntegers", source="HumanEval/22",
         params=[("values", "List PyVal")], ret="List Int",
         description="Filter a given list of any Python values, keeping only the integers (a boolean is not an integer here).",
         pre_aux=PYVAL_AUX,
         post="result = values.filterMap (fun v => match v with | PyVal.int n => some n | _ => none)",
         code="values.foldr (fun v acc => match v with | PyVal.int n => n :: acc | _ => acc) []",
         size_limit=10, tags=("list", "any", "declarative")),

    dict(id="he_025_factorize", name="factorize", source="HumanEval/25",
         params=[("n", "Nat")], ret="List Nat",
         description="Return the list of prime factors of the given integer in order from smallest to largest. Each factor is listed as many times as it appears in the factorization; the input number equals the product of all the factors.",
         pre="n ≥ 1",
         post="""result.prod = n ∧ (∀ p ∈ result, Nat.Prime p) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!""",
         code="""Id.run do
  let mut m := n
  let mut i := 2
  let mut fact : List Nat := []
  while i * i ≤ m do
    if m % i == 0 then
      fact := fact ++ [i]
      m := m / i
    else
      i := i + 1
  if m > 1 then fact := fact ++ [m]
  return fact""", valid=lambda a: a[0] >= 1, int_limit=100000, tags=("scalar", "list", "declarative")),

    dict(id="he_026_remove_duplicates", name="removeDuplicates", source="HumanEval/26",
         params=[("numbers", "List Int")], ret="List Int",
         description="From a list of integers, remove all elements that occur more than once. Keep the order of the remaining elements the same as in the input.",
         post="result = numbers.filter (fun x => numbers.count x = 1)",
         code="numbers.foldr (fun x acc => if numbers.count x = 1 then x :: acc else acc) []", tags=("list", "declarative")),

    dict(id="he_027_flip_case", name="flipCase", source="HumanEval/27",
         params=[("string", "String")], ret="String",
         description="For a given string, flip lowercase characters to uppercase and uppercase characters to lowercase.",
         pre_aux="def flipChar (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c",
         post="result.length = string.length ∧ ∀ i, i < string.length → result.toList[i]! = flipChar string.toList[i]!",
         code="String.mk (string.toList.map flipChar)", valid=lambda a: a[0].isascii(), size_limit=40,
         note="inputs are limited to ASCII: Lean's Char.isUpper/isLower know ASCII only, Python's swapcase knows Unicode",
         tags=("string", "declarative")),

    dict(id="he_032_find_zero", name="findZero", source="HumanEval/32",
         params=[("xs", "List Int")], ret="ℚ",
         description="xs are the coefficients of a polynomial, xs[0] + xs[1] * x + xs[2] * x^2 + ... Find x such that the polynomial is (nearly) zero at x. Only one zero is returned, even if there are many. The list has an even number of coefficients and its last coefficient is non-zero, which guarantees a solution.",
         pre_aux="""def polyEval (xs : List Int) (x : ℚ) : ℚ := (List.range xs.length).foldl (fun acc i => acc + ((xs[i]! : Int) : ℚ) * x ^ i) 0""",
         pre="xs ≠ [] ∧ xs.length % 2 = 0 ∧ xs.getLast! ≠ 0",
         post="|polyEval xs result| < (1 / 10000 : ℚ)",
         code="""let bound : ℚ := 1 + (xs.map (fun c => |(c : ℚ)|)).foldl max 0 / |(xs.getLast! : ℚ)|
Id.run do
  let mut lo : ℚ := -bound
  let mut hi : ℚ := bound
  let slo := polyEval xs lo
  for _ in [0:80] do
    let mid := (lo + hi) / 2
    if polyEval xs mid * slo ≤ 0 then hi := mid else lo := mid
  return (lo + hi) / 2""", valid=_poly_ok, size_limit=8, int_limit=1000,
         reference_mode="spec", permissive=True,
         note="any root is accepted (the canonical solution runs Newton's method from 0); HumanEval's own test asserts |poly(x)| < 1e-4",
         tags=("list", "float", "declarative")),

    dict(id="he_033_sort_third", name="sortThird", source="HumanEval/33",
         params=[("l", "List Int")], ret="List Int",
         description="Return a list l' identical to l at the indices that are not divisible by three, while its values at the indices divisible by three are equal to the values of l at those indices, but sorted.",
         pre_aux=THIRDS_AUX,
         post="""result.length = l.length ∧ (∀ i, i < l.length → i % 3 ≠ 0 → result[i]! = l[i]!) ∧
  (atMod 3 result).isPerm (atMod 3 l) ∧ ∀ i, i < (atMod 3 result).length - 1 → (atMod 3 result)[i]! ≤ (atMod 3 result)[i + 1]!""",
         code="""let sorted := (atMod 3 l).mergeSort (fun a b => a ≤ b)
(List.range l.length).map (fun i => if i % 3 = 0 then sorted[i / 3]! else l[i]!)""", tags=("list", "declarative")),

    dict(id="he_036_fizz_buzz", name="fizzBuzz", source="HumanEval/36",
         params=[("n", "Nat")], ret="Nat",
         description="Return the number of times the digit 7 appears in the integers less than n which are divisible by 11 or 13.",
         post="result = (((List.range n).filter (fun i => i % 11 = 0 ∨ i % 13 = 0)).map (fun i => (toString i).toList.count '7')).sum",
         code="""(List.range n).foldl (fun acc i => if i % 11 == 0 || i % 13 == 0 then acc + (toString i).toList.count '7' else acc) 0""",
         int_limit=20000, tags=("scalar", "declarative")),

    dict(id="he_037_sort_even", name="sortEven", source="HumanEval/37",
         params=[("l", "List Int")], ret="List Int",
         description="Return a list l' identical to l at the odd indices, while its values at the even indices are equal to the values of l at the even indices, but sorted.",
         pre_aux=THIRDS_AUX,
         post="""result.length = l.length ∧ (∀ i, i < l.length → i % 2 ≠ 0 → result[i]! = l[i]!) ∧
  (atMod 2 result).isPerm (atMod 2 l) ∧ ∀ i, i < (atMod 2 result).length - 1 → (atMod 2 result)[i]! ≤ (atMod 2 result)[i + 1]!""",
         code="""let sorted := (atMod 2 l).mergeSort (fun a b => a ≤ b)
(List.range l.length).map (fun i => if i % 2 = 0 then sorted[i / 2]! else l[i]!)""", tags=("list", "declarative")),

    dict(id="he_038_decode_cyclic", name="decodeCyclic", source="HumanEval/38",
         params=[("s", "String")], ret="String",
         description="Takes as input a string encoded with encode_cyclic (which cycles groups of three characters: abc becomes bca, a group of fewer than three characters is left alone) and returns the decoded string.",
         pre_aux=ENCODE_AUX,
         post="encodeGroups result.toList = s.toList",
         code="""let rec decode : List Char → List Char
  | a :: b :: c :: rest => c :: a :: b :: decode rest
  | l => l
String.mk (decode s.toList)""", size_limit=40, tags=("string", "declarative"),
         note="stated as the inverse of encode_cyclic: encoding the result gives back the input"),

    dict(id="he_039_prime_fib", name="primeFib", source="HumanEval/39",
         params=[("n", "Nat")], ret="Nat",
         description="Return the n-th number that is a Fibonacci number and also prime (the first is 2, then 3, 5, 13, 89).",
         pre="n ≥ 1",
         post="""∃ k, k < 300 ∧ Nat.fib k = result ∧ Nat.Prime result ∧
    (((List.range k).map Nat.fib).filter (fun m => decide (Nat.Prime m))).length = n - 1""",
         code="""Id.run do
  let mut count := 0
  let mut k := 0
  let mut res := 0
  while count < n do
    k := k + 1
    if decide (Nat.Prime (Nat.fib k)) then
      count := count + 1
      res := Nat.fib k
  return res""", int_limit=11, valid=lambda a: a[0] >= 1, tags=("scalar", "declarative"),
         note="the index of the Fibonacci number is searched below 300 (the 12th prime Fibonacci number has index 83)"),
]
