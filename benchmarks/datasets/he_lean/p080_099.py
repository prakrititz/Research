r"""HumanEval problems 80-99 (those not already in ``lean_specs.py``) specified in Lean."""
from fractions import Fraction

from benchmarks.datasets.he_lean.p020_039 import PYVAL_AUX
from benchmarks.datasets.he_lean.p060_079 import BINARY_AUX

VOWELS = "['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']"


def _is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def _closest_exact(value):
    """The nearest integer to the decimal string as an exact rational would give it (ties away from zero)."""
    q = Fraction(value)
    f = q.__floor__()
    frac = q - f
    if frac < Fraction(1, 2):
        return f
    if frac > Fraction(1, 2):
        return f + 1
    return f + 1 if q > 0 else f


def _canonical_closest(text):
    """HumanEval's canonical solution, through a float."""
    val = float(text)
    if abs(val - int(val)) != 0.5:
        return round(val)
    return int(val) + 1 if val > 0 else int(val) - 1


def _closest_ok(a):
    """A well-formed numeral on which the canonical solution (a float) and the exact decimal reading agree."""
    import re
    text = a[0]
    if not re.fullmatch(r"-?(\d+\.?\d*|\.\d+)", text):
        return False
    return _canonical_closest(text) == _closest_exact(text)


ENTRIES = [
    dict(id="he_080_is_happy", name="isHappy", source="HumanEval/80",
         params=[("s", "String")], ret="Bool",
         description="You are given a string s. Check if the string is happy: a string is happy if its length is at least 3 and every 3 consecutive letters are distinct.",
         post="""result = true ↔ (s.length ≥ 3 ∧ ∀ i, i < s.length - 2 → s.toList[i]! ≠ s.toList[i + 1]! ∧ s.toList[i]! ≠ s.toList[i + 2]! ∧
    s.toList[i + 1]! ≠ s.toList[i + 2]!)""",
         code="""decide (s.length ≥ 3) && (List.range (s.length - 2)).all (fun i =>
  s.toList[i]! != s.toList[i + 1]! && s.toList[i]! != s.toList[i + 2]! && s.toList[i + 1]! != s.toList[i + 2]!)""",
         size_limit=30, tags=("string", "declarative")),

    dict(id="he_081_numerical_letter_grade", name="numericalLetterGrade", source="HumanEval/81",
         params=[("grades", "List ℚ")], ret="List String",
         description="Given a list of GPAs, output a list of letter grades using the table: 4.0 is A+; above 3.7 A; above 3.3 A-; above 3.0 B+; above 2.7 B; above 2.3 B-; above 2.0 C+; above 1.7 C; above 1.3 C-; above 1.0 D+; above 0.7 D; above 0.0 D-; 0.0 is E.",
         pre_aux="""def letterGrade (x : ℚ) : String :=
  if x = 4 then "A+" else if x > 37 / 10 then "A" else if x > 33 / 10 then "A-" else if x > 3 then "B+"
  else if x > 27 / 10 then "B" else if x > 23 / 10 then "B-" else if x > 2 then "C+" else if x > 17 / 10 then "C"
  else if x > 13 / 10 then "C-" else if x > 1 then "D+" else if x > 7 / 10 then "D" else if x > 0 then "D-" else "E"
""",
         post="result.length = grades.length ∧ ∀ i, i < grades.length → result[i]! = letterGrade grades[i]!",
         code="grades.map letterGrade", tags=("list", "float", "declarative")),

    dict(id="he_082_prime_length", name="primeLength", source="HumanEval/82",
         params=[("string", "String")], ret="Bool",
         description="Take a string and return true if the string length is a prime number, false otherwise.",
         post="result = true ↔ Nat.Prime string.length", code="decide (Nat.Prime string.length)", size_limit=40,
         tags=("string", "declarative")),

    dict(id="he_083_starts_one_ends", name="startsOneEnds", source="HumanEval/83",
         params=[("n", "Nat")], ret="Nat",
         description="Given a positive integer n, return the count of the n-digit positive integers that start or end with 1.",
         pre="n ≥ 1",
         post="result = ((List.range (10 ^ n)).filter (fun m => 10 ^ (n - 1) ≤ m ∧ (m / 10 ^ (n - 1) = 1 ∨ m % 10 = 1))).length",
         code="if n == 1 then 1 else 18 * 10 ^ (n - 2)", valid=lambda a: a[0] >= 1, int_limit=5, tags=("scalar", "declarative"),
         note="the postcondition counts the numbers; it can be evaluated only for n <= 5, which is why the tests stop there"),

    dict(id="he_084_solve", name="solve84", source="HumanEval/84",
         params=[("N", "Nat")], ret="String",
         description="Given a positive integer N, return the total sum of its digits in binary, as a string.",
         pre_aux=BINARY_AUX,
         post="isBinary result.toList (((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum)",
         code="""Id.run do
  let total := ((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum
  let mut m := total
  let mut bits := ""
  while m != 0 do
    bits := toString (m % 2) ++ bits
    m := m / 2
  return (if total == 0 then "0" else bits)""", int_limit=10 ** 6, tags=("scalar", "string", "declarative")),

    dict(id="he_086_anti_shuffle", name="antiShuffle", source="HumanEval/86",
         params=[("s", "String")], ret="String",
         description="Return an ordered version of the string: each word (separated by a space) is replaced by a word in which all the characters are arranged in ascending order of their ASCII value. Keep the order of the words and the blank spaces.",
         post="""let ws := s.splitOn " "
let rs := result.splitOn " "
rs.length = ws.length ∧ ∀ i, i < ws.length → rs[i]!.toList.isPerm ws[i]!.toList ∧
  ∀ j, j < rs[i]!.length - 1 → rs[i]!.toList[j]!.toNat ≤ rs[i]!.toList[j + 1]!.toNat""",
         code="""\" \".intercalate ((s.splitOn " ").map (fun w => String.mk (w.toList.mergeSort (fun a b => a.toNat ≤ b.toNat))))""",
         size_limit=40, tags=("string", "declarative")),

    dict(id="he_087_get_row", name="getRow", source="HumanEval/87",
         params=[("lst", "List (List Int)"), ("x", "Int")], ret="List (Nat × Nat)",
         description="Given a 2-dimensional list of rows of different lengths and an integer x, find the integers x in the list and return the list of coordinates (row, column), starting with 0, sorted by rows in ascending order and, within a row, by columns in descending order.",
         post="""(∀ p ∈ result, p.1 < lst.length ∧ p.2 < lst[p.1]!.length ∧ (lst[p.1]!)[p.2]! = x) ∧
  (∀ i, i < lst.length → ∀ j, j < lst[i]!.length → (lst[i]!)[j]! = x → (i, j) ∈ result) ∧ result.Nodup ∧
  ∀ k, k < result.length - 1 → result[k]!.1 < result[k + 1]!.1 ∨ (result[k]!.1 = result[k + 1]!.1 ∧ result[k + 1]!.2 < result[k]!.2)""",
         code="""((List.range lst.length).map (fun i => ((List.range lst[i]!.length).reverse.filter (fun j => (lst[i]!)[j]! == x)).map (fun j => (i, j)))).flatten""",
         size_limit=7, tags=("list", "declarative")),

    dict(id="he_088_sort_array", name="sortArray88", source="HumanEval/88",
         params=[("array", "List Nat")], ret="List Nat",
         description="Given an array of non-negative integers, return a copy of the array after sorting: in ascending order if the sum of the first and the last element is odd, in descending order if it is even.",
         post="""result.isPerm array ∧ (array ≠ [] → ((array.head! + array.getLast!) % 2 = 1 → ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧
    ((array.head! + array.getLast!) % 2 = 0 → ∀ i, i < result.length - 1 → result[i + 1]! ≤ result[i]!))""",
         code="""if array = [] then [] else
  let asc := array.mergeSort (fun a b => a ≤ b)
  if (array.head! + array.getLast!) % 2 = 1 then asc else asc.reverse""", tags=("list", "declarative")),

    dict(id="he_089_encrypt", name="encrypt", source="HumanEval/89",
         params=[("s", "String")], ret="String",
         description="Take a string and return a string encrypted with the alphabet being rotated: each lowercase letter shifts down by two multiplied by two places (four). Other characters are unchanged.",
         pre_aux="def rot4 (c : Char) : Char := if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat ((c.toNat - 97 + 4) % 26 + 97) else c",
         post="result.length = s.length ∧ ∀ i, i < s.length → result.toList[i]! = rot4 s.toList[i]!",
         code="String.mk (s.toList.map rot4)", size_limit=40, tags=("string", "declarative")),

    dict(id="he_091_is_bored", name="isBored", source="HumanEval/91",
         params=[("S", "String")], ret="Nat",
         description="You are given a string of words; count the number of boredoms. A boredom is a sentence that starts with the word \"I\". Sentences are delimited by '.', '?' or '!'.",
         post="""let sentences := (((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim
result = (sentences.filter (fun t => t.startsWith "I ")).length""",
         code="""(((((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim).filter (fun t => t.startsWith "I ")).length""",
         valid=lambda a: a[0].isascii(), size_limit=60, tags=("string", "declarative")),

    dict(id="he_092_any_int", name="anyInt", source="HumanEval/92",
         params=[("x", "PyVal"), ("y", "PyVal"), ("z", "PyVal")], ret="Bool",
         description="Take 3 numbers. Return true if one of the numbers is equal to the sum of the other two, and all numbers are integers. Return false in any other case.",
         pre_aux=PYVAL_AUX,
         post="""result = true ↔ (match x, y, z with
  | PyVal.int a, PyVal.int b, PyVal.int c => a = b + c ∨ b = a + c ∨ c = b + a
  | _, _, _ => False)""",
         code="""match x, y, z with
| PyVal.int a, PyVal.int b, PyVal.int c => a == b + c || b == a + c || c == b + a
| _, _, _ => false""", tags=("scalar", "any", "declarative")),

    dict(id="he_093_encode", name="encode93", source="HumanEval/93",
         params=[("message", "String")], ret="String",
         description="Write a function that takes a message and encodes it in such a way that it swaps the case of all letters and replaces all vowels in the message with the letter that appears 2 places ahead of that vowel in the English alphabet.",
         pre_aux="""def encChar (c : Char) : Char :=
  let d := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
  if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains d then Char.ofNat (d.toNat + 2) else d""",
         post="result.length = message.length ∧ ∀ i, i < message.length → result.toList[i]! = encChar message.toList[i]!",
         code="String.mk (message.toList.map encChar)", valid=lambda a: a[0].isascii(), size_limit=40, tags=("string", "declarative")),

    dict(id="he_094_skjkasdkd", name="skjkasdkd", source="HumanEval/94",
         params=[("lst", "List Nat")], ret="Nat",
         description="You are given a list of integers. Find the largest prime value and return the sum of its digits.",
         pre="∃ x ∈ lst, Nat.Prime x",
         post="∃ p ∈ lst, Nat.Prime p ∧ (∀ x ∈ lst, Nat.Prime x → x ≤ p) ∧ result = ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum",
         code="""let p := (lst.filter (fun x => decide (Nat.Prime x))).foldl max 0
((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum""",
         valid=lambda a: isinstance(a[0], list) and all(isinstance(x, int) and not isinstance(x, bool) and x >= 0 for x in a[0])
                         and any(_is_prime(x) for x in a[0]), int_limit=10 ** 6, tags=("list", "declarative")),

    dict(id="he_095_check_dict_case", name="checkDictCase", source="HumanEval/95",
         params=[("keys", "List PyVal")], ret="Bool",
         description="Given the keys of a dictionary, return true if all keys are strings in lower case or all keys are strings in upper case, else return false. The function returns false if the dictionary is empty.",
         pre_aux=PYVAL_AUX + """

def lowerKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isLower && !s.toList.any Char.isUpper
  | _ => false

def upperKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isUpper && !s.toList.any Char.isLower
  | _ => false""",
         post="result = true ↔ (keys ≠ [] ∧ (keys.all lowerKey = true ∨ keys.all upperKey = true))",
         code="!keys.isEmpty && (keys.all lowerKey || keys.all upperKey)",
         adapt=lambda a: [list(a[0].keys())], valid=lambda a: all(isinstance(k, str) and k.isascii() for k in a[0]),
         note="only the keys matter; they are given as Python values because the problem allows non-string keys",
         tags=("any", "declarative")),

    dict(id="he_096_count_up_to", name="countUpTo", source="HumanEval/96",
         params=[("n", "Nat")], ret="List Nat",
         description="Take a non-negative integer and return the array of the prime numbers that are less than n, in increasing order.",
         post="(∀ p ∈ result, p < n ∧ Nat.Prime p) ∧ (∀ p, p < n → Nat.Prime p → p ∈ result) ∧ ∀ i, i < result.length - 1 → result[i]! < result[i + 1]!",
         code="(List.range n).filter (fun p => decide (Nat.Prime p))", int_limit=3000, tags=("scalar", "list", "declarative")),

    dict(id="he_099_closest_integer", name="closestInteger", source="HumanEval/99",
         params=[("value", "String")], ret="Int",
         description="Take a value (a string) representing a number and return the closest integer to it. If the number is equidistant from two integers, round it away from zero.",
         pre_aux="""def parseDec (s : String) : ℚ :=
  let neg := s.startsWith "-"
  let body := if neg then String.mk (s.toList.drop 1) else s
  let parts := body.splitOn "."
  let ip := parts[0]!
  let fp := if parts.length > 1 then parts[1]! else ""
  let iv : ℚ := ((ip.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ)
  let fv : ℚ := ((fp.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ) / 10 ^ fp.length
  (if neg then -1 else 1) * (iv + fv)""",
         pre="""let body := if value.startsWith "-" then String.mk (value.toList.drop 1) else value
(body.all (fun c => c.isDigit || c == '.') && (body.toList.filter (fun c => c == '.')).length ≤ 1 && body.toList.any Char.isDigit) = true""",
         post="""let q := parseDec value
|q - (result : ℚ)| < 1 / 2 ∨ (|q - (result : ℚ)| = 1 / 2 ∧ |q| < |(result : ℚ)|)""",
         code="""let q := parseDec value
let f := ⌊q⌋
let frac := q - (f : ℚ)
if frac < 1 / 2 then f else if frac > 1 / 2 then f + 1 else (if q > 0 then f + 1 else f)""",
         valid=lambda a: _closest_ok(a), size_limit=40, tags=("string", "scalar", "float"),
         note="the string is read as the exact decimal number it denotes (the canonical solution goes through a float, which can round a long decimal)"),
]
