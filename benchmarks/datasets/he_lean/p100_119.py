r"""HumanEval problems 101-119 (those not already in ``lean_specs.py``) specified in Lean."""
from benchmarks.datasets.he_lean.p000_019 import PAREN_AUX
from benchmarks.datasets.he_lean.p060_079 import BINARY_AUX

VOWELS = "['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']"


def _ascii_no_white(a):
    return a[0].isascii() and not any(c in a[0] for c in "\t\n\r\x0b\x0c")


def _digits_only(strings):
    return all(isinstance(s, str) and s.isdigit() and s.isascii() for s in strings)


def _mixed_ok(a):
    return isinstance(a[0], list) and all(isinstance(x, int) and not isinstance(x, bool) for x in a[0])


def _sum_ok(a):
    try:
        words = [w for w in a[0].split(" ") if w != ""]
        return len(words) > 0 and a[0] != ""
    except Exception:
        return False


ENTRIES = [
    dict(id="he_101_words_string", name="wordsString", source="HumanEval/101",
         params=[("s", "String")], ret="List String",
         description="You will be given a string of words separated by commas or spaces. Split the string into words and return an array of the words.",
         post="""result = ((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")""",
         code="""((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")""",
         valid=_ascii_no_white, size_limit=40, tags=("string", "list", "declarative")),

    dict(id="he_102_choose_num", name="chooseNum", source="HumanEval/102",
         params=[("x", "Int"), ("y", "Int")], ret="Int",
         description="Take two positive numbers x and y and return the biggest even integer number that is in the range [x, y] inclusive. If there is no such number, return -1.",
         post="""(result = -1 ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 ≠ 0) ∨
  (result % 2 = 0 ∧ x ≤ result ∧ result ≤ y ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 = 0 → x + (k : Int) ≤ result)""",
         code="if x > y then -1 else if y % 2 == 0 then y else if y - 1 ≥ x then y - 1 else -1", int_limit=10 ** 5,
         tags=("scalar", "declarative")),

    dict(id="he_103_rounded_avg", name="roundedAvg", source="HumanEval/103",
         params=[("n", "Nat"), ("m", "Nat")], ret="Option String",
         description="Given two positive integers n and m, compute the average of the integers from n through m (including n and m). Round the answer to the nearest integer (half to even, as Python does) and convert that to binary. If n is greater than m, return -1 (here: none).",
         pre_aux=BINARY_AUX + """

def roundedHalfEven (s : Nat) : Nat := if s % 2 = 0 then s / 2 else (if (s / 2) % 2 = 0 then s / 2 else s / 2 + 1)""",
         post="""match result with
| none => n > m
| some b => n ≤ m ∧ b.length ≥ 3 ∧ b.toList.take 2 = ['0', 'b'] ∧ isBinary (b.toList.drop 2) (roundedHalfEven (n + m))""",
         code="""if n > m then none else
  let avg := roundedHalfEven (n + m)
  let bits := Id.run do
    let mut k := avg
    let mut acc := ""
    while k != 0 do
      acc := toString (k % 2) ++ acc
      k := k / 2
    return (if avg == 0 then "0" else acc)
  some ("0b" ++ bits)""", adapt_out=lambda o: None if o == -1 else o, int_limit=10 ** 5,
         note="Python returns -1 or a string; here -1 is none", tags=("scalar", "string", "option", "declarative")),

    dict(id="he_104_unique_digits", name="uniqueDigits", source="HumanEval/104",
         params=[("x", "List Nat")], ret="List Nat",
         description="Given a list of positive integers x, return a sorted list of all elements that hasn't any even digit. The returned list is sorted in increasing order.",
         pre_aux="def noEvenDigit (n : Nat) : Bool := (toString n).toList.all (fun c => (c.toNat - 48) % 2 == 1)",
         post="result.isPerm (x.filter noEvenDigit) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!",
         code="(x.filter noEvenDigit).mergeSort (fun a b => a ≤ b)", valid=lambda a: _mixed_ok(a) and all(v > 0 for v in a[0]),
         int_limit=10 ** 7, tags=("list", "declarative")),

    dict(id="he_105_by_length", name="byLength", source="HumanEval/105",
         params=[("arr", "List Int")], ret="List String",
         description="Given an array of integers, sort the integers that are between 1 and 9 inclusive, reverse the resulting array, and then replace each digit by its corresponding name from \"One\", \"Two\", ..., \"Nine\". Ignore any other number.",
         pre_aux="""def numName (x : Int) : String :=
  if x = 1 then "One" else if x = 2 then "Two" else if x = 3 then "Three" else if x = 4 then "Four" else if x = 5 then "Five"
  else if x = 6 then "Six" else if x = 7 then "Seven" else if x = 8 then "Eight" else "Nine"
""",
         post="""let ds := arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)
result = (ds.mergeSort (fun a b => a ≥ b)).map numName""",
         code="""((arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (fun a b => a ≥ b)).map numName""", tags=("list", "declarative")),

    dict(id="he_106_f", name="f106", source="HumanEval/106",
         params=[("n", "Nat")], ret="List Nat",
         description="Implement the function f that takes n as a parameter and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even or the sum of the numbers from 1 to i otherwise. i starts from 1.",
         post="result.length = n ∧ ∀ i, i < n → result[i]! = (if (i + 1) % 2 = 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2)",
         code="(List.range n).map (fun i => if (i + 1) % 2 == 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2)",
         int_limit=40, tags=("scalar", "list", "declarative")),

    dict(id="he_107_even_odd_palindrome", name="evenOddPalindrome", source="HumanEval/107",
         params=[("n", "Nat")], ret="Nat × Nat",
         description="Given a positive integer n, return a tuple that has the number of even and odd integer palindromes that fall within the range [1, n], inclusive.",
         pre_aux="@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse",
         pre="n ≥ 1",
         post="""result.1 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0)).length ∧
  result.2 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1)).length""",
         code="""((List.range (n + 1)).foldl (fun acc i => if 1 ≤ i && (toString i).toList == (toString i).toList.reverse && i % 2 == 0 then acc + 1 else acc) 0,
 (List.range (n + 1)).foldl (fun acc i => if 1 ≤ i && (toString i).toList == (toString i).toList.reverse && i % 2 == 1 then acc + 1 else acc) 0)""",
         valid=lambda a: a[0] >= 1, int_limit=2000, tags=("scalar", "declarative")),

    dict(id="he_108_count_nums", name="countNums", source="HumanEval/108",
         params=[("arr", "List Int")], ret="Nat",
         description="Take an array of integers and return the number of elements which have a sum of digits > 0. If a number is negative, then its first signed digit is negative: e.g. -123 has signed digits -1, 2, and 3.",
         pre_aux="""def signedDigitSum (x : Int) : Int :=
  let ds := (toString x.natAbs).toList.map (fun c => ((c.toNat - 48 : Nat) : Int))
  if x < 0 then (ds.tail).sum - ds.head! else ds.sum""",
         post="result = (arr.filter (fun x => signedDigitSum x > 0)).length",
         code="arr.foldl (fun acc x => if signedDigitSum x > 0 then acc + 1 else acc) 0", int_limit=10 ** 7,
         tags=("list", "declarative")),

    dict(id="he_109_move_one_ball", name="moveOneBall", source="HumanEval/109",
         params=[("arr", "List Int")], ret="Bool",
         description="Given an array of integers in random order, determine whether it is possible to get an array sorted in non-decreasing order by performing right shift operations any number of times (the last element moves to the start). If the given array is empty then return true.",
         post="result = true ↔ ∃ i, i < arr.length + 1 ∧ arr.drop i ++ arr.take i = arr.mergeSort (fun a b => a ≤ b)",
         code="(List.range (arr.length + 1)).any (fun i => arr.drop i ++ arr.take i == arr.mergeSort (fun a b => a ≤ b))",
         tags=("list", "declarative")),

    dict(id="he_110_exchange", name="exchange", source="HumanEval/110",
         params=[("lst1", "List Int"), ("lst2", "List Int")], ret="String",
         description="Take two lists of numbers and determine whether it is possible to perform an exchange of elements between them to make lst1 a list of only even numbers; there is no limit on the number of exchanged elements. Return \"YES\" if it is possible, otherwise \"NO\".",
         post="""(result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (lst1.filter (fun x => x % 2 = 1)).length ≤ (lst2.filter (fun x => x % 2 = 0)).length)""",
         code="""if (lst1.filter (fun x => x % 2 == 1)).length ≤ (lst2.filter (fun x => x % 2 == 0)).length then "YES" else "NO"
""",
         tags=("list", "declarative")),

    dict(id="he_111_histogram", name="histogram", source="HumanEval/111",
         params=[("test", "String")], ret="List (String × Nat)",
         description="Given a string representing space separated lowercase letters, return a dictionary of the letter with the most repetition and containing the corresponding count. If several letters have the same occurrence, return all of them. (A dictionary is a list of key-value pairs here, in any order.)",
         post="""let ws := (test.splitOn " ").filter (fun w => w != "")
(ws = [] → result = []) ∧
(ws ≠ [] → (∀ p ∈ result, p.1 ∈ ws ∧ p.2 = ws.count p.1 ∧ ∀ w ∈ ws, ws.count w ≤ p.2) ∧
  (∀ w ∈ ws, (∀ v ∈ ws, ws.count v ≤ ws.count w) → ∃ p ∈ result, p.1 = w) ∧ (result.map Prod.fst).Nodup)""",
         code="""let ws := (test.splitOn " ").filter (fun w => w != "")
let best := ws.foldl (fun m w => max m (ws.count w)) 0
(ws.eraseDups.filter (fun w => ws.count w == best)).map (fun w => (w, ws.count w))""",
         adapt_out=lambda d: list(d.items()), valid=lambda a: a[0].isascii() and (a[0] == "" or any(w != "" for w in a[0].split(" "))),
         size_limit=40, tags=("string", "list", "declarative"), permissive=True,
         note="a dictionary has no order, so a list of its pairs in another order is the same dictionary: the specification accepts it"),

    dict(id="he_112_reverse_delete", name="reverseDelete", source="HumanEval/112",
         params=[("s", "String"), ("c", "String")], ret="String × Bool",
         description="Delete all the characters in s that are equal to any character in c, then check if the result string is a palindrome. Return a tuple containing the result string and true/false for the check.",
         post="result.1.toList = s.toList.filter (fun ch => !(c.toList.contains ch)) ∧ (result.2 = true ↔ result.1.toList = result.1.toList.reverse)",
         code="""let t := s.toList.filter (fun ch => !(c.toList.contains ch))
(String.mk t, t == t.reverse)""", size_limit=30, tags=("string", "declarative")),

    dict(id="he_113_odd_count", name="oddCount", source="HumanEval/113",
         params=[("lst", "List String")], ret="List String",
         description="Given a list of strings, where each string consists of only digits, return a list. Each element i of the output is \"the number of odd elements in the string i of the input.\" where all the i's are replaced by the number of odd digits in the i'th string of the input.",
         pre_aux="""def oddDigits (s : String) : Nat := (s.toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length
def oddMsg (n : Nat) : String := "the number of odd elements in the string i of the input.".replace "i" (toString n)""",
         pre="∀ s ∈ lst, s.toList.all Char.isDigit = true",
         post="result.length = lst.length ∧ ∀ k, k < lst.length → result[k]! = oddMsg (oddDigits lst[k]!)",
         code="lst.map (fun s => oddMsg (oddDigits s))", valid=lambda a: _digits_only(a[0]), size_limit=40, tags=("list", "string", "declarative")),

    dict(id="he_115_max_fill", name="maxFill", source="HumanEval/115",
         params=[("grid", "List (List Nat)"), ("capacity", "Nat")], ret="Nat",
         description="You are given a rectangular grid of wells. Each row represents a single well, and each 1 in a row represents a single unit of water. Each well has a corresponding bucket that can be used to extract water from it, and all buckets have the same capacity. Output the number of times you need to lower the buckets to empty the wells.",
         pre="capacity ≥ 1", post="result = (grid.map (fun row => (row.sum + capacity - 1) / capacity)).sum",
         code="grid.foldl (fun acc row => acc + (row.foldl (fun a x => a + x) 0 + capacity - 1) / capacity) 0",
         valid=lambda a: a[1] >= 1, size_limit=8, tags=("list", "declarative")),

    dict(id="he_116_sort_array", name="sortArray116", source="HumanEval/116",
         params=[("arr", "List Int")], ret="List Int",
         description="Sort an array of integers according to the number of ones in their binary representation in ascending order. For a similar number of ones, sort based on decimal value. (The ones are counted in the binary representation of the absolute value, as Python's bin does.)",
         pre_aux="def ones (x : Int) : Nat := ((Nat.digits 2 x.natAbs).filter (fun d => d == 1)).length",
         post="result.isPerm arr ∧ ∀ i, i < result.length - 1 → ones result[i]! < ones result[i + 1]! ∨ (ones result[i]! = ones result[i + 1]! ∧ result[i]! ≤ result[i + 1]!)",
         code="arr.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && a ≤ b))", tags=("list", "declarative")),

    dict(id="he_117_select_words", name="selectWords", source="HumanEval/117",
         params=[("s", "String"), ("n", "Nat")], ret="List String",
         description="Given a string s and a natural number n, return a list of all words from the string s that contain exactly n consonants, in the order these words appear in the string. If the string s is empty then return an empty list. The input string contains only letters and spaces.",
         post=f"""result = (s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !({VOWELS}.contains ch))).length == n)""",
         code=f"""(s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !({VOWELS}.contains ch))).length == n)""",
         size_limit=40, tags=("string", "list", "declarative")),

    dict(id="he_118_get_closest_vowel", name="getClosestVowel", source="HumanEval/118",
         params=[("word", "String")], ret="String",
         description="Find the closest vowel that stands between two consonants from the right side of the word (case sensitive). Vowels in the beginning and ending don't count. Return the empty string if no vowel meets the above condition. The word contains English letters only.",
         pre_aux="""def isVowelC (c : Char) : Bool := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c
@[reducible, simp] def goodAt (w : List Char) (i : Nat) : Prop :=
  1 ≤ i ∧ i + 1 < w.length ∧ isVowelC w[i]! = true ∧ isVowelC w[i - 1]! = false ∧ isVowelC w[i + 1]! = false""",
         post="""let w := word.toList
(result = "" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧
(result ≠ "" → ∃ i, i < w.length ∧ goodAt w i ∧ result = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j)""",
         code="""let w := word.toList
match ((List.range w.length).reverse.find? (fun i => 1 ≤ i && i + 1 < w.length && isVowelC w[i]! && !isVowelC w[i - 1]! && !isVowelC w[i + 1]!)) with
| some i => String.singleton w[i]!
| none => ""
""", size_limit=30, tags=("string", "declarative")),

    dict(id="he_119_match_parens", name="matchParens", source="HumanEval/119",
         params=[("lst", "List String")], ret="String",
         description="You are given a list of two strings, both consisting of open parentheses '(' or close parentheses ')' only. Check if it is possible to concatenate the two strings in some order so that the resulting string is good: a string is good if and only if all its parentheses are balanced. Return 'Yes' if there is a way to make a good string, and 'No' otherwise.",
         pre_aux=PAREN_AUX,
         pre="lst.length = 2 ∧ lst.all (fun t => t.toList.all (fun c => c == '(' || c == ')')) = true",
         post="""(result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ (isBalanced (lst[0]!.toList ++ lst[1]!.toList) ∨ isBalanced (lst[1]!.toList ++ lst[0]!.toList)))""",
         code="""let a := lst[0]!.toList
let b := lst[1]!.toList
let ok := fun (l : List Char) => decide (isBalanced l)
if ok (a ++ b) || ok (b ++ a) then "Yes" else "No"
""",
         valid=lambda a: len(a[0]) == 2 and all(set(t) <= set("()") for t in a[0]), size_limit=12, tags=("string", "list", "declarative")),
]
