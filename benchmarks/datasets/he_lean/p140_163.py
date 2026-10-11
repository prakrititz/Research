r"""HumanEval problems 140-163 (those not already in ``lean_specs.py``) specified in Lean.

Same conventions as ``p000_019.py``. Where the English statement is a procedure with no simpler description (the Roman
numerals, MD5, the operator-precedence evaluation of ``do_algebra``) the specification is a small recursive definition, and the
validator checks it against all of HumanEval's and EvalPlus' data, as for every other problem.
"""
import math
import re

_FRACTION = re.compile(r"^[0-9]+/[0-9]+$")


def _fractions_ok(a):
    return all(isinstance(s, str) and _FRACTION.match(s) and int(s.split("/")[1]) > 0 for s in a[:2])


_PREC = {"**": 3, "*": 2, "//": 2, "+": 1, "-": 1}
_CAP = 10 ** 15


def _algebra_ok(a):
    """The operators are the five of the statement, no division by zero, and no intermediate value beyond 1e15
    (``2 ** 3 ** 4 ** 5`` would take minutes to evaluate in a test). The reduction order is the one of the specification."""
    ops, xs = list(a[0]), list(a[1])
    if len(ops) + 1 != len(xs) or len(xs) < 2 or any(o not in _PREC for o in ops):
        return False
    if any((not isinstance(x, int)) or isinstance(x, bool) or x < 0 or x > 10 ** 6 for x in xs):
        return False
    while ops:
        m = max(_PREC[o] for o in ops)
        idx = [i for i, o in enumerate(ops) if _PREC[o] == m]
        i = idx[-1] if m == 3 else idx[0]
        x, y, o = xs[i], xs[i + 1], ops[i]
        if o == "//":
            if y == 0:
                return False
            v = x // y
        elif o == "**":
            if y > 64 or (x > 1 and y * math.log2(x) > 52):
                return False
            v = x ** y
        elif o == "*":
            v = x * y
        elif o == "+":
            v = x + y
        else:
            v = x - y
        if abs(v) > _CAP:
            return False
        xs[i:i + 2] = [v]
        del ops[i]
    return True


# MD5 (RFC 1321), written as a recursive definition; the 64 constants are floor(2^32 * abs(sin(i + 1))).
MD5_AUX = """def md5K : Array UInt32 := #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]
def md5S : Array UInt32 := #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!
def md5Pad (msg : List UInt8) : List UInt8 :=
  let l := msg.length
  msg ++ [0x80] ++ List.replicate ((55 + 64 - l % 64) % 64) 0 ++ (List.range 8).map (fun i => UInt8.ofNat ((l * 8 / 256 ^ i) % 256))
def md5Word (blk : List UInt8) (j : Nat) : UInt32 :=
  blk[4 * j]!.toUInt32 ||| (blk[4 * j + 1]!.toUInt32 <<< 8) ||| (blk[4 * j + 2]!.toUInt32 <<< 16) ||| (blk[4 * j + 3]!.toUInt32 <<< 24)
def md5Step (m : Array UInt32) (st : UInt32 × UInt32 × UInt32 × UInt32) (i : Nat) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := st.1
  let b := st.2.1
  let c := st.2.2.1
  let d := st.2.2.2
  let fg : UInt32 × Nat :=
    if i < 16 then ((b &&& c) ||| ((~~~b) &&& d), i)
    else if i < 32 then ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
    else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
    else (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
  let f := fg.1 + a + md5K[i]! + m[fg.2]!
  let s := md5S[i]!
  (d, b + ((f <<< s) ||| (f >>> (32 - s))), b, c)
def md5Block (st : UInt32 × UInt32 × UInt32 × UInt32) (blk : List UInt8) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let m : Array UInt32 := ((List.range 16).map (md5Word blk)).toArray
  let r := (List.range 64).foldl (md5Step m) st
  (st.1 + r.1, st.2.1 + r.2.1, st.2.2.1 + r.2.2.1, st.2.2.2 + r.2.2.2)
def md5Blocks : Nat → List UInt8 → UInt32 × UInt32 × UInt32 × UInt32 → UInt32 × UInt32 × UInt32 × UInt32
  | 0, _, st => st
  | fuel + 1, bytes, st => if bytes.length < 64 then st else md5Blocks fuel (bytes.drop 64) (md5Block st (bytes.take 64))
def md5Hex (s : String) : String :=
  let bytes := md5Pad s.toUTF8.toList
  let st := md5Blocks bytes.length bytes (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  let out := [st.1, st.2.1, st.2.2.1, st.2.2.2].flatMap (fun w => (List.range 4).map (fun k => ((w >>> (8 * k).toUInt32) &&& 0xff).toNat))
  String.mk (out.flatMap (fun b => [hexDigit (b / 16), hexDigit (b % 16)]))"""


ENTRIES = [
    dict(id="he_140_fix_spaces", name="fixSpaces", source="HumanEval/140",
         params=[("text", "String")], ret="String",
         description="Given a string text, replace all spaces in it with underscores, and if a string has more than 2 consecutive spaces, then replace all consecutive spaces with a single '-'.",
         pre_aux="""def spaceRun : List Char → Nat
  | ' ' :: t => spaceRun t + 1
  | _ => 0
def fixSpec : Nat → List Char → List Char
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, c :: t =>
    if c = ' ' then
      (if spaceRun (c :: t) ≥ 3 then ['-'] else List.replicate (spaceRun (c :: t)) '_') ++ fixSpec fuel ((c :: t).drop (spaceRun (c :: t)))
    else c :: fixSpec fuel t""",
         post="result = String.mk (fixSpec text.length text.toList)",
         code="""Id.run do
  let mut out : List Char := []
  let mut run : Nat := 0
  for c in text.toList do
    if c == ' ' then
      run := run + 1
    else
      out := out ++ (if run ≥ 3 then ['-'] else List.replicate run '_') ++ [c]
      run := 0
  out := out ++ (if run ≥ 3 then ['-'] else List.replicate run '_')
  return String.mk out""",
         valid=lambda a: a[0].isascii(), size_limit=30, tags=("string", "loop", "recursive-spec"),
         note="a maximal run of spaces of length 1 or 2 becomes that many underscores, a longer one a single '-'"),

    dict(id="he_141_file_name_check", name="fileNameCheck", source="HumanEval/141",
         params=[("file_name", "String")], ret="String",
         description="Take a string representing a file's name and return \"Yes\" if the file's name is valid and \"No\" otherwise. It is valid if and only if: there are not more than three digits in the name; it contains exactly one dot; the substring before the dot is not empty and starts with a letter of the latin alphabet; the substring after the dot is one of txt, exe, dll.",
         post="""(result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧
  ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧
    (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)))""",
         code="""let parts := file_name.splitOn "."
if (file_name.toList.filter Char.isDigit).length > 3 then "No"
else if parts.length != 2 then "No"
else if parts[0]! = "" then "No"
else if !(parts[0]!.toList[0]!).isAlpha then "No"
else if parts[1]! = "txt" || parts[1]! = "exe" || parts[1]! = "dll" then "Yes" else "No\"""",
         valid=lambda a: a[0].isascii(), size_limit=24, tags=("string", "declarative")),

    dict(id="he_142_sum_squares", name="sumSquaresIdx", source="HumanEval/142",
         params=[("lst", "List Int")], ret="Int",
         description="Take a list of integers. For all entries in the list, square the entry if its index is a multiple of 3 and cube the entry if its index is a multiple of 4 and not a multiple of 3; leave the other entries unchanged. Return the sum of all entries.",
         post="result = ((List.range lst.length).map (fun i => if i % 3 = 0 then lst[i]! ^ 2 else if i % 4 = 0 then lst[i]! ^ 3 else lst[i]!)).sum",
         code="lst.zipIdx.foldl (fun acc (x, i) => if i % 3 == 0 then acc + x ^ 2 else if i % 4 == 0 then acc + x ^ 3 else acc + x) 0",
         tags=("list", "loop")),

    dict(id="he_143_words_in_sentence", name="wordsInSentence", source="HumanEval/143",
         params=[("sentence", "String")], ret="String",
         description="Given a sentence of words separated by a single space, return a string that contains the words of the original sentence whose lengths are prime numbers, in the same order, separated by a space.",
         post="""result = " ".intercalate ((sentence.splitOn " ").filter (fun w => decide (Nat.Prime w.length)))""",
         code="""" ".intercalate ((sentence.splitOn " ").filter (fun w => w.length ≥ 2 && (List.range w.length).all (fun d => d < 2 || w.length % d != 0)))""",
         valid=lambda a: a[0].isascii(), size_limit=40, tags=("string", "list", "declarative")),

    dict(id="he_144_simplify", name="simplify", source="HumanEval/144",
         params=[("x", "String"), ("n", "String")], ret="Bool",
         description="Decide whether the product x * n of two fractions, each given as a string <numerator>/<denominator> of positive whole numbers, evaluates to a whole number.",
         pre_aux="""def numOf (s : String) : Nat := (s.splitOn "/")[0]!.toNat!
def denOf (s : String) : Nat := (s.splitOn "/")[1]!.toNat!
@[reducible] def wellFormedFrac (s : String) : Prop := (s.splitOn "/").length = 2 ∧ (s.splitOn "/").all String.isNat = true ∧ 0 < denOf s""",
         pre="wellFormedFrac x ∧ wellFormedFrac n",
         post="result = true ↔ (numOf x * numOf n) % (denOf x * denOf n) = 0",
         code="decide ((numOf x * numOf n) % (denOf x * denOf n) = 0)",
         valid=_fractions_ok, size_limit=12, tags=("string", "declarative")),

    dict(id="he_145_order_by_points", name="orderByPoints", source="HumanEval/145",
         params=[("nums", "List Int")], ret="List Int",
         description="Sort the given list of integers in ascending order according to the sum of their digits (the first digit of a negative number counts as negative). If several items have the same sum of digits, order them by their index in the original list.",
         pre_aux="""def digitWeight (x : Int) : Int :=
  let ds : List Nat := (toString x.natAbs).toList.map (fun c => c.toNat - 48)
  let s : Int := (ds.map (fun d => (d : Int))).sum
  if x < 0 then s - 2 * ((ds.head! : Nat) : Int) else s""",
         post="""result.length = nums.length ∧ (∀ i, i < result.length - 1 → digitWeight result[i]! ≤ digitWeight result[i + 1]!) ∧
  ∀ x ∈ nums, result.filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)""",
         code="nums.mergeSort (fun a b => digitWeight a ≤ digitWeight b)",
         tags=("list", "declarative"),
         note="stable: for every weight the elements of that weight appear in the original order; with the same length and ordered weights this fixes the output"),

    dict(id="he_146_special_filter", name="specialFilter", source="HumanEval/146",
         params=[("nums", "List Int")], ret="Nat",
         description="Take a list of numbers and return the number of elements in the list that are greater than 10 and both the first and last digits of the number are odd (1, 3, 5, 7, 9).",
         pre_aux="""def firstDigit (n : Nat) : Nat := (toString n).toList.head!.toNat - 48""",
         post="result = (nums.filter (fun x => x > 10 ∧ firstDigit x.natAbs % 2 = 1 ∧ x.natAbs % 10 % 2 = 1)).length",
         code="nums.foldl (fun acc x => if x > 10 && firstDigit x.natAbs % 2 == 1 && x.natAbs % 10 % 2 == 1 then acc + 1 else acc) 0",
         tags=("list", "loop")),

    dict(id="he_147_get_max_triples", name="getMaxTriples", source="HumanEval/147",
         params=[("n", "Nat")], ret="Nat",
         description="Given a positive integer n, create the array a of length n with a[i] = i * i - i + 1 for 1 <= i <= n. Return the number of triples (a[i], a[j], a[k]) with i < j < k such that a[i] + a[j] + a[k] is a multiple of 3.",
         pre="n ≥ 1",
         pre_aux="""def seqA (i : Nat) : Nat := i * i - i + 1""",
         post="""result = ((List.range n).map (fun i => ((List.range n).map (fun j => ((List.range n).filter (fun k => i < j ∧ j < k ∧ (seqA (i + 1) + seqA (j + 1) + seqA (k + 1)) % 3 = 0)).length)).sum)).sum""",
         code="""if n ≤ 2 then 0 else
  let one := 1 + (n - 2) / 3 * 2 + (n - 2) % 3
  let zero := n - one
  one * (one - 1) * (one - 2) / 6 + zero * (zero - 1) * (zero - 2) / 6""",
         valid=lambda a: a[0] >= 1, adapt_out=lambda o: int(o), int_limit=40,
         tags=("scalar", "declarative"),
         note="the canonical solution returns False (= 0) for n <= 2; the reference here uses its counting formula, the specification counts the triples"),

    dict(id="he_148_bf", name="bf", source="HumanEval/148",
         params=[("planet1", "String"), ("planet2", "String")], ret="List String",
         description="There are eight planets in our solar system: Mercury, Venus, Earth, Mars, Jupiter, Saturn, Uranus, Neptune (in order of proximity to the Sun). Take two planet names and return the list of all planets whose orbits are located between the orbits of planet1 and planet2, sorted by the proximity to the sun. Return the empty list if planet1 or planet2 is not a correct planet name.",
         pre_aux="""def solarPlanets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]""",
         post="""(planet1 ∉ solarPlanets ∨ planet2 ∉ solarPlanets → result = []) ∧
  (planet1 ∈ solarPlanets → planet2 ∈ solarPlanets → ∃ i, i < 8 ∧ solarPlanets[i]! = planet1 ∧ ∃ j, j < 8 ∧ solarPlanets[j]! = planet2 ∧
    result = (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1))""",
         code="""if solarPlanets.contains planet1 && solarPlanets.contains planet2 then
  let i := solarPlanets.idxOf planet1
  let j := solarPlanets.idxOf planet2
  (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1)
else []""",
         adapt_out=lambda o: list(o), valid=lambda a: all(s.isascii() for s in a), size_limit=12, tags=("string", "list", "declarative")),

    dict(id="he_149_sorted_list_sum", name="sortedListSum", source="HumanEval/149",
         params=[("lst", "List String")], ret="List String",
         description="Accept a list of strings, delete the strings that have odd lengths from it, and return the resulting list in sorted order: ascending by the length of each word, and alphabetically among words of the same length. The list may contain duplicates.",
         post="""List.Perm result (lst.filter (fun s => s.length % 2 = 0)) ∧
  ∀ i, i < result.length - 1 → (result[i]!.length < result[i + 1]!.length ∨ (result[i]!.length = result[i + 1]!.length ∧ ¬ (result[i + 1]! < result[i]!)))""",
         code="""(lst.filter (fun s => s.length % 2 == 0)).mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))""",
         valid=lambda a: all(isinstance(s, str) and s.isascii() for s in a[0]), size_limit=8, tags=("string", "list", "declarative")),

    dict(id="he_151_double_the_difference", name="doubleTheDifference", source="HumanEval/151",
         params=[("lst", "List (Int ⊕ ℚ)")], ret="Int",
         description="Given a list of numbers (some integers, some floats), return the sum of squares of the numbers in the list that are odd. Ignore numbers that are negative or not integers (a float is not an integer even if its value is whole). An empty list gives 0.",
         post="result = (lst.map (Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0))).sum",
         code="lst.foldl (fun (acc : Int) v => match v with | Sum.inl x => if x > 0 && x % 2 == 1 then acc + x * x else acc | Sum.inr _ => acc) 0",
         valid=lambda a: all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in a[0]), int_limit=1000,
         tags=("list", "sum", "loop"),
         note="integers and floats are told apart by the sum type: the canonical solution ignores 3.0 because str(3.0) contains a dot"),

    dict(id="he_153_strongest_extension", name="strongestExtension", source="HumanEval/153",
         params=[("class_name", "String"), ("extensions", "List String")], ret="String",
         description="Given the name of a class and a list of extensions, find the strongest extension and return ClassName.StrongestExtensionName. The strength of an extension is CAP - SM, where CAP is the number of uppercase letters in its name and SM the number of lowercase letters. If several extensions have the same strength, choose the one that comes first in the list.",
         pre="extensions ≠ []",
         pre_aux="""def strength (s : String) : Int := ((s.toList.filter Char.isUpper).length : Int) - ((s.toList.filter Char.isLower).length : Int)""",
         post="""∃ i, i < extensions.length ∧ result = class_name ++ "." ++ extensions[i]! ∧
  (∀ j, j < extensions.length → strength extensions[j]! ≤ strength extensions[i]!) ∧ ∀ j, j < i → strength extensions[j]! < strength extensions[i]!""",
         code="""class_name ++ "." ++ extensions.foldl (fun (b : String) e => if strength e > strength b then e else b) extensions.head!""",
         valid=lambda a: a[0].isascii() and len(a[1]) > 0 and all(s.isascii() for s in a[1]), size_limit=8,
         tags=("string", "list", "declarative")),

    dict(id="he_154_cycpattern_check", name="cycpatternCheck", source="HumanEval/154",
         params=[("a", "String"), ("b", "String")], ret="Bool",
         description="Given two words, return true if the second word or any of its rotations is a substring of the first word.",
         post="""result = true ↔ (b.length = 0 ∨ ∃ i, i < b.length ∧ (b.toList.drop i ++ b.toList.take i) <:+: a.toList)""",
         code="""b.length == 0 || (List.range b.length).any (fun i => (a.splitOn (String.mk (b.toList.drop i ++ b.toList.take i))).length > 1)""",
         valid=lambda a: a[0].isascii() and a[1].isascii(), size_limit=24, tags=("string", "declarative")),

    dict(id="he_155_even_odd_count", name="evenOddCount", source="HumanEval/155",
         params=[("num", "Int")], ret="Nat × Nat",
         description="Given an integer, return a pair with the number of even and odd digits respectively (of its absolute value).",
         post="""result.1 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 0)).length ∧
  result.2 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length""",
         code="""(toString num.natAbs).toList.foldl (fun (p : Nat × Nat) c => if (c.toNat - 48) % 2 == 0 then (p.1 + 1, p.2) else (p.1, p.2 + 1)) (0, 0)""",
         int_limit=10 ** 12, tags=("scalar", "declarative")),

    dict(id="he_156_int_to_mini_roman", name="intToMiniRoman", source="HumanEval/156",
         params=[("number", "Nat")], ret="String",
         description="Given a positive integer between 1 and 1000, obtain its Roman numeral equivalent as a string, in lowercase.",
         pre="1 ≤ number ∧ number ≤ 1000",
         pre_aux="""def romanTable : List (Nat × String) := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
def romanSpec : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n =>
    if n = 0 then ""
    else match romanTable.find? (fun p => decide (p.1 ≤ n)) with
      | some p => p.2 ++ romanSpec fuel (n - p.1)
      | none => \"\"""",
         post="result = romanSpec number number",
         code="""let thousands := ["", "m"]
let hundreds := ["", "c", "cc", "ccc", "cd", "d", "dc", "dcc", "dccc", "cm"]
let tens := ["", "x", "xx", "xxx", "xl", "l", "lx", "lxx", "lxxx", "xc"]
let ones := ["", "i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix"]
thousands[number / 1000]! ++ hundreds[(number % 1000) / 100]! ++ tens[(number % 100) / 10]! ++ ones[number % 10]!""",
         valid=lambda a: 1 <= a[0] <= 1000, int_limit=1000, tags=("scalar", "string", "recursive-spec")),

    dict(id="he_158_find_max", name="findMax", source="HumanEval/158",
         params=[("words", "List String")], ret="String",
         description="Accept a list of strings. Return the word with the maximum number of unique characters; if several words have the maximum number of unique characters, return the one which comes first in lexicographical order. For an empty list return the empty string.",
         pre_aux="""def uniqChars (w : String) : Nat := w.toList.eraseDups.length""",
         post="""(words = [] ∧ result = "") ∨ (result ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars result) ∧ ∀ w ∈ words, uniqChars w = uniqChars result → ¬ (w < result))""",
         code="""words.foldl (fun (best : String) w => if uniqChars w > uniqChars best || (uniqChars w == uniqChars best && decide (w < best)) then w else best) \"\"""",
         valid=lambda a: all(isinstance(s, str) and s.isascii() for s in a[0]), size_limit=8, tags=("string", "list", "declarative")),

    dict(id="he_159_eat", name="eat", source="HumanEval/159",
         params=[("number", "Nat"), ("need", "Nat"), ("remaining", "Nat")], ret="List Nat",
         description="A hungry rabbit has already eaten `number` carrots and needs to eat `need` more to complete the day's meals; `remaining` carrots are in stock. Return [total number of eaten carrots after the meals, number of carrots left after the meals]. If there are not enough remaining carrots, the rabbit eats all remaining carrots but is still hungry.",
         pre="number ≤ 1000 ∧ need ≤ 1000 ∧ remaining ≤ 1000",
         post="result.length = 2 ∧ result[0]! = number + min need remaining ∧ result[1]! = remaining - min need remaining",
         code="if need ≤ remaining then [number + need, remaining - need] else [number + remaining, 0]",
         int_limit=1000, tags=("scalar", "declarative")),

    dict(id="he_160_do_algebra", name="doAlgebra", source="HumanEval/160",
         params=[("operator", "List String"), ("operand", "List Int")], ret="Int",
         description="Given a list of operators (+, -, *, // floor division, ** exponentiation) and a list of non-negative integers with one more element than the operator list, build the algebraic expression operand[0] operator[0] operand[1] ... and return its evaluation with the usual precedence (** binds tightest and associates to the right, then * and //, then + and -, which associate to the left).",
         pre="operand.length = operator.length + 1 ∧ 2 ≤ operand.length ∧ (∀ x ∈ operand, 0 ≤ x) ∧ ∀ o ∈ operator, o = \"+\" ∨ o = \"-\" ∨ o = \"*\" ∨ o = \"//\" ∨ o = \"**\"",
         pre_aux="""def opPrec (o : String) : Nat := if o = "**" then 3 else if o = "*" ∨ o = "//" then 2 else 1
def opApply (o : String) (a b : Int) : Int :=
  if o = "+" then a + b else if o = "-" then a - b else if o = "*" then a * b else if o = "//" then a / b else a ^ b.toNat
def evalOps : Nat → List Int → List String → Int
  | 0, xs, _ => xs.head!
  | fuel + 1, xs, ops =>
    if ops = [] then xs.head! else
      let m := (ops.map opPrec).foldl max 0
      let cands := (List.range ops.length).filter (fun i => opPrec ops[i]! = m)
      let i := if m = 3 then cands.getLast! else cands.head!
      evalOps fuel (xs.take i ++ [opApply ops[i]! xs[i]! xs[i + 1]!] ++ xs.drop (i + 2)) (ops.eraseIdx i)""",
         post="result = evalOps operator.length operand operator",
         code="evalOps operator.length operand operator",
         valid=_algebra_ok, size_limit=6, int_limit=10 ** 6, tags=("list", "string", "recursive-spec"),
         note="the specification reduces the highest-precedence operator first (the rightmost of the ** ones, else the leftmost); nonnegative operands make // and ** agree with Python"),

    dict(id="he_161_solve", name="solve", source="HumanEval/161",
         params=[("s", "String")], ret="String",
         description="Given a string s, if s[i] is a letter, reverse its case from lower to upper or vice versa, otherwise keep it as it is. If the string contains no letters, reverse the string. Return the resulting string.",
         pre_aux="""def swapCase (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c""",
         post="""result = (if s.toList.any Char.isAlpha then String.mk (s.toList.map swapCase) else String.mk s.toList.reverse)""",
         code="""if s.toList.any Char.isAlpha then s.map swapCase else String.mk s.toList.reverse""",
         valid=lambda a: a[0].isascii(), size_limit=30, tags=("string", "declarative")),

    dict(id="he_162_string_to_md5", name="stringToMd5", source="HumanEval/162",
         params=[("text", "String")], ret="Option String",
         description="Given a string 'text', return its md5 hash equivalent string (32 lowercase hexadecimal digits of the MD5 digest of its UTF-8 encoding). If 'text' is an empty string, return none.",
         pre_aux=MD5_AUX,
         post="(text = \"\" → result = none) ∧ (text ≠ \"\" → result = some (md5Hex text))",
         code="if text = \"\" then none else some (md5Hex text)",
         size_limit=40, tags=("string", "option", "recursive-spec"),
         note="MD5 has no description shorter than its definition; md5Hex is RFC 1321 and is checked on every test against Python's hashlib output"),

    dict(id="he_163_generate_integers", name="generateIntegers", source="HumanEval/163",
         params=[("a", "Nat"), ("b", "Nat")], ret="List Nat",
         description="Given two positive integers a and b, return the even digits (0-9) between a and b, inclusive, in ascending order.",
         post="""(∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ d ∈ result, d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b ∧ d < 10) ∧
  ∀ d, d < 10 → d % 2 = 0 → min a b ≤ d → d ≤ max a b → d ∈ result""",
         code="((List.range (min (max a b + 1) 10 - min a b)).map (fun i => i + min a b)).filter (fun d => d % 2 == 0)",
         int_limit=1000, tags=("list", "scalar", "declarative")),
]
