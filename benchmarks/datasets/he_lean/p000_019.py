r"""HumanEval problems 0-19 (those not already in ``lean_specs.py``) specified in Lean.

Floats are read as rationals (``ℚ``); a float result is specified up to ``1/1000000``, the tolerance EvalPlus itself uses.
Shared helper definitions go in ``pre_aux`` (it comes before the precondition, the code and the postcondition in a Verina file).
"""
from fractions import Fraction

TOL = "(1 / 1000000 : ℚ)"

# balanced parentheses, as a decidable proposition on a list of characters
PAREN_AUX = """@[reducible, simp] def isBalanced (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ')' ≤ (l.take k).count '(') ∧ l.count '(' = l.count ')'"""


def _balanced(text):
    depth = 0
    for c in text:
        depth += c == "("
        depth -= c == ")"
        if depth < 0:
            return False
    return depth == 0


ENTRIES = [
    dict(id="he_000_has_close_elements", name="hasCloseElements", source="HumanEval/0",
         params=[("numbers", "List ℚ"), ("threshold", "ℚ")], ret="Bool",
         description="Check if in the given list of numbers there are two numbers closer to each other than the given threshold.",
         post="result = true ↔ ∃ j, j < numbers.length ∧ ∃ i, i < j ∧ |numbers[i]! - numbers[j]!| < threshold",
         code="(List.range numbers.length).any (fun j => (List.range j).any (fun i => decide (|numbers[i]! - numbers[j]!| < threshold)))",
         tags=("list", "float", "declarative")),

    dict(id="he_001_separate_paren_groups", name="separateParenGroups", source="HumanEval/1",
         params=[("paren_string", "String")], ret="List String",
         description="The input is a string of several groups of balanced parentheses, possibly separated by spaces. Separate the groups into strings (each group is balanced and not nested within another) and return the list of them; ignore the spaces.",
         pre_aux=PAREN_AUX,
         pre="isBalanced (paren_string.toList.filter (fun c => c != ' ')) ∧ paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')",
         post="""(result.map String.toList).flatten = paren_string.toList.filter (fun c => c != ' ') ∧
  ∀ g ∈ result, g.length > 0 ∧ isBalanced g.toList ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.toList.take k)""",
         code="""Id.run do
  let mut cnt : Int := 0
  let mut group : List Char := []
  let mut results : List String := []
  for ch in paren_string.toList do
    if ch == '(' then cnt := cnt + 1
    if ch == ')' then cnt := cnt - 1
    if ch != ' ' then group := group ++ [ch]
    if cnt == 0 then
      if group != [] then results := results ++ [String.mk group]
      group := []
  return results""",
         valid=lambda a: _balanced(a[0].replace(" ", "")) and set(a[0]) <= set("() "), size_limit=40,
         tags=("string", "list", "declarative")),

    dict(id="he_002_truncate_number", name="truncateNumber", source="HumanEval/2",
         params=[("number", "ℚ")], ret="ℚ",
         description="Given a positive floating point number, it can be decomposed into an integer part (the largest integer smaller than the number) and decimals (the leftover part, always smaller than 1). Return the decimal part of the number.",
         pre="number ≥ 0", post=f"|result - (number - (⌊number⌋ : ℚ))| ≤ {TOL}",
         code="number - (⌊number⌋ : ℚ)", valid=lambda a: a[0] >= 0, tags=("float", "declarative")),

    dict(id="he_004_mean_absolute_deviation", name="meanAbsoluteDeviation", source="HumanEval/4",
         params=[("numbers", "List ℚ")], ret="ℚ",
         description="For a given list of input numbers, calculate the Mean Absolute Deviation around the mean of the dataset: the average absolute difference between each element and the mean.",
         pre="numbers ≠ []",
         post=f"|result - (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℚ)|)).sum / (numbers.length : ℚ)| ≤ {TOL}",
         code="(numbers.map (fun x => |x - numbers.sum / (numbers.length : ℚ)|)).sum / (numbers.length : ℚ)",
         valid=lambda a: len(a[0]) > 0, tags=("list", "float")),

    dict(id="he_005_intersperse", name="intersperse", source="HumanEval/5",
         params=[("numbers", "List Int"), ("delimeter", "Int")], ret="List Int",
         description="Insert the number `delimeter` between every two consecutive elements of the input list `numbers`.",
         post="""result.length = (if numbers.length = 0 then 0 else 2 * numbers.length - 1) ∧
  (∀ i, i < numbers.length → result[2 * i]! = numbers[i]!) ∧
  (∀ i, i < numbers.length - 1 → result[2 * i + 1]! = delimeter)""",
         code="numbers.intersperse delimeter", tags=("list", "declarative")),

    dict(id="he_006_parse_nested_parens", name="parseNestedParens", source="HumanEval/6",
         params=[("paren_string", "String")], ret="List Nat",
         description="The input is a string of groups of nested parentheses separated by spaces. For each group, output the deepest level of nesting of parentheses. For example (()()) has maximum two levels of nesting while ((())) has three.",
         pre_aux="""def maxDepth (l : List Char) : Nat :=
  (((List.range (l.length + 1)).map (fun k => ((l.take k).count '(' : Int) - ((l.take k).count ')' : Int))).foldl max 0).toNat""",
         pre="paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')",
         post="""let groups := (paren_string.splitOn " ").filter (fun g => g != "")
result.length = groups.length ∧ ∀ i, i < groups.length → result[i]! = maxDepth groups[i]!.toList""",
         code="""((paren_string.splitOn " ").filter (fun g => g != "")).map (fun g => maxDepth g.toList)""",
         valid=lambda a: _balanced(a[0].replace(" ", "")) and set(a[0]) <= set("() "), size_limit=40,
         tags=("string", "list", "declarative")),

    dict(id="he_007_filter_by_substring", name="filterBySubstring", source="HumanEval/7",
         params=[("strings", "List String"), ("substring", "String")], ret="List String",
         description="Filter an input list of strings, keeping only the ones that contain the given substring.",
         pre_aux="""@[reducible, simp] def hasSub (s t : String) : Prop :=
  ∃ i, i ≤ s.length ∧ t.toList = (s.toList.drop i).take t.length""",
         post="result = strings.filter (fun s => decide (hasSub s substring))",
         code="strings.foldr (fun s acc => if (List.range (s.length + 1)).any (fun i => substring.toList.isPrefixOf (s.toList.drop i)) then s :: acc else acc) []",
         size_limit=8, tags=("string", "list", "declarative")),

    dict(id="he_008_sum_product", name="sumProduct", source="HumanEval/8",
         params=[("numbers", "List Int")], ret="Int × Int",
         description="For a given list of integers, return a tuple consisting of the sum and the product of all the integers in the list. The empty sum is 0 and the empty product is 1.",
         post="result.1 = numbers.sum ∧ result.2 = numbers.prod",
         code="(numbers.foldl (fun a x => a + x) 0, numbers.foldl (fun a x => a * x) 1)", tags=("list", "declarative")),

    dict(id="he_009_rolling_max", name="rollingMax", source="HumanEval/9",
         params=[("numbers", "List Int")], ret="List Int",
         description="From a given list of integers, generate the list of the rolling maximum element found until the given moment in the sequence.",
         post="""result.length = numbers.length ∧
  ∀ i, i < numbers.length → result[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ result[i]!""",
         code="(List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)", tags=("list", "declarative")),

    dict(id="he_010_make_palindrome", name="makePalindrome", source="HumanEval/10",
         params=[("string", "String")], ret="String",
         description="Find the shortest palindrome that begins with the supplied string: find the longest postfix of the string that is a palindrome, and append to the end of the string the reverse of the prefix that comes before the palindromic suffix.",
         pre_aux="@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse",
         post="""∃ i, i ≤ string.length ∧ isPal (string.toList.drop i) ∧ (∀ j, j < i → ¬ isPal (string.toList.drop j)) ∧
    result.toList = string.toList ++ (string.toList.take i).reverse""",
         code="""let l := string.toList
let i := ((List.range (l.length + 1)).find? (fun i => l.drop i == (l.drop i).reverse)).getD 0
String.mk (l ++ (l.take i).reverse)""", size_limit=12, tags=("string", "declarative")),

    dict(id="he_011_string_xor", name="stringXor", source="HumanEval/11",
         params=[("a", "String"), ("b", "String")], ret="String",
         description="The inputs are two strings a and b consisting only of 1s and 0s. Perform binary XOR on these inputs and return the result also as a string.",
         pre="a.length = b.length ∧ a.toList.all (fun c => c == '0' || c == '1') ∧ b.toList.all (fun c => c == '0' || c == '1')",
         post="result.length = a.length ∧ ∀ i, i < a.length → result.toList[i]! = (if a.toList[i]! = b.toList[i]! then '0' else '1')",
         code="String.mk ((a.toList.zip b.toList).map (fun p => if p.1 = p.2 then '0' else '1'))",
         valid=lambda x: len(x[0]) == len(x[1]) and set(x[0] + x[1]) <= set("01"), size_limit=30, tags=("string", "declarative")),

    dict(id="he_012_longest", name="longest", source="HumanEval/12",
         params=[("strings", "List String")], ret="Option String",
         description="Out of a list of strings, return the longest one. Return the first one in case of multiple strings of the same length. Return none in case the input list is empty.",
         post="""match result with
  | none => strings = []
  | some s => ∃ i, i < strings.length ∧ strings[i]! = s ∧ (∀ t ∈ strings, t.length ≤ s.length) ∧
      ∀ j, j < i → strings[j]!.length < s.length""",
         code="""strings.foldl (fun acc s => match acc with
  | none => some s
  | some b => if s.length > b.length then some s else some b) none""", size_limit=8, tags=("list", "string", "option", "declarative")),

    dict(id="he_014_all_prefixes", name="allPrefixes", source="HumanEval/14",
         params=[("string", "String")], ret="List String",
         description="Return the list of all prefixes of the input string, from shortest to longest.",
         post="result.length = string.length ∧ ∀ i, i < string.length → result[i]! = String.mk (string.toList.take (i + 1))",
         code="(List.range string.length).map (fun i => String.mk (string.toList.take (i + 1)))", size_limit=14, tags=("string", "list", "declarative")),

    dict(id="he_015_string_sequence", name="stringSequence", source="HumanEval/15",
         params=[("n", "Nat")], ret="String",
         description="Return a string containing the space-delimited numbers starting from 0 up to n inclusive.",
         post="result.splitOn \" \" = (List.range (n + 1)).map (fun i => toString i)",
         code="\" \".intercalate ((List.range (n + 1)).map (fun i => toString i))", int_limit=200, tags=("string", "declarative")),

    dict(id="he_017_parse_music", name="parseMusic", source="HumanEval/17",
         params=[("music_string", "String")], ret="List Nat",
         description="The input is a string representing musical notes in a special ASCII format. Return the list of integers corresponding to how many beats each note lasts. Legend: 'o' is a whole note (four beats), 'o|' a half note (two beats), '.|' a quarter note (one beat).",
         pre="music_string = \"\" ∨ ∀ n ∈ music_string.splitOn \" \", n = \"o\" ∨ n = \"o|\" ∨ n = \".|\"",
         post="""let notes := if music_string = "" then [] else music_string.splitOn " "
result.length = notes.length ∧ ∀ i, i < notes.length → result[i]! = (if notes[i]! = "o" then 4 else if notes[i]! = "o|" then 2 else 1)""",
         code="""((if music_string = "" then [] else music_string.splitOn " ")).map (fun n => if n = "o" then 4 else if n = "o|" then 2 else 1)""",
         valid=lambda a: a[0] == "" or all(t in ("o", "o|", ".|") for t in a[0].split(" ")), size_limit=40, tags=("string", "list", "declarative")),

    dict(id="he_018_how_many_times", name="howManyTimes", source="HumanEval/18",
         params=[("string", "String"), ("substring", "String")], ret="Nat",
         description="Find how many times a given substring can be found in the original string. Count overlapping cases.",
         post="result = ((List.range string.length).filter (fun i => substring.toList.isPrefixOf (string.toList.drop i))).length",
         code="""(List.range string.length).foldl (fun acc i => if substring.toList.isPrefixOf (string.toList.drop i) then acc + 1 else acc) 0""",
         size_limit=30, tags=("string", "declarative")),

    dict(id="he_019_sort_numbers", name="sortNumbers", source="HumanEval/19",
         params=[("numbers", "String")], ret="String",
         description="The input is a space-delimited string of numerals from 'zero' to 'nine'. Return the string with the numerals sorted from smallest to largest.",
         pre_aux="""def numeralNames : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]
def numeralValue (t : String) : Nat := numeralNames.idxOf t""",
         pre="numbers = \"\" ∨ ∀ t ∈ numbers.splitOn \" \", t ∈ numeralNames",
         post="""let toks := if numbers = "" then [] else numbers.splitOn " "
let sorted := if result = "" then [] else result.splitOn " "
sorted.isPerm toks ∧ ∀ i, i < sorted.length - 1 → numeralValue sorted[i]! ≤ numeralValue sorted[i + 1]!""",
         code="""\" \".intercalate (((if numbers = "" then [] else numbers.splitOn " ")).mergeSort (fun a b => numeralValue a ≤ numeralValue b))""",
         valid=lambda a: a[0] == "" or all(t in "zero one two three four five six seven eight nine".split() for t in a[0].split(" ")),
         size_limit=40, tags=("string", "list", "declarative")),
]
