r"""A library of programming tasks specified in Lean, in Verina's file format (``benchmarks/datasets/lean_specs/<id>/``).

The earlier specification language (``he_specs.py``) can state a HumanEval problem only if its inputs are numbers and its
result is a number or a boolean: about 20 of the 164. Lean states the rest: lists, strings, options, quantifiers over
indices and members. This module holds the Lean specifications, written from the problems' English descriptions, and
checks every one the way the earlier library was checked (Reading Material/16):

* **compiles** with its reference implementation;
* the **reference implementation passes every test** (tests are HumanEval's own inputs plus a spread of EvalPlus' extra
  inputs, with the expected outputs of HumanEval's canonical solution: the reference is not trusted, the data is);
* the **postcondition accepts the expected output** of every test (``decide``): a specification that rejects the
  canonical solution's output is wrong;
* the **postcondition rejects every wrong output** (``unexpected`` values built by mutating the expected one): a
  specification that accepts them is too weak to guide a derivation.

    python benchmarks/datasets/lean_specs.py build       # write benchmarks/datasets/lean_specs/<id>/
    python benchmarks/datasets/lean_specs.py validate    # Lean checks above -> benchmarks/results/lean_specs/validation.json
    python benchmarks/datasets/lean_specs.py list

A specification states *what*, the reference implementation is only there to test it: the refinement engine never sees it.
Quantifiers are written in the shape Lean can decide (``∀ i, i < n → …``, ``∃ j, j < n ∧ …``) so that a test can run them.
"""
import argparse
import copy
import json
import os
import sys
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
LIBRARY = os.path.join(ROOT, "benchmarks", "datasets", "lean_specs")
RESULTS = os.path.join(ROOT, "benchmarks", "results", "lean_specs")


# --- converting Python values to Lean literals (see lean_literals.py) -----------------------------------------------

from benchmarks.datasets.lean_literals import expected_json, lean_literal, literal, mutants, parse_type  # noqa: E402,F401


# --- the table of specifications ----------------------------------------------------------------------------------

@dataclass
class Spec:
    id: str
    name: str
    source: str                                  # "HumanEval/3" or "original"
    params: List[Tuple[str, str]]
    ret: str
    description: str
    post: str
    code: str
    pre: str = "True"
    pre_aux: str = ""
    post_aux: str = ""
    code_aux: str = ""
    int_limit: int = 10 ** 4                     # keep test inputs small enough to evaluate the specification quickly
    size_limit: int = 14                         # longest list / string used in a test
    adapt: Optional[Callable[[list], list]] = None       # HumanEval's arguments -> the Lean parameters (e.g. a dict -> its items)
    adapt_out: Optional[Callable[[Any], Any]] = None     # HumanEval's result -> the Lean result
    valid: Optional[Callable[[list], bool]] = None       # the precondition on Python values: inputs that violate it are not tests
    reference_mode: str = "equal"                        # "equal": the reference gives the expected output; "spec": its output satisfies the postcondition
    permissive: bool = False                             # the specification accepts several right answers, so a "wrong" output may be right
    exact_floats: bool = False                           # read Python floats as their exact binary value (default: as written, 0.1 = 1/10)
    plus: int = 8                                        # how many EvalPlus inputs to add to HumanEval's own
    per_total: int = 16                                  # at most this many tests
    note: str = ""
    tags: Tuple[str, ...] = ()
    tests: Optional[List[dict]] = None           # hand-written test.json entries (specifications that are not HumanEval's)


SPECS: List[Spec] = []


def add(**kwargs):
    SPECS.append(Spec(**kwargs))


add(id="he_003_below_zero", name="belowZero", source="HumanEval/3", params=[("operations", "List Int")], ret="Bool",
    description="""A bank account starts with balance zero. Given the list of deposit (positive) and withdrawal (negative) operations, decide whether the balance falls below zero at some point.""",
    post="result = true ↔ ∃ k, k ≤ operations.length ∧ (operations.take k).sum < 0",
    code="""Id.run do
  let mut balance : Int := 0
  for x in operations do
    balance := balance + x
    if balance < 0 then
      return true
  return false""", tags=("list", "loop"))

add(id="he_013_gcd", name="greatestCommonDivisor", source="HumanEval/13", params=[("a", "Nat"), ("b", "Nat")], ret="Nat",
    description="""Return the greatest common divisor of two positive integers a and b.""",
    pre="a > 0 ∧ b > 0",
    post="result > 0 ∧ a % result = 0 ∧ b % result = 0 ∧ ∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ result",
    code="Nat.gcd a b", tags=("scalar", "loop"))

add(id="he_016_count_distinct", name="countDistinctCharacters", source="HumanEval/16", params=[("s", "String")], ret="Nat",
    description="""Count how many distinct characters (ignoring case) a string contains.""",
    post="result = (s.toLower.toList.eraseDups).length",
    code="""(s.toLower.toList.foldl (fun acc c => if c ∈ acc then acc else c :: acc) []).length""",
    size_limit=40, tags=("string",))

add(id="he_023_strlen", name="strlen", source="HumanEval/23", params=[("s", "String")], ret="Nat",
    description="""Return the length of a string.""",
    post="result = s.length", code="s.toList.length", size_limit=40, tags=("string", "term"))

add(id="he_024_largest_divisor", name="largestDivisor", source="HumanEval/24", params=[("n", "Nat")], ret="Nat",
    description="""For a given number n greater than 1, find the largest number that divides n evenly and is smaller than n.""",
    pre="n > 1",
    post="result > 0 ∧ result < n ∧ n % result = 0 ∧ ∀ d, d < n → result < d → n % d ≠ 0",
    code="((List.range n).filter (fun d => d > 0 && n % d == 0)).getLast?.getD 1", tags=("scalar", "loop"))

add(id="he_028_concatenate", name="concatenate", source="HumanEval/28", params=[("strings", "List String")], ret="String",
    description="""Concatenate a list of strings into a single string.""",
    post="result = String.join strings",
    code="strings.foldl (fun acc s => acc ++ s) \"\"", size_limit=8, tags=("string", "list", "loop"))

add(id="he_029_filter_by_prefix", name="filterByPrefix", source="HumanEval/29",
    params=[("strings", "List String"), ("prefix_", "String")], ret="List String",
    description="""Keep only the strings of the list that start with the given prefix, in their original order.""",
    post="result = strings.filter (fun s => s.startsWith prefix_)",
    code="strings.foldr (fun s acc => if s.startsWith prefix_ then s :: acc else acc) []", size_limit=8,
    tags=("string", "list", "loop"))

add(id="he_030_get_positive", name="getPositive", source="HumanEval/30", params=[("l", "List Int")], ret="List Int",
    description="""Return only the positive numbers of the list, in their original order.""",
    post="result = l.filter (fun x => x > 0)",
    code="l.foldr (fun x acc => if x > 0 then x :: acc else acc) []", tags=("list", "loop"))

add(id="he_031_is_prime", name="isPrime", source="HumanEval/31", params=[("n", "Nat")], ret="Bool",
    description="""Decide whether a number is prime: greater than 1 and not divisible by any smaller number greater than 1.""",
    post="result = true ↔ (n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0)",
    code="""if n < 2 then false else (List.range n).all (fun d => d < 2 || n % d != 0)""", int_limit=300000,
    tags=("scalar", "loop"))

add(id="he_034_unique", name="unique", source="HumanEval/34", params=[("l", "List Int")], ret="List Int",
    description="""Return the sorted unique elements of a list.""",
    post="(∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l) ∧ (∀ x ∈ l, x ∈ result)",
    code="(l.eraseDups).mergeSort (fun a b => a ≤ b)", tags=("list",))

add(id="he_035_max_element", name="maxElement", source="HumanEval/35", params=[("l", "List Int")], ret="Int",
    description="""Return the maximum element of a non-empty list.""",
    pre="l ≠ []", post="result ∈ l ∧ ∀ x ∈ l, x ≤ result",
    code="l.foldl max l.head!", tags=("list", "loop"))

add(id="he_041_car_race_collision", name="carRaceCollision", source="HumanEval/41", params=[("n", "Nat")], ret="Nat",
    description="""n cars drive left to right and n other cars drive right to left on an infinite straight road; all move at the same speed and start far apart. A collision is when a left-to-right car hits a right-to-left car (they pass through each other and go on). Return the number of collisions.""",
    post="result = n * n", code="n * n", int_limit=1000, tags=("scalar", "term"))

add(id="he_042_incr_list", name="incrList", source="HumanEval/42", params=[("l", "List Int")], ret="List Int",
    description="""Return the list with every element increased by one.""",
    post="result.length = l.length ∧ ∀ i, i < l.length → result[i]! = l[i]! + 1",
    code="l.map (fun x => x + 1)", tags=("list",))

add(id="he_043_pairs_sum_to_zero", name="pairsSumToZero", source="HumanEval/43", params=[("l", "List Int")], ret="Bool",
    description="""Decide whether the list has two distinct elements (at different positions) that sum to zero.""",
    post="result = true ↔ ∃ j, j < l.length ∧ ∃ i, i < j ∧ l[i]! + l[j]! = 0",
    code="(List.range l.length).any (fun j => (List.range j).any (fun i => l[i]! + l[j]! == 0))",
    tags=("list", "loop"))

add(id="he_048_is_palindrome", name="isPalindrome", source="HumanEval/48", params=[("text", "String")], ret="Bool",
    description="""Decide whether a string reads the same forwards and backwards.""",
    post="result = true ↔ ∀ i, i < text.length → text.toList[i]! = text.toList[text.length - 1 - i]!",
    code="text.toList == text.toList.reverse", size_limit=40, tags=("string",))

add(id="he_052_below_threshold", name="belowThreshold", source="HumanEval/52", params=[("l", "List Int"), ("t", "Int")], ret="Bool",
    description="""Decide whether all numbers of the list are below the threshold t.""",
    post="result = true ↔ ∀ x ∈ l, x < t", code="l.all (fun x => x < t)", tags=("list", "loop"))

add(id="he_055_fib", name="fib", source="HumanEval/55", params=[("n", "Nat")], ret="Nat",
    description="""Return the n-th Fibonacci number (fib 0 = 0, fib 1 = 1).""",
    post="result = fibSpec n",
    post_aux="""@[simp] def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibSpec n + fibSpec (n + 1)""",
    code="""Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    (a, b) := (b, a + b)
  return a""", int_limit=24, tags=("scalar", "loop", "recursive-spec"))

add(id="he_057_monotonic", name="monotonic", source="HumanEval/57", params=[("l", "List Int")], ret="Bool",
    description="""Decide whether the elements of the list are monotonically increasing or monotonically decreasing.""",
    post="result = true ↔ ((∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) ∨ (∀ i, i < l.length - 1 → l[i]! ≥ l[i + 1]!))",
    code="""(List.range (l.length - 1)).all (fun i => l[i]! ≤ l[i + 1]!) || (List.range (l.length - 1)).all (fun i => l[i]! ≥ l[i + 1]!)""",
    tags=("list", "loop"))

add(id="he_058_common", name="common", source="HumanEval/58", params=[("l1", "List Int"), ("l2", "List Int")], ret="List Int",
    description="""Return the sorted unique elements that are common to the two lists.""",
    post="(∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l1 ∧ x ∈ l2) ∧ (∀ x ∈ l1, x ∈ l2 → x ∈ result)",
    code="((l1.filter (fun x => x ∈ l2)).eraseDups).mergeSort (fun a b => a ≤ b)", tags=("list",))

add(id="he_060_sum_to_n", name="sumToN", source="HumanEval/60", params=[("n", "Nat")], ret="Nat",
    description="""Return the sum of the numbers from 1 to n.""",
    post="2 * result = n * (n + 1)", code="(List.range (n + 1)).sum", int_limit=3000, tags=("scalar", "loop"))

add(id="he_061_correct_bracketing", name="correctBracketing", source="HumanEval/61", params=[("brackets", "String")], ret="Bool",
    description="""The string consists of '(' and ')'. Decide whether every opening bracket has a corresponding closing bracket (the brackets are balanced).""",
    post="result = true ↔ ((∀ k, k ≤ brackets.length → (brackets.toList.take k).count '(' ≥ (brackets.toList.take k).count ')') ∧ brackets.toList.count '(' = brackets.toList.count ')')",
    code="""Id.run do
  let mut depth : Int := 0
  for c in brackets.toList do
    if c == '(' then depth := depth + 1
    else if c == ')' then depth := depth - 1
    if depth < 0 then return false
  return depth == 0""", size_limit=30, tags=("string", "loop"))

add(id="he_062_derivative", name="derivative", source="HumanEval/62", params=[("xs", "List Int")], ret="List Int",
    description="""xs holds the coefficients of a polynomial xs[0] + xs[1] * x + xs[2] * x^2 + ... Return the coefficients of its derivative in the same form.""",
    post="result.length = xs.length - 1 ∧ ∀ i, i < xs.length - 1 → result[i]! = xs[i + 1]! * ((i : Int) + 1)",
    code="(xs.zipIdx.map (fun (x, i) => x * (i : Int))).drop 1", tags=("list",))

add(id="he_066_digit_sum", name="digitSum", source="HumanEval/66", params=[("s", "String")], ret="Nat",
    description="""Return the sum of the ASCII codes of the upper-case characters of the string only.""",
    post="result = ((s.toList.filter Char.isUpper).map Char.toNat).sum",
    code="s.foldl (fun acc c => if c.isUpper then acc + c.toNat else acc) 0", size_limit=40, tags=("string", "loop"))

add(id="he_072_will_it_fly", name="willItFly", source="HumanEval/72", params=[("q", "List Int"), ("w", "Int")], ret="Bool",
    description="""Decide whether the object q will fly: it is balanced (the list is a palindrome) and the sum of its elements is at most the maximum possible weight w.""",
    post="result = true ↔ ((∀ i, i < q.length → q[i]! = q[q.length - 1 - i]!) ∧ q.sum ≤ w)",
    code="q.reverse == q && decide (q.sum ≤ w)", tags=("list",))

add(id="he_085_add_even_at_odd", name="addEvenAtOdd", source="HumanEval/85", params=[("lst", "List Int")], ret="Int",
    description="""Given a non-empty list of integers, add the even elements that are at odd indices.""",
    pre="lst ≠ []",
    post="result = (((List.range lst.length).filter (fun i => i % 2 = 1 ∧ lst[i]! % 2 = 0)).map (fun i => lst[i]!)).sum",
    code="lst.zipIdx.foldl (fun acc (x, i) => if i % 2 == 1 && x % 2 == 0 then acc + x else acc) 0", tags=("list", "loop"))

add(id="he_090_next_smallest", name="nextSmallest", source="HumanEval/90", params=[("lst", "List Int")], ret="Option Int",
    description="""Return the 2nd smallest distinct element of the list, or none if there is no such element.""",
    post="""match result with
| none => ∀ x ∈ lst, ∀ y ∈ lst, x = y
| some r => r ∈ lst ∧ (∃ m ∈ lst, m < r) ∧ ∀ x ∈ lst, (∃ m ∈ lst, m < x) → r ≤ x""",
    code="(lst.eraseDups.mergeSort (fun a b => a ≤ b))[1]?", tags=("list", "option"))

add(id="he_097_multiply", name="multiply", source="HumanEval/97", params=[("a", "Int"), ("b", "Int")], ret="Int",
    description="""Complete the function that takes two integers and returns the product of their unit digits.""",
    post="result = ((a.natAbs % 10 : Nat) : Int) * ((b.natAbs % 10 : Nat) : Int)",
    code="((a.natAbs % 10 : Nat) : Int) * ((b.natAbs % 10 : Nat) : Int)", int_limit=100000, tags=("scalar", "term"),
    note="the unit digit is taken of the absolute value (EvalPlus' expected outputs), not Python's % on a negative number")

add(id="he_098_count_upper", name="countUpper", source="HumanEval/98", params=[("s", "String")], ret="Nat",
    description="""Given a string s, count the number of uppercase vowels (A, E, I, O, U) at even indices.""",
    post="result = ((List.range s.length).filter (fun i => i % 2 = 0 ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'])).length",
    code="s.toList.zipIdx.foldl (fun acc (c, i) => if i % 2 == 0 && (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U') then acc + 1 else acc) 0",
    size_limit=40, tags=("string", "loop"))

add(id="he_100_make_a_pile", name="makeAPile", source="HumanEval/100", params=[("n", "Nat")], ret="List Nat",
    description="""Given a positive integer n, make a pile of n levels of stones: the first level has n stones and each next level has the next odd (if n is odd) or even (if n is even) number. Return the number of stones in each level, in a list.""",
    pre="n > 0", post="result.length = n ∧ ∀ i, i < n → result[i]! = n + 2 * i",
    code="(List.range n).map (fun i => n + 2 * i)", int_limit=200, tags=("list",))

add(id="he_121_solution", name="solution", source="HumanEval/121", params=[("lst", "List Int")], ret="Int",
    description="""Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.""",
    pre="lst ≠ []",
    post="result = (((List.range lst.length).filter (fun i => i % 2 = 0 ∧ lst[i]! % 2 = 1)).map (fun i => lst[i]!)).sum",
    code="lst.zipIdx.foldl (fun acc (x, i) => if i % 2 == 0 && x % 2 == 1 then acc + x else acc) 0", tags=("list", "loop"))

add(id="he_126_is_sorted", name="isSorted", source="HumanEval/126", params=[("lst", "List Int")], ret="Bool",
    description="""Given a list of integers, decide whether they are sorted in ascending order; if the list has more than one duplicate of the same number (the number occurs three or more times), return false.""",
    pre="∀ x ∈ lst, x ≥ 0",
    post="result = true ↔ ((∀ i, i < lst.length - 1 → lst[i]! ≤ lst[i + 1]!) ∧ ∀ x ∈ lst, lst.count x ≤ 2)",
    code="(List.range (lst.length - 1)).all (fun i => lst[i]! ≤ lst[i + 1]!) && lst.all (fun x => lst.count x ≤ 2)",
    tags=("list",))

add(id="he_138_is_equal_to_sum_even", name="isEqualToSumEven", source="HumanEval/138", params=[("n", "Nat")], ret="Bool",
    description="""Decide whether the number n can be written as the sum of exactly 4 positive even numbers.""",
    post="result = true ↔ (n ≥ 8 ∧ n % 2 = 0)", code="n ≥ 8 && n % 2 == 0", tags=("scalar", "term"))

add(id="he_139_special_factorial", name="specialFactorial", source="HumanEval/139", params=[("n", "Nat")], ret="Nat",
    description="""The Brazilian factorial of n > 0 is n! * (n-1)! * (n-2)! * ... * 1!. Return it.""",
    pre="n > 0", post="result = ((List.range n).map (fun i => factSpec (i + 1))).prod",
    post_aux="""@[simp] def factSpec : Nat → Nat
  | 0 => 1
  | (n + 1) => (n + 1) * factSpec n""",
    code="""Id.run do
  let mut fact := 1
  let mut total := 1
  for i in [1:n + 1] do
    fact := fact * i
    total := total * fact
  return total""", int_limit=20, tags=("scalar", "loop", "recursive-spec"))

add(id="he_150_x_or_y", name="xOrY", source="HumanEval/150", params=[("n", "Nat"), ("x", "Int"), ("y", "Int")], ret="Int",
    description="""Return the value of x if n is a prime number and the value of y otherwise.""",
    post="(primeSpec n → result = x) ∧ (¬ primeSpec n → result = y)",
    post_aux="""@[reducible, simp] def primeSpec (n : Nat) : Prop := n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0""",
    code="if n ≥ 2 && (List.range n).all (fun d => d < 2 || n % d != 0) then x else y", int_limit=2000,
    tags=("scalar", "loop"))

add(id="he_152_compare", name="compareGuess", source="HumanEval/152", params=[("game", "List Int"), ("guess", "List Int")], ret="List Int",
    description="""For each match, return how far off the guess was: the absolute difference between the score and the guess at the same position (0 if the guess is right).""",
    pre="game.length = guess.length",
    post="result.length = game.length ∧ ∀ i, i < game.length → result[i]! = ((game[i]! - guess[i]!).natAbs : Int)",
    code="(game.zip guess).map (fun (g, s) => ((g - s).natAbs : Int))", tags=("list",))

add(id="he_157_right_angle_triangle", name="rightAngleTriangle", source="HumanEval/157",
    params=[("a", "Nat"), ("b", "Nat"), ("c", "Nat")], ret="Bool",
    description="""Given the lengths of the three sides of a triangle, decide whether the three sides form a right-angled triangle.""",
    post="result = true ↔ (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a)",
    code="a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a", int_limit=1000, tags=("scalar", "term"))

add(id="he_114_min_sub_array_sum", name="minSubArraySum", source="HumanEval/114", params=[("nums", "List Int")], ret="Int",
    description="""Given a non-empty list of integers, find the minimum sum of any non-empty contiguous sub-list.""",
    pre="nums ≠ []",
    post="(∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = result) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → result ≤ ((nums.drop i).take (j - i)).sum",
    code="""Id.run do
  let mut best := nums.head!
  let mut current : Int := 0
  for x in nums do
    current := min x (current + x)
    best := min best current
  return best""", size_limit=10, tags=("list", "loop"))


# --- classic algorithms (not HumanEval): hand-written tests --------------------------------------------------------------

def _case(inputs, expected, *wrong):
    return {"input": inputs, "expected": expected, "unexpected": [w for w in wrong if w != expected]}


add(id="classic_isqrt", name="isqrt", source="original", params=[("n", "Nat")], ret="Nat",
    description="""Return the integer square root of n: the largest r with r * r <= n.""",
    post="result * result ≤ n ∧ n < (result + 1) * (result + 1)", code="Nat.sqrt n", tags=("scalar", "loop", "classic"),
    tests=[_case({"n": str(n)}, int(n ** 0.5) if n < 10 ** 12 else 0, int(n ** 0.5) + 1, max(0, int(n ** 0.5) - 1))
           for n in (0, 1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17, 24, 25, 26, 99, 100, 101, 9999, 10000, 10001, 999999, 1000000)])

add(id="classic_sqrt_approx", name="sqrtApprox", source="original", params=[("N", "ℚ"), ("e", "ℚ")], ret="ℚ",
    description="""The example of the Refine4LLM paper: given N >= 0 and a precision e > 0, return x >= 0 with x * x <= N < (x + e) * (x + e).""",
    pre="N ≥ 0 ∧ e > 0",
    post="result ≥ 0 ∧ result * result ≤ N ∧ N < (result + e) * (result + e)",
    code="""Id.run do
  let mut x : ℚ := 0
  while (x + e) * (x + e) ≤ N do
    x := x + e
  return x""", tags=("scalar", "loop", "classic", "paper"),
    note="the paper's flagship example, over the rationals so that it can be executed; the paper has it over the reals",
    tests=[_case({"N": "(2 : ℚ)", "e": "(1 / 10 : ℚ)"}, "(7 / 5 : ℚ)", "(3 / 2 : ℚ)", "(13 / 10 : ℚ)"),
           _case({"N": "(2 : ℚ)", "e": "(1 / 100 : ℚ)"}, "(141 / 100 : ℚ)", "(142 / 100 : ℚ)", "(1 : ℚ)"),
           _case({"N": "(0 : ℚ)", "e": "(1 : ℚ)"}, "(0 : ℚ)", "(1 : ℚ)"),
           _case({"N": "(9 : ℚ)", "e": "(1 : ℚ)"}, "(3 : ℚ)", "(2 : ℚ)", "(4 : ℚ)"),
           _case({"N": "(10 : ℚ)", "e": "(1 / 2 : ℚ)"}, "(3 : ℚ)", "(7 / 2 : ℚ)", "(5 / 2 : ℚ)"),
           _case({"N": "(1 / 4 : ℚ)", "e": "(1 / 8 : ℚ)"}, "(1 / 2 : ℚ)", "(3 / 8 : ℚ)", "(5 / 8 : ℚ)"),
           _case({"N": "(100 : ℚ)", "e": "(3 : ℚ)"}, "(9 : ℚ)", "(12 : ℚ)", "(6 : ℚ)")])

add(id="classic_fast_power", name="fastPower", source="original", params=[("b", "Int"), ("e", "Nat")], ret="Int",
    description="""Return b raised to the power e (exponentiation by repeated squaring is the intended method).""",
    post="result = b ^ e", code="b ^ e", tags=("scalar", "loop", "classic"),
    tests=[_case({"b": "2", "e": "10"}, 1024, 1023, 2048), _case({"b": "3", "e": "0"}, 1, 0, 3), _case({"b": "0", "e": "5"}, 0, 1),
           _case({"b": "(-2)", "e": "3"}, -8, 8, -6), _case({"b": "(-2)", "e": "4"}, 16, -16), _case({"b": "7", "e": "1"}, 7, 8),
           _case({"b": "5", "e": "13"}, 1220703125, 1220703124), _case({"b": "1", "e": "100"}, 1, 0, 2)])

add(id="classic_sort_list", name="sortList", source="original", params=[("l", "List Int")], ret="List Int",
    description="""Return the elements of the list in ascending order (the result is a rearrangement of the input).""",
    post="(∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧ result.isPerm l",
    code="l.mergeSort (fun a b => a ≤ b)", tags=("list", "classic"),
    tests=[_case({"l": "[]"}, "[]", "[0]"), _case({"l": "[3, 1, 2]"}, "[1, 2, 3]", "[3, 2, 1]", "[1, 2]"),
           _case({"l": "[5, 5, 1]"}, "[1, 5, 5]", "[1, 5]", "[5, 5, 1]"), _case({"l": "[1, 2, 3]"}, "[1, 2, 3]", "[3, 2, 1]"),
           _case({"l": "[-1, 4, -3, 0]"}, "[-3, -1, 0, 4]", "[-3, -1, 0]", "[4, 0, -1, -3]"),
           _case({"l": "[9]"}, "[9]", "[8]", "[9, 9]"), _case({"l": "[2, 1]"}, "[1, 2]", "[2, 1]")])

add(id="classic_reverse", name="reverseList", source="original", params=[("l", "List Int")], ret="List Int",
    description="""Return the list in reverse order.""",
    post="result.length = l.length ∧ ∀ i, i < l.length → result[i]! = l[l.length - 1 - i]!",
    code="l.foldl (fun acc x => x :: acc) []", tags=("list", "loop", "classic"),
    tests=[_case({"l": "[]"}, "[]", "[0]"), _case({"l": "[1]"}, "[1]", "[2]", "[1, 1]"), _case({"l": "[1, 2, 3]"}, "[3, 2, 1]", "[1, 2, 3]", "[3, 2]"),
           _case({"l": "[4, 4, 5]"}, "[5, 4, 4]", "[4, 4, 5]"), _case({"l": "[-1, 0]"}, "[0, -1]", "[-1, 0]", "[0]")])



def _register_batches():
    """The rest of HumanEval, in ``benchmarks/datasets/he_lean/`` (one module per range of problems)."""
    from benchmarks.datasets import he_lean
    for entry in he_lean.entries():
        add(**entry)


_register_batches()

BY_ID = {spec.id: spec for spec in SPECS}


# --- tests drawn from HumanEval / EvalPlus ------------------------------------------------------------------------

def _fits(value: Any, spec: Spec) -> bool:
    if isinstance(value, bool):
        return True
    if isinstance(value, float):
        return abs(value) <= spec.int_limit
    if isinstance(value, dict):
        return len(value) <= spec.size_limit and all(_fits(k, spec) and _fits(v, spec) for k, v in value.items())
    if isinstance(value, int):
        return abs(value) <= spec.int_limit
    if isinstance(value, str):
        return len(value) <= spec.size_limit
    if isinstance(value, (list, tuple)):
        return len(value) <= spec.size_limit and all(_fits(v, spec) for v in value)
    return value is None


def _fits_output(value: Any, spec: Spec) -> bool:
    """Outputs may be large numbers (a factorial), but a long list or string slows the specification check down."""
    if isinstance(value, (bool, int, float)) or value is None:
        return True
    if isinstance(value, str):
        return len(value) <= 3 * spec.size_limit
    if isinstance(value, dict):
        return len(value) <= 3 * spec.size_limit
    if isinstance(value, (list, tuple)):
        return len(value) <= 3 * spec.size_limit and all(_fits_output(v, spec) for v in value)
    return False


def _pick(items: List, count: int) -> List:
    if len(items) <= count:
        return items
    step = len(items) / count
    return [items[int(i * step)] for i in range(count)]


def tests_for(spec: Spec, plus: Optional[int] = None, per_total: Optional[int] = None) -> List[dict]:
    """The spec's tests: every original HumanEval case that fits the size limits, then a spread of EvalPlus inputs."""
    if spec.tests is not None:
        return spec.tests
    plus = spec.plus if plus is None else plus
    per_total = spec.per_total if per_total is None else per_total
    from benchmarks.datasets import humaneval as he
    problems, truth = he.load_problems(), he.groundtruth()
    problem, expected = problems[spec.source], truth[spec.source]
    seen = set()

    from benchmarks.datasets import lean_literals
    lean_literals.DECIMAL = not spec.exact_floats

    def make_case(arguments, output) -> Optional[dict]:
        try:
            arguments = spec.adapt(copy.deepcopy(list(arguments))) if spec.adapt else list(arguments)
            output = spec.adapt_out(copy.deepcopy(output)) if spec.adapt_out else output
            if spec.valid is not None and not spec.valid(arguments):
                return None
        except Exception:
            return None
        if len(arguments) != len(spec.params) or not _fits(arguments, spec) or not _fits_output(output, spec):
            return None
        try:
            literals = {n: lean_literal(v, t) for (n, t), v in zip(spec.params, arguments)}
            expected_value = expected_json(output, spec.ret)
            wrong = [expected_json(m, spec.ret) for m in mutants(output, spec.ret)]
        except (ValueError, TypeError):
            return None
        key = json.dumps(literals, sort_keys=True)
        if key in seen:
            return None
        seen.add(key)
        return {"input": literals, "expected": expected_value, "unexpected": wrong}

    cases = [c for c in (make_case(a, o) for a, o in zip(problem["base_input"], expected["base"])) if c]
    extra = [c for c in (make_case(a, o) for a, o in zip(problem["plus_input"], expected["plus"])) if c]
    return (cases + _pick(extra, plus))[:per_total]


# --- writing and checking ------------------------------------------------------------------------------------------

def build(only: Optional[List[str]] = None) -> List[str]:
    from benchmarks.datasets.lean_taskfile import write_task
    written = []
    for spec in SPECS:
        if only and spec.id not in only:
            continue
        tests = tests_for(spec)
        write_task(LIBRARY, spec.id, spec.name, spec.params, spec.ret, spec.description, spec.pre, spec.post, spec.code,
                   tests, pre_aux=spec.pre_aux, code_aux=spec.code_aux, post_aux=spec.post_aux,
                   metadata={"upstream": {"name": "HumanEval" if spec.source.startswith("HumanEval") else "original", "task_id": spec.source}, "tags": list(spec.tags),
                             "note": spec.note},
                   specification={"preconditions": spec.pre, "postconditions": spec.post})
        written.append(f"{spec.id}: {len(tests)} tests")
    return written


def validate(only: Optional[List[str]] = None, imports: str = "import Mathlib") -> List[dict]:
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import LeanTask, precondition_proof, render, same_expr
    rows = []
    with LeanSession(imports=imports, startup_timeout=1200) as lean:
        print(f"imports ready in {lean.startup_seconds:.0f} s", flush=True)
        for spec in SPECS:
            if only and spec.id not in only:
                continue
            directory = os.path.join(LIBRARY, spec.id)
            row = {"id": spec.id, "source": spec.source, "tags": list(spec.tags), "compiles": False, "tests": 0,
                   "reference_passes": 0, "accepts_expected": 0, "rejects_wrong": 0, "wrong_total": 0, "undecidable": 0,
                   "errors": [], "permissive": spec.permissive, "reference_mode": spec.reference_mode}
            rows.append(row)
            if not os.path.isdir(directory):
                row["errors"].append("not built")
                continue
            task = LeanTask.from_dir(directory)
            program = open(os.path.join(directory, "task.lean"), encoding="utf8").read()
            source = "\n".join(l for l in program.splitlines() if not l.strip().startswith("import "))
            reply, env = lean.load(source, timeout=240)
            row["compiles"] = env is not None
            row["tests"] = len(task.tests)
            if env is None:
                row["errors"] = [e[:300] for e in (reply.errors or ["timeout"])[:2]]
                print(f"{spec.id:34s} DOES NOT COMPILE: {row['errors'][0][:110]!r}", flush=True)
                continue
            proof = precondition_proof(task.pre_name)

            row["failures"] = []

            def value(command: str) -> Optional[str]:
                answer = lean.run("set_option maxHeartbeats 2000000 in\n" + command, timeout=120, env=env)
                if answer.errors or not answer.infos:
                    if len(row["errors"]) < 3:
                        row["errors"].append((answer.errors or ["no output"])[0][:200])
                    return None
                return answer.infos[0].strip()

            def fail(kind: str, args: str, detail: str):
                if len(row["failures"]) < 4:
                    row["failures"].append({"kind": kind, "input": args[:160], "value": detail[:100]})

            for case in task.tests:
                args = " ".join(f"({case['input'][n]})" for n, _ in task.params)
                want = render(case["expected"], task.ret)
                if spec.reference_mode == "spec":
                    ran = value(f"#eval decide ({task.post_name} {args} ({task.name} {args} {proof}) {proof})")
                else:
                    ran = value(f"#eval {same_expr(task.ret, f'({task.name} {args} {proof})', want)}")
                row["reference_passes"] += ran == "true"
                if ran != "true":
                    fail("reference", args, f"expected {want}" + ("" if ran else " (did not run)"))
                accepted = value(f"#eval decide ({task.post_name} {args} ({want}) {proof})")
                row["accepts_expected"] += accepted == "true"
                row["undecidable"] += accepted is None
                if accepted != "true":
                    fail("accept", args, f"expected {want}" + ("" if accepted else " (spec did not run)"))
                for wrong in case.get("unexpected", []):
                    row["wrong_total"] += 1
                    shown = value(f"#eval decide ({task.post_name} {args} ({render(wrong, task.ret)}) {proof})")
                    row["rejects_wrong"] += shown == "false"
                    if shown != "false":
                        fail("reject", args, f"wrong {render(wrong, task.ret)}" + ("" if shown else " (spec did not run)"))
            print(f"{spec.id:34s} tests {row['tests']:2d}  reference {row['reference_passes']:2d}  accepts {row['accepts_expected']:2d}"
                  f"  rejects {row['rejects_wrong']:3d}/{row['wrong_total']:3d}  undecidable {row['undecidable']}"
                  f"  {(row['errors'] or [''])[0][:70]}", flush=True)
            for f in row["failures"]:
                print(f"      {f['kind']:9s} {f['input']}  {f['value']}", flush=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("command", choices=["build", "validate", "list"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--he", nargs=2, type=int, metavar=("LO", "HI"), help="the HumanEval problems LO..HI")
    ap.add_argument("--imports", default="import Mathlib")
    args = ap.parse_args()
    if args.he:
        lo, hi = args.he
        args.only = [s.id for s in SPECS if s.source.startswith("HumanEval/") and lo <= int(s.source.split("/")[1]) <= hi]
    if args.command == "list":
        for spec in SPECS:
            print(f"{spec.id:34s} {spec.source:14s} {','.join(spec.tags)}")
        print(len(SPECS), "specifications")
    elif args.command == "build":
        for line in build(args.only):
            print(line)
    else:
        rows = validate(args.only, args.imports)
        os.makedirs(RESULTS, exist_ok=True)
        stored = os.path.join(RESULTS, "validation.json")
        if args.only and os.path.exists(stored):             # a partial run replaces its own rows and keeps the others
            kept = [r for r in json.load(open(stored, encoding="utf8")) if r["id"] not in {x["id"] for x in rows}]
            order = {spec.id: k for k, spec in enumerate(SPECS)}
            rows = sorted(kept + rows, key=lambda r: order.get(r["id"], 10 ** 6))
        with open(os.path.join(RESULTS, "validation.json"), "w", encoding="utf8") as handle:
            json.dump(rows, handle, indent=1)
        good = [r for r in rows if r["compiles"] and r["reference_passes"] == r["tests"] and r["accepts_expected"] == r["tests"]]
        wrong_total = sum(r["wrong_total"] for r in rows)
        print(f"\n{len(rows)} specifications: {sum(r['compiles'] for r in rows)} compile; {len(good)} with a reference that "
              f"passes and a specification that accepts every expected output; wrong outputs rejected "
              f"{sum(r['rejects_wrong'] for r in rows)}/{wrong_total}")


if __name__ == "__main__":
    main()
