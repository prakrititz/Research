r"""HumanEval problems 40-59 (those not already in ``lean_specs.py``) specified in Lean."""

TOL = "(1 / 1000000 : ℚ)"


def _is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


ENTRIES = [
    dict(id="he_040_triples_sum_to_zero", name="triplesSumToZero", source="HumanEval/40",
         params=[("l", "List Int")], ret="Bool",
         description="Take a list of integers as input; return true if there are three distinct elements (at different positions) in the list that sum to zero, and false otherwise.",
         post="result = true ↔ ∃ k, k < l.length ∧ ∃ j, j < k ∧ ∃ i, i < j ∧ l[i]! + l[j]! + l[k]! = 0",
         code="""(List.range l.length).any (fun k => (List.range k).any (fun j => (List.range j).any (fun i => l[i]! + l[j]! + l[k]! == 0)))""",
         size_limit=12, tags=("list", "declarative")),

    dict(id="he_044_change_base", name="changeBase", source="HumanEval/44",
         params=[("x", "Nat"), ("base", "Nat")], ret="String",
         description="Change the numerical base of the input number x to base; return the string representation after the conversion. The base is less than 10.",
         pre="2 ≤ base ∧ base < 10",
         post="""result.toList.all (fun c => c.isDigit && c.toNat - '0'.toNat < base) = true ∧
  result.toList.foldl (fun acc c => acc * base + (c.toNat - '0'.toNat)) 0 = x ∧
  (x = 0 → result = "0") ∧ (x > 0 → result.toList.head! ≠ '0')""",
         code="""Id.run do
  let mut m := x
  let mut ret := ""
  while m != 0 do
    ret := toString (m % base) ++ ret
    m := m / base
  return (if x == 0 then "0" else ret)""", valid=lambda a: a[0] >= 0 and 2 <= a[1] < 10, int_limit=100000,
         tags=("scalar", "string", "declarative")),

    dict(id="he_045_triangle_area", name="triangleArea", source="HumanEval/45",
         params=[("a", "ℚ"), ("h", "ℚ")], ret="ℚ",
         description="Given the length of a side and the height, return the area of a triangle.",
         post=f"|result - a * h / 2| ≤ {TOL}", code="a * h / 2", tags=("scalar", "float", "declarative")),

    dict(id="he_046_fib4", name="fib4", source="HumanEval/46",
         params=[("n", "Nat")], ret="Nat",
         description="The Fib4 number sequence is defined as: fib4(0) = 0, fib4(1) = 0, fib4(2) = 2, fib4(3) = 0, and fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4). Compute the n-th element of the fib4 sequence efficiently (without recursion).",
         pre_aux="""def fib4Spec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | (n + 4) => fib4Spec (n + 3) + fib4Spec (n + 2) + fib4Spec (n + 1) + fib4Spec n""",
         post="result = fib4Spec n",
         code="""Id.run do
  let mut a := 0
  let mut b := 0
  let mut c := 2
  let mut d := 0
  if n == 0 then return 0
  if n == 1 then return 0
  if n == 2 then return 2
  for _ in [4:n + 1] do
    (a, b, c, d) := (b, c, d, a + b + c + d)
  return d""", int_limit=26, tags=("scalar", "recursive-spec", "declarative")),

    dict(id="he_047_median", name="median", source="HumanEval/47",
         params=[("l", "List ℚ")], ret="ℚ",
         description="Return the median of the elements in the list l.",
         pre="l ≠ []",
         post=f"""let s := l.mergeSort (fun a b => a ≤ b)
|result - (if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2)| ≤ {TOL}""",
         code="""let s := l.mergeSort (fun a b => a ≤ b)
if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2""",
         valid=lambda a: len(a[0]) > 0, tags=("list", "float")),

    dict(id="he_049_modp", name="modp", source="HumanEval/49",
         params=[("n", "Nat"), ("p", "Nat")], ret="Nat",
         description="Return 2^n modulo p (be aware of numerics).",
         pre="p > 0", post="result = 2 ^ n % p",
         code="""Id.run do
  let mut res := 1
  let mut x := 2
  let mut m := n
  while m != 0 do
    if m % 2 == 1 then res := res * x % p
    x := x * x % p
    m := m / 2
  return res % p""", valid=lambda a: a[0] >= 0 and a[1] > 0, int_limit=100000, tags=("scalar", "declarative")),

    dict(id="he_050_decode_shift", name="decodeShift", source="HumanEval/50",
         params=[("s", "String")], ret="String",
         description="Takes as input a string encoded with encode_shift (which shifts every lowercase letter by 5 in the alphabet) and returns the decoded string.",
         pre_aux="def shiftChar (c : Char) : Char := Char.ofNat ((c.toNat - 97 + 5) % 26 + 97)",
         pre="s.toList.all (fun c => c.isLower) = true",
         post="result.toList.all (fun c => c.isLower) = true ∧ result.toList.map shiftChar = s.toList",
         code="String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))",
         valid=lambda a: all("a" <= c <= "z" for c in a[0]), size_limit=40, tags=("string", "declarative"),
         note="stated as the inverse of encode_shift on lowercase letters (the canonical solution also maps other characters, which no encoder produces)"),

    dict(id="he_051_remove_vowels", name="removeVowels", source="HumanEval/51",
         params=[("text", "String")], ret="String",
         description="Take a string and return the string without vowels.",
         post="result.toList = text.toList.filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))",
         code="String.mk (text.toList.filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)))",
         size_limit=40, tags=("string", "declarative")),

    dict(id="he_053_add", name="add", source="HumanEval/53",
         params=[("x", "Int"), ("y", "Int")], ret="Int",
         description="Add two numbers x and y.", post="result = x + y", code="x + y", tags=("scalar", "term", "declarative")),

    dict(id="he_054_same_chars", name="sameChars", source="HumanEval/54",
         params=[("s0", "String"), ("s1", "String")], ret="Bool",
         description="Check if two words have the same characters (the same set of characters, regardless of how often each occurs).",
         post="result = true ↔ ((∀ c ∈ s0.toList, c ∈ s1.toList) ∧ (∀ c ∈ s1.toList, c ∈ s0.toList))",
         code="s0.toList.all (fun c => s1.toList.contains c) && s1.toList.all (fun c => s0.toList.contains c)",
         size_limit=40, tags=("string", "declarative")),

    dict(id="he_056_correct_bracketing", name="correctBracketing56", source="HumanEval/56",
         params=[("brackets", "String")], ret="Bool",
         description="brackets is a string of \"<\" and \">\". Return true if every opening bracket has a corresponding closing bracket.",
         pre="brackets.toList.all (fun c => c == '<' || c == '>') = true",
         post="""result = true ↔ ((∀ k, k ≤ brackets.length → (brackets.toList.take k).count '>' ≤ (brackets.toList.take k).count '<') ∧
    brackets.toList.count '<' = brackets.toList.count '>')""",
         code="""Id.run do
  let mut depth : Int := 0
  for c in brackets.toList do
    if c == '<' then depth := depth + 1
    else if c == '>' then depth := depth - 1
    if depth < 0 then return false
  return depth == 0""", valid=lambda a: set(a[0]) <= set("<>"), size_limit=30, tags=("string", "loop", "declarative")),

    dict(id="he_059_largest_prime_factor", name="largestPrimeFactor", source="HumanEval/59",
         params=[("n", "Nat")], ret="Nat",
         description="Return the largest prime factor of n. Assume n > 1 and n is not a prime.",
         pre="n > 1 ∧ ¬ Nat.Prime n",
         post="Nat.Prime result ∧ result ∣ n ∧ ∀ q, q < n + 1 → Nat.Prime q → q ∣ n → q ≤ result",
         code="""Id.run do
  let mut m := n
  let mut i := 2
  let mut best := 1
  while i * i ≤ m do
    if m % i == 0 then
      best := i
      m := m / i
    else
      i := i + 1
  return (if m > best then m else best)""", valid=lambda a: a[0] > 1 and not _is_prime(a[0]), int_limit=20000,
         tags=("scalar", "declarative")),
]
