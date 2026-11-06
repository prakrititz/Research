# Python constructs in HumanEval's reference solutions, and L_spec

164 reference solutions (EvalPlus canonical solutions); statements (loops, assignments, `if`) are refinement laws and not counted. *Tasks*: how many solutions use the construct.

## Same name, different meaning (the risky ones)

| Construct | Kind | Tasks | Note |
|---|---|---|---|
| `index` | form | 62 | `l[i]` past the end is a default value (0, False, ""), not an error |
| `range` | builtin | 53 | `range(n)` only; `range(a, b)` and a step have no direct form |
| `Mod` | operator | 43 | `%`: for a negative divisor the sign of the result differs from Python's |
| `Sub` | operator | 39 | on `nat`, `a - b` is 0 when b > a (Python: negative). Cast to `int` first |
| `sorted` | builtin | 19 | `sorted(l)` sorts numbers; a `key=` or `reverse=` argument has no L_spec form (write a comparison: `sorted(l, c)`) |
| `FloorDiv` | operator | 11 | `//` is `/` in L_spec; for a negative divisor Lean and Python round differently |
| `Div` | operator | 10 | on `nat`/`int`, `/` is integer division; Python's `/` is a float |
| `float literal` | form | 10 | a `rat`: exact |
| `float` | builtin | 3 | floats are written as `rat`: exact, no rounding |

## No L_spec form yet

| Construct | Kind | Tasks | Note |
|---|---|---|---|
| `list comprehension` | form | 19 | `[f(x) for x in l if p(x)]`: write `l.filter(p).map(f)` |
| `int` | builtin | 17 | parsing a string to a number |
| `.join` | method | 13 | joining strings |
| `.split` | method | 13 | splitting a string |
| `generator` | form | 12 | `sum(f(x) for x in l)`: write `sum(l.map(f))` |
| `slice with step` | form | 11 | `l[::2]`, `l[::-1]` (write `reversed(l)`) |
| `max` | builtin | 10 | min/max of a list (a binary `max(a, b)` is Lean's `max`) |
| `min` | builtin | 9 | min/max of a list (a binary `min(a, b)` is Lean's `min`) |
| `negative index` | form | 8 | `l[-1]`: write `l[len(l) - 1]` |
| `any` | builtin | 6 | `any(p(x) for x in l)`: write `exists x in l: p(x)` |
| `.replace` | method | 5 |  |
| `is_prime` | builtin | 5 |  |
| `set` | builtin | 5 | sets: write `dedup(l)` or a membership condition |
| `bin` | builtin | 4 |  |
| `dict` | builtin | 4 | dictionaries |
| `round` | builtin | 4 | Python rounds half to even |
| `.startswith` | method | 3 |  |
| `all` | builtin | 3 | `all(...)`: write `forall x in l: p(x)` |
| `chained comparison` | form | 3 | `a < b < c`: write `a < b and b < c` |
| `enumerate` | builtin | 3 | write an index loop |
| `slice a:b` | form | 3 | `l[a:b]`: write `l[a:][:b - a]` |
| `type` | builtin | 3 |  |
| `.ceil` | method | 2 |  |
| `.items` | method | 2 | dictionaries |
| `.swapcase` | method | 2 |  |
| `cmp_to_key` | builtin | 2 |  |
| `dict literal / comprehension` | form | 2 | dictionaries |
| `.encode` | method | 1 |  |
| `.hexdigest` | method | 1 |  |
| `.intersection` | method | 1 |  |
| `.keys` | method | 1 | dictionaries |
| `.lower` | method | 1 | string case |
| `.md5` | method | 1 |  |
| `.pow` | method | 1 |  |
| `.randint` | method | 1 |  |
| `.sqrt` | method | 1 |  |
| `.strip` | method | 1 |  |
| `.update` | method | 1 |  |
| `.values` | method | 1 | dictionaries |
| `count_depth` | builtin | 1 |  |
| `derivative` | builtin | 1 |  |
| `digits` | builtin | 1 |  |
| `eval` | builtin | 1 |  |
| `func` | builtin | 1 |  |
| `is_palindrome` | builtin | 1 |  |
| `is_vowel` | builtin | 1 |  |
| `miller_rabin` | builtin | 1 |  |
| `poly` | builtin | 1 |  |
| `query_gcd` | builtin | 1 |  |
| `rounding` | builtin | 1 |  |
| `strength` | builtin | 1 |  |
| `to_letter_grade` | builtin | 1 |  |
| `to_word` | builtin | 1 |  |
| `valid_parens` | builtin | 1 |  |

## In L_spec under another spelling

| Construct | Kind | Tasks | Note |
|---|---|---|---|
| `.append` | method | 13 | `l ++ [x]` |
| `ord` | builtin | 6 | `c.toNat` |
| `.isalpha` | method | 3 | `c.isAlpha` (a character) |
| `.islower` | method | 3 | `c.isLower` |
| `.isupper` | method | 3 | `c.isUpper` |
| `.sort` | method | 3 | `sorted(l)` |
| `chr` | builtin | 3 | `Char.ofNat(n)` |
| `.isdigit` | method | 2 | `c.isDigit` (a character) |
| `BitXor` | operator | 1 | `xor` |
| `zip` | builtin | 1 | `List.zip(a, b)` |

## In L_spec as in Python

| Construct | Kind | Tasks | Note |
|---|---|---|---|
| `Eq` | operator | 91 |  |
| `Add` | operator | 57 |  |
| `len` | builtin | 56 |  |
| `USub` | operator | 33 |  |
| `lambda` | form | 29 |  |
| `list` | builtin | 24 | `list(s)` of a string is its characters |
| `Lt` | operator | 22 |  |
| `Mult` | operator | 21 |  |
| `conditional expression` | form | 21 | `a if c else b` |
| `Gt` | operator | 20 |  |
| `NotEq` | operator | 20 |  |
| `filter` | builtin | 20 | `filter(p, l)` |
| `str` | builtin | 19 | `str(n)` |
| `Or` | operator | 18 |  |
| `LtE` | operator | 16 |  |
| `map` | builtin | 16 | `map(f, l)` |
| `slice` | form | 16 | `l[:k]`, `l[k:]` |
| `Pow` | operator | 14 | `**` |
| `And` | operator | 13 |  |
| `sum` | builtin | 13 |  |
| `Not` | operator | 12 |  |
| `In` | operator | 11 |  |
| `NotIn` | operator | 11 |  |
| `abs` | builtin | 7 |  |
| `GtE` | operator | 6 |  |
| `tuple` | builtin | 2 | a tuple literal |
| `.index` | method | 1 | `l.index(x)` |
| `pow` | builtin | 1 | `a ** b` |
