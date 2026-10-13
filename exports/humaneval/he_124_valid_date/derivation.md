# Derivation of he_124_valid_date

kind: **restate**

- **bind** `l : List Char` with property `l = date.toList`
  - _value_:
    - **term**: `date.toList`
  - _continuation_:
    - **term**: `decide (l.length = 10 ∧ l[2]! = '-' ∧ l[5]! = '-' ∧ (l.take 2).all Char.isDigit = true ∧ ((l.drop 3).take 2).all Char.isDigit = true ∧ (l.drop 6).all Char.isDigit = true ∧ 1 ≤ natOf (l.take 2) ∧ natOf (l.take 2) ≤ 12 ∧ 1 ≤ natOf ((l.drop 3).take 2) ∧ natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))`
