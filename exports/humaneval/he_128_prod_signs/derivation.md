# Derivation of he_128_prod_signs

kind: **restate**

- **term**: `if arr = [] then none else some ((arr.map (fun (x : Int) => (x.natAbs : Int))).sum * (arr.map Int.sign).prod)`
