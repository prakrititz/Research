# Derivation of verina_advanced_70

kind: **restate**

- **cases** on `nums.idxOf 1 > nums.idxOf (Int.ofNat nums.length)`
  - _then_:
    - **term**: `(nums.idxOf 1 : Int) + (nums.length : Int) - 2 - (nums.idxOf (Int.ofNat nums.length) : Int)`
  - _else_:
    - **term**: `(nums.idxOf 1 : Int) + (nums.length : Int) - 1 - (nums.idxOf (Int.ofNat nums.length) : Int)`
