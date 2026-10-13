import Mathlib

def md5K : Array UInt32 := #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
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
  String.mk (out.flatMap (fun b => [hexDigit (b / 16), hexDigit (b % 16)]))

@[reducible, simp]
def stringToMd5_precond (text : String) : Prop :=
  True

@[reducible, simp]
def stringToMd5_postcond (text : String) (result: Option String) (h_precond : stringToMd5_precond (text)) :=
  (text = "" → result = none) ∧ (text ≠ "" → result = some (md5Hex text))
