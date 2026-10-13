# Derivation of verina_advanced_77

kind: **restate**

- **term**: `((List.range height.length).map (fun i => Nat.min (List.take (i + 1) height |>.foldl Nat.max 0) (List.drop i height |>.foldl Nat.max 0) - height[i]!)).foldl (· + ·) 0`
