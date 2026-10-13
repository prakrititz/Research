# Derivation of he_146_special_filter

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ nums.length ∧ acc = ((nums.take i).filter (fun x => x > 10 ∧ firstDigit x.natAbs % 2 = 1 ∧ x.natAbs % 10 % 2 = 1)).length`
  - guard: `i < nums.length`
  - variant: `nums.length - i`
  - result: `acc`
  - **term**: `(i + 1, if nums[i]! > 10 ∧ firstDigit nums[i]!.natAbs % 2 = 1 ∧ nums[i]!.natAbs % 10 % 2 = 1 then acc + 1 else acc)`
