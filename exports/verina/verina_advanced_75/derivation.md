# Derivation of verina_advanced_75

kind: **restate**

- **term**: `(let subArrays := List.range (sequence.length + 1) |>.flatMap (fun start => List.range (sequence.length - start + 1) |>.map (fun len => sequence.drop start |>.take len)); let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum); subArraySums.foldl max (subArraySums.headD 0))`
  - helper lemma `ms75`: `∀ (sequence : List Int) (h : task_code_precond sequence), task_code_postcond sequence (let subArrays := List.range (sequence.length + 1) |>.flatMap (fun start => List.range (sequence.length - start + 1) |>.map (fun len => sequence.drop start |>.take len)); let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum); subArraySums.foldl max (subArraySums.headD 0)) h`
