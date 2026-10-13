# Derivation of verina_advanced_22

kind: **restate**

- **term**: `(let len := lst.length; let validPeaks := List.range len |>.filter (fun p => 1 ≤ p ∧ p < len - 1 ∧ (List.range p).all (fun i => lst[i]! < lst[i + 1]!) ∧ (List.range (len - 1 - p)).all (fun i => lst[p + i]! > lst[p + i + 1]!)); validPeaks != [])`
  - helper lemma `peak_ok`: `∀ (lst : List Int) (h : isPeakValley_precond lst), isPeakValley_postcond lst (let len := lst.length; let validPeaks := List.range len |>.filter (fun p => 1 ≤ p ∧ p < len - 1 ∧ (List.range p).all (fun i => lst[i]! < lst[i + 1]!) ∧ (List.range (len - 1 - p)).all (fun i => lst[p + i]! > lst[p + i + 1]!)); validPeaks != []) h`
