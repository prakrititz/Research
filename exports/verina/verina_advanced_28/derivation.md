# Derivation of verina_advanced_28

kind: **restate**

- **cases** on `nums = []`
  - _then_:
    - **term**: `0`
      - helper lemma `lc28_nil`: `∀ (nums : List Int) (h : longestConsecutive_precond nums), nums = [] → longestConsecutive_postcond nums (0) h`
  - _else_:
    - **term**: `(let sorted_nums := nums.mergeSort; let consec_sublist_lens := List.range nums.length |>.flatMap (fun start => List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length); consec_sublist_lens.foldl max 0)`
      - helper lemma `lc28_ne`: `∀ (nums : List Int) (h : longestConsecutive_precond nums), ¬ nums = [] → longestConsecutive_postcond nums (let sorted_nums := nums.mergeSort; let consec_sublist_lens := List.range nums.length |>.flatMap (fun start => List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length); consec_sublist_lens.foldl max 0) h`
