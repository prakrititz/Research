namespace Refine
theorem getElem_bang_zero_mem_take_of_lt {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => simp at h
  | cons x xs => simp
end Refine

example (numbers : List Int) (i : Nat) (hi : i < numbers.length) :
    List.foldl max numbers[0]! (List.take (i + 1) numbers) ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ List.foldl max numbers[0]! (List.take (i + 1) numbers) := by
  (repeat' apply And.intro) <;> (try intros) <;> solve_by_elim (maxDepth := 4) [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.mem_iff_idx, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.toList_getElem_bang, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.forall_mem_drop_iff, Refine.exists_mem_drop_iff, Refine.forall_mem_take_iff, Refine.arr_all_take_iff, Refine.arr_all_drop_iff, Refine.sorted_arr_le, Refine.foldl_max_facts, Refine.maxlist_nat, Refine.maxlist_int, Refine.allsub_nil_mem, Refine.allsub_nil_mem_arr, Refine.allsub_rev_nil_mem, Refine.longest_facts, Refine.longest_spec, Refine.maxlist_int_any, Refine.maxlen_spec, Refine.filter_pair_le, Refine.count_pair_le, Refine.find_some_of_any, Refine.find_majority, Refine.ts_inner_init, Refine.ts_outer_init, Refine.ts_inner_step, Refine.ts_inner_exit, Refine.ts_outer_step, Refine.ts_lex_all, Refine.ts_pairwise_none, Refine.getElem_bang_map_range, Refine.getElem_bang_append, Refine.pairwise_le_nodup_lt, Refine.dedup_mergeSort_strict, Refine.mem_dedup_mergeSort, Refine.foldl_max_mem_of_mem, Refine.le_foldl_max, Refine.start_le_foldl_max, Refine.getElem_bang_zero_mem_take, Refine.getElem_bang_zero_mem_take', Refine.getElem_bang_zero_mem_take_of_lt]
