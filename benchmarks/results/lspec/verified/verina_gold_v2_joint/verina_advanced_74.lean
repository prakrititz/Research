import Mathlib
import LeanEnv.RefineLib
namespace Array
def mkArray {α : Type} (n : Nat) (v : α) : Array α := Array.replicate n v
end Array
namespace Std.HashSet
def empty {α : Type} [BEq α] [Hashable α] : Std.HashSet α := {}
end Std.HashSet
syntax "pre_wit_search" : tactic
macro_rules
  | `(tactic| pre_wit_search) => `(tactic| first
      | decide
      | (refine ⟨?_, ?_⟩ <;> pre_wit_search)
      | (refine ⟨0, ?_⟩; pre_wit_search) | (refine ⟨1, ?_⟩; pre_wit_search) | (refine ⟨2, ?_⟩; pre_wit_search)
      | (refine ⟨3, ?_⟩; pre_wit_search) | (refine ⟨4, ?_⟩; pre_wit_search) | (refine ⟨5, ?_⟩; pre_wit_search))
open Std

@[reducible]
def solution_precond (nums : List Nat) : Prop :=
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)

@[reducible]
def solution_postcond (nums : List Nat) (result: Nat) : Prop :=
  let n := nums.length;

  let getSubarray_local := fun (i j : Nat) =>
    (nums.drop i).take (j - i + 1);

  let distinctCount_local := fun (l : List Nat) =>
    let foldFn := fun (seen : List Nat) (x : Nat) =>
      if seen.elem x then seen else x :: seen;
    let distinctElems := l.foldl foldFn [];
    distinctElems.length;

  let square_local := fun (n : Nat) => n * n;

  (1 <= n ∧ n <= 100 ∧ nums.all (fun x => 1 <= x ∧ x <= 100)) ->
  (
    result >= 0
    ∧
    let expectedSum : Nat :=
      List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) =>
        let innerSum : Nat :=
          List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) =>
            let j := i + d;
            let subarr := getSubarray_local i j;
            let count := distinctCount_local subarr;
            currentInnerSum + square_local count
          ) 0
        outerSum + innerSum
      ) 0;

    result = expectedSum
  )



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (norm_num; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.getElem_bang_map_range, Refine.mem_dedup_mergeSort, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.length_filter_range_succ, Refine.filter_mergeSort_key_int, Refine.filter_mergeSort_key_nat, Refine.gather_scatter2, Refine.gather_scatter3, Refine.map_toList_mk, Refine.map_comp_toList_mk, Refine.foldl_int_add, Refine.arr_foldl_push_filter, Refine.arr_all_foldl_push_filter, Refine.idxOf_filter_ne_append, Refine.filter_ne_append_filter_eq_perm, Refine.reverse_isPerm, Refine.asString_toList', Refine.asString_length', Refine.append_mk_toList, Refine.append_mk_length, Refine.append_mk_eq, String.length_toList, List.range_succ, -List.take_append_getElem, -List.getElem!_eq_getElem?_getD]; norm_num; done) | lib_apply | ((try intros); (try unfold solution_precond at *); (try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> first | omega | lib_chain) | ((try intros); (try simp_all only [Refine.getElem_bang_map_range, Refine.getElem_bang_append, Refine.getElem_bang_cons, Refine.getElem_bang_nil, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mem_mergeSort', Refine.mergeSort_length', Refine.mem_dedup_mergeSort, Refine.toList_getElem_bang, Refine.append_mk_eq, Refine.string_toList_mk, Refine.string_length_mk, List.length_map, List.length_range, Refine.foldl_int_add, Refine.asString_toList', Refine.asString_length', Refine.toDigits2_all01, Refine.foldl_toDigits2, Refine.toDigits2_head, Refine.toDigits_length_pos, Refine.gather_scatter2, Refine.gather_scatter3]); (repeat' apply And.intro) <;> (try intros) <;> lib_chain) | ((try intros); (try split_ifs) <;> (try simp only [Refine.getElem_bang_append, Refine.getElem_bang_cons, Refine.getElem_bang_nil] at *) <;> (try split_ifs) <;> grind) | ((try intros); (try casesm* _ ∧ _); (try simp only [Refine.take_succ_getElem?, List.filterMap_append, List.map_append, List.filter_append, List.flatMap_append] at *); (try subst_vars); (try split) <;> (simp_all; done)) | nlinarith | (aesop; done) | decide)))


set_option maxHeartbeats 1000000 in
def solution_derived (nums : List Nat) : { ρ : Nat // solution_postcond nums ρ } :=
  ⟨(let n := nums.length; let getSubarray_local := fun (i : Nat) (j : Nat) => (nums.drop i).take ((j - i) + 1); let distinctCount_local := fun (l : List Nat) => let foldFn := fun (seen : List Nat) (x : Nat) => if seen.elem x then seen else x :: seen; let distinctElems := l.foldl foldFn []; distinctElems.length; let square_local := fun (n : Nat) => n * n; (List.range n).foldl (fun (outerSum : Nat) (i : Nat) => let innerSum : Nat := (List.range (n - i)).foldl (fun (currentInnerSum : Nat) (d : Nat) => let j := i + d; let subarr := getSubarray_local i j; let count := distinctCount_local subarr; currentInnerSum + (square_local count)) 0; outerSum + innerSum) 0), by refine_auto⟩

def solution (nums : List Nat) : Nat := (solution_derived nums).val

theorem solution_spec_satisfied (nums : List Nat) :
    solution_postcond nums (solution nums) := (solution_derived nums).property

#print axioms solution_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((solution ([1]))) == (1))
set_option maxHeartbeats 2000000 in
#eval (((solution ([1, 1, 1]))) == (6))
set_option maxHeartbeats 2000000 in
#eval (((solution ([1, 2, 1]))) == (15))
set_option maxHeartbeats 2000000 in
#eval (((solution ([1, 2, 3, 4]))) == (50))
set_option maxHeartbeats 2000000 in
#eval (((solution ([1, 2, 2, 3, 1]))) == (62))
