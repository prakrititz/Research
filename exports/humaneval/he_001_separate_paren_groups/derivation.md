# Derivation of he_001_separate_paren_groups

kind: **loop**

- **loop** over state (i : Nat, cur : List Char, groups : List (List Char)), start (0, [], [])
  - invariant: `i ≤ (paren_string.toList.filter (fun c => c != ' ')).length ∧ (groups).flatten ++ (cur) = (paren_string.toList.filter (fun c => c != ' ')).take i ∧ (∀ g ∈ groups, g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ (cur).length → ((cur).take k).count ')' < ((cur).take k).count '('`
  - guard: `i < (paren_string.toList.filter (fun c => c != ' ')).length`
  - variant: `(paren_string.toList.filter (fun c => c != ' ')).length - i`
  - result: `groups.map String.mk`
  - helper lemma `flatten_balanced`: `∀ (groups : List (List Char)), (∀ g ∈ groups, isBalanced g) → groups.flatten.count '(' = groups.flatten.count ')'`
  - helper lemma `step_close`: `∀ (F : List Char) (i : Nat) (cur : List Char) (groups : List (List Char)), isBalanced F → i < F.length → (i ≤ F.length ∧ (groups).flatten ++ (cur) = F.take i ∧ (∀ g ∈ groups, g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ (cur).length → ((cur).take k).count ')' < ((cur).take k).count '(') → (cur ++ [F[i]!]).count '(' = (cur ++ [F[i]!]).count ')' → ((i + 1) ≤ F.length ∧ ((groups ++ [cur ++ [F[i]!]])).flatten ++ ([]) = F.take (i + 1) ∧ (∀ g ∈ (groups ++ [cur ++ [F[i]!]]), g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ ([] : List Char).length → (([] : List Char).take k).count ')' < (([] : List Char).take k).count '(')`
  - helper lemma `step_open`: `∀ (F : List Char) (i : Nat) (cur : List Char) (groups : List (List Char)), isBalanced F → i < F.length → (i ≤ F.length ∧ (groups).flatten ++ (cur) = F.take i ∧ (∀ g ∈ groups, g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ (cur).length → ((cur).take k).count ')' < ((cur).take k).count '(') → ¬ (cur ++ [F[i]!]).count '(' = (cur ++ [F[i]!]).count ')' → ((i + 1) ≤ F.length ∧ (groups).flatten ++ ((cur ++ [F[i]!])) = F.take (i + 1) ∧ (∀ g ∈ groups, g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ ((cur ++ [F[i]!])).length → (((cur ++ [F[i]!])).take k).count ')' < (((cur ++ [F[i]!])).take k).count '(')`
  - helper lemma `separate_exit`: `∀ (F : List Char) (cur : List Char) (groups : List (List Char)), isBalanced F → (F.length ≤ F.length ∧ (groups).flatten ++ (cur) = F.take F.length ∧ (∀ g ∈ groups, g ≠ [] ∧ isBalanced g ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.take k)) ∧ ∀ k, 0 < k → k ≤ (cur).length → ((cur).take k).count ')' < ((cur).take k).count '(') → ((groups.map String.mk).map String.toList).flatten = F ∧ ∀ g ∈ groups.map String.mk, g.length > 0 ∧ isBalanced g.toList ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.toList.take k)`
  - **cases** on `(cur ++ [(paren_string.toList.filter (fun c => c != ' '))[i]!]).count '(' = (cur ++ [(paren_string.toList.filter (fun c => c != ' '))[i]!]).count ')'`
    - _then_:
      - **term**: `(i + 1, ([] : List Char), groups ++ [cur ++ [(paren_string.toList.filter (fun c => c != ' '))[i]!]])`
    - _else_:
      - **term**: `(i + 1, cur ++ [(paren_string.toList.filter (fun c => c != ' '))[i]!], groups)`
