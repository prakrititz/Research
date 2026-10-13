# he_129_min_path

`minPath(grid : List (List Nat), k : Nat) : List Nat`

Given a grid with N rows and N columns (N >= 2) and a positive integer k, each cell of the grid contains a value. Every integer in the range [1, N * N] inclusive appears exactly once on the cells of the grid. Find the minimum path of length k in the grid: you can start from any cell, and in each step you can move to any of the neighbour cells (cells that share an edge with the current cell); a path of length k visits exactly k cells (not necessarily distinct). A path A is less than a path B if the ordered list of the values on the cells of A is lexicographically less than that of B. Return the ordered list of the values on the cells that the minimum path goes through.
