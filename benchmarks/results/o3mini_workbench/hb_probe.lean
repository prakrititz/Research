-- a heavy alternative under a tiny budget, then a cheap one: does `first` move on?
example : (List.range 3000).length = 3000 := by
  first | (set_option maxHeartbeats 50 in decide) | simp
