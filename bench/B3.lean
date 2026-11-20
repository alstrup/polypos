import PolyPos.Tactic
set_option profiler true
example (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    0 < 1280000 * x ^ 8 - 2560000 * x ^ 6 + 1600000 * x ^ 4 - 320000 * x ^ 2 + 20001 := by
  poly_pos
