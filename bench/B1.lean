import PolyPos.Tactic
set_option profiler true
set_option profiler.threshold 50
-- degree 12: a product of squares near five points, lifted by 10⁻⁶
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    0 < ((x - 1/10) * (x - 3/10) * (x - 5/10) * (x - 7/10) * (x - 9/10) * (x - 1/2)) ^ 2 + 1/1000000 := by
  poly_pos
