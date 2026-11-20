import PolyPos.Tactic
set_option profiler true
set_option profiler.threshold 50
-- a Taylor-polynomial bound: 1 + x + x²/2 + x³/6 + x⁴/24 > 0 on [−10, 10]
example (x : ℝ) (h1 : -10 ≤ x) (h2 : x ≤ 10) : 0 < 1 + x + x^2/2 + x^3/6 + x^4/24 := by poly_pos
