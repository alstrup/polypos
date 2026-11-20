import PolyPos.Tactic
set_option profiler true
theorem motz (x y : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    0 < x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 + 1/100 := by poly_pos
#print axioms motz
-- three variables: a positive-definite quadratic form minus a cubic, near zero
theorem three (x y z : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) (h5 : -1 ≤ z) (h6 : z ≤ 1) :
    0 < x^2 + y^2 + z^2 - x*y*z + 1/50 := by poly_pos
-- Motzkin in three variables, x⁴y² + y⁴z² + z⁴x² − 3x²y²z² ≥ 0 (AM-GM), lifted
theorem motz3 (x y z : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) (h5 : -1 ≤ z) (h6 : z ≤ 1) :
    0 < x^4*y^2 + y^4*z^2 + z^4*x^2 - 3*x^2*y^2*z^2 + 1/10 := by poly_pos
