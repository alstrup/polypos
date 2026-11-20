import Mathlib
example (x y : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    0 < x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 + 1/100 := by nlinarith [sq_nonneg (x*y), sq_nonneg (x^2 - 1), sq_nonneg (y^2-1), mul_nonneg (sq_nonneg x) (sq_nonneg y)]
example (x y z : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) (h5 : -1 ≤ z) (h6 : z ≤ 1) :
    0 < x^4*y^2 + y^4*z^2 + z^4*x^2 - 3*x^2*y^2*z^2 + 1/10 := by nlinarith [sq_nonneg (x*y), sq_nonneg (y*z), sq_nonneg (z*x)]
