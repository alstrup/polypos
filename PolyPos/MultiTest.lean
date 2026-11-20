import PolyPos.Tactic

example (x y : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (h3 : 0 ≤ y) (h4 : y ≤ 1) :
    0 < x ^ 2 + y ^ 2 - x * y + 1/10 := by poly_pos

-- the Motzkin polynomial, plus 1/100: not a sum of squares, so SOS methods need a multiplier
example (x y : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    0 < x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 + 1/100 := by poly_pos

example (x y z : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) (h5 : -1 ≤ z) (h6 : z ≤ 1) :
    0 < x^2 + y^2 + z^2 - x*y*z + 1/50 := by poly_pos

-- a false goal is reported with a corner of the box
/-- error: poly_pos: the polynomial is not positive at [x = 0, y = 1] -/
#guard_msgs in
example (x y : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (h3 : 0 ≤ y) (h4 : y ≤ 1) : 0 < x - y + 1/2 := by poly_pos
