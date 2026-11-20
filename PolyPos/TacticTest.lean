import PolyPos.Tactic

example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 2) : 0 < 100 * x ^ 2 - 200 * x + 101 := by poly_pos

example : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
    0 < 1280000 * x ^ 8 - 2560000 * x ^ 6 + 1600000 * x ^ 4 - 320000 * x ^ 2 + 20001 := by
  intro x h1 h2; poly_pos

-- rational coefficients and bounds, a comparison, ≤
example (x : ℝ) (h1 : 1/3 ≤ x) (h2 : x < 5/2) : x ^ 3 / 2 + 1 > x - x ^ 2 / 7 := by poly_pos
example (y : ℝ) (h1 : -2 ≤ y) (h2 : y ≤ 3) : (y - 1) * (y - 1) + 1/1000 ≥ 0 := by poly_pos

-- a false goal is reported with a point
/-- error: poly_pos: the polynomial is not positive at x = 1 -/
#guard_msgs in
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 2) : 0 < x ^ 2 - 2 * x + 99/100 := by poly_pos
