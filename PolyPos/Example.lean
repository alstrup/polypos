import PolyPos.Core
open PolyPos
-- 100x² − 200x + 101 > 0 on [0, 2]; it gets within 0.01 of zero at x = 1
example : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → 0 < 100 * x ^ 2 - 200 * x + 101 := by
  intro x h1 h2
  have := check_sound [101, -200, 100] (by simp) (PolyPos.Cert.split PolyPos.Cert.leaf PolyPos.Cert.leaf) 0 2 1 (by norm_num) (by norm_num)
    (by decide +kernel) x (by simpa using h1) (by simpa using h2)
  simp only [eval] at this; push_cast at this; linarith
