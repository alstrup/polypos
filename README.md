# poly_pos

A Lean 4 tactic that proves a polynomial in one real variable is positive on an interval:

```lean
import PolyPos.Tactic

example (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    0 < 1280000 * x ^ 8 - 2560000 * x ^ 6 + 1600000 * x ^ 4 - 320000 * x ^ 2 + 20001 := by
  poly_pos
```

Mathlib's `nlinarith` fails on this goal even with hints. The polynomial is 10000 (T₈(x) + 1) + 1,
which comes within 1 of zero at four points.

**Goals:** `p < q`, `p ≤ q`, `p > q`, `p ≥ q` over `ℝ`, for polynomials in one variable `x`
(`+ - * /` by constants, `^` by numerals, rational constants). The context must bound `x` by
rational constants (`a ≤ x` or `a < x`, `x ≤ b` or `x < b`). A false goal is reported with a point
where the polynomial is not positive.

**How it works:**
1. The tactic reads the goal as a polynomial and scales it to integer coefficients.
2. It searches for a certificate: a tree of interval halvings, ending on pieces whose Bernstein
   coefficients are all positive.
3. `PolyPos.check_sound` (proved in `PolyPos/Core.lean`) turns a passing `check` into the theorem.
   Lean's kernel evaluates `check`, so the search is not trusted.

| goal | Lean time |
|---|---|
| T₈ example above (32 pieces) | under 1 s |
| degree 12, near-touching at five points | 0.5 s of kernel checking |
| `1 + x + x²/2 + x³/6 + x⁴/24 > 0` on [−10, 10] | 0.1 s |

Requires Lean 4.35 and Mathlib.
