# poly_pos

A Lean 4 tactic that proves a polynomial is positive on an interval or a box:

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
   coefficients are all positive. Each half's coefficients come from its parent's by a
   substitution (de Casteljau): `H(2u + v, v)` on the left, `H(u, u + 2v)` on the right.
3. `PolyPos.checkWit_sound` (proved in `PolyPos/Core.lean`) turns a passing check into the
   theorem. Lean's kernel evaluates the check with `decide +kernel`, so the search is not
   trusted. The only axioms are Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

**Making the kernel check fast.** The certificate carries every piece's coefficients as
literals, so the kernel only confirms `subL parent = left`, `subR parent = right` and positivity
at the leaves. The kernel otherwise evaluates lazily and rebuilds whole chains of subdivisions. The
functions it runs are written with `List.rec` directly; structural recursion (`brecOn`)
reduces several times slower in the kernel. Each is proved equal to its plain reference definition.

Kernel time to check the certificate for the T₈ example (32 pieces):

| checker | kernel time |
|---|---|
| recompute each piece's coefficients from the polynomial (`check`) | 2.9 s |
| subdivide lazily (`checkFast`) | 8.1 s |
| coefficients as literals (`WCert`) | 1.15 s |
| coefficients as literals, `List.rec` functions (`checkWit`, used by the tactic) | **0.35 s** |

Whole-goal kernel time with the tactic (best of three, on a loaded machine):

| goal | kernel time |
|---|---|
| T₈ example above | 0.66 s |
| degree 12, coming within 10⁻⁶ of zero at five points | 0.21 s |
| `1 + x + x²/2 + x³/6 + x⁴/24 > 0` on [−10, 10] | 0.09 s |

## Several variables

```lean
-- the Motzkin polynomial is nonnegative but not a sum of squares
example (x y : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    0 < x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 + 1/100 := by
  poly_pos
```

With two or more real variables, each bounded by rational constants in the context, the tactic
works on the box (`PolyPos/Multi.lean`, `PolyPos/MultiMeta.lean`):

- A form is a nested list, one level per variable, each level with its degree. Halving
  variable `j` applies the one-variable subdivision at level `j`.
- `PolyPos.Multi.checkK_sound` proves the certificate checker sound, with only Lean's standard
  axioms. The checker carries every piece's coefficients and is written with recursors for the
  kernel, as in the one-variable case.
- `ring` proves that the starting form equals `L · p(x)`. The kernel never computes the
  multivariate change of basis.
- The certificate is built directly as a Lean term; elaborating it as syntax took longer than
  checking it.
- The search halves the variable that leaves the fewest non-positive coefficients, and falls
  back to taking the variables in turn when that makes no progress.

`nlinarith` fails on both Motzkin goals below, even with hints.

| goal | leaves | kernel time |
|---|---|---|
| Motzkin + 1/100 on [−1, 1]² (the coefficients are positive without halving) | 1 | 0.13 s |
| x² + y² + z² − xyz + 1/50 on [−1, 1]³ | 20 | 0.5 s |
| x⁴y² + y⁴z² + z⁴x² − 3x²y²z² + 1/10 on [−1, 1]³ | 56 | 2.7 s |

**Is a better search worth it?** The kernel check dominates: the search takes about a quarter
of a second. A smaller certificate would shorten the check, so `bench/Opt.lean` computes the
fewest pieces exactly, by dynamic programming over sub-boxes. On the three-variable Motzkin
goal and on two valley-shaped goals in two variables, the greedy rule already finds the
minimum, so a parallel search for smaller certificates (the role planned for Bend) would gain
nothing on these goals. See `bench/opt_results.txt`.

## Limitations

- Bounded intervals and boxes with rational endpoints.
- Strict positivity: `x² ≥ 0` on [−1, 1] fails, since the polynomial touches 0 at x = 0.
- Real coefficients that are not rational (`√2`, `π`) are not read.

## License

Apache-2.0.

Requires Lean 4.35 and Mathlib.
