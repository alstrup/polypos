import Mathlib

/-!
# PolyPos: positivity of a univariate polynomial on an interval, by certificate

A polynomial is a list of integer coefficients, lowest degree first. On the interval
`[A/D, B/D]` we write `x = (A u + B v) / D` with `u, v ≥ 0`, `u + v = 1`, and homogenize:
`D^n p(x) = hv (bern p A B D) u v`, a form `Σ h_k u^(n-k) v^k`. If every `h_k > 0`, then
`p > 0` on the interval (the Bernstein criterion). If not, split the interval at its midpoint
and try both halves. The certificate is the tree of splits; Lean's kernel evaluates `check`.
-/

namespace PolyPos

/-- Horner evaluation of coefficients, lowest degree first. -/
def eval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: t, x => c + x * eval t x

/-- A homogeneous form of degree `len - 1`: the head is the coefficient of `u^n`. -/
def hv : List ℤ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: t, u, v => c * u ^ t.length + v * hv t u v

/-- Pointwise sum of two forms of the same degree. -/
def add : List ℤ → List ℤ → List ℤ
  | a :: s, b :: t => (a + b) :: add s t
  | s, [] => s
  | [], t => t

def scale (k : ℤ) (h : List ℤ) : List ℤ := h.map (k * ·)

/-- Multiply a form by `A u + B v`: the `u` part keeps the indices, the `v` part shifts them. -/
def mulLin (A B : ℤ) (h : List ℤ) : List ℤ := add (scale A (h ++ [0])) (scale B (0 :: h))

/-- `(D (u + v))^n` as a form. -/
def mpow (D : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => mulLin D D (mpow D n)

/-- The homogenization of `p` on `[A/D, B/D]`. -/
def bern (A B D : ℤ) : List ℤ → List ℤ
  | [] => []
  | [c] => [c]
  | c :: t => add (scale c (mpow D t.length)) (mulLin A B (bern A B D t))

/-- A certificate: split at the midpoint, or stop and check the coefficients. -/
inductive Cert where
  | leaf : Cert
  | split : Cert → Cert → Cert
  deriving Repr

def allPos (h : List ℤ) : Bool := h.all (fun c => decide (0 < c))

def check (cs : List ℤ) : ℤ → ℤ → ℤ → Cert → Bool
  | A, B, D, .leaf => allPos (bern A B D cs)
  | A, B, D, .split l r => check cs (2 * A) (A + B) (2 * D) l && check cs (A + B) (2 * B) (2 * D) r

/-! ## The form lemmas -/

theorem length_add : ∀ s t : List ℤ, s.length = t.length → (add s t).length = s.length
  | [], [], _ => rfl
  | a :: s, b :: t, h => by simp [add, length_add s t (by simpa using h)]

theorem hv_add : ∀ (s t : List ℤ) (u v : ℝ), s.length = t.length →
    hv (add s t) u v = hv s u v + hv t u v
  | [], [], _, _, _ => by simp [add, hv]
  | a :: s, b :: t, u, v, h => by
    have h' : s.length = t.length := by simpa using h
    simp only [add, hv, hv_add s t u v h', length_add s t h', Int.cast_add]
    rw [h']; ring

theorem length_scale (k : ℤ) (h : List ℤ) : (scale k h).length = h.length := by simp [scale]

theorem hv_scale (k : ℤ) : ∀ (h : List ℤ) (u v : ℝ), hv (scale k h) u v = k * hv h u v
  | [], _, _ => by simp [scale, hv]
  | c :: t, u, v => by
    have := hv_scale k t u v
    simp only [scale, List.map_cons, hv, List.length_map, Int.cast_mul] at *
    rw [this]; ring

theorem hv_snoc0 : ∀ (h : List ℤ) (u v : ℝ), hv (h ++ [0]) u v = u * hv h u v
  | [], _, _ => by simp [hv]
  | c :: t, u, v => by
    have := hv_snoc0 t u v
    simp only [List.cons_append, hv, List.length_append, List.length_singleton, this]
    ring

theorem length_mulLin (A B : ℤ) (h : List ℤ) : (mulLin A B h).length = h.length + 1 := by
  unfold mulLin
  rw [length_add _ _ (by simp [length_scale])]
  simp [length_scale]

theorem hv_mulLin (A B : ℤ) (h : List ℤ) (u v : ℝ) :
    hv (mulLin A B h) u v = (A * u + B * v) * hv h u v := by
  unfold mulLin
  rw [hv_add _ _ _ _ (by simp [length_scale]), hv_scale, hv_scale, hv_snoc0]
  simp only [hv, Int.cast_zero, zero_mul, zero_add]
  ring

theorem length_mpow (D : ℤ) : ∀ n, (mpow D n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [mpow, length_mulLin, length_mpow D n]

theorem hv_mpow (D : ℤ) (u v : ℝ) : ∀ n, hv (mpow D n) u v = (D * (u + v)) ^ n
  | 0 => by simp [mpow, hv]
  | n + 1 => by rw [mpow, hv_mulLin, hv_mpow D u v n]; ring

theorem length_bern (A B D : ℤ) : ∀ cs : List ℤ, cs ≠ [] → (bern A B D cs).length = cs.length
  | [c], _ => rfl
  | c :: d :: t, _ => by
    have ih := length_bern A B D (d :: t) (by simp)
    simp only [bern]
    rw [length_add _ _ (by rw [length_scale, length_mpow, length_mulLin, ih])]
    simp [length_scale, length_mpow]

/-- The homogenization identity, on `u + v = 1`. -/
theorem hv_bern (A B D : ℤ) (u v : ℝ) (huv : u + v = 1) :
    ∀ cs : List ℤ, cs ≠ [] →
      hv (bern A B D cs) u v = (D : ℝ) ^ (cs.length - 1) * eval cs ((A * u + B * v) / D) ∨ (D : ℝ) = 0
  | [c], _ => by left; simp [bern, hv, eval]
  | c :: d :: t, _ => by
    by_cases hD : (D : ℝ) = 0
    · right; exact hD
    left
    have ih := hv_bern A B D u v huv (d :: t) (by simp)
    rcases ih with ih | ih
    · simp only [bern]
      have hl : (scale c (mpow D (d :: t).length)).length = (mulLin A B (bern A B D (d :: t))).length := by
        rw [length_scale, length_mpow, length_mulLin, length_bern A B D (d :: t) (by simp)]
      rw [hv_add _ _ _ _ hl, hv_scale, hv_mpow, hv_mulLin, ih, huv]
      simp only [eval, List.length_cons, Nat.add_sub_cancel]
      field_simp
      ring
    · exact absurd ih hD

/-! ## Positivity -/

theorem hv_nonneg : ∀ (h : List ℤ) (u v : ℝ), 0 ≤ u → 0 ≤ v → (∀ c ∈ h, 0 ≤ c) → 0 ≤ hv h u v
  | [], _, _, _, _, _ => by simp [hv]
  | c :: t, u, v, hu, hv0, hc => by
    simp only [hv]
    have h1 : (0 : ℝ) ≤ c := by exact_mod_cast hc c (by simp)
    have h2 := hv_nonneg t u v hu hv0 (fun d hd => hc d (by simp [hd]))
    positivity

theorem hv_pos : ∀ (h : List ℤ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 → h ≠ [] →
    (∀ c ∈ h, 0 < c) → 0 < hv h u v
  | [c], u, v, _, _, _, _, hc => by simp [hv]; exact_mod_cast hc c (by simp)
  | c :: d :: t, u, v, hu, hv0, huv, _, hc => by
    rw [hv]
    have h1 : (0 : ℝ) < c := by exact_mod_cast hc c (by simp)
    have ih := hv_pos (d :: t) u v hu hv0 huv (by simp) (fun e he => hc e (by simp [he]))
    rcases hu.eq_or_lt with h0 | h0
    · subst h0
      have : v = 1 := by linarith
      subst this
      have : (0 : ℝ) ^ (d :: t).length = 0 := by simp
      rw [this]; simpa using ih
    · have h2 : 0 ≤ v * hv (d :: t) u v :=
        mul_nonneg hv0 (hv_nonneg _ u v hu hv0 (fun e he => (hc e (by simp [he])).le))
      have h3 : 0 < (c : ℝ) * u ^ (d :: t).length := by positivity
      linarith

theorem allPos_spec (h : List ℤ) (H : allPos h = true) : ∀ c ∈ h, 0 < c := by
  simpa [allPos] using H

/-- A leaf: positive homogenized coefficients give positivity on `[A/D, B/D]`. -/
theorem leaf_sound (cs : List ℤ) (A B D : ℤ) (hcs : cs ≠ []) (hD : 0 < D) (hAB : A < B)
    (H : allPos (bern A B D cs) = true) (x : ℝ) (h1 : (A : ℝ) / D ≤ x) (h2 : x ≤ (B : ℝ) / D) :
    0 < eval cs x := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hABr : (A : ℝ) < B := by exact_mod_cast hAB
  have hBA : (0 : ℝ) < B - A := by linarith
  set u := ((B : ℝ) - D * x) / (B - A)
  set v := ((D : ℝ) * x - A) / (B - A)
  have hx1 : (A : ℝ) ≤ D * x := by rw [div_le_iff₀ hDr] at h1; linarith
  have hx2 : (D : ℝ) * x ≤ B := by rw [le_div_iff₀ hDr] at h2; linarith
  have hu : 0 ≤ u := div_nonneg (by linarith) hBA.le
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hBA.le
  have huv : u + v = 1 := by simp only [u, v]; field_simp; ring
  have hx : (A * u + B * v) / D = x := by simp only [u, v]; field_simp; ring
  have hpos := hv_pos (bern A B D cs) u v hu hv0 huv
    (by intro e; have := length_bern A B D cs hcs; rw [e] at this; simp at this; exact hcs (List.eq_nil_of_length_eq_zero this.symm))
    (allPos_spec _ H)
  rcases hv_bern A B D u v huv cs hcs with e | e
  · rw [e, hx] at hpos
    have : (0 : ℝ) < (D : ℝ) ^ (cs.length - 1) := by positivity
    exact pos_of_mul_pos_right hpos this.le
  · exact absurd e hDr.ne'

/-- A certificate proves positivity on the whole interval. -/
theorem check_sound (cs : List ℤ) (hcs : cs ≠ []) :
    ∀ (c : Cert) (A B D : ℤ), 0 < D → A < B → check cs A B D c = true →
      ∀ x : ℝ, (A : ℝ) / D ≤ x → x ≤ (B : ℝ) / D → 0 < eval cs x
  | .leaf, A, B, D, hD, hAB, H, x, h1, h2 => leaf_sound cs A B D hcs hD hAB H x h1 h2
  | .split l r, A, B, D, hD, hAB, H, x, h1, h2 => by
    simp only [check, Bool.and_eq_true] at H
    have hD2 : (0 : ℤ) < 2 * D := by omega
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    by_cases hm : x ≤ ((A + B : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ)
    · refine check_sound cs hcs l (2 * A) (A + B) (2 * D) hD2 (by omega) H.1 x ?_ hm
      push_cast; rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]; exact h1
    · refine check_sound cs hcs r (A + B) (2 * B) (2 * D) hD2 (by omega) H.2 x (le_of_lt (not_le.mp hm)) ?_
      push_cast; rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]; exact h2

end PolyPos
