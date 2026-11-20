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

theorem hv_pos : ∀ (h : List ℤ) (u v : ℝ), 0 ≤ u → 0 ≤ v → 0 < u + v → h ≠ [] →
    (∀ c ∈ h, 0 < c) → 0 < hv h u v
  | [c], u, v, _, _, _, _, hc => by simp [hv]; exact_mod_cast hc c (by simp)
  | c :: d :: t, u, v, hu, hv0, huv, _, hc => by
    rw [hv]
    have h1 : (0 : ℝ) < c := by exact_mod_cast hc c (by simp)
    have ih := hv_pos (d :: t) u v hu hv0 huv (by simp) (fun e he => hc e (by simp [he]))
    rcases hu.eq_or_lt with h0 | h0
    · subst h0
      have hv1 : 0 < v := by linarith
      have : (0 : ℝ) ^ (d :: t).length = 0 := by simp
      rw [this, mul_zero, zero_add]; exact mul_pos hv1 ih
    · have h2 : 0 ≤ v * hv (d :: t) u v := mul_nonneg hv0 ih.le
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
  have hpos := hv_pos (bern A B D cs) u v hu hv0 (by linarith)
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

/-! ## Faster checking: subdivide the form itself (de Casteljau)

On the left half the form becomes `H(2u + v, v)`, on the right half `H(u, u + 2v)`;
both are computed from the parent's coefficients, so `bern` runs once, at the root. -/

/-- `H(u, u + 2v)`. -/
def subR : List ℤ → List ℤ
  | [] => []
  | c :: t => add (c :: List.replicate t.length 0) (mulLin 1 2 (subR t))

/-- `H(2u + v, v)`, by symmetry. -/
def subL (h : List ℤ) : List ℤ := (subR h.reverse).reverse

def checkF : List ℤ → Cert → Bool
  | h, .leaf => allPos h
  | h, .split l r => checkF (subL h) l && checkF (subR h) r

/-- The fast checker: homogenize once, then subdivide the form. -/
def checkFast (cs : List ℤ) (A B D : ℤ) (c : Cert) : Bool := checkF (bern A B D cs) c

theorem hv_replicate0 : ∀ (m : ℕ) (u v : ℝ), hv (List.replicate m 0) u v = 0
  | 0, _, _ => rfl
  | m + 1, u, v => by simp [List.replicate_succ, hv, hv_replicate0 m u v]

theorem length_subR : ∀ h : List ℤ, (subR h).length = h.length
  | [] => rfl
  | c :: t => by
    simp only [subR]
    rw [length_add _ _ (by simp [length_mulLin, length_subR t])]
    simp

theorem hv_subR : ∀ (h : List ℤ) (u v : ℝ), hv (subR h) u v = hv h u (u + 2 * v)
  | [] , _, _ => rfl
  | c :: t, u, v => by
    simp only [subR]
    rw [hv_add _ _ _ _ (by simp [length_mulLin, length_subR t]), hv_mulLin, hv_subR t u v]
    simp only [hv, List.length_replicate, hv_replicate0, mul_zero, add_zero]
    push_cast; ring

theorem hv_append1 : ∀ (s : List ℤ) (c : ℤ) (u v : ℝ),
    hv (s ++ [c]) u v = u * hv s u v + c * v ^ s.length
  | [], c, u, v => by simp [hv]
  | a :: s, c, u, v => by
    simp only [List.cons_append, hv, List.length_append, hv_append1 s c u v, List.length_cons,
      List.length_nil, pow_zero, mul_one]
    ring

theorem hv_reverse : ∀ (h : List ℤ) (u v : ℝ), hv h.reverse u v = hv h v u
  | [], _, _ => rfl
  | c :: t, u, v => by
    rw [List.reverse_cons, hv_append1, hv_reverse t u v, List.length_reverse, hv]
    ring

theorem hv_subL (h : List ℤ) (u v : ℝ) : hv (subL h) u v = hv h (v + 2 * u) v := by
  rw [subL, hv_reverse, hv_subR, hv_reverse]

theorem length_subL (h : List ℤ) : (subL h).length = h.length := by
  simp [subL, length_subR]

/-- A passing `checkF` makes the form positive on the closed quadrant, away from the origin. -/
theorem checkF_sound : ∀ (c : Cert) (h : List ℤ), h ≠ [] → checkF h c = true →
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → 0 < u + v → 0 < hv h u v
  | .leaf, h, hne, H, u, v, hu, hv0, huv => hv_pos h u v hu hv0 huv hne (allPos_spec h H)
  | .split l r, h, hne, H, u, v, hu, hv0, huv => by
    simp only [checkF, Bool.and_eq_true] at H
    have neL : subL h ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero (by
      rw [← length_subL h, e]; rfl))
    have neR : subR h ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero (by
      rw [← length_subR h, e]; rfl))
    by_cases hc : v ≤ u
    · have := checkF_sound l (subL h) neL H.1 ((u - v) / 2) v (by linarith) hv0 (by linarith)
      rwa [hv_subL, show v + 2 * ((u - v) / 2) = u by ring] at this
    · have := checkF_sound r (subR h) neR H.2 u ((v - u) / 2) hu (by linarith) (by linarith)
      rwa [hv_subR, show u + 2 * ((v - u) / 2) = v by ring] at this

theorem checkFast_sound (cs : List ℤ) (hcs : cs ≠ []) (c : Cert) (A B D : ℤ) (hD : 0 < D)
    (hAB : A < B) (H : checkFast cs A B D c = true) (x : ℝ) (h1 : (A : ℝ) / D ≤ x)
    (h2 : x ≤ (B : ℝ) / D) : 0 < eval cs x := by
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
  have hne : bern A B D cs ≠ [] := fun e => hcs (List.eq_nil_of_length_eq_zero (by
    rw [← length_bern A B D cs hcs, e]; rfl))
  have hpos := checkF_sound c _ hne H u v hu hv0 (by linarith)
  rcases hv_bern A B D u v huv cs hcs with e | e
  · rw [e, hx] at hpos
    have : (0 : ℝ) < (D : ℝ) ^ (cs.length - 1) := by positivity
    exact pos_of_mul_pos_right hpos this.le
  · exact absurd e hDr.ne'

/-! ## Kernel-friendly checking

Two things make `decide +kernel` fast:
* every piece's coefficients are literals in the certificate, so the kernel checks
  `subL parent = left` and never rebuilds a chain of lazy subdivisions;
* the functions the kernel runs are written with `List.rec` directly, not through
  structural recursion (`brecOn`), which the kernel reduces slowly.

Each kernel function is proved equal to the reference definition above. -/

noncomputable def addK : List ℤ → List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => List ℤ → List ℤ) (fun t => t)
    (fun a s ih t => @List.casesOn ℤ (fun _ => List ℤ) t (a :: s) (fun b t' => (a + b) :: ih t'))
noncomputable def mapK (f : ℤ → ℤ) : List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => List ℤ) [] (fun a _ ih => f a :: ih)
noncomputable def revAux : List ℤ → List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => List ℤ → List ℤ) (fun acc => acc) (fun a _ ih acc => ih (a :: acc))
noncomputable def revK (l : List ℤ) : List ℤ := revAux l []
noncomputable def zerosK : List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => List ℤ) [] (fun _ _ ih => 0 :: ih)
noncomputable def mulLinK (h : List ℤ) : List ℤ := addK (h ++ [0]) (0 :: mapK (2 * ·) h)
noncomputable def subRK : List ℤ → List ℤ :=
  @List.rec ℤ (fun _ => List ℤ) [] (fun c t ih => addK (c :: zerosK t) (mulLinK ih))
noncomputable def subLK (h : List ℤ) : List ℤ := revK (subRK (revK h))
noncomputable def allPosK : List ℤ → Bool :=
  @List.rec ℤ (fun _ => Bool) true (fun c _ ih => decide (0 < c) && ih)
noncomputable def beqK : List ℤ → List ℤ → Bool :=
  @List.rec ℤ (fun _ => List ℤ → Bool)
    (fun t => @List.casesOn ℤ (fun _ => Bool) t true (fun _ _ => false))
    (fun a _ ih t => @List.casesOn ℤ (fun _ => Bool) t false (fun b t' => decide (a = b) && ih t'))

theorem addK_eq : ∀ s t : List ℤ, addK s t = add s t
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by
    show (a + b) :: addK s t = (a + b) :: add s t
    rw [addK_eq s t]

theorem mapK_eq (f : ℤ → ℤ) : ∀ l, mapK f l = l.map f
  | [] => rfl
  | a :: l => by show f a :: mapK f l = _; rw [mapK_eq f l]; rfl

theorem revAux_eq : ∀ l acc : List ℤ, revAux l acc = l.reverse ++ acc
  | [], _ => rfl
  | a :: l, acc => by show revAux l (a :: acc) = _; rw [revAux_eq l]; simp

theorem revK_eq (l : List ℤ) : revK l = l.reverse := by simp [revK, revAux_eq]

theorem zerosK_eq : ∀ t : List ℤ, zerosK t = List.replicate t.length 0
  | [] => rfl
  | _ :: t => by show 0 :: zerosK t = _; rw [zerosK_eq t]; rfl

theorem mulLinK_eq (h : List ℤ) : mulLinK h = mulLin 1 2 h := by
  simp [mulLinK, mulLin, addK_eq, mapK_eq, scale]

theorem subRK_eq : ∀ h : List ℤ, subRK h = subR h
  | [] => rfl
  | c :: t => by
    show addK (c :: zerosK t) (mulLinK (subRK t)) = _
    rw [addK_eq, zerosK_eq, mulLinK_eq, subRK_eq t]; rfl

theorem subLK_eq (h : List ℤ) : subLK h = subL h := by simp [subLK, subL, revK_eq, subRK_eq]

theorem allPosK_eq : ∀ h : List ℤ, allPosK h = allPos h
  | [] => rfl
  | c :: t => by
    show (decide (0 < c) && allPosK t) = _
    rw [allPosK_eq t]; simp [allPos]

theorem beqK_eq : ∀ s t : List ℤ, beqK s t = true → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [beqK] at h
  | _ :: _, [], h => by simp [beqK] at h
  | a :: s, b :: t, h => by
    change (decide (a = b) && beqK s t) = true at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, beqK_eq s t h.2]

/-- A certificate that carries every piece's coefficients. -/
inductive WCert where
  | leaf : List ℤ → WCert
  | split : List ℤ → WCert → WCert → WCert

noncomputable def WCert.formK : WCert → List ℤ :=
  @WCert.rec (fun _ => List ℤ) (fun h => h) (fun h _ _ _ _ => h)

noncomputable def checkWK : WCert → Bool :=
  @WCert.rec (fun _ => Bool) (fun h => allPosK h)
    (fun h l r il ir => beqK (subLK h) l.formK && beqK (subRK h) r.formK && il && ir)

/-- The checker the tactic uses. -/
noncomputable def checkWit (cs : List ℤ) (A B D : ℤ) (w : WCert) : Bool :=
  beqK (bern A B D cs) w.formK && checkWK w

theorem checkWK_sound : ∀ w : WCert, w.formK ≠ [] → checkWK w = true →
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → 0 < u + v → 0 < hv w.formK u v
  | .leaf h, hne, H, u, v, hu, hv0, huv =>
    hv_pos h u v hu hv0 huv hne (allPos_spec h (by rw [← allPosK_eq]; exact H))
  | .split h l r, hne, H, u, v, hu, hv0, huv => by
    change (beqK (subLK h) l.formK && beqK (subRK h) r.formK && checkWK l && checkWK r) = true at H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨⟨eL, eR⟩, HL⟩, HR⟩ := H
    have eL := beqK_eq _ _ eL; have eR := beqK_eq _ _ eR
    rw [subLK_eq] at eL; rw [subRK_eq] at eR
    change h ≠ [] at hne
    change 0 < hv h u v
    have neL : l.formK ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero (by
      rw [← length_subL h, eL, e]; rfl))
    have neR : r.formK ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero (by
      rw [← length_subR h, eR, e]; rfl))
    by_cases hc : v ≤ u
    · have := checkWK_sound l neL HL ((u - v) / 2) v (by linarith) hv0 (by linarith)
      rwa [← eL, hv_subL, show v + 2 * ((u - v) / 2) = u by ring] at this
    · have := checkWK_sound r neR HR u ((v - u) / 2) hu (by linarith) (by linarith)
      rwa [← eR, hv_subR, show u + 2 * ((v - u) / 2) = v by ring] at this

theorem checkWit_sound (cs : List ℤ) (hcs : cs ≠ []) (w : WCert) (A B D : ℤ) (hD : 0 < D)
    (hAB : A < B) (H : checkWit cs A B D w = true) (x : ℝ) (h1 : (A : ℝ) / D ≤ x)
    (h2 : x ≤ (B : ℝ) / D) : 0 < eval cs x := by
  simp only [checkWit, Bool.and_eq_true] at H
  have e0 := beqK_eq _ _ H.1
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
  have hne : w.formK ≠ [] := fun e => hcs (List.eq_nil_of_length_eq_zero (by
    rw [← length_bern A B D cs hcs, e0, e]; rfl))
  have hpos := checkWK_sound w hne H.2 u v hu hv0 (by linarith)
  rw [← e0] at hpos
  rcases hv_bern A B D u v huv cs hcs with e | e
  · rw [e, hx] at hpos
    have : (0 : ℝ) < (D : ℝ) ^ (cs.length - 1) := by positivity
    exact pos_of_mul_pos_right hpos this.le
  · exact absurd e hDr.ne'

end PolyPos
