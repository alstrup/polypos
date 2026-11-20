import Mathlib

/-!
# PolyPos.Multi: positivity of a polynomial in several variables on a box

A form in `k` variables is a nested list: `F 0 = ℤ`, `F (k+1) = List (F k)`. With a degree
`n` and a pair `(u, v)` for each variable, it denotes
`Σ h_i u^(n-i) v^i` at the outer level, each `h_i` evaluated on the remaining variables.

A certificate is a tree of halvings. Each node carries its form; halving variable `j`
substitutes `(u, v) ↦ (2u + v, v)` on the left and `(u, u + 2v)` on the right in that variable.
At the leaves every coefficient is positive, and then the form is positive wherever every
pair has `u, v ≥ 0` and `u + v > 0`.
-/

namespace PolyPos.Multi

@[reducible] def F : ℕ → Type
  | 0 => ℤ
  | k + 1 => List (F k)

/-! ## Operations on lists, generic in the element type -/

def addL {α : Type} (f : α → α → α) : List α → List α → List α
  | a :: s, b :: t => f a b :: addL f s t
  | s, [] => s
  | [], t => t

/-- Multiply by `u + 2v`: the `u` part keeps the indices, the `v` part shifts them. -/
def mulLinG {α : Type} (add : α → α → α) (dbl : α → α) (z : α) (h : List α) : List α :=
  addL add (h ++ [z]) (z :: h.map dbl)

/-- `H(u, u + 2v)`. -/
def subRG {α : Type} (add : α → α → α) (dbl : α → α) (z : α) : List α → List α
  | [] => []
  | c :: t => addL add (c :: List.replicate t.length z) (mulLinG add dbl z (subRG add dbl z t))

/-! ## Operations on forms -/

def addF : (k : ℕ) → F k → F k → F k
  | 0, a, b => (show ℤ from a) + (show ℤ from b)
  | k + 1, s, t => addL (addF k) s t

def dblF : (k : ℕ) → F k → F k
  | 0, a => 2 * (show ℤ from a)
  | k + 1, s => List.map (dblF k) (show List (F k) from s)

def zeroF : (k : ℕ) → F k
  | 0 => (0 : ℤ)
  | _ + 1 => ([] : List _)

/-- Halve variable `j`, right half. -/
def subRF : (k : ℕ) → ℕ → F k → F k
  | 0, _, a => a
  | k + 1, 0, h => subRG (addF k) (dblF k) (zeroF k) h
  | k + 1, j + 1, h => List.map (subRF k j) (show List (F k) from h)

/-- Halve variable `j`, left half (by symmetry). -/
def subLF : (k : ℕ) → ℕ → F k → F k
  | 0, _, a => a
  | k + 1, 0, h => (subRG (addF k) (dblF k) (zeroF k) (show List (F k) from h).reverse).reverse
  | k + 1, j + 1, h => List.map (subLF k j) (show List (F k) from h)

/-- Every level `i` has exactly `d_i + 1` entries. -/
def wf : (k : ℕ) → F k → List ℕ → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => false
  | k + 1, h, d :: ds => (show List (F k) from h).length == d + 1 && (show List (F k) from h).all (wf k · ds)

def allPosF : (k : ℕ) → F k → Bool
  | 0, a => decide (0 < (show ℤ from a))
  | k + 1, h => (show List (F k) from h).all (allPosF k)

def beqL {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: s, b :: t => f a b && beqL f s t
  | _, _ => false

theorem beqL_eq {α : Type} (f : α → α → Bool) (hf : ∀ a b, f a b = true → a = b) :
    ∀ s t : List α, beqL f s t = true → s = t
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
    simp only [beqL, Bool.and_eq_true] at h
    rw [hf a b h.1, beqL_eq f hf s t h.2]
  | [], _ :: _, h => by simp [beqL] at h
  | _ :: _, [], h => by simp [beqL] at h

def beqF : (k : ℕ) → F k → F k → Bool
  | 0, a, b => decide ((show ℤ from a) = (show ℤ from b))
  | k + 1, s, t => beqL (beqF k) s t

theorem beqF_eq : ∀ (k : ℕ) (a b : F k), beqF k a b = true → a = b
  | 0, _, _, h => of_decide_eq_true h
  | k + 1, s, t, h => beqL_eq (beqF k) (beqF_eq k) s t h

/-! ## Evaluation -/

/-- `Σ r_i u^(n-i) v^i` for a list of reals: degree `n`, given explicitly. -/
def hvN : ℕ → List ℝ → ℝ → ℝ → ℝ
  | _, [], _, _ => 0
  | n, c :: t, u, v => c * u ^ n + v * hvN (n - 1) t u v

/-- A point: for each variable, its degree and its pair `(u, v)`. -/
abbrev Pt := List (ℕ × ℝ × ℝ)

def ev : (k : ℕ) → F k → Pt → ℝ
  | 0, a, _ => ((show ℤ from a) : ℝ)
  | _ + 1, _, [] => 0
  | k + 1, h, (n, u, v) :: ps => hvN n ((show List (F k) from h).map (ev k · ps)) u v

/-! ## Lemmas about `hvN` -/

section hvN

theorem hvN_add : ∀ (n : ℕ) (s t : List ℝ) (u v : ℝ),
    hvN n (addL (· + ·) s t) u v = hvN n s u v + hvN n t u v
  | _, [], [], _, _ => by simp [addL, hvN]
  | _, [], _ :: _, _, _ => by simp [addL, hvN]
  | _, _ :: _, [], _, _ => by simp [addL, hvN]
  | n, a :: s, b :: t, u, v => by
    simp only [addL, hvN, hvN_add (n - 1) s t u v]; ring

theorem hvN_dbl : ∀ (n : ℕ) (s : List ℝ) (u v : ℝ), hvN n (s.map (2 * ·)) u v = 2 * hvN n s u v
  | _, [], _, _ => by simp [hvN]
  | n, a :: s, u, v => by simp only [List.map_cons, hvN, hvN_dbl (n - 1) s u v]; ring

theorem hvN_replicate0 : ∀ (n m : ℕ) (u v : ℝ), hvN n (List.replicate m 0) u v = 0
  | _, 0, _, _ => rfl
  | n, m + 1, u, v => by simp [List.replicate_succ, hvN, hvN_replicate0 (n - 1) m u v]

theorem hvN_append1 : ∀ (n : ℕ) (s : List ℝ) (c u v : ℝ),
    hvN n (s ++ [c]) u v = hvN n s u v + c * u ^ (n - s.length) * v ^ s.length
  | n, [], c, u, v => by simp [hvN]
  | n, a :: s, c, u, v => by
    simp only [List.cons_append, hvN, List.length_cons]
    rw [hvN_append1 (n - 1) s c u v, show n - 1 - s.length = n - (s.length + 1) by omega, pow_succ]
    ring

/-- A form of degree `n - 1` read at degree `n` gains a factor `u`. -/
theorem hvN_raise : ∀ (n : ℕ) (s : List ℝ) (u v : ℝ), s.length ≤ n →
    hvN n s u v = u * hvN (n - 1) s u v
  | _, [], _, _, _ => by simp [hvN]
  | 0, _ :: _, _, _, h => by simp at h
  | n + 1, c :: t, u, v, h => by
    have ht : t.length ≤ n := by simpa using h
    simp only [hvN, Nat.add_sub_cancel]
    rw [hvN_raise n t u v ht]
    cases n with
    | zero => simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp ht), hvN, mul_comm]
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring

theorem hvN_shift (n : ℕ) (s : List ℝ) (u v : ℝ) : hvN n (0 :: s) u v = v * hvN (n - 1) s u v := by
  simp [hvN]

theorem hvN_reverse : ∀ (n : ℕ) (s : List ℝ) (u v : ℝ), s.length = n + 1 →
    hvN n s.reverse u v = hvN n s v u
  | _, [], _, _, h => by simp at h
  | n, c :: t, u, v, h => by
    have ht : t.length = n := by simpa using h
    rw [List.reverse_cons, hvN_append1, List.length_reverse, ht, Nat.sub_self, pow_zero, mul_one]
    simp only [hvN]
    cases n with
    | zero =>
      simp [List.length_eq_zero_iff.mp ht, hvN]
    | succ m =>
      rw [hvN_raise (m + 1) t.reverse u v (by simp [ht]), Nat.add_sub_cancel,
        hvN_reverse m t u v ht]
      ring

theorem hvN_nonneg : ∀ (n : ℕ) (s : List ℝ) (u v : ℝ), 0 ≤ u → 0 ≤ v → (∀ c ∈ s, 0 ≤ c) →
    0 ≤ hvN n s u v
  | _, [], _, _, _, _, _ => by simp [hvN]
  | n, c :: t, u, v, hu, hv, hc => by
    simp only [hvN]
    have h1 : 0 ≤ c := hc c (by simp)
    have h2 := hvN_nonneg (n - 1) t u v hu hv (fun d hd => hc d (by simp [hd]))
    positivity

theorem hvN_pos : ∀ (n : ℕ) (s : List ℝ) (u v : ℝ), 0 ≤ u → 0 ≤ v → 0 < u + v →
    s.length = n + 1 → (∀ c ∈ s, 0 < c) → 0 < hvN n s u v
  | _, [], _, _, _, _, _, h, _ => by simp at h
  | n, c :: t, u, v, hu, hv, huv, hl, hc => by
    have ht : t.length = n := by simpa using hl
    simp only [hvN]
    have h1 : 0 < c := hc c (by simp)
    have hn := hvN_nonneg (n - 1) t u v hu hv (fun d hd => (hc d (by simp [hd])).le)
    rcases hu.eq_or_lt with h0 | h0
    · subst h0
      have hv1 : 0 < v := by linarith
      cases n with
      | zero => simp only [pow_zero, mul_one]; positivity
      | succ m =>
        have ih := hvN_pos m t 0 v le_rfl hv huv (by simpa using ht)
          (fun d hd => hc d (by simp [hd]))
        simp only [Nat.add_sub_cancel, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          not_false_eq_true, zero_pow, mul_zero, zero_add]
        exact mul_pos hv1 ih
    · have : 0 < c * u ^ n := by positivity
      have : 0 ≤ v * hvN (n - 1) t u v := mul_nonneg hv hn
      linarith

end hvN

/-! ## Generic operations map to real ones -/

section generic
variable {α : Type} (add : α → α → α) (dbl : α → α) (z : α) (e : α → ℝ)
  (hadd : ∀ a b, e (add a b) = e a + e b) (hdbl : ∀ a, e (dbl a) = 2 * e a) (hz : e z = 0)
include hadd

theorem map_addL : ∀ s t : List α, (addL add s t).map e = addL (· + ·) (s.map e) (t.map e)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by simp [addL, hadd, map_addL s t]

omit hadd in
theorem length_addL : ∀ s t : List α, (addL add s t).length = max s.length t.length
  | [], [] => rfl
  | [], _ :: _ => by simp [addL]
  | _ :: _, [] => by simp [addL]
  | a :: s, b :: t => by simp [addL, length_addL s t, Nat.succ_max_succ]

omit hadd in
theorem length_subRG : ∀ h : List α, (subRG add dbl z h).length = h.length
  | [] => rfl
  | c :: t => by
    simp only [subRG, mulLinG, length_addL, List.length_cons, List.length_replicate,
      List.length_append, List.length_map, List.length_nil, length_subRG t]
    omega

include hdbl hz

theorem map_subRG : ∀ h : List α,
    (subRG add dbl z h).map e = subRG (· + ·) (2 * ·) 0 (h.map e)
  | [] => rfl
  | c :: t => by
    have hmd : ∀ X : List α, (X.map dbl).map e = (X.map e).map (2 * ·) := fun X => by
      simp [List.map_map, Function.comp_def, hdbl]
    simp only [subRG, mulLinG, map_addL add e hadd, List.map_cons, List.map_replicate, hz,
      List.map_append, hmd, map_subRG t, List.length_map, List.map_nil]

end generic

/-- The real identity behind halving: `H(u, u + 2v)`. -/
theorem hvN_subR : ∀ (n : ℕ) (r : List ℝ) (u v : ℝ), r.length ≤ n + 1 →
    hvN n (subRG (· + ·) (2 * ·) 0 r) u v = hvN n r u (u + 2 * v)
  | _, [], _, _, _ => rfl
  | n, c :: t, u, v, hl => by
    have ht : t.length ≤ n := by simpa using hl
    have hlen : (subRG (· + ·) (2 * ·) (0 : ℝ) t).length = t.length := length_subRG _ _ _ t
    have ih : hvN (n - 1) (subRG (· + ·) (2 * ·) 0 t) u v = hvN (n - 1) t u (u + 2 * v) := by
      cases n with
      | zero => rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp ht)]; rfl
      | succ m => exact hvN_subR m t u v (by simpa using ht)
    simp only [subRG, mulLinG]
    rw [hvN_add, hvN_add, hvN_shift, hvN_dbl, hvN_append1,
      hvN_raise n (subRG (· + ·) (2 * ·) 0 t) u v (by rw [hlen]; exact ht), ih]
    simp only [hvN, hvN_replicate0]
    ring

/-! ## Evaluation is linear -/

theorem ev_add : ∀ (k : ℕ) (a b : F k) (ps : Pt), ev k (addF k a b) ps = ev k a ps + ev k b ps
  | 0, a, b, _ => by simp [ev, addF]
  | _ + 1, _, _, [] => by simp [ev]
  | k + 1, s, t, (n, u, v) :: ps => by
    simp only [ev, addF]
    rw [map_addL (addF k) (ev k · ps) (fun a b => ev_add k a b ps), hvN_add]

theorem ev_dbl : ∀ (k : ℕ) (a : F k) (ps : Pt), ev k (dblF k a) ps = 2 * ev k a ps
  | 0, a, _ => by simp [ev, dblF]
  | _ + 1, _, [] => by simp [ev]
  | k + 1, s, (n, u, v) :: ps => by
    simp only [ev, dblF, List.map_map]
    rw [show (fun a => ev k a ps) ∘ dblF k = (2 * ·) ∘ (fun a => ev k a ps) by
      funext a; simp [ev_dbl k a ps]]
    rw [← List.map_map, hvN_dbl]

theorem ev_zero : ∀ (k : ℕ) (ps : Pt), ev k (zeroF k) ps = 0
  | 0, _ => by simp [ev, zeroF]
  | _ + 1, [] => by simp [ev]
  | _ + 1, (n, u, v) :: ps => by simp [ev, zeroF, hvN]

/-! ## Halving -/

/-- Change the `j`-th entry of a list. -/
def mdf {α : Type} (f : α → α) : ℕ → List α → List α
  | 0, [] => []
  | _ + 1, [] => []
  | 0, a :: l => f a :: l
  | j + 1, a :: l => a :: mdf f j l

def rightPt : ℕ × ℝ × ℝ → ℕ × ℝ × ℝ := fun ⟨n, u, v⟩ => (n, u, u + 2 * v)
def leftPt : ℕ × ℝ × ℝ → ℕ × ℝ × ℝ := fun ⟨n, u, v⟩ => (n, v + 2 * u, v)

theorem wf_mem {k : ℕ} {h : List (F k)} {d : ℕ} {ds : List ℕ} (H : wf (k + 1) h (d :: ds) = true) :
    h.length = d + 1 ∧ ∀ a ∈ h, wf k a ds = true := by
  simp only [wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at H
  exact H

theorem ev_subR : ∀ (k j : ℕ) (h : F k) (ds : List ℕ) (ps : Pt), wf k h ds = true →
    ps.map Prod.fst = ds → ev k (subRF k j h) ps = ev k h (mdf rightPt j ps)
  | 0, _, _, _, _, _, _ => by simp [ev, subRF]
  | _ + 1, _, _, [], _, H, _ => by simp [wf] at H
  | _ + 1, _, _, _ :: _, [], _, hd => by simp at hd
  | k + 1, 0, h, d :: ds, (n, u, v) :: ps, H, hd => by
    obtain ⟨hl, _⟩ := wf_mem H
    simp only [List.map_cons, List.cons.injEq] at hd
    simp only [ev, subRF, mdf, rightPt]
    rw [map_subRG (addF k) (dblF k) (zeroF k) (ev k · ps) (fun a b => ev_add k a b ps)
      (fun a => ev_dbl k a ps) (ev_zero k ps), hvN_subR]
    simp [hl, hd.1]
  | k + 1, j + 1, h, d :: ds, (n, u, v) :: ps, H, hd => by
    obtain ⟨_, hall⟩ := wf_mem H
    simp only [List.map_cons, List.cons.injEq] at hd
    simp only [ev, subRF, mdf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ev_subR k j a ds ps (hall a ha) hd.2

theorem ev_subL : ∀ (k j : ℕ) (h : F k) (ds : List ℕ) (ps : Pt), wf k h ds = true →
    ps.map Prod.fst = ds → ev k (subLF k j h) ps = ev k h (mdf leftPt j ps)
  | 0, _, _, _, _, _, _ => by simp [ev, subLF]
  | _ + 1, _, _, [], _, H, _ => by simp [wf] at H
  | _ + 1, _, _, _ :: _, [], _, hd => by simp at hd
  | k + 1, 0, h, d :: ds, (n, u, v) :: ps, H, hd => by
    obtain ⟨hl, _⟩ := wf_mem H
    simp only [List.map_cons, List.cons.injEq] at hd
    have hl' : (h.map (ev k · ps)).length = n + 1 := by simp [hl, hd.1]
    simp only [ev, subLF, mdf, leftPt]
    rw [List.map_reverse, map_subRG (addF k) (dblF k) (zeroF k) (ev k · ps)
      (fun a b => ev_add k a b ps) (fun a => ev_dbl k a ps) (ev_zero k ps), List.map_reverse,
      hvN_reverse _ _ _ _ (by rw [length_subRG, List.length_reverse, hl']),
      hvN_subR _ _ _ _ (by rw [List.length_reverse, hl']), hvN_reverse _ _ _ _ hl']
  | k + 1, j + 1, h, d :: ds, (n, u, v) :: ps, H, hd => by
    obtain ⟨_, hall⟩ := wf_mem H
    simp only [List.map_cons, List.cons.injEq] at hd
    simp only [ev, subLF, mdf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ev_subL k j a ds ps (hall a ha) hd.2

/-! ## Leaves -/

/-- Every pair has `u, v ≥ 0` and `u + v > 0`. -/
def Valid : Pt → Prop
  | [] => True
  | (_, u, v) :: ps => (0 ≤ u ∧ 0 ≤ v ∧ 0 < u + v) ∧ Valid ps

theorem ev_pos : ∀ (k : ℕ) (h : F k) (ds : List ℕ) (ps : Pt), wf k h ds = true →
    allPosF k h = true → ps.map Prod.fst = ds → Valid ps → 0 < ev k h ps
  | 0, a, _, _, _, H, _, _ => by simpa [ev, allPosF] using H
  | _ + 1, _, [], _, W, _, _, _ => by simp [wf] at W
  | _ + 1, _, _ :: _, [], _, _, hd, _ => by simp at hd
  | k + 1, h, d :: ds, (n, u, v) :: ps, W, H, hd, ⟨⟨hu, hv, huv⟩, hps⟩ => by
    obtain ⟨hl, hall⟩ := wf_mem W
    simp only [List.map_cons, List.cons.injEq] at hd
    simp only [allPosF, List.all_eq_true] at H
    simp only [ev]
    apply hvN_pos n _ u v hu hv huv (by simp [hl, hd.1])
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact ev_pos k a ds ps (hall a ha) (H a ha) hd.2 hps

/-! ## Certificates -/

inductive MCert (k : ℕ) where
  | leaf : F k → MCert k
  | split : ℕ → F k → MCert k → MCert k → MCert k

def MCert.form {k : ℕ} : MCert k → F k
  | .leaf h => h
  | .split _ h _ _ => h

def check (k : ℕ) (ds : List ℕ) : MCert k → Bool
  | .leaf h => wf k h ds && allPosF k h
  | .split j h l r =>
    wf k h ds && beqF k (subLF k j h) l.form && beqF k (subRF k j h) r.form &&
      check k ds l && check k ds r

/-- The `j`-th entry, or a dummy. -/
def getPt : ℕ → Pt → ℕ × ℝ × ℝ
  | 0, [] => (0, 1, 1)
  | _ + 1, [] => (0, 1, 1)
  | 0, p :: _ => p
  | j + 1, _ :: l => getPt j l

theorem mdf_map_fst : ∀ (j : ℕ) (q : ℕ × ℝ × ℝ) (ps : Pt), q.1 = (getPt j ps).1 →
    (mdf (fun _ => q) j ps).map Prod.fst = ps.map Prod.fst
  | 0, _, [], _ => rfl
  | _ + 1, _, [], _ => rfl
  | 0, q, p :: l, h => by simp [mdf, getPt] at *; exact h
  | j + 1, q, p :: l, h => by simp [mdf, getPt] at *; exact mdf_map_fst j q l h

theorem mdf_mdf {α : Type} (f g : α → α) : ∀ (j : ℕ) (l : List α), mdf f j (mdf g j l) = mdf (f ∘ g) j l
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | j + 1, a :: l => by simp [mdf, mdf_mdf f g j l]

theorem mdf_get : ∀ (j : ℕ) (ps : Pt) (f : ℕ × ℝ × ℝ → ℕ × ℝ × ℝ), f (getPt j ps) = getPt j ps →
    mdf f j ps = ps
  | 0, [], _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | 0, p :: l, f, h => by simp [mdf, getPt] at *; exact h
  | j + 1, p :: l, f, h => by simp [mdf, getPt] at *; exact mdf_get j l f h

theorem valid_mdf : ∀ (j : ℕ) (ps : Pt) (q : ℕ × ℝ × ℝ), Valid ps →
    (0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧ 0 < q.2.1 + q.2.2) → Valid (mdf (fun _ => q) j ps)
  | 0, [], _, h, _ => h
  | _ + 1, [], _, h, _ => h
  | 0, _ :: l, ⟨n, u, v⟩, ⟨_, hl⟩, hq => ⟨hq, hl⟩
  | j + 1, _ :: l, q, ⟨hp, hl⟩, hq => ⟨hp, valid_mdf j l q hl hq⟩

theorem getPt_valid : ∀ (j : ℕ) (ps : Pt), Valid ps →
    0 ≤ (getPt j ps).2.1 ∧ 0 ≤ (getPt j ps).2.2 ∧ 0 < (getPt j ps).2.1 + (getPt j ps).2.2
  | 0, [], _ => by simp [getPt]
  | _ + 1, [], _ => by simp [getPt]
  | 0, (_, _, _) :: _, ⟨h, _⟩ => h
  | j + 1, _ :: l, ⟨_, h⟩ => getPt_valid j l h

theorem check_sound (k : ℕ) (ds : List ℕ) : ∀ (w : MCert k), check k ds w = true →
    ∀ ps : Pt, ps.map Prod.fst = ds → Valid ps → 0 < ev k w.form ps
  | .leaf h, H, ps, hd, hv => by
    simp only [check, Bool.and_eq_true] at H
    exact ev_pos k h ds ps H.1 H.2 hd hv
  | .split j h l r, H, ps, hd, hv => by
    simp only [check, Bool.and_eq_true] at H
    obtain ⟨⟨⟨⟨W, eL⟩, eR⟩, HL⟩, HR⟩ := H
    have eL := beqF_eq _ _ _ eL
    have eR := beqF_eq _ _ _ eR
    show 0 < ev k h ps
    have hp := getPt_valid j ps hv
    rcases hq : getPt j ps with ⟨n, u, v⟩
    rw [hq] at hp
    obtain ⟨hu, hv0, huv⟩ := hp
    by_cases hc : v ≤ u
    · -- the left half, at (n, (u - v)/2, v)
      let q : ℕ × ℝ × ℝ := (n, (u - v) / 2, v)
      have hd' : (mdf (fun _ => q) j ps).map Prod.fst = ds := by
        rw [← hd]; exact mdf_map_fst j q ps (by rw [hq])
      have := check_sound k ds l HL _ hd'
        (valid_mdf j ps q hv ⟨by simp only [q]; linarith, hv0, by simp only [q]; linarith⟩)
      rw [← eL, ev_subL k j h ds _ W hd', mdf_mdf] at this
      rwa [mdf_get j ps _ (by
        rw [hq]; simp only [Function.comp_apply, leftPt, q, Prod.mk.injEq, true_and, and_true]
        ring)] at this
    · -- the right half, at (n, u, (v - u)/2)
      let q : ℕ × ℝ × ℝ := (n, u, (v - u) / 2)
      have hd' : (mdf (fun _ => q) j ps).map Prod.fst = ds := by
        rw [← hd]; exact mdf_map_fst j q ps (by rw [hq])
      have := check_sound k ds r HR _ hd'
        (valid_mdf j ps q hv ⟨hu, by simp only [q]; linarith, by simp only [q]; linarith⟩)
      rw [← eR, ev_subR k j h ds _ W hd', mdf_mdf] at this
      rwa [mdf_get j ps _ (by
        rw [hq]; simp only [Function.comp_apply, rightPt, q, Prod.mk.injEq, true_and, and_true]
        ring)] at this

end PolyPos.Multi

namespace PolyPos.Multi

/-- The pair of a box coordinate: `u = (b - x)/(b - a)`, `v = (x - a)/(b - a)`. -/
theorem box_valid (a b x : ℝ) (hab : a < b) (h1 : a ≤ x) (h2 : x ≤ b) :
    0 ≤ (b - x) / (b - a) ∧ 0 ≤ (x - a) / (b - a) ∧ 0 < (b - x) / (b - a) + (x - a) / (b - a) := by
  have hw : 0 < b - a := by linarith
  refine ⟨div_nonneg (by linarith) hw.le, div_nonneg (by linarith) hw.le, ?_⟩
  rw [← add_div, show b - x + (x - a) = b - a by ring, div_self hw.ne']
  exact one_pos

end PolyPos.Multi

/-! ## Kernel versions

The same functions written with `List.rec` / `Nat.rec` / `MCert.rec` directly, which the
kernel reduces much faster than structural recursion (`brecOn`). Each is proved equal to the
reference definition, so `checkK_sound` follows from `check_sound`. -/

namespace PolyPos.Multi

section kernel
variable {α : Type}

noncomputable def addLK (f : α → α → α) : List α → List α → List α :=
  @List.rec α (fun _ => List α → List α) (fun t => t)
    (fun a s ih t => @List.casesOn α (fun _ => List α) t (a :: s) (fun b t' => f a b :: ih t'))
noncomputable def mapK {β : Type} (f : α → β) : List α → List β :=
  @List.rec α (fun _ => List β) [] (fun a _ ih => f a :: ih)
noncomputable def appK : List α → List α → List α :=
  @List.rec α (fun _ => List α → List α) (fun t => t) (fun a _ ih t => a :: ih t)
noncomputable def revAuxK : List α → List α → List α :=
  @List.rec α (fun _ => List α → List α) (fun acc => acc) (fun a _ ih acc => ih (a :: acc))
noncomputable def revK (l : List α) : List α := revAuxK l []
noncomputable def zerosK (z : α) : List α → List α :=
  @List.rec α (fun _ => List α) [] (fun _ _ ih => z :: ih)
noncomputable def lenK : List α → ℕ := @List.rec α (fun _ => ℕ) 0 (fun _ _ ih => ih + 1)
noncomputable def allK (p : α → Bool) : List α → Bool :=
  @List.rec α (fun _ => Bool) true (fun a _ ih => p a && ih)
noncomputable def beqLK (f : α → α → Bool) : List α → List α → Bool :=
  @List.rec α (fun _ => List α → Bool)
    (fun t => @List.casesOn α (fun _ => Bool) t true (fun _ _ => false))
    (fun a _ ih t => @List.casesOn α (fun _ => Bool) t false (fun b t' => f a b && ih t'))
noncomputable def mulLinGK (add : α → α → α) (dbl : α → α) (z : α) (h : List α) : List α :=
  addLK add (appK h [z]) (z :: mapK dbl h)
noncomputable def subRGK (add : α → α → α) (dbl : α → α) (z : α) : List α → List α :=
  @List.rec α (fun _ => List α) []
    (fun c t ih => addLK add (c :: zerosK z t) (mulLinGK add dbl z ih))

theorem addLK_eq (f : α → α → α) : ∀ s t : List α, addLK f s t = addL f s t
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by show f a b :: addLK f s t = _; rw [addLK_eq f s t]; rfl

theorem mapK_eq {β : Type} (f : α → β) : ∀ l, mapK f l = l.map f
  | [] => rfl
  | a :: l => by show f a :: mapK f l = _; rw [mapK_eq f l]; rfl

theorem appK_eq : ∀ s t : List α, appK s t = s ++ t
  | [], _ => rfl
  | a :: s, t => by show a :: appK s t = _; rw [appK_eq s t]; rfl

theorem revAuxK_eq : ∀ l acc : List α, revAuxK l acc = l.reverse ++ acc
  | [], _ => rfl
  | a :: l, acc => by show revAuxK l (a :: acc) = _; rw [revAuxK_eq l]; simp

theorem revK_eq (l : List α) : revK l = l.reverse := by simp [revK, revAuxK_eq]

theorem zerosK_eq (z : α) : ∀ t : List α, zerosK z t = List.replicate t.length z
  | [] => rfl
  | _ :: t => by show z :: zerosK z t = _; rw [zerosK_eq z t]; rfl

theorem lenK_eq : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => by show lenK l + 1 = _; rw [lenK_eq l]; rfl

theorem allK_eq (p : α → Bool) : ∀ l : List α, allK p l = l.all p
  | [] => rfl
  | a :: l => by show (p a && allK p l) = _; rw [allK_eq p l]; rfl

theorem beqLK_eq (f : α → α → Bool) : ∀ s t : List α, beqLK f s t = beqL f s t
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by show (f a b && beqLK f s t) = _; rw [beqLK_eq f s t]; rfl

theorem subRGK_eq (add : α → α → α) (dbl : α → α) (z : α) :
    ∀ h : List α, subRGK add dbl z h = subRG add dbl z h
  | [] => rfl
  | c :: t => by
    show addLK add (c :: zerosK z t) (mulLinGK add dbl z (subRGK add dbl z t)) = _
    rw [subRGK_eq add dbl z t, addLK_eq, zerosK_eq, mulLinGK, addLK_eq, appK_eq, mapK_eq]
    rfl

end kernel

noncomputable def addFK (k : ℕ) : F k → F k → F k :=
  @Nat.rec (fun k => F k → F k → F k) (fun a b => (show ℤ from a) + (show ℤ from b))
    (fun k ih => addLK ih) k
noncomputable def dblFK (k : ℕ) : F k → F k :=
  @Nat.rec (fun k => F k → F k) (fun a => 2 * (show ℤ from a)) (fun k ih => mapK ih) k
noncomputable def zeroFK (k : ℕ) : F k :=
  @Nat.rec (fun k => F k) (0 : ℤ) (fun _ _ => ([] : List _)) k
noncomputable def subRFK (k : ℕ) : ℕ → F k → F k :=
  @Nat.rec (fun k => ℕ → F k → F k) (fun _ a => a)
    (fun k ih j h => @Nat.casesOn (fun _ => F (k + 1)) j
      (subRGK (addFK k) (dblFK k) (zeroFK k) h) (fun j' => mapK (ih j') h)) k
noncomputable def subLFK (k : ℕ) : ℕ → F k → F k :=
  @Nat.rec (fun k => ℕ → F k → F k) (fun _ a => a)
    (fun k ih j h => @Nat.casesOn (fun _ => F (k + 1)) j
      (revK (subRGK (addFK k) (dblFK k) (zeroFK k) (revK h))) (fun j' => mapK (ih j') h)) k
noncomputable def wfK (k : ℕ) : F k → List ℕ → Bool :=
  @Nat.rec (fun k => F k → List ℕ → Bool) (fun _ _ => true)
    (fun k ih h ds => @List.casesOn ℕ (fun _ => Bool) ds false
      (fun d ds' => (lenK (show List (F k) from h) == d + 1) && allK (fun a => ih a ds') h)) k
noncomputable def allPosFK (k : ℕ) : F k → Bool :=
  @Nat.rec (fun k => F k → Bool) (fun a => decide (0 < (show ℤ from a))) (fun k ih h => allK ih h) k
noncomputable def beqFK (k : ℕ) : F k → F k → Bool :=
  @Nat.rec (fun k => F k → F k → Bool)
    (fun a b => decide ((show ℤ from a) = (show ℤ from b))) (fun k ih => beqLK ih) k

theorem addFK_eq : ∀ k, addFK k = addF k
  | 0 => rfl
  | k + 1 => by
    show addLK (addFK k) = _
    rw [addFK_eq k]; funext s t; rw [addLK_eq]; rfl

theorem dblFK_eq : ∀ k, dblFK k = dblF k
  | 0 => rfl
  | k + 1 => by
    show mapK (dblFK k) = _
    rw [dblFK_eq k]; funext s; rw [mapK_eq]; rfl

theorem zeroFK_eq : ∀ k, zeroFK k = zeroF k
  | 0 => rfl
  | _ + 1 => rfl

theorem subRFK_eq : ∀ k j (h : F k), subRFK k j h = subRF k j h
  | 0, _, _ => rfl
  | k + 1, 0, h => by
    show subRGK (addFK k) (dblFK k) (zeroFK k) h = _
    rw [subRGK_eq, addFK_eq, dblFK_eq, zeroFK_eq]; rfl
  | k + 1, j + 1, h => by
    show mapK (subRFK k j) h = _
    rw [mapK_eq]
    have : subRFK k j = subRF k j := funext (subRFK_eq k j)
    rw [this]; rfl

theorem subLFK_eq : ∀ k j (h : F k), subLFK k j h = subLF k j h
  | 0, _, _ => rfl
  | k + 1, 0, h => by
    show revK (subRGK (addFK k) (dblFK k) (zeroFK k) (revK h)) = _
    rw [revK_eq, subRGK_eq, addFK_eq, dblFK_eq, zeroFK_eq, revK_eq]; rfl
  | k + 1, j + 1, h => by
    show mapK (subLFK k j) h = _
    rw [mapK_eq]
    have : subLFK k j = subLF k j := funext (subLFK_eq k j)
    rw [this]; rfl

theorem wfK_eq : ∀ k (h : F k) ds, wfK k h ds = wf k h ds
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | k + 1, h, d :: ds => by
    show ((lenK (show List (F k) from h) == d + 1) && allK (fun a => wfK k a ds) h) = _
    rw [lenK_eq, allK_eq]
    have : (fun a => wfK k a ds) = (wf k · ds) := funext fun a => wfK_eq k a ds
    rw [this]; rfl

theorem allPosFK_eq : ∀ k (h : F k), allPosFK k h = allPosF k h
  | 0, _ => rfl
  | k + 1, h => by
    show allK (allPosFK k) h = _
    rw [allK_eq]
    have : allPosFK k = allPosF k := funext (allPosFK_eq k)
    rw [this]; rfl

theorem beqFK_eq : ∀ k (a b : F k), beqFK k a b = beqF k a b
  | 0, _, _ => rfl
  | k + 1, s, t => by
    show beqLK (beqFK k) s t = _
    have : beqFK k = beqF k := funext fun a => funext (beqFK_eq k a)
    rw [this, beqLK_eq]; rfl

noncomputable def MCert.formK {k : ℕ} : MCert k → F k :=
  @MCert.rec k (fun _ => F k) (fun h => h) (fun _ h _ _ _ _ => h)

noncomputable def checkK (k : ℕ) (ds : List ℕ) : MCert k → Bool :=
  @MCert.rec k (fun _ => Bool) (fun h => wfK k h ds && allPosFK k h)
    (fun j h l r il ir => wfK k h ds && beqFK k (subLFK k j h) l.formK &&
      beqFK k (subRFK k j h) r.formK && il && ir)

theorem formK_eq {k : ℕ} : ∀ w : MCert k, w.formK = w.form
  | .leaf _ => rfl
  | .split _ _ _ _ => rfl

theorem checkK_eq (k : ℕ) (ds : List ℕ) : ∀ w : MCert k, checkK k ds w = check k ds w
  | .leaf h => by
    show (wfK k h ds && allPosFK k h) = _
    rw [wfK_eq, allPosFK_eq]; rfl
  | .split j h l r => by
    show (wfK k h ds && beqFK k (subLFK k j h) l.formK && beqFK k (subRFK k j h) r.formK &&
      checkK k ds l && checkK k ds r) = _
    rw [wfK_eq, beqFK_eq, beqFK_eq, subLFK_eq, subRFK_eq, formK_eq, formK_eq, checkK_eq k ds l,
      checkK_eq k ds r]; rfl

theorem checkK_sound (k : ℕ) (ds : List ℕ) (w : MCert k) (H : checkK k ds w = true)
    (ps : Pt) (hd : ps.map Prod.fst = ds) (hv : Valid ps) : 0 < ev k w.form ps :=
  check_sound k ds w (by rw [← checkK_eq]; exact H) ps hd hv

end PolyPos.Multi
