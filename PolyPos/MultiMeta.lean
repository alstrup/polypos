import PolyPos.Multi

/-!
# Meta code for `poly_pos` in several variables

Reads the goal as a polynomial in `x₀, …, x_{k-1}`, maps the box to `[0,1]^k`, homogenizes
each variable to its degree, searches for a halving tree whose leaves have positive
coefficients, and closes the goal with `PolyPos.Multi.check_sound`. The link between the
starting form and the goal is proved by `ring`; the tree by `decide +kernel`.
-/

namespace PolyPos.MultiMeta
open Lean Meta Elab Tactic Qq PolyPos.Multi

/-! ## Polynomials: exponent vector ↦ rational coefficient -/

abbrev MP := Std.HashMap (List ℕ) ℚ

def addTerm (p : MP) (e : List ℕ) (c : ℚ) : MP :=
  let c' := p.getD e 0 + c
  if c' == 0 then p.erase e else p.insert e c'

def mpAdd (p q : MP) : MP := q.fold (fun acc e c => addTerm acc e c) p
def mpScale (s : ℚ) (p : MP) : MP :=
  if s == 0 then {} else p.fold (fun acc e c => acc.insert e (s * c)) {}
def mpMul (p q : MP) : MP :=
  p.fold (fun acc e1 c1 => q.fold (fun acc e2 c2 =>
    addTerm acc (List.zipWith (· + ·) e1 e2) (c1 * c2)) acc) {}
def mpConst (k : ℕ) (c : ℚ) : MP := if c == 0 then {} else ({} : MP).insert (List.replicate k 0) c
def mpVar (k i : ℕ) : MP := ({} : MP).insert ((List.range k).map fun j => if j == i then 1 else 0) 1
def mpPow (k : ℕ) (p : MP) : ℕ → MP
  | 0 => mpConst k 1
  | n + 1 => mpMul p (mpPow k p n)

def constQ (e : Expr) : MetaM (Option ℚ) := do
  try
    let e' : Q(ℝ) := e
    let r ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) e'
    return r.toRat
  catch _ => return none

def hasVar (xs : Array Expr) (e : Expr) : Bool := xs.any fun x => e.containsFVar x.fvarId!

partial def reify (xs : Array Expr) (e : Expr) : MetaM MP := do
  let k := xs.size
  if let some i := xs.findIdx? (· == e) then return mpVar k i
  if !hasVar xs e then
    if let some q ← constQ e then return mpConst k q
    throwError "poly_pos: {e} is not a rational constant"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return mpAdd (← reify xs a) (← reify xs b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return mpAdd (← reify xs a) (mpScale (-1) (← reify xs b))
  | (``Neg.neg, #[_, _, a]) => return mpScale (-1) (← reify xs a)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return mpMul (← reify xs a) (← reify xs b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    if hasVar xs b then throwError "poly_pos: division by {b}, which depends on a variable"
    match ← constQ b with
    | some c => if c == 0 then throwError "poly_pos: division by zero" else
        return mpScale (1 / c) (← reify xs a)
    | none => throwError "poly_pos: {b} is not a rational constant"
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    match (← whnfR (← instantiateMVars n)).nat? <|> n.nat? with
    | some m => return mpPow k (← reify xs a) m
    | none =>
      match ← (do let r ← Mathlib.Meta.NormNum.derive (α := q(ℕ)) n; pure r.toRat) with
      | some m => if m.den == 1 && 0 ≤ m.num then return mpPow k (← reify xs a) m.num.toNat
                  else throwError "poly_pos: exponent {n} is not a natural number"
      | none => throwError "poly_pos: exponent {n} is not a natural number literal"
  | _ => throwError "poly_pos: cannot read {e} as a polynomial"

/-! ## The starting form on a box -/

/-- All index vectors `β` with `lo ≤ β ≤ hi` componentwise. -/
def boxIdx : List ℕ → List ℕ → List (List ℕ)
  | l :: ls, h :: hs => (List.range (h + 1 - l)).flatMap fun i => (boxIdx ls hs).map ((l + i) :: ·)
  | _, _ => [[]]

/-- `p` on the box `[lo, hi]`, as integer coefficients of `Π u_i^(d_i-β_i) v_i^(β_i)`
indexed by `β`, and the positive scale `L` with `form = L · p`. -/
def rootTensor (p : MP) (lo hi : Array ℚ) (ds : List ℕ) : Std.HashMap (List ℕ) ℤ × ℕ := Id.run do
  let k := lo.size
  -- x_i = lo_i + (hi_i - lo_i) t_i
  let lins := (List.range k).map fun i => mpAdd (mpConst k lo[i]!) (mpScale (hi[i]! - lo[i]!) (mpVar k i))
  let q : MP := p.fold (fun acc α c =>
    mpAdd acc (mpScale c ((List.zip lins α).foldl (fun m (lin, a) => mpMul m (mpPow k lin a)) (mpConst k 1)))) {}
  -- t^α ↦ Π v^α (u + v)^(d - α)
  let mut H : Std.HashMap (List ℕ) ℚ := {}
  for (α, c) in q.toList do
    for β in boxIdx α ds do
      let w := ((ds.zip α).zip β).foldl (fun acc ((d, a), b) => acc * (Nat.choose (d - a) (b - a) : ℚ)) 1
      H := H.insert β (H.getD β 0 + c * w)
  let L : ℕ := H.fold (fun l _ q => Nat.lcm l q.den) 1
  return (H.fold (fun acc β q => acc.insert β (q * (L : ℚ)).num) {}, L)

def buildF : (k : ℕ) → List ℕ → (List ℕ → ℤ) → F k
  | 0, _, f => (f [] : ℤ)
  | _ + 1, [], _ => ([] : List _)
  | k + 1, d :: ds, f => (List.range (d + 1)).map fun i => buildF k ds (fun rest => f (i :: rest))

def getF : (k : ℕ) → F k → List ℕ → ℤ
  | 0, a, _ => (show ℤ from a)
  | _ + 1, _, [] => 0
  | k + 1, h, i :: is => match (show List (F k) from h)[i]? with
    | some a => getF k a is
    | none => 0

/-! ## Search (untrusted; the kernel re-checks) -/

inductive MFound (k : ℕ) where
  | ok : MCert k → MFound k
  | fails : List ℚ → MFound k
  | deep : MFound k

instance (k : ℕ) : Inhabited (MFound k) := ⟨.deep⟩

/-- The corners of the box, as index vectors and points. -/
def corners : List ℕ → List ℚ → List ℚ → List (List ℕ × List ℚ)
  | d :: ds, l :: ls, h :: hs =>
    (corners ds ls hs).flatMap fun (is, xs) => [(0 :: is, l :: xs), (d :: is, h :: xs)]
  | _, _, _ => [([], [])]

/-- The number of non-positive coefficients. -/
def badF : (k : ℕ) → F k → ℕ
  | 0, a => if (show ℤ from a) ≤ 0 then 1 else 0
  | k + 1, h => (show List (F k) from h).foldl (fun n a => n + badF k a) 0

/-- How to pick the variable to halve. -/
inductive Pick where
  | cyclic   -- the variables in turn
  | greedy   -- the one whose halves keep the fewest non-positive coefficients

/-- Search with a budget of pieces. -/
partial def search (k : ℕ) (ds : List ℕ) (h : F k) (lo hi : List ℚ) (j : ℕ) (fuel : ℕ)
    (pick : Pick := .greedy) : MFound k × ℕ :=
  if allPosF k h then (.ok (.leaf h), fuel)
  else match (corners ds lo hi).find? (fun (is, _) => getF k h is ≤ 0) with
  | some (_, pt) => (.fails pt, fuel)
  | none =>
    if fuel == 0 then (.deep, 0) else
    let live := (List.range k).filter (fun i => ds[i]! > 0)
    let j := match pick with
      | .cyclic => (List.range k).map (fun i => (j + i) % k) |>.find? (fun i => ds[i]! > 0) |>.getD j
      | .greedy =>
        let score := fun i => badF k (subLF k i h) + badF k (subRF k i h)
        let cyc := (List.range k).map (fun i => (j + i) % k) |>.find? (fun i => ds[i]! > 0) |>.getD j
        let best := live.foldl (fun b i => if score i < score b then i else b) cyc
        -- greedy only while it makes progress; otherwise take the variables in turn
        if score best < 2 * badF k h then best else cyc
    let mid := (lo[j]! + hi[j]!) / 2
    let (l, f1) := search k ds (subLF k j h) lo (hi.set j mid) (j + 1) (fuel - 1) pick
    match l with
    | .ok cl =>
      let (r, f2) := search k ds (subRF k j h) (lo.set j mid) hi (j + 1) f1 pick
      match r with
      | .ok cr => (.ok (.split j h cl cr), f2)
      | other => (other, f2)
    | other => (other, f1)

/-! ## Syntax -/

def intSyntax (n : ℤ) : MetaM Term :=
  if n < 0 then `(- $(Syntax.mkNumLit (toString n.natAbs))) else pure (Syntax.mkNumLit (toString n))

def ratSyntax (q : ℚ) : MetaM Term := do
  if q.den == 1 then intSyntax q.num
  else `(($(← intSyntax q.num) / $(Syntax.mkNumLit (toString q.den)) : ℝ))

def fSyntax : (k : ℕ) → F k → MetaM Term
  | 0, a => intSyntax (show ℤ from a)
  | k + 1, h => do
    let xs : Array Term ← (show List (F k) from h).toArray.mapM (fSyntax k)
    `([$xs,*])

partial def certSyntax (k : ℕ) : MCert k → MetaM Term
  | .leaf h => do `(PolyPos.Multi.MCert.leaf $(← fSyntax k h))
  | .split j h l r => do
    `(PolyPos.Multi.MCert.split $(Syntax.mkNumLit (toString j)) $(← fSyntax k h)
        $(← certSyntax k l) $(← certSyntax k r))

/-! ## Terms, built directly (no elaboration of large literals) -/

def tyE : ℕ → Expr
  | 0 => mkConst ``Int
  | k + 1 => mkApp (mkConst ``List [levelZero]) (tyE k)

def listE (T : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [levelZero]) T a acc)
    (mkApp (mkConst ``List.nil [levelZero]) T)

def fE : (k : ℕ) → F k → Expr
  | 0, a => toExpr (show ℤ from a)
  | k + 1, h => listE (tyE k) ((show List (F k) from h).map (fE k))

def certE (k : ℕ) : MCert k → Expr
  | .leaf h => mkApp2 (mkConst ``PolyPos.Multi.MCert.leaf) (toExpr k) (fE k h)
  | .split j h l r => mkApp5 (mkConst ``PolyPos.Multi.MCert.split) (toExpr k) (toExpr j) (fE k h)
      (certE k l) (certE k r)

/-! ## The proof -/

/-- Prove `0 < e` for a polynomial `e` in the variables `xs`, on the box `[lo, hi]`. -/
def prove (e : Expr) (xs : Array Expr) (lo hi : Array ℚ) : TacticM Unit := withMainContext do
  let k := xs.size
  let p ← reify xs e
  let ds : List ℕ := (List.range k).map fun i => p.fold (fun m α _ => max m α[i]!) 0
  let (H, L) := rootTensor p lo hi ds
  let root : F k := buildF k ds (fun β => H.getD β 0)
  let w ← match search k ds root lo.toList hi.toList 0 20000 with
    | (.ok w, _) => pure w
    | (.fails pt, _) =>
      throwError "poly_pos: the polynomial is not positive at {(xs.toList.zip pt).map fun (x, q) => m!"{x} = {q}"}"
    | (.deep, _) => throwError "poly_pos: no certificate within 20000 pieces"
  let kS := Syntax.mkNumLit (toString k)
  let dsElems : Array Term := ds.toArray.map fun d => Syntax.mkNumLit (toString d)
  let dsS ← `([$dsElems,*])
  let rootS ← Term.exprToSyntax (fE k root)
  let wS ← Term.exprToSyntax (certE k w)
  let mut pts : Array Term := #[]
  let mut valid : Term ← `(trivial)
  for i in (List.range k).reverse do
    let x ← Term.exprToSyntax xs[i]!
    let a ← ratSyntax lo[i]!
    let b ← ratSyntax hi[i]!
    pts := pts.push (← `(($(Syntax.mkNumLit (toString ds[i]!)), ($b - $x) / ($b - $a), ($x - $a) / ($b - $a))))
    valid ← `(⟨PolyPos.Multi.box_valid $a $b $x (by norm_num) (by linarith) (by linarith), $valid⟩)
  let ptsR := pts.reverse
  let psS ← `(([$ptsR,*] : PolyPos.Multi.Pt))
  let eS ← Term.exprToSyntax e
  let lS := Syntax.mkNumLit (toString L)
  evalTactic (← `(tactic| (
    have hpos : 0 < PolyPos.Multi.ev $kS ($rootS : PolyPos.Multi.F $kS) $psS :=
      PolyPos.Multi.checkK_sound $kS $dsS ($wS : PolyPos.Multi.MCert $kS) (by decide +kernel) $psS rfl
        $valid
    have key : PolyPos.Multi.ev $kS ($rootS : PolyPos.Multi.F $kS) $psS = ($lS : ℝ) * $eS := by
      simp only [PolyPos.Multi.ev, PolyPos.Multi.hvN, List.map]; push_cast; ring
    rw [key] at hpos
    exact pos_of_mul_pos_right hpos (by norm_num))))

end PolyPos.MultiMeta
