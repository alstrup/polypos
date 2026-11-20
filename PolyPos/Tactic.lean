import PolyPos.Core

/-!
# The `poly_pos` tactic

Proves `0 < p x`, `p x > 0`, `q x < p x`, or the `≤` versions, for a polynomial in one real
variable `x`, when the context bounds `x` by rational constants (`a ≤ x`, `x ≤ b`, or `<`).

1. Read the goal as a polynomial with rational coefficients, and scale it to integers.
2. Search for a subdivision certificate, using the verified `PolyPos.bern`.
3. Close the goal with `PolyPos.check_sound`. Lean's kernel evaluates `check`; the search is
   not trusted.
-/

namespace PolyPos.Tactic
open Lean Meta Elab Tactic Qq

/-! ## Polynomials with rational coefficients, lowest degree first -/

abbrev QPoly := Array ℚ

def qadd (p q : QPoly) : QPoly :=
  (List.range (max p.size q.size)).toArray.map fun i => p.getD i 0 + q.getD i 0

def qmul (p q : QPoly) : QPoly := Id.run do
  if p.isEmpty || q.isEmpty then return #[]
  let mut r : QPoly := Array.replicate (p.size + q.size - 1) 0
  for i in [:p.size] do
    for j in [:q.size] do
      r := r.set! (i + j) (r[i + j]! + p[i]! * q[j]!)
  return r

def qpow (p : QPoly) : ℕ → QPoly
  | 0 => #[1]
  | n + 1 => qmul p (qpow p n)

def qtrim (p : QPoly) : QPoly := Id.run do
  let mut r := p
  while r.size > 1 && r.back! == 0 do r := r.pop
  return r

/-- A closed real constant, evaluated by `norm_num`. -/
def constQ (e : Expr) : MetaM (Option ℚ) := do
  try
    let e' : Q(ℝ) := e
    let r ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) e'
    return r.toRat
  catch _ => return none

/-- Read `e` as a polynomial in the variable `x`. -/
partial def reify (x e : Expr) : MetaM QPoly := do
  if e == x then return #[0, 1]
  if !e.containsFVar x.fvarId! then
    if let some q ← constQ e then return #[q]
    throwError "poly_pos: {e} is not a rational constant"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return qadd (← reify x a) (← reify x b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    return qadd (← reify x a) ((← reify x b).map (- ·))
  | (``Neg.neg, #[_, _, a]) => return (← reify x a).map (- ·)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return qmul (← reify x a) (← reify x b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    if b.containsFVar x.fvarId! then throwError "poly_pos: division by {b}, which depends on {x}"
    match ← constQ b with
    | some c => if c == 0 then throwError "poly_pos: division by zero" else
        return (← reify x a).map (· / c)
    | none => throwError "poly_pos: {b} is not a rational constant"
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    match (← whnfR (← instantiateMVars n)).nat? <|> n.nat? with
    | some k => return qpow (← reify x a) k
    | none =>
      match ← (do let r ← Mathlib.Meta.NormNum.derive (α := q(ℕ)) n; pure r.toRat) with
      | some k => if k.den == 1 && 0 ≤ k.num then return qpow (← reify x a) k.num.toNat
                  else throwError "poly_pos: exponent {n} is not a natural number"
      | none => throwError "poly_pos: exponent {n} is not a natural number literal"
  | _ => throwError "poly_pos: cannot read {e} as a polynomial in {x}"

/-! ## Certificate search (untrusted; the kernel re-checks) -/

/-- The search result: a certificate, or the reason there is none. -/
inductive Found where
  | ok : Cert → Found
  | fails : ℚ → Found       -- p is not positive at this point
  | deep : Found
  deriving Inhabited

/-- Search on the form `h` of the interval `[A/D, B/D]`, halving with `subL` / `subR`. -/
partial def searchF (h : List ℤ) (A B D : ℤ) (depth : ℕ) : Found :=
  if allPos h then .ok .leaf
  else if h.head! ≤ 0 then .fails (mkRat A D.toNat)
  else if h.getLast! ≤ 0 then .fails (mkRat B D.toNat)
  else if depth == 0 then .deep
  else
    match searchF (subL h) (2 * A) (A + B) (2 * D) (depth - 1) with
    | .ok l =>
      match searchF (subR h) (A + B) (2 * B) (2 * D) (depth - 1) with
      | .ok r => .ok (.split l r)
      | other => other
    | other => other

def search (cs : List ℤ) (A B D : ℤ) (depth : ℕ) : Found := searchF (bern A B D cs) A B D depth

def intSyntax (n : ℤ) : MetaM Term :=
  if n < 0 then `(- $(Syntax.mkNumLit (toString n.natAbs))) else pure (Syntax.mkNumLit (toString n))

def listSyntax (h : List ℤ) : MetaM Term := do
  let xs : Array Term ← h.toArray.mapM intSyntax
  `([$xs,*])

/-- The certificate with every piece's coefficients, for `checkWit`. -/
partial def witSyntax (h : List ℤ) : Cert → MetaM Term
  | .leaf => do `(PolyPos.WCert.leaf $(← listSyntax h))
  | .split l r => do
    `(PolyPos.WCert.split $(← listSyntax h) $(← witSyntax (subL h) l) $(← witSyntax (subR h) r))

/-! ## The tactic -/

/-- Rational bounds on `x` from the context: the tightest `a ≤ x` (or `a < x`) and `x ≤ b`. -/
def bounds (x : Expr) : MetaM (Option ℚ × Option ℚ) := do
  let mut lo : Option ℚ := none
  let mut hi : Option ℚ := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let rel : Option (Expr × Expr) := match t.getAppFnArgs with
      | (``LE.le, #[_, _, a, b]) => some (a, b)
      | (``LT.lt, #[_, _, a, b]) => some (a, b)
      | (``GE.ge, #[_, _, a, b]) => some (b, a)
      | (``GT.gt, #[_, _, a, b]) => some (b, a)
      | _ => none
    let some (a, b) := rel | continue
    if b == x && !a.containsFVar x.fvarId! then
      if let some q ← constQ a then lo := some (match lo with | some l => max l q | none => q)
    if a == x && !b.containsFVar x.fvarId! then
      if let some q ← constQ b then hi := some (match hi with | some h => min h q | none => q)
  return (lo, hi)

/-- The real variable of the goal: the one free variable of type `ℝ` in `e`. -/
def theVar (e : Expr) : MetaM Expr := do
  let fv := (collectFVars {} e).fvarIds
  let mut xs := #[]
  for f in fv do
    if ← isDefEq (← f.getType) q(ℝ) then xs := xs.push (mkFVar f)
  match xs.toList with
  | [x] => return x
  | [] => throwError "poly_pos: the goal has no real variable"
  | _ => throwError "poly_pos: the goal has several real variables {xs}; only one is supported"

/-- `poly_pos` proves that a polynomial in one real variable `x` is positive (or nonnegative)
on an interval given by hypotheses `a ≤ x` and `x ≤ b` with rational `a`, `b`. -/
elab "poly_pos" : tactic => withMainContext do
  -- normalize the goal to `0 < e`
  evalTactic (← `(tactic| try simp only [gt_iff_lt, ge_iff_le]))
  withMainContext do
  let g ← whnfR (← getMainTarget)
  match g.getAppFnArgs with
  | (``LE.le, #[_, _, _, _]) => evalTactic (← `(tactic| apply le_of_lt))
  | (``GE.ge, #[_, _, _, _]) => evalTactic (← `(tactic| apply le_of_lt))
  | _ => pure ()
  withMainContext do
  let g ← whnfR (← instantiateMVars (← getMainTarget))
  let (a, b) ← match g.getAppFnArgs with
    | (``LT.lt, #[_, _, a, b]) => pure (a, b)
    | (``GT.gt, #[_, _, a, b]) => pure (b, a)
    | _ => throwError "poly_pos: the goal must be `p < q`, `p ≤ q`, `p > q` or `p ≥ q`"
  unless ← isDefEq (← inferType a) q(ℝ) do throwError "poly_pos: the goal must be about real numbers"
  let e ← if (← constQ a) == some 0 then pure b else mkAppM ``HSub.hSub #[b, a]
  let x ← theVar e
  let p := qtrim (← reify x e)
  -- scale to integer coefficients
  let L : ℕ := p.foldl (fun l q => Nat.lcm l q.den) 1
  let cs : List ℤ := (p.map fun q => (q * (L : ℚ)).num).toList
  let (some lo, some hi) ← bounds x
    | throwError "poly_pos: needs hypotheses `a ≤ {x}` and `{x} ≤ b` with rational constants a, b"
  unless lo < hi do throwError "poly_pos: the interval [{lo}, {hi}] is empty or a single point"
  let D : ℕ := Nat.lcm lo.den hi.den
  let A : ℤ := (lo * D).num
  let B : ℤ := (hi * D).num
  let cert ← match search cs A B D 40 with
    | .ok c => pure c
    | .fails q => throwError "poly_pos: the polynomial is not positive at {x} = {q}"
    | .deep => throwError "poly_pos: no certificate within 40 halvings (a root, or a near root)"
  let csElems : Array Term ← cs.toArray.mapM (fun n => (intSyntax n : MetaM Term))
  let csS ← `([$csElems,*])
  let xS ← Term.exprToSyntax x
  let eS ← Term.exprToSyntax e
  let certS ← witSyntax (bern A B D cs) cert
  let aS ← intSyntax A
  let bS ← intSyntax B
  let dS ← intSyntax D
  let lS := Syntax.mkNumLit (toString L)
  if e != b then evalTactic (← `(tactic| rw [← sub_pos]))
  evalTactic (← `(tactic| (
    have hpos := PolyPos.checkWit_sound ($csS : List ℤ) (by simp) $certS ($aS : ℤ) ($bS : ℤ) ($dS : ℤ)
      (by norm_num) (by norm_num) (by decide +kernel) $xS (by norm_num <;> linarith)
      (by norm_num <;> linarith)
    have heq : PolyPos.eval ($csS : List ℤ) $xS = ($lS : ℝ) * $eS := by
      simp only [PolyPos.eval]; push_cast; ring
    rw [heq] at hpos
    exact pos_of_mul_pos_right hpos (by norm_num))))

end PolyPos.Tactic
