import PolyPos.Tactic
open Lean Meta PolyPos.MultiMeta PolyPos.Multi

def countC {k : ℕ} : MCert k → ℕ × ℕ
  | .leaf _ => (1, 1)
  | .split _ _ l r => let (a, b) := countC l; let (c, d) := countC r; (a + c, b + d + 1)
def depthC {k : ℕ} : MCert k → ℕ
  | .leaf _ => 0
  | .split _ _ l r => max (depthC l) (depthC r) + 1

/-- The fewest leaves within depth D: memo on (box, D); a box is each variable's (level, index). -/
partial def opt (k : ℕ) (ds : List ℕ) (h : F k) (box : List (ℕ × ℕ)) (D : ℕ) :
    StateM (Std.HashMap (List (ℕ × ℕ) × ℕ) ℕ) ℕ := do
  if let some v := (← get)[(box, D)]? then return v
  let inf := 1000000000
  let v ← if allPosF k h then pure 1 else if D == 0 then pure inf else do
    let mut best := inf
    for j in List.range k do
      if ds[j]! == 0 then continue
      let (l, i) := box[j]!
      let a ← opt k ds (subLF k j h) (box.set j (l + 1, 2 * i)) (D - 1)
      if a ≥ best then continue
      let b ← opt k ds (subRF k j h) (box.set j (l + 1, 2 * i + 1)) (D - 1)
      best := min best (a + b)
    pure best
  modify (·.insert (box, D) v)
  return v

def run (name : String) (k : ℕ) (p : MP) (ds : List ℕ) (lo hi : List ℚ) (D : ℕ) : IO Unit := do
  let (H, _) := rootTensor p lo.toArray hi.toArray ds
  let root : F k := buildF k ds (fun β => H.getD β 0)
  let g := match search k ds root lo hi 0 20000 .greedy with
    | (.ok w, _) => s!"{countC w} depth {depthC w}" | _ => "none"
  let c := match search k ds root lo hi 0 20000 .cyclic with
    | (.ok w, _) => s!"{countC w}" | _ => "none"
  let t0 ← IO.monoMsNow
  let (o, st) := (opt k ds root ((List.range k).map fun _ => (0, 0)) D).run {}
  let t1 ← IO.monoMsNow
  IO.println s!"{name}: cyclic (leaves, nodes) {c}; greedy {g}; optimal within depth {D}: {o} leaves ({st.size} states, {t1 - t0} ms)"

def V (k i : ℕ) := mpVar k i
#eval do
  let x := V 2 0; let y := V 2 1
  -- a ring valley: (x² + y² − 1/2)² + 1/100
  let r := mpAdd (mpAdd (mpPow 2 x 2) (mpPow 2 y 2)) (mpConst 2 (-1/2))
  run "ring valley" 2 (mpAdd (mpPow 2 r 2) (mpConst 2 (1/100))) [4, 4] [-1, -1] [1, 1] 16
  -- a curved valley: (x − y²)² + (y − 1/3)²/10 + 1/1000
  let a := mpAdd x (mpScale (-1) (mpPow 2 y 2))
  let b := mpAdd y (mpConst 2 (-1/3))
  run "curved valley" 2 (mpAdd (mpAdd (mpPow 2 a 2) (mpScale (1/10) (mpPow 2 b 2))) (mpConst 2 (1/1000))) [2, 4] [-1, -1] [1, 1] 18
