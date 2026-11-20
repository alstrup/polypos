import PolyPos.Tactic
open Lean Meta PolyPos.MultiMeta PolyPos.Multi
def countC {k : ℕ} : MCert k → ℕ × ℕ
  | .leaf _ => (1, 1)
  | .split _ _ l r => let (a, b) := countC l; let (c, d) := countC r; (a + c, b + d + 1)
def run (name : String) (k : ℕ) (p : MP) (ds : List ℕ) (lo hi : List ℚ) : IO Unit := do
  let (H, _) := rootTensor p lo.toArray hi.toArray ds
  let root : F k := buildF k ds (fun β => H.getD β 0)
  match search k ds root lo hi 0 20000 .greedy with
  | (.ok w, _) => IO.println s!"{name}: (leaves, nodes) = {countC w}"
  | _ => IO.println s!"{name}: none"
def V (k i : ℕ) := mpVar k i
#eval do
  let x := V 2 0; let y := V 2 1
  run "motzkin2" 2 (mpAdd (mpAdd (mpAdd (mpMul (mpPow 2 x 4) (mpPow 2 y 2)) (mpMul (mpPow 2 x 2) (mpPow 2 y 4)))
    (mpScale (-3) (mpMul (mpPow 2 x 2) (mpPow 2 y 2)))) (mpConst 2 (1 + 1/100))) [4, 4] [-1, -1] [1, 1]
  let x := V 3 0; let y := V 3 1; let z := V 3 2
  run "quadratic - xyz" 3 (mpAdd (mpAdd (mpAdd (mpPow 3 x 2) (mpPow 3 y 2)) (mpAdd (mpPow 3 z 2)
    (mpScale (-1) (mpMul (mpMul x y) z)))) (mpConst 3 (1/50))) [2, 2, 2] [-1, -1, -1] [1, 1, 1]
  run "motzkin3" 3 (mpAdd (mpAdd (mpAdd (mpMul (mpPow 3 x 4) (mpPow 3 y 2)) (mpMul (mpPow 3 y 4) (mpPow 3 z 2)))
    (mpAdd (mpMul (mpPow 3 z 4) (mpPow 3 x 2)) (mpScale (-3) (mpMul (mpMul (mpPow 3 x 2) (mpPow 3 y 2)) (mpPow 3 z 2)))))
    (mpConst 3 (1/10))) [4, 4, 4] [-1, -1, -1] [1, 1, 1]
