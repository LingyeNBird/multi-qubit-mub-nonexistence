import MultiQubitMUB.FourQubitContextualityCore

set_option linter.constructorNameAsVariable false

/-!
# Part 1: Complete `Q⁻(5,2)` Classification (`f₂₇ ≤ 13 ⇒ 3 Orbits`)

Proves `qminus52_le13_classified`: any 3-qubit sign assignment `s3` with
`frustPairs (Qminus c0_09) s3 ≤ 13 * 6` maps via an `O⁻(6,2)` transvection word
(preserving `Qminus c0_09`) and a 3-qubit gauge to one of the 3 canonical orbit
representatives `rep27[0..2]` (`f₂₇ = 9, 12, 13`).
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Pure-Computable `A₂₇`, `B₃₆`, `V₁₁`, `C₁₆`, and 16-Bit DPLL Verifier -/

def A27_list : List Nat := [2, 4, 6, 16, 19, 20, 23, 26, 27, 30, 31, 32, 34, 37, 39, 44, 45, 46, 47, 48, 51, 53, 54, 58, 59, 60, 61]
def B36_list : List Nat := [1, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 33, 35, 36, 38, 40, 41, 42, 43, 49, 50, 52, 55, 56, 57, 62, 63]
def V11_list : List Nat := [2, 4, 6, 32, 34, 37, 39, 44, 45, 46, 47]
def C16_list : List Nat := [16, 19, 20, 23, 26, 27, 30, 31, 48, 51, 53, 54, 58, 59, 60, 61]
def piv5_list : List Nat := [0, 1, 3, 5, 7]
def free6_list : List Nat := [2, 4, 6, 8, 9, 10]
def pivGauges_list : List Nat := [0, 16, 41, 57, 13, 29, 36, 52, 8, 24, 33, 49, 5, 21, 44, 60, 1, 17, 40, 56, 12, 28, 37, 53, 9, 25, 32, 48, 4, 20, 45, 61]
def orbRep_list : List Nat := [0, 1, 3, 7, 15, 31]

def rep27_vecs : List (List ℤ) := [
  [1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]

def A27_val (i : Nat) : Nat := A27_list.getD i 0
def B36_val (i : Nat) : Nat := B36_list.getD i 0
def V11_val (i : Nat) : Nat := V11_list.getD i 0
def C16_val (i : Nat) : Nat := C16_list.getD i 0
def rep27_val (r : Fin 3) (i : Nat) : ℤ := (rep27_vecs.getD r.val []).getD i 0

def a27ToP0_words : List (List Nat) := [
  [], [52, 50], [22, 18], [18], [17], [22], [21], [24], [25], [28], [29], [52, 22], [50, 18], [49, 22], [55, 18], [63, 17], [62, 17], [62, 18], [63, 18], [50], [49], [55], [52], [56], [57], [62], [63]
]

def v11Map_data : List (Nat × Nat × List Nat) := [
  (0, 0, []), (1, 0, []), (1, 36, [38]), (2, 0, []), (1, 0, [35]), (2, 5, [7]), (2, 0, [35]), (3, 0, []), (1, 41, [41]), (2, 0, [13]), (2, 41, [41]), (3, 8, [8]), (2, 8, [43, 5]), (3, 0, [13]), (3, 41, [41]), (4, 0, []), (1, 0, [42]), (2, 12, [14]), (2, 0, [42]), (3, 9, [11]), (2, 33, [40, 5]), (3, 12, [14]), (3, 0, [42]), (4, 1, [1]), (2, 1, [43, 12]), (3, 4, [14, 8]), (3, 8, [42, 8]), (4, 9, [11]), (3, 1, [43, 12]), (4, 12, [14]), (4, 0, [42]), (5, 0, []), (1, 41, [43]), (2, 0, [15]), (2, 41, [43]), (3, 8, [10]), (2, 8, [41, 5]), (3, 0, [15]), (3, 41, [43]), (4, 8, [5]), (0, 0, [1]), (1, 0, [1]), (1, 13, [36]), (2, 0, [1]), (1, 41, [33]), (2, 8, [5]), (2, 41, [33]), (3, 0, [1]), (2, 1, [41, 12]), (3, 1, [12, 8]), (3, 41, [40, 8]), (4, 1, [9]), (3, 1, [41, 12]), (4, 1, [12]), (4, 41, [40]), (5, 1, [1]), (1, 41, [40]), (2, 1, [12]), (2, 41, [40]), (3, 1, [9]), (2, 8, [42, 5]), (3, 1, [12]), (3, 41, [40]), (4, 0, [3])
]

/-- Precomputed 40 edges `(i, j, vp, g)` of `C₁₆` where `C16[i] ^^^ C16[j] = V11[vp]`. -/
def edges16_list : List (Nat × Nat × Nat × ℤ) :=
  ((List.range 16).flatMap fun i =>
    ((List.range 16).flatMap fun j =>
      if j ≤ i || symp3 (C16_val i) (C16_val j) != 0 then []
      else
        let r := C16_val i ^^^ C16_val j
        match V11_list.idxOf? r with
        | some vp => [(i, j, vp, gamma3_sgn (C16_val i) (C16_val j))]
        | none => []))

/-- Precomputed 5 lines `(a, b, c, g)` inside `V₁₁`. -/
def v11Lines_list : List (Nat × Nat × Nat × ℤ) :=
  ((List.range 11).flatMap fun i =>
    ((List.range 11).flatMap fun j =>
      if j ≤ i || symp3 (V11_val i) (V11_val j) != 0 then []
      else
        let r := V11_val i ^^^ V11_val j
        match V11_list.idxOf? r with
        | some k => if k ≤ j then [] else [(i, j, k, gamma3_sgn (V11_val i) (V11_val j))]
        | none => []))

/-- Sign vector on `V₁₁` for 6-bit mask `c ∈ 0..63` (pivots = +1, free6 = ±1). -/
def v11SignOfMask (c : Nat) (i : Nat) : ℤ :=
  match free6_list.idxOf? i with
  | some k => if ((c >>> k) &&& 1) == 1 then -1 else 1
  | none => 1

/-- Induced sign on `C₁₆` edge `(i, j)` for `V₁₁` mask `c` (`0` if non-edge). -/
def M16_val (c : Nat) (i j : Nat) : ℤ :=
  if i == j || symp3 (C16_val i) (C16_val j) != 0 then 0
  else
    let r := C16_val i ^^^ C16_val j
    match V11_list.idxOf? r with
    | some vp => gamma3_sgn (C16_val i) (C16_val j) * v11SignOfMask c vp
    | none => 0

def pop8 (x : Nat) : Nat :=
  let x := Nat.sub x (Nat.land (Nat.shiftRight x 1) 85)
  let x := Nat.add (Nat.land x 51) (Nat.land (Nat.shiftRight x 2) 51)
  Nat.land (Nat.add x (Nat.shiftRight x 4)) 15

def pop16 (m : Nat) : Nat :=
  Nat.add (pop8 (Nat.land m 255)) (pop8 (Nat.land (Nat.shiftRight m 8) 255))

def applyWord3Nat (us : List Nat) (s : Nat → ℤ) : Nat → ℤ :=
  us.foldl (fun cur u v =>
    let tv := transv3_pt u v
    transv3_sgn u v * cur tv) s

def applyGauge3Nat (g : Nat) (s : Nat → ℤ) (v : Nat) : ℤ :=
  (if symp3 g v == 0 then 1 else -1) * s v

inductive Tree16 where
  | S (u : Nat) (l r : Tree16)
  | D (v : Nat)
  | L (tris : List (Nat × Nat × Nat))
  | O (ridx gSol : Nat) (us : List Nat)

/-- Check edge-disjoint frustrated triangles on unassigned vertices of `C₁₆`. -/
def checkTris16 (c : Nat) (assignedMask : Nat) : List (Nat × Nat × Nat) → List (Nat × Nat) → Bool
  | [], _ => true
  | (a, b, d) :: rest, used =>
    let okV := a < 16 && b < 16 && d < 16 && a < b && b < d &&
      ((assignedMask >>> a) &&& 1 == 0) &&
      ((assignedMask >>> b) &&& 1 == 0) &&
      ((assignedMask >>> d) &&& 1 == 0)
    let okW := M16_val c a b * M16_val c b d * M16_val c a d == -1
    let e1 := (a, b); let e2 := (b, d); let e3 := (a, d)
    let okU := !used.contains e1 && !used.contains e2 && !used.contains e3
    okV && okW && okU && checkTris16 c assignedMask rest (e1 :: e2 :: e3 :: used)

/-- Pure-kernel checker for a `Tree16` on `C₁₆` given `V₁₁` orbit mask `c` and `fV`. -/
def checkTree16 (c fV : Nat) (pAdj nAdj : List Nat) : Nat → Nat → Tree16 → Bool
  | am, nm, Tree16.S u l r =>
    u < 16 && ((am >>> u) &&& 1 == 0) &&
    checkTree16 c fV pAdj nAdj (am ||| (1 <<< u)) nm l &&
    checkTree16 c fV pAdj nAdj (am ||| (1 <<< u)) (nm ||| (1 <<< u)) r
  | am, nm, Tree16.D v =>
    v < 16 && ((am >>> v) &&& 1 == 1) &&
    let svNeg := ((nm >>> v) &&& 1) == 1
    let pm := pAdj.getD v 0
    let nmask := nAdj.getD v 0
    let posA := am &&& (am ^^^ nm)
    let negA := am &&& nm
    let fi := if svNeg then pop16 (pm &&& posA) + pop16 (nmask &&& negA)
              else pop16 (pm &&& negA) + pop16 (nmask &&& posA)
    fV < fi
  | am, nm, Tree16.L tris =>
    let posA := am &&& (am ^^^ nm)
    let negA := am &&& nm
    -- `fc2` = twice the number of frustrated assigned-assigned edges
    let fc2 := (List.range 16).foldl (fun acc u =>
      if ((am >>> u) &&& 1) == 1 then
        let pm := pAdj.getD u 0
        let nmask := nAdj.getD u 0
        let f := if ((nm >>> u) &&& 1) == 1
                 then pop16 (pm &&& posA) + pop16 (nmask &&& negA)
                 else pop16 (pm &&& negA) + pop16 (nmask &&& posA)
        acc + f
      else acc) 0
    let starLB := (List.range 16).foldl (fun acc u =>
      if ((am >>> u) &&& 1) == 0 then
        let pm := pAdj.getD u 0
        let nmask := nAdj.getD u 0
        -- Cost if u = +1 is `cP`, cost if u = -1 is `cN`
        let cP := pop16 (pm &&& negA) + pop16 (nmask &&& posA)
        let cN := pop16 (pm &&& posA) + pop16 (nmask &&& negA)
        acc + min cP cN
      else acc) 0
    checkTris16 c am tris [] && (min 13 (9 * fV) < fV + fc2 / 2 + starLB + tris.length)
  | am, nm, Tree16.O ridx gSol us =>
    (am == 65535) && (ridx < 3) && (gSol < 64) &&
    (us.all fun u => u < 64 && Q3_form 9 u == 1) &&
    let sInit : Nat → ℤ := fun v =>
      match V11_list.idxOf? v with
      | some idxV => v11SignOfMask c idxV
      | none =>
        match C16_list.idxOf? v with
        | some idxC => if ((nm >>> idxC) &&& 1) == 1 then -1 else 1
        | none => 0
    let sOut := applyGauge3Nat gSol (applyWord3Nat us sInit)
    (List.range 27).all fun i => sOut (A27_val i) == (rep27_vecs.getD ridx []).getD i 0

def mkPAdj16 (c : Nat) : List Nat :=
  (List.range 16).map fun u =>
    (List.range 16).foldl (fun m v => if M16_val c u v == 1 then m ||| (1 <<< v) else m) 0

def mkNAdj16 (c : Nat) : List Nat :=
  (List.range 16).map fun u =>
    (List.range 16).foldl (fun m v => if M16_val c u v == -1 then m ||| (1 <<< v) else m) 0

def tree_orb1 : Tree16 := Tree16.S 1 (Tree16.S 15 (Tree16.S 12 (Tree16.S 3 (Tree16.S 7 (Tree16.D 7) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.S 2 (Tree16.S 4 (Tree16.S 8 (Tree16.S 9 (Tree16.D 2) (Tree16.S 10 (Tree16.S 11 (Tree16.D 1) (Tree16.S 13 (Tree16.D 2) (Tree16.S 14 (Tree16.D 1) (Tree16.O 0 25 [17])))) (Tree16.D 4))) (Tree16.D 8)) (Tree16.D 4)) (Tree16.L [])) (Tree16.L [])))) (Tree16.D 3)) (Tree16.S 2 (Tree16.S 4 (Tree16.D 4) (Tree16.S 6 (Tree16.L []) (Tree16.S 5 (Tree16.S 3 (Tree16.S 7 (Tree16.S 8 (Tree16.S 9 (Tree16.S 10 (Tree16.D 3) (Tree16.S 11 (Tree16.D 2) (Tree16.S 13 (Tree16.D 2) (Tree16.S 14 (Tree16.O 0 13 [18, 7]) (Tree16.D 0))))) (Tree16.D 6)) (Tree16.D 3)) (Tree16.D 7)) (Tree16.L [])) (Tree16.L [])))) (Tree16.D 2))) (Tree16.D 15)) (Tree16.S 14 (Tree16.S 13 (Tree16.S 3 (Tree16.D 3) (Tree16.S 5 (Tree16.S 7 (Tree16.S 4 (Tree16.S 2 (Tree16.S 6 (Tree16.S 8 (Tree16.S 9 (Tree16.D 2) (Tree16.S 10 (Tree16.S 11 (Tree16.D 2) (Tree16.S 12 (Tree16.D 2) (Tree16.S 15 (Tree16.D 1) (Tree16.O 0 13 [21, 5])))) (Tree16.D 3))) (Tree16.D 6)) (Tree16.D 6)) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.D 5))) (Tree16.S 2 (Tree16.S 6 (Tree16.D 6) (Tree16.S 4 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 3 (Tree16.L []) (Tree16.S 5 (Tree16.D 5) (Tree16.S 8 (Tree16.D 3) (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 11 (Tree16.S 12 (Tree16.D 2) (Tree16.S 15 (Tree16.O 0 6 [22, 3]) (Tree16.D 0))) (Tree16.D 4)) (Tree16.D 0))))))))) (Tree16.D 2))) (Tree16.D 14))
def tree_orb2 : Tree16 := Tree16.S 1 (Tree16.S 2 (Tree16.S 3 (Tree16.S 4 (Tree16.S 10 (Tree16.S 7 (Tree16.S 8 (Tree16.S 11 (Tree16.D 11) (Tree16.S 15 (Tree16.S 13 (Tree16.D 13) (Tree16.S 6 (Tree16.S 9 (Tree16.D 9) (Tree16.S 5 (Tree16.S 14 (Tree16.S 12 (Tree16.D 12) (Tree16.O 1 0 [22])) (Tree16.D 5)) (Tree16.S 12 (Tree16.D 7) (Tree16.S 14 (Tree16.D 5) (Tree16.D 12))))) (Tree16.S 5 (Tree16.L []) (Tree16.S 9 (Tree16.S 12 (Tree16.D 2) (Tree16.D 4)) (Tree16.D 6))))) (Tree16.D 15))) (Tree16.D 8)) (Tree16.S 9 (Tree16.D 9) (Tree16.S 12 (Tree16.S 6 (Tree16.S 5 (Tree16.L []) (Tree16.S 8 (Tree16.S 11 (Tree16.D 11) (Tree16.S 13 (Tree16.D 2) (Tree16.S 14 (Tree16.D 14) (Tree16.S 15 (Tree16.O 1 61 [42, 25, 13]) (Tree16.D 15))))) (Tree16.D 8))) (Tree16.S 5 (Tree16.L []) (Tree16.S 8 (Tree16.D 6) (Tree16.S 11 (Tree16.S 13 (Tree16.D 6) (Tree16.S 14 (Tree16.D 1) (Tree16.S 15 (Tree16.D 4) (Tree16.D 0)))) (Tree16.D 8))))) (Tree16.D 12)))) (Tree16.D 10)) (Tree16.S 15 (Tree16.S 13 (Tree16.D 13) (Tree16.S 8 (Tree16.S 7 (Tree16.S 12 (Tree16.D 12) (Tree16.S 6 (Tree16.S 9 (Tree16.D 6) (Tree16.S 10 (Tree16.S 11 (Tree16.S 5 (Tree16.D 5) (Tree16.S 14 (Tree16.D 1) (Tree16.D 6))) (Tree16.D 4)) (Tree16.D 9))) (Tree16.S 9 (Tree16.S 5 (Tree16.S 10 (Tree16.D 10) (Tree16.S 11 (Tree16.D 11) (Tree16.S 14 (Tree16.O 1 40 [35, 24, 12]) (Tree16.D 14)))) (Tree16.S 10 (Tree16.S 11 (Tree16.S 14 (Tree16.D 14) (Tree16.O 1 40 [38, 29, 11])) (Tree16.D 11)) (Tree16.D 10))) (Tree16.D 9)))) (Tree16.S 5 (Tree16.D 7) (Tree16.S 6 (Tree16.L []) (Tree16.S 9 (Tree16.D 7) (Tree16.S 10 (Tree16.S 11 (Tree16.D 8) (Tree16.D 11)) (Tree16.D 9)))))) (Tree16.S 6 (Tree16.D 6) (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.D 8) (Tree16.S 10 (Tree16.S 9 (Tree16.D 9) (Tree16.S 11 (Tree16.S 14 (Tree16.D 1) (Tree16.S 12 (Tree16.O 1 23 [29, 11, 1]) (Tree16.D 12))) (Tree16.D 8))) (Tree16.D 10))))))) (Tree16.D 15))) (Tree16.S 4 (Tree16.S 5 (Tree16.S 6 (Tree16.S 7 (Tree16.S 8 (Tree16.S 10 (Tree16.D 3) (Tree16.S 9 (Tree16.S 11 (Tree16.D 11) (Tree16.S 12 (Tree16.D 2) (Tree16.S 13 (Tree16.D 2) (Tree16.D 3)))) (Tree16.D 9))) (Tree16.D 8)) (Tree16.L [])) (Tree16.L [])) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L [])))) (Tree16.S 12 (Tree16.D 12) (Tree16.S 15 (Tree16.S 5 (Tree16.S 7 (Tree16.S 9 (Tree16.S 10 (Tree16.D 10) (Tree16.S 14 (Tree16.S 11 (Tree16.D 1) (Tree16.S 8 (Tree16.S 13 (Tree16.D 2) (Tree16.D 3)) (Tree16.D 8))) (Tree16.D 14))) (Tree16.L [])) (Tree16.D 7)) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.S 8 (Tree16.L []) (Tree16.S 9 (Tree16.S 10 (Tree16.D 10) (Tree16.S 11 (Tree16.S 13 (Tree16.D 5) (Tree16.S 14 (Tree16.D 1) (Tree16.D 0))) (Tree16.D 5))) (Tree16.D 7))) (Tree16.L [])))) (Tree16.D 15))))) (Tree16.S 3 (Tree16.S 4 (Tree16.S 10 (Tree16.S 11 (Tree16.D 11) (Tree16.S 8 (Tree16.S 12 (Tree16.S 6 (Tree16.S 13 (Tree16.S 5 (Tree16.S 14 (Tree16.S 7 (Tree16.S 9 (Tree16.S 15 (Tree16.O 1 62 [38, 22, 1]) (Tree16.D 15)) (Tree16.D 9)) (Tree16.S 9 (Tree16.D 7) (Tree16.S 15 (Tree16.D 7) (Tree16.D 1)))) (Tree16.D 14)) (Tree16.S 7 (Tree16.D 5) (Tree16.S 9 (Tree16.D 9) (Tree16.S 14 (Tree16.D 5) (Tree16.S 15 (Tree16.D 13) (Tree16.D 0)))))) (Tree16.S 5 (Tree16.D 13) (Tree16.S 9 (Tree16.S 7 (Tree16.S 14 (Tree16.D 5) (Tree16.D 6)) (Tree16.D 9)) (Tree16.D 2)))) (Tree16.S 9 (Tree16.S 13 (Tree16.D 6) (Tree16.S 14 (Tree16.D 6) (Tree16.S 5 (Tree16.D 5) (Tree16.S 15 (Tree16.S 7 (Tree16.O 1 26 [36, 21, 3]) (Tree16.D 7)) (Tree16.D 0))))) (Tree16.D 6))) (Tree16.D 12)) (Tree16.D 8))) (Tree16.D 10)) (Tree16.S 15 (Tree16.S 5 (Tree16.S 7 (Tree16.S 8 (Tree16.S 9 (Tree16.S 10 (Tree16.D 10) (Tree16.S 11 (Tree16.D 11) (Tree16.S 14 (Tree16.S 12 (Tree16.D 12) (Tree16.S 13 (Tree16.D 3) (Tree16.D 2))) (Tree16.D 0)))) (Tree16.D 9)) (Tree16.D 8)) (Tree16.L [])) (Tree16.S 6 (Tree16.L []) (Tree16.S 9 (Tree16.S 7 (Tree16.S 8 (Tree16.S 10 (Tree16.S 11 (Tree16.D 11) (Tree16.S 12 (Tree16.D 4) (Tree16.L []))) (Tree16.D 10)) (Tree16.D 8)) (Tree16.L [])) (Tree16.D 9)))) (Tree16.D 15))) (Tree16.S 13 (Tree16.S 4 (Tree16.S 11 (Tree16.D 11) (Tree16.S 9 (Tree16.S 5 (Tree16.S 6 (Tree16.S 7 (Tree16.S 8 (Tree16.S 10 (Tree16.D 3) (Tree16.S 12 (Tree16.D 3) (Tree16.S 14 (Tree16.S 15 (Tree16.D 4) (Tree16.D 0)) (Tree16.D 0)))) (Tree16.D 8)) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 5 (Tree16.L []) (Tree16.L [])))) (Tree16.S 5 (Tree16.S 7 (Tree16.S 9 (Tree16.S 10 (Tree16.D 10) (Tree16.S 8 (Tree16.S 11 (Tree16.D 11) (Tree16.S 12 (Tree16.D 3) (Tree16.S 14 (Tree16.S 6 (Tree16.S 15 (Tree16.O 1 50 [42, 29, 5]) (Tree16.D 0)) (Tree16.D 6)) (Tree16.D 0)))) (Tree16.D 0))) (Tree16.D 9)) (Tree16.L [])) (Tree16.L []))) (Tree16.S 5 (Tree16.D 13) (Tree16.S 6 (Tree16.D 13) (Tree16.S 8 (Tree16.D 3) (Tree16.S 4 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))))))))) (Tree16.S 3 (Tree16.S 2 (Tree16.S 5 (Tree16.S 14 (Tree16.S 4 (Tree16.S 6 (Tree16.S 8 (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 11 (Tree16.D 11) (Tree16.S 15 (Tree16.D 1) (Tree16.S 13 (Tree16.S 12 (Tree16.D 2) (Tree16.D 3)) (Tree16.D 13)))) (Tree16.D 10))) (Tree16.D 8)) (Tree16.L [])) (Tree16.S 7 (Tree16.S 8 (Tree16.S 6 (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 11 (Tree16.S 12 (Tree16.D 4) (Tree16.S 13 (Tree16.D 3) (Tree16.D 5))) (Tree16.D 4)) (Tree16.D 10))) (Tree16.L [])) (Tree16.D 8)) (Tree16.L []))) (Tree16.D 14)) (Tree16.S 10 (Tree16.S 9 (Tree16.D 9) (Tree16.S 11 (Tree16.S 13 (Tree16.D 13) (Tree16.S 7 (Tree16.S 8 (Tree16.S 12 (Tree16.D 7) (Tree16.S 14 (Tree16.S 6 (Tree16.S 15 (Tree16.S 4 (Tree16.D 4) (Tree16.O 1 2 [50, 18])) (Tree16.D 7)) (Tree16.D 6)) (Tree16.D 14))) (Tree16.D 7)) (Tree16.S 12 (Tree16.S 4 (Tree16.S 15 (Tree16.D 15) (Tree16.S 6 (Tree16.S 8 (Tree16.S 14 (Tree16.O 1 60 [38, 21, 3]) (Tree16.D 14)) (Tree16.D 8)) (Tree16.S 8 (Tree16.D 6) (Tree16.S 14 (Tree16.D 6) (Tree16.D 0))))) (Tree16.S 6 (Tree16.D 4) (Tree16.S 8 (Tree16.D 8) (Tree16.S 14 (Tree16.D 12) (Tree16.S 15 (Tree16.D 1) (Tree16.D 0)))))) (Tree16.S 4 (Tree16.D 12) (Tree16.S 8 (Tree16.S 6 (Tree16.S 14 (Tree16.S 15 (Tree16.D 7) (Tree16.D 4)) (Tree16.D 6)) (Tree16.D 8)) (Tree16.D 3)))))) (Tree16.D 11))) (Tree16.D 10))) (Tree16.S 12 (Tree16.S 5 (Tree16.S 4 (Tree16.S 6 (Tree16.S 8 (Tree16.S 10 (Tree16.S 9 (Tree16.D 9) (Tree16.S 11 (Tree16.D 2) (Tree16.S 13 (Tree16.S 14 (Tree16.S 15 (Tree16.D 1) (Tree16.S 7 (Tree16.D 7) (Tree16.O 1 46 [50, 28, 7]))) (Tree16.D 1)) (Tree16.D 2)))) (Tree16.D 10)) (Tree16.D 8)) (Tree16.L [])) (Tree16.L [])) (Tree16.S 10 (Tree16.S 8 (Tree16.S 4 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.D 9) (Tree16.S 11 (Tree16.D 2) (Tree16.S 13 (Tree16.S 14 (Tree16.D 5) (Tree16.D 1)) (Tree16.D 2))))) (Tree16.L [])) (Tree16.L [])) (Tree16.S 4 (Tree16.L []) (Tree16.L []))) (Tree16.D 10))) (Tree16.S 4 (Tree16.D 12) (Tree16.S 7 (Tree16.S 8 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.D 3)) (Tree16.D 12))))) (Tree16.S 2 (Tree16.S 5 (Tree16.S 14 (Tree16.S 12 (Tree16.D 12) (Tree16.S 9 (Tree16.S 6 (Tree16.D 9) (Tree16.S 4 (Tree16.L []) (Tree16.S 7 (Tree16.S 10 (Tree16.D 9) (Tree16.S 11 (Tree16.S 8 (Tree16.D 8) (Tree16.S 15 (Tree16.S 13 (Tree16.D 13) (Tree16.O 1 2 [28, 10, 1])) (Tree16.D 0))) (Tree16.D 11))) (Tree16.D 7)))) (Tree16.S 6 (Tree16.S 13 (Tree16.S 7 (Tree16.S 8 (Tree16.S 4 (Tree16.S 10 (Tree16.S 11 (Tree16.D 11) (Tree16.S 15 (Tree16.D 15) (Tree16.O 1 10 [43, 17, 5]))) (Tree16.D 10)) (Tree16.S 10 (Tree16.D 10) (Tree16.S 11 (Tree16.S 15 (Tree16.O 1 61 [38, 28, 10]) (Tree16.D 15)) (Tree16.D 11)))) (Tree16.D 8)) (Tree16.S 8 (Tree16.D 7) (Tree16.S 11 (Tree16.S 10 (Tree16.D 5) (Tree16.S 4 (Tree16.D 4) (Tree16.S 15 (Tree16.D 7) (Tree16.D 0)))) (Tree16.D 8)))) (Tree16.D 13)) (Tree16.S 4 (Tree16.D 6) (Tree16.S 7 (Tree16.S 8 (Tree16.D 6) (Tree16.S 10 (Tree16.D 10) (Tree16.D 9))) (Tree16.L [])))))) (Tree16.D 14)) (Tree16.S 11 (Tree16.S 6 (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 14 (Tree16.S 12 (Tree16.D 12) (Tree16.S 7 (Tree16.S 4 (Tree16.L []) (Tree16.S 8 (Tree16.S 13 (Tree16.D 5) (Tree16.D 3)) (Tree16.D 7))) (Tree16.S 8 (Tree16.D 8) (Tree16.S 4 (Tree16.S 15 (Tree16.D 4) (Tree16.S 13 (Tree16.O 1 3 [21, 3, 1]) (Tree16.D 13))) (Tree16.S 13 (Tree16.S 15 (Tree16.D 13) (Tree16.D 4)) (Tree16.D 6)))))) (Tree16.D 14)) (Tree16.D 10))) (Tree16.S 8 (Tree16.D 8) (Tree16.S 13 (Tree16.D 13) (Tree16.S 7 (Tree16.S 4 (Tree16.L []) (Tree16.S 9 (Tree16.S 10 (Tree16.D 9) (Tree16.S 12 (Tree16.D 7) (Tree16.S 14 (Tree16.D 5) (Tree16.D 0)))) (Tree16.D 7))) (Tree16.S 4 (Tree16.L []) (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 12 (Tree16.D 3) (Tree16.S 14 (Tree16.S 15 (Tree16.O 1 20 [38, 36, 22]) (Tree16.D 15)) (Tree16.D 14))) (Tree16.D 10)))))))) (Tree16.D 11))) (Tree16.S 5 (Tree16.S 13 (Tree16.S 14 (Tree16.S 4 (Tree16.S 6 (Tree16.S 8 (Tree16.S 11 (Tree16.D 11) (Tree16.S 15 (Tree16.D 15) (Tree16.S 10 (Tree16.S 9 (Tree16.D 9) (Tree16.S 12 (Tree16.D 3) (Tree16.D 2))) (Tree16.D 0)))) (Tree16.L [])) (Tree16.D 6)) (Tree16.S 7 (Tree16.S 6 (Tree16.S 8 (Tree16.S 9 (Tree16.S 10 (Tree16.D 9) (Tree16.S 11 (Tree16.D 11) (Tree16.S 12 (Tree16.D 4) (Tree16.S 15 (Tree16.D 1) (Tree16.D 0))))) (Tree16.L [])) (Tree16.D 8)) (Tree16.L [])) (Tree16.L []))) (Tree16.D 14)) (Tree16.D 13)) (Tree16.S 4 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.D 9) (Tree16.S 10 (Tree16.S 11 (Tree16.D 2) (Tree16.S 8 (Tree16.S 12 (Tree16.D 3) (Tree16.D 2)) (Tree16.D 8))) (Tree16.D 10)))) (Tree16.L [])) (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.L []))))))
def tree_orb3 : Tree16 := Tree16.S 1 (Tree16.S 2 (Tree16.S 3 (Tree16.S 9 (Tree16.S 4 (Tree16.S 15 (Tree16.S 5 (Tree16.S 7 (Tree16.S 6 (Tree16.L []) (Tree16.S 8 (Tree16.S 10 (Tree16.S 11 (Tree16.D 11) (Tree16.S 12 (Tree16.S 13 (Tree16.D 13) (Tree16.S 14 (Tree16.D 14) (Tree16.O 2 28 [56, 17, 12]))) (Tree16.L []))) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])) (Tree16.S 10 (Tree16.S 13 (Tree16.D 13) (Tree16.S 12 (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 8 (Tree16.L []) (Tree16.S 11 (Tree16.S 14 (Tree16.L []) (Tree16.O 2 53 [57, 41, 14, 3])) (Tree16.L []))))) (Tree16.S 7 (Tree16.S 6 (Tree16.S 8 (Tree16.S 11 (Tree16.L []) (Tree16.S 14 (Tree16.O 2 44 [63, 40, 15, 11]) (Tree16.D 14))) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])))) (Tree16.D 10))) (Tree16.L [])) (Tree16.S 13 (Tree16.L []) (Tree16.S 7 (Tree16.S 6 (Tree16.L []) (Tree16.S 12 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.S 8 (Tree16.L []) (Tree16.S 10 (Tree16.S 11 (Tree16.S 14 (Tree16.S 15 (Tree16.O 2 19 [57, 42, 13, 1]) (Tree16.D 15)) (Tree16.L [])) (Tree16.D 11)) (Tree16.L [])))))) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))))) (Tree16.S 13 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 10 (Tree16.S 15 (Tree16.S 11 (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.S 4 (Tree16.S 7 (Tree16.L []) (Tree16.S 8 (Tree16.L []) (Tree16.S 12 (Tree16.L []) (Tree16.L [])))) (Tree16.L [])) (Tree16.L []))) (Tree16.S 4 (Tree16.S 6 (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 8 (Tree16.S 12 (Tree16.L []) (Tree16.L [])) (Tree16.L [])))) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])) (Tree16.L [])))) (Tree16.S 4 (Tree16.S 9 (Tree16.S 7 (Tree16.S 8 (Tree16.S 11 (Tree16.L []) (Tree16.S 15 (Tree16.S 5 (Tree16.S 12 (Tree16.L []) (Tree16.S 6 (Tree16.S 10 (Tree16.L []) (Tree16.S 13 (Tree16.S 14 (Tree16.O 2 57 [55, 25, 14, 1]) (Tree16.L [])) (Tree16.L []))) (Tree16.L []))) (Tree16.S 6 (Tree16.L []) (Tree16.L []))) (Tree16.D 15))) (Tree16.L [])) (Tree16.L [])) (Tree16.S 6 (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.L []))) (Tree16.S 8 (Tree16.S 7 (Tree16.S 9 (Tree16.S 10 (Tree16.L []) (Tree16.S 12 (Tree16.D 12) (Tree16.S 5 (Tree16.S 13 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 11 (Tree16.L []) (Tree16.S 14 (Tree16.L []) (Tree16.S 15 (Tree16.O 2 2 [52, 29, 14, 1]) (Tree16.D 15)))))) (Tree16.S 6 (Tree16.L []) (Tree16.L []))))) (Tree16.L [])) (Tree16.L [])) (Tree16.S 6 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))))))) (Tree16.S 3 (Tree16.S 5 (Tree16.S 12 (Tree16.S 4 (Tree16.S 11 (Tree16.D 11) (Tree16.S 6 (Tree16.S 10 (Tree16.S 15 (Tree16.S 7 (Tree16.S 8 (Tree16.S 9 (Tree16.L []) (Tree16.S 13 (Tree16.S 14 (Tree16.L []) (Tree16.O 2 52 [52, 43, 14])) (Tree16.L []))) (Tree16.D 8)) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 7 (Tree16.S 8 (Tree16.S 9 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 4 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.D 12)) (Tree16.L [])) (Tree16.L []))) (Tree16.S 12 (Tree16.S 4 (Tree16.S 10 (Tree16.S 15 (Tree16.S 9 (Tree16.L []) (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.S 8 (Tree16.S 11 (Tree16.D 11) (Tree16.S 13 (Tree16.L []) (Tree16.S 14 (Tree16.O 2 32 [50, 28, 11, 5]) (Tree16.L [])))) (Tree16.L []))) (Tree16.S 7 (Tree16.L []) (Tree16.S 8 (Tree16.L []) (Tree16.L []))))) (Tree16.L [])) (Tree16.D 10)) (Tree16.L [])) (Tree16.S 4 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.L [])))) (Tree16.S 13 (Tree16.S 8 (Tree16.S 11 (Tree16.L []) (Tree16.S 9 (Tree16.S 4 (Tree16.S 5 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 4 (Tree16.S 6 (Tree16.S 5 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.D 6)) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 8 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))))) (Tree16.S 2 (Tree16.S 3 (Tree16.S 4 (Tree16.S 13 (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.D 13))) (Tree16.S 5 (Tree16.L []) (Tree16.S 10 (Tree16.S 7 (Tree16.S 6 (Tree16.S 8 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 11 (Tree16.S 14 (Tree16.S 6 (Tree16.S 8 (Tree16.L []) (Tree16.S 9 (Tree16.D 9) (Tree16.S 12 (Tree16.S 15 (Tree16.O 2 16 [50, 29, 10, 5]) (Tree16.L [])) (Tree16.L [])))) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))) (Tree16.D 10)))) (Tree16.S 13 (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.D 13))) (Tree16.S 5 (Tree16.L []) (Tree16.S 11 (Tree16.S 14 (Tree16.S 8 (Tree16.L []) (Tree16.S 7 (Tree16.S 6 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.L []))) (Tree16.S 6 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 12 (Tree16.L []) (Tree16.S 15 (Tree16.L []) (Tree16.O 2 39 [52, 42, 15]))) (Tree16.D 10)))))) (Tree16.L [])) (Tree16.D 11))))) (Tree16.S 8 (Tree16.S 4 (Tree16.S 14 (Tree16.S 7 (Tree16.S 6 (Tree16.S 12 (Tree16.D 12) (Tree16.S 15 (Tree16.S 5 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 11 (Tree16.S 13 (Tree16.L []) (Tree16.O 2 54 [62, 41, 14, 10])) (Tree16.L [])) (Tree16.D 10)))) (Tree16.L []))) (Tree16.L [])) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 12 (Tree16.L []) (Tree16.S 5 (Tree16.S 7 (Tree16.S 6 (Tree16.S 9 (Tree16.S 10 (Tree16.D 10) (Tree16.S 11 (Tree16.S 13 (Tree16.S 14 (Tree16.S 15 (Tree16.L []) (Tree16.O 2 37 [56, 40, 15, 3])) (Tree16.D 14)) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 11 (Tree16.S 14 (Tree16.S 13 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 15 (Tree16.D 15) (Tree16.O 2 48 [57, 21, 12])) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 7 (Tree16.S 6 (Tree16.L []) (Tree16.S 9 (Tree16.S 10 (Tree16.L []) (Tree16.S 15 (Tree16.O 2 1 [56, 43, 12, 1]) (Tree16.L []))) (Tree16.L []))) (Tree16.L []))) (Tree16.D 14)) (Tree16.D 11))))) (Tree16.S 12 (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L []))) (Tree16.S 11 (Tree16.S 14 (Tree16.S 10 (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 4 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 13 (Tree16.L []) (Tree16.L []))))))) (Tree16.S 4 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.S 13 (Tree16.L []) (Tree16.L [])) (Tree16.L []))))))) (Tree16.L [])) (Tree16.L []))))) (Tree16.S 3 (Tree16.S 12 (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 8 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])) (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.D 7) (Tree16.S 4 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))))) (Tree16.L []))) (Tree16.S 9 (Tree16.L []) (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])))) (Tree16.S 5 (Tree16.S 9 (Tree16.S 6 (Tree16.S 4 (Tree16.S 7 (Tree16.L []) (Tree16.D 9)) (Tree16.L [])) (Tree16.L [])) (Tree16.S 6 (Tree16.S 8 (Tree16.S 11 (Tree16.L []) (Tree16.S 13 (Tree16.S 4 (Tree16.S 12 (Tree16.L []) (Tree16.S 7 (Tree16.S 10 (Tree16.S 14 (Tree16.S 15 (Tree16.O 2 30 [55, 24, 15, 1]) (Tree16.L [])) (Tree16.D 14)) (Tree16.L [])) (Tree16.L []))) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.D 13))) (Tree16.L [])) (Tree16.L []))) (Tree16.S 8 (Tree16.S 6 (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 14 (Tree16.S 4 (Tree16.S 13 (Tree16.S 7 (Tree16.L []) (Tree16.S 11 (Tree16.L []) (Tree16.S 12 (Tree16.S 15 (Tree16.L []) (Tree16.O 2 16 [52, 28, 15, 1])) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.D 14)) (Tree16.L []))) (Tree16.L [])) (Tree16.S 6 (Tree16.S 4 (Tree16.S 7 (Tree16.D 8) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))))))
def tree_orb4 : Tree16 := Tree16.S 3 (Tree16.S 1 (Tree16.S 2 (Tree16.S 9 (Tree16.S 4 (Tree16.S 5 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.S 6 (Tree16.S 7 (Tree16.S 8 (Tree16.S 10 (Tree16.S 11 (Tree16.L []) (Tree16.S 12 (Tree16.L []) (Tree16.S 13 (Tree16.L []) (Tree16.S 14 (Tree16.S 15 (Tree16.O 1 31 [52, 42, 1]) (Tree16.L [])) (Tree16.L []))))) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))) (Tree16.S 12 (Tree16.L []) (Tree16.S 5 (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.S 6 (Tree16.L []) (Tree16.L []))))) (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L [])))))) (Tree16.S 4 (Tree16.S 10 (Tree16.S 7 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))) (Tree16.L [])) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L []))))) (Tree16.S 2 (Tree16.S 4 (Tree16.S 14 (Tree16.S 10 (Tree16.S 13 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))) (Tree16.L [])) (Tree16.L [])) (Tree16.S 5 (Tree16.S 11 (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))) (Tree16.L [])) (Tree16.S 12 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.S 13 (Tree16.L []) (Tree16.S 14 (Tree16.S 8 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 11 (Tree16.S 15 (Tree16.L []) (Tree16.O 1 41 [52, 28])) (Tree16.L [])) (Tree16.L [])))))) (Tree16.L [])))))) (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 8 (Tree16.L []) (Tree16.L []))))) (Tree16.S 9 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L [])))))))) (Tree16.S 2 (Tree16.S 1 (Tree16.S 6 (Tree16.S 8 (Tree16.S 9 (Tree16.S 5 (Tree16.S 4 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L [])))) (Tree16.S 8 (Tree16.S 4 (Tree16.S 6 (Tree16.S 14 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 5 (Tree16.S 7 (Tree16.S 6 (Tree16.S 9 (Tree16.S 10 (Tree16.L []) (Tree16.S 11 (Tree16.S 12 (Tree16.L []) (Tree16.S 13 (Tree16.S 14 (Tree16.S 15 (Tree16.L []) (Tree16.O 1 42 [55, 29, 3])) (Tree16.L [])) (Tree16.L []))) (Tree16.L []))) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 6 (Tree16.L []) (Tree16.L [])))) (Tree16.S 5 (Tree16.S 4 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.L []))) (Tree16.S 4 (Tree16.L []) (Tree16.S 6 (Tree16.L []) (Tree16.S 7 (Tree16.L []) (Tree16.L []))))))) (Tree16.S 1 (Tree16.S 5 (Tree16.S 8 (Tree16.S 4 (Tree16.S 6 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 4 (Tree16.S 6 (Tree16.S 7 (Tree16.S 8 (Tree16.S 9 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))) (Tree16.S 6 (Tree16.S 7 (Tree16.S 8 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 12 (Tree16.S 13 (Tree16.S 15 (Tree16.L []) (Tree16.S 8 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 11 (Tree16.L []) (Tree16.S 14 (Tree16.O 1 17 [52, 42, 7]) (Tree16.L []))) (Tree16.L [])))) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])) (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L []))))) (Tree16.S 15 (Tree16.L []) (Tree16.S 9 (Tree16.L []) (Tree16.S 12 (Tree16.S 5 (Tree16.L []) (Tree16.S 4 (Tree16.L []) (Tree16.L []))) (Tree16.S 4 (Tree16.L []) (Tree16.L []))))))))
def tree_orb5 : Tree16 := Tree16.S 1 (Tree16.S 2 (Tree16.S 3 (Tree16.S 9 (Tree16.S 13 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 5 (Tree16.S 4 (Tree16.L []) (Tree16.L [])) (Tree16.L []))) (Tree16.S 10 (Tree16.S 13 (Tree16.L []) (Tree16.S 4 (Tree16.L []) (Tree16.L []))) (Tree16.L []))) (Tree16.S 7 (Tree16.S 8 (Tree16.S 4 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 10 (Tree16.L []) (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L [])))))) (Tree16.S 3 (Tree16.S 4 (Tree16.S 10 (Tree16.S 7 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 8 (Tree16.S 5 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L []))) (Tree16.S 8 (Tree16.S 11 (Tree16.L []) (Tree16.S 13 (Tree16.S 4 (Tree16.L []) (Tree16.L [])) (Tree16.L []))) (Tree16.L [])))) (Tree16.S 2 (Tree16.S 3 (Tree16.S 5 (Tree16.S 10 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.S 8 (Tree16.L []) (Tree16.S 4 (Tree16.S 6 (Tree16.L []) (Tree16.L [])) (Tree16.L [])))) (Tree16.S 8 (Tree16.S 12 (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L []))) (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L [])))) (Tree16.S 11 (Tree16.S 12 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])))) (Tree16.S 3 (Tree16.S 9 (Tree16.L []) (Tree16.S 10 (Tree16.S 12 (Tree16.L []) (Tree16.S 4 (Tree16.L []) (Tree16.S 5 (Tree16.L []) (Tree16.L [])))) (Tree16.L []))) (Tree16.S 6 (Tree16.S 10 (Tree16.S 4 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])) (Tree16.L [])) (Tree16.S 8 (Tree16.S 5 (Tree16.L []) (Tree16.L [])) (Tree16.L [])))))

/-- Check all structural invariants of `A27, B36, V11, C16, a27ToP0, pivGauges, v11Map`. -/
def checkPart1Tables : Bool :=
  (A27_list.length == 27) && (B36_list.length == 36) &&
  (V11_list.length == 11) && (C16_list.length == 16) &&
  (edges16_list.length == 40) && (v11Lines_list.length == 5) &&
  -- A27 exact match with Q3_form 9 == 0 (strictly sorted)
  ((List.range 27).all fun i => A27_val i != 0 && A27_val i < 64 && Q3_form 9 (A27_val i) == 0) &&
  ((List.range 26).all fun i => A27_val i < A27_val (i + 1)) &&
  ((List.range 64).all fun v => if v != 0 && Q3_form 9 v == 0 then A27_list.contains v else true) &&
  -- B36 exact match with Q3_form 9 == 1 (strictly sorted)
  ((List.range 36).all fun i => B36_val i != 0 && B36_val i < 64 && Q3_form 9 (B36_val i) == 1) &&
  ((List.range 35).all fun i => B36_val i < B36_val (i + 1)) &&
  ((List.range 64).all fun v => if v != 0 && Q3_form 9 v == 1 then B36_list.contains v else true) &&
  -- V11 = {p ∈ A27 | symp3 2 p == 0}, C16 = {p ∈ A27 | symp3 2 p == 1}
  ((List.range 11).all fun i => V11_val i != 0 && V11_val i < 64 && Q3_form 9 (V11_val i) == 0 && symp3 2 (V11_val i) == 0) &&
  ((List.range 10).all fun i => V11_val i < V11_val (i + 1)) &&
  ((List.range 16).all fun i => C16_val i != 0 && C16_val i < 64 && Q3_form 9 (C16_val i) == 0 && symp3 2 (C16_val i) == 1) &&
  ((List.range 15).all fun i => C16_val i < C16_val (i + 1)) &&
  ((List.range 27).all fun i => let p := A27_val i; if symp3 2 p == 0 then V11_list.contains p else C16_list.contains p) &&
  -- a27ToP0_words: each maps A27[i] -> 2 via O^-(6,2) transvections
  ((List.range 27).all fun i =>
    let us := a27ToP0_words.getD i []
    (us.all fun u => u < 64 && Q3_form 9 u == 1) &&
    (us.foldl (fun cur u => transv3_pt u cur) (A27_val i) == 2)) &&
  -- pivGauges: for every 5-bit mask m < 32, g = pivGauges[m] flips exact subset of piv5
  ((List.range 32).all fun m =>
    let g := pivGauges_list.getD m 0
    g < 64 && (List.range 5).all fun k => symp3 g (V11_val (piv5_list.getD k 0)) == ((m >>> k) &&& 1)) &&
  -- v11Map: for every 6-bit mask c < 64, maps v11SignOfMask c to v11SignOfMask (orbRep[oid]) via Stab(2) + gauge
  ((List.range 64).all fun c =>
    let (oid, gFix, us) := v11Map_data.getD c (0, 0, [])
    (oid < 6) && (gFix < 64) &&
    (us.all fun u => u < 64 && Q3_form 9 u == 1 && symp3 u 2 == 0) &&
    let sInit : Nat → ℤ := fun v => match V11_list.idxOf? v with | some i => v11SignOfMask c i | none => 0
    let sOut := applyGauge3Nat gFix (applyWord3Nat us sInit)
    let targetC := orbRep_list.getD oid 0
    (List.range 11).all fun i => sOut (V11_val i) == v11SignOfMask targetC i) &&
  -- Exact ordered frustrated pair count in V11 for orbRep[0..5] is 6 * o
  ((List.range 6).all fun o =>
    let c := orbRep_list.getD o 0
    let cnt := (List.range 11).foldl (fun acc i =>
      acc + ((List.range 11).filter fun j =>
        if i == j || symp3 (V11_val i) (V11_val j) != 0 then false
        else
          match V11_list.idxOf? (V11_val i ^^^ V11_val j) with
          | some k => gamma3_sgn (V11_val i) (V11_val j) * v11SignOfMask c i * v11SignOfMask c j * v11SignOfMask c k == -1
          | none => false).length) 0
    cnt == 6 * o) &&
  -- M16 symmetry & exact edge match with commuting pairs in C16 for c in orbRep[1..5]
  ((List.range 5).all fun o' =>
    let c := orbRep_list.getD (o' + 1) 0
    (List.range 16).all fun i =>
      (List.range 16).all fun j =>
        let w := M16_val c i j
        (w == M16_val c j i) &&
        ((w != 0) == (i != j && symp3 (C16_val i) (C16_val j) == 0)) &&
        (w == 0 || w == 1 || w == -1)) &&
  -- pop8 exactness on all 256 byte values
  ((List.range 256).all fun x =>
    pop8 x == (List.range 8).foldl (fun acc b => acc + ((x >>> b) &&& 1)) 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkPart1Tables_ok : checkPart1Tables = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkTree16_orb1_ok :
    checkTree16 1 1 (mkPAdj16 1) (mkNAdj16 1) 1 0 tree_orb1 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkTree16_orb2_ok :
    checkTree16 3 2 (mkPAdj16 3) (mkNAdj16 3) 1 0 tree_orb2 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkTree16_orb3_ok :
    checkTree16 7 3 (mkPAdj16 7) (mkNAdj16 7) 1 0 tree_orb3 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkTree16_orb4_ok :
    checkTree16 15 4 (mkPAdj16 15) (mkNAdj16 15) 1 0 tree_orb4 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkTree16_orb5_ok :
    checkTree16 31 5 (mkPAdj16 31) (mkNAdj16 31) 1 0 tree_orb5 = true := by rfl

def checkA27Common3 : Bool :=
  (List.range 27).all fun i =>
    (List.range 27).all fun j =>
      if i == j || symp3 (A27_val i) (A27_val j) != 0 then true
      else ((List.range 27).filter fun k =>
        symp3 (A27_val k) (A27_val i) == 0 && symp3 (A27_val k) (A27_val j) == 0).length == 3

set_option maxRecDepth 20000 in
lemma checkA27Common3_ok : checkA27Common3 = true := by rfl

/-! ### Section 2: Complete Soundness of Part 1 (`qminus52_le13_classified`) -/

section Part1Soundness

open scoped Classical

private lemma p1_getD_eq_getElem {α : Type*} (L : List α) (d : α) {i : Nat} (hi : i < L.length) :
    L.getD i d = L[i] := by simp [List.getD, hi]

private lemma p1_all_range {n : Nat} {P : Nat → Bool}
    (h : ((List.range n).all P) = true) {i : Nat} (hi : i < n) : P i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

private lemma p1_list_range_filter_len (n : Nat) (P : Nat → Bool) :
    ((List.range n).filter P).length =
      ((Finset.univ : Finset (Fin n)).filter fun i => P i.val = true).card := by
  have h1 : ∀ m, ((List.range m).filter P).length =
      ∑ k ∈ Finset.range m, if P k = true then 1 else 0 := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
      cases h : P m <;> simp [h]
  rw [h1, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range (fun k => if P k = true then 1 else 0) n).symm

private lemma p1_foldl_sum_range (n : Nat) (f : Nat → Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i : Fin n, f i.val := by
  have hgen : ∀ (L : List Nat) (a : Nat),
      L.foldl (fun acc i => acc + f i) a = a + (L.map f).sum := by
    intro L; induction L with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [List.foldl_cons, ih, Nat.add_assoc]
  rw [hgen, zero_add]
  have hrm : ∀ m, ((List.range m).map f).sum = ∑ k ∈ Finset.range m, f k := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [hrm]
  exact (Fin.sum_univ_eq_sum_range f n).symm

private lemma strictMono_of_step {n : Nat} {f : Nat → Nat}
    (hstep : ∀ i, i < n - 1 → f i < f (i + 1)) {i j : Nat} (hij : i < j) (hj : j < n) :
    f i < f j := by
  have hchain : ∀ d k, k + d < n → 0 < d → f k < f (k + d) := by
    intro d; induction d with
    | zero => intro _ _ hd; omega
    | succ d ih =>
      intro k hk _
      cases d with
      | zero => exact hstep k (by omega)
      | succ d' => exact lt_trans (ih k (by omega) (by omega)) (hstep (k + d' + 1) (by omega))
  have h := hchain (j - i) i (by omega) (by omega)
  rwa [show i + (j - i) = j by omega] at h

/-- Unpacked structural facts from `checkPart1Tables_ok`. -/
private lemma part1_tables_spec :
    (A27_list.length = 27 ∧ B36_list.length = 36 ∧ V11_list.length = 11 ∧ C16_list.length = 16) ∧
    (∀ i < 27, A27_val i ≠ 0 ∧ A27_val i < 64 ∧ Q3_form 9 (A27_val i) = 0) ∧
    (∀ i < 26, A27_val i < A27_val (i + 1)) ∧
    (∀ v < 64, v ≠ 0 → Q3_form 9 v = 0 → A27_list.contains v = true) ∧
    (∀ i < 36, B36_val i ≠ 0 ∧ B36_val i < 64 ∧ Q3_form 9 (B36_val i) = 1) ∧
    (∀ i < 35, B36_val i < B36_val (i + 1)) ∧
    (∀ v < 64, v ≠ 0 → Q3_form 9 v = 1 → B36_list.contains v = true) ∧
    (∀ i < 11, V11_val i ≠ 0 ∧ V11_val i < 64 ∧ Q3_form 9 (V11_val i) = 0 ∧ symp3 2 (V11_val i) = 0) ∧
    (∀ i < 10, V11_val i < V11_val (i + 1)) ∧
    (∀ i < 16, C16_val i ≠ 0 ∧ C16_val i < 64 ∧ Q3_form 9 (C16_val i) = 0 ∧ symp3 2 (C16_val i) = 1) ∧
    (∀ i < 15, C16_val i < C16_val (i + 1)) ∧
    (∀ i < 27, if symp3 2 (A27_val i) == 0 then V11_list.contains (A27_val i) = true
               else C16_list.contains (A27_val i) = true) ∧
    (∀ i < 27, let us := a27ToP0_words.getD i []
      (∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1) ∧
      us.foldl (fun cur u => transv3_pt u cur) (A27_val i) = 2) ∧
    (∀ m < 32, let g := pivGauges_list.getD m 0
      g < 64 ∧ ∀ k < 5, symp3 g (V11_val (piv5_list.getD k 0)) = ((m >>> k) &&& 1)) ∧
    (∀ c < 64, let (oid, gFix, us) := v11Map_data.getD c (0, 0, [])
      oid < 6 ∧ gFix < 64 ∧
      (∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1 ∧ symp3 u 2 = 0) ∧
      ∀ i < 11, applyGauge3Nat gFix (applyWord3Nat us
        (fun v => match V11_list.idxOf? v with | some j => v11SignOfMask c j | none => 0)) (V11_val i) =
        v11SignOfMask (orbRep_list.getD oid 0) i) ∧
    (∀ o < 6, let c := orbRep_list.getD o 0
      (List.range 11).foldl (fun acc i =>
        acc + ((List.range 11).filter fun j =>
          if i == j || symp3 (V11_val i) (V11_val j) != 0 then false
          else match V11_list.idxOf? (V11_val i ^^^ V11_val j) with
            | some k => gamma3_sgn (V11_val i) (V11_val j) * v11SignOfMask c i * v11SignOfMask c j * v11SignOfMask c k == -1
            | none => false).length) 0 = 6 * o) ∧
    (∀ o' < 5, let c := orbRep_list.getD (o' + 1) 0
      ∀ i < 16, ∀ j < 16,
        M16_val c i j = M16_val c j i ∧
        ((M16_val c i j != 0) = (i != j && symp3 (C16_val i) (C16_val j) == 0)) ∧
        (M16_val c i j = 0 ∨ M16_val c i j = 1 ∨ M16_val c i j = -1)) ∧
    (∀ x < 256, pop8 x = (List.range 8).foldl (fun acc b => acc + ((x >>> b) &&& 1)) 0) := by
  have h := checkPart1Tables_ok
  unfold checkPart1Tables at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlA, hlB⟩, hlV⟩, hlC⟩, _⟩, _⟩, hA1⟩, hA2⟩, hA3⟩,
    hB1⟩, hB2⟩, hB3⟩, hV1⟩, hV2⟩, hC1⟩, hC2⟩, hPart⟩, hToP0⟩, hPiv⟩, hMap⟩, hVcnt⟩, hM16⟩, hPop⟩
  refine ⟨⟨by simpa using hlA, by simpa using hlB, by simpa using hlV, by simpa using hlC⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have := p1_all_range hA1 hi; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at this; exact ⟨this.1.1, this.1.2, this.2⟩
  · intro i hi; have := p1_all_range hA2 hi; simpa using this
  · intro v hv hv0 hq; have := p1_all_range hA3 hv; simp [hv0, hq] at this; simpa [List.contains_eq_mem] using this
  · intro i hi; have := p1_all_range hB1 hi; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at this; exact ⟨this.1.1, this.1.2, this.2⟩
  · intro i hi; have := p1_all_range hB2 hi; simpa using this
  · intro v hv hv0 hq; have := p1_all_range hB3 hv; simp [hv0, hq] at this; simpa [List.contains_eq_mem] using this
  · intro i hi; have := p1_all_range hV1 hi; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at this; exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · intro i hi; have := p1_all_range hV2 hi; simpa using this
  · intro i hi; have := p1_all_range hC1 hi; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at this; exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · intro i hi; have := p1_all_range hC2 hi; simpa using this
  · intro i hi; have h := p1_all_range hPart hi; split_ifs at h ⊢ <;> exact h
  · intro i hi
    have hi' := p1_all_range hToP0 hi
    rcases Bool.and_eq_true _ _ |>.mp hi' with ⟨h1, h2⟩
    refine ⟨fun u hu => ?_, beq_iff_eq.mp h2⟩
    have hu' := List.all_eq_true.mp h1 u hu
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu'; exact hu'
  · intro m hm
    have hm' := p1_all_range hPiv hm
    dsimp only at hm' ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
    exact ⟨hm'.1, fun k hk => by have := p1_all_range hm'.2 hk; simpa using this⟩
  · intro c hc
    have hc' := p1_all_range hMap hc
    dsimp only at hc' ⊢
    rcases hv : v11Map_data.getD c (0, 0, []) with ⟨oid, gFix, us⟩
    rw [hv] at hc'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    refine ⟨hc'.1.1.1, hc'.1.1.2, ?_, ?_⟩
    · intro u hu
      have h1 := List.all_eq_true.mp hc'.1.2 u hu
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      exact ⟨h1.1.1, h1.1.2, h1.2⟩
    · intro i hi; have := p1_all_range hc'.2 hi; simpa using this
  · intro o ho; have := p1_all_range hVcnt ho; simpa using this
  · intro o' ho' c i hi j hj
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hM16 o' (List.mem_range.mpr ho')) i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
    exact ⟨h1.1.1, h1.1.2, by rcases h1.2 with (h0' | h0') | h0' <;> [exact Or.inl h0'; exact Or.inr (Or.inl h0'); exact Or.inr (Or.inr h0')]⟩
  · intro x hx; have := p1_all_range hPop hx; simpa using this

def A27_pt (i : Fin 27) : Fin 64 := ⟨A27_val i.val, (part1_tables_spec.2.1 i.val i.isLt).2.1⟩
def B36_pt (i : Fin 36) : Fin 64 := ⟨B36_val i.val, (part1_tables_spec.2.2.2.2.1 i.val i.isLt).2.1⟩
def V11_pt (i : Fin 11) : Fin 64 := ⟨V11_val i.val, (part1_tables_spec.2.2.2.2.2.2.2.1 i.val i.isLt).2.1⟩
def C16_pt (i : Fin 16) : Fin 64 := ⟨C16_val i.val, (part1_tables_spec.2.2.2.2.2.2.2.2.2.1 i.val i.isLt).2.1⟩

lemma A27_val_inj {i j : Fin 27} (h : A27_val i.val = A27_val j.val) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.1 hlt j.isLt))
  · exact absurd h.symm (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.1 hgt i.isLt))

lemma B36_val_inj {i j : Fin 36} (h : B36_val i.val = B36_val j.val) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.1 hlt j.isLt))
  · exact absurd h.symm (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.1 hgt i.isLt))

lemma V11_val_inj {i j : Fin 11} (h : V11_val i.val = V11_val j.val) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.2.2.2.1 hlt j.isLt))
  · exact absurd h.symm (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.2.2.2.1 hgt i.isLt))

lemma C16_val_inj {i j : Fin 16} (h : C16_val i.val = C16_val j.val) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.2.2.2.2.2.1 hlt j.isLt))
  · exact absurd h.symm (Nat.ne_of_lt (strictMono_of_step part1_tables_spec.2.2.2.2.2.2.2.2.2.2.1 hgt i.isLt))

lemma A27_val_surj (p : Fin 64) (hp0 : p.val ≠ 0) (hq : Q3_form 9 p.val = 0) :
    ∃ i : Fin 27, A27_val i.val = p.val := by
  have hc := part1_tables_spec.2.2.2.1 p.val p.isLt hp0 hq
  rw [List.contains_eq_mem, decide_eq_true_eq] at hc
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  have hilt : i < 27 := by rwa [part1_tables_spec.1.1] at hi
  exact ⟨⟨i, hilt⟩, by simp only [A27_val, p1_getD_eq_getElem _ _ hi, heq]⟩

lemma B36_val_surj (p : Fin 64) (hp0 : p.val ≠ 0) (hq : Q3_form 9 p.val = 1) :
    ∃ i : Fin 36, B36_val i.val = p.val := by
  have hc := part1_tables_spec.2.2.2.2.2.2.1 p.val p.isLt hp0 hq
  rw [List.contains_eq_mem, decide_eq_true_eq] at hc
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  have hilt : i < 36 := by rwa [part1_tables_spec.1.2.1] at hi
  exact ⟨⟨i, hilt⟩, by simp only [B36_val, p1_getD_eq_getElem _ _ hi, heq]⟩

lemma V11_val_surj (p : Fin 64) (hp0 : p.val ≠ 0) (hq : Q3_form 9 p.val = 0) (hs : symp3 2 p.val = 0) :
    ∃ i : Fin 11, V11_val i.val = p.val := by
  obtain ⟨a, ha⟩ := A27_val_surj p hp0 hq
  have hpart := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.1 a.val a.isLt
  rw [ha, hs] at hpart; simp only [beq_self_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at hpart
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hpart
  have hilt : i < 11 := by rwa [part1_tables_spec.1.2.2.1] at hi
  exact ⟨⟨i, hilt⟩, by simp only [V11_val, p1_getD_eq_getElem _ _ hi, heq]⟩

lemma C16_val_surj (p : Fin 64) (hp0 : p.val ≠ 0) (hq : Q3_form 9 p.val = 0) (hs : symp3 2 p.val = 1) :
    ∃ i : Fin 16, C16_val i.val = p.val := by
  obtain ⟨a, ha⟩ := A27_val_surj p hp0 hq
  have hpart := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.1 a.val a.isLt
  rw [ha, hs] at hpart
  simp only [show (1 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte,
    List.contains_eq_mem, decide_eq_true_eq] at hpart
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hpart
  have hilt : i < 16 := by rwa [part1_tables_spec.1.2.2.2] at hi
  exact ⟨⟨i, hilt⟩, by simp only [C16_val, p1_getD_eq_getElem _ _ hi, heq]⟩

lemma A27_pt_mem_Qminus (i : Fin 27) : dec3 (A27_pt i) ∈ Qminus c0_09 := by
  have hp := part1_tables_spec.2.1 i.val i.isLt
  simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  refine ⟨fun h => hp.1 ?_, by simp only [c0_09, quadForm_dec3, A27_pt, hp.2.2]; rfl⟩
  have := congr_arg (fun w => (enc3 w).val) h
  rw [enc3_dec3] at this
  have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
  rw [h0] at this; exact this

lemma V11_idxOf_val (i : Fin 11) : V11_list.idxOf? (V11_val i.val) = some i.val := by
  have hilt : i.val < V11_list.length := by rw [part1_tables_spec.1.2.2.1]; exact i.isLt
  have hmem : V11_val i.val = V11_list[i.val] := p1_getD_eq_getElem _ _ hilt
  rw [hmem, List.idxOf?_eq_some_iff]
  refine ⟨hilt, rfl, fun j hj heq => ?_⟩
  have hj11 : j < 11 := by omega
  have heq' : V11_val j = V11_val i.val := by
    simp only [V11_val, p1_getD_eq_getElem _ _ (by omega : j < V11_list.length),
      p1_getD_eq_getElem _ _ hilt]; exact heq
  exact absurd (congr_arg Fin.val (V11_val_inj (i := ⟨j, hj11⟩) (j := i) heq')) (Nat.ne_of_lt hj)

lemma C16_idxOf_val (i : Fin 16) : C16_list.idxOf? (C16_val i.val) = some i.val := by
  have hilt : i.val < C16_list.length := by rw [part1_tables_spec.1.2.2.2]; exact i.isLt
  have hmem : C16_val i.val = C16_list[i.val] := p1_getD_eq_getElem _ _ hilt
  rw [hmem, List.idxOf?_eq_some_iff]
  refine ⟨hilt, rfl, fun j hj heq => ?_⟩
  have hj16 : j < 16 := by omega
  have heq' : C16_val j = C16_val i.val := by
    simp only [C16_val, p1_getD_eq_getElem _ _ (by omega : j < C16_list.length),
      p1_getD_eq_getElem _ _ hilt]; exact heq
  exact absurd (congr_arg Fin.val (C16_val_inj (i := ⟨j, hj16⟩) (j := i) heq')) (Nat.ne_of_lt hj)

lemma V11_idxOf_none_of_C16 (i : Fin 16) : V11_list.idxOf? (C16_val i.val) = none := by
  rw [List.idxOf?_eq_none_iff]
  intro hmem
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
  have hj11 : j < 11 := by rwa [part1_tables_spec.1.2.2.1] at hj
  have h1 := (part1_tables_spec.2.2.2.2.2.2.2.1 j hj11).2.2.2
  have h2 := (part1_tables_spec.2.2.2.2.2.2.2.2.2.1 i.val i.isLt).2.2.2
  rw [V11_val, p1_getD_eq_getElem _ _ hj, heq] at h1
  omega

/-- Convert a list of `Nat` transvection generators `< 64` to `List (PauliIdx 3)`. -/
def word3FromNat (us : List Nat) : List (PauliIdx 3) :=
  us.map fun u => dec3 ⟨u % 64, Nat.mod_lt _ (by omega)⟩

lemma word3FromNat_append (us vs : List Nat) :
    word3FromNat (us ++ vs) = word3FromNat us ++ word3FromNat vs := List.map_append

lemma applyTransvWord_append {n : ℕ} (us vs : List (PauliIdx n)) (s : PauliIdx n → ℤ) :
    applyTransvWord (us ++ vs) s = applyTransvWord vs (applyTransvWord us s) := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih => simp only [List.cons_append, applyTransvWord, ih]

lemma applyGauge_applyGauge {n : ℕ} (g1 g2 : PauliIdx n) (s : PauliIdx n → ℤ) :
    applyGauge g1 (applyGauge g2 s) = applyGauge (g1 + g2) s := by
  ext p; simp only [applyGauge, ← mul_assoc, sympSign_add_left]

lemma applyTransv_applyGauge {n : ℕ} (u g : PauliIdx n) (s : PauliIdx n → ℤ) :
    applyTransv u (applyGauge g s) = applyGauge (transvPt u g) (applyTransv u s) := by
  ext p
  simp only [applyTransv, applyGauge]
  have hsg : sympSign g (transvPt u p) = sympSign (transvPt u g) p := by
    simp only [sympSign]
    rw [← symp_transvPt u g (transvPt u p), transvPt_invol]
  rw [hsg]; ring

lemma applyTransvWord_applyGauge {n : ℕ} (us : List (PauliIdx n)) (g : PauliIdx n) (s : PauliIdx n → ℤ) :
    ∃ g' : PauliIdx n, applyTransvWord us (applyGauge g s) = applyGauge g' (applyTransvWord us s) := by
  induction us generalizing g s with
  | nil => exact ⟨g, rfl⟩
  | cons u us ih =>
    simp only [applyTransvWord, applyTransv_applyGauge]
    exact ih (transvPt u g) (applyTransv u s)

lemma applyWord3Nat_eq_on_inv (S : Nat → Bool) (us : List Nat)
    (hinv : ∀ u ∈ us, u < 64 ∧ ∀ v < 64, S v = true → S (transv3_pt u v) = true)
    (sNat : Nat → ℤ) (s3 : PauliIdx 3 → ℤ)
    (hagree : ∀ v : Fin 64, S v.val = true → sNat v.val = s3 (dec3 v)) :
    ∀ v : Fin 64, S v.val = true →
      applyWord3Nat us sNat v.val = applyTransvWord (word3FromNat us) s3 (dec3 v) := by
  induction us generalizing sNat s3 with
  | nil => intro v hv; exact hagree v hv
  | cons u us ih =>
    have hu := hinv u (List.mem_cons_self ..)
    have hrest : ∀ w ∈ us, w < 64 ∧ ∀ v < 64, S v = true → S (transv3_pt w v) = true :=
      fun w hw => hinv w (List.mem_cons_of_mem u hw)
    simp only [applyWord3Nat, List.foldl_cons, word3FromNat, List.map_cons, applyTransvWord]
    refine ih hrest _ (applyTransv (dec3 ⟨u % 64, Nat.mod_lt _ (by omega)⟩) s3) ?_
    intro v hv
    have humod : u % 64 = u := Nat.mod_eq_of_lt hu.1
    let uF : Fin 64 := ⟨u, hu.1⟩
    have huf_eq : (⟨u % 64, Nat.mod_lt _ (by omega)⟩ : Fin 64) = uF := Fin.ext humod
    rw [huf_eq]
    have htv_lt : transv3_pt u v.val < 64 := transv3_pt_lt uF v
    have htv_S : S (transv3_pt u v.val) = true := hu.2 v.val v.isLt hv
    have hag := hagree ⟨transv3_pt u v.val, htv_lt⟩ htv_S
    simp only [applyTransv, transvPt_dec3, transvSgn_dec3]
    change transv3_sgn u v.val * sNat (transv3_pt u v.val) =
      transv3_sgn u v.val * s3 (dec3 ⟨transv3_pt u v.val, htv_lt⟩)
    rw [hag]

lemma applyGauge3Nat_eq (g : Fin 64) (sNat : Nat → ℤ) (s3 : PauliIdx 3 → ℤ)
    (v : Fin 64) (hv : sNat v.val = s3 (dec3 v)) :
    applyGauge3Nat g.val sNat v.val = applyGauge (dec3 g) s3 (dec3 v) := by
  simp only [applyGauge3Nat, applyGauge, sympSign, symp_dec3, hv]
  have hlt := symp3_lt2 g.val v.val
  generalize symp3 g.val v.val = k at hlt ⊢
  interval_cases k <;> simp

private lemma pop8_eq_card (x : Nat) (hx : x < 256) :
    pop8 x = ((Finset.univ : Finset (Fin 8)).filter fun i => ((x >>> i.val) &&& 1) = 1).card := by
  rw [part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx, p1_foldl_sum_range, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hlt : (x >>> i.val) &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
  generalize (x >>> i.val) &&& 1 = k at hlt ⊢; interval_cases k <;> simp

private lemma pop16_eq_card (m : Nat) :
    pop16 m = ((Finset.univ : Finset (Fin 16)).filter fun i => ((m >>> i.val) &&& 1) = 1).card := by
  have hlo_lt : (m &&& 255) < 256 := by rw [Nat.and_two_pow_sub_one_eq_mod m 8]; exact Nat.mod_lt _ (by omega)
  have hhi_lt : ((m >>> 8) &&& 255) < 256 := by rw [Nat.and_two_pow_sub_one_eq_mod _ 8]; exact Nat.mod_lt _ (by omega)
  simp only [pop16, show ∀ a b, Nat.add a b = a + b from fun _ _ => rfl,
    show ∀ a b, Nat.land a b = a &&& b from fun _ _ => rfl,
    show ∀ a b, Nat.shiftRight a b = a >>> b from fun _ _ => rfl]
  rw [pop8_eq_card _ hlo_lt, pop8_eq_card _ hhi_lt, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin 16 => i.val < 8)]
  congr 1
  · refine Finset.sum_bij (fun (i : Fin 8) _ => (⟨i.val, by omega⟩ : Fin 16))
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩)
      (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
      (fun j hj => ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun i _ => ?_)
    have hbit : (((m &&& 255) >>> i.val) &&& 1) = ((m >>> i.val) &&& 1) := by
      have hi : i.val < 8 := i.isLt
      have htest : ∀ a b, ((a >>> b) &&& 1) = if a.testBit b then 1 else 0 := fun a b => by
        rw [Nat.testBit, Nat.and_one_is_mod]; split_ifs with h <;> simp_all
      rw [htest, htest, Nat.testBit_and]
      have h255 : (255 : Nat).testBit i.val = true := by
        have := i.isLt; interval_cases i.val <;> decide
      simp [h255]
    simp [hbit]
  · refine Finset.sum_bij (fun (i : Fin 8) _ => (⟨8 + i.val, by omega⟩ : Fin 16))
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩)
      (fun a _ b _ h => Fin.ext (by have := congr_arg Fin.val h; dsimp at this; omega))
      (fun j hj => ⟨⟨j.val - 8, by have := j.isLt; have := (Finset.mem_filter.mp hj).2; omega⟩,
        Finset.mem_univ _, Fin.ext (by have := (Finset.mem_filter.mp hj).2; dsimp; omega)⟩)
      (fun i _ => ?_)
    have hbit : ((((m >>> 8) &&& 255) >>> i.val) &&& 1) = ((m >>> (8 + i.val)) &&& 1) := by
      have htest : ∀ a b, ((a >>> b) &&& 1) = if a.testBit b then 1 else 0 := fun a b => by
        rw [Nat.testBit, Nat.and_one_is_mod]; split_ifs with h <;> simp_all
      rw [htest, htest, Nat.testBit_and, Nat.testBit_shiftRight]
      have h255 : (255 : Nat).testBit i.val = true := by
        have := i.isLt; interval_cases i.val <;> decide
      simp [h255]
    simp [hbit]

def p0_2 : PauliIdx 3 := dec3 ⟨2, by decide⟩

def starFrust (s3 : PauliIdx 3 → ℤ) (p : PauliIdx 3) : ℕ :=
  frustPairs ((Qminus c0_09).filter fun q => symp p q = 0) s3

lemma starFrust_applyGauge (g : PauliIdx 3) (s3 : PauliIdx 3 → ℤ) (p : PauliIdx 3) :
    starFrust (applyGauge g s3) p = starFrust s3 p :=
  frustPairs_applyGauge _ g s3

lemma applyTransv_preserves_Qminus09 {u : PauliIdx 3} (hu : quadForm c0_09 u = 1)
    (s3 : PauliIdx 3 → ℤ) :
    frustPairs (Qminus c0_09) (applyTransv u s3) = frustPairs (Qminus c0_09) s3 := by
  refine frustPairs_applyTransv u (Qminus c0_09) (Qminus c0_09) (fun p => ?_) s3
  simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    quadForm_transvPt_fix hu]
  exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
         fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩

lemma starFrust_applyTransv {u : PauliIdx 3} (hu : quadForm c0_09 u = 1)
    (s3 : PauliIdx 3 → ℤ) (p : PauliIdx 3) :
    starFrust (applyTransv u s3) p = starFrust s3 (transvPt u p) := by
  refine frustPairs_applyTransv u _ _ (fun q => ?_) s3
  simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    quadForm_transvPt_fix hu, symp_transvPt]
  exact ⟨fun ⟨⟨hq0, hq⟩, hs⟩ => ⟨⟨fun h0 => hq0 (by rw [← transvPt_invol u q, h0, transvPt_zero]), hq⟩, hs⟩,
         fun ⟨⟨ht0, hq⟩, hs⟩ => ⟨⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), hq⟩, hs⟩⟩

lemma applyTransvWord_preserves_Qminus09 {us : List (PauliIdx 3)}
    (hus : ∀ u ∈ us, quadForm c0_09 u = 1) (s3 : PauliIdx 3 → ℤ) :
    frustPairs (Qminus c0_09) (applyTransvWord us s3) = frustPairs (Qminus c0_09) s3 := by
  induction us generalizing s3 with
  | nil => rfl
  | cons u us ih =>
    simp only [applyTransvWord]
    rw [ih (fun w hw => hus w (List.mem_cons_of_mem u hw)),
        applyTransv_preserves_Qminus09 (hus u (List.mem_cons_self ..))]

lemma starFrust_applyTransvWord {us : List (PauliIdx 3)}
    (hus : ∀ u ∈ us, quadForm c0_09 u = 1) (s3 : PauliIdx 3 → ℤ) (p : PauliIdx 3) :
    starFrust (applyTransvWord us s3) p =
      starFrust s3 (us.foldr (fun u cur => transvPt u cur) p) := by
  induction us generalizing s3 p with
  | nil => rfl
  | cons u us ih =>
    simp only [applyTransvWord, List.foldr_cons]
    rw [ih (fun w hw => hus w (List.mem_cons_of_mem u hw)),
        starFrust_applyTransv (hus u (List.mem_cons_self ..))]

private lemma foldl_transvPt_iff_foldr {n : ℕ} (us : List (PauliIdx n)) (p q : PauliIdx n) :
    us.foldl (fun cur u => transvPt u cur) p = q ↔
      us.foldr (fun u cur => transvPt u cur) q = p := by
  induction us generalizing p with
  | nil => simp [eq_comm]
  | cons u us ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih]
    constructor
    · intro h; rw [h, transvPt_invol]
    · intro h; rw [← h, transvPt_invol]

/-- **6-line Mermin–Peres Grid in `Q⁻(5,2)`**: every sign assignment has at least one frustrated
    line in `Qminus c0_09`, hence `∃ p ∈ Qminus c0_09, 0 < starFrust s3 p`! -/
private lemma exists_starFrust_pos {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3) :
    ∃ p ∈ Qminus c0_09, 0 < starFrust s3 p := by
  let pt : Fin 27 → PauliIdx 3 := fun i => dec3 (A27_pt i)
  have hsq : ∀ i : Fin 27, s3 (pt i) * s3 (pt i) = 1 := fun i => by
    have h0 : pt i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (A27_pt_mem_Qminus i)).1).1
    rcases hs3.2 _ h0 with h | h <;> rw [h] <;> norm_num
  have hL : ∀ (a b c : Fin 27) (g : ℤ),
      A27_val a.val ≠ A27_val b.val → symp3 (A27_val a.val) (A27_val b.val) = 0 →
      (A27_val a.val ^^^ A27_val b.val) = A27_val c.val → gamma3_sgn (A27_val a.val) (A27_val b.val) = g →
      pt a ≠ pt b ∧ symp (pt a) (pt b) = 0 ∧ pt a + pt b = pt c ∧ gammaSgn (pt a) (pt b) = g := by
    intro a b c g hne hsp hxor hgam
    refine ⟨fun h => hne (congr_arg Fin.val (equiv3.symm.injective h)),
      by simp only [pt, symp_dec3, A27_pt, hsp]; rfl, ?_,
      by simp only [pt, gammaSgn_dec3, A27_pt, hgam]⟩
    have hx := dec3_xor (A27_pt a) (A27_pt b)
    rw [← hx]; congr 1; exact Fin.ext hxor
  have h1 := hL ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ 1 (by decide) (by decide) (by decide) (by decide)
  have h2 := hL ⟨3, by decide⟩ ⟨11, by decide⟩ ⟨19, by decide⟩ 1 (by decide) (by decide) (by decide) (by decide)
  have h3 := hL ⟨5, by decide⟩ ⟨12, by decide⟩ ⟨22, by decide⟩ (-1) (by decide) (by decide) (by decide) (by decide)
  have h4 := hL ⟨0, by decide⟩ ⟨11, by decide⟩ ⟨12, by decide⟩ 1 (by decide) (by decide) (by decide) (by decide)
  have h5 := hL ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩ 1 (by decide) (by decide) (by decide) (by decide)
  have h6 := hL ⟨2, by decide⟩ ⟨19, by decide⟩ ⟨22, by decide⟩ 1 (by decide) (by decide) (by decide) (by decide)
  let v := fun (a b : Fin 27) => gammaSgn (pt a) (pt b) * s3 (pt a) * s3 (pt b) * s3 (pt a + pt b)
  have hprod : v ⟨0, by decide⟩ ⟨1, by decide⟩ * v ⟨3, by decide⟩ ⟨11, by decide⟩ *
      v ⟨5, by decide⟩ ⟨12, by decide⟩ * v ⟨0, by decide⟩ ⟨11, by decide⟩ *
      v ⟨1, by decide⟩ ⟨3, by decide⟩ * v ⟨2, by decide⟩ ⟨19, by decide⟩ = -1 := by
    simp only [v, h1.2.2.1, h1.2.2.2, h2.2.2.1, h2.2.2.2, h3.2.2.1, h3.2.2.2,
      h4.2.2.1, h4.2.2.2, h5.2.2.1, h5.2.2.2, h6.2.2.1, h6.2.2.2]
    have s0 := hsq ⟨0, by decide⟩; have s1 := hsq ⟨1, by decide⟩; have s2 := hsq ⟨2, by decide⟩
    have s3_ := hsq ⟨3, by decide⟩; have s5 := hsq ⟨5, by decide⟩; have s11 := hsq ⟨11, by decide⟩
    have s12 := hsq ⟨12, by decide⟩; have s19 := hsq ⟨19, by decide⟩; have s22 := hsq ⟨22, by decide⟩
    have hrearr :
        (1 * s3 (pt ⟨0, by decide⟩) * s3 (pt ⟨1, by decide⟩) * s3 (pt ⟨2, by decide⟩)) *
        (1 * s3 (pt ⟨3, by decide⟩) * s3 (pt ⟨11, by decide⟩) * s3 (pt ⟨19, by decide⟩)) *
        ((-1) * s3 (pt ⟨5, by decide⟩) * s3 (pt ⟨12, by decide⟩) * s3 (pt ⟨22, by decide⟩)) *
        (1 * s3 (pt ⟨0, by decide⟩) * s3 (pt ⟨11, by decide⟩) * s3 (pt ⟨12, by decide⟩)) *
        (1 * s3 (pt ⟨1, by decide⟩) * s3 (pt ⟨3, by decide⟩) * s3 (pt ⟨5, by decide⟩)) *
        (1 * s3 (pt ⟨2, by decide⟩) * s3 (pt ⟨19, by decide⟩) * s3 (pt ⟨22, by decide⟩)) =
        -(s3 (pt ⟨0, by decide⟩) * s3 (pt ⟨0, by decide⟩)) *
         (s3 (pt ⟨1, by decide⟩) * s3 (pt ⟨1, by decide⟩)) *
         (s3 (pt ⟨2, by decide⟩) * s3 (pt ⟨2, by decide⟩)) *
         (s3 (pt ⟨3, by decide⟩) * s3 (pt ⟨3, by decide⟩)) *
         (s3 (pt ⟨5, by decide⟩) * s3 (pt ⟨5, by decide⟩)) *
         (s3 (pt ⟨11, by decide⟩) * s3 (pt ⟨11, by decide⟩)) *
         (s3 (pt ⟨12, by decide⟩) * s3 (pt ⟨12, by decide⟩)) *
         (s3 (pt ⟨19, by decide⟩) * s3 (pt ⟨19, by decide⟩)) *
         (s3 (pt ⟨22, by decide⟩) * s3 (pt ⟨22, by decide⟩)) := by ring
    rw [hrearr, s0, s1, s2, s3_, s5, s11, s12, s19, s22]; norm_num
  have hv_pm1 : ∀ a b : Fin 27, pt a ≠ pt b → v a b = 1 ∨ v a b = -1 := fun a b hne => by
    have ha0 : pt a ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (A27_pt_mem_Qminus a)).1).1
    have hb0 : pt b ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (A27_pt_mem_Qminus b)).1).1
    have hab0 : pt a + pt b ≠ 0 := fun h => hne (by have := congr_arg (pt a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hmul : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → x * y = 1 ∨ x * y = -1 := by
      rintro x y (rfl | rfl) (rfl | rfl) <;> decide
    exact hmul _ _ (hmul _ _ (hmul _ _ (gammaSgn_eq_pm1 _ _) (hs3.2 _ ha0)) (hs3.2 _ hb0)) (hs3.2 _ hab0)
  have hit : ∀ a b : Fin 27, pt a ≠ pt b → symp (pt a) (pt b) = 0 → v a b = -1 →
      ∃ p ∈ Qminus c0_09, 0 < starFrust s3 p := fun a b hne hsp hfr => by
    refine ⟨pt a, A27_pt_mem_Qminus a, ?_⟩
    unfold starFrust frustPairs
    refine Finset.card_pos.mpr ⟨(pt a, pt b), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨A27_pt_mem_Qminus a, symp_self _⟩, ⟨A27_pt_mem_Qminus b, hsp⟩⟩, hne, hsp, hfr⟩
  by_cases c1 : v ⟨0, by decide⟩ ⟨1, by decide⟩ = -1
  · exact hit _ _ h1.1 h1.2.1 c1
  by_cases c2 : v ⟨3, by decide⟩ ⟨11, by decide⟩ = -1
  · exact hit _ _ h2.1 h2.2.1 c2
  by_cases c3 : v ⟨5, by decide⟩ ⟨12, by decide⟩ = -1
  · exact hit _ _ h3.1 h3.2.1 c3
  by_cases c4 : v ⟨0, by decide⟩ ⟨11, by decide⟩ = -1
  · exact hit _ _ h4.1 h4.2.1 c4
  by_cases c5 : v ⟨1, by decide⟩ ⟨3, by decide⟩ = -1
  · exact hit _ _ h5.1 h5.2.1 c5
  by_cases c6 : v ⟨2, by decide⟩ ⟨19, by decide⟩ = -1
  · exact hit _ _ h6.1 h6.2.1 c6
  have e1 : v ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := (hv_pm1 _ _ h1.1).resolve_right c1
  have e2 : v ⟨3, by decide⟩ ⟨11, by decide⟩ = 1 := (hv_pm1 _ _ h2.1).resolve_right c2
  have e3 : v ⟨5, by decide⟩ ⟨12, by decide⟩ = 1 := (hv_pm1 _ _ h3.1).resolve_right c3
  have e4 : v ⟨0, by decide⟩ ⟨11, by decide⟩ = 1 := (hv_pm1 _ _ h4.1).resolve_right c4
  have e5 : v ⟨1, by decide⟩ ⟨3, by decide⟩ = 1 := (hv_pm1 _ _ h5.1).resolve_right c5
  have e6 : v ⟨2, by decide⟩ ⟨19, by decide⟩ = 1 := (hv_pm1 _ _ h6.1).resolve_right c6
  rw [e1, e2, e3, e4, e5, e6] at hprod; norm_num at hprod

/-- Double counting on `Q⁻(5,2)`: `∑_{p ∈ Qminus c0_09} starFrust s3 p = 3 * frustPairs (Qminus c0_09) s3`. -/
private lemma double_count_starFrust (s3 : PauliIdx 3 → ℤ) :
    ∑ p ∈ Qminus c0_09, starFrust s3 p = 3 * frustPairs (Qminus c0_09) s3 := by
  let P := ((Qminus c0_09) ×ˢ (Qminus c0_09)).filter fun ab =>
    ab.1 ≠ ab.2 ∧ symp ab.1 ab.2 = 0 ∧ gammaSgn ab.1 ab.2 * s3 ab.1 * s3 ab.2 * s3 (ab.1 + ab.2) = -1
  have h1 : ∀ p ∈ Qminus c0_09, starFrust s3 p =
      (P.filter fun ab => symp p ab.1 = 0 ∧ symp p ab.2 = 0).card := fun p _ => by
    unfold starFrust frustPairs
    refine Finset.card_bij (fun ab _ => ab) ?_ (fun _ _ _ _ h => h) ?_
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_product, P] at hab ⊢
      exact ⟨⟨⟨hab.1.1.1, hab.1.2.1⟩, hab.2⟩, hab.1.1.2, hab.1.2.2⟩
    · rintro ⟨a, b⟩ hab
      refine ⟨(a, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, P] at hab ⊢
      exact ⟨⟨⟨hab.1.1.1, hab.2.1⟩, ⟨hab.1.1.2, hab.2.2⟩⟩, hab.1.2⟩
  rw [Finset.sum_congr rfl h1]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ ab ∈ P,
      (∑ p ∈ Qminus c0_09, if symp p ab.1 = 0 ∧ symp p ab.2 = 0 then 1 else 0) = 3 := by
    rintro ⟨a, b⟩ hab
    simp only [P, Finset.mem_filter, Finset.mem_product, Qminus, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true] at hab
    have h0e : (enc3 0).val = 0 := by
      have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      exact congr_arg Fin.val this
    have ha0 : (enc3 a).val ≠ 0 := fun h => hab.1.1.1 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
    have hb0 : (enc3 b).val ≠ 0 := fun h => hab.1.2.1 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
    have haQ : Q3_form 9 (enc3 a).val = 0 := by
      have h : quadForm c0_09 (dec3 (enc3 a)) = 0 := by rw [dec3_enc3]; exact hab.1.1.2
      rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 a).val
      generalize Q3_form 9 (enc3 a).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    have hbQ : Q3_form 9 (enc3 b).val = 0 := by
      have h : quadForm c0_09 (dec3 (enc3 b)) = 0 := by rw [dec3_enc3]; exact hab.1.2.2
      rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 b).val
      generalize Q3_form 9 (enc3 b).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    obtain ⟨ia, hia⟩ := A27_val_surj (enc3 a) ha0 haQ
    obtain ⟨ib, hib⟩ := A27_val_surj (enc3 b) hb0 hbQ
    have hda : dec3 (A27_pt ia) = a := by rw [show A27_pt ia = enc3 a from Fin.ext hia, dec3_enc3]
    have hdb : dec3 (A27_pt ib) = b := by rw [show A27_pt ib = enc3 b from Fin.ext hib, dec3_enc3]
    have hne : ia.val ≠ ib.val := fun h => hab.2.1 (by rw [← hda, ← hdb, Fin.ext h])
    have hsp : symp3 (A27_val ia.val) (A27_val ib.val) = 0 := by
      have h := hab.2.2.1; rw [← hda, ← hdb, symp_dec3] at h
      change ((symp3 (A27_val ia.val) (A27_val ib.val) : Nat) : ZMod 2) = 0 at h
      have hlt := symp3_lt2 (A27_val ia.val) (A27_val ib.val)
      generalize symp3 (A27_val ia.val) (A27_val ib.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    have hchk := p1_all_range (p1_all_range checkA27Common3_ok ia.isLt) ib.isLt
    simp only [beq_false_of_ne hne, hsp, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, beq_iff_eq] at hchk
    rw [p1_list_range_filter_len] at hchk
    rw [← Finset.card_filter]
    trans ((Finset.univ : Finset (Fin 27)).filter fun k =>
        (symp3 (A27_val k.val) (A27_val ia.val) == 0 && symp3 (A27_val k.val) (A27_val ib.val) == 0) = true).card
    · symm
      refine Finset.card_bij (fun k _ => dec3 (A27_pt k)) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hk
        simp only [Finset.mem_filter, A27_pt_mem_Qminus, true_and]
        rw [← hda, ← hdb, symp_dec3, symp_dec3]
        exact ⟨by simp [A27_pt, hk.1], by simp [A27_pt, hk.2]⟩
      · intro k1 _ k2 _ h
        exact A27_val_inj (congr_arg Fin.val (equiv3.symm.injective h))
      · intro p hp
        simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true] at hp
        have hp0n : (enc3 p).val ≠ 0 := fun h => hp.1.1 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
        have hpQ : Q3_form 9 (enc3 p).val = 0 := by
          have h : quadForm c0_09 (dec3 (enc3 p)) = 0 := by rw [dec3_enc3]; exact hp.1.2
          rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 p).val
          generalize Q3_form 9 (enc3 p).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
        obtain ⟨k, hk⟩ := A27_val_surj (enc3 p) hp0n hpQ
        have hdk : dec3 (A27_pt k) = p := by rw [show A27_pt k = enc3 p from Fin.ext hk, dec3_enc3]
        refine ⟨k, ?_, hdk⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq]
        have h1 := hp.2.1; rw [← hdk, ← hda, symp_dec3] at h1
        have h2 := hp.2.2; rw [← hdk, ← hdb, symp_dec3] at h2
        change ((symp3 (A27_val k.val) (A27_val ia.val) : Nat) : ZMod 2) = 0 at h1
        change ((symp3 (A27_val k.val) (A27_val ib.val) : Nat) : ZMod 2) = 0 at h2
        have hs1 : symp3 (A27_val k.val) (A27_val ia.val) = 0 := by
          have hlt := symp3_lt2 (A27_val k.val) (A27_val ia.val)
          generalize symp3 (A27_val k.val) (A27_val ia.val) = m at hlt h1 ⊢; interval_cases m; rfl; exact absurd h1 (by decide)
        have hs2 : symp3 (A27_val k.val) (A27_val ib.val) = 0 := by
          have hlt := symp3_lt2 (A27_val k.val) (A27_val ib.val)
          generalize symp3 (A27_val k.val) (A27_val ib.val) = m at hlt h2 ⊢; interval_cases m; rfl; exact absurd h2 (by decide)
        exact ⟨hs1, hs2⟩
    · exact hchk
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]; rfl

private lemma card_four_split_symp {α : Type*} (U : Finset (α × α)) (f : α → ZMod 2) :
    U.card =
      (U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 0).card +
      (U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 1).card +
      (U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 0).card +
      (U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 1).card := by
  let PAA := U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 0
  let PBB := U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 1
  let PBA := U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 0
  let PAB := U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 1
  have hu : U = (PAA ∪ PBB) ∪ (PBA ∪ PAB) := by
    ext ⟨p, q⟩; simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases zmod2_cases (f p) with h1 | h1 <;> rcases zmod2_cases (f q) with h2 | h2
      · left; left; exact ⟨hp, h1, h2⟩
      · right; right; exact ⟨hp, h1, h2⟩
      · right; left; exact ⟨hp, h1, h2⟩
      · left; right; exact ⟨hp, h1, h2⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)) <;> exact h
  have hd1 : Disjoint PAA PBB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd2 : Disjoint PBA PAB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PBA, PAB, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd3 : Disjoint (PAA ∪ PBB) (PBA ∪ PAB) := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨_, h1a, h1b⟩ | ⟨_, h1a, h1b⟩ <;> rcases h2 with ⟨_, h2a, h2b⟩ | ⟨_, h2a, h2b⟩
    · rw [h1a] at h2a; exact absurd h2a (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1a] at h2a; exact absurd h2a (by decide)
  conv_lhs => rw [hu]
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint hd2]
  dsimp only [PAA, PBB, PBA, PAB]
  ring

/-- Exact `V₁₁ ⊔ C₁₆` split of `frustPairs (Qminus c0_09) s3`:
    `frustPairs (Qminus c0_09) s3 = starFrust s3 p0_2 + 3 * NBB_16`. -/
private lemma frustPairs_Qminus09_V11_C16_split (s3 : PauliIdx 3 → ℤ) :
    let SB := (Qminus c0_09).filter fun p => symp p0_2 p = 1
    let NBB := ((SB ×ˢ SB).filter fun pq =>
      pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
      gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1).card
    frustPairs (Qminus c0_09) s3 = starFrust s3 p0_2 + 3 * NBB := by
  intro SB NBB
  let S := Qminus c0_09
  have hclosed : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → symp p q = 0 → p + q ∈ S := by
    intro p hp q hq hne hsp
    simp only [S, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
    exact ⟨fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm),
      by rw [quadForm_add, hp.2, hq.2, hsp]; simp⟩
  let P := (S ×ˢ S).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧ gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1
  let PAA := P.filter fun pq => symp p0_2 pq.1 = 0 ∧ symp p0_2 pq.2 = 0
  let PBB := P.filter fun pq => symp p0_2 pq.1 = 1 ∧ symp p0_2 pq.2 = 1
  let PBA := P.filter fun pq => symp p0_2 pq.1 = 1 ∧ symp p0_2 pq.2 = 0
  let PAB := P.filter fun pq => symp p0_2 pq.1 = 0 ∧ symp p0_2 pq.2 = 1
  have hAA_card : PAA.card = starFrust s3 p0_2 := by
    unfold starFrust frustPairs
    refine Finset.card_bij (fun pq _ => pq) ?_ (fun _ _ _ _ h => h) ?_
    · rintro ⟨p, q⟩ hpq
      simp only [PAA, P, S, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨⟨⟨hpq.1.1.1, hpq.2.1⟩, ⟨hpq.1.1.2, hpq.2.2⟩⟩, hpq.1.2⟩
    · rintro ⟨p, q⟩ hpq
      refine ⟨(p, q), ?_, rfl⟩
      simp only [PAA, P, S, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨⟨⟨hpq.1.1.1, hpq.1.2.1⟩, hpq.2⟩, hpq.1.1.2, hpq.1.2.2⟩
  have hBB_card : PBB.card = NBB := by
    refine Finset.card_bij (fun pq _ => pq) ?_ (fun _ _ _ _ h => h) ?_
    · rintro ⟨p, q⟩ hpq
      simp only [PBB, P, SB, S, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨⟨⟨hpq.1.1.1, hpq.2.1⟩, ⟨hpq.1.1.2, hpq.2.2⟩⟩, hpq.1.2⟩
    · rintro ⟨p, q⟩ hpq
      refine ⟨(p, q), ?_, rfl⟩
      simp only [PBB, P, SB, S, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      exact ⟨⟨⟨hpq.1.1.1, hpq.1.2.1⟩, hpq.2⟩, hpq.1.1.2, hpq.1.2.2⟩
  have hBA_card : PBA.card = NBB := by
    rw [← hBB_card]
    refine Finset.card_bij (fun pq _ => (pq.1, pq.1 + pq.2)) ?_ ?_ ?_
    · rintro ⟨p, q⟩ hpq
      simp only [PBA, PBB, P, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      rcases hpq with ⟨⟨⟨hpS, hqS⟩, hne, hsymp, hfr⟩, hsp, hsq⟩
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hqS).1).1
      refine ⟨⟨⟨hpS, hclosed p hpS q hqS hne hsymp⟩, ?_, ?_, ?_⟩, hsp, ?_⟩
      · intro h; exact hq0 (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
      · rw [symp_add_right, symp_self, hsymp, add_zero]
      · rw [gammaSgn_add_right hsymp, pauliIdx_add_cancel_left]; linarith
      · rw [symp_add_right, hsp, hsq, add_zero]
    · rintro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h
      refine Prod.ext h.1 ?_
      have h2 := congr_arg (p1 + ·) h.2
      rw [← h.1] at h2; simpa [pauliIdx_add_cancel_left] using h2
    · rintro ⟨a, b⟩ hab
      simp only [PBB, P, Finset.mem_filter, Finset.mem_product] at hab
      rcases hab with ⟨⟨⟨haS, hbS⟩, hne, hsymp, hfr⟩, hsa, hsb⟩
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hbS).1).1
      refine ⟨(a, a + b), ?_, Prod.ext rfl (pauliIdx_add_cancel_left a b)⟩
      simp only [PBA, P, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨haS, hclosed a haS b hbS hne hsymp⟩, ?_, ?_, ?_⟩, hsa, ?_⟩
      · intro h; exact hb0 (by have := congr_arg (a + ·) h; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
      · rw [symp_add_right, symp_self, hsymp, add_zero]
      · rw [gammaSgn_add_right hsymp, pauliIdx_add_cancel_left]; linarith
      · rw [symp_add_right, hsa, hsb]; decide
  have hAB_card : PAB.card = NBB := by
    rw [← hBA_card]
    refine Finset.card_bij (fun pq _ => (pq.2, pq.1)) ?_ ?_ ?_
    · rintro ⟨p, q⟩ hpq
      simp only [PAB, PBA, P, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      rcases hpq with ⟨⟨⟨hpS, hqS⟩, hne, hsymp, hfr⟩, hsp, hsq⟩
      refine ⟨⟨⟨hqS, hpS⟩, Ne.symm hne, by rwa [symp_comm], ?_⟩, hsq, hsp⟩
      rw [gammaSgn_comm (by rwa [symp_comm]), add_comm q p]; linarith
    · rintro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · rintro ⟨a, b⟩ hab
      simp only [PBA, P, Finset.mem_filter, Finset.mem_product] at hab
      rcases hab with ⟨⟨⟨haS, hbS⟩, hne, hsymp, hfr⟩, hsa, hsb⟩
      refine ⟨(b, a), ?_, rfl⟩
      simp only [PAB, P, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hbS, haS⟩, Ne.symm hne, by rwa [symp_comm], ?_⟩, hsb, hsa⟩
      rw [gammaSgn_comm (by rwa [symp_comm]), add_comm b a]; linarith
  change P.card = _
  rw [card_four_split_symp P (symp p0_2)]
  change PAA.card + PBB.card + PBA.card + PAB.card = _
  rw [hAA_card, hBB_card, hBA_card, hAB_card]
  omega

/-- Exact `starFrust s3 p0_2 = 6 * o` when `s3` matches `v11SignOfMask (orbRep_list[o])` on `V₁₁`. -/
private lemma starFrust_p0_eq_of_orb (o : Fin 6) {s3 : PauliIdx 3 → ℤ}
    (hV : ∀ i : Fin 11, s3 (dec3 (V11_pt i)) = v11SignOfMask (orbRep_list.getD o.val 0) i.val) :
    starFrust s3 p0_2 = 6 * o.val := by
  have hcnt := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 o.val o.isLt
  rw [← hcnt, p1_foldl_sum_range]
  let c := orbRep_list.getD o.val 0
  have hsum_card : (∑ i : Fin 11, ((List.range 11).filter fun j =>
      if i.val == j || symp3 (V11_val i.val) (V11_val j) != 0 then false
      else match V11_list.idxOf? (V11_val i.val ^^^ V11_val j) with
        | some k => gamma3_sgn (V11_val i.val) (V11_val j) * v11SignOfMask c i.val *
            v11SignOfMask c j * v11SignOfMask c k == -1
        | none => false).length) =
      ((Finset.univ : Finset (Fin 11 × Fin 11)).filter fun ij =>
        (if ij.1.val == ij.2.val || symp3 (V11_val ij.1.val) (V11_val ij.2.val) != 0 then false
         else match V11_list.idxOf? (V11_val ij.1.val ^^^ V11_val ij.2.val) with
           | some k => gamma3_sgn (V11_val ij.1.val) (V11_val ij.2.val) * v11SignOfMask c ij.1.val *
               v11SignOfMask c ij.2.val * v11SignOfMask c k == -1
           | none => false) = true).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [p1_list_range_filter_len, Finset.card_filter]
  rw [hsum_card]
  unfold starFrust frustPairs
  symm
  refine Finset.card_bij (fun ij _ => (dec3 (V11_pt ij.1), dec3 (V11_pt ij.2))) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    by_cases hbad : (i.val == j.val || symp3 (V11_val i.val) (V11_val j.val) != 0) = true
    · rw [if_pos hbad] at hij; exact absurd hij (by decide)
    · rw [if_neg hbad] at hij
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, not_not] at hbad
      rcases hbad with ⟨hne, hsp⟩
      have hpi := part1_tables_spec.2.2.2.2.2.2.2.1 i.val i.isLt
      have hpj := part1_tables_spec.2.2.2.2.2.2.2.1 j.val j.isLt
      have hmi : dec3 (V11_pt i) ∈ (Qminus c0_09).filter fun q => symp p0_2 q = 0 := by
        simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨⟨?_, by simp only [c0_09, quadForm_dec3, V11_pt, hpi.2.2.1]; rfl⟩,
          by simp only [p0_2, symp_dec3, V11_pt, hpi.2.2.2]; rfl⟩
        intro h; apply hpi.1
        have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this
        have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        rw [h0] at this; exact this
      have hmj : dec3 (V11_pt j) ∈ (Qminus c0_09).filter fun q => symp p0_2 q = 0 := by
        simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨⟨?_, by simp only [c0_09, quadForm_dec3, V11_pt, hpj.2.2.1]; rfl⟩,
          by simp only [p0_2, symp_dec3, V11_pt, hpj.2.2.2]; rfl⟩
        intro h; apply hpj.1
        have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this
        have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        rw [h0] at this; exact this
      cases hidx : V11_list.idxOf? (V11_val i.val ^^^ V11_val j.val) with
      | none => rw [hidx] at hij; simp at hij
      | some k =>
        rw [hidx, beq_iff_eq] at hij
        have hklt : k < 11 := by
          have := (List.idxOf?_eq_some_iff.mp hidx).1
          rwa [part1_tables_spec.1.2.2.1] at this
        have hkeq : V11_val k = V11_val i.val ^^^ V11_val j.val := by
          have := (List.idxOf?_eq_some_iff.mp hidx).2.1
          rw [V11_val, p1_getD_eq_getElem _ _ (by rw [part1_tables_spec.1.2.2.1]; exact hklt), this]
        have hadd : dec3 (V11_pt i) + dec3 (V11_pt j) = dec3 (V11_pt ⟨k, hklt⟩) := by
          rw [← dec3_xor]; congr 1; exact Fin.ext hkeq.symm
        simp only [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Finset.mem_filter.mp hmi, Finset.mem_filter.mp hmj⟩,
          fun h => hne (congr_arg Fin.val (V11_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))),
          by simp only [symp_dec3, V11_pt, hsp]; rfl, ?_⟩
        rw [hadd, gammaSgn_dec3, hV i, hV j, hV ⟨k, hklt⟩]
        exact hij
  · rintro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (V11_val_inj (congr_arg Fin.val (equiv3.symm.injective h.1)))
      (V11_val_inj (congr_arg Fin.val (equiv3.symm.injective h.2)))
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, Qminus, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true] at hpq
    rcases hpq with ⟨⟨⟨⟨hp0, hpQ⟩, hpS⟩, ⟨⟨hq0, hqQ⟩, hqS⟩⟩, hne, hsymp, hfr⟩
    have h0e : (enc3 0).val = 0 := by
      have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      exact congr_arg Fin.val this
    have hp0n : (enc3 p).val ≠ 0 := fun h => hp0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
    have hq0n : (enc3 q).val ≠ 0 := fun h => hq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
    have toQ0 : ∀ x : PauliIdx 3, quadForm c0_09 x = 0 → Q3_form 9 (enc3 x).val = 0 := fun x hx => by
      have h : quadForm c0_09 (dec3 (enc3 x)) = 0 := by rwa [dec3_enc3]
      rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 x).val
      generalize Q3_form 9 (enc3 x).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    have toS0 : ∀ x : PauliIdx 3, symp p0_2 x = 0 → symp3 2 (enc3 x).val = 0 := fun x hx => by
      have h : symp p0_2 (dec3 (enc3 x)) = 0 := by rwa [dec3_enc3]
      rw [p0_2, symp_dec3] at h; have hlt := symp3_lt2 2 (enc3 x).val
      generalize symp3 2 (enc3 x).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    obtain ⟨i, hi⟩ := V11_val_surj (enc3 p) hp0n (toQ0 p hpQ) (toS0 p hpS)
    obtain ⟨j, hj⟩ := V11_val_surj (enc3 q) hq0n (toQ0 q hqQ) (toS0 q hqS)
    have hdi : dec3 (V11_pt i) = p := by rw [show V11_pt i = enc3 p from Fin.ext hi, dec3_enc3]
    have hdj : dec3 (V11_pt j) = q := by rw [show V11_pt j = enc3 q from Fin.ext hj, dec3_enc3]
    have hpq0 : p + q ≠ 0 := fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hpqQ : quadForm c0_09 (p + q) = 0 := by rw [quadForm_add, hpQ, hqQ, hsymp]; simp
    have hpqS : symp p0_2 (p + q) = 0 := by rw [symp_add_right, hpS, hqS, add_zero]
    have hpq0n : (enc3 (p + q)).val ≠ 0 := fun h => hpq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
    obtain ⟨k, hk⟩ := V11_val_surj (enc3 (p + q)) hpq0n (toQ0 _ hpqQ) (toS0 _ hpqS)
    have hdk : dec3 (V11_pt k) = p + q := by rw [show V11_pt k = enc3 (p + q) from Fin.ext hk, dec3_enc3]
    have hxor : V11_val i.val ^^^ V11_val j.val = V11_val k.val := by
      have h1 : dec3 ⟨(V11_pt i).val ^^^ (V11_pt j).val, Nat.xor_lt_two_pow (n := 6) (V11_pt i).isLt (V11_pt j).isLt⟩ =
          dec3 (V11_pt k) := by rw [dec3_xor, hdi, hdj, hdk]
      exact congr_arg Fin.val (equiv3.symm.injective h1)
    have hij_ne : i.val ≠ j.val := fun h => hne (by rw [← hdi, ← hdj, Fin.ext h])
    have hij_sp : symp3 (V11_val i.val) (V11_val j.val) = 0 := by
      have h := hsymp; rw [← hdi, ← hdj, symp_dec3] at h
      change ((symp3 (V11_val i.val) (V11_val j.val) : Nat) : ZMod 2) = 0 at h
      have hlt := symp3_lt2 (V11_val i.val) (V11_val j.val)
      generalize symp3 (V11_val i.val) (V11_val j.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    refine ⟨(i, j), ?_, Prod.ext hdi hdj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_false_of_ne hij_ne, hij_sp,
      bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hxor, V11_idxOf_val k, beq_iff_eq]
    rw [← hV i, ← hV j, ← hV k, hdi, hdj, hdk]
    have hgam : gamma3_sgn (V11_val i.val) (V11_val j.val) = gammaSgn p q := by
      rw [← hdi, ← hdj, gammaSgn_dec3]; rfl
    rw [hgam]; exact hfr

/-- Master soundness of `checkTree16`: if `s3` agrees on `V₁₁` with `orbRep[o]` (`o ∈ 1..5`),
    matches `(am, nm)` on `C₁₆`, has `starFrust s3 q ≤ 6 * o` for all `q ∈ Qminus c0_09`,
    and `frustPairs (Qminus c0_09) s3 ≤ 6 * min 13 (9 * o)`, then `checkTree16 = true` produces
    an `O⁻(6,2)` word + gauge mapping `s3` on `A₂₇` to one of `rep27[0..2]`! -/
private lemma sound_checkTree16 (o : Fin 5) (t : Tree16) :
    let fV := o.val + 1
    let c := orbRep_list.getD fV 0
    ∀ (am nm : Nat) {s3 : PauliIdx 3 → ℤ},
      IsSignAssign s3 →
      (∀ i : Fin 11, s3 (dec3 (V11_pt i)) = v11SignOfMask c i.val) →
      (∀ i : Fin 16, ((am >>> i.val) &&& 1) = 1 →
        s3 (dec3 (C16_pt i)) = if ((nm >>> i.val) &&& 1) = 1 then -1 else 1) →
      (∀ i : Fin 16, ((am >>> i.val) &&& 1) = 0 → ((nm >>> i.val) &&& 1) = 0) →
      (∀ q ∈ Qminus c0_09, starFrust s3 q ≤ 6 * fV) →
      frustPairs (Qminus c0_09) s3 ≤ 6 * min 13 (9 * fV) →
      checkTree16 c fV (mkPAdj16 c) (mkNAdj16 c) am nm t = true →
      ∃ (r : Fin 3) (us : List (PauliIdx 3)) (g : PauliIdx 3),
        (∀ u ∈ us, quadForm c0_09 u = 1) ∧
        ∀ i : Fin 27, applyGauge g (applyTransvWord us s3) (dec3 (A27_pt i)) = rep27_val r i.val := by
  intro fV c
  have hM16 := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 o.val o.isLt
  have hbit_or : ∀ (m u i : Nat), (((m ||| (1 <<< u)) >>> i) &&& 1) =
      if i = u then 1 else ((m >>> i) &&& 1) := fun m u i => by
    have htest : ∀ a b, ((a >>> b) &&& 1) = if a.testBit b then 1 else 0 := fun a b => by
      rw [Nat.testBit, Nat.and_one_is_mod]; split_ifs with h <;> simp_all
    rw [htest, htest, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hiu : i = u
    · subst hiu; simp
    · have h0 : (decide (u ≤ i) && (1 : Nat).testBit (i - u)) = false := by
        by_cases hle : u ≤ i
        · have hge : 1 ≤ i - u := by omega
          have : (1 : Nat).testBit (i - u) = false := by
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
              Nat.div_eq_of_lt (show 1 < 2 ^ (i - u) from Nat.one_lt_two_pow (by omega))]
          simp [hle, this]
        · simp [hle]
      simp [hiu, h0]
  have hC16_mem : ∀ i : Fin 16, dec3 (C16_pt i) ∈ (Qminus c0_09).filter fun q => symp p0_2 q = 1 := fun i => by
    have hp := part1_tables_spec.2.2.2.2.2.2.2.2.2.1 i.val i.isLt
    simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h; apply hp.1
      have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this
      have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      rw [h0] at this; exact this
    · simp only [c0_09, quadForm_dec3, C16_pt, hp.2.2.1]; rfl
    · simp only [p0_2, symp_dec3, C16_pt, hp.2.2.2]; rfl
  have hM16_edge_eq : ∀ (s3 : PauliIdx 3 → ℤ),
      (∀ i : Fin 11, s3 (dec3 (V11_pt i)) = v11SignOfMask c i.val) →
      ∀ i j : Fin 16, M16_val c i.val j.val ≠ 0 →
        let pi := dec3 (C16_pt i); let pj := dec3 (C16_pt j)
        pi ≠ pj ∧ symp pi pj = 0 ∧ pi + pj ∈ Qminus c0_09 ∧ symp p0_2 (pi + pj) = 0 ∧
        M16_val c i.val j.val * s3 pi * s3 pj = gammaSgn pi pj * s3 pi * s3 pj * s3 (pi + pj) := by
    intro s3 hV i j hne0
    have hm := hM16 i.val i.isLt j.val j.isLt
    have hcond : i.val ≠ j.val ∧ symp3 (C16_val i.val) (C16_val j.val) = 0 := by
      have h1 := hm.2.1
      have hne_b : (M16_val c i.val j.val != 0) = true := bne_iff_ne.mpr hne0
      rw [hne_b] at h1
      have h2 := h1.symm
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h2
      exact h2
    have hmi := hC16_mem i; have hmj := hC16_mem j
    simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true] at hmi hmj
    have hpi_ne : dec3 (C16_pt i) ≠ dec3 (C16_pt j) :=
      fun h => hcond.1 (congr_arg Fin.val (C16_val_inj (congr_arg Fin.val (equiv3.symm.injective h))))
    have hsp : symp (dec3 (C16_pt i)) (dec3 (C16_pt j)) = 0 := by
      simp only [symp_dec3, C16_pt, hcond.2]; rfl
    have hadd_ne0 : dec3 (C16_pt i) + dec3 (C16_pt j) ≠ 0 := fun h => hpi_ne (by
      have := congr_arg (dec3 (C16_pt i) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hadd_Q : quadForm c0_09 (dec3 (C16_pt i) + dec3 (C16_pt j)) = 0 := by
      rw [quadForm_add, hmi.1.2, hmj.1.2, hsp]; simp
    have hadd_S : symp p0_2 (dec3 (C16_pt i) + dec3 (C16_pt j)) = 0 := by
      rw [symp_add_right, hmi.2, hmj.2]; decide
    have hadd_mem : dec3 (C16_pt i) + dec3 (C16_pt j) ∈ Qminus c0_09 := by
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨hadd_ne0, hadd_Q⟩
    refine ⟨hpi_ne, hsp, hadd_mem, hadd_S, ?_⟩
    have hxor_lt : C16_val i.val ^^^ C16_val j.val < 64 :=
      Nat.xor_lt_two_pow (n := 6) (C16_pt i).isLt (C16_pt j).isLt
    have hxor_eq : dec3 ⟨C16_val i.val ^^^ C16_val j.val, hxor_lt⟩ = dec3 (C16_pt i) + dec3 (C16_pt j) :=
      dec3_xor (C16_pt i) (C16_pt j)
    have hne0_xor : C16_val i.val ^^^ C16_val j.val ≠ 0 := fun h => hadd_ne0 (by
      rw [← hxor_eq]; rw [show (⟨C16_val i.val ^^^ C16_val j.val, hxor_lt⟩ : Fin 64) = 0 from Fin.ext h]; exact dec3_zero)
    have hQ_xor : Q3_form 9 (C16_val i.val ^^^ C16_val j.val) = 0 := by
      have h := hadd_Q; rw [← hxor_eq, c0_09, quadForm_dec3] at h
      have hlt := Q3_form_lt2 9 (C16_val i.val ^^^ C16_val j.val)
      generalize Q3_form 9 (C16_val i.val ^^^ C16_val j.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    have hS_xor : symp3 2 (C16_val i.val ^^^ C16_val j.val) = 0 := by
      have h := hadd_S; rw [← hxor_eq, p0_2, symp_dec3] at h
      have hlt := symp3_lt2 2 (C16_val i.val ^^^ C16_val j.val)
      generalize symp3 2 (C16_val i.val ^^^ C16_val j.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    obtain ⟨vp, hvp⟩ := V11_val_surj ⟨C16_val i.val ^^^ C16_val j.val, hxor_lt⟩ hne0_xor hQ_xor hS_xor
    have hdvp : dec3 (V11_pt vp) = dec3 (C16_pt i) + dec3 (C16_pt j) := by
      rw [← hxor_eq]; congr 1; exact Fin.ext hvp
    have hMval : M16_val c i.val j.val = gammaSgn (dec3 (C16_pt i)) (dec3 (C16_pt j)) * s3 (dec3 (C16_pt i) + dec3 (C16_pt j)) := by
      rw [← hdvp, hV vp, gammaSgn_dec3]
      change V11_val vp.val = C16_val i.val ^^^ C16_val j.val at hvp
      unfold M16_val; dsimp only
      rw [if_neg (by simp [hcond.1, hcond.2]), ← hvp, V11_idxOf_val vp]; rfl
    rw [hMval]; ring
  have hAdj_bit : ∀ (u v : Fin 16),
      ((((mkPAdj16 c).getD u.val 0) >>> v.val) &&& 1 = 1 ↔ M16_val c u.val v.val = 1) ∧
      ((((mkNAdj16 c).getD u.val 0) >>> v.val) &&& 1 = 1 ↔ M16_val c u.val v.val = -1) := by
    intro u v
    have hfold_bit : ∀ (P : Nat → Bool) (n : Nat) (k : Nat), k < n →
        (((List.range n).foldl (fun m j => if P j then m ||| (1 <<< j) else m) 0 >>> k) &&& 1 = 1 ↔
          P k = true) := by
      intro P n
      induction n with
      | zero => intro k hk; omega
      | succ m ih =>
        intro k hk
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        by_cases hkm : k = m
        · subst hkm
          have hlow : ∀ (L : List Nat) (acc : Nat),
              (∀ j ∈ L, j < k) → ((acc >>> k) &&& 1) = 0 →
              (((L.foldl (fun a j => if P j then a ||| (1 <<< j) else a) acc) >>> k) &&& 1) = 0 := by
            intro L; induction L with
            | nil => intro acc _ ha; exact ha
            | cons x xs ihL =>
              intro acc hlt ha
              simp only [List.foldl_cons]
              refine ihL _ (fun j hj => hlt j (List.mem_cons_of_mem x hj)) ?_
              split_ifs
              · rw [hbit_or]; have hxlt := hlt x (List.mem_cons_self ..)
                simp [Nat.ne_of_gt hxlt, ha]
              · exact ha
          have hprev0 : (((List.range k).foldl (fun m j => if P j then m ||| (1 <<< j) else m) 0 >>> k) &&& 1) = 0 :=
            hlow (List.range k) 0 (fun j hj => List.mem_range.mp hj) (by simp)
          cases hPk : P k <;> simp [hPk, hbit_or, hprev0]
        · have hklt : k < m := by omega
          split_ifs
          · rw [hbit_or, if_neg hkm]; exact ih k hklt
          · exact ih k hklt
    constructor
    · have hlt : u.val < (mkPAdj16 c).length := by simp [mkPAdj16, u.isLt]
      rw [p1_getD_eq_getElem _ _ hlt]
      simp only [mkPAdj16, List.getElem_map, List.getElem_range]
      simpa using hfold_bit (fun j => M16_val c u.val j == 1) 16 v.val v.isLt
    · have hlt : u.val < (mkNAdj16 c).length := by simp [mkNAdj16, u.isLt]
      rw [p1_getD_eq_getElem _ _ hlt]
      simp only [mkNAdj16, List.getElem_map, List.getElem_range]
      simpa using hfold_bit (fun j => M16_val c u.val j == -1) 16 v.val v.isLt
  have hfMask_eq : ∀ (am nm : Nat) (s3 : PauliIdx 3 → ℤ)
      (hA : ∀ i : Fin 16, ((am >>> i.val) &&& 1) = 1 →
        s3 (dec3 (C16_pt i)) = if ((nm >>> i.val) &&& 1) = 1 then -1 else 1)
      (u : Fin 16) (svNeg : Bool),
      let posA := am &&& (am ^^^ nm)
      let negA := am &&& nm
      let sv : ℤ := if svNeg then -1 else 1
      (if svNeg
        then pop16 ((mkPAdj16 c).getD u.val 0 &&& posA) + pop16 ((mkNAdj16 c).getD u.val 0 &&& negA)
        else pop16 ((mkPAdj16 c).getD u.val 0 &&& negA) + pop16 ((mkNAdj16 c).getD u.val 0 &&& posA)) =
      ((Finset.univ : Finset (Fin 16)).filter fun v =>
        ((am >>> v.val) &&& 1) = 1 ∧ M16_val c u.val v.val * sv * s3 (dec3 (C16_pt v)) = -1).card := by
    intro am nm s3 hA u svNeg posA negA sv
    have hbit_eq : ∀ (x k : Nat), (((x >>> k) &&& 1) = 1) ↔ x.testBit k = true := fun x k => by
      rw [Nat.testBit, Nat.and_one_is_mod]; cases h : x.testBit k <;> simp_all [Nat.testBit]
    have hbit_and : ∀ (x y k : Nat), (((x &&& y) >>> k) &&& 1 = 1) ↔
        (((x >>> k) &&& 1 = 1) ∧ ((y >>> k) &&& 1 = 1)) := fun x y k => by
      simp only [hbit_eq, Nat.testBit_and, Bool.and_eq_true]
    have hposA_bit : ∀ i : Fin 16, ((posA >>> i.val) &&& 1 = 1) ↔
        (((am >>> i.val) &&& 1 = 1) ∧ ((nm >>> i.val) &&& 1 = 0)) := fun i => by
      have hzero : ∀ (x k : Nat), (((x >>> k) &&& 1) = 0) ↔ x.testBit k = false := fun x k => by
        rw [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod]
        have hlt : (x >>> k) % 2 < 2 := Nat.mod_lt _ (by omega)
        generalize (x >>> k) % 2 = b at hlt ⊢; interval_cases b <;> decide
      simp only [posA, hbit_eq, hzero, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true]
      cases am.testBit i.val <;> cases nm.testBit i.val <;> decide
    have hnegA_bit : ∀ i : Fin 16, ((negA >>> i.val) &&& 1 = 1) ↔
        (((am >>> i.val) &&& 1 = 1) ∧ ((nm >>> i.val) &&& 1 = 1)) := fun i => hbit_and am nm i.val
    rw [pop16_eq_card, pop16_eq_card, pop16_eq_card, pop16_eq_card]
    cases svNeg with
    | true =>
      simp only [↓reduceIte, sv]
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext v
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          hbit_and, (hAdj_bit u v).1, (hAdj_bit u v).2, hposA_bit, hnegA_bit]
        have hm3 := (hM16 u.val u.isLt v.val v.isLt).2.2
        constructor
        · rintro (⟨hm1, ha, hn0⟩ | ⟨hm1, ha, hn1⟩)
          · refine ⟨ha, ?_⟩; rw [hm1, hA v ha, if_neg (by omega)]; norm_num
          · refine ⟨ha, ?_⟩; rw [hm1, hA v ha, if_pos hn1]; norm_num
        · rintro ⟨ha, hfr⟩
          have hnm2 : ((nm >>> v.val) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
          rw [hA v ha] at hfr
          rcases hm3 with hm0 | hm1 | hm1
          · rw [hm0] at hfr; norm_num at hfr
          · left; refine ⟨hm1, ha, ?_⟩
            rw [hm1] at hfr
            generalize (nm >>> v.val) &&& 1 = b at hnm2 hfr ⊢
            interval_cases b <;> first | rfl | (norm_num at hfr)
          · right; refine ⟨hm1, ha, ?_⟩
            rw [hm1] at hfr
            generalize (nm >>> v.val) &&& 1 = b at hnm2 hfr ⊢
            interval_cases b <;> first | rfl | (norm_num at hfr)
      · rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbit_and,
          (hAdj_bit u v).1, (hAdj_bit u v).2] at h1 h2
        rw [h1.1] at h2; norm_num at h2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, sv]
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext v
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          hbit_and, (hAdj_bit u v).1, (hAdj_bit u v).2, hposA_bit, hnegA_bit]
        have hm3 := (hM16 u.val u.isLt v.val v.isLt).2.2
        constructor
        · rintro (⟨hm1, ha, hn1⟩ | ⟨hm1, ha, hn0⟩)
          · refine ⟨ha, ?_⟩; rw [hm1, hA v ha, if_pos hn1]; norm_num
          · refine ⟨ha, ?_⟩; rw [hm1, hA v ha, if_neg (by omega)]; norm_num
        · rintro ⟨ha, hfr⟩
          have hnm2 : ((nm >>> v.val) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
          rw [hA v ha] at hfr
          rcases hm3 with hm0 | hm1 | hm1
          · rw [hm0] at hfr; norm_num at hfr
          · left; refine ⟨hm1, ha, ?_⟩
            rw [hm1] at hfr
            generalize (nm >>> v.val) &&& 1 = b at hnm2 hfr ⊢
            interval_cases b <;> first | rfl | (norm_num at hfr)
          · right; refine ⟨hm1, ha, ?_⟩
            rw [hm1] at hfr
            generalize (nm >>> v.val) &&& 1 = b at hnm2 hfr ⊢
            interval_cases b <;> first | rfl | (norm_num at hfr)
      · rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbit_and,
          (hAdj_bit u v).1, (hAdj_bit u v).2] at h1 h2
        rw [h1.1] at h2; norm_num at h2
  induction t with
  | S u l r ihl ihr =>
    intro am nm s3 hs3 hV hA hnm_sub hmax htot hok
    unfold checkTree16 at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    rcases hok with ⟨⟨⟨hult, hu0⟩, hl⟩, hr⟩
    let uF : Fin 16 := ⟨u, hult⟩
    have hu0_ne : dec3 (C16_pt uF) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hC16_mem uF)).1).1).1
    rcases hs3.2 _ hu0_ne with hpos | hneg
    · refine ihl (am ||| (1 <<< u)) nm hs3 hV ?_ ?_ hmax htot hl
      · intro i hi
        rw [hbit_or] at hi
        by_cases hiu : i.val = u
        · have hfi : i = uF := Fin.ext hiu
          rw [hfi, hpos]
          have hnm0 : ((nm >>> u) &&& 1) = 0 := hnm_sub uF hu0
          simp [hnm0, uF]
        · simp only [hiu, ↓reduceIte] at hi
          exact hA i hi
      · intro i hi
        rw [hbit_or] at hi
        by_cases hiu : i.val = u
        · rw [if_pos hiu] at hi; omega
        · simp only [hiu, ↓reduceIte] at hi
          exact hnm_sub i hi
    · refine ihr (am ||| (1 <<< u)) (nm ||| (1 <<< u)) hs3 hV ?_ ?_ hmax htot hr
      · intro i hi
        rw [hbit_or] at hi
        by_cases hiu : i.val = u
        · have hfi : i = uF := Fin.ext hiu
          rw [hfi, hneg, hbit_or]; simp [uF]
        · simp only [hiu, ↓reduceIte] at hi
          rw [hbit_or, if_neg hiu]; exact hA i hi
      · intro i hi
        rw [hbit_or] at hi
        by_cases hiu : i.val = u
        · rw [if_pos hiu] at hi; omega
        · simp only [hiu, ↓reduceIte] at hi
          rw [hbit_or, if_neg hiu]; exact hnm_sub i hi
  | D v =>
    intro am nm s3 hs3 hV hA _ hmax _ hok
    unfold checkTree16 at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    rcases hok with ⟨⟨hvlt, hvA⟩, hlt_fi⟩
    let vF : Fin 16 := ⟨v, hvlt⟩
    let svNeg : Bool := (((nm >>> v) &&& 1) == 1)
    have hsv : s3 (dec3 (C16_pt vF)) = if svNeg then -1 else 1 := by
      have h1 := hA vF hvA
      dsimp only [svNeg]
      by_cases h : ((nm >>> v) &&& 1) = 1
      · rw [if_pos (beq_iff_eq.mpr h)]; exact h1.trans (if_pos h)
      · rw [if_neg (by simpa using h)]; exact h1.trans (if_neg h)
    have hfi_eq := hfMask_eq am nm s3 hA vF svNeg
    dsimp only at hfi_eq
    rw [← hsv] at hfi_eq
    have hlt_fi' : fV < (if svNeg = true
        then pop16 ((mkPAdj16 c).getD v 0 &&& (am &&& (am ^^^ nm))) + pop16 ((mkNAdj16 c).getD v 0 &&& (am &&& nm))
        else pop16 ((mkPAdj16 c).getD v 0 &&& (am &&& nm)) + pop16 ((mkNAdj16 c).getD v 0 &&& (am &&& (am ^^^ nm)))) := by
      dsimp only [svNeg]; simpa [beq_iff_eq] using hlt_fi
    rw [hfi_eq] at hlt_fi'
    -- Every `j` in this filtered set yields 6 disjoint frustrated ordered pairs in `starFrust s3 (dec3 (C16_pt vF))`!
    let S := (Finset.univ : Finset (Fin 16)).filter fun j =>
      ((am >>> j.val) &&& 1) = 1 ∧ M16_val c v j.val * s3 (dec3 (C16_pt vF)) * s3 (dec3 (C16_pt j)) = -1
    let p := dec3 (C16_pt vF)
    let orb : Fin 16 → Finset (PauliIdx 3 × PauliIdx 3) := fun j =>
      let q := dec3 (C16_pt j); let r := p + q
      {(p, q), (q, p), (p, r), (r, p), (q, r), (r, q)}
    have hp_mem : p ∈ Qminus c0_09 := (Finset.mem_filter.mp (hC16_mem vF)).1
    have hp_sym : symp p0_2 p = 1 := (Finset.mem_filter.mp (hC16_mem vF)).2
    have hS_props : ∀ j ∈ S,
        let q := dec3 (C16_pt j)
        p ≠ q ∧ symp p q = 0 ∧ p + q ∈ Qminus c0_09 ∧ symp p0_2 (p + q) = 0 ∧
        gammaSgn p q * s3 p * s3 q * s3 (p + q) = -1 := fun j hj => by
      have hj2 := (Finset.mem_filter.mp hj).2.2
      have hmne : M16_val c vF.val j.val ≠ 0 := fun h => by rw [h] at hj2; norm_num at hj2
      have he := hM16_edge_eq s3 hV vF j hmne
      exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, by rw [← he.2.2.2.2]; exact hj2⟩
    have horb_card : ∀ j ∈ S, (orb j).card = 6 := fun j hj => by
      obtain ⟨hpq, _, hrQ, hrS, _⟩ := hS_props j hj
      have hqS : symp p0_2 (dec3 (C16_pt j)) = 1 := (Finset.mem_filter.mp (hC16_mem j)).2
      have hpr : p ≠ p + dec3 (C16_pt j) := fun h => by rw [h] at hp_sym; rw [hrS] at hp_sym; exact absurd hp_sym (by decide)
      have hqr : dec3 (C16_pt j) ≠ p + dec3 (C16_pt j) := fun h => by rw [h] at hqS; rw [hrS] at hqS; exact absurd hqS (by decide)
      simp only [orb]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals simp [hpq, hpr, hqr, hpq.symm, hpr.symm, hqr.symm]
    have horb_disj : (S : Set (Fin 16)).PairwiseDisjoint orb := by
      intro j1 hj1 j2 hj2 hne
      change Disjoint (orb j1) (orb j2)
      rw [Finset.disjoint_left]
      intro xy h1 h2
      have hrec : ∀ j ∈ S, ∀ ab ∈ orb j,
          (ab.1 = dec3 (C16_pt j) ∨ ab.2 = dec3 (C16_pt j) ∨ ab.1 + ab.2 = dec3 (C16_pt j)) ∧
          ∀ w, (w = ab.1 ∨ w = ab.2 ∨ w = ab.1 + ab.2) → symp p0_2 w = 1 → w ≠ p → w = dec3 (C16_pt j) := by
        intro j hj ab hab
        obtain ⟨hpq, _, _, hrS, _⟩ := hS_props j hj
        simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hab
        rcases hab with rfl | rfl | rfl | rfl | rfl | rfl
        · refine ⟨Or.inr (Or.inl rfl), fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · exact absurd rfl hwp
          · rfl
          · rw [hrS] at hs; exact absurd hs (by decide)
        · refine ⟨Or.inl rfl, fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · rfl
          · exact absurd rfl hwp
          · rw [add_comm, hrS] at hs; exact absurd hs (by decide)
        · refine ⟨Or.inr (Or.inr (pauliIdx_add_cancel_left p _)), fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · exact absurd rfl hwp
          · rw [hrS] at hs; exact absurd hs (by decide)
          · exact pauliIdx_add_cancel_left p _
        · refine ⟨Or.inr (Or.inr (by rw [add_comm, pauliIdx_add_cancel_left])), fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · rw [hrS] at hs; exact absurd hs (by decide)
          · exact absurd rfl hwp
          · rw [add_comm, pauliIdx_add_cancel_left]
        · refine ⟨Or.inl rfl, fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · rfl
          · rw [hrS] at hs; exact absurd hs (by decide)
          · exfalso; apply hwp; rw [add_comm p, pauliIdx_add_cancel_left]
        · refine ⟨Or.inr (Or.inl rfl), fun w hw hs hwp => ?_⟩
          dsimp only at hw; rcases hw with rfl | rfl | rfl
          · rw [hrS] at hs; exact absurd hs (by decide)
          · rfl
          · exfalso; apply hwp; rw [add_comm (p + _), add_comm p, pauliIdx_add_cancel_left]
      have h1r := hrec j1 hj1 xy h1
      have h2r := hrec j2 hj2 xy h2
      have hq1_eq := h2r.2 (dec3 (C16_pt j1))
        (by rcases h1r.1 with h | h | h; exact Or.inl h.symm; exact Or.inr (Or.inl h.symm); exact Or.inr (Or.inr h.symm))
        (Finset.mem_filter.mp (hC16_mem j1)).2 (hS_props j1 hj1).1.symm
      exact hne (C16_val_inj (congr_arg Fin.val (equiv3.symm.injective hq1_eq)))
    have horb_sub : S.biUnion orb ⊆
        (((Qminus c0_09).filter fun q => symp p q = 0) ×ˢ ((Qminus c0_09).filter fun q => symp p q = 0)).filter
          fun ab => ab.1 ≠ ab.2 ∧ symp ab.1 ab.2 = 0 ∧ gammaSgn ab.1 ab.2 * s3 ab.1 * s3 ab.2 * s3 (ab.1 + ab.2) = -1 := by
      intro xy hxy
      rcases Finset.mem_biUnion.mp hxy with ⟨j, hj, hab⟩
      obtain ⟨hpq, hsp, hrQ, hrS, hfr⟩ := hS_props j hj
      have hqQ : dec3 (C16_pt j) ∈ Qminus c0_09 := (Finset.mem_filter.mp (hC16_mem j)).1
      have hqS : symp p0_2 (dec3 (C16_pt j)) = 1 := (Finset.mem_filter.mp (hC16_mem j)).2
      have hpr : p ≠ p + dec3 (C16_pt j) := fun h => by rw [h] at hp_sym; rw [hrS] at hp_sym; exact absurd hp_sym (by decide)
      have hqr : dec3 (C16_pt j) ≠ p + dec3 (C16_pt j) := fun h => by rw [h] at hqS; rw [hrS] at hqS; exact absurd hqS (by decide)
      have hpm : p ∈ (Qminus c0_09).filter fun q => symp p q = 0 := Finset.mem_filter.mpr ⟨hp_mem, symp_self p⟩
      have hqm : dec3 (C16_pt j) ∈ (Qminus c0_09).filter fun q => symp p q = 0 := Finset.mem_filter.mpr ⟨hqQ, hsp⟩
      have hrm : p + dec3 (C16_pt j) ∈ (Qminus c0_09).filter fun q => symp p q = 0 :=
        Finset.mem_filter.mpr ⟨hrQ, by rw [symp_add_right, symp_self, hsp, add_zero]⟩
      have hfr_qp : gammaSgn (dec3 (C16_pt j)) p * s3 (dec3 (C16_pt j)) * s3 p * s3 (dec3 (C16_pt j) + p) = -1 := by
        rw [gammaSgn_comm (by rwa [symp_comm]), add_comm (dec3 (C16_pt j)) p]; linarith
      have hfr_pr : gammaSgn p (p + dec3 (C16_pt j)) * s3 p * s3 (p + dec3 (C16_pt j)) * s3 (p + (p + dec3 (C16_pt j))) = -1 := by
        rw [gammaSgn_add_right hsp, pauliIdx_add_cancel_left]; linarith
      have hfr_rp : gammaSgn (p + dec3 (C16_pt j)) p * s3 (p + dec3 (C16_pt j)) * s3 p * s3 (p + dec3 (C16_pt j) + p) = -1 := by
        rw [gammaSgn_comm (by rw [symp_add_left, symp_self, symp_comm, hsp, add_zero]), add_comm (p + dec3 (C16_pt j)) p]; linarith
      have hfr_qr : gammaSgn (dec3 (C16_pt j)) (p + dec3 (C16_pt j)) * s3 (dec3 (C16_pt j)) * s3 (p + dec3 (C16_pt j)) * s3 (dec3 (C16_pt j) + (p + dec3 (C16_pt j))) = -1 := by
        rw [add_comm p (dec3 (C16_pt j)), gammaSgn_add_right (by rwa [symp_comm]), pauliIdx_add_cancel_left]; linarith
      have hfr_rq : gammaSgn (p + dec3 (C16_pt j)) (dec3 (C16_pt j)) * s3 (p + dec3 (C16_pt j)) * s3 (dec3 (C16_pt j)) * s3 (p + dec3 (C16_pt j) + dec3 (C16_pt j)) = -1 := by
        rw [gammaSgn_comm (by rw [symp_add_left, hsp, symp_self, add_zero]), add_comm (p + dec3 (C16_pt j))]; linarith
      simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hab
      simp only [Finset.mem_filter, Finset.mem_product]
      rcases hab with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨Finset.mem_filter.mp hpm, Finset.mem_filter.mp hqm⟩, hpq, hsp, hfr⟩
      · exact ⟨⟨Finset.mem_filter.mp hqm, Finset.mem_filter.mp hpm⟩, hpq.symm, by rwa [symp_comm], hfr_qp⟩
      · exact ⟨⟨Finset.mem_filter.mp hpm, Finset.mem_filter.mp hrm⟩, hpr, by rw [symp_add_right, symp_self, hsp, add_zero], hfr_pr⟩
      · exact ⟨⟨Finset.mem_filter.mp hrm, Finset.mem_filter.mp hpm⟩, hpr.symm, by rw [symp_add_left, symp_self, symp_comm, hsp, add_zero], hfr_rp⟩
      · exact ⟨⟨Finset.mem_filter.mp hqm, Finset.mem_filter.mp hrm⟩, hqr, by rw [symp_add_right, symp_comm, hsp, symp_self, add_zero], hfr_qr⟩
      · exact ⟨⟨Finset.mem_filter.mp hrm, Finset.mem_filter.mp hqm⟩, hqr.symm, by rw [symp_add_left, hsp, symp_self, add_zero], hfr_rq⟩
    have hcard_le : 6 * S.card ≤ starFrust s3 p := by
      calc 6 * S.card = (S.biUnion orb).card := by
            rw [Finset.card_biUnion horb_disj, Finset.sum_congr rfl horb_card, Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ starFrust s3 p := Finset.card_le_card horb_sub
    have hmaxp := hmax p hp_mem
    have hlt_S : fV < S.card := hlt_fi'
    omega
  | L tris =>
    intro am nm s3 hs3 hV hA _ _ htot hok
    unfold checkTree16 at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨htris_ok, hgt⟩
    -- Relate `frustPairs (Qminus c0_09) s3` to ordered frustrated edges `F16` on `C₁₆`
    let F16 : Finset (Fin 16 × Fin 16) := Finset.univ.filter fun uv =>
      M16_val c uv.1.val uv.2.val * s3 (dec3 (C16_pt uv.1)) * s3 (dec3 (C16_pt uv.2)) = -1
    have hF16_eq_NBB : F16.card =
        (((Qminus c0_09).filter fun p => symp p0_2 p = 1) ×ˢ ((Qminus c0_09).filter fun p => symp p0_2 p = 1) |>.filter
          fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
            gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1).card := by
      refine Finset.card_bij (fun uv _ => (dec3 (C16_pt uv.1), dec3 (C16_pt uv.2))) ?_ ?_ ?_
      · rintro ⟨u, v⟩ huv
        have hfr := (Finset.mem_filter.mp huv).2
        have hne0 : M16_val c u.val v.val ≠ 0 := fun h => by rw [h] at hfr; norm_num at hfr
        have he := hM16_edge_eq s3 hV u v hne0
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_filter.mp (hC16_mem u), Finset.mem_filter.mp (hC16_mem v)⟩, he.1, he.2.1, by rw [← he.2.2.2.2]; exact hfr⟩
      · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (C16_val_inj (congr_arg Fin.val (equiv3.symm.injective h.1)))
          (C16_val_inj (congr_arg Fin.val (equiv3.symm.injective h.2)))
      · rintro ⟨p, q⟩ hpq
        simp only [Finset.mem_filter, Finset.mem_product, Qminus, nzPts, Finset.mem_erase,
          Finset.mem_univ, and_true] at hpq
        rcases hpq with ⟨⟨⟨⟨hp0, hpQ⟩, hpS⟩, ⟨⟨hq0, hqQ⟩, hqS⟩⟩, hne, hsp, hfr⟩
        have h0e : (enc3 0).val = 0 := by
          have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
          exact congr_arg Fin.val this
        have toQ0 : ∀ x : PauliIdx 3, quadForm c0_09 x = 0 → Q3_form 9 (enc3 x).val = 0 := fun x hx => by
          have h : quadForm c0_09 (dec3 (enc3 x)) = 0 := by rwa [dec3_enc3]
          rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 x).val
          generalize Q3_form 9 (enc3 x).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
        have toS1 : ∀ x : PauliIdx 3, symp p0_2 x = 1 → symp3 2 (enc3 x).val = 1 := fun x hx => by
          have h : symp p0_2 (dec3 (enc3 x)) = 1 := by rwa [dec3_enc3]
          rw [p0_2, symp_dec3] at h; have hlt := symp3_lt2 2 (enc3 x).val
          generalize symp3 2 (enc3 x).val = m at hlt h ⊢; interval_cases m; exact absurd h (by decide); rfl
        obtain ⟨u, hu⟩ := C16_val_surj (enc3 p) (fun h => hp0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ0 p hpQ) (toS1 p hpS)
        obtain ⟨v, hv⟩ := C16_val_surj (enc3 q) (fun h => hq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ0 q hqQ) (toS1 q hqS)
        have hdu : dec3 (C16_pt u) = p := by rw [show C16_pt u = enc3 p from Fin.ext hu, dec3_enc3]
        have hdv : dec3 (C16_pt v) = q := by rw [show C16_pt v = enc3 q from Fin.ext hv, dec3_enc3]
        have huv_ne : u.val ≠ v.val := fun h => hne (by rw [← hdu, ← hdv, Fin.ext h])
        have huv_sp : symp3 (C16_val u.val) (C16_val v.val) = 0 := by
          have h := hsp; rw [← hdu, ← hdv, symp_dec3] at h
          change ((symp3 (C16_val u.val) (C16_val v.val) : Nat) : ZMod 2) = 0 at h
          have hlt := symp3_lt2 (C16_val u.val) (C16_val v.val)
          generalize symp3 (C16_val u.val) (C16_val v.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
        have hmne : M16_val c u.val v.val ≠ 0 := by
          have h1 := (hM16 u.val u.isLt v.val v.isLt).2.1
          have h2 : (u.val != v.val && symp3 (C16_val u.val) (C16_val v.val) == 0) = true := by
            simp [huv_ne, huv_sp]
          rw [h2] at h1; exact bne_iff_ne.mp h1
        have he := hM16_edge_eq s3 hV u v hmne
        refine ⟨(u, v), ?_, Prod.ext hdu hdv⟩
        simp only [F16, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [he.2.2.2.2, hdu, hdv]; exact hfr
    have hF16_le : 6 * fV + 3 * F16.card ≤ 6 * min 13 (9 * fV) := by
      have hsplit := frustPairs_Qminus09_V11_C16_split s3
      dsimp only at hsplit
      have hst := starFrust_p0_eq_of_orb ⟨fV, by omega⟩ hV
      dsimp only at hst
      rw [hsplit, hst, ← hF16_eq_NBB] at htot
      exact htot
    -- Partition `F16` into `F_AA ⊔ F_UA ⊔ F_AU ⊔ F_UU`
    let isA : Fin 16 → Prop := fun u => ((am >>> u.val) &&& 1) = 1
    let F_AA := F16.filter fun uv => isA uv.1 ∧ isA uv.2
    let F_UA := F16.filter fun uv => ¬isA uv.1 ∧ isA uv.2
    let F_AU := F16.filter fun uv => isA uv.1 ∧ ¬isA uv.2
    let F_UU := F16.filter fun uv => ¬isA uv.1 ∧ ¬isA uv.2
    have hF16_part : F16.card = F_AA.card + F_UA.card + F_AU.card + F_UU.card := by
      have hu : F16 = (F_AA ∪ F_UA) ∪ (F_AU ∪ F_UU) := by
        ext uv; simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter]
        by_cases h1 : isA uv.1 <;> by_cases h2 : isA uv.2 <;> tauto
      have hd1 : Disjoint F_AA F_UA := Finset.disjoint_left.mpr fun _ h1 h2 =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      have hd2 : Disjoint F_AU F_UU := Finset.disjoint_left.mpr fun _ h1 h2 =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      have hd3 : Disjoint (F_AA ∪ F_UA) (F_AU ∪ F_UU) := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter] at h1 h2
        rcases h1 with ⟨_, _, ha⟩ | ⟨_, _, ha⟩ <;> rcases h2 with ⟨_, _, hna⟩ | ⟨_, _, hna⟩ <;> exact hna ha
      rw [hu, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
      omega
    have hFAU_eq : F_AU.card = F_UA.card := by
      refine Finset.card_bij (fun uv _ => (uv.2, uv.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
      · rintro ⟨u, v⟩ huv
        simp only [F_AU, F_UA, F16, Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
        refine ⟨?_, huv.2.2, huv.2.1⟩
        rw [(hM16 v.val v.isLt u.val u.isLt).1]; linarith [huv.1]
      · rintro ⟨u, v⟩ huv
        refine ⟨(v, u), ?_, rfl⟩
        simp only [F_AU, F_UA, F16, Finset.mem_filter, Finset.mem_univ, true_and] at huv ⊢
        refine ⟨?_, huv.2.2, huv.2.1⟩
        rw [(hM16 v.val v.isLt u.val u.isLt).1]; linarith [huv.1]
    -- Bound 1: `fc2 = F_AA.card`
    have hfc2_eq :
        (List.range 16).foldl (fun acc u =>
          if ((am >>> u) &&& 1) == 1 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            let f := if ((nm >>> u) &&& 1) == 1
                     then pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm))
                     else pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm)))
            acc + f
          else acc) 0 = F_AA.card := by
      have hrw : (fun acc u =>
          if ((am >>> u) &&& 1) == 1 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            let f := if ((nm >>> u) &&& 1) == 1
                     then pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm))
                     else pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm)))
            acc + f
          else acc) = (fun acc u => acc +
          if ((am >>> u) &&& 1) == 1 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            if ((nm >>> u) &&& 1) == 1
            then pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm))
            else pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm)))
          else 0) := by funext acc u; dsimp only; split_ifs <;> omega
      rw [hrw, p1_foldl_sum_range]
      have hFAA : F_AA.card = ∑ u : Fin 16,
          if isA u then ((Finset.univ : Finset (Fin 16)).filter fun v =>
            isA v ∧ M16_val c u.val v.val * s3 (dec3 (C16_pt u)) * s3 (dec3 (C16_pt v)) = -1).card
          else 0 := by
        dsimp only [F_AA, F16]
        rw [Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : isA u
        · rw [if_pos hu, Finset.card_filter]
          refine Finset.sum_congr rfl fun v _ => by by_cases hv : isA v <;> simp [hu, hv, and_comm]
        · rw [if_neg hu]
          exact Finset.sum_eq_zero fun v _ => by simp [hu]
      rw [hFAA]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : isA u
      · have hub : (((am >>> u.val) &&& 1) == 1) = true := beq_iff_eq.mpr hu
        simp only [hub, ↓reduceIte, hu]
        have hsu : s3 (dec3 (C16_pt u)) = if (((nm >>> u.val) &&& 1) == 1) then -1 else 1 := by
          have h1 := hA u hu
          by_cases hn : ((nm >>> u.val) &&& 1) = 1
          · rw [if_pos (beq_iff_eq.mpr hn)]; exact h1.trans (if_pos hn)
          · rw [if_neg (by simpa using hn)]; exact h1.trans (if_neg hn)
        have hfm := hfMask_eq am nm s3 hA u (((nm >>> u.val) &&& 1) == 1)
        dsimp only at hfm; rw [← hsu] at hfm; exact hfm
      · have hub : (((am >>> u.val) &&& 1) == 1) = false := beq_false_of_ne hu
        rw [if_neg (by rw [hub]; decide), if_neg hu]
    -- Bound 2: `starLB ≤ F_UA.card`
    have hstar_le :
        (List.range 16).foldl (fun acc u =>
          if ((am >>> u) &&& 1) == 0 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            let cP := pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm)))
            let cN := pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm))
            acc + min cP cN
          else acc) 0 ≤ F_UA.card := by
      have hrw : (fun acc u =>
          if ((am >>> u) &&& 1) == 0 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            let cP := pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm)))
            let cN := pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm))
            acc + min cP cN
          else acc) = (fun acc u => acc +
          if ((am >>> u) &&& 1) == 0 then
            let pm := (mkPAdj16 c).getD u 0
            let nmask := (mkNAdj16 c).getD u 0
            min (pop16 (pm &&& (am &&& nm)) + pop16 (nmask &&& (am &&& (am ^^^ nm))))
                (pop16 (pm &&& (am &&& (am ^^^ nm))) + pop16 (nmask &&& (am &&& nm)))
          else 0) := by funext acc u; dsimp only; split_ifs <;> omega
      rw [hrw, p1_foldl_sum_range]
      have hFUA : F_UA.card = ∑ u : Fin 16,
          if ¬isA u then ((Finset.univ : Finset (Fin 16)).filter fun v =>
            isA v ∧ M16_val c u.val v.val * s3 (dec3 (C16_pt u)) * s3 (dec3 (C16_pt v)) = -1).card
          else 0 := by
        dsimp only [F_UA, F16]
        rw [Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : isA u
        · rw [if_neg (not_not.mpr hu)]
          exact Finset.sum_eq_zero fun v _ => by simp [hu]
        · rw [if_pos hu, Finset.card_filter]
          refine Finset.sum_congr rfl fun v _ => by by_cases hv : isA v <;> simp [hu, hv, and_comm]
      rw [hFUA]
      refine Finset.sum_le_sum fun u _ => ?_
      have ham2 : ((am >>> u.val) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
      by_cases hu : isA u
      · have hub : (((am >>> u.val) &&& 1) == 0) = false := beq_false_of_ne (by dsimp [isA] at hu; omega)
        rw [if_neg (by rw [hub]; decide), if_neg (not_not.mpr hu)]
      · have hu0 : ((am >>> u.val) &&& 1) = 0 := by dsimp [isA] at hu; omega
        have hub : (((am >>> u.val) &&& 1) == 0) = true := beq_iff_eq.mpr hu0
        simp only [hub, ↓reduceIte, hu, not_false_eq_true]
        have hu_nz : dec3 (C16_pt u) ≠ 0 :=
          (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hC16_mem u)).1).1).1
        rcases hs3.2 _ hu_nz with hpos | hneg
        · have hfm := hfMask_eq am nm s3 hA u false
          simp only [Bool.false_eq_true, ↓reduceIte] at hfm
          rw [hpos, ← hfm]; exact Nat.min_le_left _ _
        · have hfm := hfMask_eq am nm s3 hA u true
          simp only [↓reduceIte] at hfm
          rw [hneg, ← hfm]; exact Nat.min_le_right _ _
    -- Bound 3: `2 * tris.length ≤ F_UU.card`
    have htris_le : ∀ (ts : List (Nat × Nat × Nat)) (used : List (Nat × Nat)),
        checkTris16 c am ts used = true →
        2 * ts.length ≤ (F_UU.filter fun uv =>
          ¬used.contains (min uv.1.val uv.2.val, max uv.1.val uv.2.val)).card := by
      intro ts
      induction ts with
      | nil => intro used _; simp
      | cons tr rest ih =>
        intro used hok
        rcases tr with ⟨a, b, d⟩
        unfold checkTris16 at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hok
        rcases hok with ⟨⟨⟨hokV, hprod⟩, hokU⟩, hrest⟩
        rcases hokV with ⟨⟨⟨⟨⟨⟨⟨ha16, hb16⟩, hd16⟩, hab⟩, hbd⟩, ha0⟩, hb0⟩, hd0⟩
        rcases hokU with ⟨⟨hu1, hu2⟩, hu3⟩
        let fa : Fin 16 := ⟨a, ha16⟩; let fb : Fin 16 := ⟨b, hb16⟩; let fd : Fin 16 := ⟨d, hd16⟩
        have hsq : ∀ x : Fin 16, s3 (dec3 (C16_pt x)) * s3 (dec3 (C16_pt x)) = 1 := fun x => by
          have h0 : dec3 (C16_pt x) ≠ 0 :=
            (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hC16_mem x)).1).1).1
          rcases hs3.2 _ h0 with h | h <;> rw [h] <;> norm_num
        have he_pm1 : ∀ x y : Fin 16, M16_val c x.val y.val ≠ 0 →
            M16_val c x.val y.val * s3 (dec3 (C16_pt x)) * s3 (dec3 (C16_pt y)) = 1 ∨
            M16_val c x.val y.val * s3 (dec3 (C16_pt x)) * s3 (dec3 (C16_pt y)) = -1 := fun x y hne => by
          have h0x : dec3 (C16_pt x) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hC16_mem x)).1).1).1
          have h0y : dec3 (C16_pt y) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hC16_mem y)).1).1).1
          have hm3 := (hM16 x.val x.isLt y.val y.isLt).2.2
          rcases hm3 with h0 | hm | hm
          · exact absurd h0 hne
          · rcases hs3.2 _ h0x with hx | hx <;> rcases hs3.2 _ h0y with hy | hy <;> (rw [hm, hx, hy]; decide)
          · rcases hs3.2 _ h0x with hx | hx <;> rcases hs3.2 _ h0y with hy | hy <;> (rw [hm, hx, hy]; decide)
        have hne_ab : M16_val c a b ≠ 0 := fun h => by rw [h] at hprod; norm_num at hprod
        have hne_bd : M16_val c b d ≠ 0 := fun h => by rw [h] at hprod; norm_num at hprod
        have hne_ad : M16_val c a d ≠ 0 := fun h => by rw [h] at hprod; norm_num at hprod
        have hex : ∃ x y : Fin 16, x.val < y.val ∧ ((x.val, y.val) = (a, b) ∨ (x.val, y.val) = (b, d) ∨ (x.val, y.val) = (a, d)) ∧
            (x, y) ∈ F_UU ∧ (y, x) ∈ F_UU := by
          have hpp : (M16_val c a b * s3 (dec3 (C16_pt fa)) * s3 (dec3 (C16_pt fb))) *
              (M16_val c b d * s3 (dec3 (C16_pt fb)) * s3 (dec3 (C16_pt fd))) *
              (M16_val c a d * s3 (dec3 (C16_pt fa)) * s3 (dec3 (C16_pt fd))) = -1 := by
            calc _ = (M16_val c a b * M16_val c b d * M16_val c a d) *
                  (s3 (dec3 (C16_pt fa)) * s3 (dec3 (C16_pt fa))) *
                  (s3 (dec3 (C16_pt fb)) * s3 (dec3 (C16_pt fb))) *
                  (s3 (dec3 (C16_pt fd)) * s3 (dec3 (C16_pt fd))) := by ring
              _ = -1 * 1 * 1 * 1 := by rw [hprod, hsq fa, hsq fb, hsq fd]
              _ = -1 := by norm_num
          have hna : ¬isA fa := by dsimp [isA, fa]; omega
          have hnb : ¬isA fb := by dsimp [isA, fb]; omega
          have hnd : ¬isA fd := by dsimp [isA, fd]; omega
          rcases he_pm1 fa fb hne_ab with h1 | h1
          · rcases he_pm1 fb fd hne_bd with h2 | h2
            · rcases he_pm1 fa fd hne_ad with h3 | h3
              · rw [h1, h2, h3] at hpp; norm_num at hpp
              · refine ⟨fa, fd, by dsimp [fa, fd]; omega, Or.inr (Or.inr rfl), ?_, ?_⟩
                · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h3, hna, hnd⟩
                · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨by rw [(hM16 d hd16 a ha16).1]; linarith [h3], hnd, hna⟩
            · refine ⟨fb, fd, by dsimp [fb, fd]; omega, Or.inr (Or.inl rfl), ?_, ?_⟩
              · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h2, hnb, hnd⟩
              · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨by rw [(hM16 d hd16 b hb16).1]; linarith [h2], hnd, hnb⟩
          · refine ⟨fa, fb, by dsimp [fa, fb]; omega, Or.inl rfl, ?_, ?_⟩
            · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, hna, hnb⟩
            · simp only [F_UU, F16, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨by rw [(hM16 b hb16 a ha16).1]; linarith [h1], hnb, hna⟩
        obtain ⟨x, y, hxy, htri_e, hxyU, hyxU⟩ := hex
        have hih := ih ((a, b) :: (b, d) :: (a, d) :: used) hrest
        let Aset := F_UU.filter fun uv => ¬used.contains (min uv.1.val uv.2.val, max uv.1.val uv.2.val)
        let Bset := F_UU.filter fun uv =>
          ¬((a, b) :: (b, d) :: (a, d) :: used).contains (min uv.1.val uv.2.val, max uv.1.val uv.2.val)
        have hxy_ne : (x, y) ≠ (y, x) := fun h => by have := congr_arg (fun p => p.1.val) h; dsimp at this; omega
        have hnotU : used.contains (x.val, y.val) = false := by
          rcases htri_e with h | h | h <;> rw [h] <;> assumption
        have hxy_A : (x, y) ∈ Aset := by
          simp only [Aset, Finset.mem_filter, hxyU, true_and, Nat.min_eq_left (le_of_lt hxy),
            Nat.max_eq_right (le_of_lt hxy), hnotU, Bool.false_eq_true, not_false_eq_true]
        have hyx_A : (y, x) ∈ Aset := by
          simp only [Aset, Finset.mem_filter, hyxU, true_and, Nat.min_eq_right (le_of_lt hxy),
            Nat.max_eq_left (le_of_lt hxy), hnotU, Bool.false_eq_true, not_false_eq_true]
        have hxy_nB : (x, y) ∉ Bset := by
          simp only [Bset, Finset.mem_filter, Nat.min_eq_left (le_of_lt hxy), Nat.max_eq_right (le_of_lt hxy),
            List.contains_cons, Bool.or_eq_true, beq_iff_eq, not_and, not_not]
          intro _; rcases htri_e with h | h | h
          · left; exact h
          · right; left; exact h
          · right; right; left; exact h
        have hyx_nB : (y, x) ∉ Bset := by
          simp only [Bset, Finset.mem_filter, Nat.min_eq_right (le_of_lt hxy), Nat.max_eq_left (le_of_lt hxy),
            List.contains_cons, Bool.or_eq_true, beq_iff_eq, not_and, not_not]
          intro _; rcases htri_e with h | h | h
          · left; exact h
          · right; left; exact h
          · right; right; left; exact h
        have hsub : insert (x, y) (insert (y, x) Bset) ⊆ Aset := by
          intro uv huv
          simp only [Finset.mem_insert] at huv
          rcases huv with rfl | rfl | hB
          · exact hxy_A
          · exact hyx_A
          · simp only [Aset, Bset, Finset.mem_filter, List.contains_cons, Bool.or_eq_true] at hB ⊢
            exact ⟨hB.1, fun hu => hB.2 (Or.inr (Or.inr (Or.inr hu)))⟩
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxy_nB]),
            Finset.card_insert_of_notMem hyx_nB] at hcard
        dsimp only [Aset, Bset] at hcard
        simp only [List.length_cons]
        omega
    have htri0 := htris_le tris [] htris_ok
    have hFUU_eq : (F_UU.filter fun uv => ¬([] : List (Nat × Nat)).contains (min uv.1.val uv.2.val, max uv.1.val uv.2.val)).card = F_UU.card := by
      congr 1; ext uv; simp
    rw [hFUU_eq] at htri0
    dsimp only at hstar_le
    rw [hfc2_eq] at hgt
    omega
  | O ridx gSol us =>
    intro am nm s3 _ hV hA _ _ _ hok
    unfold checkTree16 at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    rcases hok with ⟨⟨⟨⟨ham, hridx⟩, hgSol⟩, hus⟩, hmatch⟩
    let S : Nat → Bool := fun v => v != 0 && Q3_form 9 v == 0
    have hinv : ∀ u ∈ us, u < 64 ∧ ∀ v < 64, S v = true → S (transv3_pt u v) = true := by
      intro u hu
      rw [List.all_eq_true] at hus
      have hu' := hus u hu
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu'
      refine ⟨hu'.1, fun v hv hSv => ?_⟩
      simp only [S, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hSv ⊢
      let uF : Fin 64 := ⟨u, hu'.1⟩; let vF : Fin 64 := ⟨v, hv⟩
      have huQ : quadForm c0_09 (dec3 uF) = 1 := by simp only [c0_09, quadForm_dec3, uF, hu'.2]; rfl
      have hvQ : quadForm c0_09 (dec3 vF) = 0 := by simp only [c0_09, quadForm_dec3, vF, hSv.2]; rfl
      have htv_eq : dec3 ⟨transv3_pt u v, transv3_pt_lt uF vF⟩ = transvPt (dec3 uF) (dec3 vF) :=
        (transvPt_dec3 uF vF).symm
      have hv_nz : dec3 vF ≠ 0 := by
        intro h; apply hSv.1
        have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this
        have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        rw [h0] at this; exact this
      have htv_nz : transv3_pt u v ≠ 0 := fun h => hv_nz (by
        have h1 : transvPt (dec3 uF) (dec3 vF) = 0 := by
          rw [← htv_eq, show (⟨transv3_pt u v, transv3_pt_lt uF vF⟩ : Fin 64) = 0 from Fin.ext h]; exact dec3_zero
        rw [← transvPt_invol (dec3 uF) (dec3 vF), h1, transvPt_zero])
      have htvQ : quadForm c0_09 (dec3 ⟨transv3_pt u v, transv3_pt_lt uF vF⟩) = 0 := by
        rw [htv_eq, quadForm_transvPt_fix huQ, hvQ]
      have htvQ3 : Q3_form 9 (transv3_pt u v) = 0 := by
        rw [c0_09, quadForm_dec3] at htvQ
        have hlt := Q3_form_lt2 9 (transv3_pt u v)
        generalize Q3_form 9 (transv3_pt u v) = m at hlt htvQ ⊢; interval_cases m; rfl; exact absurd htvQ (by decide)
      exact ⟨htv_nz, htvQ3⟩
    let sInit : Nat → ℤ := fun v =>
      match V11_list.idxOf? v with
      | some idxV => v11SignOfMask c idxV
      | none =>
        match C16_list.idxOf? v with
        | some idxC => if ((nm >>> idxC) &&& 1) = 1 then -1 else 1
        | none => 0
    have h65535 : ∀ k < 16, ((65535 >>> k) &&& 1) = 1 := by decide
    have hagree : ∀ v : Fin 64, S v.val = true → sInit v.val = s3 (dec3 v) := by
      intro v hSv
      simp only [S, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hSv
      have hs2 := symp3_lt2 2 v.val
      rcases (show symp3 2 v.val = 0 ∨ symp3 2 v.val = 1 by omega) with hs0 | hs1
      · obtain ⟨iv, hiv⟩ := V11_val_surj v hSv.1 hSv.2 hs0
        have hveq : v = V11_pt iv := Fin.ext hiv.symm
        rw [hveq]; dsimp only [sInit, V11_pt]
        rw [V11_idxOf_val iv]; dsimp only; exact (hV iv).symm
      · obtain ⟨ic, hic⟩ := C16_val_surj v hSv.1 hSv.2 hs1
        have hveq : v = C16_pt ic := Fin.ext hic.symm
        rw [hveq]
        have hlhs : sInit (C16_pt ic).val = if ((nm >>> ic.val) &&& 1) = 1 then -1 else 1 := by
          dsimp only [sInit, C16_pt]; rw [V11_idxOf_none_of_C16 ic, C16_idxOf_val ic]
        rw [hlhs, hA ic (by rw [ham]; exact h65535 ic.val ic.isLt)]
    refine ⟨⟨ridx, hridx⟩, word3FromNat us, dec3 ⟨gSol, hgSol⟩, ?_, ?_⟩
    · intro u hu
      rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
      rw [List.all_eq_true] at hus
      have hu' := hus un hun
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu'
      simp only [c0_09, quadForm_dec3, Nat.mod_eq_of_lt hu'.1, hu'.2]; rfl
    · intro i
      have hAi := part1_tables_spec.2.1 i.val i.isLt
      have hSA : S (A27_pt i).val = true := by simp [S, A27_pt, hAi.1, hAi.2.2]
      have hw := applyWord3Nat_eq_on_inv S us hinv sInit s3 hagree (A27_pt i) hSA
      have hg := applyGauge3Nat_eq ⟨gSol, hgSol⟩ (applyWord3Nat us sInit) (applyTransvWord (word3FromNat us) s3) (A27_pt i) hw
      have hm := p1_all_range hmatch i.isLt
      simp only [beq_iff_eq] at hm
      change applyGauge3Nat gSol (applyWord3Nat us sInit) (A27_val i.val) = rep27_val ⟨ridx, hridx⟩ i.val at hm
      rw [← hg]; exact hm

set_option maxHeartbeats 800000 in
/-- **Master Part 1 Theorem (`Q⁻(5,2)` Classification)**:
    Every 3-qubit sign assignment `s3` with `frustPairs (Qminus c0_09) s3 ≤ 13 * 6` maps
    via an `O⁻(6,2)` transvection word (preserving `Qminus c0_09`) and a 3-qubit gauge
    to one of the 3 canonical orbit representatives `rep27[0..2]` on `A₂₇`. -/
theorem qminus52_le13_classified {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (hle : frustPairs (Qminus c0_09) s3 ≤ 13 * 6) :
    ∃ (r : Fin 3) (us : List (PauliIdx 3)) (g : PauliIdx 3),
      (∀ u ∈ us, quadForm c0_09 u = 1) ∧
      ∀ i : Fin 27, applyGauge g (applyTransvWord us s3) (dec3 (A27_pt i)) = rep27_val r i.val := by
  -- 1. Pick `pMax ∈ Qminus c0_09` maximizing `starFrust s3 p` (positive by 6-line MP grid)
  have hneQ : (Qminus c0_09).Nonempty := ⟨dec3 (A27_pt ⟨0, by decide⟩), A27_pt_mem_Qminus ⟨0, by decide⟩⟩
  obtain ⟨pMax, hpMax_mem, hpMax_ge⟩ := Finset.exists_max_image (Qminus c0_09) (starFrust s3) hneQ
  have hpMax_pos : 0 < starFrust s3 pMax := by
    obtain ⟨q, hq, hqpos⟩ := exists_starFrust_pos hs3
    exact lt_of_lt_of_le hqpos (hpMax_ge q hq)
  -- 2. Map `pMax → p0_2` via `a27ToP0_words`
  have h0e : (enc3 0).val = 0 := by
    have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
    exact congr_arg Fin.val this
  have hpMax_Q : Q3_form 9 (enc3 pMax).val = 0 := by
    have h := (Finset.mem_filter.mp hpMax_mem).2
    rw [← dec3_enc3 pMax, c0_09, quadForm_dec3] at h
    have hlt := Q3_form_lt2 9 (enc3 pMax).val
    generalize Q3_form 9 (enc3 pMax).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
  have hpMax_0 : (enc3 pMax).val ≠ 0 := fun h =>
    (Finset.mem_erase.mp (Finset.mem_filter.mp hpMax_mem).1).1 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
  obtain ⟨ip, hip⟩ := A27_val_surj (enc3 pMax) hpMax_0 hpMax_Q
  have hdip : dec3 (A27_pt ip) = pMax := by rw [show A27_pt ip = enc3 pMax from Fin.ext hip, dec3_enc3]
  let us1Nat := a27ToP0_words.getD ip.val []
  let us1 := word3FromNat us1Nat
  have hus1_spec := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.1 ip.val ip.isLt
  have hus1_Q : ∀ u ∈ us1, quadForm c0_09 u = 1 := by
    intro u hu; rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
    have h := hus1_spec.1 un hun
    simp only [c0_09, quadForm_dec3, Nat.mod_eq_of_lt h.1, h.2]; rfl
  have hfold_lt : ∀ (ws : List Nat) (v : Fin 64), (∀ w ∈ ws, w < 64) →
      ws.foldl (fun cur w => transv3_pt w cur) v.val < 64 := by
    intro ws; induction ws with
    | nil => intro v _; exact v.isLt
    | cons w ws ih =>
      intro v hws; simp only [List.foldl_cons]
      exact ih ⟨transv3_pt w v.val, transv3_pt_lt ⟨w, hws w (List.mem_cons_self ..)⟩ v⟩
        (fun x hx => hws x (List.mem_cons_of_mem w hx))
  have hfold_us1 : ∀ (ws : List Nat) (v : Fin 64) (hws : ∀ w ∈ ws, w < 64),
      (word3FromNat ws).foldl (fun cur u => transvPt u cur) (dec3 v) =
      dec3 ⟨ws.foldl (fun cur w => transv3_pt w cur) v.val, hfold_lt ws v hws⟩ := by
    intro ws
    induction ws with
    | nil => intro v _; rfl
    | cons w ws ih =>
      intro v hws
      have hw : w < 64 := hws w (List.mem_cons_self ..)
      simp only [word3FromNat, List.map_cons, List.foldl_cons]
      have hstep : transvPt (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 v) =
          dec3 ⟨transv3_pt w v.val, transv3_pt_lt ⟨w, hw⟩ v⟩ := by
        rw [show (⟨w % 64, Nat.mod_lt _ (by omega)⟩ : Fin 64) = ⟨w, hw⟩ from Fin.ext (Nat.mod_eq_of_lt hw),
            transvPt_dec3]
      calc (word3FromNat ws).foldl (fun cur u => transvPt u cur)
              (transvPt (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 v))
          = (word3FromNat ws).foldl (fun cur u => transvPt u cur)
              (dec3 ⟨transv3_pt w v.val, transv3_pt_lt ⟨w, hw⟩ v⟩) :=
            congr_arg ((word3FromNat ws).foldl (fun cur u => transvPt u cur)) hstep
        _ = _ := ih ⟨transv3_pt w v.val, transv3_pt_lt ⟨w, hw⟩ v⟩ (fun x hx => hws x (List.mem_cons_of_mem w hx))
  have hpMax_to_p0 : us1.foldl (fun cur u => transvPt u cur) pMax = p0_2 := by
    rw [← hdip, hfold_us1 us1Nat (A27_pt ip) (fun w hw => (hus1_spec.1 w hw).1)]
    congr 1; apply Fin.ext; exact hus1_spec.2
  let s1 := applyTransvWord us1 s3
  have hs1 : IsSignAssign s1 := applyTransvWord_isSignAssign us1 hs3
  have hs1_p0 : starFrust s1 p0_2 = starFrust s3 pMax := by
    rw [starFrust_applyTransvWord hus1_Q, (foldl_transvPt_iff_foldr us1 pMax p0_2).mp hpMax_to_p0]
  have hs1_max : ∀ q ∈ Qminus c0_09, starFrust s1 q ≤ starFrust s1 p0_2 := by
    intro q hq
    rw [starFrust_applyTransvWord hus1_Q, hs1_p0]
    have hq' : us1.foldr (fun u cur => transvPt u cur) q ∈ Qminus c0_09 := by
      have hgen : ∀ (ws : List (PauliIdx 3)), (∀ u ∈ ws, quadForm c0_09 u = 1) →
          ∀ x ∈ Qminus c0_09, ws.foldr (fun u cur => transvPt u cur) x ∈ Qminus c0_09 := by
        intro ws; induction ws with
        | nil => intro _ x hx; exact hx
        | cons u ws ih =>
          intro hws x hx
          have hx' := ih (fun w hw => hws w (List.mem_cons_of_mem u hw)) x hx
          simp only [List.foldr_cons, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hx' ⊢
          exact ⟨fun h0 => hx'.1 (by rw [← transvPt_invol u (ws.foldr (fun u cur => transvPt u cur) x), h0, transvPt_zero]),
            by rw [quadForm_transvPt_fix (hws u (List.mem_cons_self ..)), hx'.2]⟩
      exact hgen us1 hus1_Q q hq
    exact hpMax_ge _ hq'
  have hs1_tot : frustPairs (Qminus c0_09) s1 ≤ 13 * 6 := by
    rwa [applyTransvWord_preserves_Qminus09 hus1_Q]
  -- 3. Gauge-normalize the 5 pivots of `V₁₁` to `+1`
  have hV_nz : ∀ i : Fin 11, dec3 (V11_pt i) ≠ 0 := fun i h =>
    (part1_tables_spec.2.2.2.2.2.2.2.1 i.val i.isLt).1 (by
      have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this; rw [h0e] at this; exact this)
  let b5 : Nat → Nat := fun k =>
    if s1 (dec3 (V11_pt ⟨piv5_list.getD k 0 % 11, Nat.mod_lt _ (by omega)⟩)) = -1 then 1 else 0
  let m5 : Nat := b5 0 + 2 * b5 1 + 4 * b5 2 + 8 * b5 3 + 16 * b5 4
  have hm5_lt : m5 < 32 := by
    have : ∀ k, b5 k ≤ 1 := fun k => by dsimp [b5]; split_ifs <;> omega
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3; have h4 := this 4
    dsimp [m5]; omega
  have hm5_bit : ∀ k < 5, ((m5 >>> k) &&& 1) = b5 k := by
    have hb : ∀ j, b5 j = 0 ∨ b5 j = 1 := fun j => by dsimp [b5]; split_ifs <;> simp
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
    intro k hk; rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [m5]
    interval_cases k <;> omega
  have hg1_spec := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1 m5 hm5_lt
  let g1F : Fin 64 := ⟨pivGauges_list.getD m5 0, hg1_spec.1⟩
  let g1 : PauliIdx 3 := dec3 g1F
  let s2 := applyGauge g1 s1
  have hs2 : IsSignAssign s2 := applyGauge_isSignAssign g1 hs1
  have hs2_piv : ∀ k < 5, s2 (dec3 (V11_pt ⟨piv5_list.getD k 0 % 11, Nat.mod_lt _ (by omega)⟩)) = 1 := by
    intro k hk
    let pv : Fin 11 := ⟨piv5_list.getD k 0 % 11, Nat.mod_lt _ (by omega)⟩
    have hpv_eq : piv5_list.getD k 0 % 11 = piv5_list.getD k 0 := by interval_cases k <;> decide
    have hsp := hg1_spec.2 k hk
    rw [← hpv_eq] at hsp
    have hbit := hm5_bit k hk
    rw [hbit] at hsp
    dsimp only [s2, applyGauge, sympSign, g1]
    rw [symp_dec3]
    change (if ((symp3 g1F.val (V11_val pv.val) : ZMod 2) = 0) then (1 : ℤ) else -1) * s1 (dec3 (V11_pt pv)) = 1
    rw [hsp]
    rcases hs1.2 _ (hV_nz pv) with hpos | hneg
    · have hb0 : b5 k = 0 := by dsimp only [b5]; rw [if_neg (by rw [hpos]; decide)]
      rw [hb0, hpos]; norm_num
    · have hb1 : b5 k = 1 := by dsimp only [b5]; rw [if_pos hneg]
      rw [hb1, hneg]; decide
  -- 4. Read 6-bit mask `c6 < 64` of `s2` on `free6_list` and map to canonical `V₁₁` orbit via `v11Map_data`
  let f6idx : Nat → Fin 11 := fun k => ⟨free6_list.getD k 0 % 11, Nat.mod_lt _ (by omega)⟩
  let b6 : Nat → Nat := fun k => if s2 (dec3 (V11_pt (f6idx k))) = -1 then 1 else 0
  let c6 : Nat := b6 0 + 2 * b6 1 + 4 * b6 2 + 8 * b6 3 + 16 * b6 4 + 32 * b6 5
  have hc6_lt : c6 < 64 := by
    have : ∀ k, b6 k ≤ 1 := fun k => by dsimp [b6]; split_ifs <;> omega
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3; have h4 := this 4; have h5 := this 5
    dsimp [c6]; omega
  have hc6_bit : ∀ k < 6, ((c6 >>> k) &&& 1) = b6 k := by
    have hb : ∀ j, b6 j = 0 ∨ b6 j = 1 := fun j => by dsimp [b6]; split_ifs <;> simp
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
    intro k hk; rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [c6]
    interval_cases k <;> omega
  have hs2_V11 : ∀ i : Fin 11, s2 (dec3 (V11_pt i)) = v11SignOfMask c6 i.val := by
    have hfree : ∀ k < 6, s2 (dec3 (V11_pt (f6idx k))) =
        if ((c6 >>> k) &&& 1) == 1 then -1 else 1 := fun k hk => by
      rw [hc6_bit k hk]
      dsimp only [b6]
      have hval := hs2.2 _ (hV_nz (f6idx k))
      have haux : ∀ val : ℤ, (val = 1 ∨ val = -1) →
          val = if ((if val = -1 then (1 : Nat) else 0) == 1) then (-1 : ℤ) else 1 := by
        rintro _ (rfl | rfl) <;> rfl
      exact haux _ hval
    have hf0 : f6idx 0 = ⟨2, by decide⟩ := rfl
    have hf1 : f6idx 1 = ⟨4, by decide⟩ := rfl
    have hf2 : f6idx 2 = ⟨6, by decide⟩ := rfl
    have hf3 : f6idx 3 = ⟨8, by decide⟩ := rfl
    have hf4 : f6idx 4 = ⟨9, by decide⟩ := rfl
    have hf5 : f6idx 5 = ⟨10, by decide⟩ := rfl
    have hp0 : (⟨piv5_list.getD 0 0 % 11, Nat.mod_lt _ (by omega)⟩ : Fin 11) = ⟨0, by decide⟩ := rfl
    have hp1 : (⟨piv5_list.getD 1 0 % 11, Nat.mod_lt _ (by omega)⟩ : Fin 11) = ⟨1, by decide⟩ := rfl
    have hp2 : (⟨piv5_list.getD 2 0 % 11, Nat.mod_lt _ (by omega)⟩ : Fin 11) = ⟨3, by decide⟩ := rfl
    have hp3 : (⟨piv5_list.getD 3 0 % 11, Nat.mod_lt _ (by omega)⟩ : Fin 11) = ⟨5, by decide⟩ := rfl
    have hp4 : (⟨piv5_list.getD 4 0 % 11, Nat.mod_lt _ (by omega)⟩ : Fin 11) = ⟨7, by decide⟩ := rfl
    intro i
    fin_cases i
    · have h := hs2_piv 0 (by decide); rw [hp0] at h; exact h
    · have h := hs2_piv 1 (by decide); rw [hp1] at h; exact h
    · have h := hfree 0 (by decide); rw [hf0] at h; exact h
    · have h := hs2_piv 2 (by decide); rw [hp2] at h; exact h
    · have h := hfree 1 (by decide); rw [hf1] at h; exact h
    · have h := hs2_piv 3 (by decide); rw [hp3] at h; exact h
    · have h := hfree 2 (by decide); rw [hf2] at h; exact h
    · have h := hs2_piv 4 (by decide); rw [hp4] at h; exact h
    · have h := hfree 3 (by decide); rw [hf3] at h; exact h
    · have h := hfree 4 (by decide); rw [hf4] at h; exact h
    · have h := hfree 5 (by decide); rw [hf5] at h; exact h
  have hmap_spec := part1_tables_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c6 hc6_lt
  rcases hmap_eq : v11Map_data.getD c6 (0, 0, []) with ⟨oid, gFix, us2Nat⟩
  rw [hmap_eq] at hmap_spec
  rcases hmap_spec with ⟨hoid_lt, hgFix_lt, hus2_props, hus2_match⟩
  let us2 := word3FromNat us2Nat
  have hus2_Q : ∀ u ∈ us2, quadForm c0_09 u = 1 := by
    intro u hu; rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
    have h := hus2_props un hun
    simp only [c0_09, quadForm_dec3, Nat.mod_eq_of_lt h.1, h.2.1]; rfl
  have hus2_fix_p0 : ∀ u ∈ us2, transvPt u p0_2 = p0_2 := by
    intro u hu; rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
    have h := hus2_props un hun
    have hsp : symp (dec3 ⟨un % 64, Nat.mod_lt _ (by omega)⟩) p0_2 = 0 := by
      simp only [p0_2, symp_dec3, Nat.mod_eq_of_lt h.1, h.2.2]; rfl
    simp [transvPt, hsp]
  let gFixF : Fin 64 := ⟨gFix, hgFix_lt⟩
  let s3' := applyGauge (dec3 gFixF) (applyTransvWord us2 s2)
  have hs3' : IsSignAssign s3' := applyGauge_isSignAssign _ (applyTransvWord_isSignAssign _ hs2)
  have hs3'_V11 : ∀ i : Fin 11, s3' (dec3 (V11_pt i)) = v11SignOfMask (orbRep_list.getD oid 0) i.val := by
    let SV : Nat → Bool := fun v => v != 0 && Q3_form 9 v == 0 && symp3 2 v == 0
    have hinvV : ∀ u ∈ us2Nat, u < 64 ∧ ∀ v < 64, SV v = true → SV (transv3_pt u v) = true := by
      intro u hu
      have hu' := hus2_props u hu
      refine ⟨hu'.1, fun v hv hSv => ?_⟩
      simp only [SV, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hSv ⊢
      let uF : Fin 64 := ⟨u, hu'.1⟩; let vF : Fin 64 := ⟨v, hv⟩
      have huQ : quadForm c0_09 (dec3 uF) = 1 := by simp only [c0_09, quadForm_dec3, uF, hu'.2.1]; rfl
      have hvQ : quadForm c0_09 (dec3 vF) = 0 := by simp only [c0_09, quadForm_dec3, vF, hSv.1.2]; rfl
      have hvS : symp p0_2 (dec3 vF) = 0 := by simp only [p0_2, symp_dec3, vF, hSv.2]; rfl
      have huS : symp (dec3 uF) p0_2 = 0 := by simp only [p0_2, symp_dec3, uF, hu'.2.2]; rfl
      have htv_eq : dec3 ⟨transv3_pt u v, transv3_pt_lt uF vF⟩ = transvPt (dec3 uF) (dec3 vF) :=
        (transvPt_dec3 uF vF).symm
      have hv_nz : dec3 vF ≠ 0 := fun h => hSv.1.1 (by
        have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this; rw [h0e] at this; exact this)
      have htv_nz : transv3_pt u v ≠ 0 := fun h => hv_nz (by
        have h1 : transvPt (dec3 uF) (dec3 vF) = 0 := by
          rw [← htv_eq, show (⟨transv3_pt u v, transv3_pt_lt uF vF⟩ : Fin 64) = 0 from Fin.ext h]; exact dec3_zero
        rw [← transvPt_invol (dec3 uF) (dec3 vF), h1, transvPt_zero])
      have htvQ : Q3_form 9 (transv3_pt u v) = 0 := by
        have h : quadForm c0_09 (dec3 ⟨transv3_pt u v, transv3_pt_lt uF vF⟩) = 0 := by
          rw [htv_eq, quadForm_transvPt_fix huQ, hvQ]
        rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (transv3_pt u v)
        generalize Q3_form 9 (transv3_pt u v) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
      have htvS : symp3 2 (transv3_pt u v) = 0 := by
        have h : symp p0_2 (dec3 ⟨transv3_pt u v, transv3_pt_lt uF vF⟩) = 0 := by
          rw [htv_eq, ← symp_transvPt (dec3 uF), show transvPt (dec3 uF) p0_2 = p0_2 by simp [transvPt, huS],
              transvPt_invol, hvS]
        rw [p0_2, symp_dec3] at h; have hlt := symp3_lt2 2 (transv3_pt u v)
        generalize symp3 2 (transv3_pt u v) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
      exact ⟨⟨htv_nz, htvQ⟩, htvS⟩
    let sVInit : Nat → ℤ := fun v => match V11_list.idxOf? v with | some j => v11SignOfMask c6 j | none => 0
    have hagreeV : ∀ v : Fin 64, SV v.val = true → sVInit v.val = s2 (dec3 v) := by
      intro v hSv
      simp only [SV, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hSv
      obtain ⟨iv, hiv⟩ := V11_val_surj v hSv.1.1 hSv.1.2 hSv.2
      have hveq : v = V11_pt iv := Fin.ext hiv.symm
      rw [hveq]; dsimp only [sVInit, V11_pt]; rw [V11_idxOf_val iv]; dsimp only; exact (hs2_V11 iv).symm
    intro i
    have hVi := part1_tables_spec.2.2.2.2.2.2.2.1 i.val i.isLt
    have hSVi : SV (V11_pt i).val = true := by simp [SV, V11_pt, hVi.1, hVi.2.2.1, hVi.2.2.2]
    have hw := applyWord3Nat_eq_on_inv SV us2Nat hinvV sVInit s2 hagreeV (V11_pt i) hSVi
    have hg := applyGauge3Nat_eq gFixF (applyWord3Nat us2Nat sVInit) (applyTransvWord us2 s2) (V11_pt i) hw
    dsimp only [s3']; rw [← hg]; exact hus2_match i.val i.isLt
  have hs3'_p0 : starFrust s3' p0_2 = starFrust s1 p0_2 := by
    have hfold_p0 : ∀ (ws : List (PauliIdx 3)), (∀ u ∈ ws, transvPt u p0_2 = p0_2) →
        ws.foldr (fun u cur => transvPt u cur) p0_2 = p0_2 := by
      intro ws; induction ws with
      | nil => intro _; rfl
      | cons u ws ih => intro h; simp only [List.foldr_cons, ih (fun w hw => h w (List.mem_cons_of_mem u hw)), h u (List.mem_cons_self ..)]
    dsimp only [s3']
    rw [starFrust_applyGauge, starFrust_applyTransvWord hus2_Q, hfold_p0 us2 hus2_fix_p0, starFrust_applyGauge]
  have hs3'_max : ∀ q ∈ Qminus c0_09, starFrust s3' q ≤ 6 * oid := by
    have hst_oid := starFrust_p0_eq_of_orb ⟨oid, hoid_lt⟩ hs3'_V11
    dsimp only at hst_oid
    intro q hq
    rw [← hst_oid, hs3'_p0]
    dsimp only [s3']
    rw [starFrust_applyGauge, starFrust_applyTransvWord hus2_Q, starFrust_applyGauge]
    have hq' : us2.foldr (fun u cur => transvPt u cur) q ∈ Qminus c0_09 := by
      have hgen : ∀ (ws : List (PauliIdx 3)), (∀ u ∈ ws, quadForm c0_09 u = 1) →
          ∀ x ∈ Qminus c0_09, ws.foldr (fun u cur => transvPt u cur) x ∈ Qminus c0_09 := by
        intro ws; induction ws with
        | nil => intro _ x hx; exact hx
        | cons u ws ih =>
          intro hws x hx
          have hx' := ih (fun w hw => hws w (List.mem_cons_of_mem u hw)) x hx
          simp only [List.foldr_cons, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hx' ⊢
          exact ⟨fun h0 => hx'.1 (by rw [← transvPt_invol u (ws.foldr (fun u cur => transvPt u cur) x), h0, transvPt_zero]),
            by rw [quadForm_transvPt_fix (hws u (List.mem_cons_self ..)), hx'.2]⟩
      exact hgen us2 hus2_Q q hq
    exact hs1_max _ hq'
  have hoid_pos : 0 < oid := by
    have hst_oid := starFrust_p0_eq_of_orb ⟨oid, hoid_lt⟩ hs3'_V11
    dsimp only at hst_oid
    rw [hs3'_p0, hs1_p0] at hst_oid; omega
  have hs3'_tot_le : frustPairs (Qminus c0_09) s3' ≤ 6 * min 13 (9 * oid) := by
    have h13 : frustPairs (Qminus c0_09) s3' ≤ 13 * 6 := by
      dsimp only [s3']; rw [frustPairs_applyGauge, applyTransvWord_preserves_Qminus09 hus2_Q, frustPairs_applyGauge]
      exact hs1_tot
    have hcardQ : (Qminus c0_09).card = 27 := by
      have hbij : (Finset.univ : Finset (Fin 27)).card = (Qminus c0_09).card := by
        refine Finset.card_bij (fun i _ => dec3 (A27_pt i)) (fun i _ => A27_pt_mem_Qminus i)
          (fun a _ b _ h => A27_val_inj (congr_arg Fin.val (equiv3.symm.injective h))) (fun p hp => ?_)
        have hpQ : Q3_form 9 (enc3 p).val = 0 := by
          have h := (Finset.mem_filter.mp hp).2
          rw [← dec3_enc3 p, c0_09, quadForm_dec3] at h
          have hlt := Q3_form_lt2 9 (enc3 p).val
          generalize Q3_form 9 (enc3 p).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
        have hp0 : (enc3 p).val ≠ 0 := fun h =>
          (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).1 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
        obtain ⟨i, hi⟩ := A27_val_surj (enc3 p) hp0 hpQ
        exact ⟨i, Finset.mem_univ _, by rw [show A27_pt i = enc3 p from Fin.ext hi, dec3_enc3]⟩
      rw [← hbij, Finset.card_univ, Fintype.card_fin]
    have hdc := double_count_starFrust s3'
    have hsum_le : ∑ p ∈ Qminus c0_09, starFrust s3' p ≤ 27 * (6 * oid) := by
      calc ∑ p ∈ Qminus c0_09, starFrust s3' p ≤ ∑ _p ∈ Qminus c0_09, (6 * oid) :=
            Finset.sum_le_sum fun p hp => hs3'_max p hp
        _ = 27 * (6 * oid) := by rw [Finset.sum_const, hcardQ, smul_eq_mul]
    omega
  -- 5. Gauge-fix `C16[0]` to `+1` using `p0_2` (which fixes all of `V₁₁` and flips `C16[0]`)
  let g3 : PauliIdx 3 := if s3' (dec3 (C16_pt ⟨0, by decide⟩)) = -1 then p0_2 else 0
  let s4' := applyGauge g3 s3'
  have hs4' : IsSignAssign s4' := applyGauge_isSignAssign g3 hs3'
  have hs4'_V11 : ∀ i : Fin 11, s4' (dec3 (V11_pt i)) = v11SignOfMask (orbRep_list.getD oid 0) i.val := by
    intro i
    dsimp only [s4', applyGauge, sympSign, g3]
    have hsp0 : symp p0_2 (dec3 (V11_pt i)) = 0 := by
      have hp := (part1_tables_spec.2.2.2.2.2.2.2.1 i.val i.isLt).2.2.2
      simp only [p0_2, symp_dec3, V11_pt, hp]; rfl
    by_cases hc : s3' (dec3 (C16_pt ⟨0, by decide⟩)) = -1
    · rw [if_pos hc, if_pos hsp0, one_mul]; exact hs3'_V11 i
    · rw [if_neg hc, if_pos (symp_zero_left _), one_mul]; exact hs3'_V11 i
  have hs4'_C0 : s4' (dec3 (C16_pt ⟨0, by decide⟩)) = 1 := by
    have hsp1 : symp p0_2 (dec3 (C16_pt ⟨0, by decide⟩)) = 1 := by
      have hp := (part1_tables_spec.2.2.2.2.2.2.2.2.2.1 0 (by decide)).2.2.2
      simp only [p0_2, symp_dec3, C16_pt, hp]; rfl
    have hc0_nz : dec3 (C16_pt ⟨0, by decide⟩) ≠ 0 := fun h =>
      (part1_tables_spec.2.2.2.2.2.2.2.2.2.1 0 (by decide)).1 (by
        have := congr_arg (fun w => (enc3 w).val) h; rw [enc3_dec3] at this; rw [h0e] at this; exact this)
    dsimp only [s4', applyGauge, sympSign, g3]
    rcases hs3'.2 _ hc0_nz with hpos | hneg
    · rw [hpos]; simp [symp_zero_left]
    · rw [hneg, if_pos rfl, hsp1]; decide
  have hs4'_A : ∀ i : Fin 16, ((1 >>> i.val) &&& 1) = 1 →
      s4' (dec3 (C16_pt i)) = if ((0 >>> i.val) &&& 1) = 1 then -1 else 1 := by
    intro i hi
    have hi0 : i.val = 0 := by
      by_contra hne
      have h1 : 1 >>> i.val = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ i.val)))
      simp [h1] at hi
    have hfi : i = ⟨0, by decide⟩ := Fin.ext hi0
    rw [hfi, hs4'_C0]; simp
  have hs4'_nm : ∀ i : Fin 16, ((1 >>> i.val) &&& 1) = 0 → ((0 >>> i.val) &&& 1) = 0 := fun _ _ => by simp
  have hs4'_max : ∀ q ∈ Qminus c0_09, starFrust s4' q ≤ 6 * oid := fun q hq => by
    rw [starFrust_applyGauge]; exact hs3'_max q hq
  have hs4'_tot : frustPairs (Qminus c0_09) s4' ≤ 6 * min 13 (9 * oid) := by
    rw [frustPairs_applyGauge]; exact hs3'_tot_le
  -- 6. Dispatch `oid ∈ 1..5` to `sound_checkTree16` and collapse words + gauges!
  have htree_res : ∃ (r : Fin 3) (us4 : List (PauliIdx 3)) (g4 : PauliIdx 3),
      (∀ u ∈ us4, quadForm c0_09 u = 1) ∧
      ∀ i : Fin 27, applyGauge g4 (applyTransvWord us4 s4') (dec3 (A27_pt i)) = rep27_val r i.val := by
    have hdis : ∀ (o : Fin 5), o.val + 1 = oid →
        ∃ (r : Fin 3) (us4 : List (PauliIdx 3)) (g4 : PauliIdx 3),
          (∀ u ∈ us4, quadForm c0_09 u = 1) ∧
          ∀ i : Fin 27, applyGauge g4 (applyTransvWord us4 s4') (dec3 (A27_pt i)) = rep27_val r i.val := by
      intro o ho
      rw [← ho] at hs4'_V11 hs4'_max hs4'_tot
      fin_cases o
      · exact sound_checkTree16 ⟨0, by decide⟩ tree_orb1 1 0 hs4' hs4'_V11 hs4'_A hs4'_nm hs4'_max hs4'_tot checkTree16_orb1_ok
      · exact sound_checkTree16 ⟨1, by decide⟩ tree_orb2 1 0 hs4' hs4'_V11 hs4'_A hs4'_nm hs4'_max hs4'_tot checkTree16_orb2_ok
      · exact sound_checkTree16 ⟨2, by decide⟩ tree_orb3 1 0 hs4' hs4'_V11 hs4'_A hs4'_nm hs4'_max hs4'_tot checkTree16_orb3_ok
      · exact sound_checkTree16 ⟨3, by decide⟩ tree_orb4 1 0 hs4' hs4'_V11 hs4'_A hs4'_nm hs4'_max hs4'_tot checkTree16_orb4_ok
      · exact sound_checkTree16 ⟨4, by decide⟩ tree_orb5 1 0 hs4' hs4'_V11 hs4'_A hs4'_nm hs4'_max hs4'_tot checkTree16_orb5_ok
    exact hdis ⟨oid - 1, by omega⟩ (by dsimp; omega)
  obtain ⟨r, us4, g4, hus4_Q, hmatch⟩ := htree_res
  -- Collapse `applyGauge g4 (applyTransvWord us4 (applyGauge g3 (applyGauge gFixF (applyTransvWord us2 (applyGauge g1 (applyTransvWord us1 s3))))))`
  obtain ⟨gA, hgA⟩ := applyTransvWord_applyGauge us2 g1 (applyTransvWord us1 s3)
  have hstep2 : s4' = applyGauge (g3 + (dec3 gFixF + gA)) (applyTransvWord (us1 ++ us2) s3) := by
    dsimp only [s4', s3', s2, s1]
    rw [hgA, applyGauge_applyGauge, applyGauge_applyGauge, applyTransvWord_append, add_assoc]
  obtain ⟨gB, hgB⟩ := applyTransvWord_applyGauge us4 (g3 + (dec3 gFixF + gA)) (applyTransvWord (us1 ++ us2) s3)
  refine ⟨r, (us1 ++ us2) ++ us4, g4 + gB, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_append] at hu
    rcases hu with (h | h) | h
    · exact hus1_Q u h
    · exact hus2_Q u h
    · exact hus4_Q u h
  · intro i
    rw [← hmatch i, hstep2, hgB, applyGauge_applyGauge, applyTransvWord_append]

end Part1Soundness

end FourQubitCD

end MultiQubitMUB
