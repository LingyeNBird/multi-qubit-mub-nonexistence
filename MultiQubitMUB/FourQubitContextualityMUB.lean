import MultiQubitMUB.FourQubitSpectralAndTuran

/-!
# 4-Qubit Pure-State Fourth Moment Exceeds the MUB Threshold under `CD(W(7,2)) ≥ 1575`

Proves the main breakthrough theorem:
```lean
theorem pauliMoment4_four_gt_mub_of_contextuality_1575
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    (31 / 16 : ℝ) < pauliMoment4 4 ψ
```
with **zero `sorry`**, **zero `native_decide`**, and **standard three axioms only**
(`[propext, Classical.choice, Quot.sound]`).

## Proof Architecture
1. **Computable Pure-Integer Fraction Checker (`Frac`, `CertTree`, `checkTree`)**:
   - Unnormalized positive-denominator integer fractions (zero `gcd`) so the 107-leaf
     adaptive witness tree `mainTree` over `[0, 1/4]^4` (multiples of `1/128`) is verified
     purely inside the Lean 4 kernel via `by decide`.
2. **Zero-Calculus Algebraic Monotonicity (`wPoly`, `hPoly`, `w/h`, `(1-w)/x²`, `h/x²`)**:
   - Pure polynomial factorizations establishing monotonicity, endpoint bounds, and
     strict clamping soundness (handling unbounded `|c_{13+j}| > 1/4` whenever `B_j = 32`).
3. **Order-Statistics Extraction & Soundness (`sound_checkTree`)**:
   - Extracts the 255 nonzero Pauli expectations sorted by `|c_p|`, proves `|c (idx i)| ≤ 1/4`
     for `i ≤ 15` via Parseval, and proves every branch of `checkTree` implies `False`
     under `pauliMoment4 4 ψ ≤ 31 / 16` using `FourQubitSpectralAndTuran`.
4. **Embedded 174-Leaf Witness Tree (`mainTree`) + Kernel Reduction (`mainTree_valid`)**.
-/

namespace MultiQubitMUB

namespace FourQubitMUB

/-! ### Section 1: Computable Pure-Integer Fraction Engine & Adaptive Tree Checker -/

/-- Unnormalized positive-denominator integer fraction (zero `gcd`, ultra-fast kernel `decide`). -/
structure Frac where
  n : Int
  d : Int

def Frac.ofInt (k : Int) : Frac := ⟨k, 1⟩
def Frac.neg (x : Frac) : Frac := ⟨-x.n, x.d⟩
def Frac.add (x y : Frac) : Frac :=
  if x.d == y.d then ⟨x.n + y.n, x.d⟩ else ⟨x.n * y.d + y.n * x.d, x.d * y.d⟩
def Frac.sub (x y : Frac) : Frac :=
  if x.d == y.d then ⟨x.n - y.n, x.d⟩ else ⟨x.n * y.d - y.n * x.d, x.d * y.d⟩
def Frac.mul (x y : Frac) : Frac := ⟨x.n * y.n, x.d * y.d⟩
def Frac.sq (x : Frac) : Frac := ⟨x.n * x.n, x.d * x.d⟩
def Frac.le (x y : Frac) : Bool := x.n * y.d ≤ y.n * x.d
def Frac.lt (x y : Frac) : Bool := x.n * y.d < y.n * x.d
def Frac.min (x y : Frac) : Frac := if x.le y then x else y
def Frac.max (x y : Frac) : Frac := if x.le y then y else x
def Frac.pos (x : Frac) : Bool := 0 < x.n
def Frac.nonneg (x : Frac) : Bool := 0 ≤ x.n

instance : Add Frac := ⟨Frac.add⟩
instance : Sub Frac := ⟨Frac.sub⟩
instance : Mul Frac := ⟨Frac.mul⟩
instance : Neg Frac := ⟨Frac.neg⟩

def H_MAX   : Frac := ⟨1919, 320000⟩
def W_MIN   : Frac := ⟨388592, 30000⟩
def D2_MIN  : Frac := ⟨2541, 10000⟩
def SMAX_K0 : Frac := ⟨848, 10000⟩
def SMAX_K1 : Frac := ⟨47, 1000⟩
def SMAX_K2 : Frac := ⟨19, 1000⟩

def hFrac (n d : Int) : Frac :=
  let t := 4 * n - d
  ⟨n * t * t * (2 * n + d), 32 * d * d * d * d⟩

def wFrac (n d : Int) : Frac :=
  let t := d - 4 * n
  ⟨t * t * t * (3 * d + 4 * n), 3 * d * d * d * d⟩

def omwFrac (n d : Int) : Frac :=
  let t := d - 4 * n
  let d4 := d * d * d * d
  ⟨3 * d4 - t * t * t * (3 * d + 4 * n), 3 * d4⟩

def cFrac (A : Int) : Frac :=
  ⟨256 * (32 - A) * (96 + A), 3 * A * (64 + A)⟩

def besselBelow (S1 S2w M W_lb : Frac) : Bool :=
  let s16 := S1 + Frac.ofInt 16
  let m17 := Frac.ofInt 17 * M
  if !(s16.le m17) then false
  else
    let diff := m17 - s16
    let rhs := Frac.ofInt 120 * (Frac.ofInt 17 * S2w + S1 * S1 - Frac.ofInt 2 * S1 - Frac.ofInt 16) - diff * diff
    let lhs := Frac.ofInt 255 * W_lb
    rhs.lt lhs

def minQuad1d (A B lo hi : Frac) : Frac :=
  let d_lo := Frac.ofInt 2 * A * lo + B
  let d_hi := Frac.ofInt 2 * A * hi + B
  if d_lo.nonneg then A * lo * lo + B * lo
  else if !d_hi.pos then A * hi * hi + B * hi
  else ⟨-(B.n * B.n) * A.d, 4 * A.n * B.d * B.d⟩

def quadPosOn (A B C u v : Frac) : Bool :=
  if !A.pos then
    (A * u * u + B * u + C).pos && (A * v * v + B * v + C).pos
  else
    let du := Frac.ofInt 2 * A * u + B
    let dv := Frac.ofInt 2 * A * v + B
    if du.nonneg then (A * u * u + B * u + C).pos
    else if !dv.pos then (A * v * v + B * v + C).pos
    else (Frac.ofInt 4 * A * C - B * B).pos

def quadPosGe (A B C u : Frac) : Bool :=
  if !A.pos then false
  else
    let du := Frac.ofInt 2 * A * u + B
    if du.nonneg then (A * u * u + B * u + C).pos
    else (Frac.ofInt 4 * A * C - B * B).pos

inductive MaskCert where
  | b (w0 w1 w2 w3 : Nat)
  | q (segs : List (Nat × Nat))
  deriving Inhabited

inductive LeafCert where
  | a15 (mode xcap s13 : Nat) (uph : Bool) (sk : Nat)
  | a16 (mode xcap s13 : Nat) (uph : Bool) (sk : Nat)
  | a17 (mode xcap s13 : Nat) (uph : Bool) (sk : Nat)
  | a18 (mode xcap s13 : Nat) (uph : Bool) (sk : Nat)
  | masks (mode xcap s13 : Nat) (ms : Array MaskCert)

inductive CertTree where
  | empty
  | leaf (c : LeafCert)
  | split (dim mid : Nat) (lo hi : CertTree)

def bitSet (mask j : Nat) : Bool := (mask &&& (1 <<< j)) != 0

def checkS13 (A0 A1 A2 A3 B0 B1 B2 B3 : Int) (mode xcap s13n : Nat) : Bool :=
  let s13 : Frac := ⟨s13n, 1000000⟩
  let h0 := Frac.min (hFrac A0 128) (hFrac B0 128)
  let h1 := Frac.min (hFrac A1 128) (hFrac B1 128)
  let h2 := Frac.min (hFrac A2 128) (hFrac B2 128)
  let h3 := Frac.min (hFrac A3 128) (hFrac B3 128)
  let h_lo := h0 + h1 + h2 + h3
  let H_rem := Frac.max (Frac.ofInt 0) (H_MAX - h_lo)
  let w_hi := wFrac A0 128 + wFrac A1 128 + wFrac A2 128 + wFrac A3 128
  match mode with
  | 0 =>
    (⟨13 * B0 * B0, 16384⟩ : Frac).le s13
  | 1 =>
    if !(B0 < 32) then false
    else
      let lhs := Frac.ofInt (B0 * 16384) * H_rem
      let rhs := Frac.ofInt ((32 - B0) * (32 - B0) * (64 + B0)) * s13
      lhs.le rhs
  | 7 =>
    if !(B3 < 32) then false
    else
      let denom := (32 - B3) * (32 - B3) * (64 + B3)
      let a2sum : Frac := ⟨A0 * A0 + A1 * A1 + A2 * A2 + A3 * A3, 16384⟩
      let lhs := Frac.ofInt (B3 * 16384) * H_MAX
      let rhs := Frac.ofInt denom * (s13 + a2sum)
      lhs.le rhs
  | 2 =>
    if !(0 < A3) then false
    else
      let C := cFrac A3
      let B_joint := Frac.ofInt 13 - W_MIN + w_hi + C * H_rem
      if !B_joint.pos then s13.nonneg
      else
        let denom := omwFrac B0 128 + C * hFrac B0 128
        denom.pos && (Frac.sq ⟨B0, 128⟩ * B_joint).le (s13 * denom)
  | 3 =>
    let xn : Int := xcap
    if !(0 < A3 && 0 < xn && xn ≤ B0 * 32) then false
    else
      let C := cFrac A3
      let B_joint := Frac.ofInt 13 - W_MIN + w_hi + C * H_rem
      if !B_joint.pos then s13.nonneg
      else
        let omw_xc := omwFrac xn 4096
        let denom := omw_xc + C * hFrac xn 4096
        B_joint.le omw_xc && denom.pos && (Frac.sq ⟨xn, 4096⟩ * B_joint).le (s13 * denom)
  | 4 =>
    let xn : Int := xcap
    if !(0 < A3 && 0 < xn && xn ≤ B0 * 32 && xn ≤ 368) then false
    else
      let C := cFrac A3
      let B_joint := Frac.ofInt 13 - W_MIN + w_hi + C * H_rem
      if !B_joint.pos then s13.nonneg
      else
        let ok09 := (B0 * 32 ≤ 368) || B_joint.le (omwFrac 368 4096)
        let denom := omwFrac xn 4096 + C * hFrac xn 4096
        ok09 && B_joint.le denom && denom.pos && (Frac.sq ⟨xn, 4096⟩ * B_joint).le (s13 * denom)
  | 5 =>
    let xn : Int := xcap
    if !(0 < A3 && 0 < xn && xn ≤ B0 * 32 && xn ≤ 368) then false
    else
      let C := cFrac A3
      let B_joint := Frac.ofInt 13 - W_MIN + w_hi + C * H_rem
      if !B_joint.pos then s13.nonneg
      else
        let ok09 := (B0 * 32 ≤ 368) || B_joint.le (omwFrac 368 4096)
        let denom := omwFrac xn 4096 + C * hFrac xn 4096
        ok09 && H_rem.le (hFrac xn 4096) && denom.pos && (Frac.sq ⟨xn, 4096⟩ * B_joint).le (s13 * denom)
  | 6 =>
    let xn : Int := xcap
    if !(0 < A3 && 0 < xn && xn ≤ B0 * 32 && xn ≤ 368) then false
    else
      let C := cFrac A3
      let B_joint := Frac.ofInt 13 - W_MIN + w_hi + C * H_rem
      let ok09 := (B0 * 32 ≤ 368) || B_joint.le (omwFrac 368 4096)
      let lhs := Frac.ofInt (xn * 16777216) * H_rem
      let rhs := Frac.ofInt ((1024 - xn) * (1024 - xn) * (2048 + xn)) * s13
      ok09 && H_rem.le (hFrac xn 4096) && lhs.le rhs
  | _ => false

def checkSk (_A0 A1 A2 A3 B0 B1 B2 B3 : Int) (k : Nat) (s13n : Nat) (uph : Bool) (skn : Nat) : Bool :=
  let s13 : Frac := ⟨s13n, 1000000⟩
  let sk : Frac := ⟨skn, 1000000⟩
  if !uph then
    let add_b : Frac := match k with
      | 14 => ⟨B0 * B0, 16384⟩
      | 15 => ⟨B0 * B0 + B1 * B1, 16384⟩
      | 16 => ⟨B0 * B0 + B1 * B1 + B2 * B2, 16384⟩
      | _  => ⟨B0 * B0 + B1 * B1 + B2 * B2 + B3 * B3, 16384⟩
    (s13 + add_b).le sk
  else
    if !(B3 < 32) then false
    else
      let denom := (32 - B3) * (32 - B3) * (64 + B3)
      let sub_a : Frac := match k with
        | 14 => ⟨A1 * A1 + A2 * A2 + A3 * A3, 16384⟩
        | 15 => ⟨A2 * A2 + A3 * A3, 16384⟩
        | 16 => ⟨A3 * A3, 16384⟩
        | _  => ⟨0, 1⟩
      (Frac.ofInt (B3 * 16384) * H_MAX).le (Frac.ofInt denom * (sk + sub_a))

def kFreeOf (B0 B1 B2 B3 : Int) (mask : Nat) : Nat :=
  let c0 : Nat := if bitSet mask 0 && decide (B0 < 32) then 1 else 0
  let c1 : Nat := if bitSet mask 1 && decide (B1 < 32) then 1 else 0
  let c2 : Nat := if bitSet mask 2 && decide (B2 < 32) then 1 else 0
  let c3 : Nat := if bitSet mask 3 && decide (B3 < 32) then 1 else 0
  3 - (c0 + c1 + c2 + c3)

def checkMethod (A0 A1 A2 A3 B0 B1 B2 B3 : Int) (mask : Nat) (s13 : Frac)
    (m : Nat) (u v : Frac) (is_inf : Bool) : Bool :=
  let b0 := bitSet mask 0; let b1 := bitSet mask 1; let b2 := bitSet mask 2; let b3 := bitSet mask 3
  let ic0 := b0 && decide (B0 < 32); let ic1 := b1 && decide (B1 < 32)
  let ic2 := b2 && decide (B2 < 32); let ic3 := b3 && decide (B3 < 32)
  let k_free := kFreeOf B0 B1 B2 B3 mask
  let s2_lo : Frac :=
    ⟨(if ic0 then A0 * A0 else 0) + (if ic1 then A1 * A1 else 0) +
     (if ic2 then A2 * A2 else 0) + (if ic3 then A3 * A3 else 0), 16384⟩
  let s2_hi : Frac :=
    ⟨(if ic0 then B0 * B0 else 0) + (if ic1 then B1 * B1 else 0) +
     (if ic2 then B2 * B2 else 0) + (if ic3 then B3 * B3 else 0), 16384⟩
  let J_d2_hi : Frac :=
    ⟨(if !b0 then (32 - A0) * (32 - A0) else 0) + (if !b1 then (32 - A1) * (32 - A1) else 0) +
     (if !b2 then (32 - A2) * (32 - A2) else 0) + (if !b3 then (32 - A3) * (32 - A3) else 0), 16384⟩
  let J_q4_lo : Frac :=
    ⟨(if !b0 && decide (B0 < 32) then (1024 - B0 * B0) * (1024 - B0 * B0) else 0) +
     (if !b1 && decide (B1 < 32) then (1024 - B1 * B1) * (1024 - B1 * B1) else 0) +
     (if !b2 && decide (B2 < 32) then (1024 - B2 * B2) * (1024 - B2 * B2) else 0) +
     (if !b3 && decide (B3 < 32) then (1024 - B3 * B3) * (1024 - B3 * B3) else 0), 16384 * 16384⟩
  let tail_mult : Frac := ⟨(A3 + 32) * (A3 + 32), 16384⟩
  let uq_raw := Frac.max (Frac.ofInt 0) (⟨1, 16⟩ - s13)
  let u_q4_min := uq_raw * uq_raw
  let inv_k : Frac := if k_free == 0 then ⟨0, 1⟩ else ⟨1, k_free⟩
  match m with
  | 1 =>
    let beta := ⟨1, 8⟩ + tail_mult
    let cap_min :=
      (if ic0 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
      (if ic1 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
      (if ic2 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
      (if ic3 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
    let C := cap_min - beta * s13 + u_q4_min + J_q4_lo + tail_mult * (D2_MIN - ⟨1, 16⟩ - J_d2_hi)
    if is_inf then quadPosGe inv_k (-beta) C u else quadPosOn inv_k (-beta) C u v
  | 2 =>
    let beta : Frac := ⟨1, 8⟩
    let cap_min :=
      (if ic0 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
      (if ic1 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
      (if ic2 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
      (if ic3 then minQuad1d (Frac.ofInt 1) (-beta) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
    let C := cap_min - beta * s13 + u_q4_min + J_q4_lo
    if is_inf then quadPosGe inv_k (-beta) C u else quadPosOn inv_k (-beta) C u v
  | 3 | 4 =>
    if is_inf then false
    else
      let z_lo := s2_lo
      let z_hi := s13 + s2_hi
      let lin_z := ⟨1, 8⟩ + (z_lo + z_hi + Frac.ofInt 2 * u) * ⟨1, 16⟩
      let const_z2 := (z_lo * z_hi + Frac.ofInt 2 * z_hi * u) * ⟨1, 16⟩
      let cap_min_D :=
        (if ic0 then minQuad1d (Frac.ofInt 2) (-lin_z) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
        (if ic1 then minQuad1d (Frac.ofInt 2) (-lin_z) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
        (if ic2 then minQuad1d (Frac.ofInt 2) (-lin_z) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
        (if ic3 then minQuad1d (Frac.ofInt 2) (-lin_z) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
      let qC := cap_min_D - lin_z * s13 + const_z2
      let qB := -(⟨1, 8⟩ + z_hi * ⟨1, 8⟩)
      let qA := Frac.ofInt 2 * inv_k - ⟨1, 16⟩
      if m == 4 then quadPosOn qA qB qC u v
      else
        let Kd := Frac.ofInt 1 - Frac.ofInt 16 * s13 - s2_hi
        v.le Kd && quadPosOn (qA + ⟨1, 128⟩) (qB - Kd * ⟨1, 64⟩) (qC + Kd * Kd * ⟨1, 128⟩) u v
  | _ => false

def checkSegs (A0 A1 A2 A3 B0 B1 B2 B3 : Int) (mask : Nat) (s13 : Frac) (k_free : Nat)
    (u_n : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | [(m, 0)] =>
    if k_free == 0 then u_n == 0 && checkMethod A0 A1 A2 A3 B0 B1 B2 B3 mask s13 m ⟨0, 1⟩ ⟨0, 1⟩ false
    else checkMethod A0 A1 A2 A3 B0 B1 B2 B3 mask s13 m ⟨u_n, 200⟩ ⟨0, 1⟩ true
  | (m, v_n) :: rest =>
    if k_free == 0 || v_n ≤ u_n then false
    else checkMethod A0 A1 A2 A3 B0 B1 B2 B3 mask s13 m ⟨u_n, 200⟩ ⟨v_n, 200⟩ false &&
         checkSegs A0 A1 A2 A3 B0 B1 B2 B3 mask s13 k_free v_n rest

def checkMask (A0 A1 A2 A3 B0 B1 B2 B3 : Int) (mask : Nat) (s13 : Frac) : MaskCert → Bool
  | .b w0 w1 w2 w3 =>
    let i0 : Int := w0; let i1 : Int := w1; let i2 : Int := w2; let i3 : Int := w3
    let okW :=
      (w0 ≤ 16 && (decide (B0 < 32) || w0 == 0)) &&
      (w1 ≤ 16 && (decide (B1 < 32) || w1 == 0)) &&
      (w2 ≤ 16 && (decide (B2 < 32) || w2 == 0)) &&
      (w3 ≤ 16 && (decide (B3 < 32) || w3 == 0))
    if !okW then false
    else
      let b0 := bitSet mask 0; let b1 := bitSet mask 1; let b2 := bitSet mask 2; let b3 := bitSet mask 3
      let win_n : Int := (if b0 then i0 else 0) + (if b1 then i1 else 0) + (if b2 then i2 else 0) + (if b3 then i3 else 0)
      let wout_n : Int := (if !b0 then i0 else 0) + (if !b1 then i1 else 0) + (if !b2 then i2 else 0) + (if !b3 then i3 else 0)
      let w2_n : Int := i0 * i0 + i1 * i1 + i2 * i2 + i3 * i3
      let S1 : Frac := ⟨14 * 16 + win_n + wout_n, 16⟩
      let S2w : Frac := ⟨14 * 256 + w2_n, 256⟩
      let mv_n : Int :=
        (if decide (B0 < 32) then i0 * (1024 - B0 * B0) else 0) +
        (if decide (B1 < 32) then i1 * (1024 - B1 * B1) else 0) +
        (if decide (B2 < 32) then i2 * (1024 - B2 * B2) else 0) +
        (if decide (B3 < 32) then i3 * (1024 - B3 * B3) else 0)
      let M : Frac := Frac.ofInt 14 - Frac.ofInt 16 * s13 + ⟨mv_n, 16 * 1024⟩
      let W_lb : Frac := ⟨2 * (16 + wout_n) * (80 + win_n), 256⟩
      besselBelow S1 S2w M W_lb
  | .q segs =>
    checkSegs A0 A1 A2 A3 B0 B1 B2 B3 mask s13 (kFreeOf B0 B1 B2 B3 mask) 0 segs

def checkLeaf (A0 A1 A2 A3 B0 B1 B2 B3 : Int) : LeafCert → Bool
  | .a15 mode xcap s13n uph skn =>
    decide (B0 < 32) && checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n &&
    checkSk A0 A1 A2 A3 B0 B1 B2 B3 14 s13n uph skn &&
    (⟨skn, 1000000⟩ : Frac).le SMAX_K2 &&
    besselBelow (Frac.ofInt 15) (Frac.ofInt 15) (Frac.ofInt 15 - Frac.ofInt 16 * ⟨skn, 1000000⟩) (Frac.ofInt 20)
  | .a16 mode xcap s13n uph skn =>
    decide (B1 < 32) && checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n &&
    checkSk A0 A1 A2 A3 B0 B1 B2 B3 15 s13n uph skn &&
    (⟨skn, 1000000⟩ : Frac).le SMAX_K1 &&
    besselBelow (Frac.ofInt 16) (Frac.ofInt 16) (Frac.ofInt 16 - Frac.ofInt 16 * ⟨skn, 1000000⟩) (Frac.ofInt 24)
  | .a17 mode xcap s13n uph skn =>
    decide (B2 < 32) && checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n &&
    checkSk A0 A1 A2 A3 B0 B1 B2 B3 16 s13n uph skn &&
    (⟨skn, 1000000⟩ : Frac).le SMAX_K0 &&
    besselBelow (Frac.ofInt 17) (Frac.ofInt 17) (Frac.ofInt 17 - Frac.ofInt 16 * ⟨skn, 1000000⟩) (Frac.ofInt 28)
  | .a18 mode xcap s13n uph skn =>
    decide (B3 < 32) && checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n &&
    checkSk A0 A1 A2 A3 B0 B1 B2 B3 17 s13n uph skn &&
    besselBelow (Frac.ofInt 18) (Frac.ofInt 18) (Frac.ofInt 18 - Frac.ofInt 16 * ⟨skn, 1000000⟩) (Frac.ofInt 32)
  | .masks mode xcap s13n ms =>
    let s13 : Frac := ⟨s13n, 1000000⟩
    ms.size == 15 &&
    checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n &&
    s13.le SMAX_K2 &&
    besselBelow (Frac.ofInt 14) (Frac.ofInt 14) (Frac.ofInt 14 - Frac.ofInt 16 * s13) (Frac.ofInt 16) &&
    (List.range 15).all fun mask => checkMask A0 A1 A2 A3 B0 B1 B2 B3 mask s13 ms[mask]!

def imax (a b : Int) : Int := if a ≤ b then b else a
def imin (a b : Int) : Int := if a ≤ b then a else b

def checkTree (A0 A1 A2 A3 B0 B1 B2 B3 : Int) : CertTree → Bool
  | .empty =>
    let nA1 := imax A1 A0; let nA2 := imax A2 nA1; let nA3 := imax A3 nA2
    let nB2 := imin B2 B3; let nB1 := imin B1 nB2; let nB0 := imin B0 nB1
    decide (A0 > nB0) || decide (nA1 > nB1) || decide (nA2 > nB2) || decide (nA3 > B3)
  | .leaf c =>
    let nA1 := imax A1 A0; let nA2 := imax A2 nA1; let nA3 := imax A3 nA2
    let nB2 := imin B2 B3; let nB1 := imin B1 nB2; let nB0 := imin B0 nB1
    checkLeaf A0 nA1 nA2 nA3 nB0 nB1 nB2 B3 c
  | .split dim mid lo hi =>
    let nA1 := imax A1 A0; let nA2 := imax A2 nA1; let nA3 := imax A3 nA2
    let nB2 := imin B2 B3; let nB1 := imin B1 nB2; let nB0 := imin B0 nB1
    let m : Int := mid
    match dim with
    | 0 => checkTree A0 nA1 nA2 nA3 (imin nB0 m) nB1 nB2 B3 lo && checkTree (imax A0 m) nA1 nA2 nA3 nB0 nB1 nB2 B3 hi
    | 1 => checkTree A0 nA1 nA2 nA3 nB0 (imin nB1 m) nB2 B3 lo && checkTree A0 (imax nA1 m) nA2 nA3 nB0 nB1 nB2 B3 hi
    | 2 => checkTree A0 nA1 nA2 nA3 nB0 nB1 (imin nB2 m) B3 lo && checkTree A0 nA1 (imax nA2 m) nA3 nB0 nB1 nB2 B3 hi
    | 3 => checkTree A0 nA1 nA2 nA3 nB0 nB1 nB2 (imin B3 m) lo && checkTree A0 nA1 nA2 (imax nA3 m) nB0 nB1 nB2 B3 hi
    | _ => false

/-! ### Section 2: `Frac` Real-Valued Semantics & Exact Algebraic Monotonicity (Zero Calculus!) -/

noncomputable def Frac.toReal (x : Frac) : ℝ := (x.n : ℝ) / (x.d : ℝ)
def Frac.Valid (x : Frac) : Prop := 0 < x.d

private lemma Frac.mk_valid {n d : Int} (hd : 0 < d) : (⟨n, d⟩ : Frac).Valid := hd
private lemma Frac.valid_ofInt (k : Int) : (Frac.ofInt k).Valid := Int.zero_lt_one
private lemma valid_H_MAX : H_MAX.Valid := by norm_num [H_MAX, Frac.Valid]
private lemma valid_W_MIN : W_MIN.Valid := by norm_num [W_MIN, Frac.Valid]
private lemma valid_D2_MIN : D2_MIN.Valid := by norm_num [D2_MIN, Frac.Valid]
private lemma valid_SMAX_K0 : SMAX_K0.Valid := by norm_num [SMAX_K0, Frac.Valid]
private lemma valid_SMAX_K1 : SMAX_K1.Valid := by norm_num [SMAX_K1, Frac.Valid]
private lemma valid_SMAX_K2 : SMAX_K2.Valid := by norm_num [SMAX_K2, Frac.Valid]
private lemma Frac.valid_neg {x : Frac} (hx : x.Valid) : (-x).Valid := hx
private lemma Frac.valid_add {x y : Frac} (hx : x.Valid) (hy : y.Valid) : (x + y).Valid := by
  change (Frac.add x y).Valid; unfold Frac.add Frac.Valid at *
  split_ifs
  · exact hx
  · exact mul_pos hx hy
private lemma Frac.valid_sub {x y : Frac} (hx : x.Valid) (hy : y.Valid) : (x - y).Valid := by
  change (Frac.sub x y).Valid; unfold Frac.sub Frac.Valid at *
  split_ifs
  · exact hx
  · exact mul_pos hx hy
private lemma Frac.valid_mul {x y : Frac} (hx : x.Valid) (hy : y.Valid) : (x * y).Valid :=
  mul_pos hx hy
private lemma Frac.valid_sq {x : Frac} (hx : x.Valid) : (Frac.sq x).Valid :=
  mul_pos hx hx
private lemma Frac.valid_min {x y : Frac} (hx : x.Valid) (hy : y.Valid) : (Frac.min x y).Valid := by
  unfold Frac.min; split_ifs <;> assumption
private lemma Frac.valid_max {x y : Frac} (hx : x.Valid) (hy : y.Valid) : (Frac.max x y).Valid := by
  unfold Frac.max; split_ifs <;> assumption

private lemma Frac.d_pos {x : Frac} (hx : x.Valid) : (0 : ℝ) < (x.d : ℝ) := Int.cast_pos.mpr hx
private lemma Frac.d_ne {x : Frac} (hx : x.Valid) : (x.d : ℝ) ≠ 0 := ne_of_gt (Frac.d_pos hx)

private lemma Frac.toReal_ofInt (k : Int) : (Frac.ofInt k).toReal = (k : ℝ) := by
  simp [Frac.ofInt, Frac.toReal]
private lemma Frac.toReal_neg (x : Frac) : (-x).toReal = -x.toReal := by
  change ((-x.n : Int) : ℝ) / (x.d : ℝ) = -((x.n : ℝ) / (x.d : ℝ)); push_cast; ring
private lemma Frac.toReal_add {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    (x + y).toReal = x.toReal + y.toReal := by
  change (Frac.add x y).toReal = _; unfold Frac.add Frac.toReal
  have hdx := Frac.d_ne hx; have hdy := Frac.d_ne hy
  by_cases h : x.d == y.d
  · simp only [h, ↓reduceIte]
    have hdeq : x.d = y.d := eq_of_beq h
    rw [hdeq]; push_cast; field_simp [hdy]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; push_cast; field_simp [hdx, hdy]
private lemma Frac.toReal_sub {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    (x - y).toReal = x.toReal - y.toReal := by
  change (Frac.sub x y).toReal = _; unfold Frac.sub Frac.toReal
  have hdx := Frac.d_ne hx; have hdy := Frac.d_ne hy
  by_cases h : x.d == y.d
  · simp only [h, ↓reduceIte]
    have hdeq : x.d = y.d := eq_of_beq h
    rw [hdeq]; push_cast; field_simp [hdy]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; push_cast; field_simp [hdx, hdy]
private lemma Frac.toReal_mul (x y : Frac) : (x * y).toReal = x.toReal * y.toReal := by
  change ((x.n * y.n : Int) : ℝ) / ((x.d * y.d : Int) : ℝ) = ((x.n : ℝ) / (x.d : ℝ)) * ((y.n : ℝ) / (y.d : ℝ))
  push_cast; ring
private lemma Frac.toReal_sq (x : Frac) : (Frac.sq x).toReal = x.toReal ^ 2 := by
  simp only [Frac.sq, Frac.toReal]; push_cast; ring

private lemma Frac.le_iff {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    x.le y = true ↔ x.toReal ≤ y.toReal := by
  simp only [Frac.le, decide_eq_true_eq, Frac.toReal]
  rw [div_le_div_iff₀ (Frac.d_pos hx) (Frac.d_pos hy)]
  exact_mod_cast Iff.rfl

private lemma Frac.lt_iff {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    x.lt y = true ↔ x.toReal < y.toReal := by
  simp only [Frac.lt, decide_eq_true_eq, Frac.toReal]
  rw [div_lt_div_iff₀ (Frac.d_pos hx) (Frac.d_pos hy)]
  exact_mod_cast Iff.rfl

private lemma Frac.pos_iff {x : Frac} (hx : x.Valid) : x.pos = true ↔ 0 < x.toReal := by
  simp only [Frac.pos, decide_eq_true_eq, Frac.toReal]
  rw [div_pos_iff_of_pos_right (Frac.d_pos hx)]
  exact_mod_cast Iff.rfl

private lemma Frac.nonneg_iff {x : Frac} (hx : x.Valid) : x.nonneg = true ↔ 0 ≤ x.toReal := by
  simp only [Frac.nonneg, decide_eq_true_eq, Frac.toReal]
  rw [div_nonneg_iff]
  have hd := Frac.d_pos hx
  constructor
  · intro h; left; exact ⟨by exact_mod_cast h, le_of_lt hd⟩
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact_mod_cast h
    · linarith

private lemma Frac.toReal_min {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    (Frac.min x y).toReal = Min.min x.toReal y.toReal := by
  unfold Frac.min
  split_ifs with h
  · exact (min_eq_left ((Frac.le_iff hx hy).mp h)).symm
  · have hgt : y.toReal < x.toReal := not_le.mp (fun hle => h ((Frac.le_iff hx hy).mpr hle))
    exact (min_eq_right (le_of_lt hgt)).symm

private lemma Frac.toReal_max {x y : Frac} (hx : x.Valid) (hy : y.Valid) :
    (Frac.max x y).toReal = Max.max x.toReal y.toReal := by
  unfold Frac.max
  split_ifs with h
  · exact (max_eq_right ((Frac.le_iff hx hy).mp h)).symm
  · have hgt : y.toReal < x.toReal := not_le.mp (fun hle => h ((Frac.le_iff hx hy).mpr hle))
    exact (max_eq_left (le_of_lt hgt)).symm

private lemma Frac.valid_hFrac {n d : Int} (hd : 0 < d) : (hFrac n d).Valid := by
  unfold hFrac Frac.Valid; positivity
private lemma Frac.valid_wFrac {n d : Int} (hd : 0 < d) : (wFrac n d).Valid := by
  unfold wFrac Frac.Valid; positivity
private lemma Frac.valid_omwFrac {n d : Int} (hd : 0 < d) : (omwFrac n d).Valid := by
  unfold omwFrac Frac.Valid; positivity
private lemma Frac.valid_cFrac {A : Int} (hA : 0 < A) : (cFrac A).Valid := by
  unfold cFrac Frac.Valid; positivity

private lemma Frac.toReal_hFrac {n d : Int} (hd : 0 < d) :
    (hFrac n d).toReal = hPoly ((n : ℝ) / (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hd)
  simp only [hFrac, Frac.toReal, hPoly]; push_cast; field_simp [hd0]; ring

private lemma Frac.toReal_wFrac {n d : Int} (hd : 0 < d) :
    (wFrac n d).toReal = wPoly ((n : ℝ) / (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hd)
  simp only [wFrac, Frac.toReal, wPoly]; push_cast; field_simp [hd0]

private lemma Frac.toReal_omwFrac {n d : Int} (hd : 0 < d) :
    (omwFrac n d).toReal = 1 - wPoly ((n : ℝ) / (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hd)
  simp only [omwFrac, Frac.toReal, wPoly]; push_cast; field_simp [hd0]

private lemma Frac.toReal_cFrac {A : Int} (hA : 0 < A) :
    (cFrac A).toReal =
      16 * (1 - 4 * ((A : ℝ) / 128)) * (1 + (4 / 3) * ((A : ℝ) / 128)) /
        (((A : ℝ) / 128) * (((A : ℝ) / 128) + 1 / 2)) := by
  have hA0 : (A : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hA)
  have hA64 : (A : ℝ) + 64 ≠ 0 := by
    have : (0 : ℝ) < (A : ℝ) := Int.cast_pos.mpr hA
    linarith
  simp only [cFrac, Frac.toReal]; push_cast
  field_simp [hA0, hA64]; ring

/-! #### Zero-Calculus Algebraic Monotonicity Lemmas for `wPoly` and `hPoly` -/

lemma wPoly_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : wPoly y ≤ wPoly x := by
  have hfac : wPoly x - wPoly y =
      (32 / 3 : ℝ) * (y - x) * (1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2)) := by
    simp only [wPoly]; ring
  have hsq : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have hge : 4 * (x + y) ^ 3 ≤ 8 * (x + y) * (x ^ 2 + y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 4 * (x + y) by linarith)
    linarith
  have hcub : 0 ≤ 1 - 3 * (x + y) + 4 * (x + y) ^ 3 := by
    have hid : 1 - 3 * (x + y) + 4 * (x + y) ^ 3 = (1 - 2 * (x + y)) ^ 2 * (1 + (x + y)) := by ring
    rw [hid]; exact mul_nonneg (sq_nonneg _) (by linarith)
  have hpos : 0 ≤ 1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2) := by linarith
  have hmul : 0 ≤ (32 / 3 : ℝ) * (y - x) * (1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hpos
  linarith

lemma wPoly_strictAnti {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1 / 4) : wPoly y < wPoly x := by
  have hfac : wPoly x - wPoly y =
      (32 / 3 : ℝ) * (y - x) * (1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2)) := by
    simp only [wPoly]; ring
  have hsq : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have hge : 4 * (x + y) ^ 3 ≤ 8 * (x + y) * (x ^ 2 + y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 4 * (x + y) by linarith)
    linarith
  have hcub : 0 < 1 - 3 * (x + y) + 4 * (x + y) ^ 3 := by
    have hid : 1 - 3 * (x + y) + 4 * (x + y) ^ 3 = (1 - 2 * (x + y)) ^ 2 * (1 + (x + y)) := by ring
    rw [hid]
    have h1 : 0 < 1 - 2 * (x + y) := by linarith
    have h2 : 0 < 1 + (x + y) := by linarith
    positivity
  have hpos : 0 < 1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2) := by linarith
  have hmul : 0 < (32 / 3 : ℝ) * (y - x) * (1 - 3 * (x + y) + 8 * (x + y) * (x ^ 2 + y ^ 2)) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hpos
  linarith

lemma hPoly_ge_min_endpoints {a x b : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ 1 / 4) :
    min (hPoly a) (hPoly b) ≤ hPoly x := by
  by_cases hpeak : 0 ≤ 1 - 8 * x - 32 * x ^ 2
  · -- Left of the peak: `hPoly a ≤ hPoly x`!
    refine le_trans (min_le_left _ _) ?_
    have hdiff : hPoly x - hPoly a =
        (x - a) * ((1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2) +
          (x - a) * (3 / 16 - (3 * x ^ 2 + 2 * x * a + a ^ 2))) := by
      simp only [hPoly]; ring
    have h1 : 0 ≤ (1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hpeak
    have h2 : 3 * x ^ 2 + 2 * x * a + a ^ 2 ≤ 3 / 16 := by nlinarith
    have h3 : 0 ≤ (x - a) * (3 / 16 - (3 * x ^ 2 + 2 * x * a + a ^ 2)) :=
      mul_nonneg (by linarith) (by linarith)
    have hmul := mul_nonneg (show 0 ≤ x - a by linarith) (show 0 ≤ _ by linarith :
      0 ≤ (1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2) +
          (x - a) * (3 / 16 - (3 * x ^ 2 + 2 * x * a + a ^ 2)))
    linarith
  · -- Right of the peak: `hPoly b ≤ hPoly x`!
    push Not at hpeak
    refine le_trans (min_le_right _ _) ?_
    by_cases hx4 : x = 1 / 4
    · have hb4 : b = 1 / 4 := by linarith
      rw [hx4, hb4]
    · have hlt4 : 0 < 1 / 4 - x := by
        rcases lt_or_eq_of_le (le_trans hxb hb) with h | h
        · linarith
        · exact absurd h hx4
      let P : ℝ → ℝ → ℝ := fun u v => 1 / 32 - (3 / 16) * (u + v) + (u + v) * (u ^ 2 + v ^ 2)
      have hdiff : hPoly b - hPoly x = (b - x) * P b x := by simp only [hPoly, P]; ring
      have hdiv : (1 / 4 - x) * P b x =
          (1 / 4 - b) * ((1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2)) +
          (b - x) * (-x * (1 / 4 - x) * (x + 1 / 2)) -
          (b - x) * (1 / 4 - b) * (1 / 4 - x) * (b + 2 * x + 1 / 4) := by
        simp only [P]; ring
      have t1 : (1 / 4 - b) * ((1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2)) ≤ 0 := by
        have hneg : (1 / 32 : ℝ) * (1 - 4 * x) * (1 - 8 * x - 32 * x ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (by linarith)) (le_of_lt hpeak)
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      have t2 : (b - x) * (-x * (1 / 4 - x) * (x + 1 / 2)) ≤ 0 := by
        have hneg : -x * (1 / 4 - x) * (x + 1 / 2) ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      have t3 : 0 ≤ (b - x) * (1 / 4 - b) * (1 / 4 - x) * (b + 2 * x + 1 / 4) := by
        have h1 : 0 ≤ (b - x) * (1 / 4 - b) := mul_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ (1 / 4 - x) * (b + 2 * x + 1 / 4) := mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hP_le : P b x ≤ 0 := by nlinarith
      have hmul : (b - x) * P b x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hP_le
      linarith

lemma hPoly_strictMono_009 {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 368 / 4096) :
    hPoly x < hPoly y := by
  have hdiff : hPoly y - hPoly x =
      (y - x) * ((1 / 32 : ℝ) * (1 - 4 * y) * (1 - 8 * y - 32 * y ^ 2) +
        (y - x) * (3 / 16 - (3 * y ^ 2 + 2 * y * x + x ^ 2))) := by
    simp only [hPoly]; ring
  have hpeak : 0 < 1 - 8 * y - 32 * y ^ 2 := by nlinarith
  have h1 : 0 < (1 / 32 : ℝ) * (1 - 4 * y) * (1 - 8 * y - 32 * y ^ 2) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hpeak
  have h2 : 3 * y ^ 2 + 2 * y * x + x ^ 2 ≤ 3 / 16 := by nlinarith
  have h3 : 0 ≤ (y - x) * (3 / 16 - (3 * y ^ 2 + 2 * y * x + x ^ 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have hmul : 0 < (y - x) * ((1 / 32 : ℝ) * (1 - 4 * y) * (1 - 8 * y - 32 * y ^ 2) +
      (y - x) * (3 / 16 - (3 * y ^ 2 + 2 * y * x + x ^ 2))) :=
    mul_pos (by linarith) (by linarith)
  linarith

lemma wPoly_le_c_mul_hPoly {a y : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hay : a ≤ y) :
    let C : ℝ := 16 * (1 - 4 * a) * (1 + (4 / 3) * a) / (a * (a + 1 / 2))
    wPoly y ≤ C * hPoly y := by
  intro C
  have hden_pos : 0 < a * (a + 1 / 2) := by positivity
  have hC_nn : 0 ≤ C := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (le_of_lt hden_pos)
  by_cases hy4 : y ≤ 1 / 4
  · have hwy : wPoly y = (1 - 4 * y) ^ 2 * ((1 - 4 * y) * (1 + (4 / 3) * y)) := by simp only [wPoly]; ring
    have hhy : hPoly y = (1 - 4 * y) ^ 2 * (y * (y + 1 / 2) / 16) := by simp only [hPoly]; ring
    have hg : (1 - 4 * y) * (1 + (4 / 3) * y) ≤ (1 - 4 * a) * (1 + (4 / 3) * a) := by
      have hid : (1 - 4 * a) * (1 + (4 / 3) * a) - (1 - 4 * y) * (1 + (4 / 3) * y) =
          (y - a) * (8 / 3 + (16 / 3) * (y + a)) := by ring
      have hnn := mul_nonneg (show 0 ≤ y - a by linarith) (show (0 : ℝ) ≤ 8 / 3 + (16 / 3) * (y + a) by linarith)
      linarith
    have hd : a * (a + 1 / 2) / 16 ≤ y * (y + 1 / 2) / 16 := by nlinarith
    have hCa : C * (a * (a + 1 / 2) / 16) = (1 - 4 * a) * (1 + (4 / 3) * a) := by
      simp only [C]; field_simp [ne_of_gt hden_pos]
    have hstep : (1 - 4 * y) * (1 + (4 / 3) * y) ≤ C * (y * (y + 1 / 2) / 16) := by
      have := mul_le_mul_of_nonneg_left hd hC_nn
      linarith
    rw [hwy, hhy]
    have hrhs : C * ((1 - 4 * y) ^ 2 * (y * (y + 1 / 2) / 16)) =
        (1 - 4 * y) ^ 2 * (C * (y * (y + 1 / 2) / 16)) := by ring
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
  · push Not at hy4
    have hw_neg : wPoly y ≤ 0 := by
      have h1 : (1 - 4 * y) ^ 3 ≤ 0 := by
        have : (1 - 4 * y) ^ 3 = (1 - 4 * y) ^ 2 * (1 - 4 * y) := by ring
        rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
      simp only [wPoly]; exact mul_nonpos_of_nonpos_of_nonneg h1 (by linarith)
    have hh_nn : 0 ≤ C * hPoly y := mul_nonneg hC_nn (hPoly_nonneg (by linarith))
    linarith

lemma sq_le_endpoint_joint {xc x C : ℝ} (hxc_pos : 0 < xc) (hxc4 : xc ≤ 1 / 4)
    (hx : 0 ≤ x) (hxxc : x ≤ xc) (hC : 0 ≤ C) :
    x ^ 2 * ((1 - wPoly xc) + C * hPoly xc) ≤ xc ^ 2 * ((1 - wPoly x) + C * hPoly x) := by
  have hw_cmp : x ^ 2 * (1 - wPoly xc) ≤ xc ^ 2 * (1 - wPoly x) := by
    have hid : xc ^ 2 * (1 - wPoly x) - x ^ 2 * (1 - wPoly xc) =
        (32 / 3 : ℝ) * x * xc * (xc - x) * (1 - 8 * x * xc * (x + xc)) := by
      simp only [wPoly]; ring
    have h1 : 8 * x * xc * (x + xc) ≤ 1 := by
      have hxx : x * xc ≤ 1 / 16 := by nlinarith
      have hsum : x + xc ≤ 1 / 2 := by linarith
      nlinarith
    have hnn : 0 ≤ (32 / 3 : ℝ) * x * xc * (xc - x) * (1 - 8 * x * xc * (x + xc)) := by
      have ha : 0 ≤ (32 / 3 : ℝ) * x * xc := by positivity
      have hb : 0 ≤ (xc - x) * (1 - 8 * x * xc * (x + xc)) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    linarith
  have hh_cmp : x ^ 2 * hPoly xc ≤ xc ^ 2 * hPoly x := by
    have hid : xc ^ 2 * hPoly x - x ^ 2 * hPoly xc =
        x * xc * (xc - x) * (1 / 32 - x * xc * (x + xc)) := by
      simp only [hPoly]; ring
    have h1 : x * xc * (x + xc) ≤ 1 / 32 := by
      have hxx : x * xc ≤ 1 / 16 := by nlinarith
      have hsum : x + xc ≤ 1 / 2 := by linarith
      nlinarith
    have hnn : 0 ≤ x * xc * (xc - x) * (1 / 32 - x * xc * (x + xc)) := by
      have ha : 0 ≤ x * xc := by positivity
      have hb : 0 ≤ (xc - x) * (1 / 32 - x * xc * (x + xc)) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    linarith
  have hC_hh := mul_le_mul_of_nonneg_left hh_cmp hC
  linarith

lemma sq_le_pureH {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hb : b ≤ 1 / 4) :
    x ^ 2 * ((1 / 4 - b) ^ 2 * (1 / 2 + b)) ≤ b * hPoly x := by
  have hf_dec : (1 / 4 - b) ^ 2 * (1 / 2 + b) ≤ (1 / 4 - x) ^ 2 * (1 / 2 + x) := by
    have hid : (1 / 4 - x) ^ 2 * (1 / 2 + x) - (1 / 4 - b) ^ 2 * (1 / 2 + b) =
        (b - x) * (3 / 16 - (b ^ 2 + b * x + x ^ 2)) := by ring
    have h1 : b ^ 2 + b * x + x ^ 2 ≤ 3 / 16 := by nlinarith
    have hnn := mul_nonneg (show 0 ≤ b - x by linarith) (show 0 ≤ 3 / 16 - (b ^ 2 + b * x + x ^ 2) by linarith)
    linarith
  have h1 : x ^ 2 * ((1 / 4 - b) ^ 2 * (1 / 2 + b)) ≤ x ^ 2 * ((1 / 4 - x) ^ 2 * (1 / 2 + x)) :=
    mul_le_mul_of_nonneg_left hf_dec (sq_nonneg x)
  have h2 : x ^ 2 * ((1 / 4 - x) ^ 2 * (1 / 2 + x)) ≤ b * hPoly x := by
    have heq : b * hPoly x - x ^ 2 * ((1 / 4 - x) ^ 2 * (1 / 2 + x)) =
        (b - x) * (x * (1 / 4 - x) ^ 2 * (1 / 2 + x)) := by simp only [hPoly]; ring
    have hnn := mul_nonneg (show 0 ≤ b - x by linarith) (show 0 ≤ x * (1 / 4 - x) ^ 2 * (1 / 2 + x) by positivity)
    linarith
  linarith

/-! ### Section 3: Soundness of Quadratic & Bessel Primitives -/

private lemma sound_minQuad1d {A B lo hi : Frac} (hA : A.Valid) (hAn : 0 < A.n)
    (hB : B.Valid) (hlo : lo.Valid) (hhi : hi.Valid)
    {x : ℝ} (h1 : lo.toReal ≤ x) (h2 : x ≤ hi.toReal) :
    (minQuad1d A B lo hi).Valid ∧
    (minQuad1d A B lo hi).toReal ≤ A.toReal * x ^ 2 + B.toReal * x := by
  have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp (by simp [Frac.pos, hAn])
  have hd_lo_v : (Frac.ofInt 2 * A * lo + B).Valid :=
    Frac.valid_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hlo) hB
  have hd_hi_v : (Frac.ofInt 2 * A * hi + B).Valid :=
    Frac.valid_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hhi) hB
  unfold minQuad1d; dsimp only
  split_ifs with h_lo h_hi
  · refine ⟨Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hlo) hlo) (Frac.valid_mul hB hlo), ?_⟩
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul hA hlo) hlo) (Frac.valid_mul hB hlo),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul]
    have hd := (Frac.nonneg_iff hd_lo_v).mp h_lo
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hlo) hB,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hd
    norm_num at hd
    have hid : (A.toReal * x ^ 2 + B.toReal * x) - (A.toReal * lo.toReal * lo.toReal + B.toReal * lo.toReal) =
        (x - lo.toReal) * (A.toReal * (x - lo.toReal) + (2 * A.toReal * lo.toReal + B.toReal)) := by ring
    have hnn := mul_nonneg (show 0 ≤ x - lo.toReal by linarith)
      (show 0 ≤ A.toReal * (x - lo.toReal) + (2 * A.toReal * lo.toReal + B.toReal) by nlinarith)
    linarith
  · refine ⟨Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hhi) hhi) (Frac.valid_mul hB hhi), ?_⟩
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul hA hhi) hhi) (Frac.valid_mul hB hhi),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul]
    have hnp : ¬(0 < (Frac.ofInt 2 * A * hi + B).toReal) := fun hp => by
      have := (Frac.pos_iff hd_hi_v).mpr hp; simp [this] at h_hi
    have hd : (Frac.ofInt 2 * A * hi + B).toReal ≤ 0 := not_lt.mp hnp
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hhi) hB,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hd
    norm_num at hd
    have hid : (A.toReal * x ^ 2 + B.toReal * x) - (A.toReal * hi.toReal * hi.toReal + B.toReal * hi.toReal) =
        (hi.toReal - x) * (A.toReal * (hi.toReal - x) - (2 * A.toReal * hi.toReal + B.toReal)) := by ring
    have hnn := mul_nonneg (show 0 ≤ hi.toReal - x by linarith)
      (show 0 ≤ A.toReal * (hi.toReal - x) - (2 * A.toReal * hi.toReal + B.toReal) by nlinarith)
    linarith
  · have hv : (⟨-(B.n * B.n) * A.d, 4 * A.n * B.d * B.d⟩ : Frac).Valid := by
      unfold Frac.Valid
      have hBd : 0 < B.d := hB
      positivity
    refine ⟨hv, ?_⟩
    have heq : (⟨-(B.n * B.n) * A.d, 4 * A.n * B.d * B.d⟩ : Frac).toReal = -(B.toReal ^ 2) / (4 * A.toReal) := by
      simp only [Frac.toReal]
      have hAn0 : (A.n : ℝ) ≠ 0 := ne_of_gt (Int.cast_pos.mpr hAn)
      have hAd0 := Frac.d_ne hA
      have hBd0 := Frac.d_ne hB
      push_cast; field_simp [hAn0, hAd0, hBd0]
    rw [heq]
    have hid : (A.toReal * x ^ 2 + B.toReal * x) - (-(B.toReal ^ 2) / (4 * A.toReal)) =
        (2 * A.toReal * x + B.toReal) ^ 2 / (4 * A.toReal) := by
      field_simp [ne_of_gt hA_pos]; ring
    have hnn : 0 ≤ (2 * A.toReal * x + B.toReal) ^ 2 / (4 * A.toReal) := by positivity
    linarith

private lemma sound_quadPosOn {A B C u v : Frac}
    (hA : A.Valid) (hB : B.Valid) (hC : C.Valid) (hu : u.Valid) (hv : v.Valid)
    {t : ℝ} (hut : u.toReal ≤ t) (htv : t ≤ v.toReal)
    (hok : quadPosOn A B C u v = true) :
    0 < A.toReal * t ^ 2 + B.toReal * t + C.toReal := by
  have hfu_v : (A * u * u + B * u + C).Valid :=
    Frac.valid_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu)) hC
  have hfv_v : (A * v * v + B * v + C).Valid :=
    Frac.valid_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hv) hv) (Frac.valid_mul hB hv)) hC
  have hfu_eq : (A * u * u + B * u + C).toReal = A.toReal * u.toReal ^ 2 + B.toReal * u.toReal + C.toReal := by
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu)) hC,
        Frac.toReal_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul]; ring
  have hfv_eq : (A * v * v + B * v + C).toReal = A.toReal * v.toReal ^ 2 + B.toReal * v.toReal + C.toReal := by
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hv) hv) (Frac.valid_mul hB hv)) hC,
        Frac.toReal_add (Frac.valid_mul (Frac.valid_mul hA hv) hv) (Frac.valid_mul hB hv),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul]; ring
  unfold quadPosOn at hok; dsimp only at hok
  split_ifs at hok with hAnp hdu hdv
  · simp only [Bool.and_eq_true] at hok
    have hA_le : A.toReal ≤ 0 := not_lt.mp fun hp => by
      have := (Frac.pos_iff hA).mpr hp; simp [this] at hAnp
    have hfu := (Frac.pos_iff hfu_v).mp hok.1; rw [hfu_eq] at hfu
    have hfv := (Frac.pos_iff hfv_v).mp hok.2; rw [hfv_eq] at hfv
    by_cases huv : u.toReal = v.toReal
    · have htu : t = u.toReal := by linarith
      rw [htu]; exact hfu
    · have huv_pos : 0 < v.toReal - u.toReal := lt_of_le_of_ne (by linarith) (fun h => huv (by linarith))
      have hid : (v.toReal - u.toReal) * (A.toReal * t ^ 2 + B.toReal * t + C.toReal) =
          (v.toReal - t) * (A.toReal * u.toReal ^ 2 + B.toReal * u.toReal + C.toReal) +
          (t - u.toReal) * (A.toReal * v.toReal ^ 2 + B.toReal * v.toReal + C.toReal) +
          (-A.toReal) * ((t - u.toReal) * (v.toReal - t)) * (v.toReal - u.toReal) := by ring
      have hconv : 0 ≤ (-A.toReal) * ((t - u.toReal) * (v.toReal - t)) * (v.toReal - u.toReal) :=
        mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))) (le_of_lt huv_pos)
      have hlin : 0 < (v.toReal - t) * (A.toReal * u.toReal ^ 2 + B.toReal * u.toReal + C.toReal) +
          (t - u.toReal) * (A.toReal * v.toReal ^ 2 + B.toReal * v.toReal + C.toReal) := by
        by_cases htu : u.toReal = t
        · rw [← htu, sub_self, zero_mul, add_zero]; exact mul_pos huv_pos hfu
        · have hpos1 : 0 < t - u.toReal := lt_of_le_of_ne (by linarith) (fun h => htu (by linarith))
          have hnn1 : 0 ≤ (v.toReal - t) * (A.toReal * u.toReal ^ 2 + B.toReal * u.toReal + C.toReal) :=
            mul_nonneg (by linarith) (le_of_lt hfu)
          have hpos2 : 0 < (t - u.toReal) * (A.toReal * v.toReal ^ 2 + B.toReal * v.toReal + C.toReal) :=
            mul_pos hpos1 hfv
          linarith
      nlinarith
  · have hAp : A.pos = true := by cases h : A.pos <;> simp_all
    have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp hAp
    have hdu_v : (Frac.ofInt 2 * A * u + B).Valid :=
      Frac.valid_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hu) hB
    have hfu := (Frac.pos_iff hfu_v).mp hok; rw [hfu_eq] at hfu
    have hdu_r := (Frac.nonneg_iff hdu_v).mp hdu
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hu) hB,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hdu_r
    norm_num at hdu_r
    have hid : (A.toReal * t ^ 2 + B.toReal * t + C.toReal) -
        (A.toReal * u.toReal ^ 2 + B.toReal * u.toReal + C.toReal) =
        (t - u.toReal) * (A.toReal * (t - u.toReal) + (2 * A.toReal * u.toReal + B.toReal)) := by ring
    have hnn := mul_nonneg (show 0 ≤ t - u.toReal by linarith)
      (show 0 ≤ A.toReal * (t - u.toReal) + (2 * A.toReal * u.toReal + B.toReal) by nlinarith)
    linarith
  · have hAp : A.pos = true := by cases h : A.pos <;> simp_all
    have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp hAp
    have hdv_v : (Frac.ofInt 2 * A * v + B).Valid :=
      Frac.valid_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hv) hB
    have hfv := (Frac.pos_iff hfv_v).mp hok; rw [hfv_eq] at hfv
    have hdv_r : (Frac.ofInt 2 * A * v + B).toReal ≤ 0 := not_lt.mp fun hp => by
      have := (Frac.pos_iff hdv_v).mpr hp; simp [this] at hdv
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hv) hB,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hdv_r
    norm_num at hdv_r
    have hid : (A.toReal * t ^ 2 + B.toReal * t + C.toReal) -
        (A.toReal * v.toReal ^ 2 + B.toReal * v.toReal + C.toReal) =
        (v.toReal - t) * (A.toReal * (v.toReal - t) - (2 * A.toReal * v.toReal + B.toReal)) := by ring
    have hnn := mul_nonneg (show 0 ≤ v.toReal - t by linarith)
      (show 0 ≤ A.toReal * (v.toReal - t) - (2 * A.toReal * v.toReal + B.toReal) by nlinarith)
    linarith
  · have hAp : A.pos = true := by cases h : A.pos <;> simp_all
    have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp hAp
    have hdisc_v : (Frac.ofInt 4 * A * C - B * B).Valid :=
      Frac.valid_sub (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 4) hA) hC) (Frac.valid_mul hB hB)
    have hdisc := (Frac.pos_iff hdisc_v).mp hok
    rw [Frac.toReal_sub (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 4) hA) hC) (Frac.valid_mul hB hB),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hdisc
    norm_num at hdisc
    have hid : 4 * A.toReal * (A.toReal * t ^ 2 + B.toReal * t + C.toReal) =
        (2 * A.toReal * t + B.toReal) ^ 2 + (4 * A.toReal * C.toReal - B.toReal * B.toReal) := by ring
    nlinarith [sq_nonneg (2 * A.toReal * t + B.toReal)]

private lemma sound_quadPosGe {A B C u : Frac}
    (hA : A.Valid) (hB : B.Valid) (hC : C.Valid) (hu : u.Valid)
    {t : ℝ} (hut : u.toReal ≤ t)
    (hok : quadPosGe A B C u = true) :
    0 < A.toReal * t ^ 2 + B.toReal * t + C.toReal := by
  unfold quadPosGe at hok; dsimp only at hok
  split_ifs at hok with hAnp hdu
  · have hAp : A.pos = true := by cases h : A.pos <;> simp_all
    have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp hAp
    have hdu_v : (Frac.ofInt 2 * A * u + B).Valid :=
      Frac.valid_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hu) hB
    have hfu_v : (A * u * u + B * u + C).Valid :=
      Frac.valid_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu)) hC
    have hfu := (Frac.pos_iff hfu_v).mp hok
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu)) hC,
        Frac.toReal_add (Frac.valid_mul (Frac.valid_mul hA hu) hu) (Frac.valid_mul hB hu),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul] at hfu
    have hdu_r := (Frac.nonneg_iff hdu_v).mp hdu
    rw [Frac.toReal_add (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hA) hu) hB,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hdu_r
    norm_num at hdu_r
    have hid : (A.toReal * t ^ 2 + B.toReal * t + C.toReal) -
        (A.toReal * u.toReal * u.toReal + B.toReal * u.toReal + C.toReal) =
        (t - u.toReal) * (A.toReal * (t - u.toReal) + (2 * A.toReal * u.toReal + B.toReal)) := by ring
    have hnn := mul_nonneg (show 0 ≤ t - u.toReal by linarith)
      (show 0 ≤ A.toReal * (t - u.toReal) + (2 * A.toReal * u.toReal + B.toReal) by nlinarith)
    linarith
  · have hAp : A.pos = true := by cases h : A.pos <;> simp_all
    have hA_pos : 0 < A.toReal := (Frac.pos_iff hA).mp hAp
    have hdisc_v : (Frac.ofInt 4 * A * C - B * B).Valid :=
      Frac.valid_sub (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 4) hA) hC) (Frac.valid_mul hB hB)
    have hdisc := (Frac.pos_iff hdisc_v).mp hok
    rw [Frac.toReal_sub (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 4) hA) hC) (Frac.valid_mul hB hB),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt] at hdisc
    norm_num at hdisc
    have hid : 4 * A.toReal * (A.toReal * t ^ 2 + B.toReal * t + C.toReal) =
        (2 * A.toReal * t + B.toReal) ^ 2 + (4 * A.toReal * C.toReal - B.toReal * B.toReal) := by ring
    nlinarith [sq_nonneg (2 * A.toReal * t + B.toReal)]

private lemma sound_besselBelow {ψ : QState 4} (hunit : IsUnitState ψ)
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (w : PauliIdx 4 → ℝ) (hw0 : w 0 = 1)
    {S1 S2w M W_lb : Frac} (hS1v : S1.Valid) (hS2v : S2w.Valid) (hMv : M.Valid) (hWv : W_lb.Valid)
    (hS1_eq : (∑ p : PauliIdx 4, w p) = S1.toReal)
    (hS2_eq : (∑ p : PauliIdx 4, (w p) ^ 2) = S2w.toReal)
    (hM_ge : M.toReal ≤ ∑ p : PauliIdx 4, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * ((innerProd ψ (pauliApply p ψ)).re) ^ 2))
    (hW_ge : W_lb.toReal ≤ wAnti w)
    (hok : besselBelow S1 S2w M W_lb = true) : False := by
  classical
  have hb := bessel2d_bound hunit hF4 w hw0
  dsimp only at hb
  unfold besselBelow at hok
  have hs16v : (S1 + Frac.ofInt 16).Valid := Frac.valid_add hS1v (Frac.valid_ofInt 16)
  have hm17v : (Frac.ofInt 17 * M).Valid := Frac.valid_mul (Frac.valid_ofInt 17) hMv
  by_cases hle : (S1 + Frac.ofInt 16).le (Frac.ofInt 17 * M) = true
  · simp only [hle, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hdiff_v : (Frac.ofInt 17 * M - (S1 + Frac.ofInt 16)).Valid := Frac.valid_sub hm17v hs16v
    have h17s2_v := Frac.valid_mul (Frac.valid_ofInt 17) hS2v
    have hs1sq_v := Frac.valid_mul hS1v hS1v
    have h2s1_v := Frac.valid_mul (Frac.valid_ofInt 2) hS1v
    have hinner_v := Frac.valid_sub (Frac.valid_sub (Frac.valid_add h17s2_v hs1sq_v) h2s1_v) (Frac.valid_ofInt 16)
    have hrhs_v := Frac.valid_sub (Frac.valid_mul (Frac.valid_ofInt 120) hinner_v) (Frac.valid_mul hdiff_v hdiff_v)
    have hlhs_v := Frac.valid_mul (Frac.valid_ofInt 255) hWv
    have hlt := (Frac.lt_iff hrhs_v hlhs_v).mp hok
    have hle_r := (Frac.le_iff hs16v hm17v).mp hle
    rw [Frac.toReal_add hS1v (Frac.valid_ofInt 16), Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt] at hle_r
    rw [Frac.toReal_sub (Frac.valid_mul (Frac.valid_ofInt 120) hinner_v) (Frac.valid_mul hdiff_v hdiff_v),
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul,
        Frac.toReal_sub (Frac.valid_sub (Frac.valid_add h17s2_v hs1sq_v) h2s1_v) (Frac.valid_ofInt 16),
        Frac.toReal_sub (Frac.valid_add h17s2_v hs1sq_v) h2s1_v,
        Frac.toReal_add h17s2_v hs1sq_v,
        Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul,
        Frac.toReal_sub hm17v hs16v, Frac.toReal_add hS1v (Frac.valid_ofInt 16), Frac.toReal_mul] at hlt
    simp only [Frac.toReal_ofInt] at hlt
    norm_num at hle_r hlt
    rw [hS1_eq, hS2_eq] at hb
    set M_act := ∑ p : PauliIdx 4, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * ((innerProd ψ (pauliApply p ψ)).re) ^ 2)
    have hsq_le : (17 * M.toReal - S1.toReal - 16) ^ 2 ≤ (17 * M_act - S1.toReal - 16) ^ 2 := by nlinarith
    nlinarith
  · simp [hle] at hok

/-! ### Section 4: Order-Statistics Context & Soundness of `checkS13`, `checkSk`, `checkMask`, `checkLeaf`, `checkTree` -/

/-- State order-statistics context for a hypothetical counterexample `pauliMoment4 4 ψ ≤ 31/16`. -/
private structure StateCtx (ψ : QState 4) where
  hunit : IsUnitState ψ
  hF4 : pauliMoment4 4 ψ ≤ 31 / 16
  hL1 : ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), |(innerProd ψ (pauliApply p ψ)).re| ≤ (601919 / 10000 : ℝ)
  hLout : ∀ L : Finset (PauliIdx 4), IsLagrangian L →
    ∑ q ∈ Finset.univ \ L, |(innerProd ψ (pauliApply q ψ)).re| ≤ (594918 / 10000 : ℝ)
  idx : Fin 255 → PauliIdx 4
  idx_inj : Function.Injective idx
  idx_ne0 : ∀ i : Fin 255, idx i ≠ 0
  idx_mono : ∀ i j : Fin 255, i ≤ j →
    |(innerProd ψ (pauliApply (idx i) ψ)).re| ≤ |(innerProd ψ (pauliApply (idx j) ψ)).re|

private noncomputable def StateCtx.c {ψ : QState 4} (_ : StateCtx ψ) (p : PauliIdx 4) : ℝ :=
  (innerProd ψ (pauliApply p ψ)).re

private noncomputable def StateCtx.x {ψ : QState 4} (ctx : StateCtx ψ) (i : Fin 255) : ℝ :=
  |ctx.c (ctx.idx i)|

private noncomputable def StateCtx.xc {ψ : QState 4} (ctx : StateCtx ψ) (j : Fin 4) : ℝ :=
  min (ctx.x ⟨13 + j.val, by omega⟩) (1 / 4)

private noncomputable def StateCtx.S2_13 {ψ : QState 4} (ctx : StateCtx ψ) : ℝ :=
  ∑ i : Fin 13, (ctx.x ⟨i.val, by omega⟩) ^ 2

private lemma card_PauliIdx4_erase_zero_nat :
    (Finset.univ.erase (0 : PauliIdx 4)).card = 255 := by
  have h : ((Finset.univ.erase (0 : PauliIdx 4)).card : ℝ) = 255 := by
    rw [card_PauliIdx_erase_zero 4]; norm_num
  exact_mod_cast h

private lemma StateCtx.x_nonneg {ψ : QState 4} (ctx : StateCtx ψ) (i : Fin 255) : 0 ≤ ctx.x i :=
  abs_nonneg _

private lemma StateCtx.sum_U_eq {ψ : QState 4} (ctx : StateCtx ψ) (g : PauliIdx 4 → ℝ) :
    ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), g p = ∑ i : Fin 255, g (ctx.idx i) := by
  classical
  have himg : Finset.image ctx.idx Finset.univ = Finset.univ.erase (0 : PauliIdx 4) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_erase.mpr ⟨ctx.idx_ne0 i, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injective _ ctx.idx_inj, Finset.card_fin, card_PauliIdx4_erase_zero_nat]
  rw [← himg, Finset.sum_image (fun a _ b _ h => ctx.idx_inj h)]

private lemma sum_fin14_eq (g : Fin 255 → ℝ) :
    ∑ i : Fin 14, g ⟨i.val, by omega⟩ = (∑ i : Fin 13, g ⟨i.val, by omega⟩) + g ⟨13, by omega⟩ := by
  rw [Fin.sum_univ_castSucc]; rfl

private lemma sum_fin15_eq (g : Fin 255 → ℝ) :
    ∑ i : Fin 15, g ⟨i.val, by omega⟩ =
      (∑ i : Fin 13, g ⟨i.val, by omega⟩) + g ⟨13, by omega⟩ + g ⟨14, by omega⟩ := by
  rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [sum_fin14_eq]

private lemma sum_fin16_eq (g : Fin 255 → ℝ) :
    ∑ i : Fin 16, g ⟨i.val, by omega⟩ =
      (∑ i : Fin 13, g ⟨i.val, by omega⟩) + g ⟨13, by omega⟩ + g ⟨14, by omega⟩ + g ⟨15, by omega⟩ := by
  rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [sum_fin15_eq]

private lemma sum_fin17_eq (g : Fin 255 → ℝ) :
    ∑ i : Fin 17, g ⟨i.val, by omega⟩ =
      (∑ i : Fin 13, g ⟨i.val, by omega⟩) + g ⟨13, by omega⟩ + g ⟨14, by omega⟩ +
      g ⟨15, by omega⟩ + g ⟨16, by omega⟩ := by
  rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [sum_fin16_eq]

private lemma fin255_tail15_card :
    (Finset.univ.filter (fun j : Fin 255 => 15 ≤ j.val)).card = 240 := by
  have hcomp : (Finset.univ.filter (fun j : Fin 255 => ¬(15 ≤ j.val))).card = 15 := by
    have hbij : Finset.univ.filter (fun j : Fin 255 => ¬(15 ≤ j.val)) =
        Finset.univ.image (fun i : Fin 15 => (⟨i.val, by omega⟩ : Fin 255)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
      · rintro ⟨i, h⟩; rw [← h]; dsimp; omega
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congr_arg Fin.val h)),
        Finset.card_fin]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 255))) (fun j => 15 ≤ j.val)
  rw [Finset.card_fin, hcomp] at htot; omega

private lemma fin255_tail_contra (f : Fin 255 → ℝ) (Tail : Finset (Fin 255))
    (j0 : Fin 255) (hj0 : j0 ∈ Tail) (hcard : Tail.card = 240)
    (hTail_gt : ∀ j ∈ Tail, (1 / 16 : ℝ) < (f j) ^ 2)
    (hsum : ∑ j : Fin 255, (f j) ^ 2 = 15) : False := by
  have hsum_tail : (15 : ℝ) < ∑ j ∈ Tail, (f j) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hj0]
    have hlt0 : (1 / 16 : ℝ) < (f j0) ^ 2 := hTail_gt j0 hj0
    have hrest : ((Tail.erase j0).card : ℝ) * (1 / 16 : ℝ) ≤ ∑ j ∈ Tail.erase j0, (f j) ^ 2 := by
      have h1 : ∑ _j ∈ Tail.erase j0, (1 / 16 : ℝ) ≤ ∑ j ∈ Tail.erase j0, (f j) ^ 2 :=
        Finset.sum_le_sum fun j hj => le_of_lt (hTail_gt j (Finset.mem_of_mem_erase hj))
      rw [Finset.sum_const, nsmul_eq_mul] at h1; exact h1
    have hcard_e : (Tail.erase j0).card = 239 := by
      rw [Finset.card_erase_of_mem hj0, hcard]
    rw [hcard_e] at hrest
    have hsum' := add_lt_add_of_lt_of_le hlt0 hrest
    have h15 : (1 / 16 : ℝ) + ((239 : Nat) : ℝ) * (1 / 16 : ℝ) = 15 := by norm_num
    rw [h15] at hsum'
    exact hsum'
  have hsub_le : ∑ j ∈ Tail, (f j) ^ 2 ≤ ∑ j : Fin 255, (f j) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  rw [hsum] at hsub_le
  exact not_lt_of_ge hsub_le hsum_tail

private lemma fin255_le_quarter_of_sum_sq (f : Fin 255 → ℝ)
    (hmono : ∀ a b : Fin 255, a ≤ b → f a ≤ f b)
    (hsum : ∑ j : Fin 255, (f j) ^ 2 = 15)
    (i : Fin 255) (hi : i.val ≤ 15) : f i ≤ 1 / 4 := by
  by_contra hgt; push Not at hgt
  let Tail := Finset.univ.filter fun j : Fin 255 => 15 ≤ j.val
  have hTail_gt : ∀ j ∈ Tail, (1 / 16 : ℝ) < (f j) ^ 2 := by
    intro j hj
    have hj15 : 15 ≤ j.val := (Finset.mem_filter.mp hj).2
    have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (le_trans hi hj15)
    have hfj : (1 / 4 : ℝ) < f j := lt_of_lt_of_le hgt (hmono i j hij)
    calc (1 / 16 : ℝ) = (1 / 4) * (1 / 4) := by norm_num
      _ < f j * f j := mul_lt_mul'' hfj hfj (by norm_num) (by norm_num)
      _ = (f j) ^ 2 := by ring
  let j0 : Fin 255 := ⟨15, by omega⟩
  have hj0 : j0 ∈ Tail := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl 15⟩
  exact fin255_tail_contra f Tail j0 hj0 fin255_tail15_card hTail_gt hsum

private lemma StateCtx.x_le_quarter {ψ : QState 4} (ctx : StateCtx ψ) (i : Fin 255) (hi : i.val ≤ 15) :
    ctx.x i ≤ 1 / 4 := by
  obtain ⟨hsum2, _⟩ := sum_sq_and_fourth_four ctx.hunit
  dsimp only at hsum2
  rw [ctx.sum_U_eq] at hsum2
  have hsum_x : ∑ j : Fin 255, (ctx.x j) ^ 2 = 15 := by
    have hcongr : ∑ j : Fin 255, (ctx.x j) ^ 2 = ∑ j : Fin 255, (ctx.c (ctx.idx j)) ^ 2 :=
      Finset.sum_congr rfl fun j _ => sq_abs _
    rw [hcongr]; exact hsum2
  exact fin255_le_quarter_of_sum_sq ctx.x ctx.idx_mono hsum_x i hi

private lemma sort_pauli4_by_abs (f : PauliIdx 4 → ℝ) :
    ∃ idx : Fin 255 → PauliIdx 4,
      Function.Injective idx ∧ (∀ i : Fin 255, idx i ≠ 0) ∧
      (∀ i j : Fin 255, i ≤ j → |f (idx i)| ≤ |f (idx j)|) := by
  classical
  let eqv := Fintype.equivFin (PauliIdx 4)
  let r : PauliIdx 4 → PauliIdx 4 → Prop := fun p q => |f p| < |f q| ∨ (|f p| = |f q| ∧ eqv p ≤ eqv q)
  let : Std.Total r := ⟨fun p q => by
    rcases lt_trichotomy |f p| |f q| with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (eqv p) (eqv q) with he | he
      · exact Or.inl (Or.inr ⟨h, he⟩)
      · exact Or.inr (Or.inr ⟨h.symm, he⟩)
    · exact Or.inr (Or.inl h)⟩
  let : IsTrans (PauliIdx 4) r := ⟨fun p q t hpq hqt => by
    rcases hpq with h1 | ⟨h1, h2⟩ <;> rcases hqt with h3 | ⟨h3, h4⟩
    · exact Or.inl (lt_trans h1 h3)
    · exact Or.inl (h3 ▸ h1)
    · exact Or.inl (h1.symm ▸ h3)
    · exact Or.inr ⟨h1.trans h3, le_trans h2 h4⟩⟩
  let : Std.Antisymm r := ⟨fun p q hpq hqp => by
    rcases hpq with h1 | ⟨h1, h2⟩ <;> rcases hqp with h3 | ⟨h3, h4⟩
    · exact absurd (lt_trans h1 h3) (lt_irrefl _)
    · exact absurd (h3 ▸ h1) (lt_irrefl _)
    · exact absurd (h1 ▸ h3) (lt_irrefl _)
    · exact eqv.injective (le_antisymm h2 h4)⟩
  let U := Finset.univ.erase (0 : PauliIdx 4)
  let L := U.sort r
  have hlen : L.length = 255 := by rw [Finset.length_sort, card_PauliIdx4_erase_zero_nat]
  have hnodup : L.Nodup := Finset.sort_nodup U r
  have hpw : L.Pairwise r := Finset.pairwise_sort U r
  let idx : Fin 255 → PauliIdx 4 := fun i => L[i.val]'(by omega)
  refine ⟨idx, ?_, ?_, ?_⟩
  · intro i j hij
    have hval : i.val = j.val := (List.Nodup.getElem_inj_iff hnodup).mp hij
    exact Fin.ext hval
  · intro i
    have hmem : idx i ∈ L := List.getElem_mem (by omega)
    exact (Finset.mem_erase.mp ((Finset.mem_sort r).mp hmem)).1
  · intro i j hij
    rcases eq_or_lt_of_le (Fin.le_iff_val_le_val.mp hij) with heq | hlt
    · have : i = j := Fin.ext heq; rw [this]
    · have hr := (List.pairwise_iff_getElem.mp hpw) i.val j.val (by omega) (by omega) hlt
      rcases hr with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h

private lemma StateCtx.extract {ψ : QState 4}
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    (hunit : IsUnitState ψ) (hF4 : pauliMoment4 4 ψ ≤ 31 / 16) :
    Nonempty (StateCtx ψ) := by
  obtain ⟨idx, hinj, hne0, hmono⟩ := sort_pauli4_by_abs (fun p => (innerProd ψ (pauliApply p ψ)).re)
  exact ⟨⟨hunit, hF4, pauli_L1_le_of_contextuality_1575 hCD hunit,
    fun L' hL' => pauli_Lout_le_of_contextuality_1575 hCD hL' hunit, idx, hinj, hne0, hmono⟩⟩

/-- Box hypothesis: clamped coordinates `(xc 0, xc 1, xc 2, xc 3)` lie in `[A_j/128, B_j/128]`
    with `0 ≤ A0 ≤ A1 ≤ A2 ≤ A3` and `B0 ≤ B1 ≤ B2 ≤ B3 ≤ 32`. -/
private structure BoxHyp {ψ : QState 4} (ctx : StateCtx ψ) (A0 A1 A2 A3 B0 B1 B2 B3 : Int) : Prop where
  hA0_nn : 0 ≤ A0
  hA01 : A0 ≤ A1
  hA12 : A1 ≤ A2
  hA23 : A2 ≤ A3
  hB01 : B0 ≤ B1
  hB12 : B1 ≤ B2
  hB23 : B2 ≤ B3
  hB3_le : B3 ≤ 32
  h0_lo : (A0 : ℝ) / 128 ≤ ctx.xc 0
  h0_hi : ctx.xc 0 ≤ (B0 : ℝ) / 128
  h1_lo : (A1 : ℝ) / 128 ≤ ctx.xc 1
  h1_hi : ctx.xc 1 ≤ (B1 : ℝ) / 128
  h2_lo : (A2 : ℝ) / 128 ≤ ctx.xc 2
  h2_hi : ctx.xc 2 ≤ (B2 : ℝ) / 128
  h3_lo : (A3 : ℝ) / 128 ≤ ctx.xc 3
  h3_hi : ctx.xc 3 ≤ (B3 : ℝ) / 128

private lemma BoxHyp.unclamp {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) :
    (B0 < 32 → ctx.x ⟨13, by omega⟩ ≤ (B0 : ℝ) / 128) ∧
    (B1 < 32 → ctx.x ⟨14, by omega⟩ ≤ (B1 : ℝ) / 128) ∧
    (B2 < 32 → ctx.x ⟨15, by omega⟩ ≤ (B2 : ℝ) / 128) ∧
    (B3 < 32 → ctx.x ⟨16, by omega⟩ ≤ (B3 : ℝ) / 128) := by
  have step : ∀ {x : ℝ} {B : Int}, min x (1 / 4) ≤ (B : ℝ) / 128 → B < 32 → x ≤ (B : ℝ) / 128 := by
    intro x B hle hB32
    have hlt4 : (B : ℝ) / 128 < 1 / 4 := by
      have : (B : ℝ) < 32 := by exact_mod_cast hB32
      linarith
    by_cases hx4 : x ≤ 1 / 4
    · rwa [min_eq_left hx4] at hle
    · rw [min_eq_right (le_of_not_ge hx4)] at hle; linarith
  exact ⟨step hb.h0_hi, step hb.h1_hi, step hb.h2_hi, step hb.h3_hi⟩

private lemma BoxHyp.x_ge_A {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) :
    (A0 : ℝ) / 128 ≤ ctx.x ⟨13, by omega⟩ ∧
    (A1 : ℝ) / 128 ≤ ctx.x ⟨14, by omega⟩ ∧
    (A2 : ℝ) / 128 ≤ ctx.x ⟨15, by omega⟩ ∧
    (A3 : ℝ) / 128 ≤ ctx.x ⟨16, by omega⟩ :=
  ⟨le_trans hb.h0_lo (min_le_left _ _), le_trans hb.h1_lo (min_le_left _ _),
   le_trans hb.h2_lo (min_le_left _ _), le_trans hb.h3_lo (min_le_left _ _)⟩

private lemma BoxHyp.x13_le_B0 {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) (i : Fin 13) :
    ctx.x ⟨i.val, by omega⟩ ≤ (B0 : ℝ) / 128 := by
  have h1 : ctx.x ⟨i.val, by omega⟩ ≤ ctx.x ⟨13, by omega⟩ :=
    ctx.idx_mono ⟨i.val, by omega⟩ ⟨13, by omega⟩ (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt i.isLt))
  have h2 : ctx.x ⟨i.val, by omega⟩ ≤ 1 / 4 := ctx.x_le_quarter ⟨i.val, by omega⟩ (show i.val ≤ 15 by omega)
  exact le_trans (le_min h1 h2) hb.h0_hi

private lemma BoxHyp.h_and_w_split {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) :
    let h_lo : ℝ :=
      min (hPoly ((A0 : ℝ) / 128)) (hPoly ((B0 : ℝ) / 128)) +
      min (hPoly ((A1 : ℝ) / 128)) (hPoly ((B1 : ℝ) / 128)) +
      min (hPoly ((A2 : ℝ) / 128)) (hPoly ((B2 : ℝ) / 128)) +
      min (hPoly ((A3 : ℝ) / 128)) (hPoly ((B3 : ℝ) / 128))
    let H_rem : ℝ := max 0 (1919 / 320000 - h_lo)
    let w_hi : ℝ :=
      wPoly ((A0 : ℝ) / 128) + wPoly ((A1 : ℝ) / 128) + wPoly ((A2 : ℝ) / 128) + wPoly ((A3 : ℝ) / 128)
    (∑ i : Fin 13, hPoly (ctx.x ⟨i.val, by omega⟩)) +
      (∑ i ∈ Finset.univ.filter (fun j : Fin 255 => 17 ≤ j.val), hPoly (ctx.x i)) ≤ H_rem ∧
    (∀ (C : ℝ), 0 < A3 →
      C = 16 * (1 - 4 * ((A3 : ℝ) / 128)) * (1 + (4 / 3) * ((A3 : ℝ) / 128)) /
            (((A3 : ℝ) / 128) * (((A3 : ℝ) / 128) + 1 / 2)) →
      ∑ i : Fin 13, ((1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + C * hPoly (ctx.x ⟨i.val, by omega⟩)) ≤
        13 - 388592 / 30000 + w_hi + C * H_rem) := by
  classical
  intro h_lo H_rem w_hi
  obtain ⟨hh_glob, hw_glob⟩ := global_h_and_w_bounds ctx.hunit ctx.hL1 ctx.hF4
  dsimp only at hh_glob hw_glob
  rw [ctx.sum_U_eq] at hh_glob hw_glob
  -- Partition `Fin 255` into `I0 = {i < 13}`, `I1 = {13, 14, 15, 16}`, `I2 = {17 ≤ i}`!
  let I0 := Finset.univ.filter fun j : Fin 255 => j.val < 13
  let I1 : Finset (Fin 255) := {⟨13, by omega⟩, ⟨14, by omega⟩, ⟨15, by omega⟩, ⟨16, by omega⟩}
  let I2 := Finset.univ.filter fun j : Fin 255 => 17 ≤ j.val
  have hpart : ∀ g : Fin 255 → ℝ,
      ∑ j : Fin 255, g j = (∑ i : Fin 13, g ⟨i.val, by omega⟩) +
        (g ⟨13, by omega⟩ + g ⟨14, by omega⟩ + g ⟨15, by omega⟩ + g ⟨16, by omega⟩) +
        (∑ j ∈ I2, g j) := by
    intro g
    have hd01 : Disjoint I0 I1 := by
      rw [Finset.disjoint_left]; intro j hj0 hj1
      have hlt : j.val < 13 := (Finset.mem_filter.mp hj0).2
      simp only [I1, Finset.mem_insert, Finset.mem_singleton] at hj1
      rcases hj1 with rfl | rfl | rfl | rfl <;> (dsimp at hlt; omega)
    have hd012 : Disjoint (I0 ∪ I1) I2 := by
      rw [Finset.disjoint_left]; intro j hj01 hj2
      have hge : 17 ≤ j.val := (Finset.mem_filter.mp hj2).2
      rcases Finset.mem_union.mp hj01 with hj0 | hj1
      · have hlt : j.val < 13 := (Finset.mem_filter.mp hj0).2; omega
      · simp only [I1, Finset.mem_insert, Finset.mem_singleton] at hj1
        rcases hj1 with rfl | rfl | rfl | rfl <;> (dsimp at hge; omega)
    have hun : I0 ∪ I1 ∪ I2 = Finset.univ := by
      ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, I0, I1, I2,
        Finset.mem_insert, Finset.mem_singleton, iff_true]
      by_cases h13 : j.val < 13
      · exact Or.inl (Or.inl h13)
      · by_cases h17 : 17 ≤ j.val
        · exact Or.inr h17
        · left; right
          have hcases : j.val = 13 ∨ j.val = 14 ∨ j.val = 15 ∨ j.val = 16 := by omega
          rcases hcases with h | h | h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
          · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
          · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    have h0 : ∑ j ∈ I0, g j = ∑ i : Fin 13, g ⟨i.val, by omega⟩ := by
      refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin 13)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
      · intro i _; exact ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
      · intro _ _; rfl
    have h1 : ∑ j ∈ I1, g j = g ⟨13, by omega⟩ + g ⟨14, by omega⟩ + g ⟨15, by omega⟩ + g ⟨16, by omega⟩ := by
      simp only [I1, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
        Fin.mk.injEq, Nat.reduceEqDiff, or_self, not_false_eq_true]
      ring
    conv_lhs => rw [← hun]
    rw [Finset.sum_union hd012, Finset.sum_union hd01, h0, h1]
  have h_pt : ∀ {y : ℝ} {A B : Int}, 0 ≤ A → B ≤ 32 →
      (A : ℝ) / 128 ≤ min y (1 / 4) → min y (1 / 4) ≤ (B : ℝ) / 128 →
      min (hPoly ((A : ℝ) / 128)) (hPoly ((B : ℝ) / 128)) ≤ hPoly y := by
    intro y A B hAnn hB32 hlo hhi
    have hA_nn : (0 : ℝ) ≤ (A : ℝ) / 128 := by
      have : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAnn
      linarith
    have hB_4 : (B : ℝ) / 128 ≤ 1 / 4 := by
      have : (B : ℝ) ≤ 32 := by exact_mod_cast hB32
      linarith
    by_cases hy4 : y ≤ 1 / 4
    · rw [min_eq_left hy4] at hlo hhi
      exact hPoly_ge_min_endpoints hA_nn hlo hhi hB_4
    · push Not at hy4
      rw [min_eq_right (le_of_lt hy4)] at hhi
      have hB4 : (B : ℝ) / 128 = 1 / 4 := le_antisymm hB_4 hhi
      have hmin0 : min (hPoly ((A : ℝ) / 128)) (hPoly ((B : ℝ) / 128)) = 0 := by
        rw [hB4, show hPoly (1 / 4) = 0 by simp [hPoly]]
        exact min_eq_right (hPoly_nonneg hA_nn)
      rw [hmin0]; exact hPoly_nonneg (by linarith)
  have hh_mid : h_lo ≤ hPoly (ctx.x ⟨13, by omega⟩) + hPoly (ctx.x ⟨14, by omega⟩) +
      hPoly (ctx.x ⟨15, by omega⟩) + hPoly (ctx.x ⟨16, by omega⟩) := by
    have h0 : min (hPoly ((A0 : ℝ) / 128)) (hPoly ((B0 : ℝ) / 128)) ≤ hPoly (ctx.x ⟨13, by omega⟩) :=
      h_pt hb.hA0_nn (le_trans hb.hB01 (le_trans hb.hB12 (le_trans hb.hB23 hb.hB3_le))) hb.h0_lo hb.h0_hi
    have h1 : min (hPoly ((A1 : ℝ) / 128)) (hPoly ((B1 : ℝ) / 128)) ≤ hPoly (ctx.x ⟨14, by omega⟩) :=
      h_pt (le_trans hb.hA0_nn hb.hA01) (le_trans hb.hB12 (le_trans hb.hB23 hb.hB3_le)) hb.h1_lo hb.h1_hi
    have h2 : min (hPoly ((A2 : ℝ) / 128)) (hPoly ((B2 : ℝ) / 128)) ≤ hPoly (ctx.x ⟨15, by omega⟩) :=
      h_pt (le_trans hb.hA0_nn (le_trans hb.hA01 hb.hA12)) (le_trans hb.hB23 hb.hB3_le) hb.h2_lo hb.h2_hi
    have h3 : min (hPoly ((A3 : ℝ) / 128)) (hPoly ((B3 : ℝ) / 128)) ≤ hPoly (ctx.x ⟨16, by omega⟩) :=
      h_pt (le_trans hb.hA0_nn (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23))) hb.hB3_le hb.h3_lo hb.h3_hi
    dsimp only [h_lo]; linarith
  have hh_rem : (∑ i : Fin 13, hPoly (ctx.x ⟨i.val, by omega⟩)) + ∑ j ∈ I2, hPoly (ctx.x j) ≤ H_rem := by
    have hp := hpart (fun j => hPoly (ctx.x j))
    have hle : (∑ i : Fin 13, hPoly (ctx.x ⟨i.val, by omega⟩)) + ∑ j ∈ I2, hPoly (ctx.x j) ≤ 1919 / 320000 - h_lo := by
      change (∑ j : Fin 255, hPoly (ctx.x j)) ≤ 1919 / 320000 at hh_glob
      linarith
    exact le_trans hle (le_max_right _ _)
  refine ⟨hh_rem, fun C hA3_pos hC => ?_⟩
  have hA3_r : (0 : ℝ) < (A3 : ℝ) / 128 := by
    have : (0 : ℝ) < (A3 : ℝ) := Int.cast_pos.mpr hA3_pos; linarith
  have hA3_4 : (A3 : ℝ) / 128 ≤ 1 / 4 := by
    have : (A3 : ℝ) / 128 ≤ 1 / 4 := le_trans hb.h3_lo (min_le_right _ _)
    exact this
  have hC_nn : 0 ≤ C := by
    rw [hC]
    have h1 : (0 : ℝ) ≤ 1 - 4 * ((A3 : ℝ) / 128) := by linarith
    have h2 : (0 : ℝ) ≤ 1 + (4 / 3) * ((A3 : ℝ) / 128) := by linarith
    have h3 : (0 : ℝ) < ((A3 : ℝ) / 128) * (((A3 : ℝ) / 128) + 1 / 2) := by positivity
    positivity
  have htail_w : ∑ j ∈ I2, wPoly (ctx.x j) ≤ C * ∑ j ∈ I2, hPoly (ctx.x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj17 : 17 ≤ j.val := (Finset.mem_filter.mp hj).2
    have hj_ge : (A3 : ℝ) / 128 ≤ ctx.x j :=
      le_trans hb.x_ge_A.2.2.2 (ctx.idx_mono ⟨16, by omega⟩ j (Fin.le_iff_val_le_val.mpr (show 16 ≤ j.val by omega)))
    have hle := wPoly_le_c_mul_hPoly hA3_r hA3_4 hj_ge
    dsimp only at hle; rw [← hC] at hle; exact hle
  have hmid_w : wPoly (ctx.x ⟨13, by omega⟩) + wPoly (ctx.x ⟨14, by omega⟩) +
      wPoly (ctx.x ⟨15, by omega⟩) + wPoly (ctx.x ⟨16, by omega⟩) ≤ w_hi := by
    have hge := hb.x_ge_A
    have h0 := wPoly_anti (show (0 : ℝ) ≤ (A0 : ℝ) / 128 by have : (0 : ℝ) ≤ (A0 : ℝ) := (by exact_mod_cast hb.hA0_nn); linarith) hge.1
    have h1 := wPoly_anti (show (0 : ℝ) ≤ (A1 : ℝ) / 128 by have : (0 : ℝ) ≤ (A1 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn hb.hA01); linarith) hge.2.1
    have h2 := wPoly_anti (show (0 : ℝ) ≤ (A2 : ℝ) / 128 by have : (0 : ℝ) ≤ (A2 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn (le_trans hb.hA01 hb.hA12)); linarith) hge.2.2.1
    have h3 := wPoly_anti (le_of_lt hA3_r) hge.2.2.2
    dsimp only [w_hi]; linarith
  have hwp := hpart (fun j => wPoly (ctx.x j))
  change (388592 / 30000 : ℝ) ≤ ∑ j : Fin 255, wPoly (ctx.x j) at hw_glob
  have hsum_13 : ∑ i : Fin 13, ((1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + C * hPoly (ctx.x ⟨i.val, by omega⟩)) =
      13 - (∑ i : Fin 13, wPoly (ctx.x ⟨i.val, by omega⟩)) + C * (∑ i : Fin 13, hPoly (ctx.x ⟨i.val, by omega⟩)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]; norm_num
  rw [hsum_13]
  have hC_rem := mul_le_mul_of_nonneg_left hh_rem hC_nn
  linarith

private lemma bool_and3_false {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : ¬ (P ∧ Q ∧ R)) : (decide P && decide Q && decide R) = false := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> simp_all

private lemma bool_and4_false {P Q R S : Prop} [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (h : ¬ (P ∧ Q ∧ R ∧ S)) : (decide P && decide Q && decide R && decide S) = false := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> by_cases hs : S <;> simp_all

set_option maxHeartbeats 1600000 in
private lemma sound_checkS13 {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) {mode xcap s13n : Nat}
    (hok : checkS13 A0 A1 A2 A3 B0 B1 B2 B3 mode xcap s13n = true) :
    ctx.S2_13 ≤ ((s13n : ℝ) / 1000000) := by
  classical
  have h128 : (0 : Int) < 128 := by norm_num
  have h4096 : (0 : Int) < 4096 := by norm_num
  have hs13v : (⟨s13n, 1000000⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have hs13_eq : (⟨s13n, 1000000⟩ : Frac).toReal = (s13n : ℝ) / 1000000 := by
    simp [Frac.toReal]
  have hh0v := Frac.valid_min (Frac.valid_hFrac (n := A0) h128) (Frac.valid_hFrac (n := B0) h128)
  have hh1v := Frac.valid_min (Frac.valid_hFrac (n := A1) h128) (Frac.valid_hFrac (n := B1) h128)
  have hh2v := Frac.valid_min (Frac.valid_hFrac (n := A2) h128) (Frac.valid_hFrac (n := B2) h128)
  have hh3v := Frac.valid_min (Frac.valid_hFrac (n := A3) h128) (Frac.valid_hFrac (n := B3) h128)
  have hhlov := Frac.valid_add (Frac.valid_add (Frac.valid_add hh0v hh1v) hh2v) hh3v
  have hHmaxv : H_MAX.Valid := valid_H_MAX
  have hWminv : W_MIN.Valid := valid_W_MIN
  have hHremv := Frac.valid_max (Frac.valid_ofInt 0) (Frac.valid_sub hHmaxv hhlov)
  have hwhiv := Frac.valid_add (Frac.valid_add (Frac.valid_add
    (Frac.valid_wFrac (n := A0) h128) (Frac.valid_wFrac (n := A1) h128))
    (Frac.valid_wFrac (n := A2) h128)) (Frac.valid_wFrac (n := A3) h128)
  let h_lo_f := Frac.min (hFrac A0 128) (hFrac B0 128) + Frac.min (hFrac A1 128) (hFrac B1 128) +
    Frac.min (hFrac A2 128) (hFrac B2 128) + Frac.min (hFrac A3 128) (hFrac B3 128)
  let H_rem_f := Frac.max (Frac.ofInt 0) (H_MAX - h_lo_f)
  let w_hi_f := wFrac A0 128 + wFrac A1 128 + wFrac A2 128 + wFrac A3 128
  have hhlo_r : h_lo_f.toReal =
      min (hPoly ((A0 : ℝ) / 128)) (hPoly ((B0 : ℝ) / 128)) +
      min (hPoly ((A1 : ℝ) / 128)) (hPoly ((B1 : ℝ) / 128)) +
      min (hPoly ((A2 : ℝ) / 128)) (hPoly ((B2 : ℝ) / 128)) +
      min (hPoly ((A3 : ℝ) / 128)) (hPoly ((B3 : ℝ) / 128)) := by
    simp only [h_lo_f]
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_add hh0v hh1v) hh2v) hh3v,
        Frac.toReal_add (Frac.valid_add hh0v hh1v) hh2v,
        Frac.toReal_add hh0v hh1v,
        Frac.toReal_min (Frac.valid_hFrac h128) (Frac.valid_hFrac h128),
        Frac.toReal_min (Frac.valid_hFrac h128) (Frac.valid_hFrac h128),
        Frac.toReal_min (Frac.valid_hFrac h128) (Frac.valid_hFrac h128),
        Frac.toReal_min (Frac.valid_hFrac h128) (Frac.valid_hFrac h128),
        Frac.toReal_hFrac h128, Frac.toReal_hFrac h128, Frac.toReal_hFrac h128, Frac.toReal_hFrac h128,
        Frac.toReal_hFrac h128, Frac.toReal_hFrac h128, Frac.toReal_hFrac h128, Frac.toReal_hFrac h128]
    norm_num
  have hHrem_r : H_rem_f.toReal = max 0 (1919 / 320000 - h_lo_f.toReal) := by
    have hHmax_r : H_MAX.toReal = 1919 / 320000 := by simp [H_MAX, Frac.toReal]
    simp only [H_rem_f]
    rw [Frac.toReal_max (Frac.valid_ofInt 0) (Frac.valid_sub hHmaxv hhlov),
        Frac.toReal_ofInt, Frac.toReal_sub hHmaxv hhlov, hHmax_r, Int.cast_zero]
  have hwhi_r : w_hi_f.toReal =
      wPoly ((A0 : ℝ) / 128) + wPoly ((A1 : ℝ) / 128) + wPoly ((A2 : ℝ) / 128) + wPoly ((A3 : ℝ) / 128) := by
    simp only [w_hi_f]
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_add (Frac.valid_wFrac h128) (Frac.valid_wFrac h128)) (Frac.valid_wFrac h128)) (Frac.valid_wFrac h128),
        Frac.toReal_add (Frac.valid_add (Frac.valid_wFrac h128) (Frac.valid_wFrac h128)) (Frac.valid_wFrac h128),
        Frac.toReal_add (Frac.valid_wFrac h128) (Frac.valid_wFrac h128),
        Frac.toReal_wFrac h128, Frac.toReal_wFrac h128, Frac.toReal_wFrac h128, Frac.toReal_wFrac h128]
    norm_num
  obtain ⟨hh_rem_s, hjoint_s⟩ := hb.h_and_w_split
  rw [← hhlo_r, ← hHrem_r] at hh_rem_s hjoint_s
  rw [← hwhi_r] at hjoint_s
  have hh13_le : ∑ i : Fin 13, hPoly (ctx.x ⟨i.val, by omega⟩) ≤ H_rem_f.toReal := by
    have hnn : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin 255 => 17 ≤ j.val), hPoly (ctx.x j) :=
      Finset.sum_nonneg fun j _ => hPoly_nonneg (abs_nonneg _)
    linarith
  have hB0_le32 : B0 ≤ 32 := le_trans hb.hB01 (le_trans hb.hB12 (le_trans hb.hB23 hb.hB3_le))
  have hB0_nn : 0 ≤ B0 := by
    have h1 : (A0 : ℝ) / 128 ≤ (B0 : ℝ) / 128 := le_trans hb.h0_lo hb.h0_hi
    have h2 : A0 ≤ B0 := by exact_mod_cast (show (A0 : ℝ) ≤ (B0 : ℝ) by linarith)
    exact le_trans hb.hA0_nn h2
  -- Common joint helper: if `0 < A3`, `0 < xc ≤ 1/4`, `∀ i : Fin 13, x_i ≤ xc`, `0 < denom`, and `xc² * B_joint ≤ s13 * denom`!
  have joint_finish : ∀ (xc : ℝ), 0 < A3 → 0 < xc → xc ≤ 1 / 4 →
      (∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ xc) →
      let C := (cFrac A3).toReal
      let B_joint := 13 - 388592 / 30000 + w_hi_f.toReal + C * H_rem_f.toReal
      let denom := (1 - wPoly xc) + C * hPoly xc
      0 < denom → xc ^ 2 * B_joint ≤ ((s13n : ℝ) / 1000000) * denom →
      ctx.S2_13 ≤ ((s13n : ℝ) / 1000000) := by
    intro xc hA3 hxc_pos hxc4 hxle C B_joint denom hden_pos hle
    have hC_nn : 0 ≤ C := by
      simp only [C, Frac.toReal_cFrac hA3]
      have h1 : (A3 : ℝ) / 128 ≤ 1 / 4 := le_trans hb.h3_lo (min_le_right _ _)
      have h2 : (0 : ℝ) < (A3 : ℝ) / 128 := by
        have : (0 : ℝ) < (A3 : ℝ) := Int.cast_pos.mpr hA3; linarith
      have h3 : (0 : ℝ) ≤ 1 - 4 * ((A3 : ℝ) / 128) := by linarith
      positivity
    have hsum_le : ctx.S2_13 * denom ≤ xc ^ 2 * B_joint := by
      have hpt : ∀ i : Fin 13, (ctx.x ⟨i.val, by omega⟩) ^ 2 * denom ≤
          xc ^ 2 * ((1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + C * hPoly (ctx.x ⟨i.val, by omega⟩)) :=
        fun i => sq_le_endpoint_joint hxc_pos hxc4 (abs_nonneg _) (hxle i) hC_nn
      have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
      rw [← Finset.sum_mul, ← Finset.mul_sum] at hs
      have hbj := hjoint_s C hA3 (Frac.toReal_cFrac hA3)
      exact le_trans hs (mul_le_mul_of_nonneg_left hbj (sq_nonneg xc))
    exact le_of_mul_le_mul_right (le_trans hsum_le hle) hden_pos
  have bjoint_nonpos_finish : ∀ (hA3 : 0 < A3),
      13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal ≤ 0 →
      0 ≤ (s13n : ℝ) / 1000000 → ctx.S2_13 ≤ (s13n : ℝ) / 1000000 := by
    intro hA3 hbj_le hs_nn
    have hC_nn : 0 ≤ (cFrac A3).toReal := by
      rw [Frac.toReal_cFrac hA3]
      have h1 : (A3 : ℝ) / 128 ≤ 1 / 4 := le_trans hb.h3_lo (min_le_right _ _)
      have h2 : (0 : ℝ) < (A3 : ℝ) / 128 := by
        have : (0 : ℝ) < (A3 : ℝ) := Int.cast_pos.mpr hA3; linarith
      have h3 : (0 : ℝ) ≤ 1 - 4 * ((A3 : ℝ) / 128) := by linarith
      positivity
    have hbj := hjoint_s (cFrac A3).toReal hA3 (Frac.toReal_cFrac hA3)
    have hzero : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ = 0 := by
      intro i
      by_contra hne
      have hpos : 0 < ctx.x ⟨i.val, by omega⟩ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      have hxi4 : ctx.x ⟨i.val, by omega⟩ ≤ 1 / 4 := ctx.x_le_quarter ⟨i.val, by omega⟩ (show i.val ≤ 15 by omega)
      have hw_lt : wPoly (ctx.x ⟨i.val, by omega⟩) < 1 := by
        have := wPoly_strictAnti (le_refl 0) hpos hxi4; simp [wPoly] at this; exact this
      have hterm_pos : 0 < (1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨i.val, by omega⟩) := by
        have : 0 ≤ (cFrac A3).toReal * hPoly (ctx.x ⟨i.val, by omega⟩) := mul_nonneg hC_nn (hPoly_nonneg (abs_nonneg _))
        linarith
      have hsum_ge : (1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨i.val, by omega⟩) ≤
          ∑ j : Fin 13, ((1 - wPoly (ctx.x ⟨j.val, by omega⟩)) +
            (cFrac A3).toReal * hPoly (ctx.x ⟨j.val, by omega⟩)) :=
        Finset.single_le_sum (f := fun j : Fin 13 =>
            (1 - wPoly (ctx.x ⟨j.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨j.val, by omega⟩))
          (fun j _ => by
            have hw1 : wPoly (ctx.x ⟨j.val, by omega⟩) ≤ 1 := by
              have := wPoly_anti (le_refl 0) (ctx.x_nonneg ⟨j.val, by omega⟩); simp [wPoly] at this; exact this
            have hh := mul_nonneg hC_nn (hPoly_nonneg (ctx.x_nonneg ⟨j.val, by omega⟩))
            linarith) (Finset.mem_univ i)
      linarith
    have hS0 : ctx.S2_13 = 0 := Finset.sum_eq_zero fun i _ => by rw [hzero i]; norm_num
    rw [hS0]; exact hs_nn
  have hWmin_r : W_MIN.toReal = 388592 / 30000 := by simp [W_MIN, Frac.toReal]
  have hx13_4 : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ 1 / 4 :=
    fun i => ctx.x_le_quarter ⟨i.val, by omega⟩ (show i.val ≤ 15 by omega)
  have hC_nn_of : 0 < A3 → 0 ≤ (cFrac A3).toReal := fun hA3 => by
    rw [Frac.toReal_cFrac hA3]
    have h1 : (A3 : ℝ) / 128 ≤ 1 / 4 := le_trans hb.h3_lo (min_le_right _ _)
    have h2 : (0 : ℝ) < (A3 : ℝ) / 128 := by
      have : (0 : ℝ) < (A3 : ℝ) := Int.cast_pos.mpr hA3; linarith
    have h3 : (0 : ℝ) ≤ 1 - 4 * ((A3 : ℝ) / 128) := by linarith
    positivity
  have hsingle_joint : ∀ (hA3 : 0 < A3) (i : Fin 13),
      (1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨i.val, by omega⟩) ≤
      13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal := fun hA3 i => by
    have hC_nn := hC_nn_of hA3
    have hbj := hjoint_s (cFrac A3).toReal hA3 (Frac.toReal_cFrac hA3)
    have hterm_le : (1 - wPoly (ctx.x ⟨i.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨i.val, by omega⟩) ≤
        ∑ j : Fin 13, ((1 - wPoly (ctx.x ⟨j.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨j.val, by omega⟩)) :=
      Finset.single_le_sum
        (f := fun j : Fin 13 => (1 - wPoly (ctx.x ⟨j.val, by omega⟩)) + (cFrac A3).toReal * hPoly (ctx.x ⟨j.val, by omega⟩))
        (fun j _ => by
          have hw1 : wPoly (ctx.x ⟨j.val, by omega⟩) ≤ 1 := by
            have := wPoly_anti (le_refl 0) (ctx.x_nonneg ⟨j.val, by omega⟩); simp [wPoly] at this; exact this
          have hh := mul_nonneg hC_nn (hPoly_nonneg (ctx.x_nonneg ⟨j.val, by omega⟩))
          linarith) (Finset.mem_univ i)
    linarith
  have hx_le_368_of_ok09 : ∀ (hA3 : 0 < A3),
      (decide (B0 * 32 ≤ 368) || (Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f).le (omwFrac 368 4096)) = true →
      ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ 368 / 4096 := fun hA3 hok09 i => by
    have hCv := Frac.valid_cFrac hA3
    have hBjv := Frac.valid_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv)
    rcases Bool.or_eq_true_iff.mp hok09 with hB368 | hBj368
    · have h1 : (B0 : ℝ) * 32 ≤ 368 := by exact_mod_cast (of_decide_eq_true hB368)
      have h2 := hb.x13_le_B0 i; linarith
    · have h1 := (Frac.le_iff hBjv (Frac.valid_omwFrac (n := 368) h4096)).mp hBj368
      rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv),
          Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv,
          Frac.toReal_sub (Frac.valid_ofInt 13) hWminv, Frac.toReal_ofInt, Frac.toReal_mul, hWmin_r,
          Frac.toReal_omwFrac h4096] at h1
      simp only [Int.cast_ofNat] at h1
      by_contra hgt; push Not at hgt
      have hs := hsingle_joint hA3 i
      have hh_nn := mul_nonneg (hC_nn_of hA3) (hPoly_nonneg (ctx.x_nonneg ⟨i.val, by omega⟩))
      have hw_lt := wPoly_strictAnti (by norm_num) hgt (hx13_4 i)
      linarith
  unfold checkS13 at hok
  dsimp only at hok
  match mode with
  | 0 =>
    have hv0 : (⟨13 * B0 * B0, 16384⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
    have hle := (Frac.le_iff hv0 hs13v).mp hok
    rw [hs13_eq] at hle
    have hsum : ctx.S2_13 ≤ 13 * ((B0 : ℝ) / 128) ^ 2 := by
      calc ctx.S2_13 ≤ ∑ _i : Fin 13, ((B0 : ℝ) / 128) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hb.x13_le_B0 i) 2
        _ = 13 * ((B0 : ℝ) / 128) ^ 2 := by simp
    simp only [Frac.toReal] at hle; push_cast at hle; linarith
  | 1 =>
    by_cases hB0 : B0 < 32
    · simp only [hB0, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hok : (Frac.ofInt (B0 * 16384) * H_rem_f).le
          (Frac.ofInt ((32 - B0) * (32 - B0) * (64 + B0)) * ⟨s13n, 1000000⟩) = true := hok
      have hlv := Frac.valid_mul (Frac.valid_ofInt (B0 * 16384)) hHremv
      have hrv := Frac.valid_mul (Frac.valid_ofInt ((32 - B0) * (32 - B0) * (64 + B0))) hs13v
      have hle := (Frac.le_iff hlv hrv).mp hok
      rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt, hs13_eq] at hle
      push_cast at hle
      have hden_pos : (0 : ℝ) < (32 - (B0 : ℝ)) * (32 - (B0 : ℝ)) * (64 + (B0 : ℝ)) := by
        have h1 : (B0 : ℝ) < 32 := by exact_mod_cast hB0
        have h2 : (0 : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast hB0_nn
        positivity
      have hsum : ctx.S2_13 * ((1 / 4 - (B0 : ℝ) / 128) ^ 2 * (1 / 2 + (B0 : ℝ) / 128)) ≤
          ((B0 : ℝ) / 128) * H_rem_f.toReal := by
        have hpt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          sq_le_pureH (ctx.x_nonneg _) (hb.x13_le_B0 i) (by have : (B0 : ℝ) < 32 := (by exact_mod_cast hB0); linarith)
        rw [← Finset.sum_mul, ← Finset.mul_sum] at hpt
        have hB0_r : (0 : ℝ) ≤ (B0 : ℝ) / 128 := by
          have : (0 : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast hB0_nn
          linarith
        exact le_trans hpt (mul_le_mul_of_nonneg_left hh13_le hB0_r)
      have hsc : ((1 / 4 - (B0 : ℝ) / 128) ^ 2 * (1 / 2 + (B0 : ℝ) / 128)) * 2097152 =
          (32 - (B0 : ℝ)) * (32 - (B0 : ℝ)) * (64 + (B0 : ℝ)) := by ring
      have hmul := mul_le_mul_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2097152)
      have hlhs : ctx.S2_13 * ((1 / 4 - (B0 : ℝ) / 128) ^ 2 * (1 / 2 + (B0 : ℝ) / 128)) * 2097152 =
          ctx.S2_13 * ((32 - (B0 : ℝ)) * (32 - (B0 : ℝ)) * (64 + (B0 : ℝ))) := by rw [← hsc]; ring
      have hrhs : ((B0 : ℝ) / 128) * H_rem_f.toReal * 2097152 = ((B0 : ℝ) * 16384) * H_rem_f.toReal := by ring
      rw [hlhs, hrhs] at hmul
      rw [mul_comm ((32 - (B0 : ℝ)) * (32 - (B0 : ℝ)) * (64 + (B0 : ℝ)))] at hle
      exact le_of_mul_le_mul_right (le_trans hmul hle) hden_pos
    · simp [hB0] at hok
  | 7 =>
    by_cases hB3 : B3 < 32
    · simp only [hB3, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have ha2v : (⟨A0 * A0 + A1 * A1 + A2 * A2 + A3 * A3, 16384⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
      have hlv := Frac.valid_mul (Frac.valid_ofInt (B3 * 16384)) hHmaxv
      have hrv := Frac.valid_mul (Frac.valid_ofInt ((32 - B3) * (32 - B3) * (64 + B3))) (Frac.valid_add hs13v ha2v)
      have hle := (Frac.le_iff hlv hrv).mp hok
      rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
          Frac.toReal_add hs13v ha2v, hs13_eq] at hle
      simp only [H_MAX, Frac.toReal] at hle; push_cast at hle
      have hB3_nn : 0 ≤ B3 := le_trans hB0_nn (le_trans hb.hB01 (le_trans hb.hB12 hb.hB23))
      have hden_pos : (0 : ℝ) < (32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)) := by
        have h1 : (B3 : ℝ) < 32 := by exact_mod_cast hB3
        have h2 : (0 : ℝ) ≤ (B3 : ℝ) := by exact_mod_cast hB3_nn
        positivity
      have hx16_le : ctx.x ⟨16, by omega⟩ ≤ (B3 : ℝ) / 128 := hb.unclamp.2.2.2 hB3
      have h17_le : ∀ i : Fin 17, ctx.x ⟨i.val, by omega⟩ ≤ (B3 : ℝ) / 128 := fun i =>
        le_trans (ctx.idx_mono ⟨i.val, by omega⟩ ⟨16, by omega⟩ (Fin.le_iff_val_le_val.mpr (show i.val ≤ 16 by omega))) hx16_le
      obtain ⟨hh_glob, _⟩ := global_h_and_w_bounds ctx.hunit ctx.hL1 ctx.hF4
      dsimp only at hh_glob; rw [ctx.sum_U_eq] at hh_glob
      have h17_h : ∑ i : Fin 17, hPoly (ctx.x ⟨i.val, by omega⟩) ≤ 1919 / 320000 := by
        let S17 := Finset.univ.filter fun j : Fin 255 => j.val < 17
        have h1 : ∑ i : Fin 17, hPoly (ctx.x ⟨i.val, by omega⟩) = ∑ j ∈ S17, hPoly (ctx.x j) := by
          refine Finset.sum_bij (fun i _ => (⟨i.val, by omega⟩ : Fin 255)) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
          · intro a _ b _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
          · intro j hj; exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
        rw [h1]
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hPoly_nonneg (abs_nonneg _)) hh_glob
      have hsum17 : (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) *
          ((1 / 4 - (B3 : ℝ) / 128) ^ 2 * (1 / 2 + (B3 : ℝ) / 128)) ≤ ((B3 : ℝ) / 128) * (1919 / 320000) := by
        have hpt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          sq_le_pureH (ctx.x_nonneg _) (h17_le i) (by have : (B3 : ℝ) < 32 := (by exact_mod_cast hB3); linarith)
        rw [← Finset.sum_mul, ← Finset.mul_sum] at hpt
        have hB3_r : (0 : ℝ) ≤ (B3 : ℝ) / 128 := by
          have : (0 : ℝ) ≤ (B3 : ℝ) := by exact_mod_cast hB3_nn
          linarith
        exact le_trans hpt (mul_le_mul_of_nonneg_left h17_h hB3_r)
      have h17_split : ∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2 =
          ctx.S2_13 + (ctx.x ⟨13, by omega⟩) ^ 2 + (ctx.x ⟨14, by omega⟩) ^ 2 +
          (ctx.x ⟨15, by omega⟩) ^ 2 + (ctx.x ⟨16, by omega⟩) ^ 2 :=
        sum_fin17_eq (fun i => (ctx.x i) ^ 2)
      have hge := hb.x_ge_A
      have ha_sq : ((A0 : ℝ) ^ 2 + (A1 : ℝ) ^ 2 + (A2 : ℝ) ^ 2 + (A3 : ℝ) ^ 2) / 16384 ≤
          (ctx.x ⟨13, by omega⟩) ^ 2 + (ctx.x ⟨14, by omega⟩) ^ 2 +
          (ctx.x ⟨15, by omega⟩) ^ 2 + (ctx.x ⟨16, by omega⟩) ^ 2 := by
        have s0 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A0 : ℝ) / 128 by have : (0 : ℝ) ≤ (A0 : ℝ) := (by exact_mod_cast hb.hA0_nn); linarith) hge.1 2
        have s1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A1 : ℝ) / 128 by have : (0 : ℝ) ≤ (A1 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn hb.hA01); linarith) hge.2.1 2
        have s2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A2 : ℝ) / 128 by have : (0 : ℝ) ≤ (A2 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn (le_trans hb.hA01 hb.hA12)); linarith) hge.2.2.1 2
        have s3 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A3 : ℝ) / 128 by have : (0 : ℝ) ≤ (A3 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23))); linarith) hge.2.2.2 2
        linarith
      have hsc : ((1 / 4 - (B3 : ℝ) / 128) ^ 2 * (1 / 2 + (B3 : ℝ) / 128)) * 2097152 =
          (32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)) := by ring
      have hmul := mul_le_mul_of_nonneg_right hsum17 (by norm_num : (0 : ℝ) ≤ 2097152)
      have hlhs : (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) *
          ((1 / 4 - (B3 : ℝ) / 128) ^ 2 * (1 / 2 + (B3 : ℝ) / 128)) * 2097152 =
          (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) * ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) := by
        rw [← hsc]; ring
      have hrhs : ((B3 : ℝ) / 128) * (1919 / 320000) * 2097152 = ((B3 : ℝ) * 16384) * (1919 / 320000) := by ring
      rw [hlhs, hrhs] at hmul
      have hle' : ((B3 : ℝ) * 16384) * (1919 / 320000) ≤
          ((s13n : ℝ) / 1000000 + ((A0 : ℝ) ^ 2 + (A1 : ℝ) ^ 2 + (A2 : ℝ) ^ 2 + (A3 : ℝ) ^ 2) / 16384) *
          ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) := by
        have heq : ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) *
            ((s13n : ℝ) / 1000000 + ((A0 : ℝ) * A0 + A1 * A1 + A2 * A2 + A3 * A3) / 16384) =
            ((s13n : ℝ) / 1000000 + ((A0 : ℝ) ^ 2 + (A1 : ℝ) ^ 2 + (A2 : ℝ) ^ 2 + (A3 : ℝ) ^ 2) / 16384) *
            ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) := by ring
        linarith
      have htot := le_of_mul_le_mul_right (le_trans hmul hle') hden_pos
      linarith
    · simp [hB3] at hok
  | 2 =>
    by_cases hA3 : 0 < A3
    · simp only [hA3, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hCv := Frac.valid_cFrac hA3
      have hBjv := Frac.valid_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv)
        (Frac.valid_mul hCv hHremv)
      let Bj := Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f
      have hok : (if !Bj.pos then (⟨s13n, 1000000⟩ : Frac).nonneg
          else (omwFrac B0 128 + cFrac A3 * hFrac B0 128).pos &&
            (Frac.sq ⟨B0, 128⟩ * Bj).le (⟨s13n, 1000000⟩ * (omwFrac B0 128 + cFrac A3 * hFrac B0 128))) = true := hok
      have hBj_r : Bj.toReal = 13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal := by
        simp only [Bj]
        rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv),
            Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv,
            Frac.toReal_sub (Frac.valid_ofInt 13) hWminv, Frac.toReal_ofInt, Frac.toReal_mul, hWmin_r, Int.cast_ofNat]
      by_cases hpos : Bj.pos = true
      · simp only [hpos, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
        have hdv := Frac.valid_add (Frac.valid_omwFrac (n := B0) h128) (Frac.valid_mul hCv (Frac.valid_hFrac (n := B0) h128))
        have hden_pos := (Frac.pos_iff hdv).mp hok.1
        have hden_r : (omwFrac B0 128 + cFrac A3 * hFrac B0 128).toReal =
            (1 - wPoly ((B0 : ℝ) / 128)) + (cFrac A3).toReal * hPoly ((B0 : ℝ) / 128) := by
          rw [Frac.toReal_add (Frac.valid_omwFrac h128) (Frac.valid_mul hCv (Frac.valid_hFrac h128)),
              Frac.toReal_omwFrac h128, Frac.toReal_mul, Frac.toReal_hFrac h128]
          simp only [Int.cast_ofNat]
        rw [hden_r] at hden_pos
        have hB0_pos : (0 : ℝ) < (B0 : ℝ) / 128 := by
          by_contra h0; push Not at h0
          have hB0_z : (B0 : ℝ) / 128 = 0 := le_antisymm h0 (by have : (0 : ℝ) ≤ (B0 : ℝ) := (by exact_mod_cast hB0_nn); linarith)
          rw [hB0_z] at hden_pos; simp [wPoly, hPoly] at hden_pos
        have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_sq (Frac.mk_valid h128)) hBjv)
          (Frac.valid_mul hs13v hdv)).mp hok.2
        rw [Frac.toReal_mul (Frac.sq ⟨B0, 128⟩) Bj, Frac.toReal_sq,
            Frac.toReal_mul ⟨s13n, 1000000⟩ _, hBj_r, hden_r, hs13_eq,
            show (⟨B0, 128⟩ : Frac).toReal = (B0 : ℝ) / 128 from by simp [Frac.toReal]] at hle
        exact joint_finish ((B0 : ℝ) / 128) hA3 hB0_pos (by have : (B0 : ℝ) ≤ 32 := (by exact_mod_cast hB0_le32); linarith)
          hb.x13_le_B0 hden_pos hle
      · simp only [hpos, Bool.not_false, ↓reduceIte] at hok
        have hbj_le : Bj.toReal ≤ 0 := not_lt.mp fun hp => hpos ((Frac.pos_iff hBjv).mpr hp)
        have hs_nn := (Frac.nonneg_iff hs13v).mp hok; rw [hs13_eq] at hs_nn
        rw [hBj_r] at hbj_le
        exact bjoint_nonpos_finish hA3 hbj_le hs_nn
    · simp [hA3] at hok
  | 3 =>
    by_cases hcond : (0 < A3 ∧ 0 < xcap ∧ (xcap : Int) ≤ B0 * 32)
    · rcases hcond with ⟨hA3, hxn_pos, hxn_le⟩
      have hcond_b : (decide (0 < A3) && decide (0 < (xcap : Int)) && decide ((xcap : Int) ≤ B0 * 32)) = true := by
        simp [hA3, hxn_pos, hxn_le]
      simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hCv := Frac.valid_cFrac hA3
      have hBjv := Frac.valid_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv)
        (Frac.valid_mul hCv hHremv)
      let Bj := Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f
      have hok : (if !Bj.pos then (⟨s13n, 1000000⟩ : Frac).nonneg
          else Bj.le (omwFrac (xcap : Int) 4096) &&
            (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096).pos &&
            (Frac.sq ⟨(xcap : Int), 4096⟩ * Bj).le
              (⟨s13n, 1000000⟩ * (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096))) = true := hok
      have hBj_r : Bj.toReal = 13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal := by
        simp only [Bj]
        rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv),
            Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv,
            Frac.toReal_sub (Frac.valid_ofInt 13) hWminv, Frac.toReal_ofInt, Frac.toReal_mul, hWmin_r, Int.cast_ofNat]
      by_cases hpos : Bj.pos = true
      · simp only [hpos, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
        rcases hok with ⟨⟨hBj_omw, hden_b⟩, hle_b⟩
        have homwv := Frac.valid_omwFrac (n := (xcap : Int)) h4096
        have hdv := Frac.valid_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac (n := (xcap : Int)) h4096))
        have hxc_pos : (0 : ℝ) < (xcap : ℝ) / 4096 := by
          have : (0 : ℝ) < (xcap : ℝ) := by exact_mod_cast hxn_pos
          linarith
        have hxc_le_B0 : (xcap : ℝ) / 4096 ≤ (B0 : ℝ) / 128 := by
          have : (xcap : ℝ) ≤ (B0 : ℝ) * 32 := by exact_mod_cast hxn_le
          linarith
        have hxc4 : (xcap : ℝ) / 4096 ≤ 1 / 4 := le_trans hxc_le_B0 (by have : (B0 : ℝ) ≤ 32 := (by exact_mod_cast hB0_le32); linarith)
        have hBj_omw_r := (Frac.le_iff hBjv homwv).mp hBj_omw
        rw [hBj_r, Frac.toReal_omwFrac h4096] at hBj_omw_r
        simp only [Int.cast_natCast, Int.cast_ofNat] at hBj_omw_r
        have hx_le_xc : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ (xcap : ℝ) / 4096 := by
          intro i
          by_contra hgt; push Not at hgt
          have hs := hsingle_joint hA3 i
          have hh_nn := mul_nonneg (hC_nn_of hA3) (hPoly_nonneg (ctx.x_nonneg ⟨i.val, by omega⟩))
          have hw_lt := wPoly_strictAnti (le_of_lt hxc_pos) hgt (hx13_4 i)
          linarith
        have hden_pos := (Frac.pos_iff hdv).mp hden_b
        have hden_r : (omwFrac xcap 4096 + cFrac A3 * hFrac xcap 4096).toReal =
            (1 - wPoly ((xcap : ℝ) / 4096)) + (cFrac A3).toReal * hPoly ((xcap : ℝ) / 4096) := by
          rw [Frac.toReal_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac h4096)),
              Frac.toReal_omwFrac h4096, Frac.toReal_mul, Frac.toReal_hFrac h4096]
          simp only [Int.cast_natCast, Int.cast_ofNat]
        rw [hden_r] at hden_pos
        have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_sq (Frac.mk_valid h4096)) hBjv)
          (Frac.valid_mul hs13v hdv)).mp hle_b
        rw [Frac.toReal_mul (Frac.sq ⟨(xcap : Int), 4096⟩) Bj, Frac.toReal_sq,
            Frac.toReal_mul ⟨s13n, 1000000⟩ _, hBj_r, hden_r, hs13_eq,
            show (⟨(xcap : Int), 4096⟩ : Frac).toReal = (xcap : ℝ) / 4096 from by simp [Frac.toReal]] at hle
        exact joint_finish ((xcap : ℝ) / 4096) hA3 hxc_pos hxc4 hx_le_xc hden_pos hle
      · simp only [hpos, Bool.not_false, ↓reduceIte] at hok
        have hbj_le : Bj.toReal ≤ 0 := not_lt.mp fun hp => hpos ((Frac.pos_iff hBjv).mpr hp)
        have hs_nn := (Frac.nonneg_iff hs13v).mp hok; rw [hs13_eq] at hs_nn
        rw [hBj_r] at hbj_le
        exact bjoint_nonpos_finish hA3 hbj_le hs_nn
    · have hcond_f := bool_and3_false (P := 0 < A3) (Q := 0 < (xcap : Int)) (R := (xcap : Int) ≤ B0 * 32)
        (fun ⟨h1, h2, h3⟩ => hcond ⟨h1, by omega, h3⟩)
      simp only [hcond_f, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hok
  | 4 =>
    by_cases hcond : (0 < A3 ∧ 0 < xcap ∧ (xcap : Int) ≤ B0 * 32 ∧ xcap ≤ 368)
    · rcases hcond with ⟨hA3, hxn_pos, hxn_le, hxn_368⟩
      have hcond_b : (decide (0 < A3) && decide (0 < (xcap : Int)) && decide ((xcap : Int) ≤ B0 * 32) &&
          decide ((xcap : Int) ≤ 368)) = true := by simp [hA3, hxn_pos, hxn_le, hxn_368]
      simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hCv := Frac.valid_cFrac hA3
      have hBjv := Frac.valid_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv)
        (Frac.valid_mul hCv hHremv)
      let Bj := Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f
      have hok : (if !Bj.pos then (⟨s13n, 1000000⟩ : Frac).nonneg
          else (decide (B0 * 32 ≤ 368) || Bj.le (omwFrac 368 4096)) &&
            Bj.le (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096) &&
            (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096).pos &&
            (Frac.sq ⟨(xcap : Int), 4096⟩ * Bj).le
              (⟨s13n, 1000000⟩ * (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096))) = true := hok
      have hBj_r : Bj.toReal = 13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal := by
        simp only [Bj]
        rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv),
            Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv,
            Frac.toReal_sub (Frac.valid_ofInt 13) hWminv, Frac.toReal_ofInt, Frac.toReal_mul, hWmin_r, Int.cast_ofNat]
      by_cases hpos : Bj.pos = true
      · simp only [hpos, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
        rcases hok with ⟨⟨⟨hok09, hBj_den⟩, hden_b⟩, hle_b⟩
        have homwv := Frac.valid_omwFrac (n := (xcap : Int)) h4096
        have hdv := Frac.valid_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac (n := (xcap : Int)) h4096))
        have hxc_pos : (0 : ℝ) < (xcap : ℝ) / 4096 := by
          have : (0 : ℝ) < (xcap : ℝ) := by exact_mod_cast hxn_pos
          linarith
        have hxc_368 : (xcap : ℝ) / 4096 ≤ 368 / 4096 := by
          have : (xcap : ℝ) ≤ 368 := by exact_mod_cast hxn_368
          linarith
        have hx_le_368 := hx_le_368_of_ok09 hA3 hok09
        have hden_r : (omwFrac xcap 4096 + cFrac A3 * hFrac xcap 4096).toReal =
            (1 - wPoly ((xcap : ℝ) / 4096)) + (cFrac A3).toReal * hPoly ((xcap : ℝ) / 4096) := by
          rw [Frac.toReal_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac h4096)),
              Frac.toReal_omwFrac h4096, Frac.toReal_mul, Frac.toReal_hFrac h4096]
          simp only [Int.cast_natCast, Int.cast_ofNat]
        have hBj_den_r := (Frac.le_iff hBjv hdv).mp hBj_den
        rw [hBj_r, hden_r] at hBj_den_r
        have hx_le_xc : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ (xcap : ℝ) / 4096 := by
          intro i
          by_contra hgt; push Not at hgt
          have hs := hsingle_joint hA3 i
          have hw_lt := wPoly_strictAnti (le_of_lt hxc_pos) hgt (le_trans (hx_le_368 i) (by norm_num))
          have hh_lt := hPoly_strictMono_009 (le_of_lt hxc_pos) hgt (hx_le_368 i)
          have hh_mul := mul_le_mul_of_nonneg_left (le_of_lt hh_lt) (hC_nn_of hA3)
          linarith
        have hden_pos := (Frac.pos_iff hdv).mp hden_b; rw [hden_r] at hden_pos
        have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_sq (Frac.mk_valid h4096)) hBjv)
          (Frac.valid_mul hs13v hdv)).mp hle_b
        rw [Frac.toReal_mul (Frac.sq ⟨(xcap : Int), 4096⟩) Bj, Frac.toReal_sq,
            Frac.toReal_mul ⟨s13n, 1000000⟩ _, hBj_r, hden_r, hs13_eq,
            show (⟨(xcap : Int), 4096⟩ : Frac).toReal = (xcap : ℝ) / 4096 from by simp [Frac.toReal]] at hle
        exact joint_finish ((xcap : ℝ) / 4096) hA3 hxc_pos (by linarith) hx_le_xc hden_pos hle
      · simp only [hpos, Bool.not_false, ↓reduceIte] at hok
        have hbj_le : Bj.toReal ≤ 0 := not_lt.mp fun hp => hpos ((Frac.pos_iff hBjv).mpr hp)
        have hs_nn := (Frac.nonneg_iff hs13v).mp hok; rw [hs13_eq] at hs_nn
        rw [hBj_r] at hbj_le
        exact bjoint_nonpos_finish hA3 hbj_le hs_nn
    · have hcond_f := bool_and4_false (P := 0 < A3) (Q := 0 < (xcap : Int)) (R := (xcap : Int) ≤ B0 * 32) (S := (xcap : Int) ≤ 368)
        (fun ⟨h1, h2, h3, h4⟩ => hcond ⟨h1, by omega, h3, by omega⟩)
      simp only [hcond_f, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hok
  | 5 =>
    by_cases hcond : (0 < A3 ∧ 0 < xcap ∧ (xcap : Int) ≤ B0 * 32 ∧ xcap ≤ 368)
    · rcases hcond with ⟨hA3, hxn_pos, hxn_le, hxn_368⟩
      have hcond_b : (decide (0 < A3) && decide (0 < (xcap : Int)) && decide ((xcap : Int) ≤ B0 * 32) &&
          decide ((xcap : Int) ≤ 368)) = true := by simp [hA3, hxn_pos, hxn_le, hxn_368]
      simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hCv := Frac.valid_cFrac hA3
      have hBjv := Frac.valid_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv)
        (Frac.valid_mul hCv hHremv)
      let Bj := Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f
      have hok : (if !Bj.pos then (⟨s13n, 1000000⟩ : Frac).nonneg
          else (decide (B0 * 32 ≤ 368) || Bj.le (omwFrac 368 4096)) &&
            H_rem_f.le (hFrac (xcap : Int) 4096) &&
            (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096).pos &&
            (Frac.sq ⟨(xcap : Int), 4096⟩ * Bj).le
              (⟨s13n, 1000000⟩ * (omwFrac (xcap : Int) 4096 + cFrac A3 * hFrac (xcap : Int) 4096))) = true := hok
      have hBj_r : Bj.toReal = 13 - 388592 / 30000 + w_hi_f.toReal + (cFrac A3).toReal * H_rem_f.toReal := by
        simp only [Bj]
        rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv) (Frac.valid_mul hCv hHremv),
            Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 13) hWminv) hwhiv,
            Frac.toReal_sub (Frac.valid_ofInt 13) hWminv, Frac.toReal_ofInt, Frac.toReal_mul, hWmin_r, Int.cast_ofNat]
      by_cases hpos : Bj.pos = true
      · simp only [hpos, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
        rcases hok with ⟨⟨⟨hok09, hH_le⟩, hden_b⟩, hle_b⟩
        have homwv := Frac.valid_omwFrac (n := (xcap : Int)) h4096
        have hdv := Frac.valid_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac (n := (xcap : Int)) h4096))
        have hxc_pos : (0 : ℝ) < (xcap : ℝ) / 4096 := by
          have : (0 : ℝ) < (xcap : ℝ) := by exact_mod_cast hxn_pos
          linarith
        have hxc_368 : (xcap : ℝ) / 4096 ≤ 368 / 4096 := by
          have : (xcap : ℝ) ≤ 368 := by exact_mod_cast hxn_368
          linarith
        have hx_le_368 := hx_le_368_of_ok09 hA3 hok09
        have hH_le_r := (Frac.le_iff hHremv (Frac.valid_hFrac h4096)).mp hH_le
        rw [Frac.toReal_hFrac h4096] at hH_le_r
        simp only [Int.cast_natCast, Int.cast_ofNat] at hH_le_r
        have hx_le_xc : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ (xcap : ℝ) / 4096 := by
          intro i
          by_contra hgt; push Not at hgt
          have hsingle : hPoly (ctx.x ⟨i.val, by omega⟩) ≤ H_rem_f.toReal :=
            le_trans (Finset.single_le_sum (f := fun j : Fin 13 => hPoly (ctx.x ⟨j.val, by omega⟩))
              (fun j _ => hPoly_nonneg (abs_nonneg _)) (Finset.mem_univ i)) hh13_le
          have hh_lt := hPoly_strictMono_009 (le_of_lt hxc_pos) hgt (hx_le_368 i)
          linarith
        have hden_r : (omwFrac xcap 4096 + cFrac A3 * hFrac xcap 4096).toReal =
            (1 - wPoly ((xcap : ℝ) / 4096)) + (cFrac A3).toReal * hPoly ((xcap : ℝ) / 4096) := by
          rw [Frac.toReal_add homwv (Frac.valid_mul hCv (Frac.valid_hFrac h4096)),
              Frac.toReal_omwFrac h4096, Frac.toReal_mul, Frac.toReal_hFrac h4096]
          simp only [Int.cast_natCast, Int.cast_ofNat]
        have hden_pos := (Frac.pos_iff hdv).mp hden_b; rw [hden_r] at hden_pos
        have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_sq (Frac.mk_valid h4096)) hBjv)
          (Frac.valid_mul hs13v hdv)).mp hle_b
        rw [Frac.toReal_mul (Frac.sq ⟨(xcap : Int), 4096⟩) Bj, Frac.toReal_sq,
            Frac.toReal_mul ⟨s13n, 1000000⟩ _, hBj_r, hden_r, hs13_eq,
            show (⟨(xcap : Int), 4096⟩ : Frac).toReal = (xcap : ℝ) / 4096 from by simp [Frac.toReal]] at hle
        exact joint_finish ((xcap : ℝ) / 4096) hA3 hxc_pos (by linarith) hx_le_xc hden_pos hle
      · simp only [hpos, Bool.not_false, ↓reduceIte] at hok
        have hbj_le : Bj.toReal ≤ 0 := not_lt.mp fun hp => hpos ((Frac.pos_iff hBjv).mpr hp)
        have hs_nn := (Frac.nonneg_iff hs13v).mp hok; rw [hs13_eq] at hs_nn
        rw [hBj_r] at hbj_le
        exact bjoint_nonpos_finish hA3 hbj_le hs_nn
    · have hcond_f := bool_and4_false (P := 0 < A3) (Q := 0 < (xcap : Int)) (R := (xcap : Int) ≤ B0 * 32) (S := (xcap : Int) ≤ 368)
        (fun ⟨h1, h2, h3, h4⟩ => hcond ⟨h1, by omega, h3, by omega⟩)
      simp only [hcond_f, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hok
  | 6 =>
    by_cases hcond : (0 < A3 ∧ 0 < xcap ∧ (xcap : Int) ≤ B0 * 32 ∧ xcap ≤ 368)
    · rcases hcond with ⟨hA3, hxn_pos, hxn_le, hxn_368⟩
      have hcond_b : (decide (0 < A3) && decide (0 < (xcap : Int)) && decide ((xcap : Int) ≤ B0 * 32) &&
          decide ((xcap : Int) ≤ 368)) = true := by simp [hA3, hxn_pos, hxn_le, hxn_368]
      simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      let Bj := Frac.ofInt 13 - W_MIN + w_hi_f + cFrac A3 * H_rem_f
      have hok : ((decide (B0 * 32 ≤ 368) || Bj.le (omwFrac 368 4096)) &&
          H_rem_f.le (hFrac (xcap : Int) 4096) &&
          (Frac.ofInt ((xcap : Int) * 16777216) * H_rem_f).le
            (Frac.ofInt ((1024 - (xcap : Int)) * (1024 - (xcap : Int)) * (2048 + (xcap : Int))) * ⟨s13n, 1000000⟩)) = true := hok
      simp only [Bool.and_eq_true] at hok
      rcases hok with ⟨⟨hok09, hH_le⟩, hle_b⟩
      have hxc_pos : (0 : ℝ) < (xcap : ℝ) / 4096 := by
        have : (0 : ℝ) < (xcap : ℝ) := by exact_mod_cast hxn_pos
        linarith
      have hxc_368 : (xcap : ℝ) / 4096 ≤ 368 / 4096 := by
        have : (xcap : ℝ) ≤ 368 := by exact_mod_cast hxn_368
        linarith
      have hx_le_368 := hx_le_368_of_ok09 hA3 hok09
      have hH_le_r := (Frac.le_iff hHremv (Frac.valid_hFrac h4096)).mp hH_le
      rw [Frac.toReal_hFrac h4096] at hH_le_r
      simp only [Int.cast_natCast, Int.cast_ofNat] at hH_le_r
      have hx_le_xc : ∀ i : Fin 13, ctx.x ⟨i.val, by omega⟩ ≤ (xcap : ℝ) / 4096 := by
        intro i
        by_contra hgt; push Not at hgt
        have hsingle : hPoly (ctx.x ⟨i.val, by omega⟩) ≤ H_rem_f.toReal :=
          le_trans (Finset.single_le_sum (f := fun j : Fin 13 => hPoly (ctx.x ⟨j.val, by omega⟩))
            (fun j _ => hPoly_nonneg (abs_nonneg _)) (Finset.mem_univ i)) hh13_le
        have hh_lt := hPoly_strictMono_009 (le_of_lt hxc_pos) hgt (hx_le_368 i)
        linarith
      have hlv := Frac.valid_mul (Frac.valid_ofInt ((xcap : Int) * 16777216)) hHremv
      have hrv := Frac.valid_mul (Frac.valid_ofInt ((1024 - (xcap : Int)) * (1024 - (xcap : Int)) * (2048 + (xcap : Int)))) hs13v
      have hle := (Frac.le_iff hlv hrv).mp hle_b
      rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt, hs13_eq] at hle
      push_cast at hle
      have hden_pos : (0 : ℝ) < (1024 - (xcap : ℝ)) * (1024 - (xcap : ℝ)) * (2048 + (xcap : ℝ)) := by
        have h1 : (xcap : ℝ) ≤ 368 := by exact_mod_cast hxn_368
        have h2 : (0 : ℝ) < (xcap : ℝ) := by exact_mod_cast hxn_pos
        have h3 : (0 : ℝ) < 1024 - (xcap : ℝ) := by linarith only [h1]
        positivity
      have hsum : ctx.S2_13 * ((1 / 4 - (xcap : ℝ) / 4096) ^ 2 * (1 / 2 + (xcap : ℝ) / 4096)) ≤
          ((xcap : ℝ) / 4096) * H_rem_f.toReal := by
        have hpt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          sq_le_pureH (ctx.x_nonneg _) (hx_le_xc i) (by linarith)
        rw [← Finset.sum_mul, ← Finset.mul_sum] at hpt
        exact le_trans hpt (mul_le_mul_of_nonneg_left hh13_le (le_of_lt hxc_pos))
      have hsc : ((1 / 4 - (xcap : ℝ) / 4096) ^ 2 * (1 / 2 + (xcap : ℝ) / 4096)) * (4096 * 16777216) =
          (1024 - (xcap : ℝ)) * (1024 - (xcap : ℝ)) * (2048 + (xcap : ℝ)) := by ring
      have hmul := mul_le_mul_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 4096 * 16777216)
      have hlhs : ctx.S2_13 * ((1 / 4 - (xcap : ℝ) / 4096) ^ 2 * (1 / 2 + (xcap : ℝ) / 4096)) * (4096 * 16777216) =
          ctx.S2_13 * ((1024 - (xcap : ℝ)) * (1024 - (xcap : ℝ)) * (2048 + (xcap : ℝ))) := by rw [← hsc]; ring
      have hrhs : ((xcap : ℝ) / 4096) * H_rem_f.toReal * (4096 * 16777216) = ((xcap : ℝ) * 16777216) * H_rem_f.toReal := by ring
      rw [hlhs, hrhs] at hmul
      rw [mul_comm ((1024 - (xcap : ℝ)) * (1024 - (xcap : ℝ)) * (2048 + (xcap : ℝ)))] at hle
      exact le_of_mul_le_mul_right (le_trans hmul hle) hden_pos
    · have hcond_f := bool_and4_false (P := 0 < A3) (Q := 0 < (xcap : Int)) (R := (xcap : Int) ≤ B0 * 32) (S := (xcap : Int) ≤ 368)
        (fun ⟨h1, h2, h3, h4⟩ => hcond ⟨h1, by omega, h3, by omega⟩)
      simp only [hcond_f, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hok
  | _ + 8 => simp at hok

private lemma sound_checkSk {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) {k s13n skn : Nat} {uph : Bool}
    (hk : k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17)
    (hB_lt : (k = 14 → B0 < 32) ∧ (k = 15 → B1 < 32) ∧ (k = 16 → B2 < 32) ∧ (k = 17 → B3 < 32))
    (hs13 : ctx.S2_13 ≤ (s13n : ℝ) / 1000000)
    (hok : checkSk A0 A1 A2 A3 B0 B1 B2 B3 k s13n uph skn = true) :
    ∑ i : Fin k, (ctx.x ⟨i.val, by omega⟩) ^ 2 ≤ (skn : ℝ) / 1000000 := by
  classical
  have hs13v : (⟨s13n, 1000000⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have hskv : (⟨skn, 1000000⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have h16384 : (0 : Int) < 16384 := by norm_num
  have hunc := hb.unclamp
  have hge := hb.x_ge_A
  have hsplit14 : ∑ i : Fin 14, (ctx.x ⟨i.val, by omega⟩) ^ 2 = ctx.S2_13 + (ctx.x ⟨13, by omega⟩) ^ 2 :=
    sum_fin14_eq (fun i => (ctx.x i) ^ 2)
  have hsplit15 : ∑ i : Fin 15, (ctx.x ⟨i.val, by omega⟩) ^ 2 =
      ctx.S2_13 + (ctx.x ⟨13, by omega⟩) ^ 2 + (ctx.x ⟨14, by omega⟩) ^ 2 :=
    sum_fin15_eq (fun i => (ctx.x i) ^ 2)
  have hsplit16 : ∑ i : Fin 16, (ctx.x ⟨i.val, by omega⟩) ^ 2 =
      ctx.S2_13 + (ctx.x ⟨13, by omega⟩) ^ 2 + (ctx.x ⟨14, by omega⟩) ^ 2 + (ctx.x ⟨15, by omega⟩) ^ 2 :=
    sum_fin16_eq (fun i => (ctx.x i) ^ 2)
  have hsplit17 : ∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2 =
      ctx.S2_13 + (ctx.x ⟨13, by omega⟩) ^ 2 + (ctx.x ⟨14, by omega⟩) ^ 2 +
      (ctx.x ⟨15, by omega⟩) ^ 2 + (ctx.x ⟨16, by omega⟩) ^ 2 :=
    sum_fin17_eq (fun i => (ctx.x i) ^ 2)
  unfold checkSk at hok
  cases uph
  · simp only [Bool.not_false, ↓reduceIte] at hok
    rcases hk with rfl | rfl | rfl | rfl
    · have hle := (Frac.le_iff (Frac.valid_add hs13v (Frac.mk_valid h16384)) hskv).mp hok
      rw [Frac.toReal_add hs13v (Frac.mk_valid h16384)] at hle; simp only [Frac.toReal] at hle; push_cast at hle
      have hx0 := pow_le_pow_left₀ (abs_nonneg _) (hunc.1 (hB_lt.1 rfl)) 2
      rw [hsplit14]; linarith
    · have hle := (Frac.le_iff (Frac.valid_add hs13v (Frac.mk_valid h16384)) hskv).mp hok
      rw [Frac.toReal_add hs13v (Frac.mk_valid h16384)] at hle; simp only [Frac.toReal] at hle; push_cast at hle
      have hB1 := hB_lt.2.1 rfl
      have hx0 := pow_le_pow_left₀ (abs_nonneg _) (hunc.1 (lt_of_le_of_lt hb.hB01 hB1)) 2
      have hx1 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.1 hB1) 2
      rw [hsplit15]; linarith
    · have hle := (Frac.le_iff (Frac.valid_add hs13v (Frac.mk_valid h16384)) hskv).mp hok
      rw [Frac.toReal_add hs13v (Frac.mk_valid h16384)] at hle; simp only [Frac.toReal] at hle; push_cast at hle
      have hB2 := hB_lt.2.2.1 rfl
      have hx0 := pow_le_pow_left₀ (abs_nonneg _) (hunc.1 (lt_of_le_of_lt (le_trans hb.hB01 hb.hB12) hB2)) 2
      have hx1 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.1 (lt_of_le_of_lt hb.hB12 hB2)) 2
      have hx2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.2.1 hB2) 2
      rw [hsplit16]; linarith
    · have hle := (Frac.le_iff (Frac.valid_add hs13v (Frac.mk_valid h16384)) hskv).mp hok
      rw [Frac.toReal_add hs13v (Frac.mk_valid h16384)] at hle; simp only [Frac.toReal] at hle; push_cast at hle
      have hB3 := hB_lt.2.2.2 rfl
      have hx0 := pow_le_pow_left₀ (abs_nonneg _) (hunc.1 (lt_of_le_of_lt (le_trans hb.hB01 (le_trans hb.hB12 hb.hB23)) hB3)) 2
      have hx1 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.1 (lt_of_le_of_lt (le_trans hb.hB12 hb.hB23) hB3)) 2
      have hx2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.2.1 (lt_of_le_of_lt hb.hB23 hB3)) 2
      have hx3 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.2.2 hB3) 2
      rw [hsplit17]; linarith
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
    by_cases hB3 : B3 < 32
    · simp only [hB3, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have hB3_nn : 0 ≤ B3 := by
        have h1 : (A3 : ℝ) / 128 ≤ (B3 : ℝ) / 128 := le_trans hb.h3_lo hb.h3_hi
        have hA3_nn : 0 ≤ A3 := le_trans hb.hA0_nn (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23))
        have h2 : A3 ≤ B3 := by exact_mod_cast (show (A3 : ℝ) ≤ (B3 : ℝ) by linarith)
        exact le_trans hA3_nn h2
      have hden_pos : (0 : ℝ) < (32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)) := by
        have h1 : (B3 : ℝ) < 32 := by exact_mod_cast hB3
        have h2 : (0 : ℝ) ≤ (B3 : ℝ) := by exact_mod_cast hB3_nn
        positivity
      have hx16_le : ctx.x ⟨16, by omega⟩ ≤ (B3 : ℝ) / 128 := hunc.2.2.2 hB3
      have h17_le : ∀ i : Fin 17, ctx.x ⟨i.val, by omega⟩ ≤ (B3 : ℝ) / 128 := fun i =>
        le_trans (ctx.idx_mono ⟨i.val, by omega⟩ ⟨16, by omega⟩ (Fin.le_iff_val_le_val.mpr (show i.val ≤ 16 by omega))) hx16_le
      obtain ⟨hh_glob, _⟩ := global_h_and_w_bounds ctx.hunit ctx.hL1 ctx.hF4
      dsimp only at hh_glob; rw [ctx.sum_U_eq] at hh_glob
      have h17_h : ∑ i : Fin 17, hPoly (ctx.x ⟨i.val, by omega⟩) ≤ 1919 / 320000 := by
        let S17 := Finset.univ.filter fun j : Fin 255 => j.val < 17
        have h1 : ∑ i : Fin 17, hPoly (ctx.x ⟨i.val, by omega⟩) = ∑ j ∈ S17, hPoly (ctx.x j) := by
          refine Finset.sum_bij (fun i _ => (⟨i.val, by omega⟩ : Fin 255)) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
          · intro a _ b _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
          · intro j hj; exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
        rw [h1]
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hPoly_nonneg (abs_nonneg _)) hh_glob
      have hsum17 : (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) *
          ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) ≤ ((B3 : ℝ) * 16384) * (1919 / 320000) := by
        have hB3_4 : (B3 : ℝ) / 128 ≤ 1 / 4 := by
          have : (B3 : ℝ) < 32 := by exact_mod_cast hB3
          linarith
        have hpt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          sq_le_pureH (ctx.x_nonneg _) (h17_le i) hB3_4
        rw [← Finset.sum_mul, ← Finset.mul_sum] at hpt
        have hB3_r : (0 : ℝ) ≤ (B3 : ℝ) / 128 := by
          have : (0 : ℝ) ≤ (B3 : ℝ) := by exact_mod_cast hB3_nn
          linarith
        have h0 := le_trans hpt (mul_le_mul_of_nonneg_left h17_h hB3_r)
        have hsc : ((1 / 4 - (B3 : ℝ) / 128) ^ 2 * (1 / 2 + (B3 : ℝ) / 128)) * 2097152 =
            (32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)) := by ring
        have hmul := mul_le_mul_of_nonneg_right h0 (by norm_num : (0 : ℝ) ≤ 2097152)
        have hlhs : (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) *
            ((1 / 4 - (B3 : ℝ) / 128) ^ 2 * (1 / 2 + (B3 : ℝ) / 128)) * 2097152 =
            (∑ i : Fin 17, (ctx.x ⟨i.val, by omega⟩) ^ 2) * ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ))) := by
          rw [← hsc]; ring
        have hrhs : ((B3 : ℝ) / 128) * (1919 / 320000) * 2097152 = ((B3 : ℝ) * 16384) * (1919 / 320000) := by ring
        rw [hlhs, hrhs] at hmul; exact hmul
      have s1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A1 : ℝ) / 128 by have : (0 : ℝ) ≤ (A1 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn hb.hA01); linarith) hge.2.1 2
      have s2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A2 : ℝ) / 128 by have : (0 : ℝ) ≤ (A2 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn (le_trans hb.hA01 hb.hA12)); linarith) hge.2.2.1 2
      have s3 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A3 : ℝ) / 128 by have : (0 : ℝ) ≤ (A3 : ℝ) := (by exact_mod_cast le_trans hb.hA0_nn (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23))); linarith) hge.2.2.2 2
      have hHmaxv : H_MAX.Valid := valid_H_MAX
      rcases hk with rfl | rfl | rfl | rfl
      · have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_ofInt _) hHmaxv)
          (Frac.valid_mul (Frac.valid_ofInt _) (Frac.valid_add hskv (Frac.mk_valid h16384)))).mp hok
        rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
            Frac.toReal_add hskv (Frac.mk_valid h16384)] at hle
        simp only [H_MAX, Frac.toReal] at hle; push_cast at hle
        rw [mul_comm ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)))] at hle
        have htot := le_of_mul_le_mul_right (le_trans hsum17 hle) hden_pos
        rw [hsplit14]; rw [hsplit17] at htot; linarith
      · have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_ofInt _) hHmaxv)
          (Frac.valid_mul (Frac.valid_ofInt _) (Frac.valid_add hskv (Frac.mk_valid h16384)))).mp hok
        rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
            Frac.toReal_add hskv (Frac.mk_valid h16384)] at hle
        simp only [H_MAX, Frac.toReal] at hle; push_cast at hle
        rw [mul_comm ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)))] at hle
        have htot := le_of_mul_le_mul_right (le_trans hsum17 hle) hden_pos
        rw [hsplit15]; rw [hsplit17] at htot; linarith
      · have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_ofInt _) hHmaxv)
          (Frac.valid_mul (Frac.valid_ofInt _) (Frac.valid_add hskv (Frac.mk_valid h16384)))).mp hok
        rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
            Frac.toReal_add hskv (Frac.mk_valid h16384)] at hle
        simp only [H_MAX, Frac.toReal] at hle; push_cast at hle
        rw [mul_comm ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)))] at hle
        have htot := le_of_mul_le_mul_right (le_trans hsum17 hle) hden_pos
        rw [hsplit16]; rw [hsplit17] at htot; linarith
      · have hle := (Frac.le_iff (Frac.valid_mul (Frac.valid_ofInt _) hHmaxv)
          (Frac.valid_mul (Frac.valid_ofInt _) (Frac.valid_add hskv (Frac.mk_valid (by norm_num))))).mp hok
        rw [Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
            Frac.toReal_add hskv (Frac.mk_valid (by norm_num))] at hle
        simp only [H_MAX, Frac.toReal] at hle; push_cast at hle
        rw [mul_comm ((32 - (B3 : ℝ)) * (32 - (B3 : ℝ)) * (64 + (B3 : ℝ)))] at hle
        have htot := le_of_mul_le_mul_right (le_trans hsum17 hle) hden_pos
        linarith
    · simp [hB3] at hok

set_option maxHeartbeats 800000 in
/-- Soundness of `checkMethod` on a single interval `[u, v]` (or `[u, ∞)`). -/
private lemma sound_checkMethod {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3)
    {L S13 : Finset (PauliIdx 4)} (hL : IsLagrangian L) (hS13_sub : S13 ⊆ L) (h0_S13 : (0 : PauliIdx 4) ∈ S13)
    (hS13_card : S13.card = 13)
    {uPt : PauliIdx 4} (huL : uPt ∉ L) (hu0 : uPt ≠ 0)
    (hZ14_eq : insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ) =
      insert uPt S13)
    {mask : Nat} (_hmask_lt : mask < 15)
    (hmask_def : ∀ j : Fin 4, bitSet mask j.val = decide (ctx.idx ⟨13 + j.val, by omega⟩ ∈ L))
    {s13 : Frac} (hs13v : s13.Valid) (hs13_le : ctx.S2_13 ≤ s13.toReal)
    {m : Nat} {u v : Frac} (huv : u.Valid) (hvv : v.Valid) (hu_nn : 0 ≤ u.toReal) {is_inf : Bool}
    (hok : checkMethod A0 A1 A2 A3 B0 B1 B2 B3 mask s13 m u v is_inf = true) :
    let ps : Fin 4 → PauliIdx 4 := fun j => ctx.idx ⟨13 + j.val, by omega⟩
    let Bs : Fin 4 → Int := ![B0, B1, B2, B3]
    let Icap := Finset.univ.filter fun j : Fin 4 => ps j ∈ L ∧ Bs j < 32
    let Lfree := (L.erase 0) \ (S13.erase 0 ∪ Icap.image ps)
    let t : ℝ := ∑ p ∈ Lfree, (ctx.c p) ^ 2
    (if is_inf then u.toReal ≤ t else u.toReal ≤ t ∧ t ≤ v.toReal) → False := by
  classical
  intro ps Bs Icap Lfree t ht_range
  have hps_inj : Function.Injective ps := fun a b h => by
    have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext (by omega)
  have hps_not_Z14 : ∀ j : Fin 4, ps j ∉ insert uPt S13 := fun j hmem => by
    rw [← hZ14_eq] at hmem
    rcases Finset.mem_insert.mp hmem with h0 | hI
    · exact ctx.idx_ne0 ⟨13 + j.val, by omega⟩ h0
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hI
      have h' := congr_arg Fin.val (ctx.idx_inj hi); dsimp at h'; omega
  have hps_not_S13 : ∀ j : Fin 4, ps j ∉ S13 := fun j h => hps_not_Z14 j (Finset.mem_insert_of_mem h)
  have hps_ne_u : ∀ j : Fin 4, ps j ≠ uPt := fun j h => hps_not_Z14 j (h ▸ Finset.mem_insert_self _ _)
  have hu_not_S13 : uPt ∉ S13 := fun h => huL (hS13_sub h)
  have hS13_u_sum : (∑ p ∈ S13.erase 0, (ctx.c p) ^ 2) + (ctx.c uPt) ^ 2 = ctx.S2_13 := by
    have hZ14_e : (insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ)).erase 0 =
        Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
      rw [Finset.erase_insert]
      intro hmem; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem; exact ctx.idx_ne0 _ hi
    have hZ14_e2 : (insert uPt S13).erase 0 = insert uPt (S13.erase 0) :=
      Finset.erase_insert_of_ne hu0
    have heq : insert uPt (S13.erase 0) = Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
      rw [← hZ14_e2, ← hZ14_eq, hZ14_e]
    have hu_not_e : uPt ∉ S13.erase 0 := fun h => hu_not_S13 (Finset.mem_erase.mp h).2
    have hs1 : ∑ p ∈ insert uPt (S13.erase 0), (ctx.c p) ^ 2 = (ctx.c uPt) ^ 2 + ∑ p ∈ S13.erase 0, (ctx.c p) ^ 2 :=
      Finset.sum_insert hu_not_e
    rw [heq, Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')] at hs1
    have hsq : ∑ i : Fin 13, (ctx.c (ctx.idx ⟨i.val, by omega⟩)) ^ 2 = ctx.S2_13 :=
      Finset.sum_congr rfl fun i _ => (sq_abs _).symm
    linarith
  have hu_le4 : |ctx.c uPt| ≤ 1 / 4 := by
    have hmem : uPt ∈ insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ) := by
      rw [hZ14_eq]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with h0 | hI
    · exact absurd h0 hu0
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
      exact ctx.x_le_quarter ⟨i.val, by omega⟩ (show i.val ≤ 15 by omega)
  have hS13_e_sub : S13.erase 0 ⊆ L.erase 0 := Finset.erase_subset_erase 0 hS13_sub
  have hIcap_sub : Icap.image ps ⊆ L.erase 0 := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_erase.mpr ⟨ctx.idx_ne0 _, (Finset.mem_filter.mp hj).2.1⟩
  have hdisj_SI : Disjoint (S13.erase 0) (Icap.image ps) := by
    rw [Finset.disjoint_left]; intro p hpS hpI
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpI
    exact hps_not_S13 j (Finset.mem_erase.mp hpS).2
  have hunion_sub : S13.erase 0 ∪ Icap.image ps ⊆ L.erase 0 := Finset.union_subset hS13_e_sub hIcap_sub
  -- `Lfree.card = kFreeOf B0 B1 B2 B3 mask`!
  have hIcap_card : Icap.card =
      (if bitSet mask 0 && decide (B0 < 32) then 1 else 0) +
      (if bitSet mask 1 && decide (B1 < 32) then 1 else 0) +
      (if bitSet mask 2 && decide (B2 < 32) then 1 else 0) +
      (if bitSet mask 3 && decide (B3 < 32) then 1 else 0) := by
    have h1 : Icap.card = ∑ j : Fin 4, if ps j ∈ L ∧ Bs j < 32 then 1 else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [h1, Fin.sum_univ_four]
    have h0 : bitSet mask 0 = decide (ps 0 ∈ L) := hmask_def 0
    have h1' : bitSet mask 1 = decide (ps 1 ∈ L) := hmask_def 1
    have h2' : bitSet mask 2 = decide (ps 2 ∈ L) := hmask_def 2
    have h3' : bitSet mask 3 = decide (ps 3 ∈ L) := hmask_def 3
    simp only [Bs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [h0, h1', h2', h3']
    by_cases p0 : ps 0 ∈ L <;> by_cases b0 : B0 < 32 <;>
    by_cases p1 : ps 1 ∈ L <;> by_cases b1 : B1 < 32 <;>
    by_cases p2 : ps 2 ∈ L <;> by_cases b2 : B2 < 32 <;>
    by_cases p3 : ps 3 ∈ L <;> by_cases b3 : B3 < 32 <;> simp [p0, b0, p1, b1, p2, b2, p3, b3]
  have hkfree_eq : Lfree.card = kFreeOf B0 B1 B2 B3 mask := by
    have hL15 : (L.erase 0).card = 15 := by rw [Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num
    have hS12 : (S13.erase 0).card = 12 := by rw [Finset.card_erase_of_mem h0_S13, hS13_card]
    have hUcard : (S13.erase 0 ∪ Icap.image ps).card = 12 + Icap.card := by
      rw [Finset.card_union_of_disjoint hdisj_SI, hS12, Finset.card_image_of_injective _ hps_inj]
    have hdiff : Lfree.card = (L.erase 0).card - (S13.erase 0 ∪ Icap.image ps).card :=
      Finset.card_sdiff_of_subset hunion_sub
    rw [hdiff, hL15, hUcard, hIcap_card]
    dsimp only [kFreeOf]; omega
  -- Split `S2(L) = z + t` and `S4(L) ≥ ∑_{Icap} c⁴ + inv_k * t²`!
  set z0 : ℝ := ∑ p ∈ S13.erase 0, (ctx.c p) ^ 2
  set zI : ℝ := ∑ j ∈ Icap, (ctx.c (ps j)) ^ 2
  set z : ℝ := z0 + zI
  set S2L : ℝ := ∑ p ∈ L.erase 0, (ctx.c p) ^ 2
  set S4L : ℝ := ∑ p ∈ L.erase 0, (ctx.c p) ^ 4
  have hS2L_eq : S2L = z + t := by
    have hs := Finset.sum_sdiff hunion_sub (f := fun p => (ctx.c p) ^ 2)
    rw [Finset.sum_union hdisj_SI, Finset.sum_image (fun a _ b _ h => hps_inj h)] at hs
    linarith
  let inv_k_f : Frac := if kFreeOf B0 B1 B2 B3 mask == 0 then ⟨0, 1⟩ else ⟨1, kFreeOf B0 B1 B2 B3 mask⟩
  have hinv_k_v : inv_k_f.Valid := by
    simp only [inv_k_f]; split_ifs with h
    · exact Frac.mk_valid (by norm_num)
    · have hne : kFreeOf B0 B1 B2 B3 mask ≠ 0 := fun hz => by simp [hz] at h
      unfold Frac.Valid; exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero hne)
  have hS4_free : inv_k_f.toReal * t ^ 2 ≤ ∑ p ∈ Lfree, (ctx.c p) ^ 4 := by
    by_cases hk0 : kFreeOf B0 B1 B2 B3 mask = 0
    · have hL0 : Lfree = ∅ := Finset.card_eq_zero.mp (hkfree_eq.trans hk0)
      have ht0 : t = 0 := by simp [t, hL0]
      rw [ht0, zero_pow (by norm_num), mul_zero]
      exact Finset.sum_nonneg fun p _ => by
        rw [show (ctx.c p) ^ 4 = ((ctx.c p) ^ 2) ^ 2 by ring]; exact sq_nonneg _
    · have hne : (kFreeOf B0 B1 B2 B3 mask == 0) = false := by simp [hk0]
      simp only [inv_k_f, hne, Bool.false_eq_true, ↓reduceIte, Frac.toReal]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Lfree (fun _ => (1 : ℝ)) (fun p => (ctx.c p) ^ 2)
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hkfree_eq] at hcs
      have h4 : ∀ p, ((ctx.c p) ^ 2) ^ 2 = (ctx.c p) ^ 4 := fun p => by ring
      simp_rw [h4] at hcs
      have hkpos : (0 : ℝ) < (kFreeOf B0 B1 B2 B3 mask : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
      push_cast; rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hkpos]; linarith
  have hS4L_ge : (∑ j ∈ Icap, (ctx.c (ps j)) ^ 4) + inv_k_f.toReal * t ^ 2 ≤ S4L := by
    have hs := Finset.sum_sdiff hunion_sub (f := fun p => (ctx.c p) ^ 4)
    rw [Finset.sum_union hdisj_SI, Finset.sum_image (fun a _ b _ h => hps_inj h)] at hs
    have hnn0 : 0 ≤ ∑ p ∈ S13.erase 0, (ctx.c p) ^ 4 :=
      Finset.sum_nonneg fun p _ => by
        rw [show (ctx.c p) ^ 4 = ((ctx.c p) ^ 2) ^ 2 by ring]; exact sq_nonneg _
    linarith
  have hz0_nn : 0 ≤ z0 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz0_le : z0 ≤ s13.toReal := by linarith [sq_nonneg (ctx.c uPt)]
  -- Match the 4-term `s2_lo`, `s2_hi`, `J_d2_hi`, `J_q4_lo`, `cap_min`, `cap_min_D` bounds!
  have hge := hb.x_ge_A
  have hunc := hb.unclamp
  have hA_nn_all : 0 ≤ A0 ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 :=
    ⟨hb.hA0_nn, le_trans hb.hA0_nn hb.hA01, le_trans hb.hA0_nn (le_trans hb.hA01 hb.hA12),
     le_trans hb.hA0_nn (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23))⟩
  have hB_le_all : B0 ≤ 32 ∧ B1 ≤ 32 ∧ B2 ≤ 32 ∧ B3 ≤ 32 :=
    ⟨le_trans hb.hB01 (le_trans hb.hB12 (le_trans hb.hB23 hb.hB3_le)),
     le_trans hb.hB12 (le_trans hb.hB23 hb.hB3_le), le_trans hb.hB23 hb.hB3_le, hb.hB3_le⟩
  have hsq_bounds : ∀ j : Fin 4, j ∈ Icap →
      let As : Fin 4 → Int := ![A0, A1, A2, A3]
      ((As j : ℝ) ^ 2 / 16384 ≤ (ctx.c (ps j)) ^ 2) ∧ ((ctx.c (ps j)) ^ 2 ≤ (Bs j : ℝ) ^ 2 / 16384) := by
    intro j hj
    have hlt32 : Bs j < 32 := (Finset.mem_filter.mp hj).2.2
    fin_cases j
    · dsimp [Bs, ps] at hlt32 ⊢
      have h1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A0 : ℝ) / 128 by have : (0 : ℝ) ≤ (A0 : ℝ) := (by exact_mod_cast hA_nn_all.1); linarith) hge.1 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.1 hlt32) 2
      simp only [StateCtx.x, sq_abs] at h1 h2
      rw [show (⟨13, by omega⟩ : Fin 255) = 13 from rfl] at h1 h2
      have ha : ((A0 : ℝ) / 128) ^ 2 = (A0 : ℝ) ^ 2 / 16384 := by ring
      have hb' : ((B0 : ℝ) / 128) ^ 2 = (B0 : ℝ) ^ 2 / 16384 := by ring
      constructor <;> linarith
    · dsimp [Bs, ps] at hlt32 ⊢
      have h1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A1 : ℝ) / 128 by have : (0 : ℝ) ≤ (A1 : ℝ) := (by exact_mod_cast hA_nn_all.2.1); linarith) hge.2.1 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.1 hlt32) 2
      simp only [StateCtx.x, sq_abs] at h1 h2
      rw [show (⟨14, by omega⟩ : Fin 255) = 14 from rfl] at h1 h2
      have ha : ((A1 : ℝ) / 128) ^ 2 = (A1 : ℝ) ^ 2 / 16384 := by ring
      have hb' : ((B1 : ℝ) / 128) ^ 2 = (B1 : ℝ) ^ 2 / 16384 := by ring
      constructor <;> linarith
    · dsimp [Bs, ps] at hlt32 ⊢
      have h1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A2 : ℝ) / 128 by have : (0 : ℝ) ≤ (A2 : ℝ) := (by exact_mod_cast hA_nn_all.2.2.1); linarith) hge.2.2.1 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.2.1 hlt32) 2
      simp only [StateCtx.x, sq_abs] at h1 h2
      rw [show (⟨15, by omega⟩ : Fin 255) = 15 from rfl] at h1 h2
      have ha : ((A2 : ℝ) / 128) ^ 2 = (A2 : ℝ) ^ 2 / 16384 := by ring
      have hb' : ((B2 : ℝ) / 128) ^ 2 = (B2 : ℝ) ^ 2 / 16384 := by ring
      constructor <;> linarith
    · dsimp [Bs, ps] at hlt32 ⊢
      have h1 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (A3 : ℝ) / 128 by have : (0 : ℝ) ≤ (A3 : ℝ) := (by exact_mod_cast hA_nn_all.2.2.2); linarith) hge.2.2.2 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hunc.2.2.2 hlt32) 2
      simp only [StateCtx.x, sq_abs] at h1 h2
      rw [show (⟨16, by omega⟩ : Fin 255) = 16 from rfl] at h1 h2
      have ha : ((A3 : ℝ) / 128) ^ 2 = (A3 : ℝ) ^ 2 / 16384 := by ring
      have hb' : ((B3 : ℝ) / 128) ^ 2 = (B3 : ℝ) ^ 2 / 16384 := by ring
      constructor <;> linarith
  -- Reusable 4-term `minQuad1d` sum bound over `Icap`!
  have hcap_min_lb : ∀ (Af Bf : Frac) (hAfv : Af.Valid) (hAfn : 0 < Af.n) (hBfv : Bf.Valid),
      let ic0 := bitSet mask 0 && decide (B0 < 32); let ic1 := bitSet mask 1 && decide (B1 < 32)
      let ic2 := bitSet mask 2 && decide (B2 < 32); let ic3 := bitSet mask 3 && decide (B3 < 32)
      let cap_f :=
        (if ic0 then minQuad1d Af Bf ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
        (if ic1 then minQuad1d Af Bf ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
        (if ic2 then minQuad1d Af Bf ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
        (if ic3 then minQuad1d Af Bf ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
      cap_f.Valid ∧ cap_f.toReal ≤ ∑ j ∈ Icap, (Af.toReal * (ctx.c (ps j)) ^ 4 + Bf.toReal * (ctx.c (ps j)) ^ 2) := by
    intro Af Bf hAfv hAfn hBfv ic0 ic1 ic2 ic3 cap_f
    have h16 : ∀ n : Int, (⟨n, 16384⟩ : Frac).Valid := fun _ => Frac.mk_valid (by norm_num)
    have hpt : ∀ (j : Fin 4) (A B : Int) (ic : Bool),
        (ic = true ↔ j ∈ Icap) →
        (j ∈ Icap → ((A : ℝ) ^ 2 / 16384 ≤ (ctx.c (ps j)) ^ 2 ∧ (ctx.c (ps j)) ^ 2 ≤ (B : ℝ) ^ 2 / 16384)) →
        let term := if ic then minQuad1d Af Bf ⟨A * A, 16384⟩ ⟨B * B, 16384⟩ else Frac.ofInt 0
        term.Valid ∧ term.toReal ≤ (if j ∈ Icap then Af.toReal * (ctx.c (ps j)) ^ 4 + Bf.toReal * (ctx.c (ps j)) ^ 2 else 0) := by
      intro j A B ic hic hbd
      by_cases hj : j ∈ Icap
      · have hict : ic = true := hic.mpr hj
        simp only [hict, hj, ↓reduceIte]
        obtain ⟨hlo, hhi⟩ := hbd hj
        have hlo' : (⟨A * A, 16384⟩ : Frac).toReal ≤ (ctx.c (ps j)) ^ 2 := by
          simp only [Frac.toReal]; push_cast; linarith
        have hhi' : (ctx.c (ps j)) ^ 2 ≤ (⟨B * B, 16384⟩ : Frac).toReal := by
          simp only [Frac.toReal]; push_cast; linarith
        obtain ⟨hv, hle⟩ := sound_minQuad1d hAfv hAfn hBfv (h16 _) (h16 _) hlo' hhi'
        refine ⟨hv, ?_⟩
        have h4 : ((ctx.c (ps j)) ^ 2) ^ 2 = (ctx.c (ps j)) ^ 4 := by ring
        rw [h4] at hle; exact hle
      · have hicf : ic = false := Bool.eq_false_iff.mpr fun ht => hj (hic.mp ht)
        simp only [hicf, hj, Bool.false_eq_true, ↓reduceIte]
        exact ⟨Frac.valid_ofInt 0, by rw [Frac.toReal_ofInt]; norm_num⟩
    have hm0 : bitSet mask 0 = decide (ps 0 ∈ L) := hmask_def 0
    have hm1 : bitSet mask 1 = decide (ps 1 ∈ L) := hmask_def 1
    have hm2 : bitSet mask 2 = decide (ps 2 ∈ L) := hmask_def 2
    have hm3 : bitSet mask 3 = decide (ps 3 ∈ L) := hmask_def 3
    have hic0 : ic0 = true ↔ (0 : Fin 4) ∈ Icap := by simp [ic0, hm0, Icap, Bs]
    have hic1 : ic1 = true ↔ (1 : Fin 4) ∈ Icap := by simp [ic1, hm1, Icap, Bs]
    have hic2 : ic2 = true ↔ (2 : Fin 4) ∈ Icap := by simp [ic2, hm2, Icap, Bs]
    have hic3 : ic3 = true ↔ (3 : Fin 4) ∈ Icap := by simp [ic3, hm3, Icap, Bs]
    obtain ⟨v0, l0⟩ := hpt 0 A0 B0 ic0 hic0 (fun h => hsq_bounds 0 h)
    obtain ⟨v1, l1⟩ := hpt 1 A1 B1 ic1 hic1 (fun h => hsq_bounds 1 h)
    obtain ⟨v2, l2⟩ := hpt 2 A2 B2 ic2 hic2 (fun h => hsq_bounds 2 h)
    obtain ⟨v3, l3⟩ := hpt 3 A3 B3 ic3 hic3 (fun h => hsq_bounds 3 h)
    refine ⟨Frac.valid_add (Frac.valid_add (Frac.valid_add v0 v1) v2) v3, ?_⟩
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_add v0 v1) v2) v3,
        Frac.toReal_add (Frac.valid_add v0 v1) v2, Frac.toReal_add v0 v1]
    have hsum : ∑ j ∈ Icap, (Af.toReal * (ctx.c (ps j)) ^ 4 + Bf.toReal * (ctx.c (ps j)) ^ 2) =
        ∑ j : Fin 4, if j ∈ Icap then Af.toReal * (ctx.c (ps j)) ^ 4 + Bf.toReal * (ctx.c (ps j)) ^ 2 else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hsum, Fin.sum_univ_four]; linarith
  -- Match `s2_lo ≤ zI ≤ s2_hi`!
  let ic0 := bitSet mask 0 && decide (B0 < 32); let ic1 := bitSet mask 1 && decide (B1 < 32)
  let ic2 := bitSet mask 2 && decide (B2 < 32); let ic3 := bitSet mask 3 && decide (B3 < 32)
  let s2_lo_f : Frac :=
    ⟨(if ic0 then A0 * A0 else 0) + (if ic1 then A1 * A1 else 0) +
     (if ic2 then A2 * A2 else 0) + (if ic3 then A3 * A3 else 0), 16384⟩
  let s2_hi_f : Frac :=
    ⟨(if ic0 then B0 * B0 else 0) + (if ic1 then B1 * B1 else 0) +
     (if ic2 then B2 * B2 else 0) + (if ic3 then B3 * B3 else 0), 16384⟩
  have hs2lov : s2_lo_f.Valid := Frac.mk_valid (by norm_num)
  have hs2hiv : s2_hi_f.Valid := Frac.mk_valid (by norm_num)
  have hzI_bounds : s2_lo_f.toReal ≤ zI ∧ zI ≤ s2_hi_f.toReal := by
    have hzI_sum : zI = ∑ j : Fin 4, if j ∈ Icap then (ctx.c (ps j)) ^ 2 else 0 := by
      simp only [zI]; rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hzI_sum, Fin.sum_univ_four]
    have hpt : ∀ (j : Fin 4) (A B : Int) (ic : Bool),
        (ic = true ↔ j ∈ Icap) →
        (j ∈ Icap → ((A : ℝ) ^ 2 / 16384 ≤ (ctx.c (ps j)) ^ 2 ∧ (ctx.c (ps j)) ^ 2 ≤ (B : ℝ) ^ 2 / 16384)) →
        (((if ic then A * A else 0 : Int) : ℝ) / 16384 ≤ (if j ∈ Icap then (ctx.c (ps j)) ^ 2 else 0)) ∧
        ((if j ∈ Icap then (ctx.c (ps j)) ^ 2 else 0) ≤ ((if ic then B * B else 0 : Int) : ℝ) / 16384) := by
      intro j A B ic hic hbd
      by_cases hj : j ∈ Icap
      · simp only [hic.mpr hj, hj, ↓reduceIte]; push_cast; exact ⟨by linarith [(hbd hj).1], by linarith [(hbd hj).2]⟩
      · have hcf : ic = false := Bool.eq_false_iff.mpr fun ht => hj (hic.mp ht)
        simp [hcf, hj]
    have hm0 : bitSet mask 0 = decide (ps 0 ∈ L) := hmask_def 0
    have hm1 : bitSet mask 1 = decide (ps 1 ∈ L) := hmask_def 1
    have hm2 : bitSet mask 2 = decide (ps 2 ∈ L) := hmask_def 2
    have hm3 : bitSet mask 3 = decide (ps 3 ∈ L) := hmask_def 3
    obtain ⟨l0, u0⟩ := hpt 0 A0 B0 ic0 (by simp [ic0, hm0, Icap, Bs]) (fun h => hsq_bounds 0 h)
    obtain ⟨l1, u1⟩ := hpt 1 A1 B1 ic1 (by simp [ic1, hm1, Icap, Bs]) (fun h => hsq_bounds 1 h)
    obtain ⟨l2, u2⟩ := hpt 2 A2 B2 ic2 (by simp [ic2, hm2, Icap, Bs]) (fun h => hsq_bounds 2 h)
    obtain ⟨l3, u3⟩ := hpt 3 A3 B3 ic3 (by simp [ic3, hm3, Icap, Bs]) (fun h => hsq_bounds 3 h)
    push_cast at l0 u0 l1 u1 l2 u2 l3 u3
    simp only [s2_lo_f, s2_hi_f, Frac.toReal]; push_cast; constructor <;> linarith
  -- Match `u_q4_min`, `J_q4_lo`, `J_d2_hi`, `tail_mult` for Methods 1 & 2!
  let uq_raw_f := Frac.max (Frac.ofInt 0) (⟨1, 16⟩ - s13)
  let u_q4_min_f := uq_raw_f * uq_raw_f
  have h16v : (⟨1, 16⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have huqv : uq_raw_f.Valid := Frac.valid_max (Frac.valid_ofInt 0) (Frac.valid_sub h16v hs13v)
  have huq4v : u_q4_min_f.Valid := Frac.valid_mul huqv huqv
  have hu_q4_le : u_q4_min_f.toReal ≤ (|ctx.c uPt| - 1 / 4) ^ 2 * (|ctx.c uPt| + 1 / 4) ^ 2 := by
    have h1 : uq_raw_f.toReal = max 0 (1 / 16 - s13.toReal) := by
      simp only [uq_raw_f]
      rw [Frac.toReal_max (Frac.valid_ofInt 0) (Frac.valid_sub h16v hs13v),
          Frac.toReal_ofInt, Frac.toReal_sub h16v hs13v]; simp [Frac.toReal]
    have h2 : u_q4_min_f.toReal = (max 0 (1 / 16 - s13.toReal)) ^ 2 := by
      simp only [u_q4_min_f]; rw [Frac.toReal_mul, h1]; ring
    rw [h2]
    have hfac : (|ctx.c uPt| - 1 / 4) ^ 2 * (|ctx.c uPt| + 1 / 4) ^ 2 = (1 / 16 - (ctx.c uPt) ^ 2) ^ 2 := by
      rw [← sq_abs (ctx.c uPt)]; ring
    rw [hfac]
    have hcu_le : (ctx.c uPt) ^ 2 ≤ s13.toReal := by linarith
    by_cases hp : 0 ≤ 1 / 16 - s13.toReal
    · rw [max_eq_right hp]; exact pow_le_pow_left₀ hp (by linarith) 2
    · rw [max_eq_left (le_of_not_ge hp), zero_pow (by norm_num)]; exact sq_nonneg _
  let J_q4_lo_f : Frac :=
    ⟨(if !bitSet mask 0 && decide (B0 < 32) then (1024 - B0 * B0) * (1024 - B0 * B0) else 0) +
     (if !bitSet mask 1 && decide (B1 < 32) then (1024 - B1 * B1) * (1024 - B1 * B1) else 0) +
     (if !bitSet mask 2 && decide (B2 < 32) then (1024 - B2 * B2) * (1024 - B2 * B2) else 0) +
     (if !bitSet mask 3 && decide (B3 < 32) then (1024 - B3 * B3) * (1024 - B3 * B3) else 0), 16384 * 16384⟩
  let J_d2_hi_f : Frac :=
    ⟨(if !bitSet mask 0 then (32 - A0) * (32 - A0) else 0) +
     (if !bitSet mask 1 then (32 - A1) * (32 - A1) else 0) +
     (if !bitSet mask 2 then (32 - A2) * (32 - A2) else 0) +
     (if !bitSet mask 3 then (32 - A3) * (32 - A3) else 0), 16384⟩
  let tail_mult_f : Frac := ⟨(A3 + 32) * (A3 + 32), 16384⟩
  have hJq4v : J_q4_lo_f.Valid := Frac.mk_valid (by norm_num)
  have hJd2v : J_d2_hi_f.Valid := Frac.mk_valid (by norm_num)
  have htmv : tail_mult_f.Valid := Frac.mk_valid (by norm_num)
  have htm_nn : 0 ≤ tail_mult_f.toReal := by
    simp only [tail_mult_f, Frac.toReal]; push_cast
    have : ((A3 : ℝ) + 32) * ((A3 : ℝ) + 32) = ((A3 : ℝ) + 32) ^ 2 := by ring
    rw [this]; positivity
  -- Unified out-of-L quartic lower bound for Method 1 & Method 2!
  let Jset := Finset.univ.filter fun j : Fin 4 => ps j ∉ L
  let Special := insert uPt (Jset.image ps)
  have hSpec_sub : Special ⊆ Finset.univ \ L := by
    intro q hq
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hI
    · exact huL
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI; exact (Finset.mem_filter.mp hj).2
  have hu_not_J : uPt ∉ Jset.image ps := by
    intro h; obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h; exact hps_ne_u j hj
  have hJ_q4_sum : J_q4_lo_f.toReal ≤ ∑ j ∈ Jset, (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 := by
    have hsum : ∑ j ∈ Jset, (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 =
        ∑ j : Fin 4, if ps j ∉ L then (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 else 0 := by
      rw [← Finset.sum_filter]
    rw [hsum, Fin.sum_univ_four]
    have hpt : ∀ (j : Fin 4) (B : Int), (B < 32 → |ctx.c (ps j)| ≤ (B : ℝ) / 128) →
        (((if !bitSet mask j.val && decide (B < 32) then (1024 - B * B) * (1024 - B * B) else 0 : Int) : ℝ) / (16384 * 16384)) ≤
          if ps j ∉ L then (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 else 0 := by
      intro j B hu
      have hb_eq : bitSet mask j.val = decide (ps j ∈ L) := hmask_def j
      by_cases hjL : ps j ∈ L
      · simp [hb_eq, hjL]
      · simp only [hb_eq, hjL, decide_false, Bool.not_false, Bool.true_and, not_false_eq_true, ↓reduceIte]
        by_cases hB : B < 32
        · simp only [hB, decide_true, ↓reduceIte]; push_cast
          have hy := hu hB
          have hB4 : (B : ℝ) / 128 < 1 / 4 := by have : (B : ℝ) < 32 := (by exact_mod_cast hB); linarith
          have hB0_nn' : (0 : ℝ) ≤ (B : ℝ) / 128 := le_trans (abs_nonneg _) hy
          have hsq : |ctx.c (ps j)| ^ 2 ≤ ((B : ℝ) / 128) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
          have hnn : 0 ≤ 1 / 16 - ((B : ℝ) / 128) ^ 2 := by
            have : ((B : ℝ) / 128) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hB0_nn' (le_of_lt hB4) 2
            linarith
          have h2 : (1 / 16 - ((B : ℝ) / 128) ^ 2) ^ 2 ≤ (1 / 16 - |ctx.c (ps j)| ^ 2) ^ 2 :=
            pow_le_pow_left₀ hnn (by linarith) 2
          have hid : (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 = (1 / 16 - |ctx.c (ps j)| ^ 2) ^ 2 := by ring
          have hidB : (1024 - (B : ℝ) * B) * (1024 - (B : ℝ) * B) / (16384 * 16384) = (1 / 16 - ((B : ℝ) / 128) ^ 2) ^ 2 := by ring
          rw [hid, hidB]; exact h2
        · simp only [hB, decide_false, Bool.false_eq_true, ↓reduceIte, Int.cast_zero, zero_div]
          positivity
    have p0 := hpt 0 B0 hunc.1; have p1 := hpt 1 B1 hunc.2.1
    have p2 := hpt 2 B2 hunc.2.2.1; have p3 := hpt 3 B3 hunc.2.2.2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at p0 p1 p2
    rw [show ((3 : Fin 4) : Nat) = 3 from rfl] at p3
    push_cast at p0 p1 p2 p3
    rw [show (16384 : ℝ) * 16384 = 268435456 by norm_num] at p0 p1 p2 p3
    simp only [J_q4_lo_f, Frac.toReal]; push_cast; linarith
  -- Pointwise Method 1 excess inequality on `univ \ L`:
  have hM1_out : u_q4_min_f.toReal + J_q4_lo_f.toReal +
      tail_mult_f.toReal * (2541 / 10000 - 1 / 16 - J_d2_hi_f.toReal - S2L) ≤
      ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 := by
    obtain ⟨_, hD2_eq, _⟩ := lagrangian_quartic_mub_identities hL ctx.hunit
    dsimp only at hD2_eq
    have hLout_L := ctx.hLout L hL
    have hD2_ge : 2541 / 10000 - S2L ≤ ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 := by
      change ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 = (60 - ∑ q ∈ Finset.univ \ L, |ctx.c q|) / 2 - S2L at hD2_eq
      change ∑ q ∈ Finset.univ \ L, |ctx.c q| ≤ 594918 / 10000 at hLout_L
      linarith
    have htail_nn : ∀ q ∈ (Finset.univ \ L) \ Special,
        0 ≤ (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 - tail_mult_f.toReal * (|ctx.c q| - 1 / 4) ^ 2 := by
      intro q hq
      have hqL : q ∉ L := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hq).1).2
      have hqSp : q ∉ Special := (Finset.mem_sdiff.mp hq).2
      have hq0 : q ≠ 0 := fun h0 => hqL (h0 ▸ hL.1)
      have hmemU : q ∈ Finset.univ.erase (0 : PauliIdx 4) := Finset.mem_erase.mpr ⟨hq0, Finset.mem_univ _⟩
      have hex_i : ∃ i : Fin 255, ctx.idx i = q := by
        have himg : Finset.image ctx.idx Finset.univ = Finset.univ.erase (0 : PauliIdx 4) := by
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro p hp; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp; exact Finset.mem_erase.mpr ⟨ctx.idx_ne0 i, Finset.mem_univ _⟩
          · rw [Finset.card_image_of_injective _ ctx.idx_inj, Finset.card_fin, card_PauliIdx4_erase_zero_nat]
        rw [← himg] at hmemU; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmemU; exact ⟨i, hi⟩
      obtain ⟨i, rfl⟩ := hex_i
      have hi17 : 17 ≤ i.val := by
        by_contra hlt; push Not at hlt
        by_cases hi13 : i.val < 13
        · have hmZ : ctx.idx i ∈ insert uPt S13 := by
            rw [← hZ14_eq]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨i.val, hi13⟩, Finset.mem_univ _, rfl⟩)
          rcases Finset.mem_insert.mp hmZ with heq | hS
          · exact hqSp (heq ▸ Finset.mem_insert_self _ _)
          · exact hqL (hS13_sub hS)
        · have hj4 : i.val - 13 < 4 := by omega
          let j : Fin 4 := ⟨i.val - 13, hj4⟩
          have hpsj : ps j = ctx.idx i := by simp only [ps, j]; congr 1; apply Fin.ext; dsimp; omega
          exact hqSp (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpsj ▸ hqL⟩, hpsj⟩))
      have hgeA3 : (A3 : ℝ) / 128 ≤ |ctx.c (ctx.idx i)| :=
        le_trans hge.2.2.2 (ctx.idx_mono ⟨16, by omega⟩ i (Fin.le_iff_val_le_val.mpr (show 16 ≤ i.val by omega)))
      have htm_le : tail_mult_f.toReal ≤ (|ctx.c (ctx.idx i)| + 1 / 4) ^ 2 := by
        simp only [tail_mult_f, Frac.toReal]; push_cast
        have hA3_nn : (0 : ℝ) ≤ (A3 : ℝ) / 128 := by
          have : (0 : ℝ) ≤ (A3 : ℝ) := by exact_mod_cast hA_nn_all.2.2.2
          linarith
        have htm_eq : ((A3 : ℝ) + 32) * ((A3 : ℝ) + 32) / 16384 = ((A3 : ℝ) / 128 + 1 / 4) ^ 2 := by ring
        rw [htm_eq]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hfac : (|ctx.c (ctx.idx i)| - 1 / 4) ^ 2 * (|ctx.c (ctx.idx i)| + 1 / 4) ^ 2 -
          tail_mult_f.toReal * (|ctx.c (ctx.idx i)| - 1 / 4) ^ 2 =
          (|ctx.c (ctx.idx i)| - 1 / 4) ^ 2 * ((|ctx.c (ctx.idx i)| + 1 / 4) ^ 2 - tail_mult_f.toReal) := by ring
      rw [hfac]; exact mul_nonneg (sq_nonneg _) (by linarith)
    have hu_term : u_q4_min_f.toReal - tail_mult_f.toReal * (1 / 16) ≤
        (|ctx.c uPt| - 1 / 4) ^ 2 * (|ctx.c uPt| + 1 / 4) ^ 2 - tail_mult_f.toReal * (|ctx.c uPt| - 1 / 4) ^ 2 := by
      have hu_d2 : (|ctx.c uPt| - 1 / 4) ^ 2 ≤ 1 / 16 := by
        have h1 : (1 / 4 - |ctx.c uPt|) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg (ctx.c uPt)]) 2
        have heq : (|ctx.c uPt| - 1 / 4) ^ 2 = (1 / 4 - |ctx.c uPt|) ^ 2 := by ring
        linarith
      have := mul_le_mul_of_nonneg_left hu_d2 htm_nn
      linarith
    have hJ_term : J_q4_lo_f.toReal - tail_mult_f.toReal * J_d2_hi_f.toReal ≤
        ∑ j ∈ Jset, ((|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
          tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2) := by
      have hsum : ∑ j ∈ Jset, ((|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
            tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2) =
          ∑ j : Fin 4, if ps j ∉ L then ((|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
            tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2) else 0 := by rw [← Finset.sum_filter]
      rw [hsum, Fin.sum_univ_four]
      have hpt : ∀ (j : Fin 4) (A B : Int), 0 ≤ A → A ≤ A3 →
          (A : ℝ) / 128 ≤ |ctx.c (ps j)| → (B < 32 → |ctx.c (ps j)| ≤ (B : ℝ) / 128) →
          (((if !bitSet mask j.val && decide (B < 32) then (1024 - B * B) * (1024 - B * B) else 0 : Int) : ℝ) / (16384 * 16384)) -
            tail_mult_f.toReal * (((if !bitSet mask j.val then (32 - A) * (32 - A) else 0 : Int) : ℝ) / 16384) ≤
            if ps j ∉ L then ((|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
              tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2) else 0 := by
        intro j A B hAnn hAA3 hgeA hleB
        have hb_eq : bitSet mask j.val = decide (ps j ∈ L) := hmask_def j
        by_cases hjL : ps j ∈ L
        · simp [hb_eq, hjL]
        · simp only [hb_eq, hjL, decide_false, Bool.not_false, Bool.true_and, not_false_eq_true, ↓reduceIte]
          by_cases hy4 : |ctx.c (ps j)| ≤ 1 / 4
          · have hd2 : (|ctx.c (ps j)| - 1 / 4) ^ 2 ≤ ((32 - (A : ℝ)) * (32 - (A : ℝ))) / 16384 := by
              have h1 : (1 / 4 - |ctx.c (ps j)|) ^ 2 ≤ (1 / 4 - (A : ℝ) / 128) ^ 2 :=
                pow_le_pow_left₀ (by linarith) (by linarith) 2
              have he1 : (|ctx.c (ps j)| - 1 / 4) ^ 2 = (1 / 4 - |ctx.c (ps j)|) ^ 2 := by ring
              have he2 : (1 / 4 - (A : ℝ) / 128) ^ 2 = ((32 - (A : ℝ)) * (32 - (A : ℝ))) / 16384 := by ring
              linarith
            have hq4 : (((if decide (B < 32) then (1024 - B * B) * (1024 - B * B) else 0 : Int) : ℝ) / (16384 * 16384)) ≤
                (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 := by
              by_cases hB : B < 32
              · simp only [hB, decide_true, ↓reduceIte]; push_cast
                have hy := hleB hB
                have hB4 : (B : ℝ) / 128 < 1 / 4 := by have : (B : ℝ) < 32 := (by exact_mod_cast hB); linarith
                have hB0_nn' : (0 : ℝ) ≤ (B : ℝ) / 128 := le_trans (abs_nonneg _) hy
                have hsq : |ctx.c (ps j)| ^ 2 ≤ ((B : ℝ) / 128) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
                have hnn : 0 ≤ 1 / 16 - ((B : ℝ) / 128) ^ 2 := by
                  have : ((B : ℝ) / 128) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hB0_nn' (le_of_lt hB4) 2
                  linarith
                have hid : (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 = (1 / 16 - |ctx.c (ps j)| ^ 2) ^ 2 := by ring
                have hidB : (1024 - (B : ℝ) * B) * (1024 - (B : ℝ) * B) / (16384 * 16384) = (1 / 16 - ((B : ℝ) / 128) ^ 2) ^ 2 := by ring
                rw [hid, hidB]; exact pow_le_pow_left₀ hnn (by linarith) 2
              · simp only [hB, decide_false, Bool.false_eq_true, ↓reduceIte, Int.cast_zero, zero_div]; positivity
            have hm := mul_le_mul_of_nonneg_left hd2 htm_nn
            push_cast at hq4 ⊢; linarith
          · push Not at hy4
            have hB_not : ¬(B < 32) := fun hB => by
              have hy := hleB hB; have : (B : ℝ) < 32 := (by exact_mod_cast hB); linarith
            simp only [hB_not, decide_false, Bool.false_eq_true, ↓reduceIte, Int.cast_zero, zero_div]
            have htm_le : tail_mult_f.toReal ≤ (|ctx.c (ps j)| + 1 / 4) ^ 2 := by
              simp only [tail_mult_f, Frac.toReal]; push_cast
              have hA3_4 : (A3 : ℝ) / 128 ≤ 1 / 4 := le_trans hb.h3_lo (min_le_right _ _)
              have hA3_nn : (0 : ℝ) ≤ (A3 : ℝ) / 128 := by
                have : (0 : ℝ) ≤ (A3 : ℝ) := by exact_mod_cast hA_nn_all.2.2.2
                linarith
              have htm_eq : ((A3 : ℝ) + 32) * ((A3 : ℝ) + 32) / 16384 = ((A3 : ℝ) / 128 + 1 / 4) ^ 2 := by ring
              rw [htm_eq]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
            have hdiff_nn : 0 ≤ (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
                tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2 := by
              have hfac : (|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
                  tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2 =
                  (|ctx.c (ps j)| - 1 / 4) ^ 2 * ((|ctx.c (ps j)| + 1 / 4) ^ 2 - tail_mult_f.toReal) := by ring
              rw [hfac]; exact mul_nonneg (sq_nonneg _) (by linarith)
            have hd2_nn : 0 ≤ tail_mult_f.toReal * ((((32 - A) * (32 - A) : Int) : ℝ) / 16384) := by
              push_cast; have : (32 - (A : ℝ)) * (32 - (A : ℝ)) = (32 - (A : ℝ)) ^ 2 := by ring
              rw [this]; positivity
            linarith
      have p0 := hpt 0 A0 B0 hA_nn_all.1 (le_trans hb.hA01 (le_trans hb.hA12 hb.hA23)) hge.1 hunc.1
      have p1 := hpt 1 A1 B1 hA_nn_all.2.1 (le_trans hb.hA12 hb.hA23) hge.2.1 hunc.2.1
      have p2 := hpt 2 A2 B2 hA_nn_all.2.2.1 hb.hA23 hge.2.2.1 hunc.2.2.1
      have p3 := hpt 3 A3 B3 hA_nn_all.2.2.2 (le_refl _) hge.2.2.2 hunc.2.2.2
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at p0 p1 p2
      rw [show ((3 : Fin 4) : Nat) = 3 from rfl] at p3
      push_cast at p0 p1 p2 p3
      rw [show (16384 : ℝ) * 16384 = 268435456 by norm_num] at p0 p1 p2 p3
      rw [show J_q4_lo_f.toReal =
            (((if !bitSet mask 0 && decide (B0 < 32) then (1024 - B0 * B0) * (1024 - B0 * B0) else 0) +
              (if !bitSet mask 1 && decide (B1 < 32) then (1024 - B1 * B1) * (1024 - B1 * B1) else 0) +
              (if !bitSet mask 2 && decide (B2 < 32) then (1024 - B2 * B2) * (1024 - B2 * B2) else 0) +
              (if !bitSet mask 3 && decide (B3 < 32) then (1024 - B3 * B3) * (1024 - B3 * B3) else 0) : Int) : ℝ) / 268435456 from rfl,
          show J_d2_hi_f.toReal =
            (((if !bitSet mask 0 then (32 - A0) * (32 - A0) else 0) +
              (if !bitSet mask 1 then (32 - A1) * (32 - A1) else 0) +
              (if !bitSet mask 2 then (32 - A2) * (32 - A2) else 0) +
              (if !bitSet mask 3 then (32 - A3) * (32 - A3) else 0) : Int) : ℝ) / 16384 from rfl]
      push_cast
      have hdist : tail_mult_f.toReal *
          (((if !bitSet mask 0 = true then (32 - (A0 : ℝ)) * (32 - (A0 : ℝ)) else 0) +
            (if !bitSet mask 1 = true then (32 - (A1 : ℝ)) * (32 - (A1 : ℝ)) else 0) +
            (if !bitSet mask 2 = true then (32 - (A2 : ℝ)) * (32 - (A2 : ℝ)) else 0) +
            (if !bitSet mask 3 = true then (32 - (A3 : ℝ)) * (32 - (A3 : ℝ)) else 0)) / 16384) =
          tail_mult_f.toReal * ((if !bitSet mask 0 = true then (32 - (A0 : ℝ)) * (32 - (A0 : ℝ)) else 0) / 16384) +
          tail_mult_f.toReal * ((if !bitSet mask 1 = true then (32 - (A1 : ℝ)) * (32 - (A1 : ℝ)) else 0) / 16384) +
          tail_mult_f.toReal * ((if !bitSet mask 2 = true then (32 - (A2 : ℝ)) * (32 - (A2 : ℝ)) else 0) / 16384) +
          tail_mult_f.toReal * ((if !bitSet mask 3 = true then (32 - (A3 : ℝ)) * (32 - (A3 : ℝ)) else 0) / 16384) := by ring
      linarith
    have hsum_all := Finset.sum_sdiff hSpec_sub (f := fun q =>
      (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 - tail_mult_f.toReal * (|ctx.c q| - 1 / 4) ^ 2)
    conv_rhs at hsum_all => rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsp_sum : ∑ q ∈ Special, ((|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 -
          tail_mult_f.toReal * (|ctx.c q| - 1 / 4) ^ 2) =
        ((|ctx.c uPt| - 1 / 4) ^ 2 * (|ctx.c uPt| + 1 / 4) ^ 2 - tail_mult_f.toReal * (|ctx.c uPt| - 1 / 4) ^ 2) +
        ∑ j ∈ Jset, ((|ctx.c (ps j)| - 1 / 4) ^ 2 * (|ctx.c (ps j)| + 1 / 4) ^ 2 -
          tail_mult_f.toReal * (|ctx.c (ps j)| - 1 / 4) ^ 2) := by
      simp only [Special]; rw [Finset.sum_insert hu_not_J, Finset.sum_image (fun a _ b _ h => hps_inj h)]
    have hrest_nn : 0 ≤ ∑ q ∈ (Finset.univ \ L) \ Special,
        ((|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 - tail_mult_f.toReal * (|ctx.c q| - 1 / 4) ^ 2) :=
      Finset.sum_nonneg htail_nn
    have hD2_mul := mul_le_mul_of_nonneg_left hD2_ge htm_nn
    have hexp : tail_mult_f.toReal * (2541 / 10000 - 1 / 16 - J_d2_hi_f.toReal - S2L) =
        tail_mult_f.toReal * (2541 / 10000 - S2L) - tail_mult_f.toReal * (1 / 16) -
        tail_mult_f.toReal * J_d2_hi_f.toReal := by ring
    linarith
  -- Now dispatch on `m ∈ {1, 2, 3, 4}`!
  have h8v : (⟨1, 8⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have h64v : (⟨1, 64⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have h128v : (⟨1, 128⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  unfold checkMethod at hok
  dsimp only at hok
  match m with
  | 1 =>
    obtain ⟨hF4_eq, _, _⟩ := lagrangian_quartic_mub_identities hL ctx.hunit
    dsimp only at hF4_eq
    change pauliMoment4 4 ψ - 31 / 16 = (S4L - S2L / 8) +
      ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 at hF4_eq
    have hexcess_le : (S4L - S2L / 8) + ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 ≤ 0 := by
      linarith [ctx.hF4]
    let beta_f : Frac := ⟨1, 8⟩ + tail_mult_f
    have hbetav : beta_f.Valid := Frac.valid_add h8v htmv
    have hbeta_r : beta_f.toReal = 1 / 8 + tail_mult_f.toReal := by
      rw [Frac.toReal_add h8v htmv]; simp [Frac.toReal]
    obtain ⟨hcapv, hcap_le⟩ := hcap_min_lb (Frac.ofInt 1) (-beta_f) (Frac.valid_ofInt 1) (by norm_num [Frac.ofInt]) (Frac.valid_neg hbetav)
    let cap1_f :=
      (if ic0 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
      (if ic1 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
      (if ic2 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
      (if ic3 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
    have hD2v : D2_MIN.Valid := valid_D2_MIN
    have hD2sub_v : (D2_MIN - ⟨1, 16⟩ - J_d2_hi_f).Valid := Frac.valid_sub (Frac.valid_sub hD2v h16v) hJd2v
    have hC1v : (cap1_f - beta_f * s13 + u_q4_min_f + J_q4_lo_f + tail_mult_f * (D2_MIN - ⟨1, 16⟩ - J_d2_hi_f)).Valid :=
      Frac.valid_add (Frac.valid_add (Frac.valid_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v) hJq4v)
        (Frac.valid_mul htmv hD2sub_v)
    have hpos : 0 < inv_k_f.toReal * t ^ 2 + (-beta_f).toReal * t +
        (cap1_f - beta_f * s13 + u_q4_min_f + J_q4_lo_f + tail_mult_f * (D2_MIN - ⟨1, 16⟩ - J_d2_hi_f)).toReal := by
      cases is_inf
      · simp only [Bool.false_eq_true, ↓reduceIte] at hok ht_range
        exact sound_quadPosOn hinv_k_v (Frac.valid_neg hbetav) hC1v huv hvv ht_range.1 ht_range.2 hok
      · simp only [↓reduceIte] at hok ht_range
        exact sound_quadPosGe hinv_k_v (Frac.valid_neg hbetav) hC1v huv ht_range hok
    have hD2sub_r : (D2_MIN - ⟨1, 16⟩ - J_d2_hi_f).toReal = 2541 / 10000 - 1 / 16 - J_d2_hi_f.toReal := by
      rw [Frac.toReal_sub (Frac.valid_sub hD2v h16v) hJd2v, Frac.toReal_sub hD2v h16v]
      have hD2_r : D2_MIN.toReal = 2541 / 10000 := by simp [D2_MIN, Frac.toReal]
      have h16_r : (⟨1, 16⟩ : Frac).toReal = 1 / 16 := by simp [Frac.toReal]
      rw [hD2_r, h16_r]
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v) hJq4v)
          (Frac.valid_mul htmv hD2sub_v),
        Frac.toReal_add (Frac.valid_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v) hJq4v,
        Frac.toReal_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v,
        Frac.toReal_sub hcapv (Frac.valid_mul hbetav hs13v),
        Frac.toReal_mul beta_f s13, Frac.toReal_mul tail_mult_f _, Frac.toReal_neg, hD2sub_r] at hpos
    change cap1_f.toReal ≤ ∑ j ∈ Icap, ((Frac.ofInt 1).toReal * (ctx.c (ps j)) ^ 4 + (-beta_f).toReal * (ctx.c (ps j)) ^ 2) at hcap_le
    rw [Frac.toReal_ofInt, Frac.toReal_neg] at hcap_le
    simp only [Int.cast_one, one_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hcap_le
    change cap1_f.toReal ≤ (∑ j ∈ Icap, (ctx.c (ps j)) ^ 4) + -(beta_f.toReal * zI) at hcap_le
    have hbeta_z0 : beta_f.toReal * z0 ≤ beta_f.toReal * s13.toReal :=
      mul_le_mul_of_nonneg_left hz0_le (by linarith)
    have hlin_id : beta_f.toReal * t + beta_f.toReal * zI + beta_f.toReal * z0 =
        S2L / 8 + tail_mult_f.toReal * S2L := by
      rw [hbeta_r, hS2L_eq]; change _ = (z0 + zI + t) / 8 + tail_mult_f.toReal * (z0 + zI + t); ring
    have htm_id : tail_mult_f.toReal * (2541 / 10000 - 1 / 16 - J_d2_hi_f.toReal - S2L) =
        tail_mult_f.toReal * (2541 / 10000 - 1 / 16 - J_d2_hi_f.toReal) - tail_mult_f.toReal * S2L := by ring
    linarith
  | 2 =>
    obtain ⟨hF4_eq, _, _⟩ := lagrangian_quartic_mub_identities hL ctx.hunit
    dsimp only at hF4_eq
    change pauliMoment4 4 ψ - 31 / 16 = (S4L - S2L / 8) +
      ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 at hF4_eq
    have hexcess_le : (S4L - S2L / 8) + ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 ≤ 0 := by
      linarith [ctx.hF4]
    have hout_ge : u_q4_min_f.toReal + J_q4_lo_f.toReal ≤
        ∑ q ∈ Finset.univ \ L, (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2 := by
      have hsp := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun q => (|ctx.c q| - 1 / 4) ^ 2 * (|ctx.c q| + 1 / 4) ^ 2) hSpec_sub fun _ _ _ => by positivity
      simp only [Special] at hsp
      rw [Finset.sum_insert hu_not_J, Finset.sum_image (fun a _ b _ h => hps_inj h)] at hsp
      linarith
    let beta_f : Frac := ⟨1, 8⟩
    have hbetav : beta_f.Valid := h8v
    obtain ⟨hcapv, hcap_le⟩ := hcap_min_lb (Frac.ofInt 1) (-beta_f) (Frac.valid_ofInt 1) (by norm_num [Frac.ofInt]) (Frac.valid_neg hbetav)
    let cap2_f :=
      (if ic0 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
      (if ic1 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
      (if ic2 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
      (if ic3 then minQuad1d (Frac.ofInt 1) (-beta_f) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
    have hCv : (cap2_f - beta_f * s13 + u_q4_min_f + J_q4_lo_f).Valid :=
      Frac.valid_add (Frac.valid_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v) hJq4v
    have hpos : 0 < inv_k_f.toReal * t ^ 2 + (-beta_f).toReal * t +
        (cap2_f - beta_f * s13 + u_q4_min_f + J_q4_lo_f).toReal := by
      cases is_inf
      · simp only [Bool.false_eq_true, ↓reduceIte] at hok ht_range
        exact sound_quadPosOn hinv_k_v (Frac.valid_neg hbetav) hCv huv hvv ht_range.1 ht_range.2 hok
      · simp only [↓reduceIte] at hok ht_range
        exact sound_quadPosGe hinv_k_v (Frac.valid_neg hbetav) hCv huv ht_range hok
    rw [Frac.toReal_add (Frac.valid_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v) hJq4v,
        Frac.toReal_add (Frac.valid_sub hcapv (Frac.valid_mul hbetav hs13v)) huq4v,
        Frac.toReal_sub hcapv (Frac.valid_mul hbetav hs13v), Frac.toReal_mul beta_f s13, Frac.toReal_neg] at hpos
    change cap2_f.toReal ≤ ∑ j ∈ Icap, ((Frac.ofInt 1).toReal * (ctx.c (ps j)) ^ 4 + (-beta_f).toReal * (ctx.c (ps j)) ^ 2) at hcap_le
    rw [Frac.toReal_ofInt, Frac.toReal_neg] at hcap_le
    simp only [Int.cast_one, one_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hcap_le
    have hb8 : beta_f.toReal = 1 / 8 := by simp [beta_f, Frac.toReal]
    rw [hb8] at hpos hcap_le
    change cap2_f.toReal ≤ (∑ j ∈ Icap, (ctx.c (ps j)) ^ 4) + -(1 / 8 * zI) at hcap_le
    linarith
  | 3 | 4 =>
    cases is_inf
    · simp only [Bool.false_eq_true, ↓reduceIte] at hok ht_range
      have hvalD := val_D_le_excess hL ctx.hunit huL
      dsimp only at hvalD
      change (2 * S4L - S2L / 8 - S2L ^ 2 / 16) + (max 0 (1 - S2L - 16 * (ctx.c uPt) ^ 2)) ^ 2 / 128 ≤
        pauliMoment4 4 ψ - 31 / 16 at hvalD
      have hD_le : (2 * S4L - S2L / 8 - S2L ^ 2 / 16) + (max 0 (1 - S2L - 16 * (ctx.c uPt) ^ 2)) ^ 2 / 128 ≤ 0 := by
        linarith [ctx.hF4]
      let z_lo_f := s2_lo_f
      let z_hi_f := s13 + s2_hi_f
      have hzhiv : z_hi_f.Valid := Frac.valid_add hs13v hs2hiv
      have hz_range : z_lo_f.toReal ≤ z ∧ z ≤ z_hi_f.toReal := by
        rw [Frac.toReal_add hs13v hs2hiv]; constructor <;> linarith [hzI_bounds]
      let lin_z_f := ⟨1, 8⟩ + (z_lo_f + z_hi_f + Frac.ofInt 2 * u) * ⟨1, 16⟩
      have hlinzv : lin_z_f.Valid :=
        Frac.valid_add h8v (Frac.valid_mul (Frac.valid_add (Frac.valid_add hs2lov hzhiv) (Frac.valid_mul (Frac.valid_ofInt 2) huv)) h16v)
      have hlinz_r : lin_z_f.toReal = 1 / 8 + (z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) / 16 := by
        simp only [lin_z_f]
        rw [Frac.toReal_add h8v (Frac.valid_mul (Frac.valid_add (Frac.valid_add hs2lov hzhiv) (Frac.valid_mul (Frac.valid_ofInt 2) huv)) h16v),
            Frac.toReal_mul, Frac.toReal_add (Frac.valid_add hs2lov hzhiv) (Frac.valid_mul (Frac.valid_ofInt 2) huv),
            Frac.toReal_add hs2lov hzhiv, Frac.toReal_mul, Frac.toReal_ofInt]
        simp only [Frac.toReal]; push_cast; ring
      have hlinz_nn : 0 ≤ lin_z_f.toReal := by
        have h1 : 0 ≤ z_lo_f.toReal := by
          simp only [z_lo_f, s2_lo_f, Frac.toReal]; push_cast
          have s0 : (0 : ℝ) ≤ (if ic0 then ((A0 : ℝ) * A0) else 0) := by split_ifs <;> [exact mul_self_nonneg _; norm_num]
          have s1 : (0 : ℝ) ≤ (if ic1 then ((A1 : ℝ) * A1) else 0) := by split_ifs <;> [exact mul_self_nonneg _; norm_num]
          have s2 : (0 : ℝ) ≤ (if ic2 then ((A2 : ℝ) * A2) else 0) := by split_ifs <;> [exact mul_self_nonneg _; norm_num]
          have s3 : (0 : ℝ) ≤ (if ic3 then ((A3 : ℝ) * A3) else 0) := by split_ifs <;> [exact mul_self_nonneg _; norm_num]
          linarith only [s0, s1, s2, s3]
        have h2 : 0 ≤ z_hi_f.toReal := le_trans h1 (le_trans hz_range.1 hz_range.2)
        linarith only [hlinz_r, h1, h2, hu_nn]
      let const_z2_f := (z_lo_f * z_hi_f + Frac.ofInt 2 * z_hi_f * u) * ⟨1, 16⟩
      have hcz2v : const_z2_f.Valid :=
        Frac.valid_mul (Frac.valid_add (Frac.valid_mul hs2lov hzhiv) (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hzhiv) huv)) h16v
      have hcz2_r : const_z2_f.toReal = (z_lo_f.toReal * z_hi_f.toReal + 2 * z_hi_f.toReal * u.toReal) / 16 := by
        simp only [const_z2_f]
        rw [Frac.toReal_mul, Frac.toReal_add (Frac.valid_mul hs2lov hzhiv) (Frac.valid_mul (Frac.valid_mul (Frac.valid_ofInt 2) hzhiv) huv),
            Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_ofInt]
        simp only [Frac.toReal]; push_cast; ring
      obtain ⟨hcapDv, hcapD_le⟩ := hcap_min_lb (Frac.ofInt 2) (-lin_z_f) (Frac.valid_ofInt 2) (by norm_num [Frac.ofInt]) (Frac.valid_neg hlinzv)
      let capD_f :=
        (if ic0 then minQuad1d (Frac.ofInt 2) (-lin_z_f) ⟨A0 * A0, 16384⟩ ⟨B0 * B0, 16384⟩ else Frac.ofInt 0) +
        (if ic1 then minQuad1d (Frac.ofInt 2) (-lin_z_f) ⟨A1 * A1, 16384⟩ ⟨B1 * B1, 16384⟩ else Frac.ofInt 0) +
        (if ic2 then minQuad1d (Frac.ofInt 2) (-lin_z_f) ⟨A2 * A2, 16384⟩ ⟨B2 * B2, 16384⟩ else Frac.ofInt 0) +
        (if ic3 then minQuad1d (Frac.ofInt 2) (-lin_z_f) ⟨A3 * A3, 16384⟩ ⟨B3 * B3, 16384⟩ else Frac.ofInt 0)
      change capD_f.toReal ≤ ∑ j ∈ Icap, ((Frac.ofInt 2).toReal * (ctx.c (ps j)) ^ 4 + (-lin_z_f).toReal * (ctx.c (ps j)) ^ 2) at hcapD_le
      rw [Frac.toReal_ofInt, Frac.toReal_neg] at hcapD_le
      simp only [Int.cast_ofNat, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hcapD_le
      change capD_f.toReal ≤ 2 * (∑ j ∈ Icap, (ctx.c (ps j)) ^ 4) + -(lin_z_f.toReal * zI) at hcapD_le
      let qC_f := capD_f - lin_z_f * s13 + const_z2_f
      let qB_f := -(⟨1, 8⟩ + z_hi_f * ⟨1, 8⟩)
      let qA_f := Frac.ofInt 2 * inv_k_f - ⟨1, 16⟩
      have hqCv : qC_f.Valid := Frac.valid_add (Frac.valid_sub hcapDv (Frac.valid_mul hlinzv hs13v)) hcz2v
      have hqBv : qB_f.Valid := Frac.valid_neg (Frac.valid_add h8v (Frac.valid_mul hzhiv h8v))
      have hqAv : qA_f.Valid := Frac.valid_sub (Frac.valid_mul (Frac.valid_ofInt 2) hinv_k_v) h16v
      have hqC_r : qC_f.toReal = capD_f.toReal - lin_z_f.toReal * s13.toReal + const_z2_f.toReal := by
        simp only [qC_f]; rw [Frac.toReal_add (Frac.valid_sub hcapDv (Frac.valid_mul hlinzv hs13v)) hcz2v,
          Frac.toReal_sub hcapDv (Frac.valid_mul hlinzv hs13v), Frac.toReal_mul]
      have hqB_r : qB_f.toReal = -(1 / 8 + z_hi_f.toReal / 8) := by
        simp only [qB_f]; rw [Frac.toReal_neg, Frac.toReal_add h8v (Frac.valid_mul hzhiv h8v), Frac.toReal_mul]
        simp only [Frac.toReal]; push_cast; ring
      have hqA_r : qA_f.toReal = 2 * inv_k_f.toReal - 1 / 16 := by
        simp only [qA_f]; rw [Frac.toReal_sub (Frac.valid_mul (Frac.valid_ofInt 2) hinv_k_v) h16v, Frac.toReal_mul, Frac.toReal_ofInt]
        simp only [Frac.toReal]; push_cast; ring
      have hquad_lin : z ^ 2 + 2 * z * t ≤ (z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) * z -
          z_lo_f.toReal * z_hi_f.toReal - 2 * z_hi_f.toReal * u.toReal + 2 * z_hi_f.toReal * t := by
        have h1 : 0 ≤ (z - z_lo_f.toReal) * (z_hi_f.toReal - z) :=
          mul_nonneg (sub_nonneg.mpr hz_range.1) (sub_nonneg.mpr hz_range.2)
        have h2 : 0 ≤ 2 * (z_hi_f.toReal - z) * (t - u.toReal) :=
          mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hz_range.2)) (sub_nonneg.mpr ht_range.1)
        have hid : ((z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) * z -
            z_lo_f.toReal * z_hi_f.toReal - 2 * z_hi_f.toReal * u.toReal + 2 * z_hi_f.toReal * t) -
            (z ^ 2 + 2 * z * t) =
            (z - z_lo_f.toReal) * (z_hi_f.toReal - z) + 2 * (z_hi_f.toReal - z) * (t - u.toReal) := by ring
        linarith only [h1, h2, hid]
      have hbase_le : qA_f.toReal * t ^ 2 + qB_f.toReal * t + qC_f.toReal ≤ 2 * S4L - S2L / 8 - S2L ^ 2 / 16 := by
        have hlin_z0 : lin_z_f.toReal * z0 ≤ lin_z_f.toReal * s13.toReal := mul_le_mul_of_nonneg_left hz0_le hlinz_nn
        have hS2_sq : S2L ^ 2 = z ^ 2 + 2 * z * t + t ^ 2 := by rw [hS2L_eq]; ring
        have hlin_id : lin_z_f.toReal * zI + lin_z_f.toReal * z0 =
            (1 / 8 + (z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) / 16) * z := by
          rw [hlinz_r]; change _ = (1 / 8 + (z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) / 16) * (z0 + zI); ring
        have hring_id : (2 * inv_k_f.toReal - 1 / 16) * t ^ 2 + -(1 / 8 + z_hi_f.toReal / 8) * t -
            (1 / 8 + (z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) / 16) * z +
            (z_lo_f.toReal * z_hi_f.toReal + 2 * z_hi_f.toReal * u.toReal) / 16 =
            2 * (inv_k_f.toReal * t ^ 2) - (z + t) / 8 - t ^ 2 / 16 -
            ((z_lo_f.toReal + z_hi_f.toReal + 2 * u.toReal) * z -
              z_lo_f.toReal * z_hi_f.toReal - 2 * z_hi_f.toReal * u.toReal + 2 * z_hi_f.toReal * t) / 16 := by ring
        rw [hqA_r, hqB_r, hqC_r, hS2_sq, hS2L_eq, hcz2_r]
        linarith only [hS4L_ge, hcapD_le, hquad_lin, hlin_z0, hlin_id, hring_id]
      first
      | ( -- Case `m = 4`!
          simp only [beq_self_eq_true, ↓reduceIte] at hok
          have hpos := sound_quadPosOn hqAv hqBv hqCv huv hvv ht_range.1 ht_range.2 hok
          have hmax_nn : 0 ≤ (max 0 (1 - S2L - 16 * (ctx.c uPt) ^ 2)) ^ 2 / 128 := by positivity
          linarith only [hD_le, hbase_le, hpos, hmax_nn])
      | ( -- Case `m = 3`!
          simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at hok
          rw [Bool.and_eq_true] at hok
          let Kd_f := Frac.ofInt 1 - Frac.ofInt 16 * s13 - s2_hi_f
          have hKdv : Kd_f.Valid := Frac.valid_sub (Frac.valid_sub (Frac.valid_ofInt 1) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v)) hs2hiv
          have hKd_r : Kd_f.toReal = 1 - 16 * s13.toReal - s2_hi_f.toReal := by
            simp only [Kd_f]
            rw [Frac.toReal_sub (Frac.valid_sub (Frac.valid_ofInt 1) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v)) hs2hiv,
                Frac.toReal_sub (Frac.valid_ofInt 1) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v),
                Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt]; norm_num
          have hok1 : v.le Kd_f = true := hok.1
          have hok2 : quadPosOn (qA_f + ⟨1, 128⟩) (qB_f - Kd_f * ⟨1, 64⟩) (qC_f + Kd_f * Kd_f * ⟨1, 128⟩) u v = true := hok.2
          have hv_le_Kd := (Frac.le_iff hvv hKdv).mp hok1
          have hpos := sound_quadPosOn (Frac.valid_add hqAv h128v)
            (Frac.valid_sub hqBv (Frac.valid_mul hKdv h64v))
            (Frac.valid_add hqCv (Frac.valid_mul (Frac.valid_mul hKdv hKdv) h128v))
            huv hvv ht_range.1 ht_range.2 hok2
          rw [Frac.toReal_add hqAv h128v, Frac.toReal_sub hqBv (Frac.valid_mul hKdv h64v),
              Frac.toReal_add hqCv (Frac.valid_mul (Frac.valid_mul hKdv hKdv) h128v),
              Frac.toReal_mul, Frac.toReal_mul, Frac.toReal_mul] at hpos
          have hf128 : (⟨1, 128⟩ : Frac).toReal = 1 / 128 := by simp [Frac.toReal]
          have hf64 : (⟨1, 64⟩ : Frac).toReal = 1 / 64 := by simp [Frac.toReal]
          rw [hf128, hf64] at hpos
          have harg_ge : Kd_f.toReal - t ≤ 1 - S2L - 16 * (ctx.c uPt) ^ 2 := by
            have h16 : z0 + 16 * (ctx.c uPt) ^ 2 ≤ 16 * s13.toReal := by linarith only [hS13_u_sum, hs13_le, hz0_nn]
            rw [hKd_r, hS2L_eq]
            change 1 - 16 * s13.toReal - s2_hi_f.toReal - t ≤ 1 - (z0 + zI + t) - 16 * (ctx.c uPt) ^ 2
            linarith only [h16, hzI_bounds.2]
          have hKd_t_nn : 0 ≤ Kd_f.toReal - t := by linarith only [hv_le_Kd, ht_range.2]
          have hmax_ge : (Kd_f.toReal - t) ^ 2 / 128 ≤ (max 0 (1 - S2L - 16 * (ctx.c uPt) ^ 2)) ^ 2 / 128 := by
            have hle_m : Kd_f.toReal - t ≤ max 0 (1 - S2L - 16 * (ctx.c uPt) ^ 2) := le_trans harg_ge (le_max_right _ _)
            exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hKd_t_nn hle_m 2) (by norm_num)
          have hexp : (qA_f.toReal + 1 / 128) * t ^ 2 + (qB_f.toReal - Kd_f.toReal * (1 / 64)) * t +
              (qC_f.toReal + Kd_f.toReal * Kd_f.toReal * (1 / 128)) =
              (qA_f.toReal * t ^ 2 + qB_f.toReal * t + qC_f.toReal) + (Kd_f.toReal - t) ^ 2 / 128 := by ring
          linarith only [hD_le, hbase_le, hpos, hmax_ge, hexp])
    · simp at hok
  | m + 5 => simp at hok

/-- Soundness of `checkSegs`: covers `[u_n/200, ∞)` (or `{0}` when `k_free = 0`). -/
private lemma sound_checkSegs {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3)
    {L S13 : Finset (PauliIdx 4)} (hL : IsLagrangian L) (hS13_sub : S13 ⊆ L) (h0_S13 : (0 : PauliIdx 4) ∈ S13)
    (hS13_card : S13.card = 13)
    {uPt : PauliIdx 4} (huL : uPt ∉ L) (hu0 : uPt ≠ 0)
    (hZ14_eq : insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ) =
      insert uPt S13)
    {mask : Nat} (hmask_lt : mask < 15)
    (hmask_def : ∀ j : Fin 4, bitSet mask j.val = decide (ctx.idx ⟨13 + j.val, by omega⟩ ∈ L))
    {s13 : Frac} (hs13v : s13.Valid) (hs13_le : ctx.S2_13 ≤ s13.toReal) :
    ∀ (segs : List (Nat × Nat)) (u_n : Nat),
      checkSegs A0 A1 A2 A3 B0 B1 B2 B3 mask s13 (kFreeOf B0 B1 B2 B3 mask) u_n segs = true →
      let ps : Fin 4 → PauliIdx 4 := fun j => ctx.idx ⟨13 + j.val, by omega⟩
      let Bs : Fin 4 → Int := ![B0, B1, B2, B3]
      let Icap := Finset.univ.filter fun j : Fin 4 => ps j ∈ L ∧ Bs j < 32
      let Lfree := (L.erase 0) \ (S13.erase 0 ∪ Icap.image ps)
      let t : ℝ := ∑ p ∈ Lfree, (ctx.c p) ^ 2
      (u_n : ℝ) / 200 ≤ t → (kFreeOf B0 B1 B2 B3 mask = 0 → t = 0) → False
  | [], _, hok, _, _ => by simp [checkSegs] at hok
  | [(m, 0)], u_n, hok, ht_lo, hk0_t => by
    unfold checkSegs at hok
    by_cases hk0 : kFreeOf B0 B1 B2 B3 mask = 0
    · simp only [hk0, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hok
      have ht0 := hk0_t hk0
      exact sound_checkMethod hb hL hS13_sub h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
        hs13v hs13_le (Frac.mk_valid (by norm_num)) (Frac.mk_valid (by norm_num))
        (by simp [Frac.toReal]) hok.2 (by simp [Frac.toReal, ht0])
    · have hne : (kFreeOf B0 B1 B2 B3 mask == 0) = false := by simp [hk0]
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hok
      exact sound_checkMethod hb hL hS13_sub h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
        hs13v hs13_le (Frac.mk_valid (by norm_num)) (Frac.mk_valid (by norm_num))
        (by simp [Frac.toReal]; positivity) hok (by simpa [Frac.toReal] using ht_lo)
  | [(m, v' + 1)], u_n, hok, _, _ => by
    unfold checkSegs at hok
    by_cases hbad : (kFreeOf B0 B1 B2 B3 mask == 0 || decide (v' + 1 ≤ u_n)) = true
    · simp only [hbad, ↓reduceIte, Bool.false_eq_true] at hok
    · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hok
      simp [checkSegs] at hok
  | (m, v_n) :: hd :: tl, u_n, hok, ht_lo, hk0_t => by
    unfold checkSegs at hok
    by_cases hbad : (kFreeOf B0 B1 B2 B3 mask == 0 || decide (v_n ≤ u_n)) = true
    · simp only [hbad, ↓reduceIte, Bool.false_eq_true] at hok
    · simp only [hbad, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hok
      by_cases htv : (∑ p ∈ (L.erase 0) \ (S13.erase 0 ∪
          (Finset.univ.filter fun j : Fin 4 => ctx.idx ⟨13 + j.val, by omega⟩ ∈ L ∧
            (![B0, B1, B2, B3] : Fin 4 → Int) j < 32).image (fun j : Fin 4 => ctx.idx ⟨13 + j.val, by omega⟩)),
          (ctx.c p) ^ 2) ≤ (v_n : ℝ) / 200
      · exact sound_checkMethod hb hL hS13_sub h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
          hs13v hs13_le (Frac.mk_valid (by norm_num)) (Frac.mk_valid (by norm_num))
          (by simp [Frac.toReal]; positivity) hok.1
          (by simp [Frac.toReal]; exact ⟨ht_lo, htv⟩)
      · exact sound_checkSegs hb hL hS13_sub h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
          hs13v hs13_le (hd :: tl) v_n hok.2 (le_of_not_ge htv) hk0_t

/-- Soundness of `checkMask` (both `.b` weighted Bessel and `.q` ABD quadratic segments). -/
private lemma sound_checkMask {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3)
    {L S13 : Finset (PauliIdx 4)} (hL : IsLagrangian L) (hS13_sub : S13 ⊆ L) (h0_S13 : (0 : PauliIdx 4) ∈ S13)
    (hS13_card : S13.card = 13)
    {uPt : PauliIdx 4} (huL : uPt ∉ L) (hu0 : uPt ≠ 0)
    (hZ14_eq : insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ) =
      insert uPt S13)
    {mask : Nat} (hmask_lt : mask < 15)
    (hmask_def : ∀ j : Fin 4, bitSet mask j.val = decide (ctx.idx ⟨13 + j.val, by omega⟩ ∈ L))
    {s13 : Frac} (hs13v : s13.Valid) (hs13_le : ctx.S2_13 ≤ s13.toReal)
    {mc : MaskCert}
    (hok : checkMask A0 A1 A2 A3 B0 B1 B2 B3 mask s13 mc = true) : False := by
  classical
  cases mc with
  | b w0 w1 w2 w3 =>
    unfold checkMask at hok
    dsimp only at hok
    by_cases hokW : ((decide (w0 ≤ 16) && (decide (B0 < 32) || w0 == 0)) &&
        (decide (w1 ≤ 16) && (decide (B1 < 32) || w1 == 0)) &&
        (decide (w2 ≤ 16) && (decide (B2 < 32) || w2 == 0)) &&
        (decide (w3 ≤ 16) && (decide (B3 < 32) || w3 == 0))) = true
    · simp only [hokW, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hokW
      rcases hokW with ⟨⟨⟨⟨hw0, hB0w⟩, ⟨hw1, hB1w⟩⟩, ⟨hw2, hB2w⟩⟩, ⟨hw3, hB3w⟩⟩
      let ps : Fin 4 → PauliIdx 4 := fun j => ctx.idx ⟨13 + j.val, by omega⟩
      have hps_inj : Function.Injective ps := fun a b h => by
        have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext (by omega)
      have hps_not_Z14 : ∀ j : Fin 4, ps j ∉ insert uPt S13 := fun j hmem => by
        rw [← hZ14_eq] at hmem
        rcases Finset.mem_insert.mp hmem with h0 | hI
        · exact ctx.idx_ne0 ⟨13 + j.val, by omega⟩ h0
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hI
          have h' := congr_arg Fin.val (ctx.idx_inj hi); dsimp at h'; omega
      have hps_disj_S : ∀ j : Fin 4, ps j ∉ S13 := fun j h => hps_not_Z14 j (Finset.mem_insert_of_mem h)
      have hps_ne_u : ∀ j : Fin 4, ps j ≠ uPt := fun j h => hps_not_Z14 j (h ▸ Finset.mem_insert_self _ _)
      let ws : Fin 4 → ℝ := ![(w0 : ℝ) / 16, (w1 : ℝ) / 16, (w2 : ℝ) / 16, (w3 : ℝ) / 16]
      have hws_lo : ∀ j : Fin 4, 0 ≤ ws j := fun j => by fin_cases j <;> simp [ws] <;> positivity
      have hws_hi : ∀ j : Fin 4, ws j ≤ 1 := fun j => by
        fin_cases j <;> dsimp [ws]
        · have : (w0 : ℝ) ≤ 16 := (by exact_mod_cast hw0); linarith
        · have : (w1 : ℝ) ≤ 16 := (by exact_mod_cast hw1); linarith
        · have : (w2 : ℝ) ≤ 16 := (by exact_mod_cast hw2); linarith
        · have : (w3 : ℝ) ≤ 16 := (by exact_mod_cast hw3); linarith
      let w : PauliIdx 4 → ℝ := fun p =>
        if p ∈ S13 ∨ p = uPt then 1
        else if h : ∃ j : Fin 4, ps j = p then ws (Classical.choose h) else 0
      have hw0_1 : w 0 = 1 := by simp [w, h0_S13]
      have hw_ps : ∀ j : Fin 4, w (ps j) = ws j := fun j => by
        have hnot : ¬(ps j ∈ S13 ∨ ps j = uPt) := fun h => h.elim (hps_disj_S j) (hps_ne_u j)
        have hex : ∃ k : Fin 4, ps k = ps j := ⟨j, rfl⟩
        simp only [w, hnot, ↓reduceIte]
        split_ifs
        exact congr_arg ws (hps_inj (Classical.choose_spec hex))
      let Z14 := insert uPt S13
      have hZ14_card : Z14.card = 14 := by
        rw [Finset.card_insert_of_notMem (fun h => huL (hS13_sub h)), hS13_card]
      let P4 := Finset.univ.image ps
      have hdisj_ZP : Disjoint Z14 P4 := by
        rw [Finset.disjoint_left]; intro p hpZ hpP
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpP; exact hps_not_Z14 j hpZ
      have hw_out : ∀ p ∉ Z14 ∪ P4, w p = 0 := fun p hp => by
        have hpZ : p ∉ Z14 := fun h => hp (Finset.mem_union_left _ h)
        have hpP : p ∉ P4 := fun h => hp (Finset.mem_union_right _ h)
        have h1 : ¬(p ∈ S13 ∨ p = uPt) := fun h => hpZ (h.elim (Finset.mem_insert_of_mem) (fun e => e ▸ Finset.mem_insert_self _ _))
        have h2 : ¬(∃ j : Fin 4, ps j = p) := fun ⟨j, hj⟩ => hpP (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
        simp [w, h1, h2]
      have hw_Z14 : ∀ p ∈ Z14, w p = 1 := fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | hS
        · simp [w]
        · simp [w, hS]
      have hsum_w : ∀ g : PauliIdx 4 → ℝ, (∀ p ∉ Z14 ∪ P4, g p = 0) →
          ∑ p : PauliIdx 4, g p = (∑ p ∈ Z14, g p) + ∑ j : Fin 4, g (ps j) := by
        intro g hg0
        rw [← Finset.sum_sdiff (Finset.subset_univ (Z14 ∪ P4))]
        have h0 : ∑ p ∈ Finset.univ \ (Z14 ∪ P4), g p = 0 :=
          Finset.sum_eq_zero fun p hp => hg0 p (Finset.mem_sdiff.mp hp).2
        rw [h0, zero_add, Finset.sum_union hdisj_ZP, Finset.sum_image (fun a _ b _ h => hps_inj h)]
      -- Match `S1`, `S2w`, `M`, `W_lb`!
      let win_n : Int := (if bitSet mask 0 then (w0 : Int) else 0) + (if bitSet mask 1 then (w1 : Int) else 0) +
        (if bitSet mask 2 then (w2 : Int) else 0) + (if bitSet mask 3 then (w3 : Int) else 0)
      let wout_n : Int := (if !bitSet mask 0 then (w0 : Int) else 0) + (if !bitSet mask 1 then (w1 : Int) else 0) +
        (if !bitSet mask 2 then (w2 : Int) else 0) + (if !bitSet mask 3 then (w3 : Int) else 0)
      have hm0 : bitSet mask 0 = decide (ps 0 ∈ L) := hmask_def 0
      have hm1 : bitSet mask 1 = decide (ps 1 ∈ L) := hmask_def 1
      have hm2 : bitSet mask 2 = decide (ps 2 ∈ L) := hmask_def 2
      have hm3 : bitSet mask 3 = decide (ps 3 ∈ L) := hmask_def 3
      have hwin_eq : (win_n : ℝ) / 16 = ∑ j : Fin 4, if ps j ∈ L then ws j else 0 := by
        rw [Fin.sum_univ_four]
        simp only [win_n, ws, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hm0, hm1, hm2, hm3]
        by_cases p0 : ps 0 ∈ L <;> by_cases p1 : ps 1 ∈ L <;> by_cases p2 : ps 2 ∈ L <;> by_cases p3 : ps 3 ∈ L <;>
          simp [p0, p1, p2, p3] <;> ring
      have hwout_eq : (wout_n : ℝ) / 16 = ∑ j : Fin 4, if ps j ∉ L then ws j else 0 := by
        rw [Fin.sum_univ_four]
        simp only [wout_n, ws, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hm0, hm1, hm2, hm3]
        by_cases p0 : ps 0 ∈ L <;> by_cases p1 : ps 1 ∈ L <;> by_cases p2 : ps 2 ∈ L <;> by_cases p3 : ps 3 ∈ L <;>
          simp [p0, p1, p2, p3] <;> ring
      have hwsum_eq : (win_n : ℝ) + (wout_n : ℝ) = (w0 : ℝ) + (w1 : ℝ) + (w2 : ℝ) + (w3 : ℝ) := by
        simp only [win_n, wout_n]
        cases bitSet mask 0 <;> cases bitSet mask 1 <;> cases bitSet mask 2 <;> cases bitSet mask 3 <;>
          simp <;> ring
      have hS1_eq : (∑ p : PauliIdx 4, w p) = (⟨14 * 16 + win_n + wout_n, 16⟩ : Frac).toReal := by
        rw [hsum_w w hw_out, Finset.sum_congr rfl hw_Z14, Finset.sum_const, hZ14_card, nsmul_eq_mul, mul_one,
            Finset.sum_congr rfl (fun j _ => hw_ps j), Fin.sum_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Frac.toReal]
        push_cast; linarith
      have hS2_eq : (∑ p : PauliIdx 4, (w p) ^ 2) =
          (⟨14 * 256 + ((w0 : Int) * w0 + (w1 : Int) * w1 + (w2 : Int) * w2 + (w3 : Int) * w3), 256⟩ : Frac).toReal := by
        rw [hsum_w (fun p => (w p) ^ 2) (fun p hp => by rw [hw_out p hp]; norm_num),
            Finset.sum_congr rfl (fun p hp => by rw [hw_Z14 p hp, one_pow]), Finset.sum_const, hZ14_card,
            nsmul_eq_mul, mul_one, Finset.sum_congr rfl (fun j _ => by rw [hw_ps j]), Fin.sum_univ_four]
        simp only [ws, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Frac.toReal]
        push_cast; ring
      let mv_n : Int :=
        (if decide (B0 < 32) then (w0 : Int) * (1024 - B0 * B0) else 0) +
        (if decide (B1 < 32) then (w1 : Int) * (1024 - B1 * B1) else 0) +
        (if decide (B2 < 32) then (w2 : Int) * (1024 - B2 * B2) else 0) +
        (if decide (B3 < 32) then (w3 : Int) * (1024 - B3 * B3) else 0)
      let M_f : Frac := Frac.ofInt 14 - Frac.ofInt 16 * s13 + ⟨mv_n, 16 * 1024⟩
      have hmvv : (⟨mv_n, 16 * 1024⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
      have hMv : M_f.Valid := Frac.valid_add (Frac.valid_sub (Frac.valid_ofInt 14) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v)) hmvv
      have hM_ge : M_f.toReal ≤ ∑ p : PauliIdx 4, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) := by
        rw [hsum_w _ (fun p hp => by rw [hw_out p hp, zero_mul])]
        have hZ14_f : ∑ p ∈ Z14, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) = 14 - 16 * ctx.S2_13 := by
          rw [Finset.sum_congr rfl fun p hp => by rw [hw_Z14 p hp, one_mul]]
          have h0Z : (0 : PauliIdx 4) ∈ Z14 := Finset.mem_insert_of_mem h0_S13
          rw [← Finset.add_sum_erase _ _ h0Z]
          simp only [↓reduceIte]
          have hrest : ∑ p ∈ Z14.erase 0, (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) =
              13 - 16 * ctx.S2_13 := by
            have hpt : ∀ p ∈ Z14.erase 0, (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) = 1 - 16 * (ctx.c p) ^ 2 :=
              fun p hp => by simp [(Finset.mem_erase.mp hp).1]
            rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
                Finset.card_erase_of_mem h0Z, hZ14_card, nsmul_eq_mul, mul_one]
            have hZe : Z14.erase 0 = Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
              change (insert uPt S13).erase 0 = _; rw [← hZ14_eq, Finset.erase_insert]
              intro h; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h; exact ctx.idx_ne0 _ hi
            rw [hZe, Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
            have hsq : ∑ i : Fin 13, (ctx.c (ctx.idx ⟨i.val, by omega⟩)) ^ 2 = ctx.S2_13 :=
              Finset.sum_congr rfl fun i _ => (sq_abs _).symm
            rw [hsq]; norm_num
          rw [hrest]; ring
        have hps_f : ∑ j : Fin 4, w (ps j) * (if ps j = 0 then (1 : ℝ) else 1 - 16 * (ctx.c (ps j)) ^ 2) =
            ∑ j : Fin 4, ws j * (1 - 16 * (ctx.c (ps j)) ^ 2) :=
          Finset.sum_congr rfl fun j _ => by
            have hne : ps j ≠ 0 := ctx.idx_ne0 _
            rw [hw_ps j]; simp only [hne, ↓reduceIte]
        rw [hZ14_f, hps_f]
        rw [Fin.sum_univ_four]
        have hunc := hb.unclamp
        have hpt : ∀ (j : Fin 4) (wj : Nat) (Bj : Int), (Bj < 32 ∨ wj = 0) →
            (Bj < 32 → |ctx.c (ps j)| ≤ (Bj : ℝ) / 128) →
            ((if decide (Bj < 32) then (wj : Int) * (1024 - Bj * Bj) else 0 : Int) : ℝ) / (16 * 1024) ≤
              ((wj : ℝ) / 16) * (1 - 16 * (ctx.c (ps j)) ^ 2) := by
          intro j wj Bj hor hle
          by_cases hB : Bj < 32
          · simp only [hB, decide_true, ↓reduceIte]; push_cast
            have hsq : (ctx.c (ps j)) ^ 2 ≤ ((Bj : ℝ) / 128) ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hle hB) 2
            have hwj_nn : (0 : ℝ) ≤ (wj : ℝ) / 16 := by positivity
            have hm := mul_le_mul_of_nonneg_left (show 1 - 16 * ((Bj : ℝ) / 128) ^ 2 ≤ 1 - 16 * (ctx.c (ps j)) ^ 2 by linarith) hwj_nn
            linarith
          · have hwz : wj = 0 := hor.resolve_left hB
            simp [hB, hwz]
        have p0 := hpt 0 w0 B0 hB0w hunc.1; have p1 := hpt 1 w1 B1 hB1w hunc.2.1
        have p2 := hpt 2 w2 B2 hB2w hunc.2.2.1; have p3 := hpt 3 w3 B3 hB3w hunc.2.2.2
        push_cast at p0 p1 p2 p3
        rw [show (16 : ℝ) * 1024 = 16384 by norm_num] at p0 p1 p2 p3
        simp only [M_f, ws, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [Frac.toReal_add (Frac.valid_sub (Frac.valid_ofInt 14) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v)) hmvv,
            Frac.toReal_sub (Frac.valid_ofInt 14) (Frac.valid_mul (Frac.valid_ofInt 16) hs13v),
            Frac.toReal_mul, Frac.toReal_ofInt, Frac.toReal_ofInt,
            show (⟨mv_n, 16 * 1024⟩ : Frac).toReal = (mv_n : ℝ) / 16384 from by simp [Frac.toReal]]
        dsimp only [mv_n]; push_cast; norm_num at p0 p1 p2 p3 ⊢; linarith
      have hW_ge : (⟨2 * (16 + wout_n) * (80 + win_n), 256⟩ : Frac).toReal ≤ wAnti w := by
        have hwlb := weighted_mask_anticomm_lb hL hS13_sub hS13_card huL hps_inj hps_disj_S hps_ne_u hws_lo hws_hi
        dsimp only at hwlb
        rw [← hwin_eq, ← hwout_eq] at hwlb
        simp only [Frac.toReal]; push_cast; linarith
      exact sound_besselBelow ctx.hunit ctx.hF4 w hw0_1 (Frac.mk_valid (by norm_num)) (Frac.mk_valid (by norm_num))
        hMv (Frac.mk_valid (by norm_num)) hS1_eq hS2_eq hM_ge hW_ge hok
    · simp [hokW] at hok
  | q segs =>
    unfold checkMask at hok
    have hps_inj : Function.Injective (fun j : Fin 4 => ctx.idx ⟨13 + j.val, by omega⟩) := fun a b h => by
      have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext (by omega)
    have hps_not_S13 : ∀ j : Fin 4, ctx.idx ⟨13 + j.val, by omega⟩ ∉ S13 := fun j h => by
      have hmem : ctx.idx ⟨13 + j.val, by omega⟩ ∈ insert uPt S13 := Finset.mem_insert_of_mem h
      rw [← hZ14_eq] at hmem
      rcases Finset.mem_insert.mp hmem with h0 | hI
      · exact ctx.idx_ne0 _ h0
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hI
        have h' := congr_arg Fin.val (ctx.idx_inj hi); dsimp at h'; omega
    let ps : Fin 4 → PauliIdx 4 := fun j => ctx.idx ⟨13 + j.val, by omega⟩
    let Bs : Fin 4 → Int := ![B0, B1, B2, B3]
    let Icap := Finset.univ.filter fun j : Fin 4 => ps j ∈ L ∧ Bs j < 32
    let Lfree := (L.erase 0) \ (S13.erase 0 ∪ Icap.image ps)
    have hLfree_card : Lfree.card = kFreeOf B0 B1 B2 B3 mask := by
      have hS13_e_sub : S13.erase 0 ⊆ L.erase 0 := Finset.erase_subset_erase 0 hS13_sub
      have hIcap_sub : Icap.image ps ⊆ L.erase 0 := by
        intro p hp; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_erase.mpr ⟨ctx.idx_ne0 _, (Finset.mem_filter.mp hj).2.1⟩
      have hdisj : Disjoint (S13.erase 0) (Icap.image ps) := by
        rw [Finset.disjoint_left]; intro p hpS hpI
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpI; exact hps_not_S13 j (Finset.mem_erase.mp hpS).2
      have hIcap_c : Icap.card =
          (if bitSet mask 0 && decide (B0 < 32) then 1 else 0) +
          (if bitSet mask 1 && decide (B1 < 32) then 1 else 0) +
          (if bitSet mask 2 && decide (B2 < 32) then 1 else 0) +
          (if bitSet mask 3 && decide (B3 < 32) then 1 else 0) := by
        have h1 : Icap.card = ∑ j : Fin 4, if ps j ∈ L ∧ Bs j < 32 then 1 else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        rw [h1, Fin.sum_univ_four]
        have hm0 : bitSet mask 0 = decide (ps 0 ∈ L) := hmask_def 0
        have hm1 : bitSet mask 1 = decide (ps 1 ∈ L) := hmask_def 1
        have hm2 : bitSet mask 2 = decide (ps 2 ∈ L) := hmask_def 2
        have hm3 : bitSet mask 3 = decide (ps 3 ∈ L) := hmask_def 3
        simp only [Bs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [hm0, hm1, hm2, hm3]
        by_cases p0 : ps 0 ∈ L <;> by_cases b0 : B0 < 32 <;>
        by_cases p1 : ps 1 ∈ L <;> by_cases b1 : B1 < 32 <;>
        by_cases p2 : ps 2 ∈ L <;> by_cases b2 : B2 < 32 <;>
        by_cases p3 : ps 3 ∈ L <;> by_cases b3 : B3 < 32 <;> simp [p0, b0, p1, b1, p2, b2, p3, b3]
      have hL15 : (L.erase 0).card = 15 := by rw [Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num
      have hS12 : (S13.erase 0).card = 12 := by rw [Finset.card_erase_of_mem h0_S13, hS13_card]
      rw [Finset.card_sdiff_of_subset (Finset.union_subset hS13_e_sub hIcap_sub),
          Finset.card_union_of_disjoint hdisj, hL15, hS12, Finset.card_image_of_injective _ hps_inj, hIcap_c]
      dsimp only [kFreeOf]; omega
    exact sound_checkSegs hb hL hS13_sub h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
      hs13v hs13_le segs 0 hok
      (by simp; exact Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (fun hk0 => by
        have h0 : Lfree = ∅ := Finset.card_eq_zero.mp (hLfree_card.trans hk0)
        change ∑ p ∈ Lfree, (ctx.c p) ^ 2 = 0
        rw [h0]; simp)

/-- Helper: indicator Bessel contradiction on `Z_m = insert 0 {idx 0 .. idx (m-2)}`. -/
private lemma antiCount_lt_of_bessel {ψ : QState 4} {ctx : StateCtx ψ} {k : Nat} (hk : k ≤ 255)
    {skn : Nat} (hsk_le : ∑ i : Fin k, (ctx.x ⟨i.val, by omega⟩) ^ 2 ≤ (skn : ℝ) / 1000000)
    {A_thresh : Nat}
    (hbess : besselBelow (Frac.ofInt (k + 1)) (Frac.ofInt (k + 1))
      (Frac.ofInt (k + 1) - Frac.ofInt 16 * ⟨skn, 1000000⟩) (Frac.ofInt A_thresh) = true) :
    let Z := insert (0 : PauliIdx 4) (Finset.image (fun i : Fin k => ctx.idx ⟨i.val, by omega⟩) Finset.univ)
    Z.card = k + 1 ∧ antiCount Z < A_thresh := by
  classical
  intro Z
  have h0_not : (0 : PauliIdx 4) ∉ Finset.image (fun i : Fin k => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
    intro h; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h; exact ctx.idx_ne0 _ hi
  have hcard : Z.card = k + 1 := by
    rw [Finset.card_insert_of_notMem h0_not,
        Finset.card_image_of_injective _ (fun a b h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h'),
        Finset.card_fin]
  refine ⟨hcard, ?_⟩
  by_contra hge; push Not at hge
  let w : PauliIdx 4 → ℝ := fun p => if p ∈ Z then 1 else 0
  have hw0 : w 0 = 1 := by simp [w, Z]
  have hS1 : ∑ p : PauliIdx 4, w p = (Frac.ofInt (k + 1)).toReal := by
    simp only [w]; rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, hcard, nsmul_eq_mul, mul_one, Frac.toReal_ofInt]; push_cast; ring
  have hS2 : ∑ p : PauliIdx 4, (w p) ^ 2 = (Frac.ofInt (k + 1)).toReal := by
    have hpt : ∀ p : PauliIdx 4, (w p) ^ 2 = w p := fun p => by simp only [w]; split_ifs <;> norm_num
    simp_rw [hpt]; exact hS1
  have hskv : (⟨skn, 1000000⟩ : Frac).Valid := Frac.mk_valid (by norm_num)
  have hMv : (Frac.ofInt (k + 1) - Frac.ofInt 16 * ⟨skn, 1000000⟩).Valid :=
    Frac.valid_sub (Frac.valid_ofInt _) (Frac.valid_mul (Frac.valid_ofInt 16) hskv)
  have hM : (Frac.ofInt (k + 1) - Frac.ofInt 16 * ⟨skn, 1000000⟩).toReal ≤
      ∑ p : PauliIdx 4, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) := by
    rw [Frac.toReal_sub (Frac.valid_ofInt _) (Frac.valid_mul (Frac.valid_ofInt 16) hskv),
        Frac.toReal_ofInt, Frac.toReal_mul, Frac.toReal_ofInt]
    simp only [Frac.toReal]
    have hsum : ∑ p : PauliIdx 4, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) =
        ∑ p ∈ Z, (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Z)]
      have h0 : ∑ p ∈ Finset.univ \ Z, w p * (if p = 0 then (1 : ℝ) else 1 - 16 * (ctx.c p) ^ 2) = 0 :=
        Finset.sum_eq_zero fun p hp => by simp [w, (Finset.mem_sdiff.mp hp).2]
      rw [h0, zero_add]; exact Finset.sum_congr rfl fun p hp => by simp [w, hp]
    rw [hsum, Finset.sum_insert h0_not]
    simp only [↓reduceIte]
    rw [Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
    have hpt : ∀ i : Fin k, (if ctx.idx ⟨i.val, by omega⟩ = 0 then (1 : ℝ) else 1 - 16 * (ctx.c (ctx.idx ⟨i.val, by omega⟩)) ^ 2) =
        1 - 16 * (ctx.x ⟨i.val, by omega⟩) ^ 2 := fun i => by
      simp only [ctx.idx_ne0, ↓reduceIte, StateCtx.x, sq_abs]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    push_cast; linarith
  have hW : (Frac.ofInt A_thresh).toReal ≤ wAnti w := by
    rw [wAnti_indicator_eq, Frac.toReal_ofInt]; exact_mod_cast hge
  exact absurd (sound_besselBelow ctx.hunit ctx.hF4 w hw0 (Frac.valid_ofInt _) (Frac.valid_ofInt _)
    hMv (Frac.valid_ofInt _) hS1 hS2 hM hW hbess) id

/-- Soundness of `checkLeaf` across all 5 leaf kinds (`a15`, `a16`, `a17`, `a18`, `masks`). -/
private lemma sound_checkLeaf {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hb : BoxHyp ctx A0 A1 A2 A3 B0 B1 B2 B3) {c : LeafCert}
    (hok : checkLeaf A0 A1 A2 A3 B0 B1 B2 B3 c = true) : False := by
  classical
  cases c with
  | a15 mode xcap s13n uph skn =>
    unfold checkLeaf at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨hB0, hs13_b⟩, hsk_b⟩, hle_b⟩, hbess⟩
    have hs13 := sound_checkS13 hb hs13_b
    have hsk := sound_checkSk hb (Or.inl rfl) ⟨fun _ => hB0, fun h => by omega, fun h => by omega, fun h => by omega⟩ hs13 hsk_b
    obtain ⟨hcard, hA⟩ := antiCount_lt_of_bessel (by omega) hsk hbess
    obtain ⟨L, hL, h14⟩ := (symp_turan_unified _).2.1 hcard hA
    let Z15 := insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 14 => ctx.idx ⟨i.val, by omega⟩) Finset.univ)
    change 14 ≤ (Z15 ∩ L).card at h14
    let T := (Z15 ∩ L).erase 0
    have h0_ZL : (0 : PauliIdx 4) ∈ Z15 ∩ L := Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hL.1⟩
    have hT_sub : T ⊆ L.erase 0 := Finset.erase_subset_erase 0 Finset.inter_subset_right
    have hT_card : 13 ≤ T.card := by rw [Finset.card_erase_of_mem h0_ZL]; omega
    have hk2 : (L.erase 0 \ T).card ≤ 2 := by
      rw [Finset.card_sdiff_of_subset hT_sub, Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num; omega
    have hT_sum : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ 19 / 1000 := by
      have hT_sub_Z : T ⊆ Finset.image (fun i : Fin 14 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
        intro p hp
        have hp0 := (Finset.mem_erase.mp hp).1
        have hpZ := (Finset.mem_inter.mp (Finset.mem_erase.mp hp).2).1
        exact (Finset.mem_insert.mp hpZ).resolve_left hp0
      have h1 : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ ∑ i : Fin 14, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
        calc ∑ p ∈ T, (ctx.c p) ^ 2
            ≤ ∑ p ∈ Finset.image (fun i : Fin 14 => ctx.idx ⟨i.val, by omega⟩) Finset.univ, (ctx.c p) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hT_sub_Z fun _ _ _ => sq_nonneg _
          _ = ∑ i : Fin 14, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
              rw [Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
              exact Finset.sum_congr rfl fun i _ => (sq_abs _).symm
      have hle_r := (Frac.le_iff (Frac.mk_valid (by norm_num) : (⟨skn, 1000000⟩ : Frac).Valid) valid_SMAX_K2).mp hle_b
      simp only [SMAX_K2, Frac.toReal] at hle_r; push_cast at hle_r; linarith
    exact smax_k2_contra hL hT_sub hk2 ctx.hunit (ctx.hLout L hL) ctx.hF4 hT_sum
  | a16 mode xcap s13n uph skn =>
    unfold checkLeaf at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨hB1, hs13_b⟩, hsk_b⟩, hle_b⟩, hbess⟩
    have hs13 := sound_checkS13 hb hs13_b
    have hsk := sound_checkSk hb (Or.inr (Or.inl rfl)) ⟨fun h => by omega, fun _ => hB1, fun h => by omega, fun h => by omega⟩ hs13 hsk_b
    obtain ⟨hcard, hA⟩ := antiCount_lt_of_bessel (by omega) hsk hbess
    obtain ⟨L, hL, h15⟩ := (symp_turan_unified _).2.2.1 hcard hA
    let Z16 := insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 15 => ctx.idx ⟨i.val, by omega⟩) Finset.univ)
    change 15 ≤ (Z16 ∩ L).card at h15
    let T := (Z16 ∩ L).erase 0
    have h0_ZL : (0 : PauliIdx 4) ∈ Z16 ∩ L := Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hL.1⟩
    have hT_sub : T ⊆ L.erase 0 := Finset.erase_subset_erase 0 Finset.inter_subset_right
    have hT_card : 14 ≤ T.card := by rw [Finset.card_erase_of_mem h0_ZL]; omega
    have hk1 : (L.erase 0 \ T).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hT_sub, Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num; omega
    have hT_sum : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ 47 / 1000 := by
      have hT_sub_Z : T ⊆ Finset.image (fun i : Fin 15 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
        intro p hp
        have hp0 := (Finset.mem_erase.mp hp).1
        have hpZ := (Finset.mem_inter.mp (Finset.mem_erase.mp hp).2).1
        exact (Finset.mem_insert.mp hpZ).resolve_left hp0
      have h1 : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ ∑ i : Fin 15, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
        calc ∑ p ∈ T, (ctx.c p) ^ 2
            ≤ ∑ p ∈ Finset.image (fun i : Fin 15 => ctx.idx ⟨i.val, by omega⟩) Finset.univ, (ctx.c p) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hT_sub_Z fun _ _ _ => sq_nonneg _
          _ = ∑ i : Fin 15, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
              rw [Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
              exact Finset.sum_congr rfl fun i _ => (sq_abs _).symm
      have hle_r := (Frac.le_iff (Frac.mk_valid (by norm_num) : (⟨skn, 1000000⟩ : Frac).Valid) valid_SMAX_K1).mp hle_b
      simp only [SMAX_K1, Frac.toReal] at hle_r; push_cast at hle_r; linarith
    exact smax_k1_contra hL hT_sub hk1 ctx.hunit (ctx.hLout L hL) ctx.hF4 hT_sum
  | a17 mode xcap s13n uph skn =>
    unfold checkLeaf at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨hB2, hs13_b⟩, hsk_b⟩, hle_b⟩, hbess⟩
    have hs13 := sound_checkS13 hb hs13_b
    have hsk := sound_checkSk hb (Or.inr (Or.inr (Or.inl rfl))) ⟨fun h => by omega, fun h => by omega, fun _ => hB2, fun h => by omega⟩ hs13 hsk_b
    obtain ⟨hcard, hA⟩ := antiCount_lt_of_bessel (by omega) hsk hbess
    obtain ⟨L, hL, h16⟩ := (symp_turan_unified _).2.2.2.1 hcard hA
    let Z17 := insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 16 => ctx.idx ⟨i.val, by omega⟩) Finset.univ)
    have hL_sub : L ⊆ Z17 := by
      have heq : Z17 ∩ L = L := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hL.2.1]; norm_num; exact h16)
      rw [← heq]; exact Finset.inter_subset_left
    have hL_e_sub : L.erase 0 ⊆ Finset.image (fun i : Fin 16 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
      intro p hp
      exact (Finset.mem_insert.mp (hL_sub (Finset.mem_erase.mp hp).2)).resolve_left (Finset.mem_erase.mp hp).1
    have hS2_le : ∑ p ∈ L.erase 0, (ctx.c p) ^ 2 ≤ 848 / 10000 := by
      have h1 : ∑ p ∈ L.erase 0, (ctx.c p) ^ 2 ≤ ∑ i : Fin 16, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
        calc ∑ p ∈ L.erase 0, (ctx.c p) ^ 2
            ≤ ∑ p ∈ Finset.image (fun i : Fin 16 => ctx.idx ⟨i.val, by omega⟩) Finset.univ, (ctx.c p) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hL_e_sub fun _ _ _ => sq_nonneg _
          _ = ∑ i : Fin 16, (ctx.x ⟨i.val, by omega⟩) ^ 2 := by
              rw [Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
              exact Finset.sum_congr rfl fun i _ => (sq_abs _).symm
      have hle_r := (Frac.le_iff (Frac.mk_valid (by norm_num) : (⟨skn, 1000000⟩ : Frac).Valid) valid_SMAX_K0).mp hle_b
      simp only [SMAX_K0, Frac.toReal] at hle_r; push_cast at hle_r; linarith
    exact smax_k0_contra hL ctx.hunit (ctx.hLout L hL) ctx.hF4 hS2_le
  | a18 mode xcap s13n uph skn =>
    unfold checkLeaf at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨hB3, hs13_b⟩, hsk_b⟩, hbess⟩
    have hs13 := sound_checkS13 hb hs13_b
    have hsk := sound_checkSk hb (Or.inr (Or.inr (Or.inr rfl))) ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => hB3⟩ hs13 hsk_b
    obtain ⟨hcard, hA⟩ := antiCount_lt_of_bessel (by omega) hsk hbess
    exact (symp_turan_unified _).2.2.2.2 hcard hA
  | masks mode xcap s13n ms =>
    unfold checkLeaf at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    rcases hok with ⟨⟨⟨⟨hms15, hs13_b⟩, hle_k2⟩, hbess⟩, hall⟩
    have hs13 := sound_checkS13 hb hs13_b
    obtain ⟨hcard14, hA14⟩ := antiCount_lt_of_bessel (by omega) hs13 hbess
    obtain ⟨L, hL, h13⟩ := (symp_turan_unified _).1 hcard14 hA14
    let Z14 := insert (0 : PauliIdx 4) (Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ)
    let S13 := Z14 ∩ L
    change 13 ≤ S13.card at h13
    have h0_S13 : (0 : PauliIdx 4) ∈ S13 := Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hL.1⟩
    have hS13_le14 : S13.card ≤ 14 := by calc S13.card ≤ Z14.card := Finset.card_le_card Finset.inter_subset_left
      _ = 14 := hcard14
    have hS13_ne14 : S13.card ≠ 14 := by
      intro h14
      let T := S13.erase 0
      have hT_sub : T ⊆ L.erase 0 := Finset.erase_subset_erase 0 Finset.inter_subset_right
      have hT_card : T.card = 13 := by rw [Finset.card_erase_of_mem h0_S13, h14]
      have hk2 : (L.erase 0 \ T).card ≤ 2 := by
        rw [Finset.card_sdiff_of_subset hT_sub, Finset.card_erase_of_mem hL.1, hL.2.1, hT_card]; norm_num
      have hT_sub_Z : T ⊆ Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ := by
        intro p hp
        exact (Finset.mem_insert.mp (Finset.mem_inter.mp (Finset.mem_erase.mp hp).2).1).resolve_left (Finset.mem_erase.mp hp).1
      have hT_sum : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ 19 / 1000 := by
        have h1 : ∑ p ∈ T, (ctx.c p) ^ 2 ≤ ctx.S2_13 := by
          calc ∑ p ∈ T, (ctx.c p) ^ 2
              ≤ ∑ p ∈ Finset.image (fun i : Fin 13 => ctx.idx ⟨i.val, by omega⟩) Finset.univ, (ctx.c p) ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hT_sub_Z fun _ _ _ => sq_nonneg _
            _ = ctx.S2_13 := by
                rw [Finset.sum_image (fun a _ b _ h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext h')]
                exact Finset.sum_congr rfl fun i _ => (sq_abs _).symm
        have hle_r := (Frac.le_iff (Frac.mk_valid (by norm_num) : (⟨s13n, 1000000⟩ : Frac).Valid) valid_SMAX_K2).mp hle_k2
        simp only [SMAX_K2, Frac.toReal] at hle_r; push_cast at hle_r; linarith
      exact smax_k2_contra hL hT_sub hk2 ctx.hunit (ctx.hLout L hL) ctx.hF4 hT_sum
    have hS13_card : S13.card = 13 := by omega
    have hdiff_card : (Z14 \ S13).card = 1 := by
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_left, hcard14, hS13_card]
    obtain ⟨uPt, hu_eq⟩ := Finset.card_eq_one.mp hdiff_card
    have hu_mem : uPt ∈ Z14 \ S13 := hu_eq ▸ Finset.mem_singleton_self uPt
    have huZ : uPt ∈ Z14 := (Finset.mem_sdiff.mp hu_mem).1
    have huS : uPt ∉ S13 := (Finset.mem_sdiff.mp hu_mem).2
    have huL : uPt ∉ L := fun h => huS (Finset.mem_inter.mpr ⟨huZ, h⟩)
    have hu0 : uPt ≠ 0 := fun h0 => huL (h0 ▸ hL.1)
    have hZ14_eq : Z14 = insert uPt S13 := by
      ext p; simp only [Finset.mem_insert]
      constructor
      · intro hpZ
        by_cases hpS : p ∈ S13
        · exact Or.inr hpS
        · left; have : p ∈ ({uPt} : Finset (PauliIdx 4)) := hu_eq ▸ Finset.mem_sdiff.mpr ⟨hpZ, hpS⟩
          exact Finset.mem_singleton.mp this
      · rintro (rfl | hpS)
        · exact huZ
        · exact (Finset.mem_inter.mp hpS).1
    -- Define `mask ∈ 0..14`!
    let b0 : Nat := if ctx.idx ⟨13, by omega⟩ ∈ L then 1 else 0
    let b1 : Nat := if ctx.idx ⟨14, by omega⟩ ∈ L then 2 else 0
    let b2 : Nat := if ctx.idx ⟨15, by omega⟩ ∈ L then 4 else 0
    let b3 : Nat := if ctx.idx ⟨16, by omega⟩ ∈ L then 8 else 0
    let mask : Nat := b0 + b1 + b2 + b3
    have hmask_ne15 : mask ≠ 15 := by
      intro h15
      have h0L : ctx.idx ⟨13, by omega⟩ ∈ L := by
        by_contra hc; simp only [mask, b0, b1, b2, b3, hc, ↓reduceIte] at h15
        split_ifs at h15 <;> omega
      have h1L : ctx.idx ⟨14, by omega⟩ ∈ L := by
        by_contra hc; simp only [mask, b0, b1, b2, b3, hc, ↓reduceIte] at h15
        split_ifs at h15 <;> omega
      have h2L : ctx.idx ⟨15, by omega⟩ ∈ L := by
        by_contra hc; simp only [mask, b0, b1, b2, b3, hc, ↓reduceIte] at h15
        split_ifs at h15 <;> omega
      have h3L : ctx.idx ⟨16, by omega⟩ ∈ L := by
        by_contra hc; simp only [mask, b0, b1, b2, b3, h0L, h1L, h2L, hc, ↓reduceIte] at h15
        omega
      let P4 := Finset.univ.image (fun j : Fin 4 => ctx.idx ⟨13 + j.val, by omega⟩)
      have hP4_sub : P4 ⊆ L := by
        intro p hp; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
        fin_cases j <;> assumption
      have hdisj : Disjoint S13 P4 := by
        rw [Finset.disjoint_left]; intro p hpS hpP
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpP
        have hpZ : ctx.idx ⟨13 + j.val, by omega⟩ ∈ Z14 := (Finset.mem_inter.mp hpS).1
        rcases Finset.mem_insert.mp hpZ with h0 | hI
        · exact ctx.idx_ne0 _ h0
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hI
          have h' := congr_arg Fin.val (ctx.idx_inj hi); dsimp at h'; omega
      have hcard17 : (S13 ∪ P4).card = 17 := by
        rw [Finset.card_union_of_disjoint hdisj, hS13_card,
            Finset.card_image_of_injective _ (fun a b h => by have h' := congr_arg Fin.val (ctx.idx_inj h); dsimp at h'; exact Fin.ext (by omega)),
            Finset.card_fin]
      have hle16 : (S13 ∪ P4).card ≤ 16 := by
        calc (S13 ∪ P4).card ≤ L.card := Finset.card_le_card (Finset.union_subset Finset.inter_subset_right hP4_sub)
          _ = 16 := by rw [hL.2.1]; norm_num
      omega
    have hmask_lt : mask < 15 := by
      have hle15 : mask ≤ 15 := by
        simp only [mask, b0, b1, b2, b3]; split_ifs <;> omega
      omega
    have hmask_def : ∀ j : Fin 4, bitSet mask j.val = decide (ctx.idx ⟨13 + j.val, by omega⟩ ∈ L) := by
      intro j
      simp only [mask, b0, b1, b2, b3,
        show (⟨13, by omega⟩ : Fin 255) = 13 from rfl,
        show (⟨14, by omega⟩ : Fin 255) = 14 from rfl,
        show (⟨15, by omega⟩ : Fin 255) = 15 from rfl,
        show (⟨16, by omega⟩ : Fin 255) = 16 from rfl]
      by_cases h0L : ctx.idx 13 ∈ L <;>
      by_cases h1L : ctx.idx 14 ∈ L <;>
      by_cases h2L : ctx.idx 15 ∈ L <;>
      by_cases h3L : ctx.idx 16 ∈ L <;>
      fin_cases j <;> simp [h0L, h1L, h2L, h3L, bitSet]
    have hmc_ok : checkMask A0 A1 A2 A3 B0 B1 B2 B3 mask ⟨s13n, 1000000⟩ ms[mask]! = true :=
      List.all_eq_true.mp hall mask (List.mem_range.mpr hmask_lt)
    exact sound_checkMask hb hL Finset.inter_subset_right h0_S13 hS13_card huL hu0 hZ14_eq hmask_lt hmask_def
      (Frac.mk_valid (by norm_num) : (⟨s13n, 1000000⟩ : Frac).Valid) (by simpa [Frac.toReal] using hs13) hmc_ok

private lemma imax_eq_max (a b : Int) : imax a b = max a b := by
  unfold imax; split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

private lemma imin_eq_min (a b : Int) : imin a b = min a b := by
  unfold imin; split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

/-- Tighten any valid box `(A0..A3, B0..B3)` using coordinate monotonicity `xc 0 ≤ xc 1 ≤ xc 2 ≤ xc 3`. -/
private lemma boxHyp_tighten {ψ : QState 4} {ctx : StateCtx ψ} {A0 A1 A2 A3 B0 B1 B2 B3 : Int}
    (hA0_nn : 0 ≤ A0) (hB3_le : B3 ≤ 32)
    (h0_lo : (A0 : ℝ) / 128 ≤ ctx.xc 0) (h0_hi : ctx.xc 0 ≤ (B0 : ℝ) / 128)
    (h1_lo : (A1 : ℝ) / 128 ≤ ctx.xc 1) (h1_hi : ctx.xc 1 ≤ (B1 : ℝ) / 128)
    (h2_lo : (A2 : ℝ) / 128 ≤ ctx.xc 2) (h2_hi : ctx.xc 2 ≤ (B2 : ℝ) / 128)
    (h3_lo : (A3 : ℝ) / 128 ≤ ctx.xc 3) (h3_hi : ctx.xc 3 ≤ (B3 : ℝ) / 128) :
    let nA1 := imax A1 A0; let nA2 := imax A2 nA1; let nA3 := imax A3 nA2
    let nB2 := imin B2 B3; let nB1 := imin B1 nB2; let nB0 := imin B0 nB1
    BoxHyp ctx A0 nA1 nA2 nA3 nB0 nB1 nB2 B3 := by
  intro nA1 nA2 nA3 nB2 nB1 nB0
  have hxc01 : ctx.xc 0 ≤ ctx.xc 1 := min_le_min_right _ (ctx.idx_mono ⟨13, by omega⟩ ⟨14, by omega⟩ (Fin.le_iff_val_le_val.mpr (by dsimp; omega)))
  have hxc12 : ctx.xc 1 ≤ ctx.xc 2 := min_le_min_right _ (ctx.idx_mono ⟨14, by omega⟩ ⟨15, by omega⟩ (Fin.le_iff_val_le_val.mpr (by dsimp; omega)))
  have hxc23 : ctx.xc 2 ≤ ctx.xc 3 := min_le_min_right _ (ctx.idx_mono ⟨15, by omega⟩ ⟨16, by omega⟩ (Fin.le_iff_val_le_val.mpr (by dsimp; omega)))
  have hmax_le : ∀ {a b : Int} {x : ℝ}, (a : ℝ) / 128 ≤ x → (b : ℝ) / 128 ≤ x → ((imax a b : Int) : ℝ) / 128 ≤ x := by
    intro a b x ha hb; rw [imax_eq_max]; rcases le_total a b with h | h <;> simp [h, ha, hb]
  have hmin_ge : ∀ {a b : Int} {x : ℝ}, x ≤ (a : ℝ) / 128 → x ≤ (b : ℝ) / 128 → x ≤ ((imin a b : Int) : ℝ) / 128 := by
    intro a b x ha hb; rw [imin_eq_min]; rcases le_total a b with h | h <;> simp [h, ha, hb]
  have hn1_lo : (nA1 : ℝ) / 128 ≤ ctx.xc 1 := hmax_le h1_lo (le_trans h0_lo hxc01)
  have hn2_lo : (nA2 : ℝ) / 128 ≤ ctx.xc 2 := hmax_le h2_lo (le_trans hn1_lo hxc12)
  have hn3_lo : (nA3 : ℝ) / 128 ≤ ctx.xc 3 := hmax_le h3_lo (le_trans hn2_lo hxc23)
  have hn2_hi : ctx.xc 2 ≤ (nB2 : ℝ) / 128 := hmin_ge h2_hi (le_trans hxc23 h3_hi)
  have hn1_hi : ctx.xc 1 ≤ (nB1 : ℝ) / 128 := hmin_ge h1_hi (le_trans hxc12 hn2_hi)
  have hn0_hi : ctx.xc 0 ≤ (nB0 : ℝ) / 128 := hmin_ge h0_hi (le_trans hxc01 hn1_hi)
  exact ⟨hA0_nn, by dsimp only [nA1]; rw [imax_eq_max]; exact le_max_right _ _,
    by dsimp only [nA2]; rw [imax_eq_max]; exact le_max_right _ _,
    by dsimp only [nA3]; rw [imax_eq_max]; exact le_max_right _ _,
    by dsimp only [nB0]; rw [imin_eq_min]; exact min_le_right _ _,
    by dsimp only [nB1]; rw [imin_eq_min]; exact min_le_right _ _,
    by dsimp only [nB2]; rw [imin_eq_min]; exact min_le_right _ _,
    hB3_le, h0_lo, hn0_hi, hn1_lo, hn1_hi, hn2_lo, hn2_hi, hn3_lo, h3_hi⟩

/-- Master structural-induction soundness theorem for `checkTree`! -/
private lemma sound_checkTree {ψ : QState 4} {ctx : StateCtx ψ} :
    ∀ (t : CertTree) (A0 A1 A2 A3 B0 B1 B2 B3 : Int),
      0 ≤ A0 → B3 ≤ 32 →
      (A0 : ℝ) / 128 ≤ ctx.xc 0 → ctx.xc 0 ≤ (B0 : ℝ) / 128 →
      (A1 : ℝ) / 128 ≤ ctx.xc 1 → ctx.xc 1 ≤ (B1 : ℝ) / 128 →
      (A2 : ℝ) / 128 ≤ ctx.xc 2 → ctx.xc 2 ≤ (B2 : ℝ) / 128 →
      (A3 : ℝ) / 128 ≤ ctx.xc 3 → ctx.xc 3 ≤ (B3 : ℝ) / 128 →
      checkTree A0 A1 A2 A3 B0 B1 B2 B3 t = true → False
  | .empty, A0, A1, A2, A3, B0, B1, B2, B3, hA0, hB3, h0l, h0h, h1l, h1h, h2l, h2h, h3l, h3h, hok => by
    have hb := boxHyp_tighten hA0 hB3 h0l h0h h1l h1h h2l h2h h3l h3h
    unfold checkTree at hok
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with ((h | h) | h) | h
    · have : (A0 : ℝ) / 128 ≤ ((imin B0 (imin B1 (imin B2 B3)) : Int) : ℝ) / 128 := le_trans hb.h0_lo hb.h0_hi
      have : A0 ≤ imin B0 (imin B1 (imin B2 B3)) := by
        exact_mod_cast (show (A0 : ℝ) ≤ ((imin B0 (imin B1 (imin B2 B3)) : Int) : ℝ) by linarith)
      omega
    · have : ((imax A1 A0 : Int) : ℝ) / 128 ≤ ((imin B1 (imin B2 B3) : Int) : ℝ) / 128 := le_trans hb.h1_lo hb.h1_hi
      have : imax A1 A0 ≤ imin B1 (imin B2 B3) := by
        exact_mod_cast (show ((imax A1 A0 : Int) : ℝ) ≤ ((imin B1 (imin B2 B3) : Int) : ℝ) by linarith)
      omega
    · have : ((imax A2 (imax A1 A0) : Int) : ℝ) / 128 ≤ ((imin B2 B3 : Int) : ℝ) / 128 := le_trans hb.h2_lo hb.h2_hi
      have : imax A2 (imax A1 A0) ≤ imin B2 B3 := by
        exact_mod_cast (show ((imax A2 (imax A1 A0) : Int) : ℝ) ≤ ((imin B2 B3 : Int) : ℝ) by linarith)
      omega
    · have : ((imax A3 (imax A2 (imax A1 A0)) : Int) : ℝ) / 128 ≤ (B3 : ℝ) / 128 := le_trans hb.h3_lo hb.h3_hi
      have : imax A3 (imax A2 (imax A1 A0)) ≤ B3 := by
        exact_mod_cast (show ((imax A3 (imax A2 (imax A1 A0)) : Int) : ℝ) ≤ (B3 : ℝ) by linarith)
      omega
  | .leaf c, A0, A1, A2, A3, B0, B1, B2, B3, hA0, hB3, h0l, h0h, h1l, h1h, h2l, h2h, h3l, h3h, hok => by
    have hb := boxHyp_tighten hA0 hB3 h0l h0h h1l h1h h2l h2h h3l h3h
    exact sound_checkLeaf hb hok
  | .split dim mid lo hi, A0, A1, A2, A3, B0, B1, B2, B3, hA0, hB3, h0l, h0h, h1l, h1h, h2l, h2h, h3l, h3h, hok => by
    have hb := boxHyp_tighten hA0 hB3 h0l h0h h1l h1h h2l h2h h3l h3h
    let nA1 := imax A1 A0; let nA2 := imax A2 nA1; let nA3 := imax A3 nA2
    let nB2 := imin B2 B3; let nB1 := imin B1 nB2; let nB0 := imin B0 nB1
    let m : Int := mid
    have hmin_le : ∀ {a b : Int} {x : ℝ}, x ≤ (a : ℝ) / 128 → x ≤ (b : ℝ) / 128 → x ≤ ((imin a b : Int) : ℝ) / 128 := by
      intro a b x ha hb'; rw [imin_eq_min]; rcases le_total a b with h | h <;> simp [h, ha, hb']
    have hmax_ge : ∀ {a b : Int} {x : ℝ}, (a : ℝ) / 128 ≤ x → (b : ℝ) / 128 ≤ x → ((imax a b : Int) : ℝ) / 128 ≤ x := by
      intro a b x ha hb'; rw [imax_eq_max]; rcases le_total a b with h | h <;> simp [h, ha, hb']
    rcases dim with _ | _ | _ | _ | dim
    · simp only [checkTree, Bool.and_eq_true] at hok
      rcases le_total (ctx.xc 0) ((m : ℝ) / 128) with hle | hge
      · exact sound_checkTree lo A0 nA1 nA2 nA3 (imin nB0 m) nB1 nB2 B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo (hmin_le hb.h0_hi hle) hb.h1_lo hb.h1_hi hb.h2_lo hb.h2_hi hb.h3_lo hb.h3_hi hok.1
      · exact sound_checkTree hi (imax A0 m) nA1 nA2 nA3 nB0 nB1 nB2 B3
          (by rw [imax_eq_max]; exact le_trans hb.hA0_nn (le_max_left _ _)) hb.hB3_le
          (hmax_ge hb.h0_lo hge) hb.h0_hi hb.h1_lo hb.h1_hi hb.h2_lo hb.h2_hi hb.h3_lo hb.h3_hi hok.2
    · simp only [checkTree, Bool.and_eq_true] at hok
      rcases le_total (ctx.xc 1) ((m : ℝ) / 128) with hle | hge
      · exact sound_checkTree lo A0 nA1 nA2 nA3 nB0 (imin nB1 m) nB2 B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo hb.h0_hi hb.h1_lo (hmin_le hb.h1_hi hle) hb.h2_lo hb.h2_hi hb.h3_lo hb.h3_hi hok.1
      · exact sound_checkTree hi A0 (imax nA1 m) nA2 nA3 nB0 nB1 nB2 B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo hb.h0_hi (hmax_ge hb.h1_lo hge) hb.h1_hi hb.h2_lo hb.h2_hi hb.h3_lo hb.h3_hi hok.2
    · simp only [checkTree, Bool.and_eq_true] at hok
      rcases le_total (ctx.xc 2) ((m : ℝ) / 128) with hle | hge
      · exact sound_checkTree lo A0 nA1 nA2 nA3 nB0 nB1 (imin nB2 m) B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo hb.h0_hi hb.h1_lo hb.h1_hi hb.h2_lo (hmin_le hb.h2_hi hle) hb.h3_lo hb.h3_hi hok.1
      · exact sound_checkTree hi A0 nA1 (imax nA2 m) nA3 nB0 nB1 nB2 B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo hb.h0_hi hb.h1_lo hb.h1_hi (hmax_ge hb.h2_lo hge) hb.h2_hi hb.h3_lo hb.h3_hi hok.2
    · simp only [checkTree, Bool.and_eq_true] at hok
      rcases le_total (ctx.xc 3) ((m : ℝ) / 128) with hle | hge
      · exact sound_checkTree lo A0 nA1 nA2 nA3 nB0 nB1 nB2 (imin B3 m) hb.hA0_nn
          (by rw [imin_eq_min]; exact le_trans (min_le_left _ _) hb.hB3_le)
          hb.h0_lo hb.h0_hi hb.h1_lo hb.h1_hi hb.h2_lo hb.h2_hi hb.h3_lo (hmin_le hb.h3_hi hle) hok.1
      · exact sound_checkTree hi A0 nA1 nA2 (imax nA3 m) nB0 nB1 nB2 B3 hb.hA0_nn hb.hB3_le
          hb.h0_lo hb.h0_hi hb.h1_lo hb.h1_hi hb.h2_lo hb.h2_hi (hmax_ge hb.h3_lo hge) hb.h3_hi hok.2
    · simp only [checkTree, Bool.false_eq_true] at hok

/-! ### Section 5: Embedded 174-Leaf Witness Tree & Main Theorem -/

def mainTree : CertTree :=
.split 0 16
  (
    .split 1 16
      (
        .split 2 16
          (
            .split 3 16
              (
                .leaf (.a18 1 512 76761 true 76761)
              )
              (
                .split 0 8
                  (
                    .leaf (.a16 1 256 18954 false 38486)
                  )
                  (
                    .split 3 24
                      (
                        .split 0 12
                          (
                            .leaf (.a16 1 384 11745 false 36160)
                          )
                          (
                            .leaf (.a17 2 512 19305 false 66181)
                          )
                      )
                      (
                        .split 0 12
                          (
                            .leaf (.a16 1 384 15002 false 39417)
                          )
                          (
                            .leaf (.a17 2 512 17003 false 63879)
                          )
                      )
                  )
              )
          )
          (
            .split 0 8
              (
                .leaf (.a16 2 256 17280 false 36812)
              )
              (
                .split 2 24
                  (
                    .split 3 24
                      (
                        .split 0 12
                          (
                            .leaf (.a16 2 384 15399 false 39814)
                          )
                          (
                            .split 2 20
                              (
                                .split 3 20
                                  (
                                    .split 0 14
                                      (
                                        .leaf (.a16 2 448 13622 false 41210)
                                      )
                                      (
                                        .leaf (.a16 2 512 14936 false 46187)
                                      )
                                  )
                                  (
                                    .split 0 14
                                      (
                                        .leaf (.a16 2 448 12794 false 40382)
                                      )
                                      (
                                        .leaf (.a16 3 469 11791 false 43042)
                                      )
                                  )
                              )
                              (
                                .leaf (.a16 2 512 15017 false 46268)
                              )
                          )
                      )
                      (
                        .split 0 12
                          (
                            .leaf (.a16 2 384 14055 false 38470)
                          )
                          (
                            .leaf (.a16 2 512 15252 false 46503)
                          )
                      )
                  )
                  (
                    .split 0 12
                      (
                        .leaf (.a16 2 384 12849 false 37264)
                      )
                      (
                        .leaf (.a16 3 427 10171 false 41422)
                      )
                  )
              )
          )
      )
      (
        .split 0 8
          (
            .leaf (.a15 2 256 12449 false 16356)
          )
          (
            .split 1 24
              (
                .split 2 24
                  (
                    .split 3 24
                      (
                        .split 0 12
                          (
                            .split 1 20
                              (
                                .leaf (.a16 2 384 12696 false 45900)
                              )
                              (
                                .leaf (.a15 2 384 9897 false 18687)
                              )
                          )
                          (
                            .split 1 20
                              (
                                .split 2 20
                                  (
                                    .split 3 20
                                      (
                                        .split 0 14
                                          (
                                            .split 1 18
                                              (
                                                .leaf (.a16 2 448 12220 false 43959)
                                              )
                                              (
                                                .leaf (.a16 2 448 10458 false 46835)
                                              )
                                          )
                                          (
                                            .split 1 18
                                              (
                                                .split 2 18
                                                  (
                                                    .leaf (.a17 2 512 13966 false 69142)
                                                  )
                                                  (
                                                    .leaf (.a16 3 424 9228 false 44629)
                                                  )
                                              )
                                              (
                                                .split 0 15
                                                  (
                                                    .leaf (.a16 3 393 7860 false 46007)
                                                  )
                                                  (
                                                    .split 1 19
                                                      (
                                                        .leaf (.a16 4 281 4706 false 42365)
                                                      )
                                                      (
                                                        .leaf (.a16 4 249 3689 false 43729)
                                                      )
                                                  )
                                              )
                                          )
                                      )
                                      (
                                        .split 0 14
                                          (
                                            .split 1 18
                                              (
                                                .leaf (.a16 2 448 11197 false 42936)
                                              )
                                              (
                                                .leaf (.a16 3 407 8758 false 45135)
                                              )
                                          )
                                          (
                                            .split 1 18
                                              (
                                                .leaf (.a16 3 422 9443 false 44844)
                                              )
                                              (
                                                .leaf (.a16 4 290 5009 false 45049)
                                              )
                                          )
                                      )
                                  )
                                  (
                                    .split 0 14
                                      (
                                        .leaf (.a16 3 443 10457 false 46834)
                                      )
                                      (
                                        .split 1 18
                                          (
                                            .leaf (.a16 3 376 7417 false 42818)
                                          )
                                          (
                                            .leaf (.a16 4 286 4864 false 44904)
                                          )
                                      )
                                  )
                              )
                              (
                                .split 0 14
                                  (
                                    .split 1 22
                                      (
                                        .split 2 22
                                          (
                                            .split 3 22
                                              (
                                                .leaf (.a15 4 294 5144 false 17107)
                                              )
                                              (
                                                .leaf (.a15 4 271 4372 false 16335)
                                              )
                                          )
                                          (
                                            .leaf (.a15 4 262 4085 false 16048)
                                          )
                                      )
                                      (
                                        .leaf (.a15 4 253 3811 false 15774)
                                      )
                                  )
                                  (
                                    .leaf (.masks 4 281 4701 #[.b 6 3 3 3, .b 6 3 3 3, .b 6 0 3 3, .b 6 3 7 7, .b 6 3 0 3, .b 6 7 3 7, .b 6 0 0 3, .q [(1, 0)], .b 6 3 3 0, .b 6 7 7 3, .b 6 0 3 0, .q [(1, 0)], .b 6 3 0 0, .q [(1, 0)], .b 12 0 0 0])
                                  )
                              )
                          )
                      )
                      (
                        .split 0 12
                          (
                            .split 1 20
                              (
                                .leaf (.a16 2 384 10679 false 43883)
                              )
                              (
                                .leaf (.a15 2 384 8998 false 17788)
                              )
                          )
                          (
                            .split 1 20
                              (
                                .split 2 20
                                  (
                                    .split 3 28
                                      (
                                        .split 0 14
                                          (
                                            .leaf (.a16 3 395 8681 false 45058)
                                          )
                                          (
                                            .leaf (.a16 4 306 5576 false 45616)
                                          )
                                      )
                                      (
                                        .leaf (.a16 4 322 6168 false 46208)
                                      )
                                  )
                                  (
                                    .leaf (.a16 4 313 5830 false 45870)
                                  )
                              )
                              (
                                .leaf (.masks 4 271 4366 #[.b 6 3 3 0, .b 6 7 7 0, .b 6 0 3 0, .q [(1, 21), (3, 160), (2, 0)], .b 6 3 0 0, .q [(1, 21), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 0)], .b 6 3 3 0, .b 6 7 7 0, .b 6 0 3 0, .q [(1, 22), (3, 160), (2, 0)], .b 6 3 0 0, .q [(1, 22), (3, 160), (2, 0)], .b 12 0 0 0])
                              )
                          )
                      )
                  )
                  (
                    .split 0 12
                      (
                        .leaf (.a15 2 384 9647 false 18437)
                      )
                      (
                        .split 1 20
                          (
                            .leaf (.a16 4 297 5246 false 45286)
                          )
                          (
                            .leaf (.masks 4 256 3901 #[.b 6 3 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 22), (3, 160), (2, 0)], .b 6 3 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 23), (3, 160), (2, 0)], .b 6 3 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 23), (3, 160), (2, 0)], .b 6 3 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0])
                          )
                      )
                  )
              )
              (
                .split 0 12
                  (
                    .leaf (.a15 2 384 8441 false 17231)
                  )
                  (
                    .leaf (.masks 4 242 3486 #[.b 12 0 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0, .q [(1, 26), (3, 160), (2, 0)], .b 12 0 0 0])
                  )
              )
          )
      )
  )
  (
    .split 0 24
      (
        .split 1 24
          (
            .split 2 24
              (
                .split 3 24
                  (
                    .split 0 20
                      (
                        .split 1 20
                          (
                            .split 2 20
                              (
                                .split 3 20
                                  (
                                    .split 0 18
                                      (
                                        .split 1 18
                                          (
                                            .split 2 18
                                              (
                                                .split 3 18
                                                  (
                                                    .split 0 17
                                                      (
                                                        .leaf (.a17 3 476 11381 false 68571)
                                                      )
                                                      (
                                                        .leaf (.a16 3 371 6826 false 46377)
                                                      )
                                                  )
                                                  (
                                                    .leaf (.a17 3 411 8635 false 67962)
                                                  )
                                              )
                                              (
                                                .split 0 17
                                                  (
                                                    .leaf (.a16 3 379 7284 false 44699)
                                                  )
                                                  (
                                                    .leaf (.a16 4 267 4246 false 43797)
                                                  )
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 278 4602 #[.b 5 4 4 4, .b 0 4 4 4, .b 5 0 4 4, .b 0 0 9 9, .b 5 4 0 4, .b 0 9 0 9, .b 5 0 0 4, .b 5 4 4 9, .b 5 4 4 0, .b 0 9 9 0, .b 5 0 4 0, .b 5 4 9 4, .b 5 4 0 0, .b 5 9 4 4, .b 10 0 0 0])
                                          )
                                      )
                                      (
                                        .leaf (.masks 4 261 4056 #[.b 4 4 4 4, .b 0 4 4 4, .b 4 0 4 4, .b 0 0 9 9, .b 4 4 0 4, .b 0 9 0 9, .b 9 0 0 9, .b 4 4 4 9, .b 4 4 4 0, .b 0 9 9 0, .b 9 0 9 0, .b 4 4 9 4, .b 9 9 0 0, .b 4 9 4 4, .b 9 4 4 4])
                                      )
                                  )
                                  (
                                    .split 0 18
                                      (
                                        .split 1 18
                                          (
                                            .split 2 18
                                              (
                                                .leaf (.a16 3 370 7184 false 46735)
                                              )
                                              (
                                                .leaf (.a16 4 282 4730 false 44281)
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 262 4086 #[.b 5 4 4 3, .b 0 4 4 3, .b 5 0 4 3, .b 0 0 9 7, .b 5 4 0 3, .b 0 9 0 7, .b 10 0 0 7, .q [(1, 0)], .b 5 4 4 0, .b 0 9 9 0, .b 5 0 4 0, .b 5 4 9 3, .b 5 4 0 0, .b 5 9 4 3, .b 10 0 0 0])
                                          )
                                      )
                                      (
                                        .leaf (.masks 4 243 3518 #[.b 4 4 4 3, .b 0 4 4 3, .b 4 0 4 3, .b 0 0 9 7, .b 4 4 0 3, .b 0 9 0 7, .b 9 0 0 7, .q [(1, 0)], .b 4 4 4 0, .b 0 4 4 0, .b 4 0 4 0, .b 4 4 9 3, .b 4 4 0 0, .b 4 9 4 3, .b 9 4 4 3])
                                      )
                                  )
                              )
                              (
                                .split 0 18
                                  (
                                    .split 1 18
                                      (
                                        .leaf (.a16 4 277 4570 false 44121)
                                      )
                                      (
                                        .leaf (.masks 4 258 3959 #[.b 5 4 3 3, .b 0 9 7 7, .b 5 0 3 3, .b 5 4 7 7, .b 5 4 0 3, .b 0 9 0 7, .b 10 0 0 7, .q [(1, 0)], .b 5 4 3 0, .b 0 9 7 0, .b 10 0 7 0, .q [(1, 0)], .b 5 4 0 0, .b 5 9 3 3, .b 10 0 0 0])
                                      )
                                  )
                                  (
                                    .leaf (.masks 4 239 3403 #[.b 4 4 3 3, .b 0 9 7 7, .b 9 0 7 7, .b 4 4 7 7, .b 4 4 0 3, .b 0 9 0 7, .b 9 0 0 7, .q [(1, 0)], .b 4 4 3 0, .b 0 9 7 0, .b 9 0 7 0, .q [(1, 0)], .b 4 4 0 0, .b 4 9 3 3, .b 9 4 3 3])
                                  )
                              )
                          )
                          (
                            .leaf (.masks 4 260 4029 #[.b 4 3 3 3, .b 0 7 7 7, .b 9 0 7 7, .q [(1, 16), (3, 160), (2, 0)], .b 9 7 0 7, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 0 7, .q [(1, 0)], .b 9 7 7 0, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 7 0, .q [(1, 0)], .b 9 7 0 0, .q [(1, 0)], .q [(1, 0)]])
                          )
                      )
                      (
                        .leaf (.masks 4 231 3179 #[.b 7 7 7 7, .b 0 7 7 7, .b 7 0 7 7, .q [(1, 13), (3, 160), (2, 0)], .b 7 7 0 7, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 7 0, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                      )
                  )
                  (
                    .split 0 20
                      (
                        .split 1 20
                          (
                            .split 2 20
                              (
                                .leaf (.masks 4 281 4698 #[.b 4 4 4 0, .b 0 9 9 0, .b 9 0 9 0, .b 4 4 9 0, .b 9 9 0 0, .b 4 9 4 0, .b 9 4 4 0, .q [(1, 0)], .b 4 4 4 0, .b 0 9 9 0, .b 9 0 9 0, .b 4 4 9 0, .b 9 9 0 0, .b 4 9 4 0, .b 9 4 4 0])
                              )
                              (
                                .leaf (.masks 4 242 3484 #[.b 4 4 3 0, .b 0 9 7 0, .b 9 0 7 0, .q [(1, 22), (3, 160), (2, 0)], .b 4 4 0 0, .b 4 9 3 0, .b 9 4 3 0, .q [(1, 0)], .b 4 4 3 0, .b 0 9 7 0, .b 9 0 7 0, .q [(1, 24), (3, 160), (2, 0)], .b 4 4 0 0, .b 4 9 3 0, .b 9 4 3 0])
                              )
                          )
                          (
                            .leaf (.masks 4 206 2527 #[.b 4 3 3 0, .q [(1, 22), (3, 160), (2, 0)], .b 9 0 7 0, .q [(1, 18), (3, 160), (2, 0)], .b 9 7 0 0, .q [(1, 18), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 0)], .b 4 3 3 0, .q [(1, 23), (3, 160), (2, 0)], .b 9 0 7 0, .q [(1, 19), (3, 160), (2, 0)], .b 9 7 0 0, .q [(1, 19), (3, 160), (2, 0)], .b 14 0 0 0])
                          )
                      )
                      (
                        .split 3 28
                          (
                            .split 0 22
                              (
                                .leaf (.masks 4 167 1657 #[.b 4 3 3 1, .q [(1, 22), (3, 160), (2, 0)], .b 8 0 7 3, .q [(1, 17), (3, 160), (2, 0)], .b 8 7 0 3, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .b 4 3 3 0, .q [(1, 13), (3, 160), (2, 0)], .b 8 0 7 0, .q [(1, 0)], .b 8 7 0 0, .q [(1, 0)], .q [(1, 0)]])
                              )
                              (
                                .leaf (.masks 4 135 1081 #[.b 7 7 7 3, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 7 0, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                              )
                          )
                          (
                            .leaf (.masks 4 128 974 #[.b 7 7 7 0, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 7 0, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)]])
                          )
                      )
                  )
              )
              (
                .split 0 20
                  (
                    .split 1 20
                      (
                        .leaf (.masks 4 228 3097 #[.b 4 4 0 0, .b 4 9 0 0, .b 9 4 0 0, .q [(1, 23), (3, 160), (2, 0)], .b 4 4 0 0, .b 4 9 0 0, .b 9 4 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 4 4 0 0, .b 4 9 0 0, .b 9 4 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 4 4 0 0, .b 4 9 0 0, .b 9 4 0 0])
                      )
                      (
                        .leaf (.masks 4 194 2237 #[.b 9 7 0 0, .q [(1, 23), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 19), (3, 160), (2, 0)], .b 9 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 20), (3, 160), (2, 0)], .b 9 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 20), (3, 160), (2, 0)], .b 9 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0])
                      )
                  )
                  (
                    .split 2 28
                      (
                        .split 3 28
                          (
                            .split 0 22
                              (
                                .leaf (.masks 4 153 1389 #[.b 8 7 3 3, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 8 7 0 3, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 8 7 3 0, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 8 7 0 0, .q [(1, 0)], .q [(1, 0)]])
                              )
                              (
                                .split 2 26
                                  (
                                    .split 3 26
                                      (
                                        .leaf (.masks 4 127 961 #[.b 7 7 5 5, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .b 7 7 0 5, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 5 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                      (
                                        .leaf (.masks 4 106 665 #[.b 7 7 5 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 5 0, .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                  )
                                  (
                                    .split 0 23
                                      (
                                        .leaf (.masks 4 101 608 #[.b 7 7 3 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .b 7 7 0 3, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 3 0, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 0 0, .q [(1, 0)], .q [(1, 0)]])
                                      )
                                      (
                                        .split 2 27
                                          (
                                            .leaf (.masks 4 93 515 #[.b 7 7 4 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 4 0, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                          (
                                            .leaf (.masks 4 82 400 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                              )
                          )
                          (
                            .split 0 22
                              (
                                .leaf (.masks 4 109 708 #[.b 8 7 3 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .b 8 7 0 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 8 7 3 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .b 8 7 0 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)]])
                              )
                              (
                                .split 2 26
                                  (
                                    .leaf (.masks 4 87 450 #[.b 7 7 5 0, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .b 7 7 5 0, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)]])
                                  )
                                  (
                                    .leaf (.masks 4 84 417 #[.q [(1, 29), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)]])
                                  )
                              )
                          )
                      )
                      (
                        .split 0 22
                          (
                            .leaf (.masks 4 103 631 #[.b 8 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .b 8 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .b 8 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .b 8 7 0 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)]])
                          )
                          (
                            .leaf (.masks 4 82 400 #[.q [(1, 29), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)]])
                          )
                      )
                  )
              )
          )
          (
            .split 0 20
              (
                .leaf (.masks 4 182 1967 #[.b 14 0 0 0, .q [(1, 23), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 24), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 14 0 0 0, .q [(1, 25), (3, 160), (2, 0)], .b 14 0 0 0])
              )
              (
                .split 1 28
                  (
                    .split 2 28
                      (
                        .split 3 28
                          (
                            .split 0 22
                              (
                                .split 1 26
                                  (
                                    .split 2 26
                                      (
                                        .split 3 26
                                          (
                                            .leaf (.masks 4 131 1018 #[.b 8 5 5 5, .q [(1, 23), (3, 160), (2, 0)], .b 8 0 5 5, .q [(1, 17), (3, 160), (2, 0)], .b 8 5 0 5, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 8 5 5 0, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                          (
                                            .leaf (.masks 4 109 705 #[.b 8 5 5 3, .q [(1, 24), (3, 160), (2, 0)], .b 8 0 5 3, .q [(1, 17), (3, 160), (2, 0)], .b 8 5 0 3, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 8 5 5 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                      (
                                        .split 0 21
                                          (
                                            .leaf (.masks 4 105 654 #[.b 9 5 3 3, .q [(1, 25), (3, 160), (2, 0)], .b 9 0 3 3, .q [(1, 19), (3, 160), (2, 0)], .b 9 5 0 3, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 0 3, .q [(1, 0)], .b 9 5 3 0, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 3 0, .q [(1, 0)], .b 9 5 0 0, .q [(1, 0)], .b 13 0 0 0])
                                          )
                                          (
                                            .leaf (.masks 4 100 593 #[.b 8 5 3 3, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 8 5 0 3, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 8 5 3 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 8 5 0 0, .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                                  (
                                    .split 0 21
                                      (
                                        .leaf (.masks 4 102 617 #[.b 9 3 3 3, .q [(1, 25), (3, 160), (2, 0)], .b 9 0 3 3, .q [(1, 16), (3, 160), (2, 0)], .b 9 3 0 3, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 0 3, .q [(1, 0)], .b 9 3 3 0, .q [(1, 16), (3, 160), (2, 0)], .b 9 0 3 0, .q [(1, 0)], .b 9 3 0 0, .q [(1, 0)], .b 13 0 0 0])
                                      )
                                      (
                                        .split 1 27
                                          (
                                            .split 2 27
                                              (
                                                .split 3 27
                                                  (
                                                    .leaf (.masks 4 95 533 #[.b 8 4 4 4, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                                  (
                                                    .leaf (.masks 4 85 428 #[.b 8 4 4 3, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 8 4 4 0, .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                              (
                                                .leaf (.masks 4 84 419 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 83 410 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                              )
                              (
                                .split 1 26
                                  (
                                    .split 2 26
                                      (
                                        .split 3 26
                                          (
                                            .split 0 23
                                              (
                                                .leaf (.masks 4 121 870 #[.b 7 5 5 5, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .leaf (.masks 4 118 830 #[.b 7 5 5 5, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .split 0 23
                                              (
                                                .leaf (.masks 4 99 581 #[.b 7 5 5 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 7 5 5 0, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .split 1 25
                                                  (
                                                    .split 2 25
                                                      (
                                                        .leaf (.masks 4 94 524 #[.b 7 6 6 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .b 7 6 6 0, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .split 3 27
                                                          (
                                                            .leaf (.masks 4 91 493 #[.b 7 6 5 4, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                          )
                                                          (
                                                            .leaf (.masks 4 82 398 #[.b 7 6 5 3, .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .b 7 6 5 0, .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                          )
                                                      )
                                                  )
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 90 480 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 80 380 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                              )
                                          )
                                      )
                                      (
                                        .split 0 23
                                          (
                                            .split 1 25
                                              (
                                                .split 2 27
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 93 515 #[.b 7 6 4 4, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 7 6 0 4, .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 7 6 4 0, .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 84 418 #[.b 7 6 4 3, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .b 7 6 4 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .leaf (.masks 4 83 409 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                              (
                                                .split 2 27
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 92 501 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 82 399 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .leaf (.masks 4 81 390 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                          )
                                          (
                                            .split 1 25
                                              (
                                                .split 2 27
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 90 482 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 81 387 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .leaf (.masks 4 80 379 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                              (
                                                .split 2 27
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 89 469 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 79 369 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .leaf (.masks 4 78 361 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                          )
                                      )
                                  )
                                  (
                                    .split 0 23
                                      (
                                        .split 1 27
                                          (
                                            .split 2 27
                                              (
                                                .split 3 27
                                                  (
                                                    .leaf (.masks 4 91 490 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                                  (
                                                    .leaf (.masks 4 81 388 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                              (
                                                .leaf (.masks 4 80 380 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 79 371 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                      (
                                        .split 1 27
                                          (
                                            .split 2 27
                                              (
                                                .leaf (.masks 4 88 462 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .leaf (.masks 4 77 351 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 76 343 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                              )
                          )
                          (
                            .split 0 22
                              (
                                .split 1 26
                                  (
                                    .leaf (.masks 4 92 501 #[.b 8 5 3 0, .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 8 5 0 0, .q [(1, 16), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 8 5 3 0, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 8 5 0 0, .q [(1, 16), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)]])
                                  )
                                  (
                                    .split 3 30
                                      (
                                        .split 0 21
                                          (
                                            .split 1 27
                                              (
                                                .leaf (.masks 4 82 398 #[.b 9 4 3 1, .q [(1, 26), (3, 160), (2, 0)], .b 9 0 3 1, .q [(1, 18), (3, 160), (2, 0)], .b 9 4 0 1, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .b 9 4 3 0, .q [(1, 15), (3, 160), (2, 0)], .b 9 0 3 0, .q [(1, 0)], .b 9 4 0 0, .q [(1, 0)], .b 9 0 0 0])
                                              )
                                              (
                                                .leaf (.masks 4 79 372 #[.b 9 3 3 1, .q [(1, 26), (3, 160), (2, 0)], .b 9 0 3 1, .q [(1, 17), (3, 160), (2, 0)], .b 9 3 0 1, .q [(1, 17), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .b 9 3 3 0, .q [(1, 15), (3, 160), (2, 0)], .b 9 0 3 0, .q [(1, 0)], .b 9 3 0 0, .q [(1, 0)], .b 9 0 0 0])
                                              )
                                          )
                                          (
                                            .split 1 27
                                              (
                                                .split 2 27
                                                  (
                                                    .split 3 29
                                                      (
                                                        .leaf (.masks 4 76 342 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 8 4 4 0, .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 67 268 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 26), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .b 8 4 4 0, .q [(3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .split 3 29
                                                      (
                                                        .leaf (.masks 4 75 333 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 66 259 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 26), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 19), (3, 160), (2, 0)], .q [(3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                              )
                                              (
                                                .split 3 29
                                                  (
                                                    .leaf (.masks 4 74 325 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                                  (
                                                    .leaf (.masks 4 65 251 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 26), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 19), (3, 160), (2, 0)], .q [(3, 160), (2, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 10), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                  )
                                              )
                                          )
                                      )
                                      (
                                        .leaf (.masks 4 66 258 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 26), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 26), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)]])
                                      )
                                  )
                              )
                              (
                                .split 1 26
                                  (
                                    .split 2 26
                                      (
                                        .leaf (.masks 4 81 389 #[.q [(1, 29), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)]])
                                      )
                                      (
                                        .leaf (.masks 4 77 353 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)]])
                                      )
                                  )
                                  (
                                    .leaf (.masks 4 74 324 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)]])
                                  )
                              )
                          )
                      )
                      (
                        .split 0 22
                          (
                            .split 1 26
                              (
                                .leaf (.masks 4 86 437 #[.b 8 5 0 0, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 18), (3, 160), (2, 0)], .b 8 5 0 0, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .b 8 5 0 0, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 19), (3, 160), (2, 0)], .b 8 5 0 0, .q [(1, 25), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)]])
                              )
                              (
                                .leaf (.masks 4 82 399 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 25), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)]])
                              )
                          )
                          (
                            .split 1 26
                              (
                                .leaf (.masks 4 76 343 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 17), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)]])
                              )
                              (
                                .leaf (.masks 4 72 309 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)]])
                              )
                          )
                      )
                  )
                  (
                    .leaf (.masks 4 82 399 #[.q [(1, 29), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 29), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 29), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 29), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 24), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)]])
                  )
              )
          )
      )
      (
        .split 0 28
          (
            .split 1 28
              (
                .split 2 28
                  (
                    .split 3 28
                      (
                        .split 0 26
                          (
                            .split 1 26
                              (
                                .split 2 26
                                  (
                                    .split 3 26
                                      (
                                        .split 0 25
                                          (
                                            .split 1 25
                                              (
                                                .leaf (.masks 4 115 787 #[.q [(1, 29), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .leaf (.masks 4 98 571 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 97 558 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                      (
                                        .split 0 25
                                          (
                                            .split 1 25
                                              (
                                                .split 2 25
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 91 490 #[.b 6 6 6 4, .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 81 390 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                                  (
                                                    .split 3 27
                                                      (
                                                        .leaf (.masks 4 89 471 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                      (
                                                        .leaf (.masks 4 79 372 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                                      )
                                                  )
                                              )
                                              (
                                                .leaf (.masks 4 88 461 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .leaf (.masks 4 87 448 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                                  (
                                    .split 0 25
                                      (
                                        .split 1 25
                                          (
                                            .split 2 27
                                              (
                                                .leaf (.masks 4 89 470 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .leaf (.masks 4 77 353 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 16), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                          (
                                            .split 2 27
                                              (
                                                .leaf (.masks 4 87 451 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                              (
                                                .leaf (.masks 4 76 341 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                              )
                                          )
                                      )
                                      (
                                        .split 2 27
                                          (
                                            .leaf (.masks 4 86 437 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                          (
                                            .leaf (.masks 4 74 324 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                  )
                              )
                              (
                                .split 0 25
                                  (
                                    .split 1 27
                                      (
                                        .split 2 27
                                          (
                                            .leaf (.masks 4 86 440 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                          (
                                            .leaf (.masks 4 74 326 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                      (
                                        .leaf (.masks 4 74 323 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 23), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                  )
                                  (
                                    .split 1 27
                                      (
                                        .split 2 27
                                          (
                                            .leaf (.masks 4 85 427 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                          (
                                            .leaf (.masks 4 73 314 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                          )
                                      )
                                      (
                                        .leaf (.masks 4 72 307 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                  )
                              )
                          )
                          (
                            .split 0 27
                              (
                                .split 1 27
                                  (
                                    .split 2 27
                                      (
                                        .leaf (.masks 4 84 417 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                      (
                                        .leaf (.masks 4 71 300 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                      )
                                  )
                                  (
                                    .leaf (.masks 4 71 297 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                                  )
                              )
                              (
                                .leaf (.masks 4 70 290 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 0)]])
                              )
                          )
                      )
                      (
                        .split 0 26
                          (
                            .split 1 26
                              (
                                .split 2 26
                                  (
                                    .leaf (.masks 4 75 333 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 14), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)]])
                                  )
                                  (
                                    .leaf (.masks 4 71 300 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 20), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 15), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)]])
                                  )
                              )
                              (
                                .leaf (.masks 4 68 273 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)]])
                              )
                          )
                          (
                            .leaf (.masks 4 64 244 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)]])
                          )
                      )
                  )
                  (
                    .split 0 26
                      (
                        .leaf (.masks 4 71 299 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 13), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 22), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)]])
                      )
                      (
                        .leaf (.masks 4 63 235 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 11), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 12), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)]])
                      )
                  )
              )
              (
                .leaf (.masks 4 66 259 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 21), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)]])
              )
          )
          (
            .leaf (.masks 4 60 214 #[.q [(1, 30), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 30), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)], .q [(1, 31), (3, 160), (2, 0)]])
          )
      )
  )

set_option maxHeartbeats 800000 in
/-- Pure kernel verification of all 174 leaves of `mainTree` (zero `native_decide`, zero `sorry`)! -/
theorem mainTree_valid : checkTree 0 0 0 0 32 32 32 32 mainTree = true := by
  decide

end FourQubitMUB

/-- **Main 4-Qubit Contextuality-to-MUB Breakthrough Theorem**:
    Under the symplectic contextuality lower bound `CD(W(7,2)) ≥ 1575`
    (equivalently, `∀ σ ∈ {±1}^{𝔽₂⁸ \ {0}}, signCubeSum 4 σ ≤ 6615`),
    EVERY 4-qubit pure quantum state strictly exceeds the 4-qubit Pauli-covariant MUB threshold:
      `F₄(|ψ⟩) = ∑_{p ∈ 𝔽₂⁸} |⟨ψ|P_p|ψ⟩|⁴ > 31 / 16`.
    Proved with zero `sorry`, zero `native_decide`, and standard three axioms only. -/
theorem pauliMoment4_four_gt_mub_of_contextuality_1575
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    (31 / 16 : ℝ) < pauliMoment4 4 ψ := by
  by_contra hle
  push Not at hle
  obtain ⟨ctx⟩ := FourQubitMUB.StateCtx.extract hCD hunit hle
  have hlo : ∀ j : Fin 4, ((0 : Int) : ℝ) / 128 ≤ ctx.xc j := fun j => by
    simp only [FourQubitMUB.StateCtx.xc, Int.cast_zero, zero_div]
    exact le_min (abs_nonneg _) (by norm_num)
  have hhi : ∀ j : Fin 4, ctx.xc j ≤ ((32 : Int) : ℝ) / 128 := fun j => by
    simp only [FourQubitMUB.StateCtx.xc]
    exact le_trans (min_le_right _ _) (by norm_num)
  exact FourQubitMUB.sound_checkTree FourQubitMUB.mainTree 0 0 0 0 32 32 32 32
    (le_refl 0) (le_refl 32)
    (hlo 0) (hhi 0) (hlo 1) (hhi 1) (hlo 2) (hhi 2) (hlo 3) (hhi 3)
    FourQubitMUB.mainTree_valid

end MultiQubitMUB
