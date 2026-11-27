import MultiQubitMUB.FourQubitContextualityCore

set_option linter.constructorNameAsVariable false

/-!
# 56×56 Pure-Integer Cholesky + Diagonal-Dominance Certificate Engine for `CD(Q⁻(7,2)) ≥ 315`

Provides the computable pure-`Nat` verifier `checkCert56` (symmetric lower-triangle biased
`L L^T` + diagonal dominance check) and its exact soundness theorem `sound_checkCert56`:
for ANY 4-qubit sign assignment `s4` on `Q⁻(7,2) = Q(6,2) ⊔ B₅₆` satisfying the 136-slice
minimality condition at `c₀ = 0x88`, if `restrictA s4` is `Sp(6,2)`-equivalent to any certified
orbit representative `cert.s64`, then `frustPairs (Qminus c0_88) s4 ≥ 315 * 6`!
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Concrete Computable `B₅₆`, `otherPout`, `wlines315`, and Pure-`Nat` Verifier -/

def B56_list : List Nat :=
  (List.range 256).filter fun p => p != 0 && Q4_form 136 p == 0 && symp4 136 p == 1

def otherPoutList : List Nat :=
  (List.range 256).filter fun p => p != 0 && p != 136 && Q4_form 136 p == 1

def wlines315 : List (Nat × Nat × Nat × ℤ) :=
  ((List.range 64).flatMap fun p =>
    if p == 0 then []
    else ((List.range 64).flatMap fun q =>
      if q ≤ p || symp3 p q != 0 then []
      else
        let r := p ^^^ q
        if r ≤ q then [] else [(p, q, r, gamma3_sgn p q)]))

set_option maxRecDepth 4096 in
lemma B56_list_len : B56_list.length = 56 := by rfl

set_option maxRecDepth 4096 in
lemma otherPoutList_len : otherPoutList.length = 135 := by rfl

set_option maxRecDepth 8192 in
lemma wlines315_len : wlines315.length = 315 := by rfl

def B56_val (i : Nat) : Nat := B56_list.getD i 0
def otherPout_val (k : Nat) : Nat := otherPoutList.getD k 0

private def checkB56Props : Nat → Bool
  | 0 => true
  | n + 1 =>
    let p := B56_val n
    (p != 0 && p < 256 && Q4_form 136 p == 0 && symp4 136 p == 1) && checkB56Props n

private def checkB56Strict : Nat → Bool
  | 0 => true
  | 1 => true
  | n + 1 => (B56_val (n - 1) < B56_val n) && checkB56Strict n

private def checkB56Surj : Nat → Bool
  | 0 => true
  | n + 1 =>
    let ok :=
      if n != 0 && Q4_form 136 n == 0 && symp4 136 n == 1 then B56_list.contains n
      else true
    ok && checkB56Surj n

private def checkOtherPoutProps : Nat → Bool
  | 0 => true
  | n + 1 =>
    let p := otherPout_val n
    (p < 256 && Q4_form 136 p == 1) && checkOtherPoutProps n

set_option maxRecDepth 8192 in
private lemma checkB56Props_ok : checkB56Props 56 = true := by rfl
set_option maxRecDepth 8192 in
private lemma checkB56Strict_ok : checkB56Strict 56 = true := by rfl
set_option maxRecDepth 8192 in
private lemma checkB56Surj_ok : checkB56Surj 256 = true := by rfl
set_option maxRecDepth 8192 in
private lemma checkOtherPoutProps_ok : checkOtherPoutProps 135 = true := by rfl

lemma B56_val_props (i : Fin 56) :
    B56_val i.val ≠ 0 ∧ B56_val i.val < 256 ∧
    Q4_form 136 (B56_val i.val) = 0 ∧ symp4 136 (B56_val i.val) = 1 := by
  have hs : ∀ m n, n < m → checkB56Props m = true →
      B56_val n ≠ 0 ∧ B56_val n < 256 ∧ Q4_form 136 (B56_val n) = 0 ∧ symp4 136 (B56_val n) = 1 := by
    intro m; induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn hok
      simp only [checkB56Props, Bool.and_eq_true] at hok
      by_cases hnm : n = m
      · subst hnm
        rcases hok.1 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
      · exact ih n (by omega) hok.2
  exact hs 56 i.val i.isLt checkB56Props_ok

lemma B56_val_strictMono {i j : Fin 56} (hij : i.val < j.val) : B56_val i.val < B56_val j.val := by
  have hstep : ∀ m k, k + 1 < m → checkB56Strict m = true → B56_val k < B56_val (k + 1) := by
    intro m; induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      cases m with
      | zero => intro k hk; omega
      | succ m' =>
        intro k hk hok
        simp only [checkB56Strict, Bool.and_eq_true, decide_eq_true_eq] at hok
        by_cases hkm : k = m'
        · subst hkm; simpa using hok.1
        · exact ih k (by omega) hok.2
  have hchain : ∀ d, ∀ k, k + d < 56 → 0 < d → B56_val k < B56_val (k + d) := by
    intro d; induction d with
    | zero => intro _ _ hd; omega
    | succ d ih =>
      intro k hk _
      cases d with
      | zero => exact hstep 56 k (by omega) checkB56Strict_ok
      | succ d' =>
        exact lt_trans (ih k (by omega) (by omega)) (hstep 56 (k + d' + 1) (by omega) checkB56Strict_ok)
  have h := hchain (j.val - i.val) i.val (by omega) (by omega)
  rwa [show i.val + (j.val - i.val) = j.val by omega] at h

lemma B56_val_inj {i j : Fin 56} (h : B56_val i.val = B56_val j.val) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (B56_val_strictMono hlt))
  · exact absurd h.symm (Nat.ne_of_lt (B56_val_strictMono hgt))

private lemma getD_eq_getElem {α : Type*} (L : List α) (d : α) {i : Nat} (hi : i < L.length) :
    L.getD i d = L[i] := by simp [List.getD, hi]

private lemma getD_eq_default {α : Type*} (L : List α) (d : α) {i : Nat} (hi : L.length ≤ i) :
    L.getD i d = d := by simp [List.getD, Nat.not_lt.mpr hi]

private lemma getD_drop {α : Type*} (L : List α) (d : α) (j i : Nat) :
    (L.drop j).getD i d = L.getD (j + i) d := by
  simp only [List.getD, List.getElem?_drop]

private lemma getD_append_left {α : Type*} (L1 L2 : List α) (d : α) {i : Nat} (hi : i < L1.length) :
    (L1 ++ L2).getD i d = L1.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_right {α : Type*} (L1 L2 : List α) (d : α) {i : Nat} (hi : L1.length ≤ i) :
    (L1 ++ L2).getD i d = L2.getD (i - L1.length) d := by
  simp [List.getD, List.getElem?_append_right hi]

private lemma getD_replicate {α : Type*} (n : Nat) (x d : α) (i : Nat) (hi : i < n) :
    (List.replicate n x).getD i d = x := by
  simp [List.getD, hi]

lemma B56_val_surj (p : Fin 256) (hp0 : p.val ≠ 0) (hq : Q4_form 136 p.val = 0)
    (hs : symp4 136 p.val = 1) : ∃ i : Fin 56, B56_val i.val = p.val := by
  have hmem : ∀ m n, n < m → checkB56Surj m = true →
      n ≠ 0 → Q4_form 136 n = 0 → symp4 136 n = 1 → B56_list.contains n = true := by
    intro m; induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn hok h0 hq' hs'
      simp only [checkB56Surj, Bool.and_eq_true] at hok
      by_cases hnm : n = m
      · subst hnm
        have h1 := hok.1
        simp [h0, hq', hs'] at h1
        simpa [List.contains_eq_mem] using h1
      · exact ih n (by omega) hok.2 h0 hq' hs'
  have hc := hmem 256 p.val p.isLt checkB56Surj_ok hp0 hq hs
  rw [List.contains_eq_mem, decide_eq_true_eq] at hc
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  have hilt : i < 56 := by rwa [B56_list_len] at hi
  refine ⟨⟨i, hilt⟩, ?_⟩
  simp only [B56_val, getD_eq_getElem _ _ hi, heq]

def B56_pt (i : Fin 56) : Fin 256 := ⟨B56_val i.val, (B56_val_props i).2.1⟩

lemma otherPout_props (k : Fin 135) :
    otherPout_val k.val < 256 ∧ Q4_form 136 (otherPout_val k.val) = 1 := by
  have hs : ∀ m n, n < m → checkOtherPoutProps m = true →
      otherPout_val n < 256 ∧ Q4_form 136 (otherPout_val n) = 1 := by
    intro m; induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn hok
      simp only [checkOtherPoutProps, Bool.and_eq_true] at hok
      by_cases hnm : n = m
      · subst hnm
        exact ⟨by simpa using hok.1.1, by simpa using hok.1.2⟩
      · exact ih n (by omega) hok.2
  exact hs 135 k.val k.isLt checkOtherPoutProps_ok

def otherPoutFin (k : Fin 135) : Fin 256 := ⟨otherPout_val k.val, (otherPout_props k).1⟩

def isEdge56b (i j : Nat) : Bool :=
  i != j && symp4 (B56_val i) (B56_val j) == 0

def inSlice56b (k i j : Nat) : Bool :=
  isEdge56b i j && symp4 (otherPout_val k) (B56_val i) == 0 &&
  symp4 (otherPout_val k) (B56_val j) == 0

/-- Read sign `s[p3] ∈ {-1, 1}` for `p3 ∈ 1..63` from a 63-element list `s64` (`p3 = 0` gives `0`). -/
def getS64 (s64 : List ℤ) (p3 : Nat) : ℤ :=
  if p3 == 0 then 0 else s64.getD (p3 - 1) 0

def wEdge56c (s64 : List ℤ) (i j : Nat) : ℤ :=
  if isEdge56b i j then
    let bi := B56_val i
    let bj := B56_val j
    gamma4_sgn bi bj * getS64 s64 (proj43Nat (bi ^^^ bj))
  else 0

def countFrustWlines (s64 : List ℤ) : Nat :=
  wlines315.foldl (fun acc (a, b, c, g) =>
    if g * getS64 s64 a * getS64 s64 b * getS64 s64 c == -1 then acc + 1 else acc) 0

def countFrustWlinesSlice (k : Nat) (s64 : List ℤ) : Nat :=
  let po := otherPout_val k
  wlines315.foldl (fun acc (a, b, c, g) =>
    if symp4 po (ApauliNat a) == 0 && symp4 po (ApauliNat b) == 0 &&
       g * getS64 s64 a * getS64 s64 b * getS64 s64 c == -1
    then acc + 1 else acc) 0

/-- Exact ordered edge count `2 * E_B_sl[k]` in slice `k`. -/
def orderedEdgesInSlice (k : Nat) : Nat :=
  (List.range 56).foldl (fun acc i =>
    acc + ((List.range 56).filter fun j => inSlice56b k i j).length) 0

/-- Precomputed table of `orderedEdgesInSlice k` for all `k ∈ 0..134`. -/
def EB_ord_table : List Nat := (List.range 135).map orderedEdgesInSlice

/-- Exact ordered edge count `2 * E_B` in `B₅₆`. -/
def orderedEdgesTotal : Nat :=
  (List.range 56).foldl (fun acc i =>
    acc + ((List.range 56).filter fun j => isEdge56b i j).length) 0

set_option maxRecDepth 8192 in
lemma orderedEdgesTotal_eq : orderedEdgesTotal = 1512 := by rfl

/-! #### Pure-`Nat` Biased Symmetric Lower-Triangle Cholesky + Diagonal Dominance Engine -/

def BIAS : Nat := 16384
def BIAS2 : Nat := 268435456

def dotAndSums : List Nat → List Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | x :: xs, y :: ys, d, sa, sb =>
    dotAndSums xs ys (Nat.add d (Nat.mul x y)) (Nat.add sa x) (Nat.add sb y)
  | _, _, d, sa, sb => (d, sa, sb)

def addPrefix : List Nat → List Nat → List Nat
  | x :: xs, y :: ys => Nat.add x y :: addPrefix xs ys
  | [], ys => ys
  | xs, [] => xs

def checkLowerRowAux (B B2 QOFF : Nat) (rowA : List Nat) (i : Nat) :
    Nat → List Nat → List (List Nat) → Nat → List Nat → Option (Nat × Nat × List Nat)
  | j, [qii], rowAj :: _, offBelow, revAbs =>
    if Nat.beq i j then
      let (d, sa, sb) := dotAndSums rowA rowAj 0 0 0
      let posT := Nat.add qii (Nat.mul B (Nat.add sa sb))
      let negT := Nat.add QOFF (Nat.add d (Nat.mul (Nat.add j 1) B2))
      if Nat.ble negT posT then
        some (Nat.sub posT negT, offBelow, revAbs.reverse)
      else none
    else none
  | j, qij :: qs, rowAj :: rowsA, offBelow, revAbs =>
    let (d, sa, sb) := dotAndSums rowA rowAj 0 0 0
    let posT := Nat.add qij (Nat.mul B (Nat.add sa sb))
    let negT := Nat.add QOFF (Nat.add d (Nat.mul (Nat.add j 1) B2))
    let absR := if Nat.ble negT posT then Nat.sub posT negT else Nat.sub negT posT
    checkLowerRowAux B B2 QOFF rowA i (Nat.add j 1) qs rowsA (Nat.add offBelow absR) (absR :: revAbs)
  | _, _, _, _, _ => none

def checkLowerRow (QOFF : Nat) := checkLowerRowAux BIAS BIAS2 QOFF

def cmpDiagOff : List Nat → List Nat → List Nat → Bool
  | d :: ds, ob :: obs, oa :: oas =>
    if Nat.ble (Nat.add ob oa) d then cmpDiagOff ds obs oas else false
  | [], [], _ => true
  | _, _, _ => false

def checkAllRowsAux (B B2 QOFF : Nat) (allA : List (List Nat)) :
    Nat → List (List Nat) → List (List Nat) → List Nat → List Nat → List Nat → Bool
  | i, [], [], revDiags, revOffB, offAbove =>
    Nat.beq i 56 && cmpDiagOff revDiags.reverse revOffB.reverse offAbove
  | i, rowQ :: rowsQ, rowA :: rowsA, revDiags, revOffB, offAbove =>
    match checkLowerRowAux B B2 QOFF rowA i 0 rowQ allA 0 [] with
    | none => false
    | some (diagI, offB, absList) =>
      checkAllRowsAux B B2 QOFF allA (Nat.add i 1) rowsQ rowsA
        (diagI :: revDiags) (offB :: revOffB) (addPrefix absList offAbove)
  | _, _, _, _, _, _ => false

def checkAllRows (QOFF : Nat) := checkAllRowsAux BIAS BIAS2 QOFF

def checkALens (i : Nat) : List (List Nat) → Bool
  | [] => Nat.beq i 56
  | row :: rest =>
    if Nat.beq i 56 then false
    else Nat.beq row.length (Nat.add i 1) && checkALens (Nat.add i 1) rest

/-- Complete exact integer `56 × 56` SOS + Cholesky + DD certificate for one `Sp(6,2)`-orbit. -/
structure Cert56 where
  fA0 : Nat
  S : Nat
  K : Nat
  mu : Nat
  QOFF : Nat
  s64 : List ℤ
  alphas : List (Nat × Nat)
  betas : List (Nat × Nat × Nat × Nat)
  di : List ℤ
  Arows : List (List Nat)
  Qlow : List (List Nat)

def ecSpec (S : Nat) (alphas : List (Nat × Nat)) (betas : List (Nat × Nat × Nat × Nat))
    (i j : Nat) : ℤ :=
  let subA : ℤ := alphas.foldl (fun acc (k, val) =>
    if inSlice56b k i j then acc + (val : ℤ) else acc) 0
  let subB : ℤ := betas.foldl (fun acc (a, b, c, val) =>
    if (i == a && j == b) || (i == b && j == a) ||
       (i == b && j == c) || (i == c && j == b) ||
       (i == a && j == c) || (i == c && j == a)
    then acc + (val : ℤ) else acc) 0
  (S : ℤ) - subA - subB

def Qspec (c : Cert56) (i j : Nat) : ℤ :=
  if i == j then (c.mu : ℤ) + c.di.getD i 0
  else if isEdge56b i j then -(ecSpec c.S c.alphas c.betas i j * wEdge56c c.s64 i j)
  else 0

def checkQRow (c : Cert56) (K2 : ℤ) (i : Nat) : Nat → List Nat → Bool
  | j, [] => Nat.beq j (Nat.add i 1)
  | j, qij :: qs =>
    let ok := ((qij : ℤ) == K2 * Qspec c i j + (c.QOFF : ℤ))
    if ok then checkQRow c K2 i (Nat.add j 1) qs else false

def checkQMatch (c : Cert56) (K2 : ℤ) : Nat → List (List Nat) → Bool
  | i, [] => Nat.beq i 56
  | i, row :: rows =>
    if checkQRow c K2 i 0 row then checkQMatch c K2 (Nat.add i 1) rows else false

def checkAlphas (alphas : List (Nat × Nat)) : Bool :=
  alphas.all fun (k, val) => k < 135 && 0 < val

def checkBetas (s64 : List ℤ) (betas : List (Nat × Nat × Nat × Nat)) : Bool :=
  betas.all fun (a, b, c, val) =>
    a < b && b < c && c < 56 && 0 < val &&
    isEdge56b a b && isEdge56b b c && isEdge56b a c &&
    wEdge56c s64 a b * wEdge56c s64 b c * wEdge56c s64 a c == -1

def computeLinI (c : Cert56) : ℤ :=
  let linA := c.alphas.foldl (fun acc (k, val) =>
    let eb : ℤ := (EB_ord_table.getD k 0 : ℤ)
    let ca : ℤ := (countFrustWlinesSlice k c.s64 : ℤ)
    acc + (val : ℤ) * (eb + 4 * (ca - (c.fA0 : ℤ)))) 0
  let linB := c.betas.foldl (fun acc (_, _, _, val) => acc + 2 * (val : ℤ)) 0
  linA + linB

/-- Master pure-kernel checker for a `Cert56` (zero floats, zero `native_decide`). -/
def checkCert56 (c : Cert56) : Bool :=
  (0 < c.S) && (0 < c.K) &&
  (c.s64.length == 63) &&
  (c.s64.all fun x => x == 1 || x == -1) &&
  (countFrustWlines c.s64 == c.fA0) &&
  (c.di.length == 56) &&
  (c.di.foldl (· + ·) 0 == 0) &&
  checkAlphas c.alphas &&
  checkBetas c.s64 c.betas &&
  (decide (computeLinI c + 56 * (c.mu : ℤ) < (c.S : ℤ) * (256 + 4 * (c.fA0 : ℤ)))) &&
  checkALens 0 c.Arows &&
  checkQMatch c ((c.K : ℤ) * (c.K : ℤ)) 0 c.Qlow &&
  checkAllRows c.QOFF c.Arows 0 c.Qlow c.Arows [] [] (List.replicate 56 0)

/-! ### Section 2: Exact Soundness of `checkAllRows` & `checkCert56` (`Classical`) -/

section CertSoundness

open scoped Classical

/-- Pure integer identity for `dotAndSums`:
    given `rowA` of length `≥ j + 1` and `rowAj` of length `j + 1`,
    `(d, sa, sb)` equals `(∑_{k≤j} A_i[k] A_j[k], ∑_{k≤j} A_i[k], ∑_{k≤j} A_j[k])`. -/
private lemma dotAndSums_spec (B B2 : Nat) (hB2 : (B2 : ℤ) = (B : ℤ) * (B : ℤ)) :
    ∀ (xs ys : List Nat) (d sa sb : Nat), ys.length ≤ xs.length →
      let res := dotAndSums xs ys d sa sb
      (res.1 : ℤ) - (B : ℤ) * ((res.2.1 : ℤ) + (res.2.2 : ℤ)) +
        ((ys.length : ℤ) * (B2 : ℤ)) =
      (d : ℤ) - (B : ℤ) * ((sa : ℤ) + (sb : ℤ)) +
        ∑ k : Fin ys.length,
          ((xs.getD k.val 0 : ℤ) - (B : ℤ)) * ((ys.getD k.val 0 : ℤ) - (B : ℤ)) := by
  intro xs ys
  induction ys generalizing xs with
  | nil =>
    intro d sa sb _
    simp [dotAndSums]
  | cons y ys ih =>
    intro d sa sb hlen
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      simp only [dotAndSums, List.length_cons] at hlen ⊢
      have hih := ih xs (Nat.add d (Nat.mul x y)) (Nat.add sa x) (Nat.add sb y) (by omega)
      dsimp only at hih ⊢
      rw [Fin.sum_univ_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
        show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl,
        show ∀ a b : Nat, Nat.mul a b = a * b from fun _ _ => rfl] at hih ⊢
      push_cast at hih ⊢
      linarith

/-- Symmetric diagonally dominant integer matrix is PSD on `{±1}^{56}`! -/
private lemma sdd_quad_nonneg (R : Fin 56 → Fin 56 → ℤ)
    (hdd : ∀ i : Fin 56, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i)
    (x : Fin 56 → ℤ) (hx : ∀ i : Fin 56, x i = 1 ∨ x i = -1) :
    0 ≤ ∑ i : Fin 56, ∑ j : Fin 56, R i j * x i * x j := by
  have hxsq : ∀ i : Fin 56, x i * x i = 1 := fun i => by
    rcases hx i with h | h <;> rw [h] <;> norm_num
  have habs : ∀ i j : Fin 56, -|R i j| ≤ R i j * x i * x j := fun i j => by
    rcases hx i with h1 | h1 <;> rcases hx j with h2 | h2
    · rw [h1, h2]; simp [neg_abs_le]
    · rw [h1, h2]; simp only [mul_one, mul_neg]; exact neg_le_neg (le_abs_self _)
    · rw [h1, h2]; simp only [mul_neg, mul_one]; exact neg_le_neg (le_abs_self _)
    · rw [h1, h2]; simp [neg_abs_le]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdiag : R i i * x i * x i = R i i := by rw [mul_assoc, hxsq i, mul_one]
  rw [hdiag]
  have hoff : -(∑ j ∈ Finset.univ.erase i, |R i j|) ≤
      ∑ j ∈ Finset.univ.erase i, R i j * x i * x j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => habs i j
  linarith [hdd i]

private lemma sound_checkAllRowsAux (B B2 : Nat) (hB2 : (B2 : ℤ) = (B : ℤ) * (B : ℤ))
    {Q : Fin 56 → Fin 56 → ℤ} (hQsym : ∀ i j, Q i j = Q j i)
    {K QOFF : Nat} {Arows Qlow : List (List Nat)}
    (hAlens : checkALens 0 Arows = true)
    (hQmatch : ∀ i j : Fin 56, j.val ≤ i.val →
      (((Qlow.getD i.val []).getD j.val 0 : Nat) : ℤ) = (K : ℤ) * (K : ℤ) * Q i j + (QOFF : ℤ))
    (hQlen : Qlow.length = 56)
    (hQrowlen : ∀ i : Fin 56, (Qlow.getD i.val []).length = i.val + 1)
    (hok : checkAllRowsAux B B2 QOFF Arows 0 Qlow Arows [] [] (List.replicate 56 0) = true)
    (x : Fin 56 → ℤ) (hx : ∀ i : Fin 56, x i = 1 ∨ x i = -1) :
    0 ≤ (K : ℤ) * (K : ℤ) * ∑ i : Fin 56, ∑ j : Fin 56, Q i j * x i * x j := by
  -- Extract lower-triangular `L : Fin 56 → Fin 56 → ℤ` from `Arows`: `L i k = A_{ik} - B` for `k ≤ i`, else `0`.
  have hAlen_spec : ∀ m rows, checkALens m rows = true →
      m + rows.length = 56 ∧ ∀ t, t < rows.length → (rows.getD t []).length = m + t + 1 := by
    intro m rows
    induction rows generalizing m with
    | nil =>
      intro h; unfold checkALens at h
      exact ⟨by simpa using h, fun t ht => by simp at ht⟩
    | cons r rs ih =>
      intro h
      by_cases hm56 : m = 56
      · subst hm56; simp [checkALens] at h
      · have hbm : Nat.beq m 56 = false := by
          cases h' : Nat.beq m 56
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h') hm56
        have hunf : checkALens m (r :: rs) = (Nat.beq r.length (m + 1) && checkALens (m + 1) rs) := by
          conv_lhs => unfold checkALens
          rw [hbm]; rfl
        rw [hunf, Bool.and_eq_true] at h
        have hrlen : r.length = m + 1 := by simpa using h.1
        obtain ⟨hsum, hrest⟩ := ih (m + 1) h.2
        refine ⟨by simp; omega, fun t ht => ?_⟩
        cases t with
        | zero => simpa using hrlen
        | succ t' =>
          simp only [List.length_cons] at ht
          have := hrest t' (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  obtain ⟨hA_len56, hA_rowlen⟩ := hAlen_spec 0 Arows hAlens
  simp only [zero_add] at hA_len56 hA_rowlen
  let L : Fin 56 → Fin 56 → ℤ := fun i k =>
    if k.val ≤ i.val then ((Arows.getD i.val []).getD k.val 0 : ℤ) - (B : ℤ) else 0
  let R : Fin 56 → Fin 56 → ℤ := fun i j =>
    (K : ℤ) * (K : ℤ) * Q i j - ∑ k : Fin 56, L i k * L j k
  -- Key helper: `L_i · L_j = ∑_{k ≤ min(i,j)} (A_{ik} - B)(A_{jk} - B)`!
  have hLL_lower : ∀ i j : Fin 56, j.val ≤ i.val →
      ∑ k : Fin 56, L i k * L j k =
        ∑ k : Fin (j.val + 1),
          (((Arows.getD i.val []).getD k.val 0 : ℤ) - (B : ℤ)) *
          (((Arows.getD j.val []).getD k.val 0 : ℤ) - (B : ℤ)) := by
    intro i j hji
    have h1 : ∑ k : Fin 56, L i k * L j k =
        ∑ k ∈ Finset.univ.filter (fun k : Fin 56 => k.val ≤ j.val), L i k * L j k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin 56 => k.val ≤ j.val)]
      have h0 : ∑ k ∈ Finset.univ.filter (fun k : Fin 56 => ¬k.val ≤ j.val), L i k * L j k = 0 :=
        Finset.sum_eq_zero fun k hk => by
          have hnot : ¬k.val ≤ j.val := (Finset.mem_filter.mp hk).2
          have hlj : L j k = 0 := by dsimp only [L]; rw [if_neg hnot]
          rw [hlj, mul_zero]
      rw [h0, add_zero]
    rw [h1]
    refine Finset.sum_bij (fun (k : Fin 56) (hk : k ∈ Finset.univ.filter fun k : Fin 56 => k.val ≤ j.val) =>
        (⟨k.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2⟩ : Fin (j.val + 1)))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
      (fun k _ => ⟨⟨k.val, by have := k.isLt; have := j.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_iff.mp k.isLt⟩, Fin.ext rfl⟩)
      (fun k hk => by
        have hkj : k.val ≤ j.val := (Finset.mem_filter.mp hk).2
        have hki : k.val ≤ i.val := le_trans hkj hji
        dsimp only [L]; rw [if_pos hki, if_pos hkj])
  -- Spec of `checkLowerRowAux`: relates `(diagI, offB, absList)` directly to `R i j` (`j ≤ i`)!
  have hrow_spec : ∀ (i : Fin 56) (j : Nat) (rowQ : List Nat) (rowsA : List (List Nat))
      (offB : Nat) (revAbs : List Nat) (diagI offOut : Nat) (absOut : List Nat),
      j ≤ i.val →
      rowQ = (Qlow.getD i.val []).drop j →
      rowsA = Arows.drop j →
      checkLowerRowAux B B2 QOFF (Arows.getD i.val []) i.val j rowQ rowsA offB revAbs = some (diagI, offOut, absOut) →
      (0 ≤ R i i ∧ (diagI : ℤ) = R i i) ∧
      (offOut : ℤ) = (offB : ℤ) + ∑ m : Fin (i.val - j), |R i ⟨j + m.val, by have := m.isLt; have := i.isLt; omega⟩| ∧
      absOut = revAbs.reverse ++ (List.range (i.val - j)).map (fun m =>
        (|R i ⟨(j + m) % 56, Nat.mod_lt _ (by omega)⟩|).toNat) := by
    intro i j rowQ
    induction rowQ generalizing j with
    | nil =>
      intro rowsA offB revAbs diagI offOut absOut _ _ _ h
      unfold checkLowerRowAux at h; simp at h
    | cons q qs ih =>
      intro rowsA offB revAbs diagI offOut absOut hji hrowQ hrowsA h
      have hQrow_i := hQrowlen i
      have hlen_drop : ((Qlow.getD i.val []).drop j).length = i.val + 1 - j := by
        rw [List.length_drop, hQrow_i]
      have hq_eq : q = (Qlow.getD i.val []).getD j 0 := by
        have := congr_arg (fun l => l.getD 0 0) hrowQ
        simpa [getD_drop] using this
      have hA_jlt : j < Arows.length := by have := i.isLt; omega
      have hrowsA_cons : rowsA = Arows.getD j [] :: Arows.drop (j + 1) := by
        rw [hrowsA, List.drop_eq_getElem_cons hA_jlt, getD_eq_getElem _ _ hA_jlt]
      -- Compute `dotAndSums` at `(i, j)`!
      let jF : Fin 56 := ⟨j, by have := i.isLt; omega⟩
      have hAj_len : (Arows.getD j []).length = j + 1 := hA_rowlen j hA_jlt
      have hAi_len : (Arows.getD i.val []).length = i.val + 1 := hA_rowlen i.val (by have := i.isLt; omega)
      have hdot := dotAndSums_spec B B2 hB2 (Arows.getD i.val []) (Arows.getD j []) 0 0 0 (by omega)
      dsimp only at hdot
      have hdot_eq :
          ((dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).1 : ℤ) -
            (B : ℤ) * (((dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.1 : ℤ) +
              ((dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.2 : ℤ)) +
            ((j + 1 : ℤ) * (B2 : ℤ)) = ∑ k : Fin 56, L i k * L jF k := by
        rw [hLL_lower i jF hji]
        have hcast : ((Arows.getD j []).length : ℤ) = (j + 1 : ℤ) := by exact_mod_cast hAj_len
        rw [← hcast]
        have hsum_eq : ∑ k : Fin (Arows.getD j []).length,
            (((Arows.getD i.val []).getD k.val 0 : ℤ) - (B : ℤ)) *
            (((Arows.getD j []).getD k.val 0 : ℤ) - (B : ℤ)) =
            ∑ k : Fin (j + 1),
            (((Arows.getD i.val []).getD k.val 0 : ℤ) - (B : ℤ)) *
            (((Arows.getD j []).getD k.val 0 : ℤ) - (B : ℤ)) := by
          refine Finset.sum_bij (fun k _ => ⟨k.val, by have := k.isLt; omega⟩) (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
            (fun k _ => ⟨⟨k.val, by have := k.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
            (fun _ _ => rfl)
        rw [← hsum_eq]
        simpa using hdot
      have hQij := hQmatch i jF hji
      have hdiff_R :
          let (d, sa, sb) := dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0
          let posT := Nat.add q (Nat.mul B (Nat.add sa sb))
          let negT := Nat.add QOFF (Nat.add d (Nat.mul (Nat.add j 1) B2))
          (posT : ℤ) - (negT : ℤ) = R i jF := by
        dsimp only [R]
        simp only [show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl,
          show ∀ a b : Nat, Nat.mul a b = a * b from fun _ _ => rfl]
        rw [hq_eq, ← hdot_eq]
        have hqZ : ((Qlow.getD i.val []).getD j 0 : ℤ) = (K : ℤ) * (K : ℤ) * Q i jF + (QOFF : ℤ) := hQij
        push_cast; linarith
      cases qs with
      | nil =>
        have hjeq : i.val = j := by
          have := congr_arg List.length hrowQ; rw [hlen_drop] at this; simp at this; omega
        rw [hrowsA_cons] at h
        unfold checkLowerRowAux at h
        have hbeq : Nat.beq i.val j = true := by rw [hjeq]; exact Nat.beq_refl j
        simp only [hbeq, ↓reduceIte] at h
        dsimp only at h hdiff_R
        by_cases hle : Nat.ble (Nat.add QOFF (Nat.add (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).1
            (Nat.mul (Nat.add j 1) B2)))
            (Nat.add q (Nat.mul B (Nat.add (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.1
              (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.2))) = true
        · rw [if_pos hle] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨hdiag, hoff, habs⟩
          have hpos_ge : (Nat.add QOFF (Nat.add (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).1
              (Nat.mul (Nat.add j 1) B2))) ≤
              (Nat.add q (Nat.mul B (Nat.add (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.1
                (dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0).2.2))) :=
            Nat.le_of_ble_eq_true hle
          have hijF : jF = i := Fin.ext hjeq.symm
          rw [hijF] at hdiff_R
          have hsubZ : (diagI : ℤ) = R i i := by
            rw [← hdiag]
            change ((_ - _ : Nat) : ℤ) = R i i
            rw [Int.ofNat_sub hpos_ge]; exact hdiff_R
          refine ⟨⟨by omega, hsubZ⟩, ?_, ?_⟩
          · have hzero : ∑ m : Fin (i.val - j), |R i ⟨j + m.val, by have := m.isLt; have := i.isLt; omega⟩| = 0 :=
              Finset.sum_eq_zero fun m _ => absurd m.isLt (by omega)
            rw [← hoff, hzero, add_zero]
          · rw [← habs, show i.val - j = 0 by omega]; simp
        · rw [if_neg hle] at h; cases h
      | cons q2 qs2 =>
        have hjlt : j < i.val := by
          have := congr_arg List.length hrowQ; rw [hlen_drop] at this; simp at this; omega
        rw [hrowsA_cons] at h
        unfold checkLowerRowAux at h
        dsimp only at h
        let res := dotAndSums (Arows.getD i.val []) (Arows.getD j []) 0 0 0
        let posT := Nat.add q (Nat.mul B (Nat.add res.2.1 res.2.2))
        let negT := Nat.add QOFF (Nat.add res.1 (Nat.mul (Nat.add j 1) B2))
        let absR := if Nat.ble negT posT then Nat.sub posT negT else Nat.sub negT posT
        have habsR_eq : (absR : ℤ) = |R i jF| := by
          dsimp only [absR]
          by_cases hle : negT ≤ posT
          · have hb : Nat.ble negT posT = true := by simpa using hle
            rw [hb]; simp only [↓reduceIte]
            change ((posT - negT : Nat) : ℤ) = |R i jF|
            rw [Int.ofNat_sub hle, hdiff_R, abs_of_nonneg (by linarith)]
          · have hlt' : posT ≤ negT := by omega
            have hb : Nat.ble negT posT = false := by
              cases hb' : Nat.ble negT posT
              · rfl
              · exact absurd (Nat.le_of_ble_eq_true hb') hle
            rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
            change ((negT - posT : Nat) : ℤ) = |R i jF|
            rw [Int.ofNat_sub hlt', show (negT : ℤ) - (posT : ℤ) = -R i jF by linarith,
                abs_of_neg (by linarith)]
        have hqs_drop : q2 :: qs2 = (Qlow.getD i.val []).drop (j + 1) := by
          have := congr_arg List.tail hrowQ
          simpa [List.tail_drop] using this
        have hih := ih (j + 1) (Arows.drop (j + 1)) (Nat.add offB absR) (absR :: revAbs)
          diagI offOut absOut (by omega) hqs_drop rfl h
        refine ⟨hih.1, ?_, ?_⟩
        · have hsub1 : i.val - j = (i.val - (j + 1)) + 1 := by omega
          rw [hih.2.1]
          have hsum_shift : ∑ m : Fin (i.val - j), |R i ⟨j + m.val, by have := m.isLt; have := i.isLt; omega⟩| =
              |R i jF| + ∑ m : Fin (i.val - (j + 1)), |R i ⟨j + 1 + m.val, by have := m.isLt; have := i.isLt; omega⟩| := by
            have heq_f : ∑ m : Fin (i.val - j), |R i ⟨j + m.val, by have := m.isLt; have := i.isLt; omega⟩| =
                ∑ m : Fin ((i.val - (j + 1)) + 1), |R i ⟨j + m.val, by have := m.isLt; have := i.isLt; omega⟩| :=
              Finset.sum_bij (fun m _ => ⟨m.val, by have := m.isLt; omega⟩) (fun _ _ => Finset.mem_univ _)
                (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
                (fun m _ => ⟨⟨m.val, by have := m.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
                (fun _ _ => rfl)
            rw [heq_f, Fin.sum_univ_succ]
            congr 1
            refine Finset.sum_congr rfl fun m _ => ?_
            exact congr_arg (fun t => |R i t|) (Fin.ext (by dsimp; omega))
          rw [hsum_shift, show Nat.add offB absR = offB + absR from rfl, Nat.cast_add]; linarith
        · rw [hih.2.2]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          congr 1
          have hsub1 : i.val - j = (i.val - (j + 1)) + 1 := by omega
          rw [hsub1, List.range_succ_eq_map, List.map_cons, List.map_map]
          congr 1
          · have : (|R i ⟨(j + 0) % 56, Nat.mod_lt _ (by omega)⟩|).toNat = absR := by
              have h0 : (⟨(j + 0) % 56, Nat.mod_lt _ (by omega)⟩ : Fin 56) = jF :=
                Fin.ext (by simp [jF, Nat.mod_eq_of_lt (show j < 56 by have := i.isLt; omega)])
              rw [h0, ← habsR_eq]; simp
            exact this.symm
          · refine List.map_congr_left fun m _ => ?_
            exact congr_arg (fun t => (|R i t|).toNat) (Fin.ext (by dsimp; exact congr_arg (· % 56) (by omega)))
  -- Spec of `addPrefix`: adds `absList[k]` into `offAbove[k]` for `k < absList.length`!
  have haddPrefix_getD : ∀ (xs ys : List Nat) (k : Nat),
      (addPrefix xs ys).getD k 0 = xs.getD k 0 + ys.getD k 0 := by
    intro xs
    induction xs with
    | nil => intro ys k; simp [addPrefix]
    | cons x xs ih =>
      intro ys k
      cases ys with
      | nil => simp [addPrefix]
      | cons y ys =>
        cases k with
        | zero => simp [addPrefix]
        | succ k' => simpa [addPrefix] using ih ys k'
  -- Spec of `cmpDiagOff`: `ob[k] + oa[k] ≤ d[k]` for all `k`!
  have hcmp_spec : ∀ (ds obs oas : List Nat), ds.length = obs.length → ds.length ≤ oas.length →
      cmpDiagOff ds obs oas = true →
      ∀ k, k < ds.length → obs.getD k 0 + oas.getD k 0 ≤ ds.getD k 0 := by
    intro ds
    induction ds with
    | nil => intro _ _ _ _ _ k hk; simp at hk
    | cons d ds ih =>
      intro obs oas hlen1 hlen2 h k hk
      cases obs with
      | nil => simp at hlen1
      | cons ob obs =>
        cases oas with
        | nil => simp at hlen2
        | cons oa oas =>
          unfold cmpDiagOff at h
          split_ifs at h with hle
          · cases k with
            | zero => simpa using hle
            | succ k' =>
              simp only [List.length_cons] at hlen1 hlen2 hk
              exact ih obs oas (by omega) (by omega) h k' (by omega)
  -- Induct through `checkAllRowsAux` from `i = 0` to `56`!
  have hall_spec : ∀ (rowsQ rowsA : List (List Nat)) (i : Nat)
      (revD revOB offA : List Nat),
      i + rowsQ.length = 56 →
      rowsQ = Qlow.drop i →
      rowsA = Arows.drop i →
      revD.length = i →
      revOB.length = i →
      offA.length = 56 →
      (∀ t : Fin 56, t.val < i → (revD.reverse.getD t.val 0 : ℤ) = R t t) →
      (∀ t : Fin 56, t.val < i → (revOB.reverse.getD t.val 0 : ℤ) =
        ∑ m : Fin t.val, |R t ⟨m.val, by have := m.isLt; have := t.isLt; omega⟩|) →
      (∀ t : Fin 56, (offA.getD t.val 0 : ℤ) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < i), |R r t|) →
      checkAllRowsAux B B2 QOFF Arows i rowsQ rowsA revD revOB offA = true →
      ∀ t : Fin 56, ∑ j ∈ Finset.univ.erase t, |R t j| ≤ R t t := by
    intro rowsQ
    induction rowsQ with
    | nil =>
      intro rowsA i revD revOB offA hlen hQ hA hDlen hOBlen hOAlen hD hOB hOA hok t
      have hi56 : i = 56 := by simp at hlen; omega
      have hrowsA_nil : rowsA = [] := by rw [hA, hi56, List.drop_eq_nil_iff]; omega
      rw [hrowsA_nil] at hok
      unfold checkAllRowsAux at hok
      simp only [hi56, Nat.beq_refl, Bool.true_and] at hok
      have hcmp := hcmp_spec revD.reverse revOB.reverse offA
        (by simp [hDlen, hOBlen]) (by simp [hDlen, hOAlen, hi56]) hok t.val (by simp [hDlen, hi56, t.isLt])
      have hDt := hD t (by have := t.isLt; omega)
      have hOBt := hOB t (by have := t.isLt; omega)
      have hOAt := hOA t
      have hsum_split : ∑ j ∈ Finset.univ.erase t, |R t j| =
          (∑ m : Fin t.val, |R t ⟨m.val, by have := m.isLt; have := t.isLt; omega⟩|) +
          (∑ r ∈ Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < 56), |R r t|) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase t) (fun j : Fin 56 => j.val < t.val)]
        congr 1
        · refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
            (fun m _ => ⟨⟨m.val, by have := m.isLt; have := t.isLt; omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
                ⟨Fin.ne_of_val_ne (Nat.ne_of_lt m.isLt), Finset.mem_univ _⟩, m.isLt⟩, Fin.ext rfl⟩)
            (fun _ _ => rfl)
        · have hflt : (Finset.univ.erase t).filter (fun j : Fin 56 => ¬j.val < t.val) =
              Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < 56) := by
            ext j; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
            constructor
            · rintro ⟨hne, hge⟩; exact ⟨by have := Fin.val_ne_of_ne hne; omega, j.isLt⟩
            · rintro ⟨hlt, _⟩; exact ⟨Fin.ne_of_val_ne (by omega), by omega⟩
          rw [hflt]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hRsym : R t r = R r t := by
            simp only [R, hQsym t r]; congr 1
            refine Finset.sum_congr rfl fun k _ => mul_comm _ _
          rw [hRsym]
      rw [hi56] at hOAt
      rw [hsum_split, ← hOBt, ← hOAt, ← hDt]
      exact_mod_cast hcmp
    | cons rq rqs ih =>
      intro rowsA i revD revOB offA hlen hQ hA hDlen hOBlen hOAlen hD hOB hOA hok
      have hilt : i < 56 := by simp at hlen; omega
      let iF : Fin 56 := ⟨i, hilt⟩
      have hA_cons : rowsA = Arows.getD i [] :: Arows.drop (i + 1) := by
        rw [hA, List.drop_eq_getElem_cons (by omega), getD_eq_getElem _ _ (by omega)]
      have hrq_eq : rq = Qlow.getD i [] := by
        have := congr_arg (fun l => l.getD 0 []) hQ
        simpa [getD_drop] using this
      have hrqs_drop : rqs = Qlow.drop (i + 1) := by
        have := congr_arg List.tail hQ
        simpa [List.tail_drop] using this
      rw [hA_cons] at hok
      unfold checkAllRowsAux at hok
      cases hstep : checkLowerRowAux B B2 QOFF (Arows.getD i []) i 0 rq Arows 0 [] with
      | none => rw [hstep] at hok; simp at hok
      | some res =>
        rcases res with ⟨diagI, offB, absList⟩
        rw [hstep] at hok; dsimp only at hok
        have hspec := hrow_spec iF 0 rq Arows 0 [] diagI offB absList (Nat.zero_le _)
          (by simpa using hrq_eq) (by simp) hstep
        have habs_len : absList.length = i := by rw [hspec.2.2]; simp [iF]
        have hadd_len : (addPrefix absList offA).length = 56 := by
          have hl : ∀ xs ys : List Nat, xs.length ≤ ys.length → (addPrefix xs ys).length = ys.length := by
            intro xs; induction xs with
            | nil => intro ys _; simp [addPrefix]
            | cons x xs ihx =>
              intro ys hle; cases ys with
              | nil => simp at hle
              | cons y ys => simp [addPrefix, ihx ys (by simpa using hle)]
          rw [hl absList offA (by omega), hOAlen]
        refine ih (Arows.drop (i + 1)) (i + 1) (diagI :: revD) (offB :: revOB) (addPrefix absList offA)
          (by simp at hlen; omega) hrqs_drop rfl (by simp [hDlen]) (by simp [hOBlen]) hadd_len ?_ ?_ ?_ hok
        · intro t ht
          simp only [List.reverse_cons]
          by_cases hti : t.val < i
          · rw [getD_append_left _ _ _ (by simp [hDlen, hti])]; exact hD t hti
          · have hteq : t = iF := Fin.ext (by dsimp [iF]; omega)
            rw [hteq, getD_append_right _ _ _ (by simp [hDlen, iF])]
            simp [hDlen, hspec.1.2, iF]
        · intro t ht
          simp only [List.reverse_cons]
          by_cases hti : t.val < i
          · rw [getD_append_left _ _ _ (by simp [hOBlen, hti])]; exact hOB t hti
          · have hteq : t = iF := Fin.ext (by dsimp [iF]; omega)
            rw [hteq, getD_append_right _ _ _ (by simp [hOBlen, iF])]
            simp only [hOBlen, iF, List.length_reverse, Nat.sub_self, List.getD_cons_zero]
            have h0 := hspec.2.1; simp only [Nat.cast_zero, zero_add] at h0
            rw [h0]
            refine Finset.sum_bij (fun m _ => ⟨m.val, by have := m.isLt; omega⟩) (fun _ _ => Finset.mem_univ _)
              (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
              (fun m _ => ⟨⟨m.val, by have := m.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
              (fun m _ => congr_arg (fun u => |R iF u|) (Fin.ext (by simp)))
        · intro t
          rw [haddPrefix_getD, Nat.cast_add, hOA t]
          by_cases hti : t.val < i
          · have habs_t : (absList.getD t.val 0 : ℤ) = |R iF t| := by
              rw [hspec.2.2]; simp only [List.reverse_nil, List.nil_append, Nat.sub_zero]
              have hlt_m : t.val < ((List.range i).map fun m =>
                  (|R iF ⟨(0 + m) % 56, Nat.mod_lt _ (by omega)⟩|).toNat).length := by
                simp [hti]
              rw [getD_eq_getElem _ _ hlt_m, List.getElem_map, List.getElem_range]
              have hteq : (⟨(0 + t.val) % 56, Nat.mod_lt _ (by omega)⟩ : Fin 56) = t :=
                Fin.ext (by simp [Nat.mod_eq_of_lt t.isLt])
              rw [hteq, Int.toNat_of_nonneg (abs_nonneg _)]
            rw [habs_t]
            have hflt : Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < i + 1) =
                insert iF (Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < i)) := by
              ext r; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
              constructor
              · intro ⟨h1, h2⟩
                by_cases hri : r.val = i
                · left; exact Fin.ext hri
                · right; exact ⟨h1, by omega⟩
              · rintro (rfl | ⟨h1, h2⟩)
                · exact ⟨hti, by simp [iF]⟩
                · exact ⟨h1, by omega⟩
            rw [hflt, Finset.sum_insert (by simp [iF])]
          · have habs_0 : absList.getD t.val 0 = 0 := by
              rw [getD_eq_default _ _ (by omega)]
            rw [habs_0, Nat.cast_zero, zero_add]
            refine Finset.sum_congr (Finset.ext fun r => ?_) fun _ _ => rfl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  have hdd := hall_spec Qlow Arows 0 [] [] (List.replicate 56 0) (by omega) rfl rfl rfl rfl
    (by simp) (fun _ h => by omega) (fun _ h => by omega)
    (fun t => by
      rw [getD_replicate _ _ _ _ t.isLt]
      have hemp : Finset.univ.filter (fun r : Fin 56 => t.val < r.val ∧ r.val < 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro r _; omega
      rw [hemp]; simp) hok
  have hR_nn := sdd_quad_nonneg R hdd x hx
  have hL_nn : 0 ≤ ∑ k : Fin 56, (∑ i : Fin 56, L i k * x i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdecomp : (K : ℤ) * (K : ℤ) * (∑ i : Fin 56, ∑ j : Fin 56, Q i j * x i * x j) =
      (∑ k : Fin 56, (∑ i : Fin 56, L i k * x i) ^ 2) +
      (∑ i : Fin 56, ∑ j : Fin 56, R i j * x i * x j) := by
    have hLexp : ∑ k : Fin 56, (∑ i : Fin 56, L i k * x i) ^ 2 =
        ∑ i : Fin 56, ∑ j : Fin 56, (∑ k : Fin 56, L i k * L j k) * x i * x j := by
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hLexp, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by simp only [R]; ring
  linarith

/-- Soundness of `checkAllRows`: if `Q` is symmetric on `Fin 56`, `Qlow` stores
    `K² * Q i j + QOFF` for `j ≤ i`, and `checkAllRows` returns `true`, then
    `0 ≤ K² * ∑ i, ∑ j, Q i j * x i * x j` for every `x ∈ {±1}^{56}`! -/
lemma sound_checkAllRows {Q : Fin 56 → Fin 56 → ℤ} (hQsym : ∀ i j, Q i j = Q j i)
    {K QOFF : Nat} {Arows Qlow : List (List Nat)}
    (hAlens : checkALens 0 Arows = true)
    (hQmatch : ∀ i j : Fin 56, j.val ≤ i.val →
      (((Qlow.getD i.val []).getD j.val 0 : Nat) : ℤ) = (K : ℤ) * (K : ℤ) * Q i j + (QOFF : ℤ))
    (hQlen : Qlow.length = 56)
    (hQrowlen : ∀ i : Fin 56, (Qlow.getD i.val []).length = i.val + 1)
    (hok : checkAllRows QOFF Arows 0 Qlow Arows [] [] (List.replicate 56 0) = true)
    (x : Fin 56 → ℤ) (hx : ∀ i : Fin 56, x i = 1 ∨ x i = -1) :
    0 ≤ (K : ℤ) * (K : ℤ) * ∑ i : Fin 56, ∑ j : Fin 56, Q i j * x i * x j :=
  sound_checkAllRowsAux BIAS BIAS2 (by decide) hQsym hAlens hQmatch hQlen hQrowlen hok x hx

/-! ### Section 3: Exact `A₆₃ ⊔ B₅₆` Decomposition & Master Soundness `sound_checkCert56` -/

/-- Exact sign function on `PauliIdx 3` induced by a 63-element list `s64`. -/
def listToSign3 (s64 : List ℤ) : PauliIdx 3 → ℤ :=
  fun p => getS64 s64 (enc3 p).val

lemma listToSign3_isSignAssign {s64 : List ℤ} (hlen : s64.length = 63)
    (hpm : (s64.all fun x => x == 1 || x == -1) = true) :
    IsSignAssign (listToSign3 s64) := by
  refine ⟨?_, fun p hp => ?_⟩
  · have h0 : (enc3 0).val = 0 := by
      have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      exact congr_arg Fin.val this
    simp [listToSign3, getS64, h0]
  · have hne : (enc3 p).val ≠ 0 := fun h => hp (by
      rw [← dec3_enc3 p, show enc3 p = 0 from Fin.ext h, dec3_zero])
    have hlt : (enc3 p).val - 1 < s64.length := by have := (enc3 p).isLt; omega
    simp only [listToSign3, getS64, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte,
      getD_eq_getElem _ _ hlt]
    rw [List.all_eq_true] at hpm
    have hmem := hpm s64[(enc3 p).val - 1] (List.getElem_mem hlt)
    simp only [Bool.or_eq_true, beq_iff_eq] at hmem
    exact hmem

/-- General `A ⊔ B` frustrated-pair split for any commuting-closed subset `S ⊆ Qminus c0_88`
    (`S_A = {p ∈ S | symp c0_88 p = 0}`, `S_B = {p ∈ S | symp c0_88 p = 1}`). -/
lemma frustPairs_AB_split {S : Finset (PauliIdx 4)}
    (hsub : S ⊆ Qminus c0_88)
    (hclosed : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → symp p q = 0 → p + q ∈ S)
    (s4 : PauliIdx 4 → ℤ) :
    let SA := S.filter fun p => symp c0_88 p = 0
    let SB := S.filter fun p => symp c0_88 p = 1
    let NBB := ((SB ×ˢ SB).filter fun pq =>
      pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
      gammaSgn pq.1 pq.2 * s4 pq.1 * s4 pq.2 * s4 (pq.1 + pq.2) = -1).card
    frustPairs S s4 = frustPairs SA s4 + 3 * NBB := by
  intro SA SB NBB
  let P := (S ×ˢ S).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s4 pq.1 * s4 pq.2 * s4 (pq.1 + pq.2) = -1
  let PAA := P.filter fun pq => symp c0_88 pq.1 = 0 ∧ symp c0_88 pq.2 = 0
  let PBB := P.filter fun pq => symp c0_88 pq.1 = 1 ∧ symp c0_88 pq.2 = 1
  let PBA := P.filter fun pq => symp c0_88 pq.1 = 1 ∧ symp c0_88 pq.2 = 0
  let PAB := P.filter fun pq => symp c0_88 pq.1 = 0 ∧ symp c0_88 pq.2 = 1
  have hP_card : frustPairs S s4 = P.card := rfl
  have hAA_card : PAA.card = frustPairs SA s4 :=
    congr_arg Finset.card (Finset.ext fun ⟨p, q⟩ => by
      simp only [PAA, P, SA, Finset.mem_filter, Finset.mem_product]; tauto)
  have hBB_card : PBB.card = NBB :=
    congr_arg Finset.card (Finset.ext fun ⟨p, q⟩ => by
      simp only [PBB, P, SB, Finset.mem_filter, Finset.mem_product]; tauto)
  have hBA_card : PBA.card = NBB := by
    rw [← hBB_card]
    refine Finset.card_bij (fun pq _ => (pq.1, pq.1 + pq.2)) ?_ ?_ ?_
    · rintro ⟨p, q⟩ hpq
      simp only [PBA, PBB, P, Finset.mem_filter, Finset.mem_product] at hpq ⊢
      rcases hpq with ⟨⟨⟨hpS, hqS⟩, hne, hsymp, hfr⟩, hsp, hsq⟩
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (hsub hqS)).1).1
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
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (hsub hbS)).1).1
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
  -- Partition `P = PAA ⊔ PBB ⊔ PBA ⊔ PAB`!
  have hP_union : P = (PAA ∪ PBB) ∪ (PBA ∪ PAB) := by
    ext ⟨p, q⟩
    simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases zmod2_cases (symp c0_88 p) with h1 | h1 <;>
      rcases zmod2_cases (symp c0_88 q) with h2 | h2
      · left; left; exact ⟨hp, h1, h2⟩
      · right; right; exact ⟨hp, h1, h2⟩
      · right; left; exact ⟨hp, h1, h2⟩
      · left; right; exact ⟨hp, h1, h2⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)) <;> exact h
  have hd1 : Disjoint PAA PBB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd2 : Disjoint PBA PAB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PBA, PAB, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd3 : Disjoint (PAA ∪ PBB) (PBA ∪ PAB) := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨_, h1a, h1b⟩ | ⟨_, h1a, h1b⟩ <;> rcases h2 with ⟨_, h2a, h2b⟩ | ⟨_, h2a, h2b⟩
    · rw [h1a] at h2a; exact absurd h2a (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1a] at h2a; exact absurd h2a (by decide)
  rw [hP_card, hP_union, Finset.card_union_of_disjoint hd3,
      Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      hAA_card, hBB_card, hBA_card, hAB_card]
  omega

private lemma list_range_filter_len (n : Nat) (P : Nat → Bool) :
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

private lemma foldl_sum_range (n : Nat) (f : Nat → Nat) :
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

/-- Exact count of ordered edges in `B₅₆` is `1512`. -/
private lemma card_edges56_total :
    ((Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij =>
      isEdge56b ij.1.val ij.2.val = true).card = 1512 := by
  have h1 : ((Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij =>
      isEdge56b ij.1.val ij.2.val = true).card = orderedEdgesTotal := by
    rw [orderedEdgesTotal, foldl_sum_range]
    have hp : ((Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij =>
        isEdge56b ij.1.val ij.2.val = true).card =
        ∑ ij : Fin 56 × Fin 56, if isEdge56b ij.1.val ij.2.val = true then 1 else 0 := by
      simp only [Finset.card_filter]
    rw [hp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [list_range_filter_len, Finset.card_filter]
  rw [h1, orderedEdgesTotal_eq]

/-- Exact count of ordered edges in slice `k` of `B₅₆` equals `EB_ord_table.getD k 0`. -/
private lemma card_edges56_slice (k : Fin 135) :
    ((Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij =>
      inSlice56b k.val ij.1.val ij.2.val = true).card = EB_ord_table.getD k.val 0 := by
  have htab : EB_ord_table.getD k.val 0 = orderedEdgesInSlice k.val := by
    have hlt : k.val < EB_ord_table.length := by simp [EB_ord_table, k.isLt]
    rw [getD_eq_getElem _ _ hlt]
    simp only [EB_ord_table, List.getElem_map, List.getElem_range]
  rw [htab, orderedEdgesInSlice, foldl_sum_range]
  have hp : ((Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij =>
      inSlice56b k.val ij.1.val ij.2.val = true).card =
      ∑ ij : Fin 56 × Fin 56, if inSlice56b k.val ij.1.val ij.2.val = true then 1 else 0 := by
    simp only [Finset.card_filter]
  rw [hp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [list_range_filter_len, Finset.card_filter]

private lemma wlines315_nodup : wlines315.Nodup := by
  unfold wlines315
  rw [List.nodup_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · split_ifs
    · exact List.nodup_nil
    · rw [List.nodup_flatMap]
      refine ⟨fun q _ => by dsimp only; split_ifs <;> simp, ?_⟩
      refine List.nodup_range.imp fun {q1 q2} hne x hx1 hx2 => ?_
      dsimp only at hx1 hx2
      split_ifs at hx1 hx2 <;> simp at hx1 hx2
      rw [hx1] at hx2
      exact hne (congr_arg (fun t => t.2.1) hx2)
  · refine List.nodup_range.imp fun {p1 p2} hne x hx1 hx2 => ?_
    dsimp only at hx1 hx2
    by_cases hp1 : (p1 == 0) = true
    · simp [hp1] at hx1
    by_cases hp2 : (p2 == 0) = true
    · simp [hp2] at hx2
    simp only [hp1, hp2, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range] at hx1 hx2
    rcases hx1 with ⟨q1, _, hx1⟩
    rcases hx2 with ⟨q2, _, hx2⟩
    split_ifs at hx1 hx2 <;> simp at hx1 hx2
    rw [hx1] at hx2
    exact hne (congr_arg Prod.fst hx2)

private lemma mem_wlines315_iff (x : Nat × Nat × Nat × ℤ) :
    x ∈ wlines315 ↔
      x.1 < 64 ∧ x.2.1 < 64 ∧ x.1 ≠ 0 ∧ x.1 < x.2.1 ∧ x.2.1 < (x.1 ^^^ x.2.1) ∧
      symp3 x.1 x.2.1 = 0 ∧ x.2.2.1 = (x.1 ^^^ x.2.1) ∧ x.2.2.2 = gamma3_sgn x.1 x.2.1 := by
  rcases x with ⟨a, b, c, g⟩
  simp only [wlines315, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨p, hp, hmem⟩
    split_ifs at hmem with hp0
    · simp at hmem
    · simp only [List.mem_flatMap, List.mem_range] at hmem
      rcases hmem with ⟨q, hq, hmem2⟩
      split_ifs at hmem2 with hqcond hrcond
      · simp at hmem2
      · simp at hmem2
      · simp only [List.mem_singleton, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl, rfl, rfl⟩
        have hp_ne : a ≠ 0 := by simpa using hp0
        have hq_ok : ¬(b ≤ a) ∧ symp3 a b = 0 := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_not] at hqcond
          exact hqcond
        have hr_ok : b < a ^^^ b := by omega
        exact ⟨hp, hq, hp_ne, by omega, hr_ok, hq_ok.2, rfl, rfl⟩
  · rintro ⟨ha, hb, ha0, hab, hbc, hsymp, rfl, rfl⟩
    refine ⟨a, ha, ?_⟩
    have h1 : (a == 0) = false := beq_false_of_ne ha0
    simp only [h1, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range]
    refine ⟨b, hb, ?_⟩
    have h2 : (decide (b ≤ a) || (symp3 a b != 0)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq]
      exact ⟨by omega, hsymp⟩
    have h3 : ¬(a ^^^ b ≤ b) := by omega
    simp only [h2, Bool.false_eq_true, ↓reduceIte, h3, List.mem_singleton]

private lemma foldl_count_eq_filter_len {α : Type*} (L : List α) (P : α → Bool) (acc : Nat) :
    L.foldl (fun a x => if P x then a + 1 else a) acc = acc + (L.filter P).length := by
  induction L generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.filter_cons]
    cases h : P x <;> simp [ih] <;> omega

private lemma Apauli_inj {a b : PauliIdx 3} (h : Apauli a = Apauli b) : a = b := by
  have ha := ApauliFin_props (enc3 a)
  have hb := ApauliFin_props (enc3 b)
  have h1 : proj43Fin (enc4 (Apauli a)) = proj43Fin (enc4 (Apauli b)) := by rw [h]
  simp only [Apauli, enc4_dec4] at h1
  rw [ha.2.2.2.1, hb.2.2.2.1] at h1
  exact equiv3.injective h1

/-- Universal 6-to-1 bijection between `wlines315` and ordered commuting pairs in `nzPts 3`. -/
lemma wlines315_six_to_one (P : Nat × Nat × Nat × ℤ → Bool) (Q : PauliIdx 3 → PauliIdx 3 → Prop)
    (hQ_symm : ∀ p q, symp p q = 0 → Q p q → Q q p)
    (hQ_add : ∀ p q, symp p q = 0 → Q p q → Q p (p + q))
    (hPQ : ∀ a b : Fin 64, a.val ≠ 0 → a.val < b.val → b.val < (a.val ^^^ b.val) →
      symp3 a.val b.val = 0 →
      (P (a.val, b.val, a.val ^^^ b.val, gamma3_sgn a.val b.val) = true ↔ Q (dec3 a) (dec3 b))) :
    ((nzPts 3 ×ˢ nzPts 3).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧ Q pq.1 pq.2).card =
      6 * (wlines315.filter P).length := by
  let T := (wlines315.filter P).toFinset
  have hT_card : T.card = (wlines315.filter P).length :=
    List.toFinset_card_of_nodup (wlines315_nodup.filter P)
  let mkP : Nat → PauliIdx 3 := fun n => dec3 ⟨n % 64, Nat.mod_lt _ (by omega)⟩
  let orb : Nat × Nat × Nat × ℤ → Finset (PauliIdx 3 × PauliIdx 3) := fun t =>
    let pa := mkP t.1; let pb := mkP t.2.1; let pc := mkP t.2.2.1
    {(pa, pb), (pb, pa), (pa, pc), (pc, pa), (pb, pc), (pc, pb)}
  have hmkP_enc : ∀ n, n < 64 → (enc3 (mkP n)).val = n := fun n hn => by
    simp only [mkP, enc3_dec3, Nat.mod_eq_of_lt hn]
  have hmkP_ne : ∀ n m, n < 64 → m < 64 → n ≠ m → mkP n ≠ mkP m := fun n m hn hm hne h =>
    hne (by have := congr_arg (fun x => (enc3 x).val) h; rwa [hmkP_enc n hn, hmkP_enc m hm] at this)
  have hmkP_add : ∀ a b, a < 64 → b < 64 → mkP (a ^^^ b) = mkP a + mkP b := fun a b ha hb => by
    have hab : a ^^^ b < 64 := Nat.xor_lt_two_pow (n := 6) ha hb
    have h1 := dec3_xor ⟨a, ha⟩ ⟨b, hb⟩
    simp only [mkP, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]
    exact h1
  have hT_props : ∀ t ∈ T, t.1 < 64 ∧ t.2.1 < 64 ∧ t.2.2.1 < 64 ∧
      t.1 ≠ 0 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧
      t.2.2.1 = (t.1 ^^^ t.2.1) ∧ symp3 t.1 t.2.1 = 0 ∧
      t.2.2.2 = gamma3_sgn t.1 t.2.1 ∧ P t = true := by
    intro t ht
    simp only [T, List.mem_toFinset, List.mem_filter] at ht
    rcases (mem_wlines315_iff t).mp ht.1 with ⟨ha, hb, ha0, hab, hbc, hsymp, hc, hg⟩
    have hclt : t.2.2.1 < 64 := by rw [hc]; exact Nat.xor_lt_two_pow (n := 6) ha hb
    exact ⟨ha, hb, hclt, ha0, hab, by omega, hc, hsymp, hg, ht.2⟩
  have horb_card : ∀ t ∈ T, (orb t).card = 6 := by
    intro t ht
    obtain ⟨ha, hb, hc, _, hab, hbc, _, _, _, _⟩ := hT_props t ht
    have h1 := hmkP_ne t.1 t.2.1 ha hb (by omega)
    have h2 := hmkP_ne t.1 t.2.2.1 ha hc (by omega)
    have h3 := hmkP_ne t.2.1 t.2.2.1 hb hc (by omega)
    simp only [orb]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [h1, h2, h3, h1.symm, h2.symm, h3.symm]
  have horb_recover : ∀ t ∈ T, ∀ pq ∈ orb t,
      let x := (enc3 pq.1).val; let y := (enc3 pq.2).val; let z := (enc3 (pq.1 + pq.2)).val
      t.1 = min x (min y z) ∧ t.2.2.1 = max x (max y z) ∧
      t.2.1 = t.1 ^^^ t.2.2.1 ∧ t.2.2.2 = gamma3_sgn t.1 t.2.1 := by
    intro t ht pq hpq
    obtain ⟨ha, hb, hc, _, hab, hbc, hcxor, _, hg, _⟩ := hT_props t ht
    have hpa : (enc3 (mkP t.1)).val = t.1 := hmkP_enc t.1 ha
    have hpb : (enc3 (mkP t.2.1)).val = t.2.1 := hmkP_enc t.2.1 hb
    have hpc : (enc3 (mkP t.2.2.1)).val = t.2.2.1 := hmkP_enc t.2.2.1 hc
    have hadd_ab : mkP t.1 + mkP t.2.1 = mkP t.2.2.1 := by rw [hcxor, hmkP_add _ _ ha hb]
    have hadd_ac : mkP t.1 + mkP t.2.2.1 = mkP t.2.1 := by
      rw [← hadd_ab, pauliIdx_add_cancel_left]
    have hadd_bc : mkP t.2.1 + mkP t.2.2.1 = mkP t.1 := by
      rw [← hadd_ab, add_comm (mkP t.1), pauliIdx_add_cancel_left]
    have hbxor : t.2.1 = t.1 ^^^ t.2.2.1 := by
      rw [hcxor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hpq
    rcases hpq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [hpa, hpb, hadd_ab, hpc]; refine ⟨by omega, by omega, hbxor, hg⟩
    · simp only [hpa, hpb, add_comm (mkP t.2.1), hadd_ab, hpc]; refine ⟨by omega, by omega, hbxor, hg⟩
    · simp only [hpa, hpc, hadd_ac, hpb]; refine ⟨by omega, by omega, hbxor, hg⟩
    · simp only [hpa, hpc, add_comm (mkP t.2.2.1), hadd_ac, hpb]; refine ⟨by omega, by omega, hbxor, hg⟩
    · simp only [hpb, hpc, hadd_bc, hpa]; refine ⟨by omega, by omega, hbxor, hg⟩
    · simp only [hpb, hpc, add_comm (mkP t.2.2.1), hadd_bc, hpa]; refine ⟨by omega, by omega, hbxor, hg⟩
  have hdisj : (T : Set (Nat × Nat × Nat × ℤ)).PairwiseDisjoint orb := by
    intro t1 ht1 t2 ht2 hne
    change Disjoint (orb t1) (orb t2)
    rw [Finset.disjoint_left]
    intro pq hp1 hp2
    have hr1 := horb_recover t1 ht1 pq hp1
    have hr2 := horb_recover t2 ht2 pq hp2
    apply hne
    rcases t1 with ⟨a1, b1, c1, g1⟩
    rcases t2 with ⟨a2, b2, c2, g2⟩
    dsimp only at hr1 hr2
    have ha_eq : a1 = a2 := hr1.1.trans hr2.1.symm
    have hc_eq : c1 = c2 := hr1.2.1.trans hr2.2.1.symm
    have hb_eq : b1 = b2 := by rw [hr1.2.2.1, hr2.2.2.1, ha_eq, hc_eq]
    have hg_eq : g1 = g2 := by rw [hr1.2.2.2, hr2.2.2.2, ha_eq, hb_eq]
    rw [ha_eq, hb_eq, hc_eq, hg_eq]
  have hunion : T.biUnion orb =
      (nzPts 3 ×ˢ nzPts 3).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧ Q pq.1 pq.2 := by
    ext ⟨p, q⟩
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, nzPts,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨t, ht, hpq⟩
      obtain ⟨ha, hb, hc, ha0, hab, hbc, hcxor, hsymp, hg, hPt⟩ := hT_props t ht
      let fa : Fin 64 := ⟨t.1, ha⟩
      let fb : Fin 64 := ⟨t.2.1, hb⟩
      have hpa_eq : mkP t.1 = dec3 fa := by simp [mkP, fa, Nat.mod_eq_of_lt ha]
      have hpb_eq : mkP t.2.1 = dec3 fb := by simp [mkP, fb, Nat.mod_eq_of_lt hb]
      have hpc_eq : mkP t.2.2.1 = dec3 fa + dec3 fb := by
        rw [hcxor, hmkP_add _ _ ha hb, hpa_eq, hpb_eq]
      have hsymp_ab : symp (dec3 fa) (dec3 fb) = 0 := by rw [symp_dec3, hsymp]; rfl
      have hQab : Q (dec3 fa) (dec3 fb) := by
        have hteq : t = (fa.val, fb.val, fa.val ^^^ fb.val, gamma3_sgn fa.val fb.val) := by
          rcases t with ⟨a, b, c, g⟩; dsimp only at hcxor hg ⊢; rw [hcxor, hg]
        rw [hteq] at hPt
        exact (hPQ fa fb ha0 hab (by rw [← hcxor]; exact hbc) hsymp).mp hPt
      have hQba : Q (dec3 fb) (dec3 fa) := hQ_symm _ _ hsymp_ab hQab
      have hQac : Q (dec3 fa) (dec3 fa + dec3 fb) := hQ_add _ _ hsymp_ab hQab
      have hQca : Q (dec3 fa + dec3 fb) (dec3 fa) :=
        hQ_symm _ _ (by rw [symp_add_right, symp_self, hsymp_ab, add_zero]) hQac
      have hQbc : Q (dec3 fb) (dec3 fa + dec3 fb) := by
        rw [add_comm (dec3 fa) (dec3 fb)]
        exact hQ_add _ _ (by rwa [symp_comm]) hQba
      have hQcb : Q (dec3 fa + dec3 fb) (dec3 fb) :=
        hQ_symm _ _ (by rw [symp_add_right, symp_comm, hsymp_ab, symp_self, add_zero]) hQbc
      have ha_nz : dec3 fa ≠ 0 := by
        rw [← hpa_eq]; exact fun h => ha0 (by
          have := congr_arg (fun x => (enc3 x).val) h
          rw [hmkP_enc t.1 ha] at this
          have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
          rw [h0] at this; exact this)
      have hb_nz : dec3 fb ≠ 0 := by
        rw [← hpb_eq]; exact fun h => (show t.2.1 ≠ 0 by omega) (by
          have := congr_arg (fun x => (enc3 x).val) h
          rw [hmkP_enc t.2.1 hb] at this
          have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
          rw [h0] at this; exact this)
      have hc_nz : dec3 fa + dec3 fb ≠ 0 := by
        rw [← hpc_eq]; exact fun h => (show t.2.2.1 ≠ 0 by omega) (by
          have := congr_arg (fun x => (enc3 x).val) h
          rw [hmkP_enc t.2.2.1 hc] at this
          have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
          rw [h0] at this; exact this)
      have h1 := hmkP_ne t.1 t.2.1 ha hb (by omega)
      have h2 := hmkP_ne t.1 t.2.2.1 ha hc (by omega)
      have h3 := hmkP_ne t.2.1 t.2.2.1 hb hc (by omega)
      rw [hpa_eq, hpb_eq] at h1; rw [hpa_eq, hpc_eq] at h2; rw [hpb_eq, hpc_eq] at h3
      simp only [orb, hpa_eq, hpb_eq, hpc_eq, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hpq
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨ha_nz, hb_nz⟩, h1, hsymp_ab, hQab⟩
      · exact ⟨⟨hb_nz, ha_nz⟩, h1.symm, by rwa [symp_comm], hQba⟩
      · exact ⟨⟨ha_nz, hc_nz⟩, h2, by rw [symp_add_right, symp_self, hsymp_ab, add_zero], hQac⟩
      · exact ⟨⟨hc_nz, ha_nz⟩, h2.symm, by rw [symp_add_left, symp_self, symp_comm, hsymp_ab, add_zero], hQca⟩
      · exact ⟨⟨hb_nz, hc_nz⟩, h3, by rw [symp_add_right, symp_comm, hsymp_ab, symp_self, add_zero], hQbc⟩
      · exact ⟨⟨hc_nz, hb_nz⟩, h3.symm, by rw [symp_add_left, hsymp_ab, symp_self, add_zero], hQcb⟩
    · rintro ⟨⟨hp0, hq0⟩, hne, hsymp, hQpq⟩
      let r := p + q
      have hr0 : r ≠ 0 := fun h => hne (by
        have := congr_arg (p + ·) h; simpa [r, pauliIdx_add_cancel_left] using this.symm)
      have hpr : p ≠ r := fun h => hq0 (by
        have := congr_arg (p + ·) h; simpa [r, pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
      have hqr : q ≠ r := fun h => hp0 (by
        have := congr_arg (· + q) h; simpa [r, pauliIdx_add_self, pauliIdx_add_cancel_right] using this.symm)
      have h0e : (enc3 0).val = 0 := by
        have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        exact congr_arg Fin.val this
      let x := (enc3 p).val; let y := (enc3 q).val; let z := (enc3 r).val
      have hx_lt := (enc3 p).isLt; have hy_lt := (enc3 q).isLt; have hz_lt := (enc3 r).isLt
      have hx0 : x ≠ 0 := fun h => hp0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
      have hy0 : y ≠ 0 := fun h => hq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
      have hz0 : z ≠ 0 := fun h => hr0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))
      have hxy : x ≠ y := fun h => hne (equiv3.injective (Fin.ext h))
      have hxz : x ≠ z := fun h => hpr (equiv3.injective (Fin.ext h))
      have hyz : y ≠ z := fun h => hqr (equiv3.injective (Fin.ext h))
      have hzxor : z = x ^^^ y := by
        have h1 : r = dec3 ⟨x ^^^ y, Nat.xor_lt_two_pow (n := 6) hx_lt hy_lt⟩ := by
          rw [dec3_xor, dec3_enc3, dec3_enc3]
        have := congr_arg (fun w => (enc3 w).val) h1
        simpa [z, enc3_dec3] using this
      have hyxor : y = x ^^^ z := by rw [hzxor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hxxor : x = y ^^^ z := by rw [hzxor, Nat.xor_comm x y, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hmk_p : mkP x = p := by simp [mkP, x, Nat.mod_eq_of_lt hx_lt, dec3_enc3]
      have hmk_q : mkP y = q := by simp [mkP, y, Nat.mod_eq_of_lt hy_lt, dec3_enc3]
      have hmk_r : mkP z = r := by simp [mkP, z, Nat.mod_eq_of_lt hz_lt, dec3_enc3]
      have hsymp_pr : symp p r = 0 := by rw [show r = p + q from rfl, symp_add_right, symp_self, hsymp, add_zero]
      have hsymp_qr : symp q r = 0 := by rw [show r = p + q from rfl, symp_add_right, symp_comm, hsymp, symp_self, add_zero]
      have hQqp : Q q p := hQ_symm p q hsymp hQpq
      have hQpr : Q p r := hQ_add p q hsymp hQpq
      have hQrp : Q r p := hQ_symm p r hsymp_pr hQpr
      have hQqr : Q q r := by rw [show r = q + p from add_comm p q]; exact hQ_add q p (by rwa [symp_comm]) hQqp
      have hQrq : Q r q := hQ_symm q r hsymp_qr hQqr
      have toSymp3 : ∀ (u v : PauliIdx 3), symp u v = 0 → symp3 (enc3 u).val (enc3 v).val = 0 := fun u v hs => by
        rw [← dec3_enc3 u, ← dec3_enc3 v, symp_dec3] at hs
        have hlt := symp3_lt2 (enc3 u).val (enc3 v).val
        generalize symp3 (enc3 u).val (enc3 v).val = k at hlt hs ⊢
        interval_cases k
        · rfl
        · exact absurd hs (by decide)
      have hmake : ∀ (u v w : PauliIdx 3),
          (enc3 u).val ≠ 0 → (enc3 u).val < (enc3 v).val → (enc3 v).val < (enc3 w).val →
          (enc3 w).val = (enc3 u).val ^^^ (enc3 v).val →
          symp u v = 0 → Q u v →
          ((p, q) ∈ orb ((enc3 u).val, (enc3 v).val, (enc3 w).val, gamma3_sgn (enc3 u).val (enc3 v).val)) →
          ∃ t ∈ T, (p, q) ∈ orb t := by
        intro u v w hu0 huv hvw hwx hsuv hQuv hmem
        let t := ((enc3 u).val, (enc3 v).val, (enc3 w).val, gamma3_sgn (enc3 u).val (enc3 v).val)
        refine ⟨t, ?_, hmem⟩
        have hs3 := toSymp3 u v hsuv
        have hPt : P t = true := by
          have h1 := (hPQ (enc3 u) (enc3 v) hu0 huv (by omega) hs3).mpr (by rwa [dec3_enc3, dec3_enc3])
          simpa [t, hwx] using h1
        rw [show t ∈ T ↔ t ∈ wlines315 ∧ P t = true by simp [T]]
        exact ⟨(mem_wlines315_iff t).mpr ⟨(enc3 u).isLt, (enc3 v).isLt, hu0, huv, by dsimp [t]; omega, hs3, hwx, rfl⟩, hPt⟩
      -- 6 strict orderings of distinct `x, y, z`:
      have hmk_p' : mkP (enc3 p).val = p := hmk_p
      have hmk_q' : mkP (enc3 q).val = q := hmk_q
      have hmk_r' : mkP (enc3 r).val = r := hmk_r
      by_cases h1 : x < y
      · by_cases h2 : y < z
        · exact hmake p q r hx0 h1 h2 hzxor hsymp hQpq (by simp [orb, hmk_p', hmk_q', hmk_r'])
        · by_cases h3 : x < z
          · exact hmake p r q hx0 h3 (by omega) hyxor hsymp_pr hQpr (by simp [orb, hmk_p', hmk_q', hmk_r'])
          · exact hmake r p q hz0 (by omega) h1 (by rw [Nat.xor_comm]; exact hyxor) (by rwa [symp_comm]) hQrp
              (by simp [orb, hmk_p', hmk_q', hmk_r'])
      · by_cases h2 : x < z
        · exact hmake q p r hy0 (by omega) h2 (by rw [Nat.xor_comm]; exact hzxor) (by rwa [symp_comm]) hQqp
            (by simp [orb, hmk_p', hmk_q', hmk_r'])
        · by_cases h3 : y < z
          · exact hmake q r p hy0 h3 (by omega) hxxor hsymp_qr hQqr (by simp [orb, hmk_p', hmk_q', hmk_r'])
          · exact hmake r q p hz0 (by omega) (by omega) (by rw [Nat.xor_comm]; exact hxxor)
              (by rwa [symp_comm]) hQrq (by simp [orb, hmk_p', hmk_q', hmk_r'])
  rw [← hunion, Finset.card_biUnion hdisj, Finset.sum_congr rfl horb_card,
      Finset.sum_const, smul_eq_mul, mul_comm, hT_card]

lemma countFrustWlines_eq_frustPairs (s64 : List ℤ) :
    frustPairs (nzPts 3) (listToSign3 s64) = 6 * countFrustWlines s64 := by
  let P : Nat × Nat × Nat × ℤ → Bool := fun (a, b, c, g) =>
    g * getS64 s64 a * getS64 s64 b * getS64 s64 c == -1
  let s3 := listToSign3 s64
  let Q : PauliIdx 3 → PauliIdx 3 → Prop := fun p q =>
    gammaSgn p q * s3 p * s3 q * s3 (p + q) = -1
  have hcount : countFrustWlines s64 = (wlines315.filter P).length := by
    simpa [countFrustWlines, P] using foldl_count_eq_filter_len wlines315 P 0
  have h6 := wlines315_six_to_one P Q
    (fun p q hsp h => by dsimp only [Q] at h ⊢; rw [gammaSgn_comm (by rwa [symp_comm]), add_comm q p]; linarith)
    (fun p q hsp h => by dsimp only [Q] at h ⊢; rw [gammaSgn_add_right hsp, pauliIdx_add_cancel_left]; linarith)
    (fun a b _ _ _ _ => by
      have hadd : dec3 a + dec3 b = dec3 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ :=
        (dec3_xor a b).symm
      simp only [P, Q, s3, listToSign3, beq_iff_eq, hadd, enc3_dec3, gammaSgn_dec3])
  rw [hcount, ← h6]
  unfold frustPairs
  exact congr_arg Finset.card (by ext pq; simp only [Finset.mem_filter, Q, s3])

lemma countFrustWlinesSlice_eq_frustPairs (k : Fin 135) (s64 : List ℤ)
    {s4 : PauliIdx 4 → ℤ} (hres : restrictA s4 = listToSign3 s64) :
    frustPairs ((slicePts c0_88 (dec4 (otherPoutFin k))).filter fun p => symp c0_88 p = 0) s4 =
      6 * countFrustWlinesSlice k.val s64 := by
  let po := dec4 (otherPoutFin k)
  let P : Nat × Nat × Nat × ℤ → Bool := fun (a, b, c, g) =>
    symp4 (otherPout_val k.val) (ApauliNat a) == 0 &&
    symp4 (otherPout_val k.val) (ApauliNat b) == 0 &&
    (g * getS64 s64 a * getS64 s64 b * getS64 s64 c == -1)
  let s3 := listToSign3 s64
  let Q : PauliIdx 3 → PauliIdx 3 → Prop := fun p q =>
    symp po (Apauli p) = 0 ∧ symp po (Apauli q) = 0 ∧
    gammaSgn p q * s3 p * s3 q * s3 (p + q) = -1
  have hcount : countFrustWlinesSlice k.val s64 = (wlines315.filter P).length := by
    simpa [countFrustWlinesSlice, P] using foldl_count_eq_filter_len wlines315 P 0
  have h6 : ((nzPts 3 ×ˢ nzPts 3).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧ Q pq.1 pq.2).card =
      6 * countFrustWlinesSlice k.val s64 := by
    have h6' := wlines315_six_to_one P Q
      (fun p q hsp ⟨h1, h2, h3⟩ =>
        ⟨h2, h1, by rw [gammaSgn_comm (by rwa [symp_comm]), add_comm q p]; linarith⟩)
      (fun p q hsp ⟨h1, h2, h3⟩ => by
        refine ⟨h1, ?_, by rw [gammaSgn_add_right hsp, pauliIdx_add_cancel_left]; linarith⟩
        rw [Apauli_add_of_comm hsp, symp_add_right, h1, h2, add_zero])
      (fun a b _ _ _ _ => by
        have hadd : dec3 a + dec3 b = dec3 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ :=
          (dec3_xor a b).symm
        have hs_a : (symp4 (otherPout_val k.val) (ApauliNat a.val) == 0) = true ↔ symp po (Apauli (dec3 a)) = 0 := by
          simp only [beq_iff_eq, po, Apauli, enc3_dec3, symp_dec4, otherPoutFin, ApauliFin]
          have hlt := symp4_lt2 (otherPout_val k.val) (ApauliNat a.val)
          generalize symp4 (otherPout_val k.val) (ApauliNat a.val) = m at hlt ⊢
          interval_cases m <;> decide
        have hs_b : (symp4 (otherPout_val k.val) (ApauliNat b.val) == 0) = true ↔ symp po (Apauli (dec3 b)) = 0 := by
          simp only [beq_iff_eq, po, Apauli, enc3_dec3, symp_dec4, otherPoutFin, ApauliFin]
          have hlt := symp4_lt2 (otherPout_val k.val) (ApauliNat b.val)
          generalize symp4 (otherPout_val k.val) (ApauliNat b.val) = m at hlt ⊢
          interval_cases m <;> decide
        simp only [P, Q, s3, listToSign3, Bool.and_eq_true, hs_a, hs_b, beq_iff_eq,
          hadd, enc3_dec3, gammaSgn_dec3, and_assoc])
    rw [hcount, ← h6']
    exact congr_arg Finset.card (by ext pq; simp only [Finset.mem_filter])
  rw [← h6]; unfold frustPairs
  symm
  refine Finset.card_bij (fun pq _ => (Apauli pq.1, Apauli pq.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase, Finset.mem_univ,
      and_true, Q] at hab
    rcases hab with ⟨⟨ha0, hb0⟩, hne, hsymp, hspa, hspb, hfr⟩
    have hpA := ApauliFin_props (enc3 a)
    have hqA := ApauliFin_props (enc3 b)
    have hAp0 : Apauli a ≠ 0 := by
      intro h; apply ha0
      have h0 : Apauli 0 = 0 := by
        simp only [Apauli]; rw [show enc3 0 = 0 by rw [← dec3_zero, enc3_dec3]]; exact dec4_zero
      exact Apauli_inj (h.trans h0.symm)
    have hAq0 : Apauli b ≠ 0 := by
      intro h; apply hb0
      have h0 : Apauli 0 = 0 := by
        simp only [Apauli]; rw [show enc3 0 = 0 by rw [← dec3_zero, enc3_dec3]]; exact dec4_zero
      exact Apauli_inj (h.trans h0.symm)
    have hqa : quadForm c0_88 (Apauli a) = 0 := by simp only [c0_88, Apauli, quadForm_dec4, hpA.2.1]; rfl
    have hqb : quadForm c0_88 (Apauli b) = 0 := by simp only [c0_88, Apauli, quadForm_dec4, hqA.2.1]; rfl
    have hsa : symp c0_88 (Apauli a) = 0 := by simp only [c0_88, Apauli, symp_dec4, hpA.2.2.1]; rfl
    have hsb : symp c0_88 (Apauli b) = 0 := by simp only [c0_88, Apauli, symp_dec4, hqA.2.2.1]; rfl
    have hab0 : a + b ≠ 0 := fun h => hne (by
      have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hs4a : s4 (Apauli a) = s3 a := by
      have := congr_fun hres a; simpa [restrictA, ha0, s3] using this
    have hs4b : s4 (Apauli b) = s3 b := by
      have := congr_fun hres b; simpa [restrictA, hb0, s3] using this
    have hs4ab : s4 (Apauli a + Apauli b) = s3 (a + b) := by
      rw [← Apauli_add_of_comm hsymp]
      have := congr_fun hres (a + b); simpa [restrictA, hab0, s3] using this
    simp only [Finset.mem_filter, Finset.mem_product, slicePts, Qminus, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true]
    refine ⟨⟨⟨⟨⟨hAp0, hqa⟩, hspa⟩, hsa⟩, ⟨⟨⟨hAq0, hqb⟩, hspb⟩, hsb⟩⟩,
      fun h => hne (Apauli_inj h), by rw [Apauli_symp, hsymp], ?_⟩
    rw [Apauli_gammaSgn hsymp, hs4a, hs4b, hs4ab]; exact hfr
  · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Apauli_inj h.1) (Apauli_inj h.2)
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, slicePts, Qminus, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true] at hpq
    rcases hpq with ⟨⟨⟨⟨⟨hp0, hqp⟩, hppo⟩, hsp⟩, ⟨⟨⟨hq0, hqq⟩, hqpo⟩, hsq⟩⟩, hne, hsymp, hfr⟩
    let a := dec3 (proj43Fin (enc4 p))
    let b := dec3 (proj43Fin (enc4 q))
    have hqp4 : Q4_form 136 (enc4 p).val = 0 := by
      have h : quadForm c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, quadForm_dec4] at h
      have hlt := Q4_form_lt2 136 (enc4 p).val
      generalize Q4_form 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
    have hsp4 : symp4 136 (enc4 p).val = 0 := by
      have h : symp c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, symp_dec4] at h
      have hlt := symp4_lt2 136 (enc4 p).val
      generalize symp4 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
    have hqq4 : Q4_form 136 (enc4 q).val = 0 := by
      have h : quadForm c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, quadForm_dec4] at h
      have hlt := Q4_form_lt2 136 (enc4 q).val
      generalize Q4_form 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
    have hsq4 : symp4 136 (enc4 q).val = 0 := by
      have h : symp c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, symp_dec4] at h
      have hlt := symp4_lt2 136 (enc4 q).val
      generalize symp4 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
    have hAp : Apauli a = p := by simp only [Apauli, a, enc3_dec3, ApauliFin_bij_slice _ hqp4 hsp4, dec4_enc4]
    have hAq : Apauli b = q := by simp only [Apauli, b, enc3_dec3, ApauliFin_bij_slice _ hqq4 hsq4, dec4_enc4]
    have hAp0 : Apauli 0 = 0 := by
      simp only [Apauli]; rw [show enc3 0 = 0 by rw [← dec3_zero, enc3_dec3]]; exact dec4_zero
    have ha0 : a ≠ 0 := fun h => hp0 (by rw [← hAp, h, hAp0])
    have hb0 : b ≠ 0 := fun h => hq0 (by rw [← hAq, h, hAp0])
    have hab_ne : a ≠ b := fun h => hne (by rw [← hAp, ← hAq, h])
    have hab_symp : symp a b = 0 := by rw [← Apauli_symp, hAp, hAq, hsymp]
    have hab0 : a + b ≠ 0 := fun h => hab_ne (by
      have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hs4a : s3 a = s4 p := by
      have := congr_fun hres a; simpa [restrictA, ha0, hAp, s3] using this.symm
    have hs4b : s3 b = s4 q := by
      have := congr_fun hres b; simpa [restrictA, hb0, hAq, s3] using this.symm
    have hs4ab : s3 (a + b) = s4 (p + q) := by
      have := congr_fun hres (a + b)
      simpa [restrictA, hab0, Apauli_add_of_comm hab_symp, hAp, hAq, s3] using this.symm
    refine ⟨(a, b), ?_, Prod.ext hAp hAq⟩
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase, Finset.mem_univ,
      and_true, Q]
    refine ⟨⟨ha0, hb0⟩, hab_ne, hab_symp, by rwa [hAp], by rwa [hAq], ?_⟩
    rw [← Apauli_gammaSgn hab_symp, hAp, hAq, hs4a, hs4b, hs4ab]; exact hfr

private lemma B56_pt_mem_SB (i : Fin 56) :
    dec4 (B56_pt i) ∈ (Qminus c0_88).filter fun p => symp c0_88 p = 1 := by
  have hp := B56_val_props i
  simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h; apply hp.1
    have := congr_arg (fun w => (enc4 w).val) h
    rw [enc4_dec4] at this
    have h0 : enc4 0 = 0 := by rw [← dec4_zero, enc4_dec4]
    rw [h0] at this; exact this
  · simp only [c0_88, quadForm_dec4, B56_pt, hp.2.2.1]; rfl
  · simp only [c0_88, symp_dec4, B56_pt, hp.2.2.2]; rfl

private lemma isEdge56b_iff (i j : Fin 56) :
    isEdge56b i.val j.val = true ↔
      dec4 (B56_pt i) ≠ dec4 (B56_pt j) ∧ symp (dec4 (B56_pt i)) (dec4 (B56_pt j)) = 0 := by
  simp only [isEdge56b, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, symp_dec4, B56_pt]
  constructor
  · rintro ⟨hne, hsp⟩
    refine ⟨fun h => hne (congr_arg Fin.val (B56_val_inj (congr_arg Fin.val (equiv4.symm.injective h)))), ?_⟩
    rw [hsp]; rfl
  · rintro ⟨hne, hsp⟩
    refine ⟨fun h => hne (by rw [Fin.ext h]), ?_⟩
    have hlt := symp4_lt2 (B56_val i.val) (B56_val j.val)
    generalize symp4 (B56_val i.val) (B56_val j.val) = m at hlt hsp ⊢
    interval_cases m <;> simp_all

private lemma inSlice56b_iff (k : Fin 135) (i j : Fin 56) :
    inSlice56b k.val i.val j.val = true ↔
      isEdge56b i.val j.val = true ∧
      symp (dec4 (otherPoutFin k)) (dec4 (B56_pt i)) = 0 ∧
      symp (dec4 (otherPoutFin k)) (dec4 (B56_pt j)) = 0 := by
  have hs_iff : ∀ t : Fin 56,
      (symp4 (otherPout_val k.val) (B56_val t.val) == 0) = true ↔
      symp (dec4 (otherPoutFin k)) (dec4 (B56_pt t)) = 0 := fun t => by
    simp only [beq_iff_eq, symp_dec4, otherPoutFin, B56_pt]
    have hlt := symp4_lt2 (otherPout_val k.val) (B56_val t.val)
    generalize symp4 (otherPout_val k.val) (B56_val t.val) = m at hlt ⊢
    interval_cases m <;> decide
  simp only [inSlice56b, Bool.and_eq_true, hs_iff, and_assoc]

private lemma wEdge56c_eq_frust_sgn (s64 : List ℤ) {s4 : PauliIdx 4 → ℤ}
    (hres : restrictA s4 = listToSign3 s64) {i j : Fin 56} (he : isEdge56b i.val j.val = true) :
    let bi := dec4 (B56_pt i); let bj := dec4 (B56_pt j)
    wEdge56c s64 i.val j.val * s4 bi * s4 bj =
      gammaSgn bi bj * s4 bi * s4 bj * s4 (bi + bj) := by
  intro bi bj
  have hpi := B56_val_props i; have hpj := B56_val_props j
  have ⟨hne, hsymp⟩ := (isEdge56b_iff i j).mp he
  have hmemi := B56_pt_mem_SB i; have hmemj := B56_pt_mem_SB j
  simp only [Finset.mem_filter, Qminus, nzPts, Finset.mem_erase, Finset.mem_univ, and_true] at hmemi hmemj
  have hbij_ne0 : bi + bj ≠ 0 := fun h => hne (by
    have := congr_arg (bi + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  have hbij_Q : quadForm c0_88 (bi + bj) = 0 := by
    rw [quadForm_add, hmemi.1.2, hmemj.1.2, hsymp]; simp
  have hbij_S : symp c0_88 (bi + bj) = 0 := by
    rw [symp_add_right, hmemi.2, hmemj.2]; decide
  have hbij_enc : enc4 (bi + bj) =
      ⟨B56_val i.val ^^^ B56_val j.val, Nat.xor_lt_two_pow (n := 8) hpi.2.1 hpj.2.1⟩ := by
    have hxor := dec4_xor (B56_pt i) (B56_pt j)
    have : bi + bj = dec4 ⟨B56_val i.val ^^^ B56_val j.val, Nat.xor_lt_two_pow (n := 8) hpi.2.1 hpj.2.1⟩ :=
      hxor.symm
    rw [this, enc4_dec4]
  have hq4 : Q4_form 136 (enc4 (bi + bj)).val = 0 := by
    have h : quadForm c0_88 (dec4 (enc4 (bi + bj))) = 0 := by rwa [dec4_enc4]
    rw [c0_88, quadForm_dec4] at h
    have hlt := Q4_form_lt2 136 (enc4 (bi + bj)).val
    generalize Q4_form 136 (enc4 (bi + bj)).val = m at hlt h ⊢; interval_cases m <;> simp_all
  have hs4_ : symp4 136 (enc4 (bi + bj)).val = 0 := by
    have h : symp c0_88 (dec4 (enc4 (bi + bj))) = 0 := by rwa [dec4_enc4]
    rw [c0_88, symp_dec4] at h
    have hlt := symp4_lt2 136 (enc4 (bi + bj)).val
    generalize symp4 136 (enc4 (bi + bj)).val = m at hlt h ⊢; interval_cases m <;> simp_all
  let p3 := dec3 (proj43Fin (enc4 (bi + bj)))
  have hAp3 : Apauli p3 = bi + bj := by
    simp only [Apauli, p3, enc3_dec3, ApauliFin_bij_slice _ hq4 hs4_, dec4_enc4]
  have hp3_ne0 : p3 ≠ 0 := fun h => hbij_ne0 (by
    rw [← hAp3, h]; simp only [Apauli]
    rw [show enc3 0 = 0 by rw [← dec3_zero, enc3_dec3]]; exact dec4_zero)
  have hs4_bij : s4 (bi + bj) = getS64 s64 (proj43Nat (B56_val i.val ^^^ B56_val j.val)) := by
    have h1 := congr_fun hres p3
    simp only [restrictA, hp3_ne0, ↓reduceIte, hAp3, listToSign3] at h1
    rw [h1]; congr 1
    simp only [p3, enc3_dec3, proj43Fin, hbij_enc]
  have hgam : gammaSgn bi bj = gamma4_sgn (B56_val i.val) (B56_val j.val) := by
    simpa [bi, bj, B56_pt] using gammaSgn_dec4 (B56_pt i) (B56_pt j)
  simp only [wEdge56c, he, ↓reduceIte, ← hgam, ← hs4_bij]
  ring

private lemma wEdge56c_symm (s64 : List ℤ) (i j : Fin 56) :
    wEdge56c s64 j.val i.val = wEdge56c s64 i.val j.val := by
  by_cases he : isEdge56b i.val j.val = true
  · have hje : isEdge56b j.val i.val = true := by
      rw [isEdge56b_iff] at he ⊢; exact ⟨he.1.symm, by rw [symp_comm]; exact he.2⟩
    have hsp : symp (dec4 (B56_pt j)) (dec4 (B56_pt i)) = 0 := ((isEdge56b_iff j i).mp hje).2
    have hgam : gamma4_sgn (B56_val j.val) (B56_val i.val) = gamma4_sgn (B56_val i.val) (B56_val j.val) := by
      have h1 := gammaSgn_dec4 (B56_pt j) (B56_pt i)
      have h2 := gammaSgn_dec4 (B56_pt i) (B56_pt j)
      have hc := gammaSgn_comm hsp
      rw [h1, h2] at hc; exact hc
    simp only [wEdge56c, he, hje, ↓reduceIte, hgam, Nat.xor_comm (B56_val j.val)]
  · have hje : isEdge56b j.val i.val ≠ true := fun h => he (by
      rw [isEdge56b_iff] at h ⊢; exact ⟨h.1.symm, by rw [symp_comm]; exact h.2⟩)
    simp only [wEdge56c, Bool.eq_false_iff.mpr he, Bool.eq_false_iff.mpr hje, Bool.false_eq_true, ↓reduceIte]

private lemma sum_wEdge56_total (s64 : List ℤ) {s4 : PauliIdx 4 → ℤ} (hs4 : IsSignAssign s4)
    (hres : restrictA s4 = listToSign3 s64) :
    let x : Fin 56 → ℤ := fun i => s4 (dec4 (B56_pt i))
    let SB := (Qminus c0_88).filter fun p => symp c0_88 p = 1
    let NBB := ((SB ×ˢ SB).filter fun pq =>
      pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
      gammaSgn pq.1 pq.2 * s4 pq.1 * s4 pq.2 * s4 (pq.1 + pq.2) = -1).card
    (∑ i : Fin 56, ∑ j : Fin 56,
      if isEdge56b i.val j.val = true then wEdge56c s64 i.val j.val * x i * x j else 0) =
      1512 - 2 * (NBB : ℤ) := by
  intro x SB NBB
  let E := (Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij => isEdge56b ij.1.val ij.2.val = true
  let F := E.filter fun ij =>
    gammaSgn (dec4 (B56_pt ij.1)) (dec4 (B56_pt ij.2)) * s4 (dec4 (B56_pt ij.1)) *
      s4 (dec4 (B56_pt ij.2)) * s4 (dec4 (B56_pt ij.1) + dec4 (B56_pt ij.2)) = -1
  have hF_eq : F.card = NBB := by
    refine Finset.card_bij (fun ij _ => (dec4 (B56_pt ij.1), dec4 (B56_pt ij.2))) ?_ ?_ ?_
    · rintro ⟨i, j⟩ hij
      simp only [F, E, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      have ⟨hne, hsp⟩ := (isEdge56b_iff i j).mp hij.1
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨B56_pt_mem_SB i, B56_pt_mem_SB j⟩, hne, hsp, hij.2⟩
    · rintro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext
        (B56_val_inj (congr_arg Fin.val (equiv4.symm.injective h.1)))
        (B56_val_inj (congr_arg Fin.val (equiv4.symm.injective h.2)))
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.mem_product, SB, Qminus, nzPts, Finset.mem_erase,
        Finset.mem_univ, and_true] at hpq
      rcases hpq with ⟨⟨⟨⟨hp0, hqp⟩, hsp⟩, ⟨⟨hq0, hqq⟩, hsq⟩⟩, hne, hsymp, hfr⟩
      have h0e : (enc4 0).val = 0 := by
        have : enc4 0 = 0 := by rw [← dec4_zero, enc4_dec4]
        exact congr_arg Fin.val this
      have hp0n : (enc4 p).val ≠ 0 := fun h => hp0 (equiv4.injective (Fin.ext (h.trans h0e.symm)))
      have hq0n : (enc4 q).val ≠ 0 := fun h => hq0 (equiv4.injective (Fin.ext (h.trans h0e.symm)))
      have hqp4 : Q4_form 136 (enc4 p).val = 0 := by
        have h : quadForm c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
        rw [c0_88, quadForm_dec4] at h; have hlt := Q4_form_lt2 136 (enc4 p).val
        generalize Q4_form 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hsp4 : symp4 136 (enc4 p).val = 1 := by
        have h : symp c0_88 (dec4 (enc4 p)) = 1 := by rwa [dec4_enc4]
        rw [c0_88, symp_dec4] at h; have hlt := symp4_lt2 136 (enc4 p).val
        generalize symp4 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hqq4 : Q4_form 136 (enc4 q).val = 0 := by
        have h : quadForm c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
        rw [c0_88, quadForm_dec4] at h; have hlt := Q4_form_lt2 136 (enc4 q).val
        generalize Q4_form 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hsq4 : symp4 136 (enc4 q).val = 1 := by
        have h : symp c0_88 (dec4 (enc4 q)) = 1 := by rwa [dec4_enc4]
        rw [c0_88, symp_dec4] at h; have hlt := symp4_lt2 136 (enc4 q).val
        generalize symp4 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
      obtain ⟨i, hi⟩ := B56_val_surj (enc4 p) hp0n hqp4 hsp4
      obtain ⟨j, hj⟩ := B56_val_surj (enc4 q) hq0n hqq4 hsq4
      have hdi : dec4 (B56_pt i) = p := by
        rw [show B56_pt i = enc4 p from Fin.ext hi, dec4_enc4]
      have hdj : dec4 (B56_pt j) = q := by
        rw [show B56_pt j = enc4 q from Fin.ext hj, dec4_enc4]
      refine ⟨(i, j), ?_, Prod.ext hdi hdj⟩
      simp only [F, E, Finset.mem_filter, Finset.mem_univ, true_and, hdi, hdj, hfr, and_true]
      exact (isEdge56b_iff i j).mpr (by rw [hdi, hdj]; exact ⟨hne, hsymp⟩)
  rw [← Fintype.sum_prod_type (f := fun ij : Fin 56 × Fin 56 =>
        if isEdge56b ij.1.val ij.2.val = true then wEdge56c s64 ij.1.val ij.2.val * x ij.1 * x ij.2 else 0),
      ← Finset.sum_filter]
  have hterm : ∀ ij ∈ E,
      wEdge56c s64 ij.1.val ij.2.val * x ij.1 * x ij.2 =
      1 - 2 * (if gammaSgn (dec4 (B56_pt ij.1)) (dec4 (B56_pt ij.2)) *
        s4 (dec4 (B56_pt ij.1)) * s4 (dec4 (B56_pt ij.2)) *
        s4 (dec4 (B56_pt ij.1) + dec4 (B56_pt ij.2)) = -1 then (1 : ℤ) else 0) := by
    rintro ⟨i, j⟩ hij
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    have he : isEdge56b i.val j.val = true := hij
    rw [wEdge56c_eq_frust_sgn s64 hres he]
    have ⟨hne, _⟩ := (isEdge56b_iff i j).mp he
    have hi0 : dec4 (B56_pt i) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB i)).1).1).1
    have hj0 : dec4 (B56_pt j) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB j)).1).1).1
    have hij0 : dec4 (B56_pt i) + dec4 (B56_pt j) ≠ 0 := fun h => hne (by
      have := congr_arg (dec4 (B56_pt i) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hmul_pm1 : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b = 1 ∨ a * b = -1 := by
      rintro a b (rfl | rfl) (rfl | rfl) <;> decide
    have hpm1 : ∀ z : ℤ, (z = 1 ∨ z = -1) → z = 1 - 2 * (if z = -1 then (1 : ℤ) else 0) := by
      rintro z (rfl | rfl) <;> decide
    exact hpm1 _ (hmul_pm1 _ _ (hmul_pm1 _ _ (hmul_pm1 _ _
      (gammaSgn_eq_pm1 (dec4 (B56_pt i)) (dec4 (B56_pt j)))
      (hs4.2 _ hi0)) (hs4.2 _ hj0)) (hs4.2 _ hij0))
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, Finset.sum_boole, ← hF_eq]
  have hE : E.card = 1512 := card_edges56_total
  have hFc : (E.filter fun x => gammaSgn (dec4 (B56_pt x.1)) (dec4 (B56_pt x.2)) * s4 (dec4 (B56_pt x.1)) *
      s4 (dec4 (B56_pt x.2)) * s4 (dec4 (B56_pt x.1) + dec4 (B56_pt x.2)) = -1).card = F.card :=
    congr_arg Finset.card (by ext x; simp only [F, Finset.mem_filter])
  rw [hE, hFc]; rfl

private lemma sum_wEdge56_slice (k : Fin 135) (s64 : List ℤ) {s4 : PauliIdx 4 → ℤ}
    (hs4 : IsSignAssign s4) (hres : restrictA s4 = listToSign3 s64) :
    let po := dec4 (otherPoutFin k)
    let x : Fin 56 → ℤ := fun i => s4 (dec4 (B56_pt i))
    let SBk := (slicePts c0_88 po).filter fun p => symp c0_88 p = 1
    let NBBk := ((SBk ×ˢ SBk).filter fun pq =>
      pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
      gammaSgn pq.1 pq.2 * s4 pq.1 * s4 pq.2 * s4 (pq.1 + pq.2) = -1).card
    (∑ i : Fin 56, ∑ j : Fin 56,
      if inSlice56b k.val i.val j.val = true then wEdge56c s64 i.val j.val * x i * x j else 0) =
      (EB_ord_table.getD k.val 0 : ℤ) - 2 * (NBBk : ℤ) := by
  intro po x SBk NBBk
  let Ek := (Finset.univ : Finset (Fin 56 × Fin 56)).filter fun ij => inSlice56b k.val ij.1.val ij.2.val = true
  let Fk := Ek.filter fun ij =>
    gammaSgn (dec4 (B56_pt ij.1)) (dec4 (B56_pt ij.2)) * s4 (dec4 (B56_pt ij.1)) *
      s4 (dec4 (B56_pt ij.2)) * s4 (dec4 (B56_pt ij.1) + dec4 (B56_pt ij.2)) = -1
  have hFk_eq : Fk.card = NBBk := by
    refine Finset.card_bij (fun ij _ => (dec4 (B56_pt ij.1), dec4 (B56_pt ij.2))) ?_ ?_ ?_
    · rintro ⟨i, j⟩ hij
      simp only [Fk, Ek, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      have ⟨he, hsi, hsj⟩ := (inSlice56b_iff k i j).mp hij.1
      have ⟨hne, hsp⟩ := (isEdge56b_iff i j).mp he
      have hmi := B56_pt_mem_SB i; have hmj := B56_pt_mem_SB j
      simp only [Finset.mem_filter] at hmi hmj
      simp only [Finset.mem_filter, Finset.mem_product, SBk, slicePts]
      exact ⟨⟨⟨⟨hmi.1, hsi⟩, hmi.2⟩, ⟨⟨hmj.1, hsj⟩, hmj.2⟩⟩, hne, hsp, hij.2⟩
    · rintro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext
        (B56_val_inj (congr_arg Fin.val (equiv4.symm.injective h.1)))
        (B56_val_inj (congr_arg Fin.val (equiv4.symm.injective h.2)))
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.mem_product, SBk, slicePts, Qminus, nzPts,
        Finset.mem_erase, Finset.mem_univ, and_true] at hpq
      rcases hpq with ⟨⟨⟨⟨⟨hp0, hqp⟩, hppo⟩, hsp⟩, ⟨⟨⟨hq0, hqq⟩, hqpo⟩, hsq⟩⟩, hne, hsymp, hfr⟩
      have h0e : (enc4 0).val = 0 := by
        have : enc4 0 = 0 := by rw [← dec4_zero, enc4_dec4]
        exact congr_arg Fin.val this
      have hp0n : (enc4 p).val ≠ 0 := fun h => hp0 (equiv4.injective (Fin.ext (h.trans h0e.symm)))
      have hq0n : (enc4 q).val ≠ 0 := fun h => hq0 (equiv4.injective (Fin.ext (h.trans h0e.symm)))
      have hqp4 : Q4_form 136 (enc4 p).val = 0 := by
        have h : quadForm c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
        rw [c0_88, quadForm_dec4] at h; have hlt := Q4_form_lt2 136 (enc4 p).val
        generalize Q4_form 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hsp4 : symp4 136 (enc4 p).val = 1 := by
        have h : symp c0_88 (dec4 (enc4 p)) = 1 := by rwa [dec4_enc4]
        rw [c0_88, symp_dec4] at h; have hlt := symp4_lt2 136 (enc4 p).val
        generalize symp4 136 (enc4 p).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hqq4 : Q4_form 136 (enc4 q).val = 0 := by
        have h : quadForm c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
        rw [c0_88, quadForm_dec4] at h; have hlt := Q4_form_lt2 136 (enc4 q).val
        generalize Q4_form 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
      have hsq4 : symp4 136 (enc4 q).val = 1 := by
        have h : symp c0_88 (dec4 (enc4 q)) = 1 := by rwa [dec4_enc4]
        rw [c0_88, symp_dec4] at h; have hlt := symp4_lt2 136 (enc4 q).val
        generalize symp4 136 (enc4 q).val = m at hlt h ⊢; interval_cases m <;> simp_all
      obtain ⟨i, hi⟩ := B56_val_surj (enc4 p) hp0n hqp4 hsp4
      obtain ⟨j, hj⟩ := B56_val_surj (enc4 q) hq0n hqq4 hsq4
      have hdi : dec4 (B56_pt i) = p := by rw [show B56_pt i = enc4 p from Fin.ext hi, dec4_enc4]
      have hdj : dec4 (B56_pt j) = q := by rw [show B56_pt j = enc4 q from Fin.ext hj, dec4_enc4]
      refine ⟨(i, j), ?_, Prod.ext hdi hdj⟩
      simp only [Fk, Ek, Finset.mem_filter, Finset.mem_univ, true_and, hdi, hdj, hfr, and_true]
      exact (inSlice56b_iff k i j).mpr ⟨(isEdge56b_iff i j).mpr (by rw [hdi, hdj]; exact ⟨hne, hsymp⟩),
        by rwa [hdi], by rwa [hdj]⟩
  rw [← Fintype.sum_prod_type (f := fun ij : Fin 56 × Fin 56 =>
        if inSlice56b k.val ij.1.val ij.2.val = true then wEdge56c s64 ij.1.val ij.2.val * x ij.1 * x ij.2 else 0),
      ← Finset.sum_filter]
  have hterm : ∀ ij ∈ Ek,
      wEdge56c s64 ij.1.val ij.2.val * x ij.1 * x ij.2 =
      1 - 2 * (if gammaSgn (dec4 (B56_pt ij.1)) (dec4 (B56_pt ij.2)) *
        s4 (dec4 (B56_pt ij.1)) * s4 (dec4 (B56_pt ij.2)) *
        s4 (dec4 (B56_pt ij.1) + dec4 (B56_pt ij.2)) = -1 then (1 : ℤ) else 0) := by
    rintro ⟨i, j⟩ hij
    simp only [Ek, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    have he : isEdge56b i.val j.val = true := ((inSlice56b_iff k i j).mp hij).1
    rw [wEdge56c_eq_frust_sgn s64 hres he]
    have ⟨hne, _⟩ := (isEdge56b_iff i j).mp he
    have hi0 : dec4 (B56_pt i) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB i)).1).1).1
    have hj0 : dec4 (B56_pt j) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB j)).1).1).1
    have hij0 : dec4 (B56_pt i) + dec4 (B56_pt j) ≠ 0 := fun h => hne (by
      have := congr_arg (dec4 (B56_pt i) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hmul_pm1 : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b = 1 ∨ a * b = -1 := by
      rintro a b (rfl | rfl) (rfl | rfl) <;> decide
    have hpm1 : ∀ z : ℤ, (z = 1 ∨ z = -1) → z = 1 - 2 * (if z = -1 then (1 : ℤ) else 0) := by
      rintro z (rfl | rfl) <;> decide
    exact hpm1 _ (hmul_pm1 _ _ (hmul_pm1 _ _ (hmul_pm1 _ _
      (gammaSgn_eq_pm1 (dec4 (B56_pt i)) (dec4 (B56_pt j)))
      (hs4.2 _ hi0)) (hs4.2 _ hj0)) (hs4.2 _ hij0))
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, Finset.sum_boole, ← hFk_eq]
  have hEk : Ek.card = EB_ord_table.getD k.val 0 := card_edges56_slice k
  rw [hEk]

/-- **Master Soundness of `checkCert56`**:
    If `checkCert56 cert = true`, then ANY 4-qubit sign assignment `s4` with min-slice at `c0_88`
    whose `W(5,2)` restriction equals `listToSign3 cert.s64` satisfies `frustPairs (Qminus c0_88) s4 ≥ 315 * 6`! -/
theorem sound_checkCert56 (cert : Cert56) (hcert : checkCert56 cert = true)
    {s4 : PauliIdx 4 → ℤ} (hs4 : IsSignAssign s4)
    (hmin : ∀ po ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) s4 ≤ frustPairs (slicePts c0_88 po) s4)
    (hres : restrictA s4 = listToSign3 cert.s64) :
    315 * 6 ≤ frustPairs (Qminus c0_88) s4 := by
  unfold checkCert56 at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSpos, hKpos⟩, hs64_len⟩, hs64_pm⟩, hfA0_eq⟩, hdi_len⟩, hdi_sum⟩,
    halphas⟩, hbetas⟩, hlin_lt⟩, hAlens⟩, hQmatch⟩, hall⟩
  let x : Fin 56 → ℤ := fun i => s4 (dec4 (B56_pt i))
  have hx : ∀ i : Fin 56, x i = 1 ∨ x i = -1 := fun i => by
    have hi0 : dec4 (B56_pt i) ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB i)).1).1).1
    exact hs4.2 _ hi0
  have hxsq : ∀ i : Fin 56, x i * x i = 1 := fun i => by rcases hx i with h | h <;> rw [h] <;> norm_num
  -- 1. PSD bound `0 ≤ xᵀ Q x` from `sound_checkAllRows`
  let Q : Fin 56 → Fin 56 → ℤ := fun i j => Qspec cert i.val j.val
  have hQsym : ∀ i j : Fin 56, Q i j = Q j i := by
    intro i j
    simp only [Q, Qspec]
    by_cases hij : i = j
    · subst hij; simp
    · have hne1 : (i.val == j.val) = false := beq_false_of_ne (Fin.val_ne_of_ne hij)
      have hne2 : (j.val == i.val) = false := beq_false_of_ne (Fin.val_ne_of_ne (Ne.symm hij))
      simp only [hne1, hne2, Bool.false_eq_true, ↓reduceIte]
      have hedge : isEdge56b i.val j.val = isEdge56b j.val i.val := by
        apply Bool.eq_iff_iff.mpr
        rw [isEdge56b_iff, isEdge56b_iff]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, by rwa [symp_comm]⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, by rwa [symp_comm]⟩⟩
      have hslice_sym : ∀ k, inSlice56b k i.val j.val = inSlice56b k j.val i.val := fun k => by
        simp only [inSlice56b, hedge]; cases isEdge56b j.val i.val <;> simp [Bool.and_comm]
      have hsubA : ∀ (L : List (Nat × Nat)) (a : ℤ),
          L.foldl (fun acc (k, val) => if inSlice56b k i.val j.val then acc + (val : ℤ) else acc) a =
          L.foldl (fun acc (k, val) => if inSlice56b k j.val i.val then acc + (val : ℤ) else acc) a := by
        intro L; induction L with
        | nil => intro _; rfl
        | cons kv rest ih => intro a; simp only [List.foldl_cons, hslice_sym kv.1]; exact ih _
      have hsubB : ∀ (L : List (Nat × Nat × Nat × Nat)) (a : ℤ),
          L.foldl (fun acc (a, b, c, val) =>
            if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
               (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
               (i.val == a && j.val == c) || (i.val == c && j.val == a)
            then acc + (val : ℤ) else acc) a =
          L.foldl (fun acc (a, b, c, val) =>
            if (j.val == a && i.val == b) || (j.val == b && i.val == a) ||
               (j.val == b && i.val == c) || (j.val == c && i.val == b) ||
               (j.val == a && i.val == c) || (j.val == c && i.val == a)
            then acc + (val : ℤ) else acc) a := by
        intro L; induction L with
        | nil => intro _; rfl
        | cons t rest ih =>
          intro acc; rcases t with ⟨a, b, c, val⟩
          have hcond : ((i.val == a && j.val == b) || (i.val == b && j.val == a) ||
              (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
              (i.val == a && j.val == c) || (i.val == c && j.val == a)) =
            ((j.val == a && i.val == b) || (j.val == b && i.val == a) ||
              (j.val == b && i.val == c) || (j.val == c && i.val == b) ||
              (j.val == a && i.val == c) || (j.val == c && i.val == a)) := by
            have hbool : ∀ p1 p2 p3 p4 p5 p6 : Bool,
                ((p1 && p2) || (p3 && p4) || (p3 && p6) || (p5 && p2) || (p1 && p6) || (p5 && p4)) =
                ((p4 && p3) || (p2 && p1) || (p2 && p5) || (p6 && p3) || (p4 && p5) || (p6 && p1)) := by
              decide
            exact hbool (i.val == a) (j.val == b) (i.val == b) (j.val == a) (i.val == c) (j.val == c)
          simp only [List.foldl_cons, hcond]; exact ih _
      rw [hedge]
      split_ifs
      · rw [wEdge56c_symm cert.s64 i j]; simp only [ecSpec, hsubA, hsubB]
      · rfl
  have hQlow_spec : cert.Qlow.length = 56 ∧
      ∀ i j : Fin 56, j.val ≤ i.val →
        (cert.Qlow.getD i.val []).length = i.val + 1 ∧
        (((cert.Qlow.getD i.val []).getD j.val 0 : Nat) : ℤ) =
          (cert.K : ℤ) * (cert.K : ℤ) * Q i j + (cert.QOFF : ℤ) := by
    have hrow : ∀ (i : Nat) (j : Nat) (row : List Nat),
        checkQRow cert ((cert.K : ℤ) * (cert.K : ℤ)) i j row = true →
        row.length + j = i + 1 ∧
        ∀ m, m < row.length →
          ((row.getD m 0 : Nat) : ℤ) =
            (cert.K : ℤ) * (cert.K : ℤ) * Qspec cert i (j + m) + (cert.QOFF : ℤ) := by
      intro i j row; induction row generalizing j with
      | nil =>
        intro h; simp only [checkQRow, Nat.beq_eq,
          show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl] at h
        exact ⟨by simp; omega, fun m hm => by simp at hm⟩
      | cons q qs ih =>
        intro h; simp only [checkQRow,
          show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl] at h
        split_ifs at h with hok
        · simp only [beq_iff_eq] at hok
          obtain ⟨hlen, hspec⟩ := ih (j + 1) h
          refine ⟨by simp; omega, fun m hm => ?_⟩
          cases m with
          | zero => simpa using hok
          | succ m' =>
            have := hspec m' (by simp at hm; omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hallQ : ∀ (i : Nat) (rows : List (List Nat)),
        checkQMatch cert ((cert.K : ℤ) * (cert.K : ℤ)) i rows = true →
        rows.length + i = 56 ∧
        ∀ m, m < rows.length →
          (rows.getD m []).length = i + m + 1 ∧
          ∀ j, j ≤ i + m →
            (((rows.getD m []).getD j 0 : Nat) : ℤ) =
              (cert.K : ℤ) * (cert.K : ℤ) * Qspec cert (i + m) j + (cert.QOFF : ℤ) := by
      intro i rows; induction rows generalizing i with
      | nil =>
        intro h; simp only [checkQMatch, Nat.beq_eq] at h
        exact ⟨by simp; omega, fun m hm => by simp at hm⟩
      | cons r rs ih =>
        intro h; simp only [checkQMatch,
          show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl] at h
        split_ifs at h with hr
        · obtain ⟨hrlen, hrspec⟩ := hrow i 0 r hr
          obtain ⟨hslen, hsspec⟩ := ih (i + 1) h
          refine ⟨by simp; omega, fun m hm => ?_⟩
          cases m with
          | zero =>
            refine ⟨by simpa using hrlen, fun j hj => ?_⟩
            simpa using hrspec j (by omega)
          | succ m' =>
            have h1 := hsspec m' (by simp at hm; omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
    obtain ⟨hlen, hspec⟩ := hallQ 0 cert.Qlow hQmatch
    refine ⟨by omega, fun i j hj => ?_⟩
    have hi := hspec i.val (by have := i.isLt; omega)
    exact ⟨by simpa using hi.1, by simpa [Q] using hi.2 j.val (by omega)⟩
  have hquad_nn : 0 ≤ ∑ i : Fin 56, ∑ j : Fin 56, Q i j * x i * x j := by
    have hK2 := sound_checkAllRows hQsym hAlens (fun i j hij => (hQlow_spec.2 i j hij).2)
      hQlow_spec.1 (fun i => (hQlow_spec.2 i i (le_refl _)).1) hall x hx
    have hKposZ : (0 : ℤ) < (cert.K : ℤ) * (cert.K : ℤ) := by nlinarith
    nlinarith
  -- 2. Expand `∑ i j, Q i j * x i * x j`:
  --    diagonal sum = `56 * mu`, off-diagonal = `-S * W_tot + sum_alphas + sum_betas`
  have hdi_zero : ∑ i : Fin 56, cert.di.getD i.val 0 = 0 := by
    have hfold : ∀ (L : List ℤ) (a : ℤ), L.foldl (· + ·) a = a + ∑ k : Fin L.length, L.getD k.val 0 := by
      intro L; induction L with
      | nil => intro a; simp
      | cons v vs ih =>
        intro a; simp only [List.foldl_cons, ih, List.length_cons, Fin.sum_univ_succ]
        have hsum : ∑ k : Fin vs.length, (v :: vs).getD k.succ.val 0 =
            ∑ k : Fin vs.length, vs.getD k.val 0 :=
          Finset.sum_congr rfl fun _ _ => rfl
        rw [hsum]; change a + v + _ = a + (v + _); ring
    have h := hfold cert.di 0
    rw [hdi_sum, zero_add] at h
    have hcast : ∑ k : Fin cert.di.length, cert.di.getD k.val 0 = ∑ i : Fin 56, cert.di.getD i.val 0 := by
      refine Finset.sum_bij (fun k _ => ⟨k.val, by have := k.isLt; omega⟩) (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Fin.ext (by simpa using congr_arg Fin.val h))
        (fun i _ => ⟨⟨i.val, by have := i.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    rw [hcast] at h; exact h.symm
  let Wtot : ℤ := ∑ i : Fin 56, ∑ j : Fin 56,
    if isEdge56b i.val j.val = true then wEdge56c cert.s64 i.val j.val * x i * x j else 0
  let Wsl : Nat → ℤ := fun k => ∑ i : Fin 56, ∑ j : Fin 56,
    if inSlice56b k i.val j.val = true then wEdge56c cert.s64 i.val j.val * x i * x j else 0
  have hA_fold : ∀ (L : List (Nat × Nat)) (acc : ℤ),
      (∑ i : Fin 56, ∑ j : Fin 56,
        if isEdge56b i.val j.val = true then
          (L.foldl (fun a (k, val) => if inSlice56b k i.val j.val then a + (val : ℤ) else a) acc) *
            wEdge56c cert.s64 i.val j.val * x i * x j
        else 0) =
      acc * Wtot + L.foldl (fun a (k, val) => a + (val : ℤ) * Wsl k) 0 := by
    intro L; induction L with
    | nil =>
      intro acc
      simp only [List.foldl_nil, add_zero, Wtot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    | cons kv rest ih =>
      intro acc; rcases kv with ⟨k, val⟩
      have hshift : ∀ (R : List (Nat × Nat)) (a b : ℤ),
          R.foldl (fun s (k', v') => s + (v' : ℤ) * Wsl k') (a + b) =
          a + R.foldl (fun s (k', v') => s + (v' : ℤ) * Wsl k') b := by
        intro R; induction R with
        | nil => intro _ _; rfl
        | cons p ps ihr => intro a b; simp only [List.foldl_cons, add_assoc, ihr]
      have hshiftI : ∀ (R : List (Nat × Nat)) (i j : Fin 56) (a b : ℤ),
          R.foldl (fun s (k', v') => if inSlice56b k' i.val j.val then s + (v' : ℤ) else s) (a + b) =
          a + R.foldl (fun s (k', v') => if inSlice56b k' i.val j.val then s + (v' : ℤ) else s) b := by
        intro R; induction R with
        | nil => intro _ _ _ _; rfl
        | cons p ps ihr =>
          intro i j a b; simp only [List.foldl_cons]
          split_ifs
          · rw [add_assoc, ihr]
          · exact ihr i j a b
      simp only [List.foldl_cons, zero_add]
      rw [show rest.foldl (fun a (k', v') => a + (v' : ℤ) * Wsl k') ((val : ℤ) * Wsl k) =
          (val : ℤ) * Wsl k + rest.foldl (fun a (k', v') => a + (v' : ℤ) * Wsl k') 0 from
            by simpa using hshift rest ((val : ℤ) * Wsl k) 0]
      have hsplit_head : ∀ i j : Fin 56,
          (if isEdge56b i.val j.val = true then
            rest.foldl (fun a (k', v') => if inSlice56b k' i.val j.val then a + (v' : ℤ) else a)
              (if inSlice56b k i.val j.val = true then acc + (val : ℤ) else acc) *
              wEdge56c cert.s64 i.val j.val * x i * x j
          else 0) =
          (if isEdge56b i.val j.val = true then
            rest.foldl (fun a (k', v') => if inSlice56b k' i.val j.val then a + (v' : ℤ) else a) acc *
              wEdge56c cert.s64 i.val j.val * x i * x j
          else 0) +
          (val : ℤ) * (if inSlice56b k i.val j.val = true then wEdge56c cert.s64 i.val j.val * x i * x j else 0) := by
        intro i j
        by_cases hs : inSlice56b k i.val j.val = true
        · have he : isEdge56b i.val j.val = true := by
            simp only [inSlice56b, Bool.and_eq_true] at hs; exact hs.1.1
          simp only [hs, he, ↓reduceIte]
          rw [show acc + (val : ℤ) = (val : ℤ) + acc by ring, hshiftI rest i j (val : ℤ) acc]
          ring
        · rw [if_neg hs, if_neg hs]; ring
      simp_rw [hsplit_head, Finset.sum_add_distrib, ih acc, ← Finset.mul_sum]
      change acc * Wtot + rest.foldl (fun a (k', v') => a + (v' : ℤ) * Wsl k') 0 + (val : ℤ) * Wsl k = _
      ring
  let triSum : Nat → Nat → Nat → ℤ := fun a b c =>
    ∑ i : Fin 56, ∑ j : Fin 56,
      if isEdge56b i.val j.val = true then
        (if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
            (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
            (i.val == a && j.val == c) || (i.val == c && j.val == a)
         then wEdge56c cert.s64 i.val j.val * x i * x j else 0)
      else 0
  have hB_fold : ∀ (L : List (Nat × Nat × Nat × Nat)) (acc : ℤ),
      (∑ i : Fin 56, ∑ j : Fin 56,
        if isEdge56b i.val j.val = true then
          (L.foldl (fun s (a, b, c, val) =>
            if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
               (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
               (i.val == a && j.val == c) || (i.val == c && j.val == a)
            then s + (val : ℤ) else s) acc) *
            wEdge56c cert.s64 i.val j.val * x i * x j
        else 0) =
      acc * Wtot + L.foldl (fun s (a, b, c, val) => s + (val : ℤ) * triSum a b c) 0 := by
    intro L; induction L with
    | nil =>
      intro acc
      simp only [List.foldl_nil, add_zero, Wtot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    | cons t rest ih =>
      intro acc; rcases t with ⟨a, b, c, val⟩
      have hshift : ∀ (R : List (Nat × Nat × Nat × Nat)) (u v : ℤ),
          R.foldl (fun s (a', b', c', v') => s + (v' : ℤ) * triSum a' b' c') (u + v) =
          u + R.foldl (fun s (a', b', c', v') => s + (v' : ℤ) * triSum a' b' c') v := by
        intro R; induction R with
        | nil => intro _ _; rfl
        | cons p ps ihr => intro u v; simp only [List.foldl_cons, add_assoc, ihr]
      have hshiftI : ∀ (R : List (Nat × Nat × Nat × Nat)) (i j : Fin 56) (u v : ℤ),
          R.foldl (fun s (a', b', c', v') =>
            if (i.val == a' && j.val == b') || (i.val == b' && j.val == a') ||
               (i.val == b' && j.val == c') || (i.val == c' && j.val == b') ||
               (i.val == a' && j.val == c') || (i.val == c' && j.val == a')
            then s + (v' : ℤ) else s) (u + v) =
          u + R.foldl (fun s (a', b', c', v') =>
            if (i.val == a' && j.val == b') || (i.val == b' && j.val == a') ||
               (i.val == b' && j.val == c') || (i.val == c' && j.val == b') ||
               (i.val == a' && j.val == c') || (i.val == c' && j.val == a')
            then s + (v' : ℤ) else s) v := by
        intro R; induction R with
        | nil => intro _ _ _ _; rfl
        | cons p ps ihr =>
          intro i j u v; simp only [List.foldl_cons]
          split_ifs
          · rw [add_assoc, ihr]
          · exact ihr i j u v
      simp only [List.foldl_cons, zero_add]
      rw [show rest.foldl (fun s (a', b', c', v') => s + (v' : ℤ) * triSum a' b' c') ((val : ℤ) * triSum a b c) =
          (val : ℤ) * triSum a b c + rest.foldl (fun s (a', b', c', v') => s + (v' : ℤ) * triSum a' b' c') 0 from
            by simpa using hshift rest ((val : ℤ) * triSum a b c) 0]
      have hsplit_head : ∀ i j : Fin 56,
          (if isEdge56b i.val j.val = true then
            rest.foldl (fun s (a', b', c', v') =>
              if (i.val == a' && j.val == b') || (i.val == b' && j.val == a') ||
                 (i.val == b' && j.val == c') || (i.val == c' && j.val == b') ||
                 (i.val == a' && j.val == c') || (i.val == c' && j.val == a')
              then s + (v' : ℤ) else s)
              (if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
                  (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
                  (i.val == a && j.val == c) || (i.val == c && j.val == a)
               then acc + (val : ℤ) else acc) *
              wEdge56c cert.s64 i.val j.val * x i * x j
          else 0) =
          (if isEdge56b i.val j.val = true then
            rest.foldl (fun s (a', b', c', v') =>
              if (i.val == a' && j.val == b') || (i.val == b' && j.val == a') ||
                 (i.val == b' && j.val == c') || (i.val == c' && j.val == b') ||
                 (i.val == a' && j.val == c') || (i.val == c' && j.val == a')
              then s + (v' : ℤ) else s) acc *
              wEdge56c cert.s64 i.val j.val * x i * x j
          else 0) +
          (val : ℤ) * (if isEdge56b i.val j.val = true then
            (if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
                (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
                (i.val == a && j.val == c) || (i.val == c && j.val == a)
             then wEdge56c cert.s64 i.val j.val * x i * x j else 0)
          else 0) := by
        intro i j
        by_cases he : isEdge56b i.val j.val = true
        · simp only [he, ↓reduceIte]
          split_ifs
          · rw [show acc + (val : ℤ) = (val : ℤ) + acc by ring, hshiftI rest i j (val : ℤ) acc]; ring
          · ring
        · rw [if_neg he, if_neg he, if_neg he]; ring
      simp_rw [hsplit_head, Finset.sum_add_distrib, ih acc, ← Finset.mul_sum]
      change acc * Wtot + rest.foldl (fun s (a', b', c', v') => s + (v' : ℤ) * triSum a' b' c') 0 +
        (val : ℤ) * triSum a b c = _
      ring
  have hQ_expand : ∑ i : Fin 56, ∑ j : Fin 56, Q i j * x i * x j =
      56 * (cert.mu : ℤ) - (cert.S : ℤ) * Wtot +
      cert.alphas.foldl (fun a (k, val) => a + (val : ℤ) * Wsl k) 0 +
      cert.betas.foldl (fun a (a', b', c', val) => a + (val : ℤ) * triSum a' b' c') 0 := by
    have hsplit : ∀ i j : Fin 56, Q i j * x i * x j =
        (if i = j then (cert.mu : ℤ) + cert.di.getD i.val 0 else 0) +
        (if isEdge56b i.val j.val = true then
          (-(cert.S : ℤ)) * wEdge56c cert.s64 i.val j.val * x i * x j +
          (cert.alphas.foldl (fun acc (k, val) =>
            if inSlice56b k i.val j.val then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j +
          (cert.betas.foldl (fun acc (a, b, c, val) =>
            if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
               (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
               (i.val == a && j.val == c) || (i.val == c && j.val == a)
            then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j
        else 0) := by
      intro i j
      simp only [Q, Qspec]
      by_cases hij : i = j
      · subst hij
        have he : isEdge56b i.val i.val = false := by simp [isEdge56b]
        simp only [beq_self_eq_true, ↓reduceIte, he, Bool.false_eq_true, add_zero]
        calc ((cert.mu : ℤ) + cert.di.getD i.val 0) * x i * x i
            = ((cert.mu : ℤ) + cert.di.getD i.val 0) * (x i * x i) := by ring
          _ = (cert.mu : ℤ) + cert.di.getD i.val 0 := by rw [hxsq i, mul_one]
      · have hne : (i.val == j.val) = false := beq_false_of_ne (Fin.val_ne_of_ne hij)
        simp only [hij, hne, Bool.false_eq_true, ↓reduceIte, zero_add]
        split_ifs
        · simp only [ecSpec]; ring
        · ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hdiag : (∑ i : Fin 56, ∑ j : Fin 56, if i = j then (cert.mu : ℤ) + cert.di.getD i.val 0 else 0) =
        56 * (cert.mu : ℤ) := by
      have h1 : ∀ i : Fin 56,
          (∑ j : Fin 56, if i = j then (cert.mu : ℤ) + cert.di.getD i.val 0 else 0) =
          (cert.mu : ℤ) + cert.di.getD i.val 0 := fun i => by simp
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hdi_zero, add_zero]; rfl
    have hoff_split : ∀ i j : Fin 56,
        (if isEdge56b i.val j.val = true then
          (-(cert.S : ℤ)) * wEdge56c cert.s64 i.val j.val * x i * x j +
          (cert.alphas.foldl (fun acc (k, val) =>
            if inSlice56b k i.val j.val then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j +
          (cert.betas.foldl (fun acc (a, b, c, val) =>
            if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
               (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
               (i.val == a && j.val == c) || (i.val == c && j.val == a)
            then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j
        else 0) =
        (if isEdge56b i.val j.val = true then (-(cert.S : ℤ)) * wEdge56c cert.s64 i.val j.val * x i * x j else 0) +
        (if isEdge56b i.val j.val = true then
          (cert.alphas.foldl (fun acc (k, val) =>
            if inSlice56b k i.val j.val then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j else 0) +
        (if isEdge56b i.val j.val = true then
          (cert.betas.foldl (fun acc (a, b, c, val) =>
            if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
               (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
               (i.val == a && j.val == c) || (i.val == c && j.val == a)
            then acc + (val : ℤ) else acc) 0) *
            wEdge56c cert.s64 i.val j.val * x i * x j else 0) := fun i j => by split_ifs <;> ring
    simp_rw [hoff_split, Finset.sum_add_distrib]
    have hSterm : (∑ i : Fin 56, ∑ j : Fin 56,
        if isEdge56b i.val j.val = true then (-(cert.S : ℤ)) * wEdge56c cert.s64 i.val j.val * x i * x j else 0) =
        -(cert.S : ℤ) * Wtot := by
      simp only [Wtot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [hdiag, hSterm, hA_fold cert.alphas 0, hB_fold cert.betas 0]
    ring
  -- 3. Upper bound alpha terms using `hmin`
  have hfA0_pairs : frustPairs (slicePts c0_88 c0_88) s4 = 6 * cert.fA0 := by
    rw [frustPairs_slice_eq_restrictA, hres, countFrustWlines_eq_frustPairs, hfA0_eq]
  have hWsl_le : ∀ k : Fin 135,
      Wsl k.val ≤ (EB_ord_table.getD k.val 0 : ℤ) + 4 * ((countFrustWlinesSlice k.val cert.s64 : ℤ) - (cert.fA0 : ℤ)) := by
    intro k
    let po := dec4 (otherPoutFin k)
    have hpo_mem : po ∈ outPts c0_88 := by
      rw [outPts, Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [po, c0_88]; rw [quadForm_dec4]; simp [otherPoutFin, (otherPout_props k).2]
    have hsub : slicePts c0_88 po ⊆ Qminus c0_88 := fun _ hp => (Finset.mem_filter.mp hp).1
    have hclosed : ∀ p ∈ slicePts c0_88 po, ∀ q ∈ slicePts c0_88 po, p ≠ q → symp p q = 0 →
        p + q ∈ slicePts c0_88 po := by
      intro p hp q hq hne hsp
      simp only [slicePts, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        and_true] at hp hq ⊢
      refine ⟨⟨fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm),
        by rw [quadForm_add, hp.1.2, hq.1.2, hsp]; simp⟩,
        by rw [symp_add_right, hp.2, hq.2, add_zero]⟩
    have hsplit := frustPairs_AB_split hsub hclosed s4
    dsimp only at hsplit
    have hSA := countFrustWlinesSlice_eq_frustPairs k cert.s64 hres
    have hmink := hmin po hpo_mem
    rw [hfA0_pairs, hsplit, hSA] at hmink
    have hsum := sum_wEdge56_slice k cert.s64 hs4 hres
    dsimp only at hsum
    change Wsl k.val = _ at hsum
    have hminkZ : (6 * cert.fA0 : ℤ) ≤
        6 * (countFrustWlinesSlice k.val cert.s64 : ℤ) +
        3 * (frustPairs ((slicePts c0_88 po).filter fun p => symp c0_88 p = 1) s4 : ℤ) := by
      exact_mod_cast hmink
    dsimp only [po] at hminkZ
    unfold frustPairs at hminkZ
    omega
  have halpha_le : cert.alphas.foldl (fun a (k, val) => a + (val : ℤ) * Wsl k) 0 ≤
      cert.alphas.foldl (fun acc (k, val) =>
        acc + (val : ℤ) * ((EB_ord_table.getD k 0 : ℤ) + 4 * ((countFrustWlinesSlice k cert.s64 : ℤ) - (cert.fA0 : ℤ)))) 0 := by
    have hgen : ∀ (L : List (Nat × Nat)) (a1 a2 : ℤ), a1 ≤ a2 → checkAlphas L = true →
        L.foldl (fun a (k, val) => a + (val : ℤ) * Wsl k) a1 ≤
        L.foldl (fun acc (k, val) =>
          acc + (val : ℤ) * ((EB_ord_table.getD k 0 : ℤ) + 4 * ((countFrustWlinesSlice k cert.s64 : ℤ) - (cert.fA0 : ℤ)))) a2 := by
      intro L; induction L with
      | nil => intro _ _ h _; exact h
      | cons kv rest ih =>
        intro a1 a2 hle hok
        rcases kv with ⟨k, val⟩
        simp only [checkAlphas, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
        simp only [List.foldl_cons]
        refine ih _ _ ?_ hok.2
        have hk := hWsl_le ⟨k, hok.1.1⟩
        have hmul := mul_le_mul_of_nonneg_left hk (Int.natCast_nonneg val)
        linarith
    exact hgen cert.alphas 0 0 le_rfl halphas
  -- 4. Upper bound beta triangle terms: `triSum a b c ≤ 2`
  have htri_le : ∀ a b c : Nat, a < b → b < c → c < 56 →
      isEdge56b a b = true → isEdge56b b c = true → isEdge56b a c = true →
      wEdge56c cert.s64 a b * wEdge56c cert.s64 b c * wEdge56c cert.s64 a c = -1 →
      triSum a b c ≤ 2 := by
    intro a b c hab hbc hc56 heab hebc heac hwprod
    let fa : Fin 56 := ⟨a, by omega⟩; let fb : Fin 56 := ⟨b, by omega⟩; let fc : Fin 56 := ⟨c, hc56⟩
    have hterm_eq : ∀ i j : Fin 56,
        (if isEdge56b i.val j.val = true then
          (if (i.val == a && j.val == b) || (i.val == b && j.val == a) ||
              (i.val == b && j.val == c) || (i.val == c && j.val == b) ||
              (i.val == a && j.val == c) || (i.val == c && j.val == a)
           then wEdge56c cert.s64 i.val j.val * x i * x j else 0)
        else 0) =
        (if i = fa ∧ j = fb then wEdge56c cert.s64 a b * x fa * x fb else 0) +
        (if i = fb ∧ j = fa then wEdge56c cert.s64 b a * x fb * x fa else 0) +
        (if i = fb ∧ j = fc then wEdge56c cert.s64 b c * x fb * x fc else 0) +
        (if i = fc ∧ j = fb then wEdge56c cert.s64 c b * x fc * x fb else 0) +
        (if i = fa ∧ j = fc then wEdge56c cert.s64 a c * x fa * x fc else 0) +
        (if i = fc ∧ j = fa then wEdge56c cert.s64 c a * x fc * x fa else 0) := by
      intro i j
      have hba : isEdge56b b a = true :=
        (isEdge56b_iff fb fa).mpr (by have h := (isEdge56b_iff fa fb).mp heab; exact ⟨h.1.symm, by rw [symp_comm]; exact h.2⟩)
      have hcb : isEdge56b c b = true :=
        (isEdge56b_iff fc fb).mpr (by have h := (isEdge56b_iff fb fc).mp hebc; exact ⟨h.1.symm, by rw [symp_comm]; exact h.2⟩)
      have hca : isEdge56b c a = true :=
        (isEdge56b_iff fc fa).mpr (by have h := (isEdge56b_iff fa fc).mp heac; exact ⟨h.1.symm, by rw [symp_comm]; exact h.2⟩)
      have hab_ne : fa ≠ fb := fun h => by have := congr_arg Fin.val h; dsimp [fa, fb] at this; omega
      have hbc_ne : fb ≠ fc := fun h => by have := congr_arg Fin.val h; dsimp [fb, fc] at this; omega
      have hac_ne : fa ≠ fc := fun h => by have := congr_arg Fin.val h; dsimp [fa, fc] at this; omega
      have hval_ne : ∀ u v : Fin 56, u ≠ v → (u.val == v.val) = false := fun u v h => beq_false_of_ne (Fin.val_ne_of_ne h)
      by_cases hia : i = fa
      · subst hia
        by_cases hjb : j = fb
        · subst hjb; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, heab]
        · by_cases hjc : j = fc
          · subst hjc; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, heac]
          · have hjbv : (j.val == b) = false := hval_ne j fb hjb
            have hjcv : (j.val == c) = false := hval_ne j fc hjc
            have habv : (a == b) = false := beq_false_of_ne (by omega)
            have hacv : (a == c) = false := beq_false_of_ne (by omega)
            simp [fa, fb, fc, hab_ne, hac_ne, hjb, hjc, hjbv, hjcv, habv, hacv]
      · by_cases hib : i = fb
        · subst hib
          by_cases hja : j = fa
          · subst hja; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, hba]
          · by_cases hjc : j = fc
            · subst hjc; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, hebc]
            · have hjav : (j.val == a) = false := hval_ne j fa hja
              have hjcv : (j.val == c) = false := hval_ne j fc hjc
              have hbav : (b == a) = false := beq_false_of_ne (by omega)
              have hbcv : (b == c) = false := beq_false_of_ne (by omega)
              simp [fa, fb, fc, hab_ne.symm, hbc_ne, hja, hjc, hjav, hjcv, hbav, hbcv]
        · by_cases hic : i = fc
          · subst hic
            by_cases hja : j = fa
            · subst hja; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, hca]
            · by_cases hjb : j = fb
              · subst hjb; simp [fa, fb, fc, hab_ne, hbc_ne, hac_ne, hab_ne.symm, hbc_ne.symm, hac_ne.symm, hcb]
              · have hjav : (j.val == a) = false := hval_ne j fa hja
                have hjbv : (j.val == b) = false := hval_ne j fb hjb
                have hcav : (c == a) = false := beq_false_of_ne (by omega)
                have hcbv : (c == b) = false := beq_false_of_ne (by omega)
                simp [fa, fb, fc, hac_ne.symm, hbc_ne.symm, hja, hjb, hjav, hjbv, hcav, hcbv]
          · have hiav : (i.val == a) = false := hval_ne i fa hia
            have hibv : (i.val == b) = false := hval_ne i fb hib
            have hicv : (i.val == c) = false := hval_ne i fc hic
            simp [hia, hib, hic, hiav, hibv, hicv]
    have htri_val : triSum a b c =
        2 * (wEdge56c cert.s64 a b * x fa * x fb +
             wEdge56c cert.s64 b c * x fb * x fc +
             wEdge56c cert.s64 a c * x fa * x fc) := by
      simp only [triSum]
      simp_rw [hterm_eq, Finset.sum_add_distrib]
      have hsingle : ∀ (p q : Fin 56) (v : ℤ),
          (∑ i : Fin 56, ∑ j : Fin 56, if i = p ∧ j = q then v else 0) = v := fun p q v => by
        have h1 : ∀ i : Fin 56, (∑ j : Fin 56, if i = p ∧ j = q then v else 0) = if i = p then v else 0 :=
          fun i => by by_cases h : i = p <;> simp [h]
        simp_rw [h1]; simp
      rw [hsingle, hsingle, hsingle, hsingle, hsingle, hsingle,
          wEdge56c_symm cert.s64 fa fb, wEdge56c_symm cert.s64 fb fc, wEdge56c_symm cert.s64 fa fc]
      ring
    rw [htri_val]
    have hw_pm1 : ∀ u v : Fin 56, isEdge56b u.val v.val = true →
        wEdge56c cert.s64 u.val v.val * x u * x v = 1 ∨
        wEdge56c cert.s64 u.val v.val * x u * x v = -1 := fun u v huv => by
      rw [wEdge56c_eq_frust_sgn cert.s64 hres huv]
      have ⟨hne, _⟩ := (isEdge56b_iff u v).mp huv
      have hu0 : dec4 (B56_pt u) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB u)).1).1).1
      have hv0 : dec4 (B56_pt v) ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (B56_pt_mem_SB v)).1).1).1
      have huv0 : dec4 (B56_pt u) + dec4 (B56_pt v) ≠ 0 := fun h => hne (by
        have := congr_arg (dec4 (B56_pt u) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
      have hmul_pm1 : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b = 1 ∨ a * b = -1 := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> decide
      exact hmul_pm1 _ _ (hmul_pm1 _ _ (hmul_pm1 _ _
        (gammaSgn_eq_pm1 (dec4 (B56_pt u)) (dec4 (B56_pt v)))
        (hs4.2 _ hu0)) (hs4.2 _ hv0)) (hs4.2 _ huv0)
    set u := wEdge56c cert.s64 fa.val fb.val * x fa * x fb
    set v := wEdge56c cert.s64 fb.val fc.val * x fb * x fc
    set w := wEdge56c cert.s64 fa.val fc.val * x fa * x fc
    have huvw : u * v * w = -1 := by
      calc u * v * w = (wEdge56c cert.s64 a b * wEdge56c cert.s64 b c * wEdge56c cert.s64 a c) *
              (x fa * x fa) * (x fb * x fb) * (x fc * x fc) := by dsimp [u, v, w, fa, fb, fc]; ring
        _ = -1 * 1 * 1 * 1 := by rw [hwprod, hxsq fa, hxsq fb, hxsq fc]
        _ = -1 := by norm_num
    change 2 * (u + v + w) ≤ 2
    rcases hw_pm1 fa fb heab with hu | hu <;>
    rcases hw_pm1 fb fc hebc with hv | hv <;>
    rcases hw_pm1 fa fc heac with hw | hw
    · dsimp only [u, v, w] at huvw; rw [hu, hv, hw] at huvw; norm_num at huvw
    all_goals (dsimp only [u, v, w]; omega)
  have hbeta_le : cert.betas.foldl (fun s (a, b, c, val) => s + (val : ℤ) * triSum a b c) 0 ≤
      cert.betas.foldl (fun acc (_, _, _, val) => acc + 2 * (val : ℤ)) 0 := by
    have hgen : ∀ (L : List (Nat × Nat × Nat × Nat)) (a1 a2 : ℤ), a1 ≤ a2 →
        checkBetas cert.s64 L = true →
        L.foldl (fun s (a, b, c, val) => s + (val : ℤ) * triSum a b c) a1 ≤
        L.foldl (fun acc (_, _, _, val) => acc + 2 * (val : ℤ)) a2 := by
      intro L; induction L with
      | nil => intro _ _ h _; exact h
      | cons t rest ih =>
        intro a1 a2 hle hok
        rcases t with ⟨a, b, c, val⟩
        simp only [checkBetas, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
        rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨hab, hbc⟩, hc56⟩, _⟩, heab⟩, hebc⟩, heac⟩, hwp⟩, hrest⟩
        simp only [List.foldl_cons]
        refine ih _ _ ?_ hrest
        have ht := htri_le a b c hab hbc hc56 heab hebc heac hwp
        have hmul := mul_le_mul_of_nonneg_left ht (Int.natCast_nonneg val)
        linarith
    exact hgen cert.betas 0 0 le_rfl hbetas
  -- 5. Combine `hquad_nn`, `hQ_expand`, `halpha_le`, `hbeta_le`, `hlin_lt` to get `Wtot < 256 + 4 * fA0`
  have hWtot_lt : Wtot < 256 + 4 * (cert.fA0 : ℤ) := by
    have hcomb : (cert.S : ℤ) * Wtot ≤ computeLinI cert + 56 * (cert.mu : ℤ) := by
      unfold computeLinI; linarith
    have hSlt : (cert.S : ℤ) * Wtot < (cert.S : ℤ) * (256 + 4 * (cert.fA0 : ℤ)) := by linarith
    nlinarith
  -- 6. Connect `Wtot` to `frustPairs (Qminus c0_88) s4` via `frustPairs_AB_split` and `6 ∣`
  have hQ_closed : ∀ p ∈ Qminus c0_88, ∀ q ∈ Qminus c0_88, p ≠ q → symp p q = 0 →
      p + q ∈ Qminus c0_88 := by
    intro p hp q hq hne hsp
    simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
    exact ⟨fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm),
      by rw [quadForm_add, hp.2, hq.2, hsp]; simp⟩
  have hsplitQ := frustPairs_AB_split (Finset.Subset.refl _) hQ_closed s4
  dsimp only at hsplitQ
  have hWtot_eq := sum_wEdge56_total cert.s64 hs4 hres
  dsimp only at hWtot_eq
  change Wtot = _ at hWtot_eq
  have hdvd : 6 ∣ frustPairs (Qminus c0_88) s4 :=
    dvd_six_frustPairs (Qminus c0_88) (by simp [Qminus, nzPts]) hQ_closed s4
  obtain ⟨fQ, hfQ⟩ := hdvd
  have hSA_eq : (Qminus c0_88).filter (fun p => symp c0_88 p = 0) = slicePts c0_88 c0_88 := rfl
  rw [hSA_eq, hfA0_pairs] at hsplitQ
  omega

/-- **Orbit-Hit Reduction to `CD(Q⁻(7,2)) ≥ 315`**:
    If `restrictA s4` maps under a 3-qubit transvection word `us` to a sign assignment with the
    same `W(5,2)` line frustrations as a passing `Cert56`, then `frustPairs (Qminus c0_88) s4 ≥ 315 * 6`! -/
theorem cd315_of_hits_cert (cert : Cert56) (hcert : checkCert56 cert = true)
    {s4 : PauliIdx 4 → ℤ} (hs4 : IsSignAssign s4)
    (hmin : ∀ po ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) s4 ≤ frustPairs (slicePts c0_88 po) s4)
    (us : List (PauliIdx 3))
    (heq : ∀ a b : PauliIdx 3, a ≠ 0 → b ≠ 0 → a ≠ b → symp a b = 0 →
      applyTransvWord us (restrictA s4) a * applyTransvWord us (restrictA s4) b *
        applyTransvWord us (restrictA s4) (a + b) =
      listToSign3 cert.s64 a * listToSign3 cert.s64 b * listToSign3 cert.s64 (a + b)) :
    315 * 6 ≤ frustPairs (Qminus c0_88) s4 := by
  have hcert' := hcert
  unfold checkCert56 at hcert'
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert'
  have hs3_cert : IsSignAssign (listToSign3 cert.s64) :=
    listToSign3_isSignAssign hcert'.1.1.1.1.1.1.1.1.1.1.2 hcert'.1.1.1.1.1.1.1.1.1.2
  let s4' := liftTransv3Word us s4
  have hs4' : IsSignAssign s4' := liftTransv3Word_isSignAssign us hs4
  have hmin' := liftTransv3Word_preserves_minSlice us hmin
  have hres' : restrictA s4' = applyTransvWord us (restrictA s4) := liftTransv3Word_restrictA us s4
  have hs3' : IsSignAssign (restrictA s4') := by
    rw [hres']; exact applyTransvWord_isSignAssign us (restrictA_isSignAssign hs4)
  have heq' : ∀ a b : PauliIdx 3, a ≠ 0 → b ≠ 0 → a ≠ b → symp a b = 0 →
      restrictA s4' a * restrictA s4' b * restrictA s4' (a + b) =
      listToSign3 cert.s64 a * listToSign3 cert.s64 b * listToSign3 cert.s64 (a + b) := by
    rw [hres']; exact heq
  obtain ⟨G, hG⟩ := w5_frust_eq_implies_gauge4 hs3' hs3_cert heq'
  let s4'' := applyGauge G s4'
  have hs4'' : IsSignAssign s4'' := applyGauge_isSignAssign G hs4'
  have hmin'' : ∀ po ∈ outPts c0_88,
      frustPairs (slicePts c0_88 c0_88) s4'' ≤ frustPairs (slicePts c0_88 po) s4'' := by
    intro po hpo
    rw [frustPairs_applyGauge, frustPairs_applyGauge]
    exact hmin' po hpo
  have hres'' : restrictA s4'' = listToSign3 cert.s64 := hG s4' rfl
  have h315 := sound_checkCert56 cert hcert hs4'' hmin'' hres''
  rw [frustPairs_applyGauge, liftTransv3Word_preserves_Qminus] at h315
  exact h315

end CertSoundness

end FourQubitCD

end MultiQubitMUB
