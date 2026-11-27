import MultiQubitMUB.GeneralLowerBound

/-!
# 4-Qubit Pauli Contextuality Core: Symplectic Transvections, Double Counting & `W(5,2)` Lift

Establishes the exact algebraic and combinatorial infrastructure reducing the 4-qubit Pauli
contextuality bound `signCubeSum 4 σ ≤ 6615` (`CD(W(7,2)) ≥ 1575`) to the canonical minimal-slice
classification on `Q⁻(7,2) = Q(6,2) ⊔ B₅₆`, `W(5,2)`, and `Q⁻(5,2)`.
-/

namespace MultiQubitMUB

namespace FourQubitCD

set_option linter.constructorNameAsVariable false

/-! ### Section 1: Computable Bit-Level `Fin 256` & `Fin 64` Operations (Zero `Classical`!) -/

def pop4 (x : Nat) : Nat :=
  (x &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1) + ((x >>> 3) &&& 1)

def dot2_4 (a b : Nat) : Nat := pop4 (a &&& b) &&& 1
def symp4 (p q : Nat) : Nat := dot2_4 (p >>> 4) (q &&& 15) ^^^ dot2_4 (p &&& 15) (q >>> 4)
def Q4_0 (p : Nat) : Nat := dot2_4 (p >>> 4) (p &&& 15)
def Q4_form (c p : Nat) : Nat := Q4_0 p ^^^ symp4 c p
def gamma4_bit (p q : Nat) : Nat := ((Q4_0 p &&& Q4_0 q) ^^^ dot2_4 (p >>> 4) (q &&& 15)) &&& 1
def gamma4_sgn (p q : Nat) : ℤ := if gamma4_bit p q == 0 then 1 else -1
def transv4_pt (u v : Nat) : Nat := if symp4 u v == 0 then v else v ^^^ u
def transv4_bit (u v : Nat) : Nat :=
  if symp4 u v == 0 then 0 else ((Q4_0 u ||| Q4_0 v) ^^^ dot2_4 (u >>> 4) (v &&& 15)) &&& 1
def transv4_sgn (u v : Nat) : ℤ := if transv4_bit u v == 0 then 1 else -1

def pop3 (x : Nat) : Nat :=
  (x &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1)

def dot2_3 (a b : Nat) : Nat := pop3 (a &&& b) &&& 1
def symp3 (p q : Nat) : Nat := dot2_3 (p >>> 3) (q &&& 7) ^^^ dot2_3 (p &&& 7) (q >>> 3)
def Q3_0 (p : Nat) : Nat := dot2_3 (p >>> 3) (p &&& 7)
def Q3_form (c p : Nat) : Nat := Q3_0 p ^^^ symp3 c p
def gamma3_bit (p q : Nat) : Nat := ((Q3_0 p &&& Q3_0 q) ^^^ dot2_3 (p >>> 3) (q &&& 7)) &&& 1
def gamma3_sgn (p q : Nat) : ℤ := if gamma3_bit p q == 0 then 1 else -1
def transv3_pt (u v : Nat) : Nat := if symp3 u v == 0 then v else v ^^^ u
def transv3_bit (u v : Nat) : Nat :=
  if symp3 u v == 0 then 0 else ((Q3_0 u ||| Q3_0 v) ^^^ dot2_3 (u >>> 3) (v &&& 7)) &&& 1
def transv3_sgn (u v : Nat) : ℤ := if transv3_bit u v == 0 then 1 else -1

/-- Canonical coordinate lift `W(5,2) → 𝔽₂⁸` (zeroing qubit 3). -/
def lift34Nat (p3 : Nat) : Nat := ((p3 >>> 3) <<< 4) ||| (p3 &&& 7)

/-- Canonical cocycle-preserving isomorphism `W(5,2) ≃ Q_{0x88}⁻ ∩ 0x88^⊥`. -/
def ApauliNat (p3 : Nat) : Nat :=
  lift34Nat p3 ^^^ (if Q3_0 p3 == 1 then 136 else 0)

def proj43Nat (p4 : Nat) : Nat :=
  (((p4 >>> 4) &&& 7) <<< 3) ||| (p4 &&& 7)

private lemma lift34Nat_lt (p3 : Nat) (hp : p3 < 64) : lift34Nat p3 < 256 := by
  have h1 : (p3 >>> 3) <<< 4 < 256 := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]; norm_num; omega
  have h2 : p3 &&& 7 < 256 := by
    rw [Nat.and_two_pow_sub_one_eq_mod p3 3]; norm_num; omega
  exact Nat.or_lt_two_pow (n := 8) h1 h2

private lemma ApauliNat_lt (p3 : Nat) (hp : p3 < 64) : ApauliNat p3 < 256 := by
  unfold ApauliNat
  have h1 := lift34Nat_lt p3 hp
  split_ifs
  · exact Nat.xor_lt_two_pow (n := 8) h1 (by omega)
  · simpa using h1

private lemma proj43Nat_lt (p4 : Nat) : proj43Nat p4 < 64 := by
  have h1 : ((p4 >>> 4) &&& 7) <<< 3 < 64 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 3, Nat.shiftLeft_eq]; norm_num; omega
  have h2 : p4 &&& 7 < 64 := by
    rw [Nat.and_two_pow_sub_one_eq_mod p4 3]; norm_num; omega
  exact Nat.or_lt_two_pow (n := 6) h1 h2

def ApauliFin (p3 : Fin 64) : Fin 256 := ⟨ApauliNat p3.val, ApauliNat_lt p3.val p3.isLt⟩
def proj43Fin (p4 : Fin 256) : Fin 64 := ⟨proj43Nat p4.val, proj43Nat_lt p4.val⟩
def lift34Fin (p3 : Fin 64) : Fin 256 := ⟨lift34Nat p3.val, lift34Nat_lt p3.val p3.isLt⟩

private def checkApauliAll : Nat → Bool
  | 0 => true
  | n + 1 =>
    let a := ApauliNat n
    let ok :=
      (if n == 0 then true else a != 0) &&
      (Q4_form 136 a == 0) &&
      (symp4 136 a == 0) &&
      (proj43Nat a == n) &&
      (symp4 128 a == Q3_0 n)
    ok && checkApauliAll n

private lemma checkApauliAll_ok : checkApauliAll 64 = true := by rfl

private lemma checkApauliAll_sound : ∀ m n, n < m → checkApauliAll m = true →
    (n ≠ 0 → ApauliNat n ≠ 0) ∧
    Q4_form 136 (ApauliNat n) = 0 ∧
    symp4 136 (ApauliNat n) = 0 ∧
    proj43Nat (ApauliNat n) = n ∧
    symp4 128 (ApauliNat n) = Q3_0 n := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn hok
    simp only [checkApauliAll, Bool.and_eq_true] at hok
    by_cases hnm : n = m
    · subst hnm
      rcases hok.1 with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
      refine ⟨fun hne => ?_, by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
      have hb : (n == 0) = false := beq_false_of_ne hne
      simp only [hb, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq] at h0
      exact h0
    · exact ih n (by omega) hok.2

lemma ApauliFin_props (p3 : Fin 64) :
    (p3.val ≠ 0 → ApauliFin p3 ≠ ⟨0, by decide⟩) ∧
    Q4_form 136 (ApauliFin p3).val = 0 ∧
    symp4 136 (ApauliFin p3).val = 0 ∧
    proj43Fin (ApauliFin p3) = p3 ∧
    symp4 128 (ApauliFin p3).val = Q3_0 p3.val := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := checkApauliAll_sound 64 p3.val p3.isLt checkApauliAll_ok
  exact ⟨fun hne h => h0 hne (congr_arg Fin.val h), h1, h2, Fin.ext h3, h4⟩

private def checkBijSlice : Nat → Bool
  | 0 => true
  | n + 1 =>
    let ok := if Q4_form 136 n == 0 && symp4 136 n == 0 then ApauliNat (proj43Nat n) == n else true
    ok && checkBijSlice n

set_option maxRecDepth 4096 in
private lemma checkBijSlice_ok : checkBijSlice 256 = true := by rfl

private lemma checkBijSlice_sound : ∀ m n, n < m → checkBijSlice m = true →
    Q4_form 136 n = 0 → symp4 136 n = 0 → ApauliNat (proj43Nat n) = n := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn hok hq hs
    simp only [checkBijSlice, Bool.and_eq_true] at hok
    by_cases hnm : n = m
    · subst hnm
      have h1 := hok.1
      rw [hq, hs] at h1
      simpa using h1
    · exact ih n (by omega) hok.2 hq hs

lemma ApauliFin_bij_slice (p4 : Fin 256) (hq : Q4_form 136 p4.val = 0)
    (hs : symp4 136 p4.val = 0) : ApauliFin (proj43Fin p4) = p4 :=
  Fin.ext (checkBijSlice_sound 256 p4.val p4.isLt checkBijSlice_ok hq hs)

private def checkBasisSymp3 : Nat → Bool
  | 0 => true
  | n + 1 =>
    let ok :=
      (symp3 n 1 == ((n >>> 3) &&& 1)) &&
      (symp3 n 2 == ((n >>> 4) &&& 1)) &&
      (symp3 n 4 == ((n >>> 5) &&& 1)) &&
      (symp3 n 8 == (n &&& 1)) &&
      (symp3 n 16 == ((n >>> 1) &&& 1)) &&
      (symp3 n 32 == ((n >>> 2) &&& 1))
    ok && checkBasisSymp3 n

private lemma checkBasisSymp3_ok : checkBasisSymp3 64 = true := by rfl

private lemma checkBasisSymp3_sound : ∀ m n, n < m → checkBasisSymp3 m = true →
    symp3 n 1 = ((n >>> 3) &&& 1) ∧ symp3 n 2 = ((n >>> 4) &&& 1) ∧
    symp3 n 4 = ((n >>> 5) &&& 1) ∧ symp3 n 8 = (n &&& 1) ∧
    symp3 n 16 = ((n >>> 1) &&& 1) ∧ symp3 n 32 = ((n >>> 2) &&& 1) := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn hok
    simp only [checkBasisSymp3, Bool.and_eq_true] at hok
    by_cases hnm : n = m
    · subst hnm
      rcases hok.1 with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3,
             by simpa using h4, by simpa using h5, by simpa using h6⟩
    · exact ih n (by omega) hok.2

private def checkPoutOne (po : Nat) : Bool :=
  if Q4_form 136 po != 1 then true
  else if po == 136 then true
  else if Q4_form 136 (po ^^^ 136) == 1 && transv4_pt (po ^^^ 136) po == 136 then true
  else ([128, 129, 130, 132] : List Nat).any fun u =>
    let po1 := po ^^^ u
    Q4_form 136 u == 1 && symp4 u po == 1 &&
    Q4_form 136 (po1 ^^^ 136) == 1 && transv4_pt (po1 ^^^ 136) po1 == 136

private def checkPoutAll : Nat → Bool
  | 0 => true
  | n + 1 => checkPoutOne n && checkPoutAll n

set_option maxRecDepth 4096 in
private lemma checkPoutAll_ok : checkPoutAll 256 = true := by rfl

private def checkLift34Val : Nat → Bool
  | 0 => true
  | n + 1 => (lift34Nat n == (n / 8) * 16 + n % 8) && checkLift34Val n

private lemma checkLift34Val_ok : checkLift34Val 64 = true := by rfl

private lemma lift34Nat_val_eq (p3 : Nat) (hp : p3 < 64) :
    lift34Nat p3 = (p3 / 8) * 16 + p3 % 8 := by
  have hsound : ∀ m n, n < m → checkLift34Val m = true → lift34Nat n = (n / 8) * 16 + n % 8 := by
    intro m
    induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn hok
      simp only [checkLift34Val, Bool.and_eq_true, beq_iff_eq] at hok
      by_cases hnm : n = m
      · subst hnm; exact hok.1
      · exact ih n (by omega) hok.2
  exact hsound 64 p3 hp checkLift34Val_ok

private lemma checkPoutAll_sound : ∀ m n, n < m → checkPoutAll m = true → checkPoutOne n = true := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn hok
    simp only [checkPoutAll, Bool.and_eq_true] at hok
    by_cases hnm : n = m
    · subst hnm; exact hok.1
    · exact ih n (by omega) hok.2

private lemma pout_exists_transv_to_88 (po : Fin 256) (hpo : Q4_form 136 po.val = 1) :
    po.val = 136 ∨
    (Q4_form 136 (po.val ^^^ 136) = 1 ∧ transv4_pt (po.val ^^^ 136) po.val = 136) ∨
    ∃ u ∈ ([128, 129, 130, 132] : List Nat),
      Q4_form 136 u = 1 ∧ symp4 u po.val = 1 ∧
      let po1 := po.val ^^^ u
      Q4_form 136 (po1 ^^^ 136) = 1 ∧ transv4_pt (po1 ^^^ 136) po1 = 136 := by
  have h := checkPoutAll_sound 256 po.val po.isLt checkPoutAll_ok
  unfold checkPoutOne at h
  simp only [hpo, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h with h1 h2
  · left; exact beq_iff_eq.mp h1
  · right; left
    simp only [Bool.and_eq_true, beq_iff_eq] at h2; exact h2
  · right; right
    rw [List.any_eq_true] at h
    obtain ⟨u, huMem, huOk⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at huOk
    exact ⟨u, huMem, huOk.1.1.1, huOk.1.1.2, huOk.1.2, huOk.2⟩

private def commReachStep (known : List Nat) : List Nat :=
  (List.range 64).filter fun c =>
    c != 0 && (known.contains c ||
      known.any fun a =>
        let b := a ^^^ c
        b != 0 && b != a && symp3 a b == 0 && known.contains b)

private def commReachN : Nat → List Nat → List Nat
  | 0, k => k
  | n + 1, k => commReachN n (commReachStep k)

private def checkCommReachAll : Nat → Bool
  | 0 => true
  | n + 1 =>
    (if n == 0 then true else (commReachN 4 [1, 2, 4, 8, 16, 32, 9]).contains n) &&
    checkCommReachAll n

private lemma checkCommReachAll_ok : checkCommReachAll 64 = true := by rfl

private lemma mem_commReach_all (v : Fin 64) (hv : v.val ≠ 0) :
    (commReachN 4 [1, 2, 4, 8, 16, 32, 9]).contains v.val = true := by
  have hsound : ∀ m n, n < m → checkCommReachAll m = true → n ≠ 0 →
      (commReachN 4 [1, 2, 4, 8, 16, 32, 9]).contains n = true := by
    intro m
    induction m with
    | zero => intro n hn; omega
    | succ m ih =>
      intro n hn hok hne
      simp only [checkCommReachAll, Bool.and_eq_true] at hok
      by_cases hnm : n = m
      · subst hnm
        have h1 := hok.1
        have hb : (n == 0) = false := beq_false_of_ne hne
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at h1
        exact h1
      · exact ih n (by omega) hok.2 hne
  exact hsound 64 v.val v.isLt checkCommReachAll_ok hv

/-! ### Section 2: Universal `PauliIdx n` Cocycle, Transvections & Double Counting (`Classical`) -/

section PauliIdxSection

open scoped Classical

/-- Commuting Pauli product phase bit `γ(p, q) = Q₀(p) Q₀(q) + p_x · q_z ∈ ZMod 2`. -/
def gammaBit {n : ℕ} (p q : PauliIdx n) : ZMod 2 :=
  quadForm0 p * quadForm0 q + dot p.1 q.2

/-- Commuting Pauli product sign `(-1)^{γ(p, q)} ∈ {-1, 1}`. -/
def gammaSgn {n : ℕ} (p q : PauliIdx n) : ℤ :=
  if gammaBit p q = 0 then 1 else -1

lemma gammaSgn_eq_pm1 {n : ℕ} (p q : PauliIdx n) : gammaSgn p q = 1 ∨ gammaSgn p q = -1 := by
  unfold gammaSgn; split_ifs <;> simp

lemma gammaSgn_sq {n : ℕ} (p q : PauliIdx n) : gammaSgn p q * gammaSgn p q = 1 := by
  rcases gammaSgn_eq_pm1 p q with h | h <;> rw [h] <;> norm_num

private lemma zmod2_sq (x : ZMod 2) : x * x = x := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_two_mul (x : ZMod 2) : 2 * x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_mul_two (x : ZMod 2) : x * 2 = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma sympSign_zero_left' {n : ℕ} (q : PauliIdx n) : sympSign 0 q = 1 := by
  simp [sympSign, symp_zero_left]

/-- Exact agreement between `(pauliPhase p q).re` and `gammaSgn p q` on commuting pairs. -/
lemma pauliPhase_re_eq_gammaSgn {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    (pauliPhase p q).re = (gammaSgn p q : ℝ) := by
  have hdot : dot (p + q).1 (p + q).2 = dot p.1 p.2 + dot q.1 q.2 := by
    have h := quadForm0_add p q
    simp only [quadForm0] at h
    rw [h, hs, add_zero]
  have hchi : chi q.2 p.1 = if dot p.1 q.2 = 0 then 1 else -1 := by
    simp only [chi, dot_comm q.2 p.1]
  simp only [pauliPhase, pauliPh, hdot, hchi, gammaSgn, gammaBit, quadForm0]
  rcases zmod2_cases (dot p.1 p.2) with h1 | h1 <;>
  rcases zmod2_cases (dot q.1 q.2) with h2 | h2 <;>
  rcases zmod2_cases (dot p.1 q.2) with h3 | h3 <;>
  simp [h1, h2, h3, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]

lemma gammaBit_comm {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    gammaBit p q = gammaBit q p := by
  have hd : dot p.1 q.2 = dot q.1 p.2 := by
    simp only [symp, dot_comm p.2 q.1] at hs
    rcases zmod2_cases (dot p.1 q.2) with h1 | h1 <;>
    rcases zmod2_cases (dot q.1 p.2) with h2 | h2 <;> simp_all
    all_goals exact absurd hs (by decide)
  simp only [gammaBit, mul_comm (quadForm0 p), hd]

lemma gammaSgn_comm {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    gammaSgn p q = gammaSgn q p := by
  simp only [gammaSgn, gammaBit_comm hs]

lemma gammaBit_add_left {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    gammaBit (p + q) q = gammaBit p q := by
  simp only [gammaBit, quadForm0_add, hs, add_zero, Prod.fst_add, dot_add_left]
  change (quadForm0 p + quadForm0 q) * quadForm0 q + (dot p.1 q.2 + quadForm0 q) =
    quadForm0 p * quadForm0 q + dot p.1 q.2
  rw [add_mul, zmod2_sq]
  have h : quadForm0 p * quadForm0 q + quadForm0 q + (dot p.1 q.2 + quadForm0 q) =
      quadForm0 p * quadForm0 q + dot p.1 q.2 + (quadForm0 q + quadForm0 q) := by ring
  rw [h, zmod2_add_self, add_zero]

lemma gammaSgn_add_left {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    gammaSgn (p + q) q = gammaSgn p q := by
  simp only [gammaSgn, gammaBit_add_left hs]

lemma gammaSgn_add_right {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    gammaSgn p (p + q) = gammaSgn p q := by
  have hs' : symp p (p + q) = 0 := by rw [symp_add_right, symp_self, hs, add_zero]
  rw [gammaSgn_comm hs', add_comm p q, gammaSgn_add_left (by rwa [symp_comm]), gammaSgn_comm hs]

/-- Symplectic transvection `T_u(v) = v + ω(u, v) u`. -/
def transvPt {n : ℕ} (u v : PauliIdx n) : PauliIdx n :=
  if symp u v = 0 then v else v + u

/-- Clifford transvection sign bit (for `U_u = (I + i P_u)/√2`). -/
def transvBit {n : ℕ} (u v : PauliIdx n) : ZMod 2 :=
  if symp u v = 0 then 0
  else quadForm0 u + quadForm0 v + quadForm0 u * quadForm0 v + dot u.1 v.2

/-- Clifford transvection sign `(-1)^{transvBit u v} ∈ {-1, 1}`. -/
def transvSgn {n : ℕ} (u v : PauliIdx n) : ℤ :=
  if transvBit u v = 0 then 1 else -1

lemma transvSgn_eq_pm1 {n : ℕ} (u v : PauliIdx n) : transvSgn u v = 1 ∨ transvSgn u v = -1 := by
  unfold transvSgn; split_ifs <;> simp

lemma transvPt_zero {n : ℕ} (u : PauliIdx n) : transvPt u 0 = 0 := by
  simp [transvPt, symp_zero_right]

lemma transvPt_invol {n : ℕ} (u v : PauliIdx n) : transvPt u (transvPt u v) = v := by
  unfold transvPt
  by_cases h : symp u v = 0
  · simp [h]
  · have h' : symp u (v + u) ≠ 0 := by rwa [symp_add_right, symp_self, add_zero]
    simp [h, h', pauliIdx_add_cancel_right]

lemma transvPt_add {n : ℕ} (u p q : PauliIdx n) :
    transvPt u (p + q) = transvPt u p + transvPt u q := by
  unfold transvPt
  rcases zmod2_cases (symp u p) with hp | hp <;> rcases zmod2_cases (symp u q) with hq | hq
  · simp [symp_add_right, hp, hq]
  · simp [symp_add_right, hp, hq, add_assoc]
  · simp [symp_add_right, hp, hq, show (1 : ZMod 2) ≠ 0 by decide]; abel
  · simp only [symp_add_right, hp, hq, show (1 : ZMod 2) + 1 = 0 by decide,
      show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
    calc p + q = p + q + (u + u) := by rw [pauliIdx_add_self, add_zero]
      _ = (p + u) + (q + u) := by abel

lemma symp_transvPt {n : ℕ} (u p q : PauliIdx n) :
    symp (transvPt u p) (transvPt u q) = symp p q := by
  unfold transvPt
  rcases zmod2_cases (symp u p) with hp | hp <;> rcases zmod2_cases (symp u q) with hq | hq
  · simp [hp, hq]
  · simp [hp, hq, symp_add_right, show symp p u = 0 by rw [symp_comm]; exact hp]
  · simp [hp, hq, symp_add_left]
  · simp only [hp, hq, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte,
      symp_add_left, symp_add_right, symp_self, add_zero]
    rw [symp_comm p u, hp]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    calc symp p q + 1 + 1 = symp p q + (1 + 1) := by ring
      _ = symp p q := by rw [this, add_zero]

lemma quadForm_transvPt {n : ℕ} (c u p : PauliIdx n) :
    quadForm c (transvPt u p) =
      if quadForm c u = 1 then quadForm c p else quadForm (c + u) p := by
  unfold transvPt
  have h1ne0 : (1 : ZMod 2) ≠ 0 := by decide
  have h0ne1 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (symp u p) with hp | hp <;> rcases zmod2_cases (quadForm c u) with hu | hu
  · simp only [hp, hu, h0ne1, ↓reduceIte]; simp only [quadForm, symp_add_left, hp, add_zero]
  · simp only [hp, hu, ↓reduceIte]
  · simp only [hp, hu, h1ne0, h0ne1, ↓reduceIte, quadForm_add]
    rw [symp_comm p u, hp]
    simp only [quadForm, symp_add_left, hp]
    ring
  · simp only [hp, hu, h1ne0, ↓reduceIte, quadForm_add]
    rw [symp_comm p u, hp]
    calc quadForm c p + 1 + 1 = quadForm c p + (1 + 1) := by ring
      _ = quadForm c p := by rw [h11, add_zero]

lemma quadForm_transvPt_fix {n : ℕ} {c u : PauliIdx n} (hu : quadForm c u = 1) (p : PauliIdx n) :
    quadForm c (transvPt u p) = quadForm c p := by
  rw [quadForm_transvPt, if_pos hu]

lemma quadForm_transvPt_move {n : ℕ} {c u : PauliIdx n} (hu : quadForm c u = 0) (p : PauliIdx n) :
    quadForm c (transvPt u p) = quadForm (c + u) p := by
  rw [quadForm_transvPt, if_neg (by rw [hu]; decide)]

/-- Universal `ZMod 2` Clifford transvection cocycle identity (all `n`, all commuting `p, q`). -/
lemma transvBit_cocycle {n : ℕ} (u p q : PauliIdx n) (hs : symp p q = 0) :
    transvBit u p + transvBit u q + transvBit u (p + q) +
      gammaBit (transvPt u p) (transvPt u q) = gammaBit p q := by
  have h1ne0 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (symp u p) with hp | hp <;> rcases zmod2_cases (symp u q) with hq | hq
  · simp [transvBit, transvPt, symp_add_right, hp, hq]
  · have hcomm1 : gammaBit (transvPt u p) (transvPt u q) = gammaBit (transvPt u q) (transvPt u p) :=
      gammaBit_comm (by rw [symp_transvPt, hs])
    have hcomm2 : gammaBit p q = gammaBit q p := gammaBit_comm hs
    rw [hcomm1, hcomm2, add_comm p q]
    have hspq : symp u (q + p) = 1 := by rw [symp_add_right, hq, hp, add_zero]
    have hsqp : symp q p = 0 := by rw [symp_comm, hs]
    simp only [transvBit, transvPt, hp, hq, hspq, h1ne0, ↓reduceIte,
      gammaBit, quadForm0_add, hsqp, add_zero, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
    rw [symp_comm q u, hq]
    ring_nf
    simp [zmod2_two_mul, zmod2_mul_two]
  · have hspq : symp u (p + q) = 1 := by rw [symp_add_right, hp, hq, add_zero]
    simp only [transvBit, transvPt, hp, hq, hspq, h1ne0, ↓reduceIte,
      gammaBit, quadForm0_add, hs, add_zero, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
    rw [symp_comm p u, hp]
    ring_nf
    simp [zmod2_two_mul, zmod2_mul_two]
  · have hspq : symp u (p + q) = 0 := by rw [symp_add_right, hp, hq, h11]
    have hsymp_pu : dot p.1 u.2 + dot u.1 p.2 = 1 := by
      have := hp; simp only [symp, dot_comm u.2 p.1] at this; rw [add_comm] at this; exact this
    simp only [transvBit, transvPt, hp, hq, hspq, h1ne0, ↓reduceIte,
      gammaBit, quadForm0_add, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right]
    rw [symp_comm p u, hp, symp_comm q u, hq]
    have hsq := zmod2_sq (quadForm0 u)
    have hdu : dot u.1 u.2 = quadForm0 u := rfl
    rw [hdu]
    have hgoal :
        quadForm0 u + quadForm0 p + quadForm0 u * quadForm0 p + dot u.1 p.2 +
          (quadForm0 u + quadForm0 q + quadForm0 u * quadForm0 q + dot u.1 q.2) + 0 +
          ((quadForm0 p + quadForm0 u + 1) * (quadForm0 q + quadForm0 u + 1) +
            (dot p.1 q.2 + dot u.1 q.2 + (dot p.1 u.2 + quadForm0 u))) =
        quadForm0 p * quadForm0 q + dot p.1 q.2 +
          (quadForm0 u * quadForm0 u + quadForm0 u) +
          ((dot p.1 u.2 + dot u.1 p.2) + 1) +
          2 * (quadForm0 u + quadForm0 p + quadForm0 q +
               quadForm0 u * quadForm0 p + quadForm0 u * quadForm0 q +
               quadForm0 u + dot u.1 q.2) := by ring
    rw [hgoal, hsq, hsymp_pu, zmod2_add_self, h11, zmod2_two_mul]; ring

private lemma sign_zmod2_add (a b : ZMod 2) :
    (if a + b = 0 then (1 : ℤ) else -1) =
      (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma transvSgn_cocycle {n : ℕ} (u p q : PauliIdx n) (hs : symp p q = 0) :
    transvSgn u p * transvSgn u q * transvSgn u (p + q) *
      gammaSgn (transvPt u p) (transvPt u q) = gammaSgn p q := by
  have h := transvBit_cocycle u p q hs
  simp only [transvSgn, gammaSgn]
  rw [← h, sign_zmod2_add, sign_zmod2_add, sign_zmod2_add]

/-- A valid `{±1}` sign assignment on `PauliIdx n \ {0}` with `s 0 = 0`. -/
def IsSignAssign {n : ℕ} (s : PauliIdx n → ℤ) : Prop :=
  s 0 = 0 ∧ ∀ p : PauliIdx n, p ≠ 0 → s p = 1 ∨ s p = -1

/-- Apply a Clifford transvection `T_u` to a sign assignment `s`. -/
def applyTransv {n : ℕ} (u : PauliIdx n) (s : PauliIdx n → ℤ) : PauliIdx n → ℤ :=
  fun v => transvSgn u v * s (transvPt u v)

/-- Apply a symplectic gauge `(-1)^{ω(g, v)}` to a sign assignment `s`. -/
def applyGauge {n : ℕ} (g : PauliIdx n) (s : PauliIdx n → ℤ) : PauliIdx n → ℤ :=
  fun v => sympSign g v * s v

/-- Apply a word (list) of transvections left-to-right. -/
def applyTransvWord {n : ℕ} : List (PauliIdx n) → (PauliIdx n → ℤ) → (PauliIdx n → ℤ)
  | [], s => s
  | u :: us, s => applyTransvWord us (applyTransv u s)

lemma applyTransv_isSignAssign {n : ℕ} (u : PauliIdx n) {s : PauliIdx n → ℤ}
    (hs : IsSignAssign s) : IsSignAssign (applyTransv u s) := by
  refine ⟨by simp [applyTransv, transvPt_zero, hs.1], fun p hp => ?_⟩
  have htp : transvPt u p ≠ 0 := fun h => hp (by rw [← transvPt_invol u p, h, transvPt_zero])
  simp only [applyTransv]
  rcases transvSgn_eq_pm1 u p with h1 | h1 <;> rcases hs.2 _ htp with h2 | h2 <;>
    simp [h1, h2]

lemma applyGauge_isSignAssign {n : ℕ} (g : PauliIdx n) {s : PauliIdx n → ℤ}
    (hs : IsSignAssign s) : IsSignAssign (applyGauge g s) := by
  refine ⟨by simp [applyGauge, hs.1], fun p hp => ?_⟩
  simp only [applyGauge, sympSign]
  rcases hs.2 p hp with h2 | h2 <;> split_ifs <;> simp [h2]

lemma applyTransvWord_isSignAssign {n : ℕ} (us : List (PauliIdx n)) {s : PauliIdx n → ℤ}
    (hs : IsSignAssign s) : IsSignAssign (applyTransvWord us s) := by
  induction us generalizing s with
  | nil => exact hs
  | cons u us ih => exact ih (applyTransv_isSignAssign u hs)

lemma line_sign_applyTransv {n : ℕ} (u p q : PauliIdx n) (hs : symp p q = 0)
    (s : PauliIdx n → ℤ) :
    gammaSgn p q * applyTransv u s p * applyTransv u s q * applyTransv u s (p + q) =
      gammaSgn (transvPt u p) (transvPt u q) *
        s (transvPt u p) * s (transvPt u q) * s (transvPt u p + transvPt u q) := by
  simp only [applyTransv, transvPt_add]
  have hc := transvSgn_cocycle u p q hs
  have h1 : transvSgn u p * transvSgn u p = 1 := by
    rcases transvSgn_eq_pm1 u p with h | h <;> rw [h] <;> norm_num
  have h2 : transvSgn u q * transvSgn u q = 1 := by
    rcases transvSgn_eq_pm1 u q with h | h <;> rw [h] <;> norm_num
  have h3 : transvSgn u (p + q) * transvSgn u (p + q) = 1 := by
    rcases transvSgn_eq_pm1 u (p + q) with h | h <;> rw [h] <;> norm_num
  calc gammaSgn p q * (transvSgn u p * s (transvPt u p)) *
          (transvSgn u q * s (transvPt u q)) *
          (transvSgn u (p + q) * s (transvPt u p + transvPt u q))
      = (transvSgn u p * transvSgn u q * transvSgn u (p + q) * gammaSgn p q) *
          s (transvPt u p) * s (transvPt u q) * s (transvPt u p + transvPt u q) := by ring
    _ = (gammaSgn (transvPt u p) (transvPt u q) *
          (transvSgn u p * transvSgn u p) * (transvSgn u q * transvSgn u q) *
          (transvSgn u (p + q) * transvSgn u (p + q))) *
          s (transvPt u p) * s (transvPt u q) * s (transvPt u p + transvPt u q) := by
            rw [← hc]; ring
    _ = _ := by rw [h1, h2, h3]; ring

lemma line_sign_applyGauge {n : ℕ} (g p q : PauliIdx n) (s : PauliIdx n → ℤ) :
    gammaSgn p q * applyGauge g s p * applyGauge g s q * applyGauge g s (p + q) =
      gammaSgn p q * s p * s q * s (p + q) := by
  simp only [applyGauge, sympSign_add_right]
  have h1 : sympSign g p * sympSign g p = 1 := by simp [sympSign]; split_ifs <;> norm_num
  have h2 : sympSign g q * sympSign g q = 1 := by simp [sympSign]; split_ifs <;> norm_num
  calc gammaSgn p q * (sympSign g p * s p) * (sympSign g q * s q) *
          (sympSign g p * sympSign g q * s (p + q))
      = gammaSgn p q * s p * s q * s (p + q) *
          (sympSign g p * sympSign g p) * (sympSign g q * sympSign g q) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- Number of ordered commuting distinct frustrated pairs `(p, q) ∈ S × S`. -/
def frustPairs {n : ℕ} (S : Finset (PauliIdx n)) (s : PauliIdx n → ℤ) : ℕ :=
  ((S ×ˢ S).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1).card

lemma frustPairs_applyGauge {n : ℕ} (S : Finset (PauliIdx n)) (g : PauliIdx n)
    (s : PauliIdx n → ℤ) :
    frustPairs S (applyGauge g s) = frustPairs S s := by
  unfold frustPairs
  congr 1; ext ⟨p, q⟩
  simp [line_sign_applyGauge]

lemma frustPairs_applyTransv {n : ℕ} (u : PauliIdx n) (S T : Finset (PauliIdx n))
    (hmap : ∀ p, p ∈ S ↔ transvPt u p ∈ T) (s : PauliIdx n → ℤ) :
    frustPairs S (applyTransv u s) = frustPairs T s := by
  unfold frustPairs
  refine Finset.card_bij (fun pq _ => (transvPt u pq.1, transvPt u pq.2)) ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    rcases hpq with ⟨⟨hp, hq⟩, hne, hsymp, hfr⟩
    refine ⟨⟨(hmap p).mp hp, (hmap q).mp hq⟩, ?_, ?_, ?_⟩
    · intro heq; exact hne (by rw [← transvPt_invol u p, ← transvPt_invol u q, heq])
    · rw [symp_transvPt, hsymp]
    · rw [← line_sign_applyTransv u p q hsymp s]; exact hfr
  · rintro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by rw [← transvPt_invol u p1, ← transvPt_invol u p2, h.1])
      (by rw [← transvPt_invol u q1, ← transvPt_invol u q2, h.2])
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    rcases hab with ⟨⟨ha, hb⟩, hne, hsymp, hfr⟩
    refine ⟨(transvPt u a, transvPt u b), ?_, by simp [transvPt_invol]⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    have hs' : symp (transvPt u a) (transvPt u b) = 0 := by rw [symp_transvPt, hsymp]
    refine ⟨⟨(hmap _).mpr (by rwa [transvPt_invol]), (hmap _).mpr (by rwa [transvPt_invol])⟩,
      ?_, hs', ?_⟩
    · intro heq; exact hne (by rw [← transvPt_invol u a, ← transvPt_invol u b, heq])
    · rw [line_sign_applyTransv u _ _ hs' s, transvPt_invol, transvPt_invol]; exact hfr

/-- Every commuting-closed subset `S` without `0` has `6 ∣ frustPairs S s` (6 ordered pairs per line). -/
lemma dvd_six_frustPairs {n : ℕ} (S : Finset (PauliIdx n)) (h0 : (0 : PauliIdx n) ∉ S)
    (hclosed : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → symp p q = 0 → p + q ∈ S)
    (s : PauliIdx n → ℤ) : 6 ∣ frustPairs S s := by
  let P := (S ×ˢ S).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1
  let f : PauliIdx n × PauliIdx n → Finset (PauliIdx n) := fun pq => {pq.1, pq.2, pq.1 + pq.2}
  have hcard : P.card = ∑ L ∈ P.image f, (P.filter (fun pq => f pq = L)).card :=
    Finset.card_eq_sum_card_fiberwise fun pq hpq => Finset.mem_image_of_mem f hpq
  change 6 ∣ P.card
  rw [hcard]
  refine Finset.dvd_sum fun L hL => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hL
  simp only [P, Finset.mem_filter, Finset.mem_product] at hab
  rcases hab with ⟨⟨haS, hbS⟩, hab_ne, hsymp, hfr⟩
  have hcS : a + b ∈ S := hclosed a haS b hbS hab_ne hsymp
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ haS)
  have hb0 : b ≠ 0 := fun h => h0 (h ▸ hbS)
  have hac_ne : a ≠ a + b := fun h => hb0 (by
    have := congr_arg (a + ·) h; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
  have hbc_ne : b ≠ a + b := fun h => ha0 (by
    have := congr_arg (· + b) h; simpa [pauliIdx_add_self, pauliIdx_add_cancel_right] using this.symm)
  have hfib : P.filter (fun pq => f pq = {a, b, a + b}) =
      {(a, b), (b, a), (a, a + b), (a + b, a), (b, a + b), (a + b, b)} := by
    ext ⟨p, q⟩
    simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨_, _⟩, hpq, _, _⟩, hfeq⟩
      have hp : p ∈ ({a, b, a + b} : Finset (PauliIdx n)) := by rw [← hfeq]; simp [f]
      have hq : q ∈ ({a, b, a + b} : Finset (PauliIdx n)) := by rw [← hfeq]; simp [f]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
        simp [hp, hq] at hpq ⊢
    · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩)
      · rw [hp, hq]; exact ⟨⟨⟨haS, hbS⟩, hab_ne, hsymp, hfr⟩, rfl⟩
      · rw [hp, hq]
        refine ⟨⟨⟨hbS, haS⟩, Ne.symm hab_ne, by rwa [symp_comm], ?_⟩, ?_⟩
        · rw [gammaSgn_comm (by rwa [symp_comm]), add_comm b a]; linarith
        · ext x; simp only [f, add_comm b a, Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [hp, hq]
        refine ⟨⟨⟨haS, hcS⟩, hac_ne, by rw [symp_add_right, symp_self, hsymp, add_zero], ?_⟩, ?_⟩
        · rw [gammaSgn_add_right hsymp, pauliIdx_add_cancel_left]; linarith
        · ext x; simp only [f, pauliIdx_add_cancel_left, Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [hp, hq]
        refine ⟨⟨⟨hcS, haS⟩, Ne.symm hac_ne, by rw [symp_add_left, symp_self, symp_comm, hsymp, add_zero], ?_⟩, ?_⟩
        · rw [add_comm a b, gammaSgn_add_left (by rwa [symp_comm]), gammaSgn_comm (by rwa [symp_comm]),
            add_comm b a, add_comm (a + b) a, pauliIdx_add_cancel_left]; linarith
        · ext x; simp only [f, add_comm (a + b) a, pauliIdx_add_cancel_left,
            Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [hp, hq]
        refine ⟨⟨⟨hbS, hcS⟩, hbc_ne, by rw [symp_add_right, symp_comm, hsymp, symp_self, add_zero], ?_⟩, ?_⟩
        · rw [add_comm a b, gammaSgn_add_right (by rwa [symp_comm]), gammaSgn_comm (by rwa [symp_comm]),
            pauliIdx_add_cancel_left, add_comm b a]; linarith
        · ext x; simp only [f, add_comm a b, pauliIdx_add_cancel_left,
            Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [hp, hq]
        refine ⟨⟨⟨hcS, hbS⟩, Ne.symm hbc_ne, by rw [symp_add_left, hsymp, symp_self, add_zero], ?_⟩, ?_⟩
        · rw [gammaSgn_add_left hsymp, pauliIdx_add_cancel_right]; linarith
        · ext x; simp only [f, pauliIdx_add_cancel_right, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hfib]
  have hne1 : (a, b) ∉ ({(b, a), (a, a + b), (a + b, a), (b, a + b), (a + b, b)} :
      Finset (PauliIdx n × PauliIdx n)) := by
    simp [hab_ne, hac_ne, hbc_ne, hab_ne.symm, hac_ne.symm, hbc_ne.symm]
  have hne2 : (b, a) ∉ ({(a, a + b), (a + b, a), (b, a + b), (a + b, b)} :
      Finset (PauliIdx n × PauliIdx n)) := by
    simp [hab_ne, hac_ne, hbc_ne, hab_ne.symm, hac_ne.symm, hbc_ne.symm]
  have hne3 : (a, a + b) ∉ ({(a + b, a), (b, a + b), (a + b, b)} :
      Finset (PauliIdx n × PauliIdx n)) := by
    simp [hab_ne, hac_ne, hbc_ne, hab_ne.symm, hac_ne.symm, hbc_ne.symm]
  have hne4 : (a + b, a) ∉ ({(b, a + b), (a + b, b)} :
      Finset (PauliIdx n × PauliIdx n)) := by
    simp [hab_ne, hac_ne, hbc_ne, hab_ne.symm, hac_ne.symm, hbc_ne.symm]
  have hne5 : (b, a + b) ∉ ({(a + b, b)} : Finset (PauliIdx n × PauliIdx n)) := by
    simp [hbc_ne]
  rw [Finset.card_insert_of_notMem hne1, Finset.card_insert_of_notMem hne2,
      Finset.card_insert_of_notMem hne3, Finset.card_insert_of_notMem hne4,
      Finset.card_insert_of_notMem hne5, Finset.card_singleton]

/-- Elliptic centers `C_ell = {c : PauliIdx n | Q₀(c) = 1}`. -/
def ellCenters (n : ℕ) : Finset (PauliIdx n) :=
  Finset.univ.filter fun c => quadForm0 c = 1

/-- Nonzero points of `PauliIdx n`. -/
def nzPts (n : ℕ) : Finset (PauliIdx n) :=
  Finset.univ.erase 0

/-- Elliptic quadric `Q_c⁻ = {p ≠ 0 | Q_c(p) = 0}`. -/
def Qminus {n : ℕ} (c : PauliIdx n) : Finset (PauliIdx n) :=
  (nzPts n).filter fun p => quadForm c p = 0

/-- Outside points of `Q_c⁻`: `{p | Q_c(p) = 1}`. -/
def outPts {n : ℕ} (c : PauliIdx n) : Finset (PauliIdx n) :=
  Finset.univ.filter fun p => quadForm c p = 1

/-- Hyperplane slice `Q_c⁻ ∩ po^⊥`. -/
def slicePts {n : ℕ} (c po : PauliIdx n) : Finset (PauliIdx n) :=
  (Qminus c).filter fun p => symp po p = 0

/-- Universal multiplicity of an isotropic line in elliptic quadrics `Q_c⁻` (`24` at `n=4`, `4` at `n=3`). -/
lemma card_elliptic_lines_mult {n : ℕ} (hn : 2 ≤ n) {a b : PauliIdx n}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hs : symp a b = 0) :
    ((Finset.univ.filter fun c : PauliIdx n =>
        quadForm0 c = 1 ∧ quadForm c a = 0 ∧ quadForm c b = 0).card : ℤ) =
      (2 : ℤ) ^ (2 * n - 3) - (2 : ℤ) ^ (n - 1) := by
  have hab0 : a + b ≠ 0 := fun h => hab (by
    have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  let q0s : PauliIdx n → ℤ := fun x => if quadForm0 x = 0 then 1 else -1
  have hind : ∀ c : PauliIdx n,
      (if quadForm0 c = 1 ∧ quadForm c a = 0 ∧ quadForm c b = 0 then (8 : ℤ) else 0) =
      (1 - q0s c) * (1 + q0s a * sympSign a c) * (1 + q0s b * sympSign b c) := by
    intro c
    have hqa : quadForm c a = 0 ↔ quadForm0 a = symp a c := by
      simp only [quadForm, symp_comm c a]
      rcases zmod2_cases (quadForm0 a) with h1 | h1 <;>
      rcases zmod2_cases (symp a c) with h2 | h2 <;> simp [h1, h2]
      all_goals decide
    have hqb : quadForm c b = 0 ↔ quadForm0 b = symp b c := by
      simp only [quadForm, symp_comm c b]
      rcases zmod2_cases (quadForm0 b) with h1 | h1 <;>
      rcases zmod2_cases (symp b c) with h2 | h2 <;> simp [h1, h2]
      all_goals decide
    simp only [hqa, hqb, q0s, sympSign]
    rcases zmod2_cases (quadForm0 c) with hc | hc <;>
    rcases zmod2_cases (quadForm0 a) with h1 | h1 <;>
    rcases zmod2_cases (symp a c) with h2 | h2 <;>
    rcases zmod2_cases (quadForm0 b) with h3 | h3 <;>
    rcases zmod2_cases (symp b c) with h4 | h4 <;>
    simp [hc, h1, h2, h3, h4]
  have hsum : (8 : ℤ) * ((Finset.univ.filter fun c : PauliIdx n =>
      quadForm0 c = 1 ∧ quadForm c a = 0 ∧ quadForm c b = 0).card : ℤ) =
      ∑ c : PauliIdx n, (1 - q0s c) * (1 + q0s a * sympSign a c) * (1 + q0s b * sympSign b c) := by
    simp_rw [← hind, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have hq0ab : q0s (a + b) = q0s a * q0s b := by
    simp only [q0s, quadForm0_add, hs, add_zero]
    rcases zmod2_cases (quadForm0 a) with h1 | h1 <;>
    rcases zmod2_cases (quadForm0 b) with h2 | h2 <;> simp [h1, h2]
    decide
  have hq0_sq : ∀ x : PauliIdx n, q0s x * q0s x = 1 := fun x => by
    simp only [q0s]; split_ifs <;> norm_num
  have hprod : ∀ v c : PauliIdx n, q0s c * sympSign v c = (if quadForm v c = 0 then (1 : ℤ) else -1) := by
    intro v c; simp only [q0s, sympSign, quadForm]
    rcases zmod2_cases (quadForm0 c) with h1 | h1 <;>
    rcases zmod2_cases (symp v c) with h2 | h2 <;> simp [h1, h2]
    decide
  have hqsum : ∀ v : PauliIdx n, ∑ c : PauliIdx n, q0s v * (q0s c * sympSign v c) = (2 : ℤ) ^ n := by
    intro v; simp_rw [← Finset.mul_sum, hprod, sum_quadChar]
    change q0s v * (q0s v * (2 : ℤ) ^ n) = (2 : ℤ) ^ n
    rw [← mul_assoc, hq0_sq, one_mul]
  have hexp : ∑ c : PauliIdx n, (1 - q0s c) * (1 + q0s a * sympSign a c) * (1 + q0s b * sympSign b c) =
      (4 : ℤ) ^ n - 4 * (2 : ℤ) ^ n := by
    have hterm : ∀ c : PauliIdx n,
        (1 - q0s c) * (1 + q0s a * sympSign a c) * (1 + q0s b * sympSign b c) =
        sympSign 0 c + q0s a * sympSign a c + q0s b * sympSign b c + q0s (a + b) * sympSign (a + b) c
        - (q0s 0 * (q0s c * sympSign 0 c) + q0s a * (q0s c * sympSign a c) +
           q0s b * (q0s c * sympSign b c) + q0s (a + b) * (q0s c * sympSign (a + b) c)) := by
      intro c
      have hq00 : q0s 0 = 1 := by simp [q0s, quadForm0, dot_zero_left]
      rw [sympSign_add_left, hq0ab, hq00, sympSign_zero_left']
      ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h0 := sum_sympSign_univ (0 : PauliIdx n)
    have ha' := sum_sympSign_univ a
    have hb' := sum_sympSign_univ b
    have hab' := sum_sympSign_univ (a + b)
    simp only [↓reduceIte, ha, hb, hab0] at h0 ha' hb' hab'
    have hqa' : ∑ c : PauliIdx n, q0s a * sympSign a c = 0 := by rw [← Finset.mul_sum, ha', mul_zero]
    have hqb' : ∑ c : PauliIdx n, q0s b * sympSign b c = 0 := by rw [← Finset.mul_sum, hb', mul_zero]
    have hqab' : ∑ c : PauliIdx n, q0s (a + b) * sympSign (a + b) c = 0 := by
      rw [← Finset.mul_sum, hab', mul_zero]
    rw [h0, hqa', hqb', hqab', hqsum 0, hqsum a, hqsum b, hqsum (a + b)]
    ring
  rw [hexp] at hsum
  have h4n : (4 : ℤ) ^ n = 8 * (2 : ℤ) ^ (2 * n - 3) := by
    have hpow : (4 : ℤ) ^ n = (2 : ℤ) ^ (2 * n) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [hpow, show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (2 * n - 3) = 2 * n by omega]
  have h2n : 4 * (2 : ℤ) ^ n = 8 * (2 : ℤ) ^ (n - 1) := by
    calc 4 * (2 : ℤ) ^ n = 4 * (2 * (2 : ℤ) ^ (n - 1)) := by
          rw [← pow_succ', show n - 1 + 1 = n by omega]
      _ = 8 * (2 : ℤ) ^ (n - 1) := by ring
  linarith

/-- Universal multiplicity of a `Q_{c0}⁻` isotropic line in hyperplane slices (`40` at `n=4`). -/
lemma card_slice_lines_mult {n : ℕ} (hn : 2 ≤ n) {c0 a b : PauliIdx n}
    (hc0 : quadForm0 c0 = 1) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hs : symp a b = 0)
    (hqa : quadForm c0 a = 0) (hqb : quadForm c0 b = 0) :
    ((Finset.univ.filter fun p : PauliIdx n =>
        quadForm c0 p = 1 ∧ symp p a = 0 ∧ symp p b = 0).card : ℤ) =
      (2 : ℤ) ^ (2 * n - 3) + (2 : ℤ) ^ (n - 1) := by
  have hab0 : a + b ≠ 0 := fun h => hab (by
    have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  let qcs : PauliIdx n → ℤ := fun x => if quadForm c0 x = 0 then 1 else -1
  have hind : ∀ p : PauliIdx n,
      (if quadForm c0 p = 1 ∧ symp p a = 0 ∧ symp p b = 0 then (8 : ℤ) else 0) =
      (1 - qcs p) * (1 + sympSign a p) * (1 + sympSign b p) := by
    intro p; simp only [qcs, sympSign, symp_comm a p, symp_comm b p]
    rcases zmod2_cases (quadForm c0 p) with h1 | h1 <;>
    rcases zmod2_cases (symp p a) with h2 | h2 <;>
    rcases zmod2_cases (symp p b) with h3 | h3 <;> simp [h1, h2, h3]
  have hsum : (8 : ℤ) * ((Finset.univ.filter fun p : PauliIdx n =>
      quadForm c0 p = 1 ∧ symp p a = 0 ∧ symp p b = 0).card : ℤ) =
      ∑ p : PauliIdx n, (1 - qcs p) * (1 + sympSign a p) * (1 + sympSign b p) := by
    simp_rw [← hind, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have hqcs_prod : ∀ v p : PauliIdx n,
      qcs p * sympSign v p = (if quadForm (c0 + v) p = 0 then (1 : ℤ) else -1) := by
    intro v p; simp only [qcs, sympSign, quadForm, symp_add_left]
    rw [show quadForm0 p + (symp c0 p + symp v p) = (quadForm0 p + symp c0 p) + symp v p by ring]
    rcases zmod2_cases (quadForm0 p + symp c0 p) with h1 | h1 <;>
    rcases zmod2_cases (symp v p) with h2 | h2 <;> simp [h1, h2]
    decide
  have hqcs_sum : ∀ v : PauliIdx n, quadForm c0 v = 0 →
      ∑ p : PauliIdx n, qcs p * sympSign v p = -(2 : ℤ) ^ n := by
    intro v hv
    simp_rw [hqcs_prod, sum_quadChar]
    have hq0cv : quadForm0 (c0 + v) = 1 := by
      rw [quadForm0_add, hc0]
      have : quadForm0 v + symp c0 v = 0 := hv
      rw [add_assoc, this, add_zero]
    simp [hq0cv]
  have hq0 : quadForm c0 0 = 0 := quadForm_zero c0
  have hqab : quadForm c0 (a + b) = 0 := by rw [quadForm_add, hqa, hqb, hs]; simp
  have hexp : ∑ p : PauliIdx n, (1 - qcs p) * (1 + sympSign a p) * (1 + sympSign b p) =
      (4 : ℤ) ^ n + 4 * (2 : ℤ) ^ n := by
    have hterm : ∀ p : PauliIdx n,
        (1 - qcs p) * (1 + sympSign a p) * (1 + sympSign b p) =
        sympSign 0 p + sympSign a p + sympSign b p + sympSign (a + b) p
        - (qcs p * sympSign 0 p + qcs p * sympSign a p +
           qcs p * sympSign b p + qcs p * sympSign (a + b) p) := by
      intro p; rw [sympSign_add_left, sympSign_zero_left']; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h0 := sum_sympSign_univ (0 : PauliIdx n)
    have ha' := sum_sympSign_univ a
    have hb' := sum_sympSign_univ b
    have hab' := sum_sympSign_univ (a + b)
    simp only [↓reduceIte, ha, hb, hab0] at h0 ha' hb' hab'
    rw [hqcs_sum 0 hq0, hqcs_sum a hqa, hqcs_sum b hqb, hqcs_sum (a + b) hqab]
    linarith
  rw [hexp] at hsum
  have h4n : (4 : ℤ) ^ n = 8 * (2 : ℤ) ^ (2 * n - 3) := by
    have hpow : (4 : ℤ) ^ n = (2 : ℤ) ^ (2 * n) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [hpow, show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (2 * n - 3) = 2 * n by omega]
  have h2n : 4 * (2 : ℤ) ^ n = 8 * (2 : ℤ) ^ (n - 1) := by
    calc 4 * (2 : ℤ) ^ n = 4 * (2 * (2 : ℤ) ^ (n - 1)) := by
          rw [← pow_succ', show n - 1 + 1 = n by omega]
      _ = 8 * (2 : ℤ) ^ (n - 1) := by ring
  linarith

/-- Double-counting over all `120` copies of `Q⁻(7,2)` in `W(7,2)`. -/
theorem double_count_W72_Qminus (s : PauliIdx 4 → ℤ) :
    24 * frustPairs (nzPts 4) s = ∑ c ∈ ellCenters 4, frustPairs (Qminus c) s := by
  let P := (nzPts 4 ×ˢ nzPts 4).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1
  have hP_card : frustPairs (nzPts 4) s = P.card := rfl
  have hrhs : ∀ c ∈ ellCenters 4,
      frustPairs (Qminus c) s = ∑ pq ∈ P, if quadForm c pq.1 = 0 ∧ quadForm c pq.2 = 0 then 1 else 0 := by
    intro c _
    unfold frustPairs
    rw [Finset.sum_boole, Nat.cast_id]
    refine congr_arg Finset.card (Finset.ext fun ⟨p, q⟩ => ?_)
    simp only [P, Qminus, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩ => ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩,
           fun ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩ => ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩⟩
  rw [Finset.sum_congr rfl hrhs, Finset.sum_comm]
  have hinner : ∀ pq ∈ P,
      (∑ c ∈ ellCenters 4, if quadForm c pq.1 = 0 ∧ quadForm c pq.2 = 0 then 1 else 0) = 24 := by
    rintro ⟨a, b⟩ hab
    simp only [P, nzPts, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at hab
    rw [Finset.sum_boole, Nat.cast_id]
    have hflt : (ellCenters 4).filter (fun c => quadForm c a = 0 ∧ quadForm c b = 0) =
        Finset.univ.filter (fun c : PauliIdx 4 => quadForm0 c = 1 ∧ quadForm c a = 0 ∧ quadForm c b = 0) := by
      ext c; simp [ellCenters, and_assoc]
    rw [hflt]
    have hZ := card_elliptic_lines_mult (n := 4) (by norm_num) hab.1.1.1 hab.1.2.1 hab.2.1 hab.2.2.1
    norm_num at hZ; omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm, hP_card]

/-- Double-counting over all `136` hyperplane slices `Q_{c0}⁻ ∩ po^⊥` of `Q⁻(7,2)`. -/
theorem double_count_Qminus72_slices {c0 : PauliIdx 4} (hc0 : quadForm0 c0 = 1)
    (s : PauliIdx 4 → ℤ) :
    40 * frustPairs (Qminus c0) s = ∑ po ∈ outPts c0, frustPairs (slicePts c0 po) s := by
  let P := (Qminus c0 ×ˢ Qminus c0).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1
  have hP_card : frustPairs (Qminus c0) s = P.card := rfl
  have hrhs : ∀ po ∈ outPts c0,
      frustPairs (slicePts c0 po) s = ∑ pq ∈ P, if symp po pq.1 = 0 ∧ symp po pq.2 = 0 then 1 else 0 := by
    intro po _
    unfold frustPairs
    rw [Finset.sum_boole, Nat.cast_id]
    refine congr_arg Finset.card (Finset.ext fun ⟨p, q⟩ => ?_)
    simp only [P, slicePts, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩ => ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩,
           fun ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩ => ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩⟩
  rw [Finset.sum_congr rfl hrhs, Finset.sum_comm]
  have hinner : ∀ pq ∈ P,
      (∑ po ∈ outPts c0, if symp po pq.1 = 0 ∧ symp po pq.2 = 0 then 1 else 0) = 40 := by
    rintro ⟨a, b⟩ hab
    simp only [P, Qminus, nzPts, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at hab
    rw [Finset.sum_boole, Nat.cast_id]
    have hflt : (outPts c0).filter (fun po => symp po a = 0 ∧ symp po b = 0) =
        Finset.univ.filter (fun po : PauliIdx 4 => quadForm c0 po = 1 ∧ symp po a = 0 ∧ symp po b = 0) := by
      ext po; simp [outPts, and_assoc]
    rw [hflt]
    have hZ := card_slice_lines_mult (n := 4) (by norm_num) hc0 hab.1.1.1.1 hab.1.2.1.1
      hab.2.1 hab.2.2.1 hab.1.1.2 hab.1.2.2
    norm_num at hZ; omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm, hP_card]

/-- Double-counting over all `28` copies of `Q⁻(5,2)` in `W(5,2)`. -/
theorem double_count_W52_Qminus52 (s : PauliIdx 3 → ℤ) :
    4 * frustPairs (nzPts 3) s = ∑ c ∈ ellCenters 3, frustPairs (Qminus c) s := by
  let P := (nzPts 3 ×ˢ nzPts 3).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1
  have hP_card : frustPairs (nzPts 3) s = P.card := rfl
  have hrhs : ∀ c ∈ ellCenters 3,
      frustPairs (Qminus c) s = ∑ pq ∈ P, if quadForm c pq.1 = 0 ∧ quadForm c pq.2 = 0 then 1 else 0 := by
    intro c _
    unfold frustPairs
    rw [Finset.sum_boole, Nat.cast_id]
    refine congr_arg Finset.card (Finset.ext fun ⟨p, q⟩ => ?_)
    simp only [P, Qminus, Finset.mem_filter, Finset.mem_product]
    exact ⟨fun ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩ => ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩,
           fun ⟨⟨⟨hp1, hq1⟩, h3⟩, hp2, hq2⟩ => ⟨⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩, h3⟩⟩
  rw [Finset.sum_congr rfl hrhs, Finset.sum_comm]
  have hinner : ∀ pq ∈ P,
      (∑ c ∈ ellCenters 3, if quadForm c pq.1 = 0 ∧ quadForm c pq.2 = 0 then 1 else 0) = 4 := by
    rintro ⟨a, b⟩ hab
    simp only [P, nzPts, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at hab
    rw [Finset.sum_boole, Nat.cast_id]
    have hflt : (ellCenters 3).filter (fun c => quadForm c a = 0 ∧ quadForm c b = 0) =
        Finset.univ.filter (fun c : PauliIdx 3 => quadForm0 c = 1 ∧ quadForm c a = 0 ∧ quadForm c b = 0) := by
      ext c; simp [ellCenters, and_assoc]
    rw [hflt]
    have hZ := card_elliptic_lines_mult (n := 3) (by norm_num) hab.1.1.1 hab.1.2.1 hab.2.1 hab.2.2.1
    norm_num at hZ; omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm, hP_card]

private lemma card_comm_pairs_four :
    ((nzPts 4 ×ˢ nzPts 4).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0).card = 32130 := by
  have hrow : ∀ q ∈ nzPts 4, ((nzPts 4).filter fun p => q ≠ p ∧ symp q p = 0).card = 126 := by
    intro q hq
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
    have hsum_s := sum_sympSign_univ q
    simp only [hq0, ↓reduceIte] at hsum_s
    let Zq := Finset.univ.filter fun p : PauliIdx 4 => symp q p = 0
    have hZq : (Zq.card : ℤ) = 128 := by
      have htot : (Finset.univ : Finset (PauliIdx 4)).card = 256 := by
        rw [Finset.card_univ, card_PauliIdx]; norm_num
      have h2 : ∑ p : PauliIdx 4, sympSign q p = 2 * (Zq.card : ℤ) - 256 := by
        have hs' : ∑ p : PauliIdx 4, sympSign q p =
            ∑ p : PauliIdx 4, (if symp q p = 0 then (2 : ℤ) else 0) - ∑ _p : PauliIdx 4, (1 : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => by simp only [sympSign]; split_ifs <;> ring
        rw [hs', Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.sum_const,
            htot]; ring
      linarith
    have hflt : (nzPts 4).filter (fun p => q ≠ p ∧ symp q p = 0) = (Zq.erase 0).erase q := by
      ext p
      simp only [nzPts, Zq, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hp0, hqp, hsp⟩; exact ⟨Ne.symm hqp, hp0, hsp⟩
      · rintro ⟨hpq, hp0, hsp⟩; exact ⟨hp0, Ne.symm hpq, hsp⟩
    rw [hflt, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
    · omega
    · simp [Zq, symp_zero_right]
    · simp [Zq, hq0, symp_self]
  have hcardC : ((nzPts 4 ×ˢ nzPts 4).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0).card =
      ∑ q ∈ nzPts 4, ((nzPts 4).filter fun p => q ≠ p ∧ symp q p = 0).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => by rw [Finset.card_filter]
  rw [hcardC, Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]
  have hUcard : (nzPts 4).card = 255 := by
    rw [nzPts, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_PauliIdx]
    norm_num
  rw [hUcard]

private lemma sum_comm_pairs_eq_card_sub_frust {n : ℕ} (U : Finset (PauliIdx n))
    (h0 : (0 : PauliIdx n) ∉ U) {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    let C := (U ×ˢ U).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0
    (∑ pq ∈ C, ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ)) =
      (C.card : ℝ) - 2 * (frustPairs U s : ℝ) := by
  intro C
  have hterm : ∀ pq ∈ C,
      ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) =
      1 - 2 * (if gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1 then (1 : ℝ) else 0) := by
    have hmul_pm1 : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b = 1 ∨ a * b = -1 := by
      rintro a b (rfl | rfl) (rfl | rfl) <;> decide
    have hpm1 : ∀ z : ℤ, (z = 1 ∨ z = -1) → (z : ℝ) = 1 - 2 * (if z = -1 then (1 : ℝ) else 0) := by
      rintro z (rfl | rfl) <;> norm_num
    rintro ⟨p, q⟩ hpq
    simp only [C, Finset.mem_filter, Finset.mem_product] at hpq
    have hp0 : p ≠ 0 := fun h => h0 (h ▸ hpq.1.1)
    have hq0 : q ≠ 0 := fun h => h0 (h ▸ hpq.1.2)
    have hpq0 : p + q ≠ 0 := fun h => hpq.2.1 (by
      have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    exact hpm1 _ (hmul_pm1 _ _ (hmul_pm1 _ _ (hmul_pm1 _ _ (gammaSgn_eq_pm1 p q)
      (hs.2 p hp0)) (hs.2 q hq0)) (hs.2 (p + q) hpq0))
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1; congr 1
  refine congr_arg (Nat.cast : ℕ → ℝ) ?_
  unfold frustPairs
  refine congr_arg Finset.card (Finset.ext fun pq => ?_)
  simp only [C, Finset.mem_filter]
  exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩

/-- Exact bridge from `signCubeSum 4 σ` to `frustPairs (nzPts 4) s`:
    `signCubeSum 4 σ = 16065 - frustPairs (nzPts 4) s`. -/
theorem signCubeSum_eq_frustPairs {σ : PauliIdx 4 → ℝ} (h0 : σ 0 = 0)
    (hpm : ∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let s : PauliIdx 4 → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
    IsSignAssign s ∧ signCubeSum 4 σ = 16065 - (frustPairs (nzPts 4) s : ℝ) := by
  intro s
  have hs_valid : IsSignAssign s :=
    ⟨by simp [s], fun p hp => by simp only [s, hp, ↓reduceIte]; split_ifs <;> simp⟩
  have hs_cast : ∀ p : PauliIdx 4, (s p : ℝ) = σ p := fun p => by
    by_cases hp : p = 0
    · subst hp; simp [s, h0]
    · simp only [s, hp, ↓reduceIte]
      rcases hpm p hp with h | h
      · simp [h]
      · have hne : σ p ≠ 1 := by linarith
        simp only [hne, ↓reduceIte, h]; norm_num
  refine ⟨hs_valid, ?_⟩
  have hsum_eq : ∀ (U : Finset (PauliIdx 4)),
      ∑ q ∈ U, σ q * ((1 / 2 : ℝ) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p)) =
      (1 / 2 : ℝ) * ∑ pq ∈ (U ×ˢ U).filter (fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0),
        ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) := by
    intro U
    have h1 : ∀ q ∈ U,
        σ q * ((1 / 2 : ℝ) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p)) =
        (1 / 2 : ℝ) * ∑ p ∈ U,
          if q ≠ p ∧ symp q p = 0 then ((gammaSgn q p * s q * s p * s (q + p) : ℤ) : ℝ) else 0 := by
      intro q hqU
      rw [← mul_assoc, mul_comm (σ q), mul_assoc, Finset.mul_sum]
      refine congr_arg ((1 / 2 : ℝ) * ·) ?_
      rw [← Finset.add_sum_erase U _ hqU]
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hqp : q ≠ p := Ne.symm (Finset.mem_erase.mp hp).1
      rcases zmod2_cases (symp q p) with hsp | hsp
      · simp only [hqp, hsp, not_false_eq_true, and_self, ↓reduceIte,
          pauliPhase_re_eq_gammaSgn hsp, ← hs_cast]
        push_cast; ring
      · simp only [hqp, hsp, show (1 : ZMod 2) ≠ 0 by decide, and_false, ↓reduceIte,
          (pauliPhase_re_cases q p).2 hsp]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_product']
    exact congr_arg ((1 / 2 : ℝ) * ·) (Finset.sum_filter _ _).symm
  unfold signCubeSum
  change (∑ q ∈ nzPts 4, σ q * ((1 / 2 : ℝ) * ∑ p ∈ (nzPts 4).erase q, (pauliPhase q p).re * σ p * σ (q + p))) = _
  rw [hsum_eq (nzPts 4), sum_comm_pairs_eq_card_sub_frust (nzPts 4) (by simp [nzPts]) hs_valid,
      card_comm_pairs_four, show ((32130 : ℕ) : ℝ) = 32130 by norm_num]
  ring

/-- Transitivity on elliptic centers: for any `c, c0` with `Q₀(c) = Q₀(c0) = 1`,
    the single transvection `T_{c + c0}` maps `Q_c⁻` onto `Q_{c0}⁻`! -/
lemma frustPairs_Qminus_eq_of_ellCenter {n : ℕ} {c c0 : PauliIdx n}
    (hc : quadForm0 c = 1) (hc0 : quadForm0 c0 = 1) (s : PauliIdx n → ℤ) :
    frustPairs (Qminus c) s = frustPairs (Qminus c0) (applyTransv (c + c0) s) := by
  have hq : quadForm c0 (c + c0) = 0 := by
    rw [quadForm, quadForm0_add, hc, hc0, symp_add_right, symp_self, add_zero, symp_comm c0 c]
    have : (1 : ZMod 2) + 1 = 0 := by decide
    calc 1 + 1 + symp c c0 + symp c c0 = (1 + 1) + (symp c c0 + symp c c0) := by ring
      _ = 0 := by rw [this, zmod2_add_self, add_zero]
  have hadd : c0 + (c + c0) = c := by rw [add_comm c c0, pauliIdx_add_cancel_left]
  symm
  refine frustPairs_applyTransv (c + c0) (Qminus c0) (Qminus c) ?_ s
  intro p
  simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  have hm : quadForm c (transvPt (c + c0) p) = quadForm c0 p := by
    have := quadForm_transvPt_move hq (transvPt (c + c0) p)
    rw [transvPt_invol, hadd] at this
    exact this.symm
  rw [hm]
  exact ⟨fun ⟨hp0, hqp⟩ => ⟨fun h => hp0 (by rw [← transvPt_invol (c + c0) p, h, transvPt_zero]), hqp⟩,
         fun ⟨htp0, hqp⟩ => ⟨fun h => htp0 (by rw [h, transvPt_zero]), hqp⟩⟩

/-! ### Section 3: Equivalence `PauliIdx 4 ≃ Fin 256` & `PauliIdx 3 ≃ Fin 64` -/

/-- Decode `Fin 256` to `PauliIdx 4`: upper 4 bits = `x`, lower 4 bits = `z`. -/
def dec4 (k : Fin 256) : PauliIdx 4 :=
  (fun i => (((k.val >>> (4 + i.val)) &&& 1 : Nat) : ZMod 2),
   fun i => (((k.val >>> i.val) &&& 1 : Nat) : ZMod 2))

/-- Encode `PauliIdx 4` to `Fin 256`. -/
def enc4 (p : PauliIdx 4) : Fin 256 :=
  ⟨(p.1 0).val * 16 + (p.1 1).val * 32 + (p.1 2).val * 64 + (p.1 3).val * 128 +
   (p.2 0).val + (p.2 1).val * 2 + (p.2 2).val * 4 + (p.2 3).val * 8, by
    have h0 := (p.1 0).val_lt; have h1 := (p.1 1).val_lt
    have h2 := (p.1 2).val_lt; have h3 := (p.1 3).val_lt
    have g0 := (p.2 0).val_lt; have g1 := (p.2 1).val_lt
    have g2 := (p.2 2).val_lt; have g3 := (p.2 3).val_lt
    omega⟩

/-- Decode `Fin 64` to `PauliIdx 3`: upper 3 bits = `x`, lower 3 bits = `z`. -/
def dec3 (k : Fin 64) : PauliIdx 3 :=
  (fun i => (((k.val >>> (3 + i.val)) &&& 1 : Nat) : ZMod 2),
   fun i => (((k.val >>> i.val) &&& 1 : Nat) : ZMod 2))

/-- Encode `PauliIdx 3` to `Fin 64`. -/
def enc3 (p : PauliIdx 3) : Fin 64 :=
  ⟨(p.1 0).val * 8 + (p.1 1).val * 16 + (p.1 2).val * 32 +
   (p.2 0).val + (p.2 1).val * 2 + (p.2 2).val * 4, by
    have h0 := (p.1 0).val_lt; have h1 := (p.1 1).val_lt; have h2 := (p.1 2).val_lt
    have g0 := (p.2 0).val_lt; have g1 := (p.2 1).val_lt; have g2 := (p.2 2).val_lt
    omega⟩

lemma enc4_dec4 (k : Fin 256) : enc4 (dec4 k) = k := by
  apply Fin.ext
  have hk := k.isLt
  simp only [enc4, dec4, Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl]
  have hbit : ∀ (x s : Nat), ((((x >>> s) &&& 1 : Nat) : ZMod 2)).val = (x / 2 ^ s) % 2 := fun x s => by
    rw [ZMod.val_natCast, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  simp only [hbit]; norm_num; omega

lemma dec4_enc4 (p : PauliIdx 4) : dec4 (enc4 p) = p := by
  have hz : ∀ x : ZMod 2, (x.val : ZMod 2) = x := fun x => by
    rcases zmod2_cases x with rfl | rfl <;> decide
  have ha0 := (p.1 0).val_lt; have ha1 := (p.1 1).val_lt
  have ha2 := (p.1 2).val_lt; have ha3 := (p.1 3).val_lt
  have hb0 := (p.2 0).val_lt; have hb1 := (p.2 1).val_lt
  have hb2 := (p.2 2).val_lt; have hb3 := (p.2 3).val_lt
  let N := (p.1 0).val * 16 + (p.1 1).val * 32 + (p.1 2).val * 64 + (p.1 3).val * 128 +
           (p.2 0).val + (p.2 1).val * 2 + (p.2 2).val * 4 + (p.2 3).val * 8
  have hbit : ∀ s : Nat, (N >>> s) &&& 1 = (N / 2 ^ s) % 2 := fun s => by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  apply Prod.ext <;> (ext i; fin_cases i)
  · change (((N >>> 4) &&& 1 : Nat) : ZMod 2) = p.1 0
    rw [hbit 4, show N / 2 ^ 4 % 2 = (p.1 0).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 5) &&& 1 : Nat) : ZMod 2) = p.1 1
    rw [hbit 5, show N / 2 ^ 5 % 2 = (p.1 1).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 6) &&& 1 : Nat) : ZMod 2) = p.1 2
    rw [hbit 6, show N / 2 ^ 6 % 2 = (p.1 2).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 7) &&& 1 : Nat) : ZMod 2) = p.1 3
    rw [hbit 7, show N / 2 ^ 7 % 2 = (p.1 3).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 0) &&& 1 : Nat) : ZMod 2) = p.2 0
    rw [hbit 0, show N / 2 ^ 0 % 2 = (p.2 0).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 1) &&& 1 : Nat) : ZMod 2) = p.2 1
    rw [hbit 1, show N / 2 ^ 1 % 2 = (p.2 1).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 2) &&& 1 : Nat) : ZMod 2) = p.2 2
    rw [hbit 2, show N / 2 ^ 2 % 2 = (p.2 2).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 3) &&& 1 : Nat) : ZMod 2) = p.2 3
    rw [hbit 3, show N / 2 ^ 3 % 2 = (p.2 3).val by dsimp only [N]; omega]; exact hz _

def equiv4 : PauliIdx 4 ≃ Fin 256 where
  toFun := enc4
  invFun := dec4
  left_inv := dec4_enc4
  right_inv := enc4_dec4

lemma enc3_dec3 (k : Fin 64) : enc3 (dec3 k) = k := by
  apply Fin.ext
  have hk := k.isLt
  simp only [enc3, dec3, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hbit : ∀ (x s : Nat), ((((x >>> s) &&& 1 : Nat) : ZMod 2)).val = (x / 2 ^ s) % 2 := fun x s => by
    rw [ZMod.val_natCast, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  simp only [hbit]; norm_num; omega

lemma dec3_enc3 (p : PauliIdx 3) : dec3 (enc3 p) = p := by
  have hz : ∀ x : ZMod 2, (x.val : ZMod 2) = x := fun x => by
    rcases zmod2_cases x with rfl | rfl <;> decide
  have ha0 := (p.1 0).val_lt; have ha1 := (p.1 1).val_lt; have ha2 := (p.1 2).val_lt
  have hb0 := (p.2 0).val_lt; have hb1 := (p.2 1).val_lt; have hb2 := (p.2 2).val_lt
  let N := (p.1 0).val * 8 + (p.1 1).val * 16 + (p.1 2).val * 32 +
           (p.2 0).val + (p.2 1).val * 2 + (p.2 2).val * 4
  have hbit : ∀ s : Nat, (N >>> s) &&& 1 = (N / 2 ^ s) % 2 := fun s => by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  apply Prod.ext <;> (ext i; fin_cases i)
  · change (((N >>> 3) &&& 1 : Nat) : ZMod 2) = p.1 0
    rw [hbit 3, show N / 2 ^ 3 % 2 = (p.1 0).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 4) &&& 1 : Nat) : ZMod 2) = p.1 1
    rw [hbit 4, show N / 2 ^ 4 % 2 = (p.1 1).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 5) &&& 1 : Nat) : ZMod 2) = p.1 2
    rw [hbit 5, show N / 2 ^ 5 % 2 = (p.1 2).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 0) &&& 1 : Nat) : ZMod 2) = p.2 0
    rw [hbit 0, show N / 2 ^ 0 % 2 = (p.2 0).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 1) &&& 1 : Nat) : ZMod 2) = p.2 1
    rw [hbit 1, show N / 2 ^ 1 % 2 = (p.2 1).val by dsimp only [N]; omega]; exact hz _
  · change (((N >>> 2) &&& 1 : Nat) : ZMod 2) = p.2 2
    rw [hbit 2, show N / 2 ^ 2 % 2 = (p.2 2).val by dsimp only [N]; omega]; exact hz _

def equiv3 : PauliIdx 3 ≃ Fin 64 where
  toFun := enc3
  invFun := dec3
  left_inv := dec3_enc3
  right_inv := enc3_dec3

lemma dec4_zero : dec4 0 = 0 := by
  apply Prod.ext <;> (ext i; fin_cases i <;> decide)

lemma dec3_zero : dec3 0 = 0 := by
  apply Prod.ext <;> (ext i; fin_cases i <;> decide)

private lemma nat_bit_xor_zmod2 (a b k : Nat) :
    ((((a ^^^ b) >>> k) &&& 1 : Nat) : ZMod 2) =
      (((a >>> k) &&& 1 : Nat) : ZMod 2) + (((b >>> k) &&& 1 : Nat) : ZMod 2) := by
  have h : (((a ^^^ b) >>> k) &&& 1) = (((a >>> k) &&& 1) + ((b >>> k) &&& 1)) % 2 := by
    have h1 : ((a ^^^ b) >>> k) &&& 1 = (((a >>> k) &&& 1) ^^^ ((b >>> k) &&& 1)) := by
      rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
    rw [h1]
    have ha : (a >>> k) &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
    have hb : (b >>> k) &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
    generalize (a >>> k) &&& 1 = x at ha ⊢
    generalize (b >>> k) &&& 1 = y at hb ⊢
    interval_cases x <;> interval_cases y <;> decide
  rw [h, ← Nat.cast_add]; exact ZMod.natCast_mod _ 2

lemma dec4_xor (a b : Fin 256) :
    dec4 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt⟩ = dec4 a + dec4 b := by
  apply Prod.ext <;> (ext i; simp only [dec4, Pi.add_apply]; exact nat_bit_xor_zmod2 a.val b.val _)

lemma dec3_xor (a b : Fin 64) :
    dec3 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ = dec3 a + dec3 b := by
  apply Prod.ext <;> (ext i; simp only [dec3, Pi.add_apply]; exact nat_bit_xor_zmod2 a.val b.val _)

private lemma nat_and_bit_eq (x y : Nat) : (x &&& y) &&& 1 = ((x &&& 1) * (y &&& 1)) := by
  have h : (x &&& y) &&& 1 = (x &&& 1) &&& (y &&& 1) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and]; cases x.testBit i <;> cases y.testBit i <;> cases (1 : Nat).testBit i <;> rfl
  rw [h]
  have hx : x &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
  have hy : y &&& 1 < 2 := by rw [Nat.and_one_is_mod]; omega
  generalize x &&& 1 = a at hx ⊢
  generalize y &&& 1 = b at hy ⊢
  interval_cases a <;> interval_cases b <;> decide

private lemma nat_bit_and_mul_zmod2 (a b k : Nat) :
    ((((a &&& b) >>> k) &&& 1 : Nat) : ZMod 2) =
      (((a >>> k) &&& 1 : Nat) : ZMod 2) * (((b >>> k) &&& 1 : Nat) : ZMod 2) := by
  rw [Nat.shiftRight_and_distrib, nat_and_bit_eq, Nat.cast_mul]

private lemma dot2_4_cast (a b : Nat) :
    (dot2_4 a b : ZMod 2) =
      ∑ i : Fin 4, (((a >>> i.val) &&& 1 : Nat) : ZMod 2) * (((b >>> i.val) &&& 1 : Nat) : ZMod 2) := by
  rw [dot2_4, pop4, Nat.and_one_is_mod, ZMod.natCast_mod]
  simp only [Nat.cast_add, Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 by rfl]
  rw [show ((((a &&& b) &&& 1 : Nat) : ZMod 2)) = ((((a &&& b) >>> 0) &&& 1 : Nat) : ZMod 2) by rfl,
      nat_bit_and_mul_zmod2 a b 0, nat_bit_and_mul_zmod2 a b 1,
      nat_bit_and_mul_zmod2 a b 2, nat_bit_and_mul_zmod2 a b 3]

private lemma dot2_3_cast (a b : Nat) :
    (dot2_3 a b : ZMod 2) =
      ∑ i : Fin 3, (((a >>> i.val) &&& 1 : Nat) : ZMod 2) * (((b >>> i.val) &&& 1 : Nat) : ZMod 2) := by
  rw [dot2_3, pop3, Nat.and_one_is_mod, ZMod.natCast_mod]
  simp only [Nat.cast_add, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [show ((((a &&& b) &&& 1 : Nat) : ZMod 2)) = ((((a &&& b) >>> 0) &&& 1 : Nat) : ZMod 2) by rfl,
      nat_bit_and_mul_zmod2 a b 0, nat_bit_and_mul_zmod2 a b 1, nat_bit_and_mul_zmod2 a b 2]

private lemma low4_bit (x : Nat) (i : Fin 4) : (((x &&& 15) >>> i.val) &&& 1) = (x >>> i.val) &&& 1 := by
  have h15 : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4
  rw [h15]
  fin_cases i <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl,
      Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] <;>
    norm_num <;> omega

private lemma low3_bit (x : Nat) (i : Fin 3) : (((x &&& 7) >>> i.val) &&& 1) = (x >>> i.val) &&& 1 := by
  have h7 : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
  rw [h7]
  fin_cases i <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] <;>
    norm_num <;> omega

private lemma hi4_bit (x : Nat) (i : Fin 4) : (((x >>> 4) >>> i.val) &&& 1) = (x >>> (4 + i.val)) &&& 1 := by
  rw [Nat.shiftRight_add]

private lemma hi3_bit (x : Nat) (i : Fin 3) : (((x >>> 3) >>> i.val) &&& 1) = (x >>> (3 + i.val)) &&& 1 := by
  rw [Nat.shiftRight_add]

lemma dot_dec4_fst_snd (a b : Fin 256) :
    dot (dec4 a).1 (dec4 b).2 = (dot2_4 (a.val >>> 4) (b.val &&& 15) : ZMod 2) := by
  rw [dot2_4_cast]; simp only [dot, dec4]
  refine Finset.sum_congr rfl fun i _ => by rw [hi4_bit, low4_bit]

lemma dot_dec4_snd_fst (a b : Fin 256) :
    dot (dec4 a).2 (dec4 b).1 = (dot2_4 (a.val &&& 15) (b.val >>> 4) : ZMod 2) := by
  rw [dot2_4_cast]; simp only [dot, dec4]
  refine Finset.sum_congr rfl fun i _ => by rw [low4_bit, hi4_bit]

lemma dot_dec3_fst_snd (a b : Fin 64) :
    dot (dec3 a).1 (dec3 b).2 = (dot2_3 (a.val >>> 3) (b.val &&& 7) : ZMod 2) := by
  rw [dot2_3_cast]; simp only [dot, dec3]
  refine Finset.sum_congr rfl fun i _ => by rw [hi3_bit, low3_bit]

lemma dot_dec3_snd_fst (a b : Fin 64) :
    dot (dec3 a).2 (dec3 b).1 = (dot2_3 (a.val &&& 7) (b.val >>> 3) : ZMod 2) := by
  rw [dot2_3_cast]; simp only [dot, dec3]
  refine Finset.sum_congr rfl fun i _ => by rw [low3_bit, hi3_bit]

private lemma bit_xor_zmod2 (a b : Nat) (ha : a < 2) (hb : b < 2) :
    ((a ^^^ b : Nat) : ZMod 2) = (a : ZMod 2) + (b : ZMod 2) := by
  interval_cases a <;> interval_cases b <;> decide

private lemma bit_and_zmod2 (a b : Nat) (ha : a < 2) (hb : b < 2) :
    ((a &&& b : Nat) : ZMod 2) = (a : ZMod 2) * (b : ZMod 2) := by
  interval_cases a <;> interval_cases b <;> decide

private lemma bit_or_zmod2 (a b : Nat) (ha : a < 2) (hb : b < 2) :
    ((a ||| b : Nat) : ZMod 2) = (a : ZMod 2) + (b : ZMod 2) + (a : ZMod 2) * (b : ZMod 2) := by
  interval_cases a <;> interval_cases b <;> decide

lemma dot2_4_lt2 (a b : Nat) : dot2_4 a b < 2 := by
  rw [dot2_4, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
lemma dot2_3_lt2 (a b : Nat) : dot2_3 a b < 2 := by
  rw [dot2_3, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
lemma Q4_0_lt2 (p : Nat) : Q4_0 p < 2 := dot2_4_lt2 _ _
lemma Q3_0_lt2 (p : Nat) : Q3_0 p < 2 := dot2_3_lt2 _ _
lemma symp4_lt2 (p q : Nat) : symp4 p q < 2 := Nat.xor_lt_two_pow (n := 1) (dot2_4_lt2 _ _) (dot2_4_lt2 _ _)
lemma symp3_lt2 (p q : Nat) : symp3 p q < 2 := Nat.xor_lt_two_pow (n := 1) (dot2_3_lt2 _ _) (dot2_3_lt2 _ _)
lemma Q4_form_lt2 (c p : Nat) : Q4_form c p < 2 := Nat.xor_lt_two_pow (n := 1) (Q4_0_lt2 p) (symp4_lt2 c p)
lemma Q3_form_lt2 (c p : Nat) : Q3_form c p < 2 := Nat.xor_lt_two_pow (n := 1) (Q3_0_lt2 p) (symp3_lt2 c p)

lemma symp_dec4 (a b : Fin 256) : symp (dec4 a) (dec4 b) = (symp4 a.val b.val : ZMod 2) := by
  simp only [symp, symp4, dot_dec4_fst_snd, dot_dec4_snd_fst]
  exact (bit_xor_zmod2 _ _ (dot2_4_lt2 _ _) (dot2_4_lt2 _ _)).symm

lemma quadForm0_dec4 (a : Fin 256) : quadForm0 (dec4 a) = (Q4_0 a.val : ZMod 2) :=
  dot_dec4_fst_snd a a

lemma quadForm_dec4 (c a : Fin 256) : quadForm (dec4 c) (dec4 a) = (Q4_form c.val a.val : ZMod 2) := by
  simp only [quadForm, Q4_form, quadForm0_dec4, symp_dec4]
  exact (bit_xor_zmod2 _ _ (Q4_0_lt2 _) (symp4_lt2 _ _)).symm

lemma gammaSgn_dec4 (a b : Fin 256) : gammaSgn (dec4 a) (dec4 b) = gamma4_sgn a.val b.val := by
  have hb : gammaBit (dec4 a) (dec4 b) = (gamma4_bit a.val b.val : ZMod 2) := by
    simp only [gammaBit, gamma4_bit, quadForm0_dec4, dot_dec4_fst_snd]
    have h1 := Q4_0_lt2 a.val; have h2 := Q4_0_lt2 b.val; have h3 := dot2_4_lt2 (a.val >>> 4) (b.val &&& 15)
    have h12 : Q4_0 a.val &&& Q4_0 b.val < 2 := Nat.and_lt_two_pow (n := 1) _ h2
    have hx : ((Q4_0 a.val &&& Q4_0 b.val) ^^^ dot2_4 (a.val >>> 4) (b.val &&& 15)) < 2 :=
      Nat.xor_lt_two_pow (n := 1) h12 h3
    rw [show (((Q4_0 a.val &&& Q4_0 b.val) ^^^ dot2_4 (a.val >>> 4) (b.val &&& 15)) &&& 1) =
        ((Q4_0 a.val &&& Q4_0 b.val) ^^^ dot2_4 (a.val >>> 4) (b.val &&& 15)) by
          rw [Nat.and_one_is_mod]; omega]
    rw [bit_xor_zmod2 _ _ h12 h3, bit_and_zmod2 _ _ h1 h2]
  simp only [gammaSgn, gamma4_sgn, hb]
  have hlt : gamma4_bit a.val b.val < 2 := by
    rw [gamma4_bit, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
  generalize gamma4_bit a.val b.val = k at hlt ⊢
  interval_cases k <;> decide

lemma transv4_pt_lt (u v : Fin 256) : transv4_pt u.val v.val < 256 := by
  unfold transv4_pt; split_ifs
  · exact v.isLt
  · exact Nat.xor_lt_two_pow (n := 8) v.isLt u.isLt

lemma transvPt_dec4 (u v : Fin 256) :
    transvPt (dec4 u) (dec4 v) = dec4 ⟨transv4_pt u.val v.val, transv4_pt_lt u v⟩ := by
  have hlt := symp4_lt2 u.val v.val
  by_cases h : symp4 u.val v.val = 0
  · have hpt : (⟨transv4_pt u.val v.val, transv4_pt_lt u v⟩ : Fin 256) = v :=
      Fin.ext (by simp [transv4_pt, h])
    rw [hpt, transvPt, symp_dec4, h]; simp
  · have h1 : symp4 u.val v.val = 1 := by omega
    have hpt : (⟨transv4_pt u.val v.val, transv4_pt_lt u v⟩ : Fin 256) =
        ⟨v.val ^^^ u.val, Nat.xor_lt_two_pow (n := 8) v.isLt u.isLt⟩ :=
      Fin.ext (by simp [transv4_pt, h1])
    rw [hpt, transvPt, symp_dec4, h1]
    simp only [Nat.cast_one, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
    exact (dec4_xor v u).symm

lemma transvSgn_dec4 (u v : Fin 256) : transvSgn (dec4 u) (dec4 v) = transv4_sgn u.val v.val := by
  have hb : transvBit (dec4 u) (dec4 v) = (transv4_bit u.val v.val : ZMod 2) := by
    simp only [transvBit, transv4_bit, symp_dec4, quadForm0_dec4, dot_dec4_fst_snd]
    have hs := symp4_lt2 u.val v.val
    generalize symp4 u.val v.val = k at hs ⊢
    interval_cases k
    · simp
    · simp only [show ((1 : Nat) : ZMod 2) ≠ 0 by decide, ↓reduceIte,
        show (1 == 0) = false by decide, Bool.false_eq_true]
      have h1 := Q4_0_lt2 u.val; have h2 := Q4_0_lt2 v.val; have h3 := dot2_4_lt2 (u.val >>> 4) (v.val &&& 15)
      have ho : Q4_0 u.val ||| Q4_0 v.val < 2 := Nat.or_lt_two_pow (n := 1) h1 h2
      have hx : ((Q4_0 u.val ||| Q4_0 v.val) ^^^ dot2_4 (u.val >>> 4) (v.val &&& 15)) < 2 :=
        Nat.xor_lt_two_pow (n := 1) ho h3
      rw [show (((Q4_0 u.val ||| Q4_0 v.val) ^^^ dot2_4 (u.val >>> 4) (v.val &&& 15)) &&& 1) =
          ((Q4_0 u.val ||| Q4_0 v.val) ^^^ dot2_4 (u.val >>> 4) (v.val &&& 15)) by
            rw [Nat.and_one_is_mod]; omega]
      rw [bit_xor_zmod2 _ _ ho h3, bit_or_zmod2 _ _ h1 h2]
  simp only [transvSgn, transv4_sgn, hb]
  have hlt : transv4_bit u.val v.val < 2 := by
    unfold transv4_bit; split_ifs
    · omega
    · rw [Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
  generalize transv4_bit u.val v.val = k at hlt ⊢
  interval_cases k <;> decide

lemma symp_dec3 (a b : Fin 64) : symp (dec3 a) (dec3 b) = (symp3 a.val b.val : ZMod 2) := by
  simp only [symp, symp3, dot_dec3_fst_snd, dot_dec3_snd_fst]
  exact (bit_xor_zmod2 _ _ (dot2_3_lt2 _ _) (dot2_3_lt2 _ _)).symm

lemma quadForm0_dec3 (a : Fin 64) : quadForm0 (dec3 a) = (Q3_0 a.val : ZMod 2) :=
  dot_dec3_fst_snd a a

lemma quadForm_dec3 (c a : Fin 64) : quadForm (dec3 c) (dec3 a) = (Q3_form c.val a.val : ZMod 2) := by
  simp only [quadForm, Q3_form, quadForm0_dec3, symp_dec3]
  exact (bit_xor_zmod2 _ _ (Q3_0_lt2 _) (symp3_lt2 _ _)).symm

lemma gammaSgn_dec3 (a b : Fin 64) : gammaSgn (dec3 a) (dec3 b) = gamma3_sgn a.val b.val := by
  have hb : gammaBit (dec3 a) (dec3 b) = (gamma3_bit a.val b.val : ZMod 2) := by
    simp only [gammaBit, gamma3_bit, quadForm0_dec3, dot_dec3_fst_snd]
    have h1 := Q3_0_lt2 a.val; have h2 := Q3_0_lt2 b.val; have h3 := dot2_3_lt2 (a.val >>> 3) (b.val &&& 7)
    have h12 : Q3_0 a.val &&& Q3_0 b.val < 2 := Nat.and_lt_two_pow (n := 1) _ h2
    have hx : ((Q3_0 a.val &&& Q3_0 b.val) ^^^ dot2_3 (a.val >>> 3) (b.val &&& 7)) < 2 :=
      Nat.xor_lt_two_pow (n := 1) h12 h3
    rw [show (((Q3_0 a.val &&& Q3_0 b.val) ^^^ dot2_3 (a.val >>> 3) (b.val &&& 7)) &&& 1) =
        ((Q3_0 a.val &&& Q3_0 b.val) ^^^ dot2_3 (a.val >>> 3) (b.val &&& 7)) by
          rw [Nat.and_one_is_mod]; omega]
    rw [bit_xor_zmod2 _ _ h12 h3, bit_and_zmod2 _ _ h1 h2]
  simp only [gammaSgn, gamma3_sgn, hb]
  have hlt : gamma3_bit a.val b.val < 2 := by
    rw [gamma3_bit, Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
  generalize gamma3_bit a.val b.val = k at hlt ⊢
  interval_cases k <;> decide

lemma transv3_pt_lt (u v : Fin 64) : transv3_pt u.val v.val < 64 := by
  unfold transv3_pt; split_ifs
  · exact v.isLt
  · exact Nat.xor_lt_two_pow (n := 6) v.isLt u.isLt

lemma transvPt_dec3 (u v : Fin 64) :
    transvPt (dec3 u) (dec3 v) = dec3 ⟨transv3_pt u.val v.val, transv3_pt_lt u v⟩ := by
  have hlt := symp3_lt2 u.val v.val
  by_cases h : symp3 u.val v.val = 0
  · have hpt : (⟨transv3_pt u.val v.val, transv3_pt_lt u v⟩ : Fin 64) = v :=
      Fin.ext (by simp [transv3_pt, h])
    rw [hpt, transvPt, symp_dec3, h]; simp
  · have h1 : symp3 u.val v.val = 1 := by omega
    have hpt : (⟨transv3_pt u.val v.val, transv3_pt_lt u v⟩ : Fin 64) =
        ⟨v.val ^^^ u.val, Nat.xor_lt_two_pow (n := 6) v.isLt u.isLt⟩ :=
      Fin.ext (by simp [transv3_pt, h1])
    rw [hpt, transvPt, symp_dec3, h1]
    simp only [Nat.cast_one, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
    exact (dec3_xor v u).symm

lemma transvSgn_dec3 (u v : Fin 64) : transvSgn (dec3 u) (dec3 v) = transv3_sgn u.val v.val := by
  have hb : transvBit (dec3 u) (dec3 v) = (transv3_bit u.val v.val : ZMod 2) := by
    simp only [transvBit, transv3_bit, symp_dec3, quadForm0_dec3, dot_dec3_fst_snd]
    have hs := symp3_lt2 u.val v.val
    generalize symp3 u.val v.val = k at hs ⊢
    interval_cases k
    · simp
    · simp only [show ((1 : Nat) : ZMod 2) ≠ 0 by decide, ↓reduceIte,
        show (1 == 0) = false by decide, Bool.false_eq_true]
      have h1 := Q3_0_lt2 u.val; have h2 := Q3_0_lt2 v.val; have h3 := dot2_3_lt2 (u.val >>> 3) (v.val &&& 7)
      have ho : Q3_0 u.val ||| Q3_0 v.val < 2 := Nat.or_lt_two_pow (n := 1) h1 h2
      have hx : ((Q3_0 u.val ||| Q3_0 v.val) ^^^ dot2_3 (u.val >>> 3) (v.val &&& 7)) < 2 :=
        Nat.xor_lt_two_pow (n := 1) ho h3
      rw [show (((Q3_0 u.val ||| Q3_0 v.val) ^^^ dot2_3 (u.val >>> 3) (v.val &&& 7)) &&& 1) =
          ((Q3_0 u.val ||| Q3_0 v.val) ^^^ dot2_3 (u.val >>> 3) (v.val &&& 7)) by
            rw [Nat.and_one_is_mod]; omega]
      rw [bit_xor_zmod2 _ _ ho h3, bit_or_zmod2 _ _ h1 h2]
  simp only [transvSgn, transv3_sgn, hb]
  have hlt : transv3_bit u.val v.val < 2 := by
    unfold transv3_bit; split_ifs
    · omega
    · rw [Nat.and_one_is_mod]; exact Nat.mod_lt _ (by omega)
  generalize transv3_bit u.val v.val = k at hlt ⊢
  interval_cases k <;> decide

/-! ### Section 4: Canonical Center `0x88`, `A_pauli` Isomorphism, & `O⁻(8,2)` Lifting -/

/-- Canonical 4-qubit elliptic center `c₀ = 0x88 = 136`. -/
def c0_88 : PauliIdx 4 := dec4 ⟨136, by decide⟩

/-- Canonical 3-qubit elliptic center `c₃ = 0x09 = 9`. -/
def c0_09 : PauliIdx 3 := dec3 ⟨9, by decide⟩

lemma quadForm0_c0_88 : quadForm0 c0_88 = 1 := by
  rw [c0_88, quadForm0_dec4]; decide

lemma quadForm0_c0_09 : quadForm0 c0_09 = 1 := by
  rw [c0_09, quadForm0_dec3]; decide

def Apauli (p3 : PauliIdx 3) : PauliIdx 4 :=
  dec4 (ApauliFin (enc3 p3))

/-- Pure bitwise coordinate lemmas for `ApauliFin` and `lift34Fin`. -/
private lemma lift34Nat_bit_lo (p3 s : Nat) (hp : p3 < 64) (hs : s < 3) :
    ((lift34Nat p3 >>> s) &&& 1) = (p3 >>> s) &&& 1 := by
  rw [lift34Nat_val_eq p3 hp, Nat.and_one_is_mod, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  interval_cases s <;> norm_num <;> omega

private lemma lift34Nat_bit_hi (p3 s : Nat) (hp : p3 < 64) (hs : s < 3) :
    ((lift34Nat p3 >>> (4 + s)) &&& 1) = (p3 >>> (3 + s)) &&& 1 := by
  rw [lift34Nat_val_eq p3 hp, Nat.and_one_is_mod, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  interval_cases s <;> norm_num <;> omega

private lemma lift34Nat_bit3 (p3 : Nat) (hp : p3 < 64) :
    ((lift34Nat p3 >>> 3) &&& 1) = 0 ∧ ((lift34Nat p3 >>> 7) &&& 1) = 0 := by
  rw [lift34Nat_val_eq p3 hp, Nat.and_one_is_mod, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  norm_num; omega

private lemma dec4_lift34Fin_coords (p3 : Fin 64) :
    (dec4 (lift34Fin p3)).1 0 = (dec3 p3).1 0 ∧
    (dec4 (lift34Fin p3)).1 1 = (dec3 p3).1 1 ∧
    (dec4 (lift34Fin p3)).1 2 = (dec3 p3).1 2 ∧
    (dec4 (lift34Fin p3)).1 3 = 0 ∧
    (dec4 (lift34Fin p3)).2 0 = (dec3 p3).2 0 ∧
    (dec4 (lift34Fin p3)).2 1 = (dec3 p3).2 1 ∧
    (dec4 (lift34Fin p3)).2 2 = (dec3 p3).2 2 ∧
    (dec4 (lift34Fin p3)).2 3 = 0 := by
  have h3 := lift34Nat_bit3 p3.val p3.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (((lift34Nat p3.val >>> 4) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_hi p3.val 0 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 5) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_hi p3.val 1 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 6) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_hi p3.val 2 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 7) &&& 1 : Nat) : ZMod 2) = 0; rw [h3.2]; rfl
  · change (((lift34Nat p3.val >>> 0) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_lo p3.val 0 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 1) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_lo p3.val 1 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 2) &&& 1 : Nat) : ZMod 2) = _; rw [lift34Nat_bit_lo p3.val 2 p3.isLt (by omega)]; rfl
  · change (((lift34Nat p3.val >>> 3) &&& 1 : Nat) : ZMod 2) = 0; rw [h3.1]; rfl

private lemma c0_88_coords :
    c0_88.1 0 = 0 ∧ c0_88.1 1 = 0 ∧ c0_88.1 2 = 0 ∧ c0_88.1 3 = 1 ∧
    c0_88.2 0 = 0 ∧ c0_88.2 1 = 0 ∧ c0_88.2 2 = 0 ∧ c0_88.2 3 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private lemma dec4_ApauliFin_eq (p3 : Fin 64) :
    dec4 (ApauliFin p3) = dec4 (lift34Fin p3) + (if Q3_0 p3.val = 1 then c0_88 else 0) := by
  have hlt := Q3_0_lt2 p3.val
  by_cases hq : Q3_0 p3.val = 1
  · simp only [hq, ↓reduceIte]
    have hfin : ApauliFin p3 = ⟨(lift34Fin p3).val ^^^ (⟨136, by decide⟩ : Fin 256).val,
        Nat.xor_lt_two_pow (n := 8) (lift34Fin p3).isLt (by decide)⟩ := by
      apply Fin.ext; simp [ApauliFin, ApauliNat, lift34Fin, hq]
    rw [hfin]; exact dec4_xor (lift34Fin p3) ⟨136, by decide⟩
  · simp only [hq, ↓reduceIte, add_zero]
    have hq0 : Q3_0 p3.val = 0 := by omega
    have hfin : ApauliFin p3 = lift34Fin p3 := by
      apply Fin.ext; simp [ApauliFin, ApauliNat, lift34Fin, hq0]
    rw [hfin]

private lemma dec4_ApauliFin_coords (p3 : Fin 64) :
    (dec4 (ApauliFin p3)).1 0 = (dec3 p3).1 0 ∧
    (dec4 (ApauliFin p3)).1 1 = (dec3 p3).1 1 ∧
    (dec4 (ApauliFin p3)).1 2 = (dec3 p3).1 2 ∧
    (dec4 (ApauliFin p3)).1 3 = (Q3_0 p3.val : ZMod 2) ∧
    (dec4 (ApauliFin p3)).2 0 = (dec3 p3).2 0 ∧
    (dec4 (ApauliFin p3)).2 1 = (dec3 p3).2 1 ∧
    (dec4 (ApauliFin p3)).2 2 = (dec3 p3).2 2 ∧
    (dec4 (ApauliFin p3)).2 3 = (Q3_0 p3.val : ZMod 2) := by
  rw [dec4_ApauliFin_eq]
  have hl := dec4_lift34Fin_coords p3
  have hc := c0_88_coords
  have hlt := Q3_0_lt2 p3.val
  split_ifs with hq
  · simp [hl, hc, hq]
  · have hq0 : Q3_0 p3.val = 0 := by omega
    simp [hl, hq0]

lemma Apauli_mem_slice {p3 : PauliIdx 3} (hp : p3 ≠ 0) :
    Apauli p3 ∈ slicePts c0_88 c0_88 := by
  have hne : (enc3 p3).val ≠ 0 := fun h => hp (by
    rw [← dec3_enc3 p3]; change dec3 (enc3 p3) = 0
    have : enc3 p3 = 0 := Fin.ext h
    rw [this, dec3_zero])
  have h := ApauliFin_props (enc3 p3)
  rw [slicePts, Finset.mem_filter, Qminus, Finset.mem_filter, nzPts, Finset.mem_erase]
  refine ⟨⟨⟨fun hz => h.1 hne (by
    have := congr_arg enc4 hz; rw [Apauli, enc4_dec4] at this
    have h0 : enc4 0 = ⟨0, by decide⟩ := by rw [← dec4_zero, enc4_dec4]; rfl
    rwa [h0] at this), Finset.mem_univ _⟩, ?_⟩, ?_⟩
  · simp only [Apauli, c0_88, quadForm_dec4, h.2.1]; rfl
  · simp only [Apauli, c0_88, symp_dec4, h.2.2.1]; rfl

lemma dot_Apauli_fst_snd (a b : PauliIdx 3) :
    dot (Apauli a).1 (Apauli b).2 = dot a.1 b.2 + quadForm0 a * quadForm0 b := by
  have ha := dec4_ApauliFin_coords (enc3 a)
  have hb := dec4_ApauliFin_coords (enc3 b)
  simp only [dot, Apauli, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2]
  simp only [dec3_enc3, ← quadForm0_dec3, dec3_enc3]

lemma Apauli_symp (a b : PauliIdx 3) : symp (Apauli a) (Apauli b) = symp a b := by
  simp only [symp, dot_comm (Apauli a).2 (Apauli b).1, dot_Apauli_fst_snd, dot_comm a.2 b.1]
  have h : dot a.1 b.2 + quadForm0 a * quadForm0 b + (dot b.1 a.2 + quadForm0 b * quadForm0 a) =
      dot a.1 b.2 + dot b.1 a.2 + (quadForm0 a * quadForm0 b + quadForm0 a * quadForm0 b) := by ring
  rw [h, zmod2_add_self, add_zero]

lemma Apauli_add_of_comm {a b : PauliIdx 3} (hs : symp a b = 0) :
    Apauli (a + b) = Apauli a + Apauli b := by
  have ha := dec4_ApauliFin_coords (enc3 a)
  have hb := dec4_ApauliFin_coords (enc3 b)
  have hab := dec4_ApauliFin_coords (enc3 (a + b))
  have hQ : quadForm0 (a + b) = quadForm0 a + quadForm0 b := by rw [quadForm0_add, hs, add_zero]
  apply Prod.ext <;> (ext i; fin_cases i)
  · exact hab.1.trans (by simp [dec3_enc3, ha.1, hb.1, Apauli])
  · exact hab.2.1.trans (by simp [dec3_enc3, ha.2.1, hb.2.1, Apauli])
  · exact hab.2.2.1.trans (by simp [dec3_enc3, ha.2.2.1, hb.2.2.1, Apauli])
  · change (dec4 (ApauliFin (enc3 (a + b)))).1 3 =
      (dec4 (ApauliFin (enc3 a))).1 3 + (dec4 (ApauliFin (enc3 b))).1 3
    rw [hab.2.2.2.1, ha.2.2.2.1, hb.2.2.2.1, ← quadForm0_dec3, ← quadForm0_dec3, ← quadForm0_dec3,
      dec3_enc3, dec3_enc3, dec3_enc3, hQ]
  · exact hab.2.2.2.2.1.trans (by simp [dec3_enc3, ha.2.2.2.2.1, hb.2.2.2.2.1, Apauli])
  · exact hab.2.2.2.2.2.1.trans (by simp [dec3_enc3, ha.2.2.2.2.2.1, hb.2.2.2.2.2.1, Apauli])
  · exact hab.2.2.2.2.2.2.1.trans (by simp [dec3_enc3, ha.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, Apauli])
  · change (dec4 (ApauliFin (enc3 (a + b)))).2 3 =
      (dec4 (ApauliFin (enc3 a))).2 3 + (dec4 (ApauliFin (enc3 b))).2 3
    rw [hab.2.2.2.2.2.2.2, ha.2.2.2.2.2.2.2, hb.2.2.2.2.2.2.2,
      ← quadForm0_dec3, ← quadForm0_dec3, ← quadForm0_dec3, dec3_enc3, dec3_enc3, dec3_enc3, hQ]

lemma quadForm0_Apauli (a : PauliIdx 3) : quadForm0 (Apauli a) = 0 := by
  have h := ApauliFin_props (enc3 a)
  have hQ0 : Q4_0 (ApauliFin (enc3 a)).val = 0 := by
    have hq := h.2.1; have hs := h.2.2.1
    simp only [Q4_form, hs, Nat.xor_zero] at hq; exact hq
  simp only [Apauli, quadForm0_dec4, hQ0]; rfl

lemma Apauli_gammaSgn {a b : PauliIdx 3} (_hs : symp a b = 0) :
    gammaSgn (Apauli a) (Apauli b) = gammaSgn a b := by
  simp only [gammaSgn, gammaBit, quadForm0_Apauli, zero_mul, zero_add, dot_Apauli_fst_snd]
  have h : dot a.1 b.2 + quadForm0 a * quadForm0 b = quadForm0 a * quadForm0 b + dot a.1 b.2 := by ring
  rw [h]
  by_cases h0 : quadForm0 a * quadForm0 b + dot a.1 b.2 = 0 <;> simp [h0]

/-- Restrict a 4-qubit sign assignment `s4` to `W(5,2)` via `Apauli`. -/
def restrictA (s4 : PauliIdx 4 → ℤ) : PauliIdx 3 → ℤ :=
  fun p3 => if p3 = 0 then 0 else s4 (Apauli p3)

lemma restrictA_isSignAssign {s4 : PauliIdx 4 → ℤ} (hs4 : IsSignAssign s4) :
    IsSignAssign (restrictA s4) := by
  refine ⟨by simp [restrictA], fun p hp => ?_⟩
  simp only [restrictA, hp, ↓reduceIte]
  have hmem := Apauli_mem_slice hp
  simp only [slicePts, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase] at hmem
  exact hs4.2 (Apauli p) hmem.1.1.1

lemma frustPairs_slice_eq_restrictA (s4 : PauliIdx 4 → ℤ) :
    frustPairs (slicePts c0_88 c0_88) s4 = frustPairs (nzPts 3) (restrictA s4) := by
  symm
  unfold frustPairs
  refine Finset.card_bij (fun pq _ => (Apauli pq.1, Apauli pq.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase, Finset.mem_univ, and_true] at hab ⊢
    rcases hab with ⟨⟨ha, hb⟩, hne, hsymp, hfr⟩
    have hab0 : a + b ≠ 0 := fun h => hne (by
      have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    refine ⟨⟨Apauli_mem_slice ha, Apauli_mem_slice hb⟩, ?_, ?_, ?_⟩
    · intro heq; apply hne
      have h1 := congr_arg (proj43Fin ∘ enc4) heq
      simp only [Function.comp_apply, Apauli, enc4_dec4, (ApauliFin_props _).2.2.2.1] at h1
      exact equiv3.injective h1
    · rw [Apauli_symp, hsymp]
    · rw [Apauli_gammaSgn hsymp, ← Apauli_add_of_comm hsymp]
      simpa [restrictA, ha, hb, hab0] using hfr
  · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    have ha := congr_arg (proj43Fin ∘ enc4) heq.1
    have hb := congr_arg (proj43Fin ∘ enc4) heq.2
    simp only [Function.comp_apply, Apauli, enc4_dec4, (ApauliFin_props _).2.2.2.1] at ha hb
    exact Prod.ext (equiv3.injective ha) (equiv3.injective hb)
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, slicePts, Qminus, nzPts,
      Finset.mem_erase, Finset.mem_univ, and_true] at hpq
    rcases hpq with ⟨⟨⟨⟨hp0, hqp⟩, hsp⟩, ⟨⟨hq0, hqq⟩, hsq⟩⟩, hne, hsymp, hfr⟩
    let a := dec3 (proj43Fin (enc4 p))
    let b := dec3 (proj43Fin (enc4 q))
    have hqp4 : Q4_form 136 (enc4 p).val = 0 := by
      have h : quadForm c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, quadForm_dec4] at h
      have hlt := Q4_form_lt2 136 (enc4 p).val
      generalize Q4_form 136 (enc4 p).val = k at hlt h ⊢; interval_cases k <;> simp_all
    have hsp4 : symp4 136 (enc4 p).val = 0 := by
      have h : symp c0_88 (dec4 (enc4 p)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, symp_dec4] at h
      have hlt := symp4_lt2 136 (enc4 p).val
      generalize symp4 136 (enc4 p).val = k at hlt h ⊢; interval_cases k <;> simp_all
    have hqq4 : Q4_form 136 (enc4 q).val = 0 := by
      have h : quadForm c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, quadForm_dec4] at h
      have hlt := Q4_form_lt2 136 (enc4 q).val
      generalize Q4_form 136 (enc4 q).val = k at hlt h ⊢; interval_cases k <;> simp_all
    have hsq4 : symp4 136 (enc4 q).val = 0 := by
      have h : symp c0_88 (dec4 (enc4 q)) = 0 := by rwa [dec4_enc4]
      rw [c0_88, symp_dec4] at h
      have hlt := symp4_lt2 136 (enc4 q).val
      generalize symp4 136 (enc4 q).val = k at hlt h ⊢; interval_cases k <;> simp_all
    have hAp : Apauli a = p := by
      simp only [Apauli, a, enc3_dec3, ApauliFin_bij_slice _ hqp4 hsp4, dec4_enc4]
    have hAq : Apauli b = q := by
      simp only [Apauli, b, enc3_dec3, ApauliFin_bij_slice _ hqq4 hsq4, dec4_enc4]
    have hAp0 : Apauli 0 = 0 := by
      simp only [Apauli]; rw [show enc3 0 = 0 by rw [← dec3_zero, enc3_dec3]]
      exact dec4_zero
    have ha0 : a ≠ 0 := fun h => hp0 (by rw [← hAp, h, hAp0])
    have hb0 : b ≠ 0 := fun h => hq0 (by rw [← hAq, h, hAp0])
    have hab_ne : a ≠ b := fun h => hne (by rw [← hAp, ← hAq, h])
    have hab_symp : symp a b = 0 := by rw [← Apauli_symp, hAp, hAq, hsymp]
    have hab0 : a + b ≠ 0 := fun h => hab_ne (by
      have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    refine ⟨(a, b), ?_, Prod.ext hAp hAq⟩
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨⟨ha0, hb0⟩, hab_ne, hab_symp, ?_⟩
    rw [← Apauli_gammaSgn hab_symp, hAp, hAq]
    simpa [restrictA, ha0, hb0, hab0, Apauli_add_of_comm hab_symp, hAp, hAq] using hfr

/-- Lift a 3-qubit transvection `T_{u3}` to an `O⁻(8,2)` transvection fixing `c0_88`
    (with optional 4-qubit gauge `lift34(u3)` when `Q3_0(u3) = 0`). -/
def liftTransv3 (u3 : PauliIdx 3) (s4 : PauliIdx 4 → ℤ) : PauliIdx 4 → ℤ :=
  let U : PauliIdx 4 := Apauli u3 + c0_88
  let s4' := applyTransv U s4
  if quadForm0 u3 = 0 then applyGauge (dec4 (lift34Fin (enc3 u3))) s4' else s4'

lemma liftTransv3_Q_and_S (u3 : PauliIdx 3) :
    quadForm c0_88 (Apauli u3 + c0_88) = 1 ∧ symp c0_88 (Apauli u3 + c0_88) = 0 := by
  have hp := ApauliFin_props (enc3 u3)
  have hqA : quadForm c0_88 (Apauli u3) = 0 := by
    simp only [c0_88, Apauli, quadForm_dec4, hp.2.1]; rfl
  have hsA : symp c0_88 (Apauli u3) = 0 := by
    simp only [c0_88, Apauli, symp_dec4, hp.2.2.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [quadForm_add, hqA, quadForm, symp_self, add_zero, quadForm0_c0_88,
      symp_comm (Apauli u3) c0_88, hsA]; simp
  · rw [symp_add_right, hsA, symp_self, add_zero]

lemma liftTransv3_isSignAssign (u3 : PauliIdx 3) {s4 : PauliIdx 4 → ℤ}
    (hs4 : IsSignAssign s4) : IsSignAssign (liftTransv3 u3 s4) := by
  unfold liftTransv3; dsimp only; split_ifs
  · exact applyGauge_isSignAssign _ (applyTransv_isSignAssign _ hs4)
  · exact applyTransv_isSignAssign _ hs4

lemma liftTransv3_restrictA (u3 : PauliIdx 3) (s4 : PauliIdx 4 → ℤ) :
    restrictA (liftTransv3 u3 s4) = applyTransv u3 (restrictA s4) := by
  ext v3
  by_cases hv : v3 = 0
  · subst hv; simp [restrictA, applyTransv, transvPt_zero]
  · have htv : transvPt u3 v3 ≠ 0 := fun h => hv (by rw [← transvPt_invol u3 v3, h, transvPt_zero])
    simp only [restrictA, applyTransv, hv, htv, ↓reduceIte, liftTransv3]
    set U := Apauli u3 + c0_88
    have hsympU : symp U (Apauli v3) = symp u3 v3 := by
      have hsA : symp c0_88 (Apauli v3) = 0 := by
        simp only [c0_88, Apauli, symp_dec4, (ApauliFin_props (enc3 v3)).2.2.1]; rfl
      rw [symp_add_left, Apauli_symp, hsA, add_zero]
    have hpt : transvPt U (Apauli v3) = Apauli (transvPt u3 v3) := by
      simp only [transvPt, hsympU]
      split_ifs with hs
      · rfl
      · have hs1 : symp u3 v3 = 1 := (zmod2_cases (symp u3 v3)).resolve_left hs
        have hu := dec4_ApauliFin_coords (enc3 u3)
        have hvv := dec4_ApauliFin_coords (enc3 v3)
        have hvu := dec4_ApauliFin_coords (enc3 (v3 + u3))
        have hc := c0_88_coords
        have hQ : quadForm0 (v3 + u3) = quadForm0 v3 + quadForm0 u3 + 1 := by
          rw [quadForm0_add, symp_comm, hs1]
        apply Prod.ext <;> (ext i; fin_cases i)
        · change (dec4 (ApauliFin (enc3 v3))).1 0 + ((dec4 (ApauliFin (enc3 u3))).1 0 + c0_88.1 0) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).1 0
          rw [hvv.1, hu.1, hvu.1, hc.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).1 1 + ((dec4 (ApauliFin (enc3 u3))).1 1 + c0_88.1 1) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).1 1
          rw [hvv.2.1, hu.2.1, hvu.2.1, hc.2.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).1 2 + ((dec4 (ApauliFin (enc3 u3))).1 2 + c0_88.1 2) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).1 2
          rw [hvv.2.2.1, hu.2.2.1, hvu.2.2.1, hc.2.2.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).1 3 + ((dec4 (ApauliFin (enc3 u3))).1 3 + c0_88.1 3) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).1 3
          rw [hvv.2.2.2.1, hu.2.2.2.1, hvu.2.2.2.1, hc.2.2.2.1,
            ← quadForm0_dec3, ← quadForm0_dec3, ← quadForm0_dec3, dec3_enc3, dec3_enc3, dec3_enc3, hQ]; ring
        · change (dec4 (ApauliFin (enc3 v3))).2 0 + ((dec4 (ApauliFin (enc3 u3))).2 0 + c0_88.2 0) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).2 0
          rw [hvv.2.2.2.2.1, hu.2.2.2.2.1, hvu.2.2.2.2.1, hc.2.2.2.2.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).2 1 + ((dec4 (ApauliFin (enc3 u3))).2 1 + c0_88.2 1) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).2 1
          rw [hvv.2.2.2.2.2.1, hu.2.2.2.2.2.1, hvu.2.2.2.2.2.1, hc.2.2.2.2.2.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).2 2 + ((dec4 (ApauliFin (enc3 u3))).2 2 + c0_88.2 2) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).2 2
          rw [hvv.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hvu.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, add_zero, dec3_enc3, dec3_enc3, dec3_enc3]; rfl
        · change (dec4 (ApauliFin (enc3 v3))).2 3 + ((dec4 (ApauliFin (enc3 u3))).2 3 + c0_88.2 3) =
            (dec4 (ApauliFin (enc3 (v3 + u3)))).2 3
          rw [hvv.2.2.2.2.2.2.2, hu.2.2.2.2.2.2.2, hvu.2.2.2.2.2.2.2, hc.2.2.2.2.2.2.2,
            ← quadForm0_dec3, ← quadForm0_dec3, ← quadForm0_dec3, dec3_enc3, dec3_enc3, dec3_enc3, hQ]; ring
    have hQU : quadForm0 U = 1 := by
      have hqs := liftTransv3_Q_and_S u3
      have := hqs.1; rw [quadForm, hqs.2, add_zero] at this; exact this
    have hdotUv : dot U.1 (Apauli v3).2 = dot u3.1 v3.2 + (quadForm0 u3 + 1) * quadForm0 v3 := by
      have hu := dec4_ApauliFin_coords (enc3 u3)
      have hvv := dec4_ApauliFin_coords (enc3 v3)
      have hc := c0_88_coords
      simp only [U, dot, Prod.fst_add, Pi.add_apply, Fin.sum_univ_four, Fin.sum_univ_three, Apauli]
      rw [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1,
          hvv.2.2.2.2.1, hvv.2.2.2.2.2.1, hvv.2.2.2.2.2.2.1, hvv.2.2.2.2.2.2.2,
          hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1]
      simp only [dec3_enc3, add_zero, ← quadForm0_dec3, dec3_enc3]
    have hsympG : symp (dec4 (lift34Fin (enc3 u3))) (Apauli v3) = symp u3 v3 := by
      have hl := dec4_lift34Fin_coords (enc3 u3)
      have hvv := dec4_ApauliFin_coords (enc3 v3)
      simp only [symp, dot, Fin.sum_univ_four, Fin.sum_univ_three, Apauli]
      rw [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2.1, hl.2.2.2.2.2.2.2,
          hvv.1, hvv.2.1, hvv.2.2.1, hvv.2.2.2.2.1, hvv.2.2.2.2.2.1, hvv.2.2.2.2.2.2.1]
      simp [dec3_enc3]
    have hbit : transvBit U (Apauli v3) =
        transvBit u3 v3 + (if quadForm0 u3 = 0 then symp u3 v3 else 0) := by
      simp only [transvBit, hsympU, hQU, quadForm0_Apauli, hdotUv]
      rcases zmod2_cases (symp u3 v3) with hs | hs
      · simp [hs]
      · simp only [hs, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
        rcases zmod2_cases (quadForm0 u3) with hq | hq <;>
        rcases zmod2_cases (quadForm0 v3) with hvq | hvq <;>
        simp [hq, hvq] <;> ring_nf <;> simp [zmod2_two_mul, zmod2_mul_two]
    split_ifs with hq
    · simp only [applyGauge, applyTransv, hpt, ← mul_assoc]
      have hsgn : sympSign (dec4 (lift34Fin (enc3 u3))) (Apauli v3) * transvSgn U (Apauli v3) =
          transvSgn u3 v3 := by
        simp only [sympSign, hsympG, transvSgn, hbit, hq, ↓reduceIte]
        rw [sign_zmod2_add]
        rcases zmod2_cases (symp u3 v3) with hs | hs <;>
        rcases zmod2_cases (transvBit u3 v3) with hb | hb <;> simp [hs, hb]
      rw [hsgn]
    · simp only [applyTransv, hpt]
      have hsgn : transvSgn U (Apauli v3) = transvSgn u3 v3 := by
        simp only [transvSgn, hbit, hq, ↓reduceIte, add_zero]
      rw [hsgn]

lemma liftTransv3_preserves_Qminus (u3 : PauliIdx 3) (s4 : PauliIdx 4 → ℤ) :
    frustPairs (Qminus c0_88) (liftTransv3 u3 s4) = frustPairs (Qminus c0_88) s4 := by
  set U := Apauli u3 + c0_88
  have hQU : quadForm c0_88 U = 1 := (liftTransv3_Q_and_S u3).1
  have hQ_fix : frustPairs (Qminus c0_88) (liftTransv3 u3 s4) =
      frustPairs (Qminus c0_88) (applyTransv U s4) := by
    unfold liftTransv3; dsimp only; split_ifs
    · exact frustPairs_applyGauge _ _ _
    · rfl
  rw [hQ_fix]
  refine frustPairs_applyTransv U (Qminus c0_88) (Qminus c0_88) ?_ s4
  intro p
  simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    quadForm_transvPt_fix hQU]
  exact ⟨fun ⟨hp0, hq⟩ => ⟨fun h => hp0 (by rw [← transvPt_invol U p, h, transvPt_zero]), hq⟩,
         fun ⟨htp0, hq⟩ => ⟨fun h => htp0 (by rw [h, transvPt_zero]), hq⟩⟩

lemma liftTransv3_preserves_slice (u3 : PauliIdx 3) (po : PauliIdx 4) (s4 : PauliIdx 4 → ℤ) :
    frustPairs (slicePts c0_88 po) (liftTransv3 u3 s4) =
      frustPairs (slicePts c0_88 (transvPt (Apauli u3 + c0_88) po)) s4 := by
  set U := Apauli u3 + c0_88
  have hQU : quadForm c0_88 U = 1 := (liftTransv3_Q_and_S u3).1
  have hQ_fix : frustPairs (slicePts c0_88 po) (liftTransv3 u3 s4) =
      frustPairs (slicePts c0_88 po) (applyTransv U s4) := by
    unfold liftTransv3; dsimp only; split_ifs
    · exact frustPairs_applyGauge _ _ _
    · rfl
  rw [hQ_fix]
  refine frustPairs_applyTransv U (slicePts c0_88 po) (slicePts c0_88 (transvPt U po)) ?_ s4
  intro p
  simp only [slicePts, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    quadForm_transvPt_fix hQU, symp_transvPt]
  exact ⟨fun ⟨⟨hp0, hq⟩, hs⟩ => ⟨⟨fun h => hp0 (by rw [← transvPt_invol U p, h, transvPt_zero]), hq⟩, hs⟩,
         fun ⟨⟨htp0, hq⟩, hs⟩ => ⟨⟨fun h => htp0 (by rw [h, transvPt_zero]), hq⟩, hs⟩⟩

lemma liftTransv3_preserves_minSlice (u3 : PauliIdx 3) {s4 : PauliIdx 4 → ℤ}
    (hmin : ∀ po ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) s4 ≤ frustPairs (slicePts c0_88 po) s4) :
    ∀ po ∈ outPts c0_88,
      frustPairs (slicePts c0_88 c0_88) (liftTransv3 u3 s4) ≤
      frustPairs (slicePts c0_88 po) (liftTransv3 u3 s4) := by
  set U := Apauli u3 + c0_88
  have hQU : quadForm c0_88 U = 1 := (liftTransv3_Q_and_S u3).1
  have hSU : symp c0_88 U = 0 := (liftTransv3_Q_and_S u3).2
  have hfix : transvPt U c0_88 = c0_88 := by
    simp only [transvPt, symp_comm U c0_88, hSU, ↓reduceIte]
  intro po hpo
  rw [liftTransv3_preserves_slice, liftTransv3_preserves_slice, hfix]
  apply hmin
  simp only [outPts, Finset.mem_filter, Finset.mem_univ, true_and] at hpo ⊢
  rw [quadForm_transvPt_fix hQU]; exact hpo

/-- Lift a word of 3-qubit transvections to 4-qubit `O⁻(8,2)` fixing `c0_88`. -/
def liftTransv3Word : List (PauliIdx 3) → (PauliIdx 4 → ℤ) → (PauliIdx 4 → ℤ)
  | [], s4 => s4
  | u :: us, s4 => liftTransv3Word us (liftTransv3 u s4)

lemma liftTransv3Word_isSignAssign (us : List (PauliIdx 3)) {s4 : PauliIdx 4 → ℤ}
    (hs4 : IsSignAssign s4) : IsSignAssign (liftTransv3Word us s4) := by
  induction us generalizing s4 with
  | nil => exact hs4
  | cons u us ih => exact ih (liftTransv3_isSignAssign u hs4)

lemma liftTransv3Word_restrictA (us : List (PauliIdx 3)) (s4 : PauliIdx 4 → ℤ) :
    restrictA (liftTransv3Word us s4) = applyTransvWord us (restrictA s4) := by
  induction us generalizing s4 with
  | nil => rfl
  | cons u us ih =>
    simp only [liftTransv3Word, applyTransvWord]
    rw [ih, liftTransv3_restrictA]

lemma liftTransv3Word_preserves_Qminus (us : List (PauliIdx 3)) (s4 : PauliIdx 4 → ℤ) :
    frustPairs (Qminus c0_88) (liftTransv3Word us s4) = frustPairs (Qminus c0_88) s4 := by
  induction us generalizing s4 with
  | nil => rfl
  | cons u us ih => rw [liftTransv3Word, ih, liftTransv3_preserves_Qminus]

lemma liftTransv3Word_preserves_minSlice (us : List (PauliIdx 3)) {s4 : PauliIdx 4 → ℤ}
    (hmin : ∀ po ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) s4 ≤ frustPairs (slicePts c0_88 po) s4) :
    ∀ po ∈ outPts c0_88,
      frustPairs (slicePts c0_88 c0_88) (liftTransv3Word us s4) ≤
      frustPairs (slicePts c0_88 po) (liftTransv3Word us s4) := by
  induction us generalizing s4 with
  | nil => exact hmin
  | cons u us ih => exact ih (liftTransv3_preserves_minSlice u hmin)

/-! ### Section 5: `W(5,2)` Frustration Equality Implies 4-Qubit Gauge Equivalence -/

lemma comm_mult_eq_one_of_gens {t : Fin 64 → ℤ}
    (hgen : ∀ v : Fin 64, ([1, 2, 4, 8, 16, 32, 9] : List Nat).contains v.val = true → t v = 1)
    (hmult : ∀ a b : Fin 64, a.val ≠ 0 → b.val ≠ 0 → a ≠ b → symp3 a.val b.val = 0 →
      t a * t b = t ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩) :
    ∀ v : Fin 64, v.val ≠ 0 → t v = 1 := by
  have hinv : ∀ n (k : List Nat),
      (∀ a ∈ k, a ≠ 0 ∧ a < 64) →
      (∀ x : Fin 64, k.contains x.val = true → t x = 1) →
      (∀ a ∈ commReachN n k, a ≠ 0 ∧ a < 64) ∧
      (∀ x : Fin 64, (commReachN n k).contains x.val = true → t x = 1) := by
    intro n
    induction n with
    | zero => intro k hlt hk; exact ⟨hlt, hk⟩
    | succ m ih =>
      intro k hlt hk
      apply ih (commReachStep k)
      · intro a ha
        simp only [commReachStep, List.mem_filter, List.mem_range, Bool.and_eq_true,
          bne_iff_ne, ne_eq] at ha
        exact ⟨ha.2.1, ha.1⟩
      · intro x hx
        simp only [commReachStep, List.contains_eq_mem, List.mem_filter, List.mem_range, x.isLt,
          true_and, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
        rcases hx.2 with hmem | hany
        · exact hk x (by simpa [List.contains_eq_mem] using hmem)
        · rw [List.any_eq_true] at hany
          obtain ⟨a, ha_mem, ha_ok⟩ := hany
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.contains_eq_mem,
            decide_eq_true_eq] at ha_ok
          obtain ⟨⟨⟨hb0, hba⟩, hsymp⟩, hb_mem⟩ := ha_ok
          have ⟨ha0, ha_lt⟩ := hlt a ha_mem
          have ⟨_, hb_lt⟩ := hlt (a ^^^ x.val) hb_mem
          let fa : Fin 64 := ⟨a, ha_lt⟩
          let fb : Fin 64 := ⟨a ^^^ x.val, hb_lt⟩
          have hfab : fa ≠ fb := fun h => hba (congr_arg Fin.val h).symm
          have hmul := hmult fa fb ha0 hb0 hfab hsymp
          have hta : t fa = 1 := hk fa (by simpa [List.contains_eq_mem] using ha_mem)
          have htb : t fb = 1 := hk fb (by simpa [List.contains_eq_mem] using hb_mem)
          have hxor : fa.val ^^^ fb.val = x.val := by
            simp only [fa, fb]
            rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
          have hfx : (⟨fa.val ^^^ fb.val, Nat.xor_lt_two_pow (n := 6) fa.isLt fb.isLt⟩ : Fin 64) = x :=
            Fin.ext hxor
          rw [hfx, hta, htb] at hmul
          linarith
  have hbase_lt : ∀ a ∈ ([1, 2, 4, 8, 16, 32, 9] : List Nat), a ≠ 0 ∧ a < 64 := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  have hres := (hinv 4 [1, 2, 4, 8, 16, 32, 9] hbase_lt hgen).2
  intro v hv
  exact hres v (mem_commReach_all v hv)

/-- **Gauge Lifting Theorem on `W(5,2)`**:
    If `s3, s3'` are two sign assignments on `PauliIdx 3` with identical frustration on every
    commuting pair, then there exists a 4-qubit gauge `G : PauliIdx 4` such that for all `s4`
    with `restrictA s4 = s3`, we have `restrictA (applyGauge G s4) = s3'`! -/
theorem w5_frust_eq_implies_gauge4 {s3 s3' : PauliIdx 3 → ℤ}
    (hs3 : IsSignAssign s3) (hs3' : IsSignAssign s3')
    (heq : ∀ a b : PauliIdx 3, a ≠ 0 → b ≠ 0 → a ≠ b → symp a b = 0 →
      s3 a * s3 b * s3 (a + b) = s3' a * s3' b * s3' (a + b)) :
    ∃ G : PauliIdx 4, ∀ s4 : PauliIdx 4 → ℤ,
      restrictA s4 = s3 → restrictA (applyGauge G s4) = s3' := by
  let d : Fin 64 → ℤ := fun v => s3 (dec3 v) * s3' (dec3 v)
  let bitOf : ℤ → Nat := fun z => if z = 1 then 0 else 1
  let b1 := bitOf (d ⟨1, by decide⟩); let b2 := bitOf (d ⟨2, by decide⟩)
  let b4 := bitOf (d ⟨4, by decide⟩); let b8 := bitOf (d ⟨8, by decide⟩)
  let b16 := bitOf (d ⟨16, by decide⟩); let b32 := bitOf (d ⟨32, by decide⟩)
  have hb1 : b1 < 2 := by simp [b1, bitOf]; split_ifs <;> omega
  have hb2 : b2 < 2 := by simp [b2, bitOf]; split_ifs <;> omega
  have hb4 : b4 < 2 := by simp [b4, bitOf]; split_ifs <;> omega
  have hb8 : b8 < 2 := by simp [b8, bitOf]; split_ifs <;> omega
  have hb16 : b16 < 2 := by simp [b16, bitOf]; split_ifs <;> omega
  have hb32 : b32 < 2 := by simp [b32, bitOf]; split_ifs <;> omega
  let gNat : Nat := b1 * 8 + b2 * 16 + b4 * 32 + b8 + b16 * 2 + b32 * 4
  have hg_lt : gNat < 64 := by dsimp only [gNat]; omega
  let gFin : Fin 64 := ⟨gNat, hg_lt⟩
  let bBit : Nat := symp3 gNat 9 ^^^ bitOf (d ⟨9, by decide⟩)
  let G : PauliIdx 4 := dec4 (lift34Fin gFin) + (if bBit = 1 then dec4 ⟨128, by decide⟩ else 0)
  have hG_symp : ∀ v : Fin 64,
      symp G (Apauli (dec3 v)) =
        ((symp3 gFin.val v.val ^^^ (if bBit = 1 then Q3_0 v.val else 0) : Nat) : ZMod 2) := by
    intro v
    have h1 : symp (dec4 (lift34Fin gFin)) (Apauli (dec3 v)) = symp (dec3 gFin) (dec3 v) := by
      have hl := dec4_lift34Fin_coords gFin
      have hvv := dec4_ApauliFin_coords v
      simp only [symp, dot, Fin.sum_univ_four, Fin.sum_univ_three, Apauli, enc3_dec3]
      rw [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2.1, hl.2.2.2.2.2.2.2,
          hvv.1, hvv.2.1, hvv.2.2.1, hvv.2.2.2.2.1, hvv.2.2.2.2.2.1, hvv.2.2.2.2.2.2.1]; simp
    have h2 : symp (dec4 ⟨128, by decide⟩) (Apauli (dec3 v)) = (Q3_0 v.val : ZMod 2) := by
      simp only [Apauli, enc3_dec3, symp_dec4, (ApauliFin_props v).2.2.2.2]
    simp only [G, symp_add_left, h1, symp_dec3]
    split_ifs with hb
    · rw [h2, bit_xor_zmod2 _ _ (symp3_lt2 _ _) (Q3_0_lt2 _)]
    · simp [symp_zero_left]
  have hc_eq : ∀ v : Fin 64,
      sympSign G (Apauli (dec3 v)) =
        if (symp3 gFin.val v.val ^^^ (if bBit = 1 then Q3_0 v.val else 0)) == 0 then 1 else -1 := by
    intro v
    simp only [sympSign, hG_symp]
    have hlt : symp3 gFin.val v.val ^^^ (if bBit = 1 then Q3_0 v.val else 0) < 2 := by
      have h1 := symp3_lt2 gFin.val v.val
      have h2 : (if bBit = 1 then Q3_0 v.val else 0) < 2 := by split_ifs; exact Q3_0_lt2 v.val; omega
      exact Nat.xor_lt_two_pow (n := 1) h1 h2
    generalize symp3 gFin.val v.val ^^^ (if bBit = 1 then Q3_0 v.val else 0) = k at hlt ⊢
    interval_cases k <;> decide
  let t : Fin 64 → ℤ := fun v => sympSign G (Apauli (dec3 v)) * d v
  have hd_pm1 : ∀ v : Fin 64, v.val ≠ 0 → d v = 1 ∨ d v = -1 := fun v hv => by
    have hv0 : dec3 v ≠ 0 := fun h => hv (by
      have := congr_arg enc3 h; rw [enc3_dec3] at this
      have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      rw [h0] at this; exact congr_arg Fin.val this)
    simp only [d]
    rcases hs3.2 _ hv0 with h1 | h1 <;> rcases hs3'.2 _ hv0 with h2 | h2 <;> simp [h1, h2]
  have hbit_of_pm1 : ∀ z : ℤ, (z = 1 ∨ z = -1) → (if bitOf z == 0 then (1 : ℤ) else -1) = z := by
    rintro z (rfl | rfl) <;> decide
  have hgs := checkBasisSymp3_sound 64 gNat hg_lt checkBasisSymp3_ok
  have hs1 : symp3 gNat 1 = b1 := by
    rw [hgs.1, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [gNat]; norm_num; omega
  have hs2 : symp3 gNat 2 = b2 := by
    rw [hgs.2.1, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [gNat]; norm_num; omega
  have hs4 : symp3 gNat 4 = b4 := by
    rw [hgs.2.2.1, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [gNat]; norm_num; omega
  have hs8 : symp3 gNat 8 = b8 := by
    rw [hgs.2.2.2.1, Nat.and_one_is_mod]; dsimp only [gNat]; omega
  have hs16 : symp3 gNat 16 = b16 := by
    rw [hgs.2.2.2.2.1, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [gNat]; norm_num; omega
  have hs32 : symp3 gNat 32 = b32 := by
    rw [hgs.2.2.2.2.2, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; dsimp only [gNat]; norm_num; omega
  have ht_gen : ∀ v : Fin 64, ([1, 2, 4, 8, 16, 32, 9] : List Nat).contains v.val = true → t v = 1 := by
    intro v hv
    have hv_cases : v.val = 1 ∨ v.val = 2 ∨ v.val = 4 ∨ v.val = 8 ∨ v.val = 16 ∨ v.val = 32 ∨ v.val = 9 := by
      simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
        decide_eq_true_eq] at hv
      exact hv
    have hmul_self : ∀ z : ℤ, (z = 1 ∨ z = -1) → z * z = 1 := by rintro z (rfl | rfl) <;> norm_num
    simp only [t, hc_eq]
    rcases hv_cases with h | h | h | h | h | h | h
    · have hv' : v = ⟨1, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 1 = 0 by decide, ite_self, Nat.xor_zero, hs1, b1]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨2, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 2 = 0 by decide, ite_self, Nat.xor_zero, hs2, b2]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨4, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 4 = 0 by decide, ite_self, Nat.xor_zero, hs4, b4]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨8, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 8 = 0 by decide, ite_self, Nat.xor_zero, hs8, b8]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨16, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 16 = 0 by decide, ite_self, Nat.xor_zero, hs16, b16]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨32, by decide⟩ := Fin.ext h
      rw [hv']; simp only [gFin, show Q3_0 32 = 0 by decide, ite_self, Nat.xor_zero, hs32, b32]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
    · have hv' : v = ⟨9, by decide⟩ := Fin.ext h
      rw [hv']
      have hq9 : Q3_0 9 = 1 := by decide
      have hxor9 : symp3 gNat 9 ^^^ (if bBit = 1 then 1 else 0) = bitOf (d ⟨9, by decide⟩) := by
        have h1 := symp3_lt2 gNat 9
        have h2 : bitOf (d ⟨9, by decide⟩) < 2 := by simp [bitOf]; split_ifs <;> omega
        change symp3 gNat 9 ^^^ (if symp3 gNat 9 ^^^ bitOf (d ⟨9, by decide⟩) = 1 then 1 else 0) =
          bitOf (d ⟨9, by decide⟩)
        generalize symp3 gNat 9 = x at h1 ⊢
        generalize bitOf (d ⟨9, by decide⟩) = y at h2 ⊢
        interval_cases x <;> interval_cases y <;> decide
      simp only [gFin, hq9, hxor9]
      rw [hbit_of_pm1 _ (hd_pm1 _ (by decide))]; exact hmul_self _ (hd_pm1 _ (by decide))
  have ht_mult : ∀ a b : Fin 64, a.val ≠ 0 → b.val ≠ 0 → a ≠ b → symp3 a.val b.val = 0 →
      t a * t b = t ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ := by
    intro a b ha hb hab hs
    have ha0 : dec3 a ≠ 0 := fun h => ha (by
      have := congr_arg enc3 h; rw [enc3_dec3] at this
      have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      rw [h0] at this; exact congr_arg Fin.val this)
    have hb0 : dec3 b ≠ 0 := fun h => hb (by
      have := congr_arg enc3 h; rw [enc3_dec3] at this
      have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      rw [h0] at this; exact congr_arg Fin.val this)
    have hab0 : dec3 a ≠ dec3 b := fun h => hab (equiv3.symm.injective h)
    have hsp : symp (dec3 a) (dec3 b) = 0 := by rw [symp_dec3, hs]; rfl
    have he := heq (dec3 a) (dec3 b) ha0 hb0 hab0 hsp
    have hdec_ab : dec3 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ = dec3 a + dec3 b :=
      dec3_xor a b
    have hcab : sympSign G (Apauli (dec3 a)) * sympSign G (Apauli (dec3 b)) =
        sympSign G (Apauli (dec3 a + dec3 b)) := by
      rw [Apauli_add_of_comm hsp, sympSign_add_right]
    have hdab : d a * d b = d ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ := by
      simp only [d, hdec_ab]
      have h1 : s3 (dec3 a + dec3 b) * s3 (dec3 a + dec3 b) = 1 := by
        have hab_ne0 : dec3 a + dec3 b ≠ 0 := fun h => hab0 (by
          have := congr_arg (dec3 a + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
        rcases hs3.2 _ hab_ne0 with h | h <;> rw [h] <;> norm_num
      have h2 : s3' (dec3 a) * s3' (dec3 a) = 1 := by
        rcases hs3'.2 _ ha0 with h | h <;> rw [h] <;> norm_num
      have h3 : s3' (dec3 b) * s3' (dec3 b) = 1 := by
        rcases hs3'.2 _ hb0 with h | h <;> rw [h] <;> norm_num
      have hmul : (s3 (dec3 a) * s3 (dec3 b) * s3 (dec3 a + dec3 b)) *
          (s3' (dec3 a) * s3' (dec3 b) * s3 (dec3 a + dec3 b)) =
          (s3' (dec3 a) * s3' (dec3 b) * s3' (dec3 a + dec3 b)) *
          (s3' (dec3 a) * s3' (dec3 b) * s3 (dec3 a + dec3 b)) := by rw [he]
      calc s3 (dec3 a) * s3' (dec3 a) * (s3 (dec3 b) * s3' (dec3 b))
          = (s3 (dec3 a) * s3 (dec3 b) * s3 (dec3 a + dec3 b)) *
              (s3' (dec3 a) * s3' (dec3 b) * s3 (dec3 a + dec3 b)) := by
                have : s3 (dec3 a) * s3' (dec3 a) * (s3 (dec3 b) * s3' (dec3 b)) *
                    (s3 (dec3 a + dec3 b) * s3 (dec3 a + dec3 b)) =
                    (s3 (dec3 a) * s3 (dec3 b) * s3 (dec3 a + dec3 b)) *
                    (s3' (dec3 a) * s3' (dec3 b) * s3 (dec3 a + dec3 b)) := by ring
                rw [← this, h1, mul_one]
        _ = (s3' (dec3 a) * s3' (dec3 b) * s3' (dec3 a + dec3 b)) *
              (s3' (dec3 a) * s3' (dec3 b) * s3 (dec3 a + dec3 b)) := hmul
        _ = (s3' (dec3 a) * s3' (dec3 a)) * (s3' (dec3 b) * s3' (dec3 b)) *
              (s3 (dec3 a + dec3 b) * s3' (dec3 a + dec3 b)) := by ring
        _ = s3 (dec3 a + dec3 b) * s3' (dec3 a + dec3 b) := by rw [h2, h3]; ring
    simp only [t, hdec_ab]
    calc sympSign G (Apauli (dec3 a)) * d a * (sympSign G (Apauli (dec3 b)) * d b)
        = (sympSign G (Apauli (dec3 a)) * sympSign G (Apauli (dec3 b))) * (d a * d b) := by ring
      _ = sympSign G (Apauli (dec3 a + dec3 b)) * d ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 6) a.isLt b.isLt⟩ := by
            rw [hcab, hdab]
  have ht_one := comm_mult_eq_one_of_gens ht_gen ht_mult
  refine ⟨G, fun s4 hs4 => ?_⟩
  ext p
  by_cases hp : p = 0
  · subst hp; simp [restrictA, hs3'.1]
  · have hne : (enc3 p).val ≠ 0 := fun h => hp (by
      rw [← dec3_enc3 p]; change dec3 (enc3 p) = 0
      rw [show enc3 p = 0 from Fin.ext h, dec3_zero])
    have ht1 := ht_one (enc3 p) hne
    simp only [t, d, dec3_enc3] at ht1
    have hs4p : s4 (Apauli p) = s3 p := by
      have := congr_fun hs4 p; simpa [restrictA, hp] using this
    have hs3'sq : s3' p * s3' p = 1 := by rcases hs3'.2 p hp with h | h <;> rw [h] <;> norm_num
    simp only [restrictA, hp, ↓reduceIte, applyGauge, hs4p]
    calc sympSign G (Apauli p) * s3 p
        = (sympSign G (Apauli p) * (s3 p * s3' p)) * s3' p := by
            have : (sympSign G (Apauli p) * (s3 p * s3' p)) * s3' p =
                sympSign G (Apauli p) * s3 p * (s3' p * s3' p) := by ring
            rw [this, hs3'sq, mul_one]
      _ = 1 * s3' p := by rw [ht1]
      _ = s3' p := one_mul _

/-! ### Section 6: Part 0 Reduction Theorem (`signCubeSum_le_6615_of_minSlice`) -/

lemma exists_Ominus_word_pout_to_88 {po : PauliIdx 4} (hpo : po ∈ outPts c0_88) :
    ∃ us : List (PauliIdx 4),
      (∀ u ∈ us, quadForm c0_88 u = 1) ∧
      (∀ s4 : PauliIdx 4 → ℤ,
        frustPairs (Qminus c0_88) (applyTransvWord us s4) = frustPairs (Qminus c0_88) s4 ∧
        frustPairs (slicePts c0_88 c0_88) (applyTransvWord us s4) = frustPairs (slicePts c0_88 po) s4 ∧
        ((∀ q ∈ outPts c0_88, frustPairs (slicePts c0_88 po) s4 ≤ frustPairs (slicePts c0_88 q) s4) →
          ∀ q ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) (applyTransvWord us s4) ≤
            frustPairs (slicePts c0_88 q) (applyTransvWord us s4))) := by
  have hpoQ : Q4_form 136 (enc4 po).val = 1 := by
    simp only [outPts, Finset.mem_filter, Finset.mem_univ, true_and] at hpo
    have h : quadForm c0_88 (dec4 (enc4 po)) = 1 := by rwa [dec4_enc4]
    rw [c0_88, quadForm_dec4] at h
    have hlt := Q4_form_lt2 136 (enc4 po).val
    generalize Q4_form 136 (enc4 po).val = k at hlt h ⊢; interval_cases k <;> simp_all
  have h1step : ∀ (u : PauliIdx 4) (hu : quadForm c0_88 u = 1) (s4 : PauliIdx 4 → ℤ) (q : PauliIdx 4),
      frustPairs (Qminus c0_88) (applyTransv u s4) = frustPairs (Qminus c0_88) s4 ∧
      frustPairs (slicePts c0_88 q) (applyTransv u s4) = frustPairs (slicePts c0_88 (transvPt u q)) s4 := by
    intro u hu s4 q
    constructor
    · refine frustPairs_applyTransv u (Qminus c0_88) (Qminus c0_88) (fun p => ?_) s4
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        quadForm_transvPt_fix hu]
      exact ⟨fun ⟨hp0, h⟩ => ⟨fun hc => hp0 (by rw [← transvPt_invol u p, hc, transvPt_zero]), h⟩,
             fun ⟨ht0, h⟩ => ⟨fun hc => ht0 (by rw [hc, transvPt_zero]), h⟩⟩
    · refine frustPairs_applyTransv u (slicePts c0_88 q) (slicePts c0_88 (transvPt u q)) (fun p => ?_) s4
      simp only [slicePts, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        quadForm_transvPt_fix hu, symp_transvPt]
      exact ⟨fun ⟨⟨hp0, h⟩, hs⟩ => ⟨⟨fun hc => hp0 (by rw [← transvPt_invol u p, hc, transvPt_zero]), h⟩, hs⟩,
             fun ⟨⟨ht0, h⟩, hs⟩ => ⟨⟨fun hc => ht0 (by rw [hc, transvPt_zero]), h⟩, hs⟩⟩
  rcases pout_exists_transv_to_88 (enc4 po) hpoQ with heq | ⟨hq1, htv1⟩ | ⟨uNat, huMem, hqu, hsu, hq2, htv2⟩
  · refine ⟨[], fun _ h => by simp at h, fun s4 => ?_⟩
    have hpe : po = c0_88 := by
      apply equiv4.injective
      change enc4 po = enc4 (dec4 ⟨136, by decide⟩)
      rw [enc4_dec4]; exact Fin.ext heq
    subst hpe; exact ⟨rfl, rfl, id⟩
  · let uFin : Fin 256 := ⟨(enc4 po).val ^^^ 136, Nat.xor_lt_two_pow (n := 8) (enc4 po).isLt (by decide)⟩
    let u := dec4 uFin
    have huQ : quadForm c0_88 u = 1 := by rw [c0_88, quadForm_dec4, hq1]; rfl
    have htu : transvPt u c0_88 = po := by
      have ht : transvPt u po = c0_88 := by
        rw [← dec4_enc4 po, transvPt_dec4, c0_88]; congr 1; exact Fin.ext htv1
      rw [← ht, transvPt_invol]
    refine ⟨[u], fun x hx => by simp at hx; rw [hx]; exact huQ, fun s4 => ?_⟩
    simp only [applyTransvWord]
    refine ⟨(h1step u huQ s4 c0_88).1, ?_, ?_⟩
    · rw [(h1step u huQ s4 c0_88).2, htu]
    · intro hmin q hq
      rw [(h1step u huQ s4 c0_88).2, (h1step u huQ s4 q).2, htu]
      apply hmin
      simp only [outPts, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [quadForm_transvPt_fix huQ]; exact hq
  · have hu_lt : uNat < 256 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at huMem; omega
    let u1Fin : Fin 256 := ⟨uNat, hu_lt⟩
    let po1Fin : Fin 256 := ⟨(enc4 po).val ^^^ uNat, Nat.xor_lt_two_pow (n := 8) (enc4 po).isLt hu_lt⟩
    let u2Fin : Fin 256 := ⟨po1Fin.val ^^^ 136, Nat.xor_lt_two_pow (n := 8) po1Fin.isLt (by decide)⟩
    let u1 := dec4 u1Fin; let u2 := dec4 u2Fin
    have hu1Q : quadForm c0_88 u1 = 1 := by rw [c0_88, quadForm_dec4, hqu]; rfl
    have hu2Q : quadForm c0_88 u2 = 1 := by rw [c0_88, quadForm_dec4, hq2]; rfl
    have ht1 : transvPt u1 po = dec4 po1Fin := by
      rw [← dec4_enc4 po, transvPt_dec4]; congr 1; apply Fin.ext
      simp only [transv4_pt, u1Fin, po1Fin, hsu, show (1 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
    have ht2 : transvPt u2 (dec4 po1Fin) = c0_88 := by
      rw [transvPt_dec4, c0_88]; congr 1; exact Fin.ext htv2
    have hcomp : transvPt u1 (transvPt u2 c0_88) = po := by
      rw [← ht2, transvPt_invol, ← ht1, transvPt_invol]
    refine ⟨[u1, u2], fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl; exact hu1Q; exact hu2Q, fun s4 => ?_⟩
    simp only [applyTransvWord]
    refine ⟨?_, ?_, ?_⟩
    · rw [(h1step u2 hu2Q _ c0_88).1, (h1step u1 hu1Q s4 c0_88).1]
    · rw [(h1step u2 hu2Q _ c0_88).2, (h1step u1 hu1Q s4 _).2, hcomp]
    · intro hmin q hq
      rw [(h1step u2 hu2Q _ c0_88).2, (h1step u1 hu1Q s4 _).2, hcomp,
          (h1step u2 hu2Q _ q).2, (h1step u1 hu1Q s4 _).2]
      apply hmin
      simp only [outPts, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [quadForm_transvPt_fix hu1Q, quadForm_transvPt_fix hu2Q]; exact hq

/-- **Master Part 0 Reduction**:
    To prove `∀ σ, signCubeSum 4 σ ≤ 6615`, it suffices to show NO valid `s4 : PauliIdx 4 → ℤ`
    simultaneously satisfies `f_Q < 315`, min-slice at `c0_88` (`f_A ≤ 92`), and min-`Q⁻(5,2)` at `c0_09` (`f_27 ≤ 13`). -/
theorem signCubeSum_le_6615_of_minSlice
    (hmain : ∀ s4 : PauliIdx 4 → ℤ, IsSignAssign s4 →
      frustPairs (Qminus c0_88) s4 < 315 * 6 →
      (∀ po ∈ outPts c0_88, frustPairs (slicePts c0_88 c0_88) s4 ≤ frustPairs (slicePts c0_88 po) s4) →
      frustPairs (nzPts 3) (restrictA s4) ≤ 92 * 6 →
      (∀ c3 ∈ ellCenters 3, frustPairs (Qminus c0_09) (restrictA s4) ≤ frustPairs (Qminus c3) (restrictA s4)) →
      frustPairs (Qminus c0_09) (restrictA s4) ≤ 13 * 6 →
      False) :
    ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615 := by
  have hQ315 : ∀ s4 : PauliIdx 4 → ℤ, IsSignAssign s4 → 315 * 6 ≤ frustPairs (Qminus c0_88) s4 := by
    intro s4 hs4
    by_contra hlt; push Not at hlt
    have hne_out : (outPts c0_88).Nonempty := ⟨c0_88, by
      rw [outPts, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [quadForm, symp_self, add_zero]; exact quadForm0_c0_88⟩⟩
    obtain ⟨po, hpo_mem, hpo_min⟩ := Finset.exists_min_image (outPts c0_88)
      (fun p => frustPairs (slicePts c0_88 p) s4) hne_out
    obtain ⟨us4, _, hus4⟩ := exists_Ominus_word_pout_to_88 hpo_mem
    let s4' := applyTransvWord us4 s4
    have hs4' : IsSignAssign s4' := applyTransvWord_isSignAssign us4 hs4
    obtain ⟨hQeq, _, hmin'⟩ := hus4 s4
    have hmin_s4' := hmin' hpo_min
    have hQlt' : frustPairs (Qminus c0_88) s4' < 315 * 6 := by rw [hQeq]; exact hlt
    have hcard_out : (outPts c0_88).card = 136 := by
      have hcardQ := card_elliptic_quadric (n := 4) (by norm_num) quadForm0_c0_88
      have h256 : (Finset.univ : Finset (PauliIdx 4)).card = 256 := by
        rw [Finset.card_univ, card_PauliIdx]; norm_num
      have hpart : (outPts c0_88).card + (Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0).card = 256 := by
        rw [← h256, ← Finset.card_union_of_disjoint]
        · refine congr_arg Finset.card (Finset.ext fun p => ?_)
          simp only [outPts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases zmod2_cases (quadForm c0_88 p) with h | h <;> simp [h]
        · rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [outPts, Finset.mem_filter] at hp1 hp2
          rw [hp1.2] at hp2; exact absurd hp2.2 (by decide)
      have hQ0 : (Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0).card =
          (Finset.univ.filter fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0_88 p = 0).card + 1 := by
        have hmem0 : (0 : PauliIdx 4) ∈ Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0 := by
          simp [quadForm_zero]
        rw [← Finset.card_erase_add_one hmem0]
        refine congr_arg (· + 1) (congr_arg Finset.card (Finset.ext fun p => ?_))
        simp [and_comm]
      have h119 : (Finset.univ.filter fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0_88 p = 0).card = 119 := by
        norm_num at hcardQ; exact_mod_cast hcardQ
      omega
    have hsum_sl : 136 * frustPairs (slicePts c0_88 c0_88) s4' ≤ 40 * frustPairs (Qminus c0_88) s4' := by
      rw [double_count_Qminus72_slices quadForm0_c0_88 s4', ← hcard_out, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun p hp => hmin_s4' p hp
    have hdvd_Q : 6 ∣ frustPairs (Qminus c0_88) s4' := by
      refine dvd_six_frustPairs (Qminus c0_88) (by simp [Qminus, nzPts]) ?_ s4'
      intro p hp q hq hne hs
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
      refine ⟨fun h => hne (by
        have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm), ?_⟩
      rw [quadForm_add, hp.2, hq.2, hs]; simp
    have hdvd_A : 6 ∣ frustPairs (nzPts 3) (restrictA s4') := by
      refine dvd_six_frustPairs (nzPts 3) (by simp [nzPts]) ?_ (restrictA s4')
      intro p _ q _ hne _
      simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
      intro h; exact hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    rw [frustPairs_slice_eq_restrictA] at hsum_sl
    have hfA_le : frustPairs (nzPts 3) (restrictA s4') ≤ 92 * 6 := by
      obtain ⟨kQ, hkQ⟩ := hdvd_Q
      obtain ⟨kA, hkA⟩ := hdvd_A
      omega
    have hne_c3 : (ellCenters 3).Nonempty := ⟨c0_09, by
      rw [ellCenters, Finset.mem_filter]; exact ⟨Finset.mem_univ _, quadForm0_c0_09⟩⟩
    obtain ⟨c3, hc3_mem, hc3_min⟩ := Finset.exists_min_image (ellCenters 3)
      (fun c => frustPairs (Qminus c) (restrictA s4')) hne_c3
    let s4'' := liftTransv3 (c3 + c0_09) s4'
    have hs4'' : IsSignAssign s4'' := liftTransv3_isSignAssign _ hs4'
    have hQlt'' : frustPairs (Qminus c0_88) s4'' < 315 * 6 := by
      rw [liftTransv3_preserves_Qminus]; exact hQlt'
    have hmin'' := liftTransv3_preserves_minSlice (c3 + c0_09) hmin_s4'
    have hres'' : restrictA s4'' = applyTransv (c3 + c0_09) (restrictA s4') :=
      liftTransv3_restrictA _ _
    have hfA_eq'' : frustPairs (nzPts 3) (restrictA s4'') = frustPairs (nzPts 3) (restrictA s4') := by
      rw [hres'']
      refine frustPairs_applyTransv (c3 + c0_09) (nzPts 3) (nzPts 3) (fun p => ?_) (restrictA s4')
      simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hp0 h => hp0 (by rw [← transvPt_invol _ p, h, transvPt_zero]),
             fun ht0 h => ht0 (by rw [h, transvPt_zero])⟩
    have hfA_le'' : frustPairs (nzPts 3) (restrictA s4'') ≤ 92 * 6 := by rw [hfA_eq'']; exact hfA_le
    have hc3_Q0 : quadForm0 c3 = 1 := (Finset.mem_filter.mp hc3_mem).2
    have hmin_c3'' : ∀ c ∈ ellCenters 3,
        frustPairs (Qminus c0_09) (restrictA s4'') ≤ frustPairs (Qminus c) (restrictA s4'') := by
      intro c hc
      rw [hres'', ← frustPairs_Qminus_eq_of_ellCenter hc3_Q0 quadForm0_c0_09]
      let u := c3 + c0_09
      rcases zmod2_cases (quadForm c u) with hcu | hcu
      · have hc'_mem : c + u ∈ ellCenters 3 := by
          simp only [ellCenters, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
          have hq : quadForm c u = 0 := hcu
          rw [quadForm0_add, hc]
          have : quadForm0 u + symp c u = 0 := hq
          rw [add_assoc, this, add_zero]
        have hmap : frustPairs (Qminus c) (applyTransv u (restrictA s4')) =
            frustPairs (Qminus (c + u)) (restrictA s4') := by
          refine frustPairs_applyTransv u (Qminus c) (Qminus (c + u)) (fun p => ?_) _
          simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
          have hm : quadForm (c + u) (transvPt u p) = quadForm c p := by
            have := quadForm_transvPt_move hcu (transvPt u p)
            rw [transvPt_invol] at this; exact this.symm
          rw [hm]
          exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
                 fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
        rw [hmap]; exact hc3_min (c + u) hc'_mem
      · have hmap : frustPairs (Qminus c) (applyTransv u (restrictA s4')) =
            frustPairs (Qminus c) (restrictA s4') := by
          refine frustPairs_applyTransv u (Qminus c) (Qminus c) (fun p => ?_) _
          simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
            quadForm_transvPt_fix hcu]
          exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
                 fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
        rw [hmap]; exact hc3_min c hc
    have hcard_c3 : (ellCenters 3).card = 28 := by
      have hZ := card_elliptic_centers (n := 3) (by norm_num)
      norm_num at hZ; exact_mod_cast hZ
    have hsum_28 : 28 * frustPairs (Qminus c0_09) (restrictA s4'') ≤ 4 * frustPairs (nzPts 3) (restrictA s4'') := by
      rw [double_count_W52_Qminus52, ← hcard_c3, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun c hc => hmin_c3'' c hc
    have hdvd_27 : 6 ∣ frustPairs (Qminus c0_09) (restrictA s4'') := by
      refine dvd_six_frustPairs (Qminus c0_09) (by simp [Qminus, nzPts]) ?_ _
      intro p hp q hq hne hs
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
      refine ⟨fun h => hne (by
        have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm), ?_⟩
      rw [quadForm_add, hp.2, hq.2, hs]; simp
    have hf27_le : frustPairs (Qminus c0_09) (restrictA s4'') ≤ 13 * 6 := by
      obtain ⟨k27, hk27⟩ := hdvd_27
      omega
    exact hmain s4'' hs4'' hQlt'' hmin'' hfA_le'' hmin_c3'' hf27_le
  intro σ h0 hpm
  obtain ⟨hs, hsum⟩ := signCubeSum_eq_frustPairs h0 hpm
  set s : PauliIdx 4 → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
  have hcard120 : (ellCenters 4).card = 120 := by
    have hZ := card_elliptic_centers (n := 4) (by norm_num)
    norm_num at hZ; exact_mod_cast hZ
  have h120_lb : 120 * (315 * 6) ≤ 24 * frustPairs (nzPts 4) s := by
    rw [double_count_W72_Qminus, ← hcard120, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun c hc => ?_
    have hcQ : quadForm0 c = 1 := (Finset.mem_filter.mp hc).2
    rw [frustPairs_Qminus_eq_of_ellCenter hcQ quadForm0_c0_88]
    exact hQ315 _ (applyTransv_isSignAssign _ hs)
  have hfW_lb : (9450 : ℕ) ≤ frustPairs (nzPts 4) s := by omega
  have hfW_R : (9450 : ℝ) ≤ (frustPairs (nzPts 4) s : ℝ) := by exact_mod_cast hfW_lb
  linarith

end PauliIdxSection

end FourQubitCD

end MultiQubitMUB
