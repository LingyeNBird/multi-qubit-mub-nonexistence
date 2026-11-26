import MultiQubitMUB.PauliGroup
import MultiQubitMUB.SpikeFamily

/-!
# Exact Degree-6 Rational SOS Lower Bound for Two-Qubit Pure States: `F₂(|ψ⟩) ≥ 12/7`

Proves in complete generality for EVERY 2-qubit unit pure state `|ψ⟩ ∈ (ℂ²)⊗²`
(zero `sorry`, zero `native_decide`, standard three Lean axioms only):

  `pauliMoment4_two_ge_twelve_sevenths : ∀ ψ : QState 2, IsUnitState ψ → (12 / 7 : ℝ) ≤ pauliMoment4 2 ψ`

This achieves the exact global optimum of the full degree-6 Clifford-invariant SOS / Lasserre
hierarchy (`M₃` / `T₁₂` / `Sym⁶` on `Cl₂`), upgrading the previous bound `1.634` in
`GeneralLowerBound.lean` to the exact rational `12 / 7 ≈ 1.714286` (vs. Welch `8 / 5 = 1.600`
and true 2-qubit minimum `7 / 4 = 1.750` at the 2-qubit MUB fiducial).

## Proof Architecture (Three Elementary Pauli SOS Identities)

Let `c p = ⟨ψ | P_p | ψ⟩ ∈ ℝ`, `g p = c p ^ 2`, `F₄ = ∑_p g_p²`, `F₆ = ∑_p g_p³`, and
`T_ord = ∑_{p≠0, q≠0, p≠q, ω(p,q)=0} g_p g_q g_{p+q}` (`= 6 T₂₂₂`). Using only:
- `pauli_symp_self_dual` (`W g = 4 g`),
- `pauli_purity_identity` (`ρ² = ρ` in Pauli basis), and
- `pauli_prod_eq_conv` (`4 c_a c_b = ∑_p Re(Tr(P_a P_p P_b P_{a+p+b})/4) c_p c_{a+p+b}`),

we establish three exact nonnegativity identities:
1. **`sos_B_nonneg`**:
   `∑_{ω(p,q)=1} g_p (g_q - g_{p+q})² = 10 F₄ - 12 F₆ + 2 T_ord - 4 ≥ 0`
2. **`sos_C_nonneg`**:
   `∑_{s≠0} ∑_{p ∈ s^⊥ \ {0,s}} (3 R(s, p) - c_s (7 + 9 g_s))² = 6 (162 F₆ + 243 T_ord - 93 F₄ - 198) ≥ 0`
   where `R(s, p) = 9 c_s (g_p + g_{s+p}) - 2 γ(s, p) c_p c_{s+p}`.
3. **`sos_A_nonneg`**:
   `∑_{ω(s,r)=1} (∑_{u ∈ T(s,r)} c_u ∑_{v ∈ T(s,r)\{u}} (y_v y_{s+u+v} - z_v z_{s+u+v}))² = 4 (28 F₄ - 12 T_ord - 40) ≥ 0`
   where `T(s, r) = {u ∈ s^⊥ \ {0, s} | ω(r, u) = 1}`, `y_v = Im(pauliPhase r v) c_{r+v}`,
   and `z_v = Im(pauliPhase (r+s) v) c_{r+s+v}`.

The positive integer linear combination
  `45 * (28 F₄ - 12 T_ord - 40) + 27 * (10 F₄ - 12 F₆ + 2 T_ord - 4) + 2 * (162 F₆ + 243 T_ord - 93 F₄ - 198) = 1344 F₄ - 2304 ≥ 0`
eliminates `F₆` and `T_ord` identically and yields `pauliMoment4 2 ψ ≥ 2304 / 1344 = 12 / 7`.
-/

namespace MultiQubitMUB

namespace TwoQubitSOS

/-! ### Step 1: Computable Integer Phase Functions & General-`n` Pauli Phase Algebra -/

/-- Exact integer real part of `pauliPhase p q`: `±1` when `symp p q = 0`, `0` when `symp p q = 1`. -/
def phaseRe {n : ℕ} (p q : PauliIdx n) : ℤ :=
  if symp p q = 0 then
    (if dot p.1 p.2 = 1 ∧ dot q.1 q.2 = 1 then -1 else 1) * chi q.2 p.1
  else 0

/-- Exact integer imaginary part of `pauliPhase p q`: `±1` when `symp p q = 1`, `0` when `symp p q = 0`. -/
def phaseIm {n : ℕ} (p q : PauliIdx n) : ℤ :=
  if symp p q = 1 then
    (if dot p.1 p.2 = 0 ∧ dot q.1 q.2 = 0 then -1 else 1) * chi q.2 p.1
  else 0

lemma pauliPhase_eq_int {n : ℕ} (p q : PauliIdx n) :
    pauliPhase p q = (phaseRe p q : ℂ) + (phaseIm p q : ℂ) * Complex.I := by
  have hdot : dot (p + q).1 (p + q).2 = dot p.1 p.2 + dot q.1 q.2 + symp p q := by
    simp only [Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right, symp, dot_comm q.1 p.2]
    ring
  have h1 := zmod2_cases (dot p.1 p.2)
  have h2 := zmod2_cases (dot q.1 q.2)
  have h3 := zmod2_cases (symp p q)
  have h4 := chi_eq_one_or_neg_one q.2 p.1
  simp only [pauliPhase, pauliPh, phaseRe, phaseIm, hdot]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
  all_goals
    simp [h1, h2, h3, h4, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]

lemma pauliPhase_re_eq {n : ℕ} (p q : PauliIdx n) :
    (pauliPhase p q).re = (phaseRe p q : ℝ) := by
  rw [pauliPhase_eq_int]; simp

lemma pauliPhase_im_eq {n : ℕ} (p q : PauliIdx n) :
    (pauliPhase p q).im = (phaseIm p q : ℝ) := by
  rw [pauliPhase_eq_int]; simp

lemma pauliPhase_eq_re_of_symp_zero {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    pauliPhase p q = (phaseRe p q : ℂ) := by
  rw [pauliPhase_eq_int]; simp [phaseIm, hs]

lemma pauliPhase_eq_im_of_symp_one {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 1) :
    pauliPhase p q = (phaseIm p q : ℂ) * Complex.I := by
  rw [pauliPhase_eq_int]; simp [phaseRe, hs]

lemma phaseRe_sq_one_int {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    phaseRe p q ^ 2 = 1 := by
  simp only [phaseRe, hs, ↓reduceIte]
  rcases chi_eq_one_or_neg_one q.2 p.1 with h | h <;> split_ifs <;> simp [h]

lemma phaseRe_sq_one {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 0) :
    (phaseRe p q : ℝ) ^ 2 = 1 := by
  exact_mod_cast phaseRe_sq_one_int hs

lemma phaseIm_sq_one_int {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 1) :
    phaseIm p q ^ 2 = 1 := by
  simp only [phaseIm, hs, ↓reduceIte]
  rcases chi_eq_one_or_neg_one q.2 p.1 with h | h <;> split_ifs <;> simp [h]

lemma phaseIm_sq_one {n : ℕ} {p q : PauliIdx n} (hs : symp p q = 1) :
    (phaseIm p q : ℝ) ^ 2 = 1 := by
  exact_mod_cast phaseIm_sq_one_int hs

/-- Exact integer real part of `pauliPhase a p * pauliPhase (a + p) b`. -/
def trace4Int {n : ℕ} (a p b : PauliIdx n) : ℤ :=
  phaseRe a p * phaseRe (a + p) b - phaseIm a p * phaseIm (a + p) b

lemma trace4_re_eq {n : ℕ} (a p b : PauliIdx n) :
    (pauliPhase a p * pauliPhase (a + p) b).re = (trace4Int a p b : ℝ) := by
  rw [Complex.mul_re, pauliPhase_re_eq, pauliPhase_re_eq, pauliPhase_im_eq, pauliPhase_im_eq]
  simp [trace4Int]

private def basisZero (n : ℕ) : QState n := fun x => if x = 0 then 1 else 0

private lemma innerProd_basisZero (n : ℕ) : innerProd (basisZero n) (basisZero n) = 1 := by
  simp only [innerProd, basisZero]
  rw [Finset.sum_eq_single (0 : F2 n)]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma pauli_smul_cancel {n : ℕ} (p : PauliIdx n) {c₁ c₂ : ℂ}
    (h : ∀ ψ : QState n, c₁ • pauliApply p ψ = c₂ • pauliApply p ψ) : c₁ = c₂ := by
  have h1 := congr_arg (innerProd (pauliApply p (basisZero n))) (h (basisZero n))
  rw [innerProd_smul_right, innerProd_smul_right, innerProd_pauliApply_both, innerProd_basisZero] at h1
  simpa using h1

private lemma pauliApply_conj {n : ℕ} (a b : PauliIdx n) (ψ : QState n) :
    pauliApply a (pauliApply b (pauliApply a ψ)) = (sympSign a b : ℂ) • pauliApply b ψ := by
  rw [pauliApply_comm a b _, pauliApply_invol]

private lemma pauliPhase_assoc {n : ℕ} (a b c : PauliIdx n) :
    pauliPhase a b * pauliPhase (a + b) c = pauliPhase b c * pauliPhase a (b + c) := by
  refine pauli_smul_cancel (a + b + c) fun ψ => ?_
  have h1 : pauliApply a (pauliApply b (pauliApply c ψ)) =
      (pauliPhase a b * pauliPhase (a + b) c) • pauliApply (a + b + c) ψ := by
    rw [pauliApply_comp a b _, pauliApply_comp (a + b) c _, smul_smul]
  have h2 : pauliApply a (pauliApply b (pauliApply c ψ)) =
      (pauliPhase b c * pauliPhase a (b + c)) • pauliApply (a + b + c) ψ := by
    rw [pauliApply_comp b c ψ, pauliApply_smul, pauliApply_comp a (b + c) ψ, smul_smul, add_assoc]
  rw [← h1, h2]

private lemma pauliPhase_invol_left {n : ℕ} (a b : PauliIdx n) :
    pauliPhase a b * pauliPhase a (a + b) = 1 := by
  refine pauli_smul_cancel b fun ψ => ?_
  have h1 : pauliApply a (pauliApply a (pauliApply b ψ)) = pauliApply b ψ := pauliApply_invol a _
  have h2 : pauliApply a (pauliApply a (pauliApply b ψ)) =
      (pauliPhase a b * pauliPhase a (a + b)) • pauliApply b ψ := by
    rw [pauliApply_comp a b ψ, pauliApply_smul, pauliApply_comp a (a + b) ψ,
        pauliIdx_add_cancel_left, smul_smul]
  rw [h2] at h1; simpa using h1

private lemma pauliPhase_invol_right {n : ℕ} (a b : PauliIdx n) :
    pauliPhase a b * pauliPhase (a + b) b = 1 := by
  refine pauli_smul_cancel a fun ψ => ?_
  have h1 : pauliApply a (pauliApply b (pauliApply b ψ)) = pauliApply a ψ := by rw [pauliApply_invol]
  have h2 : pauliApply a (pauliApply b (pauliApply b ψ)) =
      (pauliPhase a b * pauliPhase (a + b) b) • pauliApply a ψ := by
    rw [pauliApply_comp a b _, pauliApply_comp (a + b) b _, pauliIdx_add_cancel_right, smul_smul]
  rw [h2] at h1; simpa using h1

private lemma phaseRe_comm_sym {n : ℕ} (s p : PauliIdx n) (hs : symp s p = 0) :
    phaseRe s p = phaseRe p s ∧ phaseRe s p = phaseRe s (s + p) := by
  have h1 : pauliPhase s p = pauliPhase p s := by
    rw [pauliPhase_comm s p]; simp [sympSign, hs]
  have hs2 : symp s (s + p) = 0 := by rw [symp_add_right, symp_self, zero_add]; exact hs
  have hre1 : phaseRe s p = phaseRe p s := by
    have hr := congr_arg Complex.re h1
    rw [pauliPhase_re_eq, pauliPhase_re_eq] at hr
    exact_mod_cast hr
  have hre2 : phaseRe s p = phaseRe s (s + p) := by
    have hin := pauliPhase_invol_left s p
    rw [pauliPhase_eq_re_of_symp_zero hs, pauliPhase_eq_re_of_symp_zero hs2] at hin
    have hZ : phaseRe s p * phaseRe s (s + p) = 1 := by
      have hr := congr_arg Complex.re hin
      norm_cast at hr
    have hsq := phaseRe_sq_one_int hs
    calc phaseRe s p = phaseRe s p * 1 := (mul_one _).symm
      _ = phaseRe s p * (phaseRe s p * phaseRe s (s + p)) := by rw [hZ]
      _ = phaseRe s p ^ 2 * phaseRe s (s + p) := by ring
      _ = phaseRe s (s + p) := by rw [hsq, one_mul]
  exact ⟨hre1, hre2⟩

private lemma phaseRe_add_left_eq {n : ℕ} (a b : PauliIdx n) (hs : symp a b = 0) :
    phaseRe (a + b) b = phaseRe a b := by
  have hs' : symp b a = 0 := by rw [symp_comm]; exact hs
  have h1 := (phaseRe_comm_sym b a hs').2
  have h2 := (phaseRe_comm_sym b (b + a) (by rw [symp_add_right, symp_self, zero_add]; exact hs')).1
  rw [add_comm b a] at h1 h2
  rw [← h2, ← h1, (phaseRe_comm_sym a b hs).1]

private lemma trace4Int_zero_of_symp {n : ℕ} (w a p : PauliIdx n)
    (hwa : symp w a = 1) (hwp : symp w p = 0) :
    trace4Int a p (a + w) = 0 := by
  have h1 : symp (a + p) (a + w) = symp a p + 1 := by
    rw [symp_add_left, symp_add_right, symp_add_right, symp_self, zero_add,
        symp_comm p a, symp_comm a w, hwa, symp_comm p w, hwp, add_zero]
    ring
  simp only [trace4Int, phaseRe, phaseIm, h1]
  rcases zmod2_cases (symp a p) with h | h <;> simp [h, show (1 : ZMod 2) + 1 = 0 by decide]

private lemma trace4Int_self {n : ℕ} (a w : PauliIdx n) :
    trace4Int a a (a + w) = 1 ∧ trace4Int a (a + w) (a + w) = 1 := by
  have h1 : (pauliPhase a a * pauliPhase (a + a) (a + w)).re = 1 := by
    rw [pauliPhase_self, pauliIdx_add_self, pauliPhase_zero_left, mul_one, Complex.one_re]
  have h2 : (pauliPhase a (a + w) * pauliPhase (a + (a + w)) (a + w)).re = 1 := by
    rw [pauliPhase_invol_right, Complex.one_re]
  rw [trace4_re_eq] at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

private lemma trace4Int_other {n : ℕ} (y w a : PauliIdx n)
    (hyw : symp y w = 0) (hya : symp y a = 0) :
    trace4Int a (y + a) (a + w) = phaseRe y a * phaseRe y (a + w) ∧
    trace4Int a (y + a + w) (a + w) = phaseRe y a * phaseRe y (a + w) := by
  have hyaw : symp y (a + w) = 0 := by rw [symp_add_right, hya, hyw, add_zero]
  have hay : symp a y = 0 := by rw [symp_comm]; exact hya
  have h1 : pauliPhase a (y + a) * pauliPhase (a + (y + a)) (a + w) =
      (phaseRe y a : ℂ) * (phaseRe y (a + w) : ℂ) := by
    have ha1 : a + (y + a) = y := by rw [add_comm y a, pauliIdx_add_cancel_left]
    have ha2 : pauliPhase a (y + a) = (phaseRe y a : ℂ) := by
      have hs : symp a (y + a) = 0 := by rw [symp_add_right, symp_self, add_zero]; exact hay
      rw [pauliPhase_eq_re_of_symp_zero hs, (phaseRe_comm_sym a (y + a) hs).2, ha1,
          (phaseRe_comm_sym a y hay).1]
    rw [ha1, ha2, pauliPhase_eq_re_of_symp_zero hyaw]
  have h2 : pauliPhase a (y + a + w) * pauliPhase (a + (y + a + w)) (a + w) =
      (phaseRe y a : ℂ) * (phaseRe y (a + w) : ℂ) := by
    rw [pauliPhase_assoc]
    have hidx : y + a + w + (a + w) = y := by
      calc y + a + w + (a + w) = y + (a + a) + (w + w) := by abel
        _ = y := by rw [pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero]
    rw [hidx, pauliPhase_eq_re_of_symp_zero hay, (phaseRe_comm_sym a y hay).1]
    have hidx2 : y + a + w = y + (a + w) := add_assoc y a w
    have hs2 : symp (y + (a + w)) (a + w) = 0 := by
      rw [symp_add_left, symp_self, add_zero]; exact hyaw
    rw [hidx2, pauliPhase_eq_re_of_symp_zero hs2, phaseRe_add_left_eq y (a + w) hyaw, mul_comm]
  have hr1 := congr_arg Complex.re h1
  have hr2 := congr_arg Complex.re h2
  rw [trace4_re_eq] at hr1 hr2
  have hre_mul : ∀ x z : ℤ, ((x : ℂ) * (z : ℂ)).re = ((x * z : ℤ) : ℝ) := fun x z => by
    norm_cast
  rw [hre_mul] at hr1 hr2
  exact ⟨by exact_mod_cast hr1, by exact_mod_cast hr2⟩

private lemma trace4Int_shift_w {n : ℕ} (a q w : PauliIdx n) :
    trace4Int a (q + w) (a + w) = trace4Int a q (a + w) := by
  let lam1 : ℂ := pauliPhase a (q + w) * pauliPhase (a + (q + w)) (a + w)
  let lam2 : ℂ := pauliPhase a q * pauliPhase (a + q) (a + w)
  have hact1 : ∀ ψ : QState n,
      pauliApply a (pauliApply (q + w) (pauliApply (a + w) (pauliApply q ψ))) = lam1 • ψ := fun ψ => by
    have hidx : a + (q + w) + (a + w) = q := by
      calc a + (q + w) + (a + w) = q + (a + a) + (w + w) := by abel
        _ = q := by rw [pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero]
    rw [pauliApply_comp a (q + w) _, pauliApply_comp (a + (q + w)) (a + w) _, hidx,
        pauliApply_invol, smul_smul]
  have hact2 : ∀ ψ : QState n,
      pauliApply a (pauliApply q (pauliApply (a + w) (pauliApply (q + w) ψ))) = lam2 • ψ := fun ψ => by
    have hidx : a + q + (a + w) = q + w := by
      calc a + q + (a + w) = (a + a) + (q + w) := by abel
        _ = q + w := by rw [pauliIdx_add_self, zero_add]
    rw [pauliApply_comp a q _, pauliApply_comp (a + q) (a + w) _, hidx,
        pauliApply_invol, smul_smul]
  have hlam2 : lam2 = innerProd (basisZero n)
      (pauliApply q (pauliApply (a + w) (pauliApply (q + w) (pauliApply a (basisZero n))))) := by
    have h := congr_arg (innerProd (pauliApply a (basisZero n))) (hact2 (pauliApply a (basisZero n)))
    rw [innerProd_smul_right, innerProd_pauliApply_both, innerProd_pauliApply_both,
        innerProd_basisZero, mul_one] at h
    exact h.symm
  have hlam1 : lam1 = innerProd (basisZero n)
      (pauliApply a (pauliApply (q + w) (pauliApply (a + w) (pauliApply q (basisZero n))))) := by
    have h := congr_arg (innerProd (basisZero n)) (hact1 (basisZero n))
    rw [innerProd_smul_right, innerProd_basisZero, mul_one] at h
    exact h.symm
  have hconj : star lam2 = lam1 := by
    rw [hlam2, hlam1, ← innerProd_conj_symm]
    rw [← innerProd_pauliApply_right q, ← innerProd_pauliApply_right (a + w),
        ← innerProd_pauliApply_right (q + w), ← innerProd_pauliApply_right a]
  have hre := congr_arg Complex.re hconj
  rw [Complex.star_def, Complex.conj_re] at hre
  simp only [lam1, lam2, trace4_re_eq] at hre
  exact_mod_cast hre.symm

/-- Sign identity for `P3`: `trace4Int u (r + u) u₂ = -(phaseIm r u * phaseIm r u₂)`. -/
private lemma sign_P3_eq {n : ℕ} (r u u₂ : PauliIdx n)
    (hru : symp r u = 1) (hru2 : symp r u₂ = 1) :
    trace4Int u (r + u) u₂ = -(phaseIm r u * phaseIm r u₂) := by
  have hur : symp u r = 1 := by rw [symp_comm]; exact hru
  have h1 : pauliPhase u (r + u) = (phaseIm r u : ℂ) * Complex.I := by
    have hinv := pauliPhase_invol_left u r
    rw [add_comm u r, pauliPhase_comm u r] at hinv
    have hsgn : (sympSign u r : ℂ) = -1 := by simp [sympSign, hur]
    rw [hsgn, pauliPhase_eq_im_of_symp_one hru] at hinv
    have hsq : ((phaseIm r u : ℂ) ^ 2) = 1 := by exact_mod_cast phaseIm_sq_one_int hru
    calc pauliPhase u (r + u)
        = (-1 * ((phaseIm r u : ℂ) * Complex.I) * pauliPhase u (r + u)) *
            ((phaseIm r u : ℂ) * Complex.I) := by
          have : -1 * ((phaseIm r u : ℂ) * Complex.I) * ((phaseIm r u : ℂ) * Complex.I) = 1 := by
            calc _ = - (phaseIm r u : ℂ) ^ 2 * (Complex.I ^ 2) := by ring
              _ = - 1 * (-1) := by rw [hsq, Complex.I_sq]
              _ = 1 := by ring
          calc pauliPhase u (r + u) = 1 * pauliPhase u (r + u) := (one_mul _).symm
            _ = (-1 * ((phaseIm r u : ℂ) * Complex.I) * ((phaseIm r u : ℂ) * Complex.I)) *
                  pauliPhase u (r + u) := by rw [this]
            _ = _ := by ring
      _ = 1 * ((phaseIm r u : ℂ) * Complex.I) := by rw [hinv]
      _ = (phaseIm r u : ℂ) * Complex.I := one_mul _
  have hprod : pauliPhase u (r + u) * pauliPhase (u + (r + u)) u₂ =
      (-((phaseIm r u * phaseIm r u₂ : ℤ) : ℂ)) := by
    have hadd : u + (r + u) = r := by rw [add_comm r u, pauliIdx_add_cancel_left]
    rw [hadd, h1, pauliPhase_eq_im_of_symp_one hru2]
    push_cast
    calc ((phaseIm r u : ℂ) * Complex.I) * ((phaseIm r u₂ : ℂ) * Complex.I)
        = (phaseIm r u : ℂ) * (phaseIm r u₂ : ℂ) * Complex.I ^ 2 := by ring
      _ = (phaseIm r u : ℂ) * (phaseIm r u₂ : ℂ) * (-1) := by rw [Complex.I_sq]
      _ = -((phaseIm r u : ℂ) * (phaseIm r u₂ : ℂ)) := by ring
  have hre := congr_arg Complex.re hprod
  rw [trace4_re_eq] at hre
  simp only [Complex.neg_re, Complex.intCast_re] at hre
  exact_mod_cast hre

/-- Sign identity for `P2`: universal conjugation proof for all `n`. -/
private lemma sign_P2_eq {n : ℕ} (s r u v : PauliIdx n)
    (hsr : symp s r = 1) (hsu : symp s u = 0) (hsv : symp s v = 0)
    (hru : symp r u = 1) (hrv : symp r v = 1) (huv : symp u v = 1) :
    -(phaseIm r v * phaseIm r (s + u + v) * phaseIm (r + s) v * phaseIm (r + s) (s + u + v)) =
      phaseRe u (r + v) * phaseRe u (r + (s + u + v)) := by
  set w := s + u + v
  have hsw : symp s w = 0 := by simp [w, symp_add_right, symp_self, hsu, hsv]
  have hrw : symp r w = 1 := by
    simp only [w, symp_add_right, symp_comm r s, hsr, hru, hrv]; decide
  have hrsv : symp (r + s) v = 1 := by rw [symp_add_left, hrv, hsv, add_zero]
  have hrsw : symp (r + s) w = 1 := by rw [symp_add_left, hrw, hsw, add_zero]
  have hurs : symp u (r + v) = 0 := by rw [symp_add_right, symp_comm u r, hru, huv]; decide
  have hurw : symp u (r + w) = 0 := by
    have huw : symp u w = 1 := by
      simp only [w, symp_add_right, symp_comm u s, hsu, symp_self, huv]; decide
    rw [symp_add_right, symp_comm u r, hru, huw]; decide
  have hidx1 : (r + v) + (r + s + w) = u := by
    calc (r + v) + (r + s + (s + u + v)) = u + (r + r) + (s + s) + (v + v) := by abel
      _ = u := by rw [pauliIdx_add_self, pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero, add_zero]
  have hidx2 : (r + w) + (r + s + v) = u := by
    calc (r + (s + u + v)) + (r + s + v) = u + (r + r) + (s + s) + (v + v) := by abel
      _ = u := by rw [pauliIdx_add_self, pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero, add_zero]
  have hph1 : pauliPhase (r + v) (r + s + w) = (phaseRe u (r + v) : ℂ) := by
    have heq : u + (r + v) = r + s + w := by
      rw [← hidx1, add_comm (r + v) (r + s + w), pauliIdx_add_cancel_right]
    have hs : symp (r + v) (r + s + w) = 0 := by
      rw [← heq, symp_add_right, symp_self, add_zero, symp_comm]; exact hurs
    rw [pauliPhase_eq_re_of_symp_zero hs, ← phaseRe_add_left_eq (r + v) (r + s + w) hs, hidx1]
    have hcom := (phaseRe_comm_sym u (r + v) hurs).2
    rw [heq] at hcom; exact congrArg Int.cast hcom.symm
  have hph2 : pauliPhase (r + w) (r + s + v) = (phaseRe u (r + w) : ℂ) := by
    have heq : u + (r + w) = r + s + v := by
      rw [← hidx2, add_comm (r + w) (r + s + v), pauliIdx_add_cancel_right]
    have hs : symp (r + w) (r + s + v) = 0 := by
      rw [← heq, symp_add_right, symp_self, add_zero, symp_comm]; exact hurw
    rw [pauliPhase_eq_re_of_symp_zero hs, ← phaseRe_add_left_eq (r + w) (r + s + v) hs, hidx2]
    have hcom := (phaseRe_comm_sym u (r + w) hurw).2
    rw [heq] at hcom; exact congrArg Int.cast hcom.symm
  let c4 : ℂ := pauliPhase r v * pauliPhase (r + s) w * pauliPhase r w * pauliPhase (r + s) v
  have hmul : c4 * ((phaseRe u (r + v) : ℂ) * (phaseRe u (r + w) : ℂ)) = -1 := by
    refine pauli_smul_cancel (0 : PauliIdx n) fun ψ => ?_
    simp only [pauliApply_zero]
    have h12 : ∀ φ : QState n, pauliApply (r + w) (pauliApply (r + s + v) φ) = (phaseRe u (r + w) : ℂ) • pauliApply u φ :=
      fun φ => by rw [pauliApply_comp, hidx2, hph2]
    have h34 : ∀ φ : QState n, pauliApply (r + v) (pauliApply (r + s + w) φ) = (phaseRe u (r + v) : ℂ) • pauliApply u φ :=
      fun φ => by rw [pauliApply_comp, hidx1, hph1]
    have hway1 : c4 • pauliApply (r + v) (pauliApply (r + s + w) (pauliApply (r + w) (pauliApply (r + s + v) ψ))) =
        (c4 * ((phaseRe u (r + v) : ℂ) * (phaseRe u (r + w) : ℂ))) • ψ := by
      rw [h12, pauliApply_smul, pauliApply_smul, h34, pauliApply_invol, smul_smul, smul_smul]
      exact congrArg (· • ψ) (by ring)
    have hway2 : c4 • pauliApply (r + v) (pauliApply (r + s + w) (pauliApply (r + w) (pauliApply (r + s + v) ψ))) =
        (-1 : ℂ) • ψ := by
      have ha1 : ∀ φ, pauliApply (r + s) (pauliApply v φ) = pauliPhase (r + s) v • pauliApply (r + s + v) φ :=
        fun φ => pauliApply_comp (r + s) v φ
      have ha2 : ∀ φ, pauliApply r (pauliApply w φ) = pauliPhase r w • pauliApply (r + w) φ :=
        fun φ => pauliApply_comp r w φ
      have ha3 : ∀ φ, pauliApply (r + s) (pauliApply w φ) = pauliPhase (r + s) w • pauliApply (r + s + w) φ :=
        fun φ => pauliApply_comp (r + s) w φ
      have ha4 : ∀ φ, pauliApply r (pauliApply v φ) = pauliPhase r v • pauliApply (r + v) φ :=
        fun φ => pauliApply_comp r v φ
      have hcomb : pauliApply r (pauliApply v (pauliApply (r + s) (pauliApply w
          (pauliApply r (pauliApply w (pauliApply (r + s) (pauliApply v ψ))))))) =
          c4 • pauliApply (r + v) (pauliApply (r + s + w) (pauliApply (r + w) (pauliApply (r + s + v) ψ))) := by
        calc _ = pauliPhase (r + s) v • pauliApply r (pauliApply v (pauliApply (r + s) (pauliApply w
              (pauliApply r (pauliApply w (pauliApply (r + s + v) ψ)))))) := by
              rw [ha1]; simp only [pauliApply_smul]
          _ = (pauliPhase (r + s) v * pauliPhase r w) • pauliApply r (pauliApply v (pauliApply (r + s) (pauliApply w
              (pauliApply (r + w) (pauliApply (r + s + v) ψ))))) := by
              rw [ha2]; simp only [pauliApply_smul, smul_smul]
          _ = (pauliPhase (r + s) v * pauliPhase r w * pauliPhase (r + s) w) • pauliApply r (pauliApply v
              (pauliApply (r + s + w) (pauliApply (r + w) (pauliApply (r + s + v) ψ)))) := by
              rw [ha3]; simp only [pauliApply_smul, smul_smul]
          _ = (pauliPhase (r + s) v * pauliPhase r w * pauliPhase (r + s) w * pauliPhase r v) •
              pauliApply (r + v) (pauliApply (r + s + w) (pauliApply (r + w) (pauliApply (r + s + v) ψ))) := by
              rw [ha4]; simp only [smul_smul]
          _ = c4 • _ := congrArg (· • _) (by simp only [c4]; ring)
      rw [← hcomb]
      have hwr : symp w r = 1 := by rw [symp_comm]; exact hrw
      have hrsr : symp (r + s) r = 1 := by rw [symp_add_left, symp_self, zero_add]; exact hsr
      have hvr : symp v r = 1 := by rw [symp_comm]; exact hrv
      have hc1 : ∀ φ, pauliApply w (pauliApply r (pauliApply w φ)) = (-1 : ℂ) • pauliApply r φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hwr]
      have hc2 : ∀ φ, pauliApply (r + s) (pauliApply r (pauliApply (r + s) φ)) = (-1 : ℂ) • pauliApply r φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hrsr]
      have hc3 : ∀ φ, pauliApply v (pauliApply r (pauliApply v φ)) = (-1 : ℂ) • pauliApply r φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hvr]
      rw [hc1, pauliApply_smul, pauliApply_smul, pauliApply_smul,
          hc2, pauliApply_smul, pauliApply_smul,
          hc3, pauliApply_smul, pauliApply_invol]
      simp only [smul_smul]; exact congrArg (· • ψ) (by norm_num)
    rw [← hway1, hway2]
  have hc4 : c4 = ((phaseIm r v * phaseIm r w * phaseIm (r + s) v * phaseIm (r + s) w : ℤ) : ℂ) := by
    simp only [c4, pauliPhase_eq_im_of_symp_one hrv, pauliPhase_eq_im_of_symp_one hrsw,
      pauliPhase_eq_im_of_symp_one hrw, pauliPhase_eq_im_of_symp_one hrsv]
    push_cast
    calc ((phaseIm r v : ℂ) * Complex.I) * ((phaseIm (r + s) w : ℂ) * Complex.I) *
          ((phaseIm r w : ℂ) * Complex.I) * ((phaseIm (r + s) v : ℂ) * Complex.I)
        = (phaseIm r v : ℂ) * (phaseIm r w : ℂ) * (phaseIm (r + s) v : ℂ) * (phaseIm (r + s) w : ℂ) *
            (Complex.I ^ 2 * Complex.I ^ 2) := by ring
      _ = (phaseIm r v : ℂ) * (phaseIm r w : ℂ) * (phaseIm (r + s) v : ℂ) * (phaseIm (r + s) w : ℂ) *
            ((-1) * (-1)) := by rw [Complex.I_sq]
      _ = _ := by ring
  rw [hc4] at hmul
  have hZ : (phaseIm r v * phaseIm r w * phaseIm (r + s) v * phaseIm (r + s) w) *
      (phaseRe u (r + v) * phaseRe u (r + w)) = -1 := by
    have hre := congr_arg Complex.re hmul
    norm_cast at hre
  have hsq : (phaseIm r v * phaseIm r w * phaseIm (r + s) v * phaseIm (r + s) w) ^ 2 = 1 := by
    have h1 := phaseIm_sq_one_int hrv
    have h2 := phaseIm_sq_one_int hrw
    have h3 := phaseIm_sq_one_int hrsv
    have h4 := phaseIm_sq_one_int hrsw
    calc _ = phaseIm r v ^ 2 * phaseIm r w ^ 2 * phaseIm (r + s) v ^ 2 * phaseIm (r + s) w ^ 2 := by ring
      _ = 1 * 1 * 1 * 1 := by rw [h1, h2, h3, h4]
      _ = 1 := by ring
  set A := phaseIm r v * phaseIm r w * phaseIm (r + s) v * phaseIm (r + s) w
  set B := phaseRe u (r + v) * phaseRe u (r + w)
  calc -A = A * (-1) := by ring
    _ = A * (A * B) := by rw [hZ]
    _ = A ^ 2 * B := by ring
    _ = B := by rw [hsq, one_mul]

/-- Sign identity for `P4`: universal conjugation proof for all `n`. -/
private lemma sign_P4_eq {n : ℕ} (s r uk u : PauliIdx n)
    (hsr : symp s r = 1) (hsuk : symp s uk = 0) (hsu : symp s u = 0)
    (hruk : symp r uk = 1) (hru : symp r u = 1) (huku : symp uk u = 1) :
    phaseIm r (s + uk + u) * phaseIm r uk * phaseIm (r + s) u * phaseIm (r + s) uk =
      phaseRe (r + s + uk) u * phaseRe (r + uk) (s + uk + u) := by
  set u₂ := s + uk + u
  have hsu2 : symp s u₂ = 0 := by simp [u₂, symp_add_right, symp_self, hsuk, hsu]
  have hru2 : symp r u₂ = 1 := by
    simp only [u₂, symp_add_right, symp_comm r s, hsr, hruk, hru]; decide
  have hrsu : symp (r + s) u = 1 := by rw [symp_add_left, hru, hsu, add_zero]
  have hrsuk : symp (r + s) uk = 1 := by rw [symp_add_left, hruk, hsuk, add_zero]
  have hu2uk : symp u₂ uk = 1 := by
    simp only [u₂, symp_add_left, hsuk, symp_self, symp_comm u uk, huku]; decide
  have hcm1 : symp (r + s + uk) u = 0 := by
    rw [symp_add_left, hrsu, huku]; decide
  have hcm2 : symp (r + uk) u₂ = 0 := by
    rw [symp_add_left, hru2, symp_comm uk u₂, hu2uk]; decide
  have hidx1 : (r + s + uk) + u = r + u₂ := by simp only [u₂]; abel
  have hidx2 : (r + uk) + u₂ = r + s + u := by
    calc (r + uk) + (s + uk + u) = r + s + u + (uk + uk) := by abel
      _ = r + s + u := by rw [pauliIdx_add_self, add_zero]
  let c4 : ℂ := pauliPhase (r + s) uk * pauliPhase r u₂ * pauliPhase r uk * pauliPhase (r + s) u
  have hmul : c4 * ((phaseRe (r + s + uk) u : ℂ) * (phaseRe (r + uk) u₂ : ℂ)) = 1 := by
    refine pauli_smul_cancel (0 : PauliIdx n) fun ψ => ?_
    simp only [pauliApply_zero]
    have h12 : ∀ φ : QState n, pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) φ)) =
        (phaseRe (r + uk) u₂ : ℂ) • φ := fun φ => by
      rw [pauliApply_comp, hidx2, pauliPhase_eq_re_of_symp_zero hcm2, pauliApply_invol]
    have h34 : ∀ φ : QState n, pauliApply (r + s + uk) (pauliApply u (pauliApply (r + u₂) φ)) =
        (phaseRe (r + s + uk) u : ℂ) • φ := fun φ => by
      rw [pauliApply_comp, hidx1, pauliPhase_eq_re_of_symp_zero hcm1, pauliApply_invol]
    have hway1 : c4 • pauliApply (r + s + uk) (pauliApply u (pauliApply (r + u₂)
        (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ))))) =
        (c4 * ((phaseRe (r + s + uk) u : ℂ) * (phaseRe (r + uk) u₂ : ℂ))) • ψ := by
      rw [h12, pauliApply_smul, pauliApply_smul, pauliApply_smul, h34, smul_smul, smul_smul]
      exact congrArg (· • ψ) (by ring)
    have hway2 : c4 • pauliApply (r + s + uk) (pauliApply u (pauliApply (r + u₂)
        (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ))))) =
        (1 : ℂ) • ψ := by
      have ha1 : ∀ φ, pauliApply (r + s) (pauliApply u φ) = pauliPhase (r + s) u • pauliApply (r + s + u) φ :=
        fun φ => pauliApply_comp (r + s) u φ
      have ha2 : ∀ φ, pauliApply r (pauliApply uk φ) = pauliPhase r uk • pauliApply (r + uk) φ :=
        fun φ => pauliApply_comp r uk φ
      have ha3 : ∀ φ, pauliApply r (pauliApply u₂ φ) = pauliPhase r u₂ • pauliApply (r + u₂) φ :=
        fun φ => pauliApply_comp r u₂ φ
      have ha4 : ∀ φ, pauliApply (r + s) (pauliApply uk φ) = pauliPhase (r + s) uk • pauliApply (r + s + uk) φ :=
        fun φ => pauliApply_comp (r + s) uk φ
      have hcomb : pauliApply (r + s) (pauliApply uk (pauliApply u (pauliApply r (pauliApply u₂
          (pauliApply r (pauliApply uk (pauliApply u₂ (pauliApply (r + s) (pauliApply u ψ))))))))) =
          c4 • pauliApply (r + s + uk) (pauliApply u (pauliApply (r + u₂)
            (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ))))) := by
        calc _ = pauliPhase (r + s) u • pauliApply (r + s) (pauliApply uk (pauliApply u (pauliApply r (pauliApply u₂
              (pauliApply r (pauliApply uk (pauliApply u₂ (pauliApply (r + s + u) ψ)))))))) := by
              rw [ha1]; simp only [pauliApply_smul]
          _ = (pauliPhase (r + s) u * pauliPhase r uk) • pauliApply (r + s) (pauliApply uk (pauliApply u
              (pauliApply r (pauliApply u₂ (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ))))))) := by
              rw [ha2]; simp only [pauliApply_smul, smul_smul]
          _ = (pauliPhase (r + s) u * pauliPhase r uk * pauliPhase r u₂) • pauliApply (r + s) (pauliApply uk
              (pauliApply u (pauliApply (r + u₂) (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ)))))) := by
              rw [ha3]; simp only [pauliApply_smul, smul_smul]
          _ = (pauliPhase (r + s) u * pauliPhase r uk * pauliPhase r u₂ * pauliPhase (r + s) uk) •
              pauliApply (r + s + uk) (pauliApply u (pauliApply (r + u₂)
                (pauliApply (r + uk) (pauliApply u₂ (pauliApply (r + s + u) ψ))))) := by
              rw [ha4]; simp only [smul_smul]
          _ = c4 • _ := congrArg (· • _) (by simp only [c4]; ring)
      rw [← hcomb]
      have hc1 : ∀ φ, pauliApply r (pauliApply u₂ (pauliApply r φ)) = (-1 : ℂ) • pauliApply u₂ φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hru2]
      have hc2 : ∀ φ, pauliApply u₂ (pauliApply uk (pauliApply u₂ φ)) = (-1 : ℂ) • pauliApply uk φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hu2uk]
      have hc3 : ∀ φ, pauliApply uk (pauliApply u (pauliApply uk φ)) = (-1 : ℂ) • pauliApply u φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, huku]
      have hc4' : ∀ φ, pauliApply (r + s) (pauliApply u (pauliApply (r + s) φ)) = (-1 : ℂ) • pauliApply u φ := fun φ => by
        rw [pauliApply_conj]; simp [sympSign, hrsu]
      rw [hc1, pauliApply_smul, pauliApply_smul, pauliApply_smul,
          hc2, pauliApply_smul, pauliApply_smul, pauliApply_smul,
          hc3, pauliApply_smul,
          hc4', pauliApply_invol]
      simp only [smul_smul]; exact congrArg (· • ψ) (by norm_num)
    rw [← hway1, hway2]
  have hc4 : c4 = ((phaseIm r u₂ * phaseIm r uk * phaseIm (r + s) u * phaseIm (r + s) uk : ℤ) : ℂ) := by
    simp only [c4, pauliPhase_eq_im_of_symp_one hrsuk, pauliPhase_eq_im_of_symp_one hru2,
      pauliPhase_eq_im_of_symp_one hruk, pauliPhase_eq_im_of_symp_one hrsu]
    push_cast
    calc ((phaseIm (r + s) uk : ℂ) * Complex.I) * ((phaseIm r u₂ : ℂ) * Complex.I) *
          ((phaseIm r uk : ℂ) * Complex.I) * ((phaseIm (r + s) u : ℂ) * Complex.I)
        = (phaseIm r u₂ : ℂ) * (phaseIm r uk : ℂ) * (phaseIm (r + s) u : ℂ) * (phaseIm (r + s) uk : ℂ) *
            (Complex.I ^ 2 * Complex.I ^ 2) := by ring
      _ = (phaseIm r u₂ : ℂ) * (phaseIm r uk : ℂ) * (phaseIm (r + s) u : ℂ) * (phaseIm (r + s) uk : ℂ) *
            ((-1) * (-1)) := by rw [Complex.I_sq]
      _ = _ := by ring
  rw [hc4] at hmul
  have hZ : (phaseIm r u₂ * phaseIm r uk * phaseIm (r + s) u * phaseIm (r + s) uk) *
      (phaseRe (r + s + uk) u * phaseRe (r + uk) u₂) = 1 := by
    have hre := congr_arg Complex.re hmul
    norm_cast at hre
  have hsq : (phaseIm r u₂ * phaseIm r uk * phaseIm (r + s) u * phaseIm (r + s) uk) ^ 2 = 1 := by
    have h1 := phaseIm_sq_one_int hru2
    have h2 := phaseIm_sq_one_int hruk
    have h3 := phaseIm_sq_one_int hrsu
    have h4 := phaseIm_sq_one_int hrsuk
    calc _ = phaseIm r u₂ ^ 2 * phaseIm r uk ^ 2 * phaseIm (r + s) u ^ 2 * phaseIm (r + s) uk ^ 2 := by ring
      _ = 1 * 1 * 1 * 1 := by rw [h1, h2, h3, h4]
      _ = 1 := by ring
  set A := phaseIm r u₂ * phaseIm r uk * phaseIm (r + s) u * phaseIm (r + s) uk
  set B := phaseRe (r + s + uk) u * phaseRe (r + uk) u₂
  calc A = A * 1 := (mul_one _).symm
    _ = A * (A * B) := by rw [hZ]
    _ = A ^ 2 * B := by ring
    _ = B := by rw [hsq, one_mul]

/-! ### Step 2: General Pure-State Rank-1 Convolution Identity (`pauli_prod_eq_conv`) -/

/-- For any `n`-qubit pure state `ψ` and any `a, b ∈ 𝔽₂²ⁿ`:
    `2ⁿ c_a c_b = ∑_p trace4Int(a, p, b) * c_p * c_{a + p + b}`. -/
lemma pauli_prod_eq_conv {n : ℕ} (ψ : QState n) (a b : PauliIdx n) :
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    ∑ p : PauliIdx n, (trace4Int a p b : ℝ) * c p * c (a + p + b) =
      (2 : ℝ) ^ n * c a * c b := by
  intro c
  have hc_real : ∀ p : PauliIdx n, (c p : ℂ) = innerProd ψ (pauliApply p ψ) :=
    fun p => innerProd_pauliApply_self_real p ψ
  have h := congr_arg (innerProd (pauliApply a ψ)) (pauli_completeness ψ (pauliApply b ψ))
  rw [innerProd_sum_right, innerProd_smul_right] at h
  have hrhs : innerProd (pauliApply a ψ) ψ = innerProd ψ (pauliApply a ψ) := by
    rw [← innerProd_pauliApply_right]
  rw [hrhs] at h
  have hterm : ∀ p : PauliIdx n,
      innerProd (pauliApply a ψ) (innerProd ψ (pauliApply p ψ) • pauliApply p (pauliApply b ψ)) =
      innerProd ψ (pauliApply p ψ) * (pauliPhase a p * pauliPhase (a + p) b) *
        innerProd ψ (pauliApply (a + p + b) ψ) := by
    intro p
    rw [innerProd_smul_right, ← innerProd_pauliApply_right, pauliApply_comp,
        innerProd_smul_right, pauliApply_comp, innerProd_smul_right]
    ring
  simp_rw [hterm] at h
  have hre := congr_arg Complex.re h
  rw [Complex.re_sum] at hre
  have hre_mul : ∀ (x y : ℝ) (z : ℂ), ((x : ℂ) * z * (y : ℂ)).re = z.re * x * y := fun x y z => by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hlhs : (∑ p : PauliIdx n, (innerProd ψ (pauliApply p ψ) *
      (pauliPhase a p * pauliPhase (a + p) b) *
      innerProd ψ (pauliApply (a + p + b) ψ)).re) =
      ∑ p : PauliIdx n, (trace4Int a p b : ℝ) * c p * c (a + p + b) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hc_real p, ← hc_real (a + p + b), hre_mul, trace4_re_eq]
  have hrhs2 : ((2 : ℂ) ^ n * innerProd ψ (pauliApply b ψ) * innerProd ψ (pauliApply a ψ)).re =
      (2 : ℝ) ^ n * c a * c b := by
    rw [← hc_real a, ← hc_real b]
    have h2 : (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) := by norm_cast
    rw [h2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  rw [hlhs, hrhs2] at hre
  exact hre

/-! ### Step 3: Pure Symplectic Character-Sum Geometry on `𝔽₂⁴ = PauliIdx 2` -/

private lemma sum_sympSign_two (d : PauliIdx 2) :
    ∑ x : PauliIdx 2, (sympSign d x : ℝ) = if d = 0 then 16 else 0 := by
  have hZ : ∑ x : PauliIdx 2, sympSign d x = if d = 0 then 16 else 0 := by
    revert d; decide
  have hR := congr_arg (Int.cast (R := ℝ)) hZ
  push_cast at hR
  by_cases hd : d = 0
  · rw [if_pos hd] at hR ⊢; exact hR
  · rw [if_neg hd] at hR ⊢; exact hR

private lemma pauli_add_eq_zero_iff {n : ℕ} (a b : PauliIdx n) : a + b = 0 ↔ a = b := by
  constructor
  · intro h; have h1 := congr_arg (· + b) h; rw [pauliIdx_add_cancel_right, zero_add] at h1; exact h1
  · intro h; rw [h, pauliIdx_add_self]

private lemma pauli_add_eq_left_iff {n : ℕ} (a b : PauliIdx n) : a + b = a ↔ b = 0 := by
  constructor
  · intro h; have h1 := congr_arg (a + ·) h; rw [pauliIdx_add_cancel_left, pauliIdx_add_self] at h1; exact h1
  · intro h; rw [h, add_zero]

private lemma pauli_add_eq_right_iff {n : ℕ} (a b : PauliIdx n) : a + b = b ↔ a = 0 := by
  rw [add_comm]; exact pauli_add_eq_left_iff b a

private lemma card_symp_zero_two {s : PauliIdx 2} (hs : s ≠ 0) :
    ∑ p : PauliIdx 2, (if symp s p = 0 then (1 : ℝ) else 0) = 8 := by
  have hsum : ∑ p : PauliIdx 2, ((1 : ℝ) + (sympSign s p : ℝ)) = 16 := by
    rw [Finset.sum_add_distrib, sum_sympSign_two, if_neg hs, add_zero]
    simp
  have hpt : ∀ p : PauliIdx 2, ((1 : ℝ) + (sympSign s p : ℝ)) =
      2 * (if symp s p = 0 then (1 : ℝ) else 0) := fun p => by
    simp only [sympSign]
    rcases zmod2_cases (symp s p) with h | h <;> simp [h] <;> ring
  simp_rw [hpt, ← Finset.mul_sum] at hsum
  linarith

private lemma card_comm_ne_two {s : PauliIdx 2} (hs : s ≠ 0) :
    ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (1 : ℝ) else 0) = 6 := by
  have h8 := card_symp_zero_two hs
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2))] at h8
  have hsin : s ∈ Finset.univ.erase (0 : PauliIdx 2) := Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩
  rw [← Finset.add_sum_erase _ _ hsin] at h8
  rw [if_pos (symp_zero_right s), if_pos (symp_self s)] at h8
  have hrest : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 2)).erase s,
      (if symp s p = 0 then (1 : ℝ) else 0) =
      ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (1 : ℝ) else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)),
        ← Finset.add_sum_erase _ _ hsin]
    rw [if_neg (by simp), if_neg (by simp), zero_add, zero_add]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hps : p ≠ s := (Finset.mem_erase.mp hp).1
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    by_cases h0 : symp s p = 0
    · rw [if_pos h0, if_pos ⟨hp0, hps, h0⟩]
    · rw [if_neg h0, if_neg (fun h => h0 h.2.2)]
  rw [hrest] at h8; linarith

private lemma card_symp_two_cond (a b : PauliIdx 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (e₁ e₂ : ZMod 2) :
    ∑ v : PauliIdx 2, (if symp a v = e₁ ∧ symp b v = e₂ then (1 : ℝ) else 0) = 4 := by
  let s₁ : ℝ := if e₁ = 0 then 1 else -1
  let s₂ : ℝ := if e₂ = 0 then 1 else -1
  have hab0 : a + b ≠ 0 := fun h => hab ((pauli_add_eq_zero_iff a b).mp h)
  have hsum : ∑ v : PauliIdx 2,
      (1 + s₁ * (sympSign a v : ℝ)) * (1 + s₂ * (sympSign b v : ℝ)) = 16 := by
    have hexp : ∀ v : PauliIdx 2,
        (1 + s₁ * (sympSign a v : ℝ)) * (1 + s₂ * (sympSign b v : ℝ)) =
        1 + s₁ * (sympSign a v : ℝ) + s₂ * (sympSign b v : ℝ) +
          (s₁ * s₂) * (sympSign (a + b) v : ℝ) := fun v => by
      rw [sympSign_add_left]; push_cast; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sympSign_two a, sum_sympSign_two b, sum_sympSign_two (a + b),
        if_neg ha, if_neg hb, if_neg hab0]
    simp
  have hpt : ∀ v : PauliIdx 2,
      (1 + s₁ * (sympSign a v : ℝ)) * (1 + s₂ * (sympSign b v : ℝ)) =
      4 * (if symp a v = e₁ ∧ symp b v = e₂ then (1 : ℝ) else 0) := fun v => by
    simp only [s₁, s₂, sympSign]
    rcases zmod2_cases e₁ with rfl | rfl <;> rcases zmod2_cases e₂ with rfl | rfl <;>
      rcases zmod2_cases (symp a v) with h1 | h1 <;> rcases zmod2_cases (symp b v) with h2 | h2 <;>
      simp [h1, h2] <;> ring
  simp_rw [hpt, ← Finset.mul_sum] at hsum
  linarith

private lemma card_symp_three_cond (u p q : PauliIdx 2)
    (hu : u ≠ 0) (hup : symp u p = 0) (huq : symp u q = 0) (hpq : symp p q = 1)
    (e₁ e₂ e₃ : ZMod 2) :
    ∑ v : PauliIdx 2, (if symp u v = e₁ ∧ symp p v = e₂ ∧ symp q v = e₃ then (1 : ℝ) else 0) = 2 := by
  have hp0 : p ≠ 0 := fun h => by rw [h, symp_zero_left] at hpq; exact absurd hpq (by decide)
  have hq0 : q ≠ 0 := fun h => by rw [h, symp_zero_right] at hpq; exact absurd hpq (by decide)
  have hup0 : u + p ≠ 0 := fun h => by
    have heq := (pauli_add_eq_zero_iff u p).mp h
    rw [heq] at huq; rw [huq] at hpq; exact absurd hpq (by decide)
  have huq0 : u + q ≠ 0 := fun h => by
    have heq := (pauli_add_eq_zero_iff u q).mp h
    rw [heq] at hup; rw [symp_comm q p] at hup; rw [hup] at hpq; exact absurd hpq (by decide)
  have hpq0 : p + q ≠ 0 := fun h => by
    have heq := (pauli_add_eq_zero_iff p q).mp h
    rw [heq, symp_self] at hpq; exact absurd hpq (by decide)
  have hupq0 : u + p + q ≠ 0 := fun h => by
    have h1 : symp (u + p + q) p = 0 := by rw [h, symp_zero_left]
    rw [symp_add_left, symp_add_left, hup, symp_self, symp_comm q p, hpq] at h1
    exact absurd h1 (by decide)
  let s₁ : ℝ := if e₁ = 0 then 1 else -1
  let s₂ : ℝ := if e₂ = 0 then 1 else -1
  let s₃ : ℝ := if e₃ = 0 then 1 else -1
  have hsum : ∑ v : PauliIdx 2,
      (1 + s₁ * (sympSign u v : ℝ)) * (1 + s₂ * (sympSign p v : ℝ)) *
        (1 + s₃ * (sympSign q v : ℝ)) = 16 := by
    have hexp : ∀ v : PauliIdx 2,
        (1 + s₁ * (sympSign u v : ℝ)) * (1 + s₂ * (sympSign p v : ℝ)) *
          (1 + s₃ * (sympSign q v : ℝ)) =
        1 + s₁ * (sympSign u v : ℝ) + s₂ * (sympSign p v : ℝ) + s₃ * (sympSign q v : ℝ) +
        (s₁ * s₂) * (sympSign (u + p) v : ℝ) + (s₁ * s₃) * (sympSign (u + q) v : ℝ) +
        (s₂ * s₃) * (sympSign (p + q) v : ℝ) + (s₁ * s₂ * s₃) * (sympSign (u + p + q) v : ℝ) := fun v => by
      simp only [sympSign_add_left]; push_cast; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sympSign_two u, sum_sympSign_two p, sum_sympSign_two q,
        sum_sympSign_two (u + p), sum_sympSign_two (u + q), sum_sympSign_two (p + q),
        sum_sympSign_two (u + p + q),
        if_neg hu, if_neg hp0, if_neg hq0, if_neg hup0, if_neg huq0, if_neg hpq0, if_neg hupq0]
    simp
  have hpt : ∀ v : PauliIdx 2,
      (1 + s₁ * (sympSign u v : ℝ)) * (1 + s₂ * (sympSign p v : ℝ)) *
        (1 + s₃ * (sympSign q v : ℝ)) =
      8 * (if symp u v = e₁ ∧ symp p v = e₂ ∧ symp q v = e₃ then (1 : ℝ) else 0) := fun v => by
    simp only [s₁, s₂, s₃, sympSign]
    rcases zmod2_cases e₁ with rfl | rfl <;> rcases zmod2_cases e₂ with rfl | rfl <;>
      rcases zmod2_cases e₃ with rfl | rfl <;>
      rcases zmod2_cases (symp u v) with h1 | h1 <;> rcases zmod2_cases (symp p v) with h2 | h2 <;>
      rcases zmod2_cases (symp q v) with h3 | h3 <;> simp [h1, h2, h3] <;> ring
  simp_rw [hpt, ← Finset.mul_sum] at hsum
  linarith

/-- Any element of `u^⊥ ∩ p^⊥` (for distinct commuting nonzero `u, p ∈ 𝔽₂⁴`) is in `{0, u, p, u + p}`! -/
private lemma mem_perp_inter_four (u p q : PauliIdx 2)
    (hu : u ≠ 0) (hp : p ≠ 0) (hpu : p ≠ u) (hup : symp u p = 0)
    (huq : symp u q = 0) (hpq : symp p q = 0) :
    q = 0 ∨ q = u ∨ q = p ∨ q = u + p := by
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨hq0, hqu, hqp, hqup⟩
  have hcard := card_symp_two_cond u p hu hp (Ne.symm hpu) 0 0
  have hup0 : u + p ≠ 0 := fun h => hpu ((pauli_add_eq_zero_iff u p).mp h).symm
  have hupu : u + p ≠ u := fun h => hp ((pauli_add_eq_left_iff u p).mp h)
  have hupp : u + p ≠ p := fun h => hu ((pauli_add_eq_right_iff u p).mp h)
  let S : Finset (PauliIdx 2) := {0, u, p, u + p, q}
  have hS_le : ∑ v ∈ S, (if symp u v = 0 ∧ symp p v = 0 then (1 : ℝ) else 0) ≤
      ∑ v : PauliIdx 2, (if symp u v = 0 ∧ symp p v = 0 then (1 : ℝ) else 0) :=
    Finset.sum_le_univ_sum_of_nonneg fun v => by split_ifs <;> norm_num
  have hS_val : ∑ v ∈ S, (if symp u v = 0 ∧ symp p v = 0 then (1 : ℝ) else 0) = 5 := by
    simp only [S]
    rw [Finset.sum_insert (by simp [hu.symm, hp.symm, hup0.symm, hq0.symm]),
        Finset.sum_insert (by simp [hpu.symm, hupu.symm, hqu.symm]),
        Finset.sum_insert (by simp [hupp.symm, hqp.symm]),
        Finset.sum_insert (by simp [hqup.symm]),
        Finset.sum_singleton]
    have h1 : symp u 0 = 0 ∧ symp p 0 = 0 := ⟨symp_zero_right _, symp_zero_right _⟩
    have h2 : symp u u = 0 ∧ symp p u = 0 := ⟨symp_self _, by rw [symp_comm]; exact hup⟩
    have h3 : symp u p = 0 ∧ symp p p = 0 := ⟨hup, symp_self _⟩
    have h4 : symp u (u + p) = 0 ∧ symp p (u + p) = 0 :=
      ⟨by rw [symp_add_right, symp_self, zero_add]; exact hup,
       by rw [symp_add_right, symp_self, add_zero, symp_comm]; exact hup⟩
    rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos ⟨huq, hpq⟩]
    norm_num
  linarith

/-- Any element `p ∈ y^⊥` with `symp w p = 1` (for commuting distinct `y, w`, and fixed `a ∈ y^⊥` with `symp w a = 1`)
    is one of the 4 elements `{a, a + w, y + a, y + a + w}`! -/
private lemma mem_perp_anti_four (y w a p : PauliIdx 2)
    (hy : y ≠ 0) (hw : w ≠ 0) (hwy : w ≠ y) (hyw : symp y w = 0)
    (hya : symp y a = 0) (hwa : symp w a = 1)
    (hyp : symp y p = 0) (hwp : symp w p = 1) :
    p = a ∨ p = a + w ∨ p = y + a ∨ p = y + a + w := by
  have h1 : symp y (p + a) = 0 := by rw [symp_add_right, hyp, hya, add_zero]
  have h2 : symp w (p + a) = 0 := by rw [symp_add_right, hwp, hwa]; decide
  rcases mem_perp_inter_four y w (p + a) hy hw hwy hyw h1 h2 with h | h | h | h
  · left; exact (pauli_add_eq_zero_iff p a).mp h
  · right; right; left
    have := congr_arg (· + a) h; rw [pauliIdx_add_cancel_right] at this; exact this
  · right; left
    have := congr_arg (· + a) h; rw [pauliIdx_add_cancel_right, add_comm] at this; exact this
  · right; right; right
    have := congr_arg (· + a) h; rw [pauliIdx_add_cancel_right] at this
    calc p = y + w + a := this
      _ = y + a + w := by abel

/-- For `symp s r = 1` and `u ∈ T(s, r)`, the set `T(s, r) \ {u}` has size 2 and consists of `{v, s + u + v}`
    for any `v ∈ T(s, r) \ {u}`! -/
private lemma T_set_eq_three (s r u v x : PauliIdx 2)
    (hsr : symp s r = 1)
    (hu0 : u ≠ 0) (hus : u ≠ s) (hsu : symp s u = 0) (hru : symp r u = 1)
    (hv0 : v ≠ 0) (hvs : v ≠ s) (hsv : symp s v = 0) (hrv : symp r v = 1) (hvu : v ≠ u)
    (hx0 : x ≠ 0) (hxs : x ≠ s) (hsx : symp s x = 0) (hrx : symp r x = 1) :
    x = u ∨ x = v ∨ x = s + u + v := by
  have hs0 : s ≠ 0 := fun h => by rw [h, symp_zero_left] at hsr; exact absurd hsr (by decide)
  have huv : symp u v = 1 := by
    rcases zmod2_cases (symp u v) with h0 | h1
    · exfalso
      rcases mem_perp_inter_four s u v hs0 hu0 hus hsu hsv h0 with rfl | rfl | rfl | rfl
      · exact hv0 rfl
      · exact hvs rfl
      · exact hvu rfl
      · rw [symp_add_right, symp_comm r s, hsr, hru] at hrv; exact absurd hrv (by decide)
    · exact h1
  have h1 : symp s (x + u) = 0 := by rw [symp_add_right, hsx, hsu, add_zero]
  have h2 : symp r (x + u) = 0 := by rw [symp_add_right, hrx, hru]; decide
  -- Wait: `x + u ∈ s^⊥ ∩ r^⊥`! What are the 4 elements of `s^⊥ ∩ r^⊥`? `{0, u + v, s + v, s + u}`? No: `s ∉ r^⊥`!
  -- Look at `y = u + v` and `z = s + u + v + u = s + v`? Wait: `symp s (u + v) = 0` and `symp r (u + v) = 0`!
  -- Better: use `mem_perp_inter_four s u x` vs `symp u x`:
  rcases zmod2_cases (symp u x) with hux0 | hux1
  · rcases mem_perp_inter_four s u x hs0 hu0 hus hsu hsx hux0 with rfl | rfl | rfl | rfl
    · exact absurd rfl hx0
    · exact absurd rfl hxs
    · left; rfl
    · rw [symp_add_right, symp_comm r s, hsr, hru] at hrx; exact absurd hrx (by decide)
  · -- `symp u x = 1` and `symp s x = 0`, `symp r x = 1`; look at `x + v`: commutes with `s`, `r`, `u`? Wait: `symp u (x + v) = 1 + 1 = 0`!
    have hsu_xv : symp s (x + v) = 0 := by rw [symp_add_right, hsx, hsv, add_zero]
    have hu_xv : symp u (x + v) = 0 := by rw [symp_add_right, hux1, huv]; decide
    rcases mem_perp_inter_four s u (x + v) hs0 hu0 hus hsu hsu_xv hu_xv with h | h | h | h
    · right; left; exact (pauli_add_eq_zero_iff x v).mp h
    · exfalso
      have hx_sv : x = s + v := by
        have := congr_arg (· + v) h; rw [pauliIdx_add_cancel_right] at this; exact this
      rw [hx_sv, symp_add_right, symp_comm r s, hsr, hrv] at hrx; exact absurd hrx (by decide)
    · exfalso
      have hx_uv : x = u + v := by
        have := congr_arg (· + v) h; rw [pauliIdx_add_cancel_right] at this; exact this
      rw [hx_uv, symp_add_right, hru, hrv] at hrx; exact absurd hrx (by decide)
    · right; right
      have := congr_arg (· + v) h; rw [pauliIdx_add_cancel_right] at this; exact this

/-! ### Step 4: Core Two-Qubit Pure-State Identities -/

section TwoQubit

variable {ψ : QState 2}

private abbrev cval (ψ : QState 2) (p : PauliIdx 2) : ℝ :=
  (innerProd ψ (pauliApply p ψ)).re

private abbrev gval (ψ : QState 2) (p : PauliIdx 2) : ℝ :=
  (cval ψ p) ^ 2

private abbrev F4 (ψ : QState 2) : ℝ := ∑ p : PauliIdx 2, gval ψ p ^ 2
private abbrev F6 (ψ : QState 2) : ℝ := ∑ p : PauliIdx 2, gval ψ p ^ 3
private abbrev Tord (ψ : QState 2) : ℝ :=
  ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
    if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ symp p q = 0 then gval ψ p * gval ψ q * gval ψ (p + q) else 0
private abbrev Tanti (ψ : QState 2) : ℝ :=
  ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
    if symp p q = 1 then gval ψ p * gval ψ q * gval ψ (p + q) else 0

private lemma F4_eq_pauliMoment4 : F4 ψ = pauliMoment4 2 ψ := by
  simp only [F4, pauliMoment4, gval, cval]
  refine Finset.sum_congr rfl fun p _ => by rw [innerProd_pauliApply_self_normSq]

private lemma cval_zero (hunit : IsUnitState ψ) : cval ψ 0 = 1 := by
  simp [cval, pauliApply_zero, show innerProd ψ ψ = 1 from hunit]

private lemma gval_zero (hunit : IsUnitState ψ) : gval ψ 0 = 1 := by
  rw [gval, cval_zero hunit]; norm_num

private lemma sum_gval (hunit : IsUnitState ψ) : ∑ p : PauliIdx 2, gval ψ p = 4 := by
  have h := sum_normSq_pauliExpect hunit
  have hsq : ∀ p : PauliIdx 2, Complex.normSq (innerProd ψ (pauliApply p ψ)) = gval ψ p :=
    fun p => innerProd_pauliApply_self_normSq p ψ
  simp_rw [hsq] at h
  norm_num at h; exact h

private lemma sum_erase_gval (hunit : IsUnitState ψ) :
    ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ p = 3 := by
  have h := Finset.add_sum_erase Finset.univ (gval ψ) (Finset.mem_univ (0 : PauliIdx 2))
  rw [sum_gval hunit, gval_zero hunit] at h; linarith

private lemma sum_erase_gval_sq (hunit : IsUnitState ψ) :
    ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ p ^ 2 = F4 ψ - 1 := by
  have h := Finset.add_sum_erase Finset.univ (fun p => gval ψ p ^ 2) (Finset.mem_univ (0 : PauliIdx 2))
  rw [gval_zero hunit] at h
  change (1 : ℝ) ^ 2 + ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ p ^ 2 = F4 ψ at h
  linarith

private lemma sum_erase_gval_cube (hunit : IsUnitState ψ) :
    ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ p ^ 3 = F6 ψ - 1 := by
  have h := Finset.add_sum_erase Finset.univ (fun p => gval ψ p ^ 3) (Finset.mem_univ (0 : PauliIdx 2))
  rw [gval_zero hunit] at h
  change (1 : ℝ) ^ 3 + ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ p ^ 3 = F6 ψ at h
  linarith

private lemma self_dual_gval (q : PauliIdx 2) :
    ∑ p : PauliIdx 2, (sympSign p q : ℝ) * gval ψ p = 4 * gval ψ q := by
  have h := pauli_symp_self_dual ψ q
  have hsq : ∀ p : PauliIdx 2, Complex.normSq (innerProd ψ (pauliApply p ψ)) = gval ψ p :=
    fun p => innerProd_pauliApply_self_normSq p ψ
  simp_rw [hsq] at h
  norm_num at h; exact h

private lemma sum_gval_anti (hunit : IsUnitState ψ) (q : PauliIdx 2) :
    ∑ p : PauliIdx 2, (if symp p q = 1 then gval ψ p else 0) = 2 - 2 * gval ψ q := by
  have h1 := sum_gval hunit
  have h2 := self_dual_gval (ψ := ψ) q
  have hsub : ∑ p : PauliIdx 2, ((1 : ℝ) - (sympSign p q : ℝ)) * gval ψ p = 4 - 4 * gval ψ q := by
    have hsplit : ∑ p : PauliIdx 2, ((1 : ℝ) - (sympSign p q : ℝ)) * gval ψ p =
        (∑ p : PauliIdx 2, gval ψ p) - ∑ p : PauliIdx 2, (sympSign p q : ℝ) * gval ψ p := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit, h1, h2]
  have hpt : ∀ p : PauliIdx 2, ((1 : ℝ) - (sympSign p q : ℝ)) * gval ψ p =
      2 * (if symp p q = 1 then gval ψ p else 0) := fun p => by
    simp only [sympSign]
    rcases zmod2_cases (symp p q) with h | h
    · rw [if_pos h, if_neg (by rw [h]; decide)]; norm_num
    · rw [if_neg (by rw [h]; decide), if_pos h]; push_cast; ring
  simp_rw [hpt, ← Finset.mul_sum] at hsub
  linarith

private lemma sum_gval_comm_ne (hunit : IsUnitState ψ) {q : PauliIdx 2} (hq : q ≠ 0) :
    ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ q ∧ symp p q = 0 then gval ψ p else 0) = 1 + gval ψ q := by
  have htot := sum_gval hunit
  have hanti := sum_gval_anti hunit q
  have hsplit : ∑ p : PauliIdx 2, gval ψ p =
      gval ψ 0 + gval ψ q +
      (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ q ∧ symp p q = 0 then gval ψ p else 0) +
      (∑ p : PauliIdx 2, if symp p q = 1 then gval ψ p else 0) := by
    have h0q : gval ψ 0 + gval ψ q =
        ∑ p : PauliIdx 2, (if p = 0 ∨ p = q then gval ψ p else 0) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2))]
      have hqin : q ∈ Finset.univ.erase (0 : PauliIdx 2) := Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
      rw [← Finset.add_sum_erase _ _ hqin]
      have hrest : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 2)).erase q,
          (if p = 0 ∨ p = q then gval ψ p else 0) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have h1 : p ≠ q := (Finset.mem_erase.mp hp).1
        have h2 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        rw [if_neg (by tauto)]
      rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl), hrest, add_zero]
    rw [h0q, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp0 : p = 0
    · subst hp0
      rw [if_pos (Or.inl rfl), if_neg (by simp), if_neg (by rw [symp_zero_left]; decide)]; ring
    · by_cases hpq : p = q
      · subst hpq
        rw [if_pos (Or.inr rfl), if_neg (by simp), if_neg (by rw [symp_self]; decide)]; ring
      · rcases zmod2_cases (symp p q) with hs | hs
        · rw [if_neg (by tauto), if_pos ⟨hp0, hpq, hs⟩, if_neg (by rw [hs]; decide)]; ring
        · rw [if_neg (by tauto), if_neg (by intro h; rw [hs] at h; exact absurd h.2.2 (by decide)),
              if_pos hs]; ring
  rw [htot, gval_zero hunit, hanti] at hsplit
  linarith

/-- Inclusion-exclusion from `W g = 4 g`: `∑_{ω(a,z)=1 ∧ ω(b,z)=1} g_z = 1 - g_a - g_b + g_{a+b}`. -/
private lemma sum_gval_anti_both (hunit : IsUnitState ψ) (a b : PauliIdx 2) :
    ∑ z : PauliIdx 2, (if symp a z = 1 ∧ symp b z = 1 then gval ψ z else 0) =
      1 - gval ψ a - gval ψ b + gval ψ (a + b) := by
  have h0 := sum_gval hunit
  have ha := self_dual_gval (ψ := ψ) a
  have hb := self_dual_gval (ψ := ψ) b
  have hab := self_dual_gval (ψ := ψ) (a + b)
  have hcomb : ∑ z : PauliIdx 2,
      ((1 : ℝ) - (sympSign z a : ℝ) - (sympSign z b : ℝ) + (sympSign z (a + b) : ℝ)) * gval ψ z =
      4 - 4 * gval ψ a - 4 * gval ψ b + 4 * gval ψ (a + b) := by
    have hs : ∑ z : PauliIdx 2,
        ((1 : ℝ) - (sympSign z a : ℝ) - (sympSign z b : ℝ) + (sympSign z (a + b) : ℝ)) * gval ψ z =
        (∑ z, gval ψ z) - (∑ z, (sympSign z a : ℝ) * gval ψ z) -
        (∑ z, (sympSign z b : ℝ) * gval ψ z) + (∑ z, (sympSign z (a + b) : ℝ) * gval ψ z) := by
      simp only [sub_mul, add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hs, h0, ha, hb, hab]
  have hpt : ∀ z : PauliIdx 2,
      ((1 : ℝ) - (sympSign z a : ℝ) - (sympSign z b : ℝ) + (sympSign z (a + b) : ℝ)) * gval ψ z =
      4 * (if symp a z = 1 ∧ symp b z = 1 then gval ψ z else 0) := fun z => by
    rw [sympSign_add_right]
    simp only [sympSign, symp_comm z a, symp_comm z b]
    rcases zmod2_cases (symp a z) with h1 | h1 <;> rcases zmod2_cases (symp b z) with h2 | h2
    · rw [if_pos h1, if_pos h2, if_neg (fun h => by rw [h1] at h; exact absurd h.1 (by decide))]; norm_num
    · rw [if_pos h1, if_neg (by rw [h2]; decide), if_neg (fun h => by rw [h1] at h; exact absurd h.1 (by decide))]; norm_num
    · rw [if_neg (by rw [h1]; decide), if_pos h2, if_neg (fun h => by rw [h2] at h; exact absurd h.2 (by decide))]; norm_num
    · rw [if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide), if_pos ⟨h1, h2⟩]; push_cast; ring
  simp_rw [hpt, ← Finset.mul_sum] at hcomb
  linarith

/-- Real part of `pauli_purity_identity` for `n = 2` (`q ≠ 0`). -/
private lemma purity_comm_sum (hunit : IsUnitState ψ) {q : PauliIdx 2} (hq : q ≠ 0) :
    ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ q ∧ symp q p = 0 then
        (phaseRe q p : ℝ) * cval ψ p * cval ψ (q + p) else 0) = 2 * cval ψ q := by
  have hc_real : ∀ p : PauliIdx 2, (cval ψ p : ℂ) = innerProd ψ (pauliApply p ψ) :=
    fun p => innerProd_pauliApply_self_real p ψ
  have hpur := congr_arg Complex.re (pauli_purity_identity hunit q)
  rw [Complex.re_sum] at hpur
  have hre_mul : ∀ (x y : ℝ) (z : ℂ), ((x : ℂ) * z * (y : ℂ)).re = z.re * x * y := fun x y z => by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hlhs : ∑ p : PauliIdx 2,
      (innerProd ψ (pauliApply p ψ) * pauliPhase q p * innerProd ψ (pauliApply (q + p) ψ)).re =
      ∑ p : PauliIdx 2, (phaseRe q p : ℝ) * cval ψ p * cval ψ (q + p) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hc_real p, ← hc_real (q + p), hre_mul, pauliPhase_re_eq]
  have hrhs : ((2 : ℂ) ^ 2 * innerProd ψ (pauliApply q ψ)).re = 4 * cval ψ q := by
    rw [← hc_real q]
    have h4 : (2 : ℂ) ^ 2 = ((4 : ℝ) : ℂ) := by norm_num
    rw [h4, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hlhs, hrhs] at hpur
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2))] at hpur
  have hqin : q ∈ Finset.univ.erase (0 : PauliIdx 2) := Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
  rw [← Finset.add_sum_erase _ _ hqin] at hpur
  have ht0 : (phaseRe q 0 : ℝ) * cval ψ 0 * cval ψ (q + 0) = cval ψ q := by
    have hre0 : (phaseRe q 0 : ℝ) = 1 := by
      rw [← pauliPhase_re_eq, pauliPhase_zero_right, Complex.one_re]
    rw [hre0, cval_zero hunit, add_zero]; ring
  have htq : (phaseRe q q : ℝ) * cval ψ q * cval ψ (q + q) = cval ψ q := by
    have hreq : (phaseRe q q : ℝ) = 1 := by
      rw [← pauliPhase_re_eq, pauliPhase_self, Complex.one_re]
    rw [hreq, pauliIdx_add_self, cval_zero hunit]; ring
  rw [ht0, htq] at hpur
  have hrest : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 2)).erase q,
      (phaseRe q p : ℝ) * cval ψ p * cval ψ (q + p) =
      ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ q ∧ symp q p = 0 then
        (phaseRe q p : ℝ) * cval ψ p * cval ψ (q + p) else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)),
        ← Finset.add_sum_erase _ _ hqin]
    rw [if_neg (by simp), if_neg (by simp), zero_add, zero_add]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    rcases zmod2_cases (symp q p) with hs | hs
    · rw [if_pos ⟨hp0, hpq, hs⟩]
    · have hz : phaseRe q p = 0 := by simp [phaseRe, hs]
      rw [if_neg (fun h => by rw [hs] at h; exact absurd h.2.2 (by decide)), hz]; simp
  rw [← hrest]; linarith

/-- Key WHT-Parseval cubic convolution identity for `n = 2`: `∑_p ∑_q g_p g_q g_{p+q} = 4 * F₆`. -/
private lemma sum_gval_conv3 :
    ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, gval ψ p * gval ψ q * gval ψ (p + q) =
      4 * F6 ψ := by
  have hcube : ∑ x : PauliIdx 2, (4 * gval ψ x) ^ 3 = 64 * F6 ψ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
  have hexp : ∑ x : PauliIdx 2, (4 * gval ψ x) ^ 3 =
      ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, ∑ r : PauliIdx 2,
        gval ψ p * gval ψ q * gval ψ r * ∑ x : PauliIdx 2, (sympSign (p + q + r) x : ℝ) := by
    have hstep : ∀ x : PauliIdx 2, (4 * gval ψ x) ^ 3 =
        ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, ∑ r : PauliIdx 2,
          gval ψ p * gval ψ q * gval ψ r * (sympSign (p + q + r) x : ℝ) := fun x => by
      rw [← self_dual_gval (ψ := ψ) x, pow_three]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
        Finset.sum_congr rfl fun r _ => ?_
      rw [sympSign_add_left, sympSign_add_left]; push_cast; ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum]
  rw [hcube] at hexp
  simp_rw [sum_sympSign_two] at hexp
  have hcollapse : ∀ p q : PauliIdx 2,
      (∑ r : PauliIdx 2, gval ψ p * gval ψ q * gval ψ r * (if p + q + r = 0 then (16 : ℝ) else 0)) =
      16 * (gval ψ p * gval ψ q * gval ψ (p + q)) := fun p q => by
    have hiff : ∀ r : PauliIdx 2, p + q + r = 0 ↔ r = p + q := fun r => by
      rw [pauli_add_eq_zero_iff, eq_comm]
    simp_rw [hiff]
    rw [Finset.sum_eq_single (p + q)]
    · rw [if_pos rfl]; ring
    · intro r _ hne; rw [if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hcollapse, ← Finset.mul_sum] at hexp
  linarith

/-- Partition of `∑_{p, q} g_p g_q g_{p+q} = 4 F₆` gives `T_ord + T_anti = 4 F₆ - 3 F₄ + 2`. -/
private lemma Tord_add_Tanti (hunit : IsUnitState ψ) :
    Tord ψ + Tanti ψ = 4 * F6 ψ - 3 * F4 ψ + 2 := by
  have hconv := sum_gval_conv3 (ψ := ψ)
  have hsplit : ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, gval ψ p * gval ψ q * gval ψ (p + q) =
      (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if p = 0 ∨ q = 0 ∨ p = q then gval ψ p * gval ψ q * gval ψ (p + q) else 0) +
      Tord ψ + Tanti ψ := by
    simp only [Tord, Tanti, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases hp : p = 0
    · subst hp
      rw [if_pos (Or.inl rfl), if_neg (by simp), if_neg (by rw [symp_zero_left]; decide)]; ring
    · by_cases hq : q = 0
      · subst hq
        rw [if_pos (Or.inr (Or.inl rfl)), if_neg (by simp), if_neg (by rw [symp_zero_right]; decide)]; ring
      · by_cases hpq : p = q
        · subst hpq
          rw [if_pos (Or.inr (Or.inr rfl)), if_neg (by simp), if_neg (by rw [symp_self]; decide)]; ring
        · have hnot : ¬ (p = 0 ∨ q = 0 ∨ p = q) := fun h => by
            rcases h with rfl | rfl | rfl <;> [exact hp rfl; exact hq rfl; exact hpq rfl]
          rcases zmod2_cases (symp p q) with hs | hs
          · rw [if_neg hnot, if_pos ⟨hp, hq, hpq, hs⟩, if_neg (by rw [hs]; decide)]; ring
          · rw [if_neg hnot, if_neg (fun h => by rw [hs] at h; exact absurd h.2.2.2 (by decide)),
                if_pos hs]; ring
  have hdiag : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if p = 0 ∨ q = 0 ∨ p = q then gval ψ p * gval ψ q * gval ψ (p + q) else 0) =
      3 * F4 ψ - 2 := by
    have hpt : ∀ p q : PauliIdx 2,
        (if p = 0 ∨ q = 0 ∨ p = q then gval ψ p * gval ψ q * gval ψ (p + q) else 0) =
        (if p = 0 then gval ψ q ^ 2 else 0) +
        (if q = 0 then gval ψ p ^ 2 else 0) +
        (if p = q then gval ψ p ^ 2 else 0) -
        (if p = 0 ∧ q = 0 then (2 : ℝ) else 0) := fun p q => by
      by_cases hp : p = 0
      · subst hp
        by_cases hq : q = 0
        · subst hq
          simp only [true_or, and_self, ↓reduceIte, zero_add, gval_zero hunit]; ring
        · have h0q : ¬ ((0 : PauliIdx 2) = q) := Ne.symm hq
          simp only [true_or, hq, h0q, and_false, ↓reduceIte, zero_add, gval_zero hunit]; ring
      · by_cases hq : q = 0
        · subst hq
          simp only [hp, true_or, or_true, false_and, ↓reduceIte, add_zero, gval_zero hunit]; ring
        · by_cases hpq : p = q
          · subst hpq
            simp only [hp, or_true, false_and, ↓reduceIte, pauliIdx_add_self, gval_zero hunit]; ring
          · have hnot : ¬ (p = 0 ∨ q = 0 ∨ p = q) := fun h => by
              rcases h with rfl | rfl | rfl <;> [exact hp rfl; exact hq rfl; exact hpq rfl]
            rw [if_neg hnot, if_neg hp, if_neg hq, if_neg hpq, if_neg (fun h => hp h.1)]; ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have s1 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if p = 0 then gval ψ q ^ 2 else 0) = F4 ψ := by
      rw [Finset.sum_eq_single (0 : PauliIdx 2)]
      · simp [F4]
      · intro p _ hp; simp [hp]
      · intro h; exact absurd (Finset.mem_univ _) h
    have s2 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if q = 0 then gval ψ p ^ 2 else 0) = F4 ψ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_eq_single (0 : PauliIdx 2)]
      · rw [if_pos rfl]
      · intro q _ hq; rw [if_neg hq]
      · intro h; exact absurd (Finset.mem_univ _) h
    have s3 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if p = q then gval ψ p ^ 2 else 0) = F4 ψ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_eq_single p]
      · rw [if_pos rfl]
      · intro q _ hq; rw [if_neg (Ne.symm hq)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have s4 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if p = 0 ∧ q = 0 then (2 : ℝ) else 0) = 2 := by
      rw [Finset.sum_eq_single (0 : PauliIdx 2)]
      · rw [Finset.sum_eq_single (0 : PauliIdx 2)]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro q _ hq; rw [if_neg (fun h => hq h.2)]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro p _ hp; refine Finset.sum_eq_zero fun q _ => by rw [if_neg (fun h => hp h.1)]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [s1, s2, s3, s4]; ring
  linarith

/-! ### Step 5: Exact Algebraic Proofs of SOS Identity B (`Cut 13`) and SOS Identity C (`Cut 15`) -/

/-- **SOS Identity B (Cut 13)**: `10 F₄ - 12 F₆ + 2 T_ord - 4 ≥ 0`. -/
private lemma sos_B_nonneg (hunit : IsUnitState ψ) :
    0 ≤ 10 * F4 ψ - 12 * F6 ψ + 2 * Tord ψ - 4 := by
  let S_B : ℝ := ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
    if symp p q = 1 then gval ψ p * (gval ψ q - gval ψ (p + q)) ^ 2 else 0
  have hnn : 0 ≤ S_B := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact le_rfl
  have hexp : S_B = 10 * F4 ψ - 12 * F6 ψ + 2 * Tord ψ - 4 := by
    have hsplit : S_B =
        (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if symp p q = 1 then gval ψ p * gval ψ q ^ 2 else 0) +
        (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if symp p q = 1 then gval ψ p * gval ψ (p + q) ^ 2 else 0) -
        2 * Tanti ψ := by
      simp only [S_B, Tanti, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> ring
    have hsym : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if symp p q = 1 then gval ψ p * gval ψ (p + q) ^ 2 else 0) =
        ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if symp p q = 1 then gval ψ p * gval ψ q ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft p) _ _ fun q => ?_
      simp [symp_add_right, symp_self]
    have hsqsum : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if symp p q = 1 then gval ψ p * gval ψ q ^ 2 else 0) = 2 * F4 ψ - 2 * F6 ψ := by
      rw [Finset.sum_comm]
      have hinner : ∀ q : PauliIdx 2,
          (∑ p : PauliIdx 2, if symp p q = 1 then gval ψ p * gval ψ q ^ 2 else 0) =
          gval ψ q ^ 2 * (2 - 2 * gval ψ q) := fun q => by
        rw [← sum_gval_anti hunit q, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      simp_rw [hinner]
      simp only [F4, F6, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    have hta := Tord_add_Tanti hunit
    rw [hsplit, hsym, hsqsum]; linarith
  linarith

private lemma sum_gs_gp2_comm (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p ^ 2 else 0) =
      F4 ψ + F6 ψ - 2 := by
  rw [Finset.sum_comm]
  have hinner : ∀ p : PauliIdx 2,
      (∑ s : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p ^ 2 else 0) =
      if p = 0 then 0 else gval ψ p ^ 2 * (1 + gval ψ p) := fun p => by
    by_cases hp : p = 0
    · rw [if_pos hp]; refine Finset.sum_eq_zero fun s _ => by rw [if_neg (by simp [hp])]
    · rw [if_neg hp, ← sum_gval_comm_ne hunit hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hc : s ≠ 0 ∧ s ≠ p ∧ symp s p = 0
      · rw [if_pos ⟨hc.1, hp, Ne.symm hc.2.1, hc.2.2⟩, if_pos hc]; ring
      · rw [if_neg (fun h => hc ⟨h.1, Ne.symm h.2.2.1, h.2.2.2⟩), if_neg hc, mul_zero]
  simp_rw [hinner]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_pos rfl, zero_add]
  have h1 : ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2),
      (if p = 0 then (0 : ℝ) else gval ψ p ^ 2 * (1 + gval ψ p)) =
      ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), (gval ψ p ^ 2 + gval ψ p ^ 3) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [if_neg (Finset.mem_erase.mp hp).1]; ring
  rw [h1, Finset.sum_add_distrib, sum_erase_gval_sq hunit, sum_erase_gval_cube hunit]; ring

private lemma sum_gp_gsp_comm (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p * gval ψ (s + p) else 0) =
      F4 ψ + 2 := by
  have hbij : (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p * gval ψ (s + p) else 0) =
      ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if p ≠ 0 ∧ q ≠ 0 ∧ q ≠ p ∧ symp q p = 0 then gval ψ p * gval ψ q else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight p) _ _ fun s => ?_
    change (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p * gval ψ (s + p) else 0) =
      (if p ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ p ∧ symp (s + p) p = 0 then gval ψ p * gval ψ (s + p) else 0)
    have hcond : (s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0) ↔
        (p ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ p ∧ symp (s + p) p = 0) := by
      simp only [symp_add_left, symp_self, add_zero, ne_eq, pauli_add_eq_zero_iff, pauli_add_eq_right_iff]
      tauto
    by_cases hc : s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
    · rw [if_pos hc, if_pos (hcond.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
  rw [hbij]
  have hinner : ∀ p : PauliIdx 2,
      (∑ q : PauliIdx 2, if p ≠ 0 ∧ q ≠ 0 ∧ q ≠ p ∧ symp q p = 0 then gval ψ p * gval ψ q else 0) =
      if p = 0 then 0 else gval ψ p * (1 + gval ψ p) := fun p => by
    by_cases hp : p = 0
    · rw [if_pos hp]; refine Finset.sum_eq_zero fun q _ => by rw [if_neg (by simp [hp])]
    · rw [if_neg hp, ← sum_gval_comm_ne hunit hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : q ≠ 0 ∧ q ≠ p ∧ symp q p = 0
      · rw [if_pos ⟨hp, h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]
  simp_rw [hinner]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_pos rfl, zero_add]
  have h1 : ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2),
      (if p = 0 then (0 : ℝ) else gval ψ p * (1 + gval ψ p)) =
      ∑ p ∈ Finset.univ.erase (0 : PauliIdx 2), (gval ψ p + gval ψ p ^ 2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [if_neg (Finset.mem_erase.mp hp).1]; ring
  rw [h1, Finset.sum_add_distrib, sum_erase_gval hunit, sum_erase_gval_sq hunit]; ring

private lemma sum_gs_line_triple (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        gval ψ s * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
      2 * (F4 ψ - 1) := by
  have hinner : ∀ s : PauliIdx 2,
      (∑ p : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        gval ψ s * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
      if s = 0 then 0 else 2 * gval ψ s ^ 2 := fun s => by
    by_cases hs : s = 0
    · rw [if_pos hs]; refine Finset.sum_eq_zero fun p _ => by rw [if_neg (by simp [hs])]
    · rw [if_neg hs]
      have hp := purity_comm_sum hunit hs
      have hmul := congr_arg (fun t => gval ψ s * cval ψ s * t) hp
      rw [Finset.mul_sum] at hmul
      have hcongr : (∑ p : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          gval ψ s * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
          ∑ p : PauliIdx 2, gval ψ s * cval ψ s *
            (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (phaseRe s p : ℝ) * cval ψ p * cval ψ (s + p) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hc : p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
        · rw [if_pos ⟨hs, hc⟩, if_pos hc]; ring
        · rw [if_neg (fun h => hc h.2), if_neg hc, mul_zero]
      rw [hcongr, hmul]; simp only [gval]; ring
  simp_rw [hinner]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_pos rfl, zero_add]
  have h1 : ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2), (if s = 0 then (0 : ℝ) else 2 * gval ψ s ^ 2) =
      2 * ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ s ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => by rw [if_neg (Finset.mem_erase.mp hs).1]
  rw [h1, sum_erase_gval_sq hunit]

private lemma sum_gp_line_triple (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        gval ψ p * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
      2 * (F4 ψ - 1) := by
  rw [Finset.sum_comm, ← sum_gs_line_triple hunit]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : p ≠ 0 ∧ s ≠ 0 ∧ s ≠ p ∧ symp p s = 0
  · have hc' : s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 :=
      ⟨hc.2.1, hc.1, Ne.symm hc.2.2.1, by rw [symp_comm]; exact hc.2.2.2⟩
    have hph : phaseRe s p = phaseRe p s := (phaseRe_comm_sym s p hc'.2.2.2).1
    rw [if_pos hc', if_pos hc, hph, add_comm s p]; ring
  · have hc' : ¬ (s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0) := fun h =>
      hc ⟨h.2.1, h.1, Ne.symm h.2.2.1, by rw [symp_comm]; exact h.2.2.2⟩
    rw [if_neg hc', if_neg hc]

private lemma sum_gsp_line_triple (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        gval ψ (s + p) * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
      2 * (F4 ψ - 1) := by
  rw [← sum_gp_line_triple hunit]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun p => ?_
  change (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
      gval ψ (s + p) * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) =
    (if s ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ s ∧ symp s (s + p) = 0 then
      gval ψ (s + p) * ((phaseRe s (s + p) : ℝ) * cval ψ s * cval ψ (s + p) * cval ψ (s + (s + p))) else 0)
  have hcond : (s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0) ↔
      (s ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ s ∧ symp s (s + p) = 0) := by
    simp only [symp_add_right, symp_self, zero_add, ne_eq, pauli_add_eq_zero_iff, pauli_add_eq_left_iff]
    tauto
  by_cases hc : s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
  · have hph : phaseRe s p = phaseRe s (s + p) := (phaseRe_comm_sym s p hc.2.2.2).2
    rw [if_pos hc, if_pos (hcond.mp hc), pauliIdx_add_cancel_left, hph]; ring
  · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]

private lemma sum_line_triple (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        (phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p) else 0) = 6 := by
  have hinner : ∀ s : PauliIdx 2,
      (∑ p : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
        (phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p) else 0) =
      if s = 0 then 0 else 2 * gval ψ s := fun s => by
    by_cases hs : s = 0
    · rw [if_pos hs]; refine Finset.sum_eq_zero fun p _ => by rw [if_neg (by simp [hs])]
    · rw [if_neg hs]
      have hp := purity_comm_sum hunit hs
      have hmul := congr_arg (fun t => cval ψ s * t) hp
      rw [Finset.mul_sum] at hmul
      have hcongr : (∑ p : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          (phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p) else 0) =
          ∑ p : PauliIdx 2, cval ψ s *
            (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (phaseRe s p : ℝ) * cval ψ p * cval ψ (s + p) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hc : p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
        · rw [if_pos ⟨hs, hc⟩, if_pos hc]; ring
        · rw [if_neg (fun h => hc h.2), if_neg hc, mul_zero]
      rw [hcongr, hmul]; simp only [gval]; ring
  simp_rw [hinner]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_pos rfl, zero_add]
  have h1 : ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2), (if s = 0 then (0 : ℝ) else 2 * gval ψ s) =
      2 * ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => by rw [if_neg (Finset.mem_erase.mp hs).1]
  rw [h1, sum_erase_gval hunit]; norm_num

private lemma Tord_comm_reidx :
    (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p * gval ψ (s + p) else 0) =
      Tord ψ := by
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : s ≠ 0 ∧ p ≠ 0 ∧ s ≠ p ∧ symp s p = 0
  · rw [if_pos ⟨hc.1, hc.2.1, Ne.symm hc.2.2.1, hc.2.2.2⟩, if_pos hc]
  · rw [if_neg (fun h => hc ⟨h.1, h.2.1, Ne.symm h.2.2.1, h.2.2.2⟩), if_neg hc]

/-- **SOS Identity C (Cut 15)**: `162 F₆ + 243 T_ord - 93 F₄ - 198 ≥ 0`. -/
private lemma sos_C_nonneg (hunit : IsUnitState ψ) :
    0 ≤ 162 * F6 ψ + 243 * Tord ψ - 93 * F4 ψ - 198 := by
  let R : PauliIdx 2 → PauliIdx 2 → ℝ := fun s p =>
    9 * cval ψ s * (gval ψ p + gval ψ (s + p)) - 2 * (phaseRe s p : ℝ) * cval ψ p * cval ψ (s + p)
  let S_C : ℝ := ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
    if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
      (3 * R s p - cval ψ s * (7 + 9 * gval ψ s)) ^ 2
    else 0
  have hnn : 0 ≤ S_C := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun p _ => by
    split_ifs <;> [exact sq_nonneg _; exact le_rfl]
  have hsum_R : ∀ s : PauliIdx 2, s ≠ 0 →
      ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then R s p else 0) =
      2 * cval ψ s * (7 + 9 * gval ψ s) := fun s hs => by
    have hsp : ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ (s + p) else 0) =
        1 + gval ψ s := by
      have hbi : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ (s + p) else 0) =
          ∑ q : PauliIdx 2, if q ≠ 0 ∧ q ≠ s ∧ symp q s = 0 then gval ψ q else 0 := by
        refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun p => ?_
        change (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ (s + p) else 0) =
          (if s + p ≠ 0 ∧ s + p ≠ s ∧ symp (s + p) s = 0 then gval ψ (s + p) else 0)
        have hcond : (p ≠ 0 ∧ p ≠ s ∧ symp s p = 0) ↔ (s + p ≠ 0 ∧ s + p ≠ s ∧ symp (s + p) s = 0) := by
          simp only [symp_add_left, symp_self, zero_add, symp_comm p s,
              ne_eq, pauli_add_eq_zero_iff, pauli_add_eq_left_iff]
          tauto
        by_cases hc : p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
        · rw [if_pos hc, if_pos (hcond.mp hc)]
        · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
      rw [hbi, sum_gval_comm_ne hunit hs]
    have hp' : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p else 0) = 1 + gval ψ s := by
      rw [← sum_gval_comm_ne hunit hs]
      refine Finset.sum_congr rfl fun p _ => by rw [symp_comm]
    have hpur := purity_comm_sum hunit hs
    have hsplit : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then R s p else 0) =
        9 * cval ψ s * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p else 0) +
        9 * cval ψ s * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ (s + p) else 0) -
        2 * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          (phaseRe s p : ℝ) * cval ψ p * cval ψ (s + p) else 0) := by
      simp only [R, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
    rw [hsplit, hp', hsp, hpur]; ring
  have hSC_red : S_C =
      9 * (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
        if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0) -
      6 * (∑ s : PauliIdx 2, if s ≠ 0 then gval ψ s * (7 + 9 * gval ψ s) ^ 2 else 0) := by
    simp only [S_C, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s = 0
    · rw [if_neg (by simp [hs]), mul_zero, sub_zero]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [if_neg (by simp [hs]), if_neg (by simp [hs]), mul_zero]
    · rw [if_pos hs]
      have hcongr_l : (∑ p : PauliIdx 2, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          (3 * R s p - cval ψ s * (7 + 9 * gval ψ s)) ^ 2 else 0) =
          ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
            (3 * R s p - cval ψ s * (7 + 9 * gval ψ s)) ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hc : p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
        · rw [if_pos ⟨hs, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2), if_neg hc]
      have hcongr_r : (∑ p : PauliIdx 2, (9 : ℝ) * (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0)) =
          9 * ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hc : p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
        · rw [if_pos ⟨hs, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2), if_neg hc]
      rw [hcongr_l, hcongr_r]
      set A := cval ψ s * (7 + 9 * gval ψ s)
      have hexp1 : ∑ p : PauliIdx 2, (if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (3 * R s p - A) ^ 2 else 0) =
          9 * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0) -
          6 * A * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then R s p else 0) +
          A ^ 2 * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (1 : ℝ) else 0) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      rw [hexp1, hsum_R s hs, card_comm_ne_two hs]
      have hA2 : A ^ 2 = gval ψ s * (7 + 9 * gval ψ s) ^ 2 := by simp only [A, gval]; ring
      have hA_eq : 2 * cval ψ s * (7 + 9 * gval ψ s) = 2 * A := by simp only [A]; ring
      rw [hA_eq, ← hA2]; ring
  have hS_sub : (∑ s : PauliIdx 2, if s ≠ 0 then gval ψ s * (7 + 9 * gval ψ s) ^ 2 else 0) =
      126 * F4 ψ + 81 * F6 ψ - 60 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_neg (by simp), zero_add]
    have hpt : ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2),
        (if s ≠ 0 then gval ψ s * (7 + 9 * gval ψ s) ^ 2 else 0) =
        ∑ s ∈ Finset.univ.erase (0 : PauliIdx 2), (49 * gval ψ s + 126 * gval ψ s ^ 2 + 81 * gval ψ s ^ 3) := by
      refine Finset.sum_congr rfl fun s hs => by rw [if_pos (Finset.mem_erase.mp hs).1]; ring
    rw [hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_erase_gval hunit, sum_erase_gval_sq hunit, sum_erase_gval_cube hunit]; ring
  have hR2 : (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
      if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0) =
      22 * F4 ψ + 162 * F6 ψ + 162 * Tord ψ - 172 := by
    have hsplit : (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
        if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then (R s p) ^ 2 else 0) =
        81 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p ^ 2 else 0) +
        81 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ (s + p) ^ 2 else 0) +
        162 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p * gval ψ (s + p) else 0) -
        36 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          gval ψ p * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) -
        36 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then
          gval ψ (s + p) * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p)) else 0) +
        4 * (∑ s, ∑ p, if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ p * gval ψ (s + p) else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
      · have hph2 := phaseRe_sq_one hc.2.2.2
        rw [if_pos hc, if_pos hc, if_pos hc, if_pos hc, if_pos hc, if_pos hc, if_pos hc]
        simp only [R, gval]
        calc (9 * cval ψ s * (cval ψ p ^ 2 + cval ψ (s + p) ^ 2) -
              2 * (phaseRe s p : ℝ) * cval ψ p * cval ψ (s + p)) ^ 2
            = 81 * (cval ψ s ^ 2 * (cval ψ p ^ 2) ^ 2) +
              81 * (cval ψ s ^ 2 * (cval ψ (s + p) ^ 2) ^ 2) +
              162 * (cval ψ s ^ 2 * cval ψ p ^ 2 * cval ψ (s + p) ^ 2) -
              36 * (cval ψ p ^ 2 * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p))) -
              36 * (cval ψ (s + p) ^ 2 * ((phaseRe s p : ℝ) * cval ψ s * cval ψ p * cval ψ (s + p))) +
              4 * ((phaseRe s p : ℝ) ^ 2) * (cval ψ p ^ 2 * cval ψ (s + p) ^ 2) := by ring
          _ = _ := by rw [hph2]; ring
      · rw [if_neg hc, if_neg hc, if_neg hc, if_neg hc, if_neg hc, if_neg hc, if_neg hc]; ring
    have hsym1 : (∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
        if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ (s + p) ^ 2 else 0) =
        ∑ s : PauliIdx 2, ∑ p : PauliIdx 2,
        if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ p ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun p => ?_
      change (if s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0 then gval ψ s * gval ψ (s + p) ^ 2 else 0) =
        (if s ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ s ∧ symp s (s + p) = 0 then gval ψ s * gval ψ (s + p) ^ 2 else 0)
      have hcond : (s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0) ↔
          (s ≠ 0 ∧ s + p ≠ 0 ∧ s + p ≠ s ∧ symp s (s + p) = 0) := by
        rw [symp_add_right, symp_self, zero_add]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨h1, fun h => h3 ((pauli_add_eq_zero_iff s p).mp h).symm,
            fun h => h2 ((pauli_add_eq_left_iff s p).mp h), h4⟩
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨h1, fun h => h3 (by rw [h, add_zero]),
            fun h => h2 (by rw [h, pauliIdx_add_self]), h4⟩
      by_cases hc : s ≠ 0 ∧ p ≠ 0 ∧ p ≠ s ∧ symp s p = 0
      · rw [if_pos hc, if_pos (hcond.mp hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
    rw [hsplit, hsym1, Tord_comm_reidx, sum_gs_gp2_comm hunit, sum_gp_line_triple hunit,
        sum_gsp_line_triple hunit, sum_gp_gsp_comm hunit]; ring
  rw [hSC_red, hR2, hS_sub] at hnn
  linarith

/-! ### Step 6: Exact Algebraic Proof of SOS Identity A (`Cut 10: 28 F₄ - 12 T_ord - 40 ≥ 0`) -/

/-- Shared 3-variable core condition: `u ≠ 0, p, q ∈ u^⊥ \ {0, u}, symp p q = 1`. -/
private abbrev coreCond (u p q : PauliIdx 2) : Prop :=
  u ≠ 0 ∧ p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1

/-- Core sum 1 (`P1_base`): `∑_{coreCond u p q} g_u g_p g_q = F₄ - T_ord + 2`. -/
private lemma P1_base_eq (hunit : IsUnitState ψ) :
    ∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      (if coreCond u p q then gval ψ u * gval ψ p * gval ψ q else 0) =
    F4 ψ - Tord ψ + 2 := by
  have hinner : ∀ u : PauliIdx 2, u ≠ 0 →
      (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
        then gval ψ p * gval ψ q else 0) =
      (1 + gval ψ u) ^ 2 -
      (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p ^ 2 else 0) -
      (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0) := fun u hu => by
    have hsq : (1 + gval ψ u) ^ 2 =
        ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0
          then gval ψ p * gval ψ q else 0 := by
      have h1 : (1 + gval ψ u) = ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p else 0 := by
        rw [← sum_gval_comm_ne hunit hu]
        refine Finset.sum_congr rfl fun p _ => by rw [symp_comm]
      rw [h1, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hp : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
      · by_cases hq : q ≠ 0 ∧ q ≠ u ∧ symp u q = 0
        · rw [if_pos hp, if_pos hq, if_pos ⟨hp.1, hq.1, hp.2.1, hq.2.1, hp.2.2, hq.2.2⟩]
        · rw [if_pos hp, if_neg hq, if_neg (fun h => hq ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩), mul_zero]
      · rw [if_neg hp, zero_mul, if_neg (fun h => hp ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩)]
    have hdecomp : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0
        then gval ψ p * gval ψ q else 0) =
        (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p ^ 2 else 0) +
        (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0) +
        (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
          then gval ψ p * gval ψ q else 0) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
      · have hup_ok : u + p ≠ 0 ∧ u + p ≠ u ∧ symp u (u + p) = 0 :=
          ⟨fun h => hp.2.1 ((pauli_add_eq_zero_iff u p).mp h).symm,
           fun h => hp.1 ((pauli_add_eq_left_iff u p).mp h),
           by rw [symp_add_right, symp_self, zero_add]; exact hp.2.2⟩
        have hne : p ≠ u + p := fun h => hu ((pauli_add_eq_right_iff u p).mp h.symm)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        have hup_in : u + p ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hup_in]
        have h1 : (if p ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ p ≠ u ∧ symp u p = 0 ∧ symp u p = 0
            then gval ψ p * gval ψ p else 0) = gval ψ p ^ 2 := by
          rw [if_pos ⟨hp.1, hp.1, hp.2.1, hp.2.1, hp.2.2, hp.2.2⟩, sq]
        have h2 : (if p ≠ 0 ∧ u + p ≠ 0 ∧ p ≠ u ∧ u + p ≠ u ∧ symp u p = 0 ∧ symp u (u + p) = 0
            then gval ψ p * gval ψ (u + p) else 0) = gval ψ p * gval ψ (u + p) := by
          rw [if_pos ⟨hp.1, hup_ok.1, hp.2.1, hup_ok.2.1, hp.2.2, hup_ok.2.2⟩]
        have h3 : ∑ q ∈ (Finset.univ.erase p).erase (u + p),
            (if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0
             then gval ψ p * gval ψ q else 0) =
            ∑ q : PauliIdx 2,
            (if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
             then gval ψ p * gval ψ q else 0) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hup_in]
          rw [if_neg (fun h => by rw [symp_self] at h; exact absurd h.2.2.2.2.2.2 (by decide)),
              if_neg (fun h => by
                have hs : symp p (u + p) = 0 := by rw [symp_add_right, symp_self, add_zero, symp_comm]; exact hp.2.2
                rw [hs] at h; exact absurd h.2.2.2.2.2.2 (by decide)),
              zero_add, zero_add]
          refine Finset.sum_congr rfl fun q hq => ?_
          have hq_ne_up : q ≠ u + p := (Finset.mem_erase.mp hq).1
          have hq_ne_p : q ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
          by_cases hqc : q ≠ 0 ∧ q ≠ u ∧ symp u q = 0
          · have hsym1 : symp p q = 1 := by
              rcases zmod2_cases (symp p q) with h0 | h1
              · exfalso
                rcases mem_perp_inter_four u p q hu hp.1 hp.2.1 hp.2.2 hqc.2.2 h0 with rfl | rfl | rfl | rfl
                · exact hqc.1 rfl
                · exact hqc.2.1 rfl
                · exact hq_ne_p rfl
                · exact hq_ne_up rfl
              · exact h1
            rw [if_pos ⟨hp.1, hqc.1, hp.2.1, hqc.2.1, hp.2.2, hqc.2.2⟩,
                if_pos ⟨hp.1, hqc.1, hp.2.1, hqc.2.1, hp.2.2, hqc.2.2, hsym1⟩]
          · rw [if_neg (fun h => hqc ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩),
                if_neg (fun h => hqc ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩)]
        rw [h1, h2, h3, if_pos hp, if_pos hp]; ring
      · rw [if_neg hp, if_neg hp, zero_add, zero_add]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [if_neg (fun h => hp ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩),
            if_neg (fun h => hp ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩)]
    linarith
  have hsum : (∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if coreCond u p q then gval ψ u * gval ψ p * gval ψ q else 0) =
      (∑ u : PauliIdx 2, if u ≠ 0 then gval ψ u * (1 + gval ψ u) ^ 2 else 0) -
      (∑ u : PauliIdx 2, ∑ p : PauliIdx 2,
        if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p ^ 2 else 0) -
      (∑ u : PauliIdx 2, ∑ p : PauliIdx 2,
        if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p * gval ψ (u + p) else 0) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = 0
    · rw [if_neg (by simp [hu])]
      have hz1 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if coreCond u p q then gval ψ u * gval ψ p * gval ψ q else 0) = 0 :=
        Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => by rw [if_neg (by simp [coreCond, hu])]
      have hz2 : (∑ p : PauliIdx 2, if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p ^ 2 else 0) = 0 :=
        Finset.sum_eq_zero fun p _ => by rw [if_neg (by simp [hu])]
      have hz3 : (∑ p : PauliIdx 2, if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p * gval ψ (u + p) else 0) = 0 :=
        Finset.sum_eq_zero fun p _ => by rw [if_neg (by simp [hu])]
      rw [hz1, hz2, hz3]; ring
    · rw [if_pos hu]
      have hi := congr_arg (gval ψ u * ·) (hinner u hu)
      have hl : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if coreCond u p q then gval ψ u * gval ψ p * gval ψ q else 0) =
          gval ψ u * (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
            if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
            then gval ψ p * gval ψ q else 0) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        by_cases h : p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
        · rw [if_pos ⟨hu, h⟩, if_pos h]; ring
        · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]
      have hr1 : gval ψ u * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p ^ 2 else 0) =
          ∑ p : PauliIdx 2, if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p ^ 2 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
        · rw [if_pos h, if_pos ⟨hu, h⟩]
        · rw [if_neg h, if_neg (fun h' => h h'.2), mul_zero]
      have hr2 : gval ψ u * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0) =
          ∑ p : PauliIdx 2, if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p * gval ψ (u + p) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
        · rw [if_pos h, if_pos ⟨hu, h⟩]; ring
        · rw [if_neg h, if_neg (fun h' => h h'.2), mul_zero]
      rw [hl, hi, mul_sub, mul_sub, hr1, hr2]
  have hterm1 : (∑ u : PauliIdx 2, if u ≠ 0 then gval ψ u * (1 + gval ψ u) ^ 2 else 0) =
      2 * F4 ψ + F6 ψ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_neg (by simp), zero_add]
    have hpt : ∑ u ∈ Finset.univ.erase (0 : PauliIdx 2),
        (if u ≠ 0 then gval ψ u * (1 + gval ψ u) ^ 2 else 0) =
        ∑ u ∈ Finset.univ.erase (0 : PauliIdx 2), (gval ψ u + 2 * gval ψ u ^ 2 + gval ψ u ^ 3) := by
      refine Finset.sum_congr rfl fun u hu => by rw [if_pos (Finset.mem_erase.mp hu).1]; ring
    rw [hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_erase_gval hunit, sum_erase_gval_sq hunit, sum_erase_gval_cube hunit]; ring
  rw [hsum, hterm1, sum_gs_gp2_comm hunit, Tord_comm_reidx]; ring

/-- Core sum 2 (`P2_core`): `∑_{coreCond u p q} g_u (phaseRe u p c_p c_{u+p}) (phaseRe u q c_q c_{u+q}) = 4 F₄ - 2 T_ord - 4`. -/
private lemma P2_core_eq (hunit : IsUnitState ψ) :
    ∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      (if coreCond u p q then
        gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
          ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) =
    4 * F4 ψ - 2 * Tord ψ - 4 := by
  -- For fixed `u ≠ 0`, squaring `∑_{p ∈ u^⊥\{0,u}} L(p) = 2 c_u` gives
  -- `4 g_u = 2 ∑_{p ∈ u^⊥\{0,u}} g_p g_{u+p} + ∑_{p,q ∈ u^⊥\{0,u}, ω(p,q)=1} L(p) L(q)`!
  -- OH!! We don't even need `s` at all!! Multiply by `g_u` and sum over `u ≠ 0` directly!!
  have hinner : ∀ u : PauliIdx 2, u ≠ 0 →
      (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
        then ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
             ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) =
      4 * gval ψ u -
      2 * (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0) := fun u hu => by
    let L : PauliIdx 2 → ℝ := fun p => (phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)
    have hsq := congr_arg (fun t : ℝ => t ^ 2) (purity_comm_sum hunit hu)
    have hsq_r : (2 * cval ψ u) ^ 2 = 4 * gval ψ u := by simp only [gval]; ring
    rw [hsq_r] at hsq
    have hdecomp : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then L p else 0) ^ 2 =
        (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then 2 * L p ^ 2 else 0) +
        (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
          then L p * L q else 0) := by
      rw [sq, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      by_cases hp : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
      · have hup_ok : u + p ≠ 0 ∧ u + p ≠ u ∧ symp u (u + p) = 0 :=
          ⟨fun h => hp.2.1 ((pauli_add_eq_zero_iff u p).mp h).symm,
           fun h => hp.1 ((pauli_add_eq_left_iff u p).mp h),
           by rw [symp_add_right, symp_self, zero_add]; exact hp.2.2⟩
        have hne : p ≠ u + p := fun h => hu ((pauli_add_eq_right_iff u p).mp h.symm)
        have hLp : L (u + p) = L p := by
          simp only [L, pauliIdx_add_cancel_left, ← (phaseRe_comm_sym u p hp.2.2).2]; ring
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        have hup_in : u + p ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hup_in]
        have h1 : (if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then L p else 0) *
            (if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then L p else 0) = L p ^ 2 := by rw [if_pos hp, sq]
        have h2 : (if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then L p else 0) *
            (if u + p ≠ 0 ∧ u + p ≠ u ∧ symp u (u + p) = 0 then L (u + p) else 0) = L p ^ 2 := by
          rw [if_pos hp, if_pos hup_ok, hLp, sq]
        have h3 : ∑ q ∈ (Finset.univ.erase p).erase (u + p),
            (if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then L p else 0) *
            (if q ≠ 0 ∧ q ≠ u ∧ symp u q = 0 then L q else 0) =
            ∑ q : PauliIdx 2,
            (if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
             then L p * L q else 0) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hup_in]
          have hz1 : (if p ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ p ≠ u ∧ symp u p = 0 ∧ symp u p = 0 ∧ symp p p = 1
              then L p * L p else 0) = 0 :=
            if_neg (fun h => by rw [symp_self] at h; exact absurd h.2.2.2.2.2.2 (by decide))
          have hz2 : (if p ≠ 0 ∧ u + p ≠ 0 ∧ p ≠ u ∧ u + p ≠ u ∧ symp u p = 0 ∧ symp u (u + p) = 0 ∧ symp p (u + p) = 1
              then L p * L (u + p) else 0) = 0 :=
            if_neg (fun h => by
              have hs : symp p (u + p) = 0 := by rw [symp_add_right, symp_self, add_zero, symp_comm]; exact hp.2.2
              rw [hs] at h; exact absurd h.2.2.2.2.2.2 (by decide))
          rw [hz1, hz2, zero_add, zero_add]
          refine Finset.sum_congr rfl fun q hq => ?_
          have hq_ne_up : q ≠ u + p := (Finset.mem_erase.mp hq).1
          have hq_ne_p : q ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
          by_cases hqc : q ≠ 0 ∧ q ≠ u ∧ symp u q = 0
          · have hsym1 : symp p q = 1 := by
              rcases zmod2_cases (symp p q) with h0 | h1
              · exfalso
                rcases mem_perp_inter_four u p q hu hp.1 hp.2.1 hp.2.2 hqc.2.2 h0 with rfl | rfl | rfl | rfl
                · exact hqc.1 rfl
                · exact hqc.2.1 rfl
                · exact hq_ne_p rfl
                · exact hq_ne_up rfl
              · exact h1
            rw [if_pos hp, if_pos hqc, if_pos ⟨hp.1, hqc.1, hp.2.1, hqc.2.1, hp.2.2, hqc.2.2, hsym1⟩]
          · rw [if_pos hp, if_neg hqc, mul_zero,
                if_neg (fun h => hqc ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩)]
        rw [h1, h2, h3, if_pos hp]; ring
      · have h0 : (if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then 2 * L p ^ 2 else 0) = 0 := if_neg hp
        rw [h0, zero_add]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [if_neg hp, zero_mul, if_neg (fun h => hp ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩)]
    have hL2 : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then 2 * L p ^ 2 else 0) =
        2 * ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
      · have hph2 := phaseRe_sq_one hp.2.2
        rw [if_pos hp, if_pos hp]; simp only [L, gval]
        calc 2 * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) ^ 2
            = 2 * (phaseRe u p : ℝ) ^ 2 * (cval ψ p ^ 2 * cval ψ (u + p) ^ 2) := by ring
          _ = 2 * (cval ψ p ^ 2 * cval ψ (u + p) ^ 2) := by rw [hph2]; ring
      · rw [if_neg hp, if_neg hp, mul_zero]
    rw [hdecomp, hL2] at hsq
    linarith
  have hsum : (∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if coreCond u p q then
        gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
          ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) =
      4 * (∑ u : PauliIdx 2, if u ≠ 0 then gval ψ u ^ 2 else 0) -
      2 * (∑ u : PauliIdx 2, ∑ p : PauliIdx 2,
        if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p * gval ψ (u + p) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = 0
    · rw [if_neg (by simp [hu]), mul_zero]
      have hz1 : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if coreCond u p q then
          gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
            ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) = 0 :=
        Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => by rw [if_neg (by simp [coreCond, hu])]
      have hz2 : (∑ p : PauliIdx 2, (2 : ℝ) * (if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then
          gval ψ u * gval ψ p * gval ψ (u + p) else 0)) = 0 :=
        Finset.sum_eq_zero fun p _ => by rw [if_neg (by simp [hu]), mul_zero]
      rw [hz1, hz2]; ring
    · rw [if_pos hu]
      have hi := congr_arg (gval ψ u * ·) (hinner u hu)
      have hl : (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if coreCond u p q then
            gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
              ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) =
          gval ψ u * (∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
            if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
            then ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
                 ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        by_cases h : p ≠ 0 ∧ q ≠ 0 ∧ p ≠ u ∧ q ≠ u ∧ symp u p = 0 ∧ symp u q = 0 ∧ symp p q = 1
        · rw [if_pos ⟨hu, h⟩, if_pos h]; ring
        · rw [if_neg (fun h' => h h'.2), if_neg h, mul_zero]
      have hr : 2 * (gval ψ u * ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ p * gval ψ (u + p) else 0) =
          ∑ p : PauliIdx 2, (2 : ℝ) * (if u ≠ 0 ∧ p ≠ 0 ∧ p ≠ u ∧ symp u p = 0 then gval ψ u * gval ψ p * gval ψ (u + p) else 0) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p ≠ 0 ∧ p ≠ u ∧ symp u p = 0
        · rw [if_pos h, if_pos ⟨hu, h⟩]; ring
        · rw [if_neg h, if_neg (fun h' => h h'.2)]; ring
      rw [hl, hi]; linarith
  have h1 : (∑ u : PauliIdx 2, if u ≠ 0 then gval ψ u ^ 2 else 0) = F4 ψ - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 2)), if_neg (by simp), zero_add]
    have hpt : ∑ u ∈ Finset.univ.erase (0 : PauliIdx 2), (if u ≠ 0 then gval ψ u ^ 2 else 0) =
        ∑ u ∈ Finset.univ.erase (0 : PauliIdx 2), gval ψ u ^ 2 :=
      Finset.sum_congr rfl fun u hu => if_pos (Finset.mem_erase.mp hu).1
    rw [hpt, sum_erase_gval_sq hunit]
  rw [hsum, h1, Tord_comm_reidx]; ring

/-- Core sum 3 (`P3_base`): directly from `pauli_prod_eq_conv` + `P1_base_eq` + `P2_core_eq`!
    `∑_{y, w comm} ∑_{a ∈ y^⊥, ω(w,a)=1} ∑_{q ∉ y^⊥, ω(w,q)=1} tr4(a,q,a+w) g_y c_a c_{a+w} c_q c_{q+w} = -6 F₄ + 2 T_ord + 12`. -/
private lemma P3_base_eq (hunit : IsUnitState ψ) :
    ∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2, ∑ q : PauliIdx 2,
      (if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
          symp y q = 1 ∧ symp w q = 1
       then (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w)
       else 0) =
    -6 * F4 ψ + 2 * Tord ψ + 12 := by
  have hinner : ∀ y w a : PauliIdx 2,
      y ≠ 0 → w ≠ 0 → w ≠ y → symp y w = 0 → symp y a = 0 → symp w a = 1 →
      (∑ q : PauliIdx 2, if symp y q = 1 ∧ symp w q = 1 then
          (trace4Int a q (a + w) : ℝ) * cval ψ q * cval ψ (q + w) else 0) =
      2 * cval ψ a * cval ψ (a + w) -
      2 * (phaseRe y a : ℝ) * (phaseRe y (a + w) : ℝ) * cval ψ (y + a) * cval ψ (y + a + w) := by
    intro y w a hy hw hwy hyw hya hwa
    have hconv := pauli_prod_eq_conv ψ a (a + w)
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h4] at hconv
    have hadd : ∀ p : PauliIdx 2, a + p + (a + w) = p + w := fun p => by
      calc a + p + (a + w) = (a + a) + (p + w) := by abel
        _ = p + w := by rw [pauliIdx_add_self, zero_add]
    simp_rw [hadd] at hconv
    have hsplit : (∑ p : PauliIdx 2, (trace4Int a p (a + w) : ℝ) * cval ψ p * cval ψ (p + w)) =
        (∑ p : PauliIdx 2, if symp y p = 0 ∧ symp w p = 1 then
          (trace4Int a p (a + w) : ℝ) * cval ψ p * cval ψ (p + w) else 0) +
        (∑ q : PauliIdx 2, if symp y q = 1 ∧ symp w q = 1 then
          (trace4Int a q (a + w) : ℝ) * cval ψ q * cval ψ (q + w) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rcases zmod2_cases (symp w p) with h0 | h1
      · have hz := trace4Int_zero_of_symp w a p hwa h0
        rw [hz, if_neg (fun h => by rw [h0] at h; exact absurd h.2 (by decide)),
            if_neg (fun h => by rw [h0] at h; exact absurd h.2 (by decide))]; simp
      · rcases zmod2_cases (symp y p) with hy0 | hy1
        · rw [if_pos ⟨hy0, h1⟩, if_neg (fun h => by rw [hy0] at h; exact absurd h.1 (by decide)), add_zero]
        · rw [if_neg (fun h => by rw [hy1] at h; exact absurd h.1 (by decide)), if_pos ⟨hy1, h1⟩, zero_add]
    have h4terms : (∑ p : PauliIdx 2, if symp y p = 0 ∧ symp w p = 1 then
        (trace4Int a p (a + w) : ℝ) * cval ψ p * cval ψ (p + w) else 0) =
        2 * cval ψ a * cval ψ (a + w) +
        2 * (phaseRe y a : ℝ) * (phaseRe y (a + w) : ℝ) * cval ψ (y + a) * cval ψ (y + a + w) := by
      have h12 : a ≠ a + w := fun h => hw ((pauli_add_eq_left_iff a w).mp h.symm)
      have h13 : a ≠ y + a := fun h => hy ((pauli_add_eq_right_iff y a).mp h.symm)
      have h14 : a ≠ y + a + w := fun h => by
        have h' : y + w = 0 := by
          have := congr_arg (· + a) h; rw [pauliIdx_add_self] at this
          calc y + w = (y + w) + (a + a) := by rw [pauliIdx_add_self, add_zero]
            _ = y + a + w + a := by abel
            _ = 0 := this.symm
        exact hwy ((pauli_add_eq_zero_iff y w).mp h').symm
      have h23 : a + w ≠ y + a := fun h => by
        have h' : y + w = 0 := by
          have := congr_arg (· + a) h
          calc y + w = (y + a + a) + w := by rw [pauliIdx_add_cancel_right]
            _ = (a + w + a) + w := by rw [← this]
            _ = (a + a) + (w + w) := by abel
            _ = 0 := by rw [pauliIdx_add_self, pauliIdx_add_self, add_zero]
        exact hwy ((pauli_add_eq_zero_iff y w).mp h').symm
      have h24 : a + w ≠ y + a + w := fun h => by
        have := congr_arg (· + (a + w)) h
        rw [pauliIdx_add_self] at this
        have h' : y = 0 := by
          calc y = y + a + w + (a + w) := by
                calc y = y + (a + a) + (w + w) := by rw [pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero]
                  _ = y + a + w + (a + w) := by abel
            _ = 0 := this.symm
        exact hy h'
      have h34 : y + a ≠ y + a + w := fun h => hw ((pauli_add_eq_left_iff (y + a) w).mp h.symm)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      have h2in : a + w ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm h12, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ h2in]
      have h3in : y + a ∈ (Finset.univ.erase a).erase (a + w) :=
        Finset.mem_erase.mpr ⟨Ne.symm h23, Finset.mem_erase.mpr ⟨Ne.symm h13, Finset.mem_univ _⟩⟩
      rw [← Finset.add_sum_erase _ _ h3in]
      have h4in : y + a + w ∈ ((Finset.univ.erase a).erase (a + w)).erase (y + a) :=
        Finset.mem_erase.mpr ⟨Ne.symm h34,
          Finset.mem_erase.mpr ⟨Ne.symm h24,
            Finset.mem_erase.mpr ⟨Ne.symm h14, Finset.mem_univ _⟩⟩⟩
      rw [← Finset.add_sum_erase _ _ h4in]
      have hrest : ∑ p ∈ (((Finset.univ.erase a).erase (a + w)).erase (y + a)).erase (y + a + w),
          (if symp y p = 0 ∧ symp w p = 1 then (trace4Int a p (a + w) : ℝ) * cval ψ p * cval ψ (p + w) else 0) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have h4ne : p ≠ y + a + w := (Finset.mem_erase.mp hp).1
        have h3ne : p ≠ y + a := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have h2ne : p ≠ a + w := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2).1
        have h1ne : p ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2).2).1
        rw [if_neg]
        intro ⟨hyp, hwp⟩
        rcases mem_perp_anti_four y w a p hy hw hwy hyw hya hwa hyp hwp with rfl | rfl | rfl | rfl
        · exact h1ne rfl
        · exact h2ne rfl
        · exact h3ne rfl
        · exact h4ne rfl
      rw [hrest, add_zero]
      have hs1 : symp y a = 0 ∧ symp w a = 1 := ⟨hya, hwa⟩
      have hs2 : symp y (a + w) = 0 ∧ symp w (a + w) = 1 :=
        ⟨by rw [symp_add_right, hya, hyw, add_zero], by rw [symp_add_right, hwa, symp_self, add_zero]⟩
      have hs3 : symp y (y + a) = 0 ∧ symp w (y + a) = 1 :=
        ⟨by rw [symp_add_right, symp_self, zero_add]; exact hya,
         by rw [symp_add_right, symp_comm w y, hyw, zero_add]; exact hwa⟩
      have hs4 : symp y (y + a + w) = 0 ∧ symp w (y + a + w) = 1 :=
        ⟨by rw [symp_add_right, hs3.1, hyw, add_zero],
         by rw [symp_add_right, hs3.2, symp_self, add_zero]⟩
      have ht1 := (trace4Int_self a w).1
      have ht2 := (trace4Int_self a w).2
      have ht3 := (trace4Int_other y w a hyw hya).1
      have ht4 := (trace4Int_other y w a hyw hya).2
      rw [if_pos hs1, if_pos hs2, if_pos hs3, if_pos hs4, ht1, ht2, ht3, ht4,
          pauliIdx_add_cancel_right, pauliIdx_add_cancel_right]
      push_cast; ring
    rw [hsplit, h4terms] at hconv; linarith
  have hsum : (∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2, ∑ q : PauliIdx 2,
      if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧ symp y q = 1 ∧ symp w q = 1
      then (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) =
      2 * (∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
        then gval ψ y * gval ψ a * gval ψ (a + w) else 0) -
      2 * (∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
        then gval ψ y * ((phaseRe y a : ℝ) * cval ψ a * cval ψ (y + a)) *
             ((phaseRe y (a + w) : ℝ) * cval ψ (a + w) * cval ψ (y + (a + w))) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => ?_
    by_cases hc : y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
    · have hi := congr_arg (fun t => gval ψ y * cval ψ a * cval ψ (a + w) * t)
        (hinner y w a hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
      rw [Finset.mul_sum] at hi
      have hl : (∑ q : PauliIdx 2,
          if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧ symp y q = 1 ∧ symp w q = 1
          then (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) =
          ∑ q : PauliIdx 2, gval ψ y * cval ψ a * cval ψ (a + w) *
            (if symp y q = 1 ∧ symp w q = 1 then (trace4Int a q (a + w) : ℝ) * cval ψ q * cval ψ (q + w) else 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases hq : symp y q = 1 ∧ symp w q = 1
        · rw [if_pos ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2, hq.1, hq.2⟩, if_pos hq]; ring
        · rw [if_neg (fun h => hq ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩), if_neg hq, mul_zero]
      rw [hl, hi, if_pos hc, if_pos hc]
      simp only [gval, add_assoc]; ring
    · rw [if_neg hc, if_neg hc]
      have hz : (∑ q : PauliIdx 2,
          if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧ symp y q = 1 ∧ symp w q = 1
          then (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) = 0 :=
        Finset.sum_eq_zero fun q _ => if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)
      rw [hz]; ring
  -- Both sums reindex 1-to-1 via `(y, w, a) ↦ (y, a, b = a + w)` directly to `P1_base_eq` and `P2_core_eq`!
  have hcond_eq : ∀ y a b : PauliIdx 2,
      (y ≠ 0 ∧ a + b ≠ 0 ∧ a + b ≠ y ∧ symp y (a + b) = 0 ∧ symp y a = 0 ∧ symp (a + b) a = 1) ↔
      coreCond y a b := fun y a b => by
    constructor
    · rintro ⟨hy, hab0, haby, hyab, hya, haba⟩
      have hyb : symp y b = 0 := by rw [symp_add_right, hya, zero_add] at hyab; exact hyab
      have hba : symp b a = 1 := by rw [symp_add_left, symp_self, zero_add] at haba; exact haba
      have hab : symp a b = 1 := by rw [symp_comm]; exact hba
      have ha0 : a ≠ 0 := fun h => by rw [h, symp_zero_left] at hab; exact absurd hab (by decide)
      have hb0 : b ≠ 0 := fun h => by rw [h, symp_zero_right] at hab; exact absurd hab (by decide)
      have hay : a ≠ y := fun h => by rw [h, hyb] at hab; exact absurd hab (by decide)
      have hby : b ≠ y := fun h => by rw [h, symp_comm, hya] at hab; exact absurd hab (by decide)
      exact ⟨hy, ha0, hb0, hay, hby, hya, hyb, hab⟩
    · rintro ⟨hy, _, _, _, _, hya, hyb, hab⟩
      have hab0 : a + b ≠ 0 := fun h => by
        rw [(pauli_add_eq_zero_iff a b).mp h, symp_self] at hab; exact absurd hab (by decide)
      have haby : a + b ≠ y := fun h => by
        have h1 : symp (a + b) a = 0 := by rw [h]; exact hya
        rw [symp_add_left, symp_self, zero_add, symp_comm b a, hab] at h1; exact absurd h1 (by decide)
      exact ⟨hy, hab0, haby, by rw [symp_add_right, hya, hyb, add_zero], hya,
        by rw [symp_add_left, symp_self, zero_add, symp_comm]; exact hab⟩
  have hsum1 : (∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2,
      if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
      then gval ψ y * gval ψ a * gval ψ (a + w) else 0) = F4 ψ - Tord ψ + 2 := by
    rw [← P1_base_eq hunit]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun w => ?_
    change (if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
        then gval ψ y * gval ψ a * gval ψ (a + w) else 0) =
      (if coreCond y a (a + w) then gval ψ y * gval ψ a * gval ψ (a + w) else 0)
    have hiff := hcond_eq y a (a + w)
    rw [pauliIdx_add_cancel_left] at hiff
    by_cases hc : coreCond y a (a + w)
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  have hsum2 : (∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2,
      if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
      then gval ψ y * ((phaseRe y a : ℝ) * cval ψ a * cval ψ (y + a)) *
           ((phaseRe y (a + w) : ℝ) * cval ψ (a + w) * cval ψ (y + (a + w))) else 0) =
      4 * F4 ψ - 2 * Tord ψ - 4 := by
    rw [← P2_core_eq hunit]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun w => ?_
    change (if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1
        then gval ψ y * ((phaseRe y a : ℝ) * cval ψ a * cval ψ (y + a)) *
             ((phaseRe y (a + w) : ℝ) * cval ψ (a + w) * cval ψ (y + (a + w))) else 0) =
      (if coreCond y a (a + w)
        then gval ψ y * ((phaseRe y a : ℝ) * cval ψ a * cval ψ (y + a)) *
             ((phaseRe y (a + w) : ℝ) * cval ψ (a + w) * cval ψ (y + (a + w))) else 0)
    have hiff := hcond_eq y a (a + w)
    rw [pauliIdx_add_cancel_left] at hiff
    by_cases hc : coreCond y a (a + w)
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  rw [hsum, hsum1, hsum2]; ring

/-- Predicate for `u ∈ T(s, r) := {u ∈ s^⊥ \ {0, s} | symp r u = 1}`. -/
private abbrev inT (s r u : PauliIdx 2) : Prop :=
  u ≠ 0 ∧ u ≠ s ∧ symp s u = 0 ∧ symp r u = 1

/-- Key fiber-count lemma: for fixed `(u, p, q)` with `coreCond u p q`,
    there are EXACTLY 2 elements `v` with `symp (u+p+q) (p+v) = 1 ∧ inT (u+p+q) (p+v) u ∧ inT (u+p+q) (p+v) v ∧ v ≠ u`. -/
private lemma fiber_T_pair_count (u p q : PauliIdx 2) :
    (∑ v : PauliIdx 2,
      if symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
         inT (u + p + q) (p + v) v ∧ v ≠ u then (1 : ℝ) else 0) =
    if coreCond u p q then 2 else 0 := by
  by_cases hc : coreCond u p q
  · rw [if_pos hc]
    rcases hc with ⟨hu, hp0, hq0, hpu, hqu, hup, huq, hpq⟩
    have hiff : ∀ v : PauliIdx 2,
        (symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
         inT (u + p + q) (p + v) v ∧ v ≠ u) ↔
        (symp u v = 1 ∧ symp p v = 1 ∧ symp q v = 0) := fun v => by
      constructor
      · rintro ⟨hsr, ⟨_, _, _, hru⟩, ⟨_, _, hsv, hrv⟩, _⟩
        have huv : symp u v = 1 := by
          rw [symp_add_left, symp_comm p u, hup, zero_add, symp_comm v u] at hru; exact hru
        have hpv : symp p v = 1 := by
          rw [symp_add_left, symp_self, add_zero] at hrv; exact hrv
        have hqv : symp q v = 0 := by
          rw [symp_add_left, symp_add_left, huv, hpv] at hsv
          rcases zmod2_cases (symp q v) with h0 | h1
          · exact h0
          · rw [h1] at hsv; exact absurd hsv (by decide)
        exact ⟨huv, hpv, hqv⟩
      · rintro ⟨huv, hpv, hqv⟩
        have hsr : symp (u + p + q) (p + v) = 1 := by
          simp only [symp_add_left, symp_add_right, hup, symp_self, symp_comm q p, hpq, huv, hpv, hqv]; decide
        have hru : symp (p + v) u = 1 := by
          rw [symp_add_left, symp_comm p u, hup, zero_add, symp_comm v u, huv]
        have hsu : symp (u + p + q) u = 0 := by
          simp only [symp_add_left, symp_self, symp_comm p u, hup, symp_comm q u, huq]; decide
        have hus : u ≠ u + p + q := fun h => by
          have : p + q = 0 := by
            have := congr_arg (u + ·) h
            calc p + q = u + (u + p + q) := by
                  calc p + q = (u + u) + (p + q) := by rw [pauliIdx_add_self, zero_add]
                    _ = u + (u + p + q) := by abel
              _ = u + u := by rw [← this]
              _ = 0 := pauliIdx_add_self u
          rw [(pauli_add_eq_zero_iff p q).mp this, symp_self] at hpq; exact absurd hpq (by decide)
        have hv0 : v ≠ 0 := fun h => by rw [h, symp_zero_right] at huv; exact absurd huv (by decide)
        have hvu : v ≠ u := fun h => by rw [h, symp_self] at huv; exact absurd huv (by decide)
        have hvs : v ≠ u + p + q := fun h => by
          have : symp q v = 1 := by rw [h, symp_add_right, symp_add_right, symp_comm q u, huq, symp_comm q p, hpq, symp_self]; decide
          rw [hqv] at this; exact absurd this (by decide)
        have hsv : symp (u + p + q) v = 0 := by
          simp only [symp_add_left, huv, hpv, hqv]; decide
        have hrv : symp (p + v) v = 1 := by
          rw [symp_add_left, hpv, symp_self, add_zero]
        exact ⟨hsr, ⟨hu, hus, hsu, hru⟩, ⟨hv0, hvs, hsv, hrv⟩, hvu⟩
    have hcongr : (∑ v : PauliIdx 2,
        if symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
           inT (u + p + q) (p + v) v ∧ v ≠ u then (1 : ℝ) else 0) =
        ∑ v : PauliIdx 2, if symp u v = 1 ∧ symp p v = 1 ∧ symp q v = 0 then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : symp u v = 1 ∧ symp p v = 1 ∧ symp q v = 0
      · rw [if_pos ((hiff v).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((hiff v).mp h')), if_neg h]
    rw [hcongr, card_symp_three_cond u p q hu hup huq hpq 1 1 0]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg]
    rintro ⟨hsr, ⟨hu, hus, hsu, hru⟩, ⟨hv0, hvs, hsv, hrv⟩, hvu⟩
    apply hc
    have hpv : symp p v = 1 := by rw [symp_add_left, symp_self, add_zero] at hrv; exact hrv
    have hup_eq : symp u p = symp u q := by
      rw [symp_add_left, symp_add_left, symp_self, zero_add, symp_comm p u, symp_comm q u] at hsu
      rcases zmod2_cases (symp u p) with h1 | h1 <;> rcases zmod2_cases (symp u q) with h2 | h2 <;>
        simp_all [show (1 : ZMod 2) + 1 = 0 by decide]
    -- Also `symp (u+p+q) v = 0` and `symp (p+v) u = 1` gives `symp p u + symp v u = 1`;
    -- and `symp (u+p+q) (p+v) = 1` reduces to `symp (u+p+q) p = 1` -> `symp u p + symp q p = 1`!
    -- Wait: why does `symp u p = 0` follow?! Because `u ∈ T(s, r)` and `v ∈ T(s, r) \ {u}` implies `symp u v = 1`!!
    have huv : symp u v = 1 := by
      rcases zmod2_cases (symp u v) with h0 | h1
      · exfalso
        have hs0 : u + p + q ≠ 0 := fun h => by rw [h, symp_zero_left] at hsr; exact absurd hsr (by decide)
        rcases mem_perp_inter_four (u + p + q) u v hs0 hu hus hsu hsv h0 with rfl | rfl | rfl | rfl
        · exact hv0 rfl
        · exact hvs rfl
        · exact hvu rfl
        · rw [symp_add_right, symp_comm _ (u + p + q), hsr, hru] at hrv
          exact absurd hrv (by decide)
      · exact h1
    have hup : symp u p = 0 := by
      rw [symp_add_left, symp_comm p u, symp_comm v u, huv] at hru
      rcases zmod2_cases (symp u p) with h0 | h1
      · exact h0
      · rw [h1] at hru; exact absurd hru (by decide)
    have huq : symp u q = 0 := hup_eq.symm.trans hup
    have hpq : symp p q = 1 := by
      rw [symp_add_right, hsv, add_zero, symp_add_left, symp_add_left, hup, symp_self, zero_add,
          zero_add, symp_comm q p] at hsr
      exact hsr
    have hp0 : p ≠ 0 := fun h => by rw [h, symp_zero_left] at hpq; exact absurd hpq (by decide)
    have hq0 : q ≠ 0 := fun h => by rw [h, symp_zero_right] at hpq; exact absurd hpq (by decide)
    have hpu : p ≠ u := fun h => by rw [h, huq] at hpq; exact absurd hpq (by decide)
    have hqu : q ≠ u := fun h => by rw [h, symp_comm p u, hup] at hpq; exact absurd hpq (by decide)
    exact ⟨hu, hp0, hq0, hpu, hqu, hup, huq, hpq⟩

/-- Helper: `P4_s_prod := ∑_{s, r, uk} c_{r+uk} c_{r+s+uk} (c_{r+s+uk} - Lz0) (c_{r+uk} - Ly0) = 4 + 2 F₄ - 2 T_ord`. -/
private lemma P4_s_prod_eq (hunit : IsUnitState ψ) :
    ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      (if symp s r = 1 ∧ inT s r uk then
        cval ψ (r + uk) * cval ψ (r + s + uk) *
          (cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
          (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk))
       else 0) =
    4 + 2 * F4 ψ - 2 * Tord ψ := by
  have hsplit : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        cval ψ (r + uk) * cval ψ (r + s + uk) *
          (cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
          (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk))
      else 0) =
      (∑ s, ∑ r, ∑ uk, if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) -
      (∑ s, ∑ r, ∑ uk, if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) -
      (∑ s, ∑ r, ∑ uk, if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ (r + s + uk) * cval ψ r * cval ψ (s + uk)) else 0) +
      (∑ s, ∑ r, ∑ uk, if symp s r = 1 ∧ inT s r uk then
        gval ψ (s + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (r + s + uk)) *
          ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (r + uk)) else 0) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun uk _ => ?_
    by_cases hc : symp s r = 1 ∧ inT s r uk
    · rw [if_pos hc, if_pos hc, if_pos hc, if_pos hc, if_pos hc]; simp only [gval]; ring
    · rw [if_neg hc, if_neg hc, if_neg hc, if_neg hc, if_neg hc]; ring
  -- Term 1: `24 - 6 F₄` (3-to-1 onto `{(a, b) | symp a b = 1}`!)
  have ht1 : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) =
      24 - 6 * F4 ψ := by
    -- Reindex `(s, r, uk) ↦ (a = r + uk, b = r + s + uk, uk)`!
    have hreidx : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) =
        ∑ a : PauliIdx 2, ∑ b : PauliIdx 2,
          (∑ uk : PauliIdx 2, if symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk then (1 : ℝ) else 0) *
            (gval ψ a * gval ψ b) := by
      have h1 : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
          if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) =
          ∑ uk : PauliIdx 2, ∑ a : PauliIdx 2, ∑ b : PauliIdx 2,
            if symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk then gval ψ a * gval ψ b else 0 := by
        rw [Finset.sum_comm]
        calc _ = ∑ r, ∑ uk, ∑ s, if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0 :=
              Finset.sum_congr rfl fun r _ => Finset.sum_comm
          _ = ∑ uk, ∑ r, ∑ s, if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0 :=
              Finset.sum_comm
          _ = ∑ uk, ∑ a, ∑ b, if symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk then gval ψ a * gval ψ b else 0 := by
              refine Finset.sum_congr rfl fun uk _ => ?_
              refine Fintype.sum_equiv (Equiv.addRight uk) _ _ fun r => ?_
              change (∑ s, if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) =
                ∑ b, if symp (r + uk + b) (r + uk + uk) = 1 ∧ inT (r + uk + b) (r + uk + uk) uk
                  then gval ψ (r + uk) * gval ψ b else 0
              refine Fintype.sum_equiv (Equiv.addLeft (r + uk)) _ _ fun s => ?_
              change (if symp s r = 1 ∧ inT s r uk then gval ψ (r + uk) * gval ψ (r + s + uk) else 0) =
                (if symp (r + uk + (r + uk + s)) (r + uk + uk) = 1 ∧
                    inT (r + uk + (r + uk + s)) (r + uk + uk) uk
                  then gval ψ (r + uk) * gval ψ (r + uk + s) else 0)
              have he1 : r + uk + (r + uk + s) = s := pauliIdx_add_cancel_left (r + uk) s
              have he2 : r + uk + uk = r := pauliIdx_add_cancel_right r uk
              have he3 : r + uk + s = r + s + uk := by abel
              rw [he1, he2, he3]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun uk _ => by split_ifs <;> ring
    have hcnt : ∀ a b : PauliIdx 2,
        (∑ uk : PauliIdx 2, if symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk then (1 : ℝ) else 0) =
        if symp a b = 1 then 3 else 0 := fun a b => by
      by_cases hab : symp a b = 1
      · rw [if_pos hab]
        have ha0 : a ≠ 0 := fun h => by rw [h, symp_zero_left] at hab; exact absurd hab (by decide)
        have hb0 : b ≠ 0 := fun h => by rw [h, symp_zero_right] at hab; exact absurd hab (by decide)
        have hab_ne : a ≠ b := fun h => by rw [h, symp_self] at hab; exact absurd hab (by decide)
        have h4 := card_symp_two_cond a b ha0 hb0 hab_ne 1 1
        have hpt : ∀ uk : PauliIdx 2,
            (symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk) ↔
            (symp a uk = 1 ∧ symp b uk = 1 ∧ uk ≠ a + b) := fun uk => by
          constructor
          · rintro ⟨_, ⟨_, hne, hsuk, hruk⟩⟩
            have hauk : symp a uk = 1 := by rw [symp_add_left, symp_self, add_zero] at hruk; exact hruk
            have hbuk : symp b uk = 1 := by
              rw [symp_add_left, hauk] at hsuk
              rcases zmod2_cases (symp b uk) with h0 | h1
              · rw [h0] at hsuk; exact absurd hsuk (by decide)
              · exact h1
            exact ⟨hauk, hbuk, hne⟩
          · rintro ⟨hauk, hbuk, hne⟩
            have hsuk : symp (a + b) uk = 0 := by rw [symp_add_left, hauk, hbuk]; decide
            have hsr : symp (a + b) (a + uk) = 1 := by
              rw [symp_add_right, hsuk, add_zero, symp_add_left, symp_self, zero_add, symp_comm, hab]
            have huk0 : uk ≠ 0 := fun h => by rw [h, symp_zero_right] at hauk; exact absurd hauk (by decide)
            have hruk : symp (a + uk) uk = 1 := by rw [symp_add_left, hauk, symp_self, add_zero]
            exact ⟨hsr, ⟨huk0, hne, hsuk, hruk⟩⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (a + b))] at h4
        have hab_in : symp a (a + b) = 1 ∧ symp b (a + b) = 1 :=
          ⟨by rw [symp_add_right, symp_self, zero_add]; exact hab,
           by rw [symp_add_right, symp_self, add_zero, symp_comm]; exact hab⟩
        rw [if_pos hab_in] at h4
        have heq : (∑ uk : PauliIdx 2, if symp (a + b) (a + uk) = 1 ∧ inT (a + b) (a + uk) uk then (1 : ℝ) else 0) =
            ∑ uk ∈ Finset.univ.erase (a + b), if symp a uk = 1 ∧ symp b uk = 1 then (1 : ℝ) else 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (a + b))]
          rw [if_neg (fun h => ((hpt (a + b)).mp h).2.2 rfl), zero_add]
          refine Finset.sum_congr rfl fun uk huk => ?_
          have hne : uk ≠ a + b := (Finset.mem_erase.mp huk).1
          by_cases h : symp a uk = 1 ∧ symp b uk = 1
          · rw [if_pos ((hpt uk).mpr ⟨h.1, h.2, hne⟩), if_pos h]
          · rw [if_neg (fun h' => h ⟨((hpt uk).mp h').1, ((hpt uk).mp h').2.1⟩), if_neg h]
        rw [heq]; linarith
      · rw [if_neg hab]
        refine Finset.sum_eq_zero fun uk _ => ?_
        rw [if_neg]
        rintro ⟨hsr, ⟨_, _, hsuk, _⟩⟩
        rw [symp_add_right, hsuk, add_zero, symp_add_left, symp_self, zero_add, symp_comm] at hsr
        exact hab hsr
    rw [hreidx]
    simp_rw [hcnt]
    have hsum_anti : (∑ a : PauliIdx 2, ∑ b : PauliIdx 2,
        (if symp a b = 1 then (3 : ℝ) else 0) * (gval ψ a * gval ψ b)) = 24 - 6 * F4 ψ := by
      have h3 : (∑ a : PauliIdx 2, ∑ b : PauliIdx 2,
          (if symp a b = 1 then (3 : ℝ) else 0) * (gval ψ a * gval ψ b)) =
          3 * ∑ b : PauliIdx 2, gval ψ b * (∑ a : PauliIdx 2, if symp a b = 1 then gval ψ a else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
      rw [h3]
      simp_rw [sum_gval_anti hunit]
      have htot := sum_gval hunit
      have h2 : ∑ b : PauliIdx 2, gval ψ b * (2 - 2 * gval ψ b) = 2 * (∑ b, gval ψ b) - 2 * F4 ψ := by
        simp only [F4, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => by ring
      rw [h2, htot]; ring
    exact hsum_anti
  -- Term 2a & 2b are equal via `r ↦ r + s` symmetry, and each equals `8 - 2 F₄`!
  have ht2_sym : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ (r + s + uk) * cval ψ r * cval ψ (s + uk)) else 0) =
      ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun r => ?_
    refine Finset.sum_congr rfl fun uk _ => ?_
    change (if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ (r + s + uk) * cval ψ r * cval ψ (s + uk)) else 0) =
      (if symp s (r + s) = 1 ∧ inT s (r + s) uk then
        gval ψ (r + s + s + uk) * ((phaseRe (r + s + uk) (r + s + s) : ℝ) * cval ψ (r + s + uk) * cval ψ (r + s + s) * cval ψ (s + uk)) else 0)
    have hrss : r + s + s = r := pauliIdx_add_cancel_right r s
    have hcond : (symp s r = 1 ∧ inT s r uk) ↔ (symp s (r + s) = 1 ∧ inT s (r + s) uk) := by
      simp only [inT, symp_add_right, symp_add_left, symp_self, add_zero]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, by rw [h4, add_zero]; exact h5⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩; rw [h4, add_zero] at h5; exact ⟨h1, h2, h3, h4, h5⟩
    rw [hrss]
    by_cases hc : symp s r = 1 ∧ inT s r uk
    · rw [if_pos hc, if_pos (hcond.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
  have ht2a : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
      8 - 2 * F4 ψ := by
    -- Bijection `(s, r, uk) ↦ (yk = r + uk, rr = r + s, zk = r + s + uk)`!
    -- Inverse: `s = yk + zk, r = rr + yk + zk, uk = rr + zk`!
    have hbij : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk then
          gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
        ∑ yk : PauliIdx 2, ∑ rr : PauliIdx 2, ∑ zk : PauliIdx 2,
          if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 ∧ symp yk zk = 1 ∧ symp rr zk = 1 then
            gval ψ zk * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0 := by
      -- Reindex step by step: `r ↦ yk = r + uk`, then `s ↦ rr = s + (yk + uk)`, then `uk ↦ zk = uk + rr`!
      rw [Finset.sum_comm]
      have h1 : (∑ r : PauliIdx 2, ∑ s : PauliIdx 2, ∑ uk : PauliIdx 2,
          if symp s r = 1 ∧ inT s r uk then
            gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
          ∑ uk : PauliIdx 2, ∑ r : PauliIdx 2, ∑ s : PauliIdx 2,
          if symp s r = 1 ∧ inT s r uk then
            gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0 := by
        calc _ = ∑ r, ∑ uk, ∑ s, _ := Finset.sum_congr rfl fun r _ => Finset.sum_comm
          _ = ∑ uk, ∑ r, ∑ s, _ := Finset.sum_comm
      rw [h1]
      have h2 : (∑ uk : PauliIdx 2, ∑ r : PauliIdx 2, ∑ s : PauliIdx 2,
          if symp s r = 1 ∧ inT s r uk then
            gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
          ∑ uk : PauliIdx 2, ∑ yk : PauliIdx 2, ∑ rr : PauliIdx 2,
          if symp (yk + uk + rr) (yk + uk) = 1 ∧ inT (yk + uk + rr) (yk + uk) uk then
            gval ψ (rr + uk) * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0 := by
        refine Finset.sum_congr rfl fun uk _ => ?_
        refine Fintype.sum_equiv (Equiv.addRight uk) _ _ fun r => ?_
        refine Fintype.sum_equiv (Equiv.addLeft r) _ _ fun s => ?_
        change (if symp s r = 1 ∧ inT s r uk then
            gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
          (if symp (r + uk + uk + (r + s)) (r + uk + uk) = 1 ∧ inT (r + uk + uk + (r + s)) (r + uk + uk) uk then
            gval ψ (r + s + uk) * ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + uk) * cval ψ (r + s) * cval ψ (r + uk + (r + s))) else 0)
        have he1 : r + uk + uk = r := pauliIdx_add_cancel_right r uk
        have he2 : r + (r + s) = s := pauliIdx_add_cancel_left r s
        have he3 : r + uk + (r + s) = s + uk := by
          calc r + uk + (r + s) = (r + r) + (s + uk) := by abel
            _ = s + uk := by rw [pauliIdx_add_self, zero_add]
        rw [he1, he2, he3]
      rw [h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun yk _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun rr _ => ?_
      refine Fintype.sum_equiv (Equiv.addRight rr) _ _ fun uk => ?_
      change (if symp (yk + uk + rr) (yk + uk) = 1 ∧ inT (yk + uk + rr) (yk + uk) uk then
          gval ψ (rr + uk) * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) =
        (if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 ∧ symp yk (uk + rr) = 1 ∧ symp rr (uk + rr) = 1 then
          gval ψ (uk + rr) * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0)
      rw [add_comm rr uk]
      have hcond : (symp (yk + uk + rr) (yk + uk) = 1 ∧ inT (yk + uk + rr) (yk + uk) uk) ↔
          (yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 ∧ symp yk (uk + rr) = 1 ∧ symp rr (uk + rr) = 1) := by
        constructor
        · rintro ⟨hsr, ⟨huk0, hne, hsuk, hruk⟩⟩
          have hykuk : symp yk uk = 1 := by rw [symp_add_left, symp_self, add_zero] at hruk; exact hruk
          have hrruk : symp rr uk = 1 := by
            rw [symp_add_left, symp_add_left, hykuk, symp_self, add_zero] at hsuk
            rcases zmod2_cases (symp rr uk) with h0 | h1
            · rw [h0] at hsuk; exact absurd hsuk (by decide)
            · exact h1
          have hykrr : symp yk rr = 0 := by
            rw [symp_add_left, symp_self, zero_add, symp_add_right, symp_comm rr yk, hrruk] at hsr
            rcases zmod2_cases (symp yk rr) with h0 | h1
            · exact h0
            · rw [h1] at hsr; exact absurd hsr (by decide)
          have h1 : symp yk (uk + rr) = 1 := by rw [symp_add_right, hykuk, hykrr, add_zero]
          have h2 : symp rr (uk + rr) = 1 := by rw [symp_add_right, hrruk, symp_self, add_zero]
          have hyk0 : yk ≠ 0 := fun h => by rw [h, symp_zero_left] at h1; exact absurd h1 (by decide)
          have hrr0 : rr ≠ 0 := fun h => by rw [h, symp_zero_left] at h2; exact absurd h2 (by decide)
          have hrryk : rr ≠ yk := fun h => by
            apply hne
            calc uk = uk + (yk + yk) := by rw [pauliIdx_add_self, add_zero]
              _ = yk + uk + rr := by rw [h]; abel
          exact ⟨hyk0, hrr0, hrryk, hykrr, h1, h2⟩
        · rintro ⟨hyk0, hrr0, hrryk, hykrr, h1, h2⟩
          have hykuk : symp yk uk = 1 := by rw [symp_add_right, hykrr, add_zero] at h1; exact h1
          have hrruk : symp rr uk = 1 := by rw [symp_add_right, symp_self, add_zero] at h2; exact h2
          have hsr : symp (yk + uk + rr) (yk + uk) = 1 := by
            rw [symp_add_left, symp_self, zero_add, symp_add_right, symp_comm rr yk, hykrr, zero_add, hrruk]
          have huk0 : uk ≠ 0 := fun h => by rw [h, symp_zero_right] at hykuk; exact absurd hykuk (by decide)
          have hne : uk ≠ yk + uk + rr := fun h => by
            have : yk + rr = 0 := by
              have := congr_arg (· + uk) h
              rw [pauliIdx_add_self] at this
              calc yk + rr = (yk + rr) + (uk + uk) := by rw [pauliIdx_add_self, add_zero]
                _ = yk + uk + rr + uk := by abel
                _ = 0 := this.symm
            exact hrryk ((pauli_add_eq_zero_iff yk rr).mp this).symm
          have hsuk : symp (yk + uk + rr) uk = 0 := by
            rw [symp_add_left, symp_add_left, hykuk, symp_self, add_zero, hrruk]; decide
          have hruk : symp (yk + uk) uk = 1 := by rw [symp_add_left, hykuk, symp_self, add_zero]
          exact ⟨hsr, ⟨huk0, hne, hsuk, hruk⟩⟩
      by_cases hc : yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 ∧ symp yk (uk + rr) = 1 ∧ symp rr (uk + rr) = 1
      · rw [if_pos (hcond.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]
    rw [hbij]
    -- Now sum `gval ψ zk` over `zk` using `sum_gval_anti_both`!
    have hzk : ∀ yk rr : PauliIdx 2,
        (∑ zk : PauliIdx 2, if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 ∧ symp yk zk = 1 ∧ symp rr zk = 1
          then gval ψ zk * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) =
        if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          (1 - gval ψ yk - gval ψ rr + gval ψ (yk + rr)) *
            ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0 := fun yk rr => by
      by_cases hc : yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0
      · rw [if_pos hc, ← sum_gval_anti_both hunit yk rr, Finset.sum_mul]
        refine Finset.sum_congr rfl fun zk _ => ?_
        by_cases hz : symp yk zk = 1 ∧ symp rr zk = 1
        · rw [if_pos ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hz.1, hz.2⟩, if_pos hz]
        · rw [if_neg (fun h => hz ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩), if_neg hz, zero_mul]
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun zk _ => ?_
        rw [if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
    simp_rw [hzk]
    have hlin : (∑ yk : PauliIdx 2, ∑ rr : PauliIdx 2,
        if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          (1 - gval ψ yk - gval ψ rr + gval ψ (yk + rr)) *
            ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) =
        (∑ yk, ∑ rr, if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          (phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr) else 0) -
        (∑ yk, ∑ rr, if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          gval ψ yk * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) -
        (∑ yk, ∑ rr, if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          gval ψ rr * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) +
        (∑ yk, ∑ rr, if yk ≠ 0 ∧ rr ≠ 0 ∧ rr ≠ yk ∧ symp yk rr = 0 then
          gval ψ (yk + rr) * ((phaseRe yk rr : ℝ) * cval ψ yk * cval ψ rr * cval ψ (yk + rr)) else 0) := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun yk _ => Finset.sum_congr rfl fun rr _ => by split_ifs <;> ring
    rw [hlin, sum_line_triple hunit, sum_gs_line_triple hunit, sum_gp_line_triple hunit, sum_gsp_line_triple hunit]
    ring
  -- Term 3: exact 1-to-1 bijection `(s, r, uk) ↦ (u = s + uk, p = r, q = r + s)` onto `P2_core_eq`!
  have ht3 : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        gval ψ (s + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (r + s + uk)) *
          ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (r + uk)) else 0) =
      4 * F4 ψ - 2 * Tord ψ - 4 := by
    rw [← P2_core_eq hunit]
    -- Reindex: `s ↦ q = r + s`, then `uk ↦ u = (r + q) + uk`!
    rw [Finset.sum_comm]
    have h1 : (∑ r : PauliIdx 2, ∑ s : PauliIdx 2, ∑ uk : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk then
          gval ψ (s + uk) * ((phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (r + s + uk)) *
            ((phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (r + uk)) else 0) =
        ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, ∑ u : PauliIdx 2,
          if coreCond u p q then
            gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
              ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft p) _ _ fun s => ?_
      refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun uk => ?_
      change (if symp s p = 1 ∧ inT s p uk then
          gval ψ (s + uk) * ((phaseRe (p + s + uk) p : ℝ) * cval ψ p * cval ψ (p + s + uk)) *
            ((phaseRe (p + uk) (p + s) : ℝ) * cval ψ (p + s) * cval ψ (p + uk)) else 0) =
        (if coreCond (s + uk) p (p + s) then
          gval ψ (s + uk) * ((phaseRe (s + uk) p : ℝ) * cval ψ p * cval ψ (s + uk + p)) *
            ((phaseRe (s + uk) (p + s) : ℝ) * cval ψ (p + s) * cval ψ (s + uk + (p + s))) else 0)
      have hcond : (symp s p = 1 ∧ inT s p uk) ↔ coreCond (s + uk) p (p + s) := by
        constructor
        · rintro ⟨hsp, ⟨huk0, huks, hsuk, hpuk⟩⟩
          have hu0 : s + uk ≠ 0 := fun h => huks ((pauli_add_eq_zero_iff s uk).mp h).symm
          have hup : symp (s + uk) p = 0 := by rw [symp_add_left, hsp, symp_comm uk p, hpuk]; decide
          have huq : symp (s + uk) (p + s) = 0 := by
            rw [symp_add_right, hup, zero_add, symp_add_left, symp_self, zero_add, symp_comm uk s, hsuk]
          have hpq : symp p (p + s) = 1 := by rw [symp_add_right, symp_self, zero_add, symp_comm]; exact hsp
          have hp0 : p ≠ 0 := fun h => by rw [h, symp_zero_left] at hpq; exact absurd hpq (by decide)
          have hq0 : p + s ≠ 0 := fun h => by rw [h, symp_zero_right] at hpq; exact absurd hpq (by decide)
          have hpu : p ≠ s + uk := fun h => by
            have h1 : symp (s + uk) (p + s) = 1 := by rw [← h]; exact hpq
            rw [huq] at h1; exact absurd h1 (by decide)
          have hqu : p + s ≠ s + uk := fun h => by
            have h1 : symp p (s + uk) = 1 := by rw [← h]; exact hpq
            rw [symp_comm, hup] at h1; exact absurd h1 (by decide)
          exact ⟨hu0, hp0, hq0, hpu, hqu, hup, huq, hpq⟩
        · rintro ⟨hu0, _, _, _, _, hup, huq, hpq⟩
          have hsp : symp s p = 1 := by
            rw [symp_add_right, symp_self, zero_add, symp_comm] at hpq; exact hpq
          have hpuk : symp p uk = 1 := by
            rw [symp_add_left, hsp] at hup
            rcases zmod2_cases (symp uk p) with h0 | h1
            · rw [h0] at hup; exact absurd hup (by decide)
            · rw [symp_comm]; exact h1
          have hsuk : symp s uk = 0 := by
            rw [symp_add_right, hup, zero_add, symp_add_left, symp_self, zero_add, symp_comm] at huq
            exact huq
          have huk0 : uk ≠ 0 := fun h => by rw [h, symp_zero_right] at hpuk; exact absurd hpuk (by decide)
          have huks : uk ≠ s := fun h => hu0 (by rw [h, pauliIdx_add_self])
          exact ⟨hsp, ⟨huk0, huks, hsuk, hpuk⟩⟩
      by_cases hc : symp s p = 1 ∧ inT s p uk
      · have hcc := hcond.mp hc
        have hidx1 : p + s + uk = s + uk + p := by abel
        have hidx2 : p + uk = s + uk + (p + s) := by
          calc p + uk = p + uk + (s + s) := by rw [pauliIdx_add_self, add_zero]
            _ = s + uk + (p + s) := by abel
        have hph1 : phaseRe (p + s + uk) p = phaseRe (s + uk) p := by
          rw [hidx1]; exact phaseRe_add_left_eq (s + uk) p hcc.2.2.2.2.2.1
        have hph2 : phaseRe (p + uk) (p + s) = phaseRe (s + uk) (p + s) := by
          rw [hidx2]; exact phaseRe_add_left_eq (s + uk) (p + s) hcc.2.2.2.2.2.2.1
        rw [if_pos hc, if_pos hcc, hph1, hph2, hidx1, hidx2]
      · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
    rw [h1]
    calc (∑ p : PauliIdx 2, ∑ q : PauliIdx 2, ∑ u : PauliIdx 2,
          if coreCond u p q then
            gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
              ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0)
        = ∑ p : PauliIdx 2, ∑ u : PauliIdx 2, ∑ q : PauliIdx 2,
          if coreCond u p q then
            gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
              ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0 :=
            Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
          if coreCond u p q then
            gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
              ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q)) else 0 := Finset.sum_comm
  rw [hsplit, ht1, ht2_sym, ht2a, ht3]; ring

/-- Shared `Y` helper for `S_A`: `Yval ψ r v = Im(pauliPhase r v) * c_{r + v}`. -/
private abbrev Yval (ψ : QState 2) (r v : PauliIdx 2) : ℝ :=
  (phaseIm r v : ℝ) * cval ψ (r + v)

private lemma T_third_prop (s r u v : PauliIdx 2)
    (hsr : symp s r = 1) (hu : inT s r u) (hv : inT s r v) (hvu : v ≠ u) :
    inT s r (s + u + v) ∧ (s + u + v) ≠ u ∧ (s + u + v) ≠ v ∧ symp u v = 1 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, symp_zero_left] at hsr; exact absurd hsr (by decide)
  have huv : symp u v = 1 := by
    rcases zmod2_cases (symp u v) with h0 | h1
    · exfalso
      rcases mem_perp_inter_four s u v hs0 hu.1 hu.2.1 hu.2.2.1 hv.2.2.1 h0 with rfl | rfl | rfl | rfl
      · exact hv.1 rfl
      · exact hv.2.1 rfl
      · exact hvu rfl
      · have hrv := hv.2.2.2
        rw [symp_add_right, symp_comm r s, hsr, hu.2.2.2] at hrv; exact absurd hrv (by decide)
    · exact h1
  have hsw : symp s (s + u + v) = 0 := by simp only [symp_add_right, symp_self, hu.2.2.1, hv.2.2.1]; decide
  have hrw : symp r (s + u + v) = 1 := by
    simp only [symp_add_right, symp_comm r s, hsr, hu.2.2.2, hv.2.2.2]; decide
  have hw0 : s + u + v ≠ 0 := fun h => by rw [h, symp_zero_right] at hrw; exact absurd hrw (by decide)
  have hws : s + u + v ≠ s := fun h => by
    have : u + v = 0 := by
      have := congr_arg (s + ·) h; rw [pauliIdx_add_self] at this
      calc u + v = (s + s) + (u + v) := by rw [pauliIdx_add_self, zero_add]
        _ = s + (s + u + v) := by abel
        _ = 0 := by rw [this]
    exact hvu ((pauli_add_eq_zero_iff u v).mp this).symm
  have hwu : s + u + v ≠ u := fun h => by
    have : s + v = 0 := by
      have := congr_arg (· + u) h; rw [pauliIdx_add_self] at this
      calc s + v = (s + v) + (u + u) := by rw [pauliIdx_add_self, add_zero]
        _ = s + u + v + u := by abel
        _ = 0 := this
    exact hv.2.1 ((pauli_add_eq_zero_iff s v).mp this).symm
  have hwv : s + u + v ≠ v := fun h => by
    have : s + u = 0 := by
      have := congr_arg (· + v) h; rw [pauliIdx_add_self] at this
      calc s + u = (s + u) + (v + v) := by rw [pauliIdx_add_self, add_zero]
        _ = s + u + v + v := by abel
        _ = 0 := this
    exact hu.2.1 ((pauli_add_eq_zero_iff s u).mp this).symm
  exact ⟨⟨hw0, hws, hsw, hrw⟩, hwu, hwv, huv⟩

private lemma hrs_iff_T (s r u v : PauliIdx 2) :
    (symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u) ↔
    (symp s (r + s) = 1 ∧ inT s (r + s) u ∧ inT s (r + s) v ∧ v ≠ u) := by
  simp only [inT, symp_add_right, symp_add_left, symp_self, add_zero]
  constructor
  · rintro ⟨h1, ⟨h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
    exact ⟨h1, ⟨h2, h3, h4, by rw [h4, add_zero]; exact h5⟩, ⟨h6, h7, h8, by rw [h8, add_zero]; exact h9⟩, h10⟩
  · rintro ⟨h1, ⟨h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
    rw [h4, add_zero] at h5; rw [h8, add_zero] at h9
    exact ⟨h1, ⟨h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩

/-- Shared 4-variable reindexing lemma onto `coreCond u p q` with fiber count `2`! -/
private lemma sum_T_pair_reidx (f : PauliIdx 2 → PauliIdx 2 → PauliIdx 2 → ℝ) :
    (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then f u (r + v) (r + (s + u + v)) else 0) =
    2 * ∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2, if coreCond u p q then f u p q else 0 := by
  have hswap : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then f u (r + v) (r + (s + u + v)) else 0) =
      ∑ u : PauliIdx 2, ∑ v : PauliIdx 2, ∑ r : PauliIdx 2, ∑ s : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then f u (r + v) (r + (s + u + v)) else 0 := by
    calc _ = ∑ s, ∑ u, ∑ r, ∑ v, _ := Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ u, ∑ s, ∑ r, ∑ v, _ := Finset.sum_comm
      _ = ∑ u, ∑ s, ∑ v, ∑ r, _ := Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ u, ∑ v, ∑ s, ∑ r, _ := Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ u, ∑ v, ∑ r, ∑ s, _ := Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_comm
  rw [hswap]
  have hpush : (∑ u : PauliIdx 2, ∑ v : PauliIdx 2, ∑ r : PauliIdx 2, ∑ s : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then f u (r + v) (r + (s + u + v)) else 0) =
      ∑ u : PauliIdx 2, ∑ v : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
         inT (u + p + q) (p + v) v ∧ v ≠ u then f u p q else 0 := by
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun r => ?_
    refine Fintype.sum_equiv (Equiv.addLeft (u + (r + v))) _ _ fun s => ?_
    change (if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then f u (r + v) (r + (s + u + v)) else 0) =
      (if symp (u + (r + v) + (u + (r + v) + s)) (r + v + v) = 1 ∧
          inT (u + (r + v) + (u + (r + v) + s)) (r + v + v) u ∧
          inT (u + (r + v) + (u + (r + v) + s)) (r + v + v) v ∧ v ≠ u then
        f u (r + v) (u + (r + v) + s) else 0)
    have he1 : u + (r + v) + (u + (r + v) + s) = s := pauliIdx_add_cancel_left (u + (r + v)) s
    have he2 : r + v + v = r := pauliIdx_add_cancel_right r v
    have he3 : r + (s + u + v) = u + (r + v) + s := by abel
    rw [he1, he2, he3]
  rw [hpush]
  have hswap2 : (∑ u : PauliIdx 2, ∑ v : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
      if symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
         inT (u + p + q) (p + v) v ∧ v ≠ u then f u p q else 0) =
      ∑ u : PauliIdx 2, ∑ p : PauliIdx 2, ∑ q : PauliIdx 2,
        (∑ v : PauliIdx 2, if symp (u + p + q) (p + v) = 1 ∧ inT (u + p + q) (p + v) u ∧
            inT (u + p + q) (p + v) v ∧ v ≠ u then (1 : ℝ) else 0) * f u p q := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
  rw [hswap2]
  simp_rw [fiber_T_pair_count]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by split_ifs <;> ring

/-- Piece 1 of `S_A`: `4 * (F₄ - T_ord + 2)`. -/
private lemma sos_A_P1 (hunit : IsUnitState ψ) :
    (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2 +
          Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0) =
    4 * (F4 ψ - Tord ψ + 2) := by
  have hY_sq : ∀ s r u v : PauliIdx 2, symp s r = 1 → inT s r u → inT s r v → v ≠ u →
      Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2 = gval ψ (r + v) * gval ψ (r + (s + u + v)) := by
    intro s r u v hsr hu hv hvu
    have ht := T_third_prop s r u v hsr hu hv hvu
    have h1 := phaseIm_sq_one hv.2.2.2
    have h2 := phaseIm_sq_one ht.1.2.2.2
    simp only [Yval, gval]
    calc ((phaseIm r v : ℝ) * cval ψ (r + v)) ^ 2 *
          ((phaseIm r (s + u + v) : ℝ) * cval ψ (r + (s + u + v))) ^ 2
        = (phaseIm r v : ℝ) ^ 2 * (phaseIm r (s + u + v) : ℝ) ^ 2 *
          (cval ψ (r + v) ^ 2 * cval ψ (r + (s + u + v)) ^ 2) := by ring
      _ = cval ψ (r + v) ^ 2 * cval ψ (r + (s + u + v)) ^ 2 := by rw [h1, h2]; ring
  have h2eq : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * (Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0) =
      ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * (Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun r => ?_
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    change (if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0) =
      (if symp s (r + s) = 1 ∧ inT s (r + s) u ∧ inT s (r + s) v ∧ v ≠ u then
        gval ψ u * (Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0)
    by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u
    · rw [if_pos hc, if_pos ((hrs_iff_T s r u v).mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((hrs_iff_T s r u v).mpr h))]
  have ha : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * (Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2 +
            Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0) =
      (∑ s, ∑ r, ∑ u, ∑ v, if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2) else 0) +
      (∑ s, ∑ r, ∑ u, ∑ v, if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (Yval ψ (r + s) v ^ 2 * Yval ψ (r + s) (s + u + v) ^ 2) else 0) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u
        · rw [if_pos hc, if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc, if_neg hc, add_zero]
  have h1 : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * (Yval ψ r v ^ 2 * Yval ψ r (s + u + v) ^ 2) else 0) =
      ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * gval ψ (r + v) * gval ψ (r + (s + u + v)) else 0 := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u
    · rw [if_pos hc, if_pos hc, hY_sq s r u v hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]; ring
    · rw [if_neg hc, if_neg hc]
  rw [ha, h2eq, h1, sum_T_pair_reidx (fun u p q => gval ψ u * gval ψ p * gval ψ q), P1_base_eq hunit]; ring

/-- Piece 2 of `S_A`: `2 * (8 F₄ - 4 T_ord - 8)`. -/
private lemma sos_A_P2 (hunit : IsUnitState ψ) :
    (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (-2 * (Yval ψ r v * Yval ψ r (s + u + v) * Yval ψ (r + s) v * Yval ψ (r + s) (s + u + v))) else 0) =
    2 * (8 * F4 ψ - 4 * Tord ψ - 8) := by
  have hrew : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
        gval ψ u * (-2 * (Yval ψ r v * Yval ψ r (s + u + v) * Yval ψ (r + s) v * Yval ψ (r + s) (s + u + v))) else 0) =
      2 * ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
          gval ψ u * ((phaseRe u (r + v) : ℝ) * cval ψ (r + v) * cval ψ (u + (r + v))) *
            ((phaseRe u (r + (s + u + v)) : ℝ) * cval ψ (r + (s + u + v)) * cval ψ (u + (r + (s + u + v)))) else 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u
    · have ht := T_third_prop s r u v hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      have hsgn := sign_P2_eq s r u v hc.1 hc.2.1.2.2.1 hc.2.2.1.2.2.1 hc.2.1.2.2.2 hc.2.2.1.2.2.2 ht.2.2.2
      have hsgnR : -((phaseIm r v : ℝ) * (phaseIm r (s + u + v) : ℝ) *
          (phaseIm (r + s) v : ℝ) * (phaseIm (r + s) (s + u + v) : ℝ)) =
          (phaseRe u (r + v) : ℝ) * (phaseRe u (r + (s + u + v)) : ℝ) := by exact_mod_cast hsgn
      have hi1 : r + s + (s + u + v) = u + (r + v) := by
        calc r + s + (s + u + v) = (s + s) + (u + (r + v)) := by abel
          _ = u + (r + v) := by rw [pauliIdx_add_self, zero_add]
      have hi2 : r + s + v = u + (r + (s + u + v)) := by
        calc r + s + v = (u + u) + (r + s + v) := by rw [pauliIdx_add_self, zero_add]
          _ = u + (r + (s + u + v)) := by abel
      rw [if_pos hc, if_pos hc]; simp only [Yval, hi1, hi2]
      calc gval ψ u * (-2 * ((phaseIm r v : ℝ) * cval ψ (r + v) *
            ((phaseIm r (s + u + v) : ℝ) * cval ψ (r + (s + u + v))) *
            ((phaseIm (r + s) v : ℝ) * cval ψ (u + (r + (s + u + v)))) *
            ((phaseIm (r + s) (s + u + v) : ℝ) * cval ψ (u + (r + v)))))
          = 2 * (gval ψ u * (-((phaseIm r v : ℝ) * (phaseIm r (s + u + v) : ℝ) *
              (phaseIm (r + s) v : ℝ) * (phaseIm (r + s) (s + u + v) : ℝ))) *
              cval ψ (r + v) * cval ψ (u + (r + v)) * cval ψ (r + (s + u + v)) *
              cval ψ (u + (r + (s + u + v)))) := by ring
        _ = 2 * (gval ψ u * ((phaseRe u (r + v) : ℝ) * (phaseRe u (r + (s + u + v)) : ℝ)) *
              cval ψ (r + v) * cval ψ (u + (r + v)) * cval ψ (r + (s + u + v)) *
              cval ψ (u + (r + (s + u + v)))) := by rw [hsgnR]
        _ = _ := by ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  rw [hrew, sum_T_pair_reidx (fun u p q => gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
      ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q))), P2_core_eq hunit]; ring

/-- Piece 3 of `S_A`: `6 F₄ - 2 T_ord - 12`. -/
private lemma sos_A_P3 (hunit : IsUnitState ψ) :
    (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ *
          (Yval ψ r u * Yval ψ r u₂ * Yval ψ r (s + u + u₂) ^ 2 +
           Yval ψ (r + s) u * Yval ψ (r + s) u₂ * Yval ψ (r + s) (s + u + u₂) ^ 2) else 0) =
    6 * F4 ψ - 2 * Tord ψ - 12 := by
  let Y := Yval ψ
  have hT_third := T_third_prop
  have hrs_iff := hrs_iff_T
  have hhalf_sym : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) =
      ∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun r => ?_
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u₂ _ => ?_
    change (if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) =
      (if symp s (r + s) = 1 ∧ inT s (r + s) u ∧ inT s (r + s) u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0)
    by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u
    · rw [if_pos hc, if_pos ((hrs_iff s r u u₂).mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((hrs_iff s r u u₂).mpr h))]
  have hsplit : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ *
          (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2 + Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) =
      -2 * ∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
          cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0 := by
    have ha : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ *
            (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2 + Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) =
        (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2) else 0) +
        (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u₂ _ => by split_ifs <;> ring
    rw [ha, hhalf_sym, ← two_mul]
    have hneg : 2 * (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2) else 0) =
        -2 * (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
            cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun u₂ _ => ?_
      by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u
      · have ht := hT_third s r u u₂ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
        have hsq := phaseIm_sq_one ht.1.2.2.2
        have hsgn := sign_P3_eq r u u₂ hc.2.1.2.2.2 hc.2.2.1.2.2.2
        have hsgnR : (trace4Int u (r + u) u₂ : ℝ) = -((phaseIm r u : ℝ) * (phaseIm r u₂ : ℝ)) := by
          exact_mod_cast hsgn
        rw [if_pos hc, if_pos hc, hsgnR]; simp only [Y, gval]
        calc 2 * (cval ψ u * cval ψ u₂ *
              ((phaseIm r u : ℝ) * cval ψ (r + u) * ((phaseIm r u₂ : ℝ) * cval ψ (r + u₂)) *
                ((phaseIm r (s + u + u₂) : ℝ) * cval ψ (r + (s + u + u₂))) ^ 2))
            = 2 * ((phaseIm r (s + u + u₂) : ℝ) ^ 2 *
                (cval ψ u * cval ψ u₂ * (phaseIm r u : ℝ) * (phaseIm r u₂ : ℝ) *
                  cval ψ (r + u) * cval ψ (r + u₂) * cval ψ (r + (s + u + u₂)) ^ 2)) := by ring
          _ = 2 * (1 * (cval ψ u * cval ψ u₂ * (phaseIm r u : ℝ) * (phaseIm r u₂ : ℝ) *
                  cval ψ (r + u) * cval ψ (r + u₂) * cval ψ (r + (s + u + u₂)) ^ 2)) := by rw [hsq]
          _ = _ := by ring
      · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
    exact hneg
  -- Now show `2 * ∑_{s,r,u,u₂} tr4 = P3_base` by splitting `P3_base` on `symp a q ∈ {0, 1}`!
  have hP3_half : 2 * (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
          cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0) =
      -6 * F4 ψ + 2 * Tord ψ + 12 := by
    -- First map `(s, r, u, u₂)` 1-to-1 onto `(y = r + s + u + u₂, w = u + u₂, a = u, q = r + u)` with `symp a q = 1`!
    have hbij : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
            cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0) =
        ∑ y : PauliIdx 2, ∑ w : PauliIdx 2, ∑ a : PauliIdx 2, ∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 1 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0 := by
      -- Move `u` outermost, reindex `r ↦ q = r + u`, `u₂ ↦ w = u + u₂`, `s ↦ y = s + (r + u + u₂)`!
      have hord : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
              cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0) =
          ∑ u, ∑ r, ∑ u₂, ∑ s, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            (trace4Int u (r + u) u₂ : ℝ) * gval ψ (r + (s + u + u₂)) *
              cval ψ u * cval ψ u₂ * cval ψ (r + u) * cval ψ (r + u₂) else 0 := by
        calc _ = ∑ s, ∑ u, ∑ r, ∑ u₂, _ := Finset.sum_congr rfl fun s _ => Finset.sum_comm
          _ = ∑ u, ∑ s, ∑ r, ∑ u₂, _ := Finset.sum_comm
          _ = ∑ u, ∑ r, ∑ s, ∑ u₂, _ := Finset.sum_congr rfl fun u _ => Finset.sum_comm
          _ = ∑ u, ∑ r, ∑ u₂, ∑ s, _ := Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm
      rw [hord]
      have hstep : (∑ a : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u₂ : PauliIdx 2, ∑ s : PauliIdx 2,
          if symp s r = 1 ∧ inT s r a ∧ inT s r u₂ ∧ u₂ ≠ a then
            (trace4Int a (r + a) u₂ : ℝ) * gval ψ (r + (s + a + u₂)) *
              cval ψ a * cval ψ u₂ * cval ψ (r + a) * cval ψ (r + u₂) else 0) =
          ∑ a : PauliIdx 2, ∑ q : PauliIdx 2, ∑ w : PauliIdx 2, ∑ y : PauliIdx 2,
          if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
             symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 1 then
            (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun r => ?_
        refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun u₂ => ?_
        refine Fintype.sum_equiv (Equiv.addLeft (r + a + u₂)) _ _ fun s => ?_
        change (if symp s r = 1 ∧ inT s r a ∧ inT s r u₂ ∧ u₂ ≠ a then
            (trace4Int a (r + a) u₂ : ℝ) * gval ψ (r + (s + a + u₂)) *
              cval ψ a * cval ψ u₂ * cval ψ (r + a) * cval ψ (r + u₂) else 0) =
          (if r + a + u₂ + s ≠ 0 ∧ a + u₂ ≠ 0 ∧ a + u₂ ≠ r + a + u₂ + s ∧
              symp (r + a + u₂ + s) (a + u₂) = 0 ∧ symp (r + a + u₂ + s) a = 0 ∧
              symp (a + u₂) a = 1 ∧ symp (r + a + u₂ + s) (r + a) = 1 ∧
              symp (a + u₂) (r + a) = 1 ∧ symp a (r + a) = 1 then
            (trace4Int a (r + a) (a + (a + u₂)) : ℝ) * gval ψ (r + a + u₂ + s) *
              cval ψ a * cval ψ (a + (a + u₂)) * cval ψ (r + a) * cval ψ (r + a + (a + u₂)) else 0)
        have he1 : a + (a + u₂) = u₂ := pauliIdx_add_cancel_left a u₂
        have he2 : r + a + (a + u₂) = r + u₂ := by
          calc r + a + (a + u₂) = r + (a + a) + u₂ := by abel
            _ = r + u₂ := by rw [pauliIdx_add_self, add_zero]
        have he3 : r + (s + a + u₂) = r + a + u₂ + s := by abel
        rw [he1, he2, he3]
        have hcond : (symp s r = 1 ∧ inT s r a ∧ inT s r u₂ ∧ u₂ ≠ a) ↔
            (r + a + u₂ + s ≠ 0 ∧ a + u₂ ≠ 0 ∧ a + u₂ ≠ r + a + u₂ + s ∧
              symp (r + a + u₂ + s) (a + u₂) = 0 ∧ symp (r + a + u₂ + s) a = 0 ∧
              symp (a + u₂) a = 1 ∧ symp (r + a + u₂ + s) (r + a) = 1 ∧
              symp (a + u₂) (r + a) = 1 ∧ symp a (r + a) = 1) := by
          constructor
          · rintro ⟨hsr, ha, hu2, hne⟩
            have ht := hT_third s r a u₂ hsr ha hu2 hne
            have hau2 : symp a u₂ = 1 := ht.2.2.2
            have hya : symp (r + a + u₂ + s) a = 0 := by
              simp only [symp_add_left, ha.2.2.2, symp_self, symp_comm u₂ a, hau2, ha.2.2.1]; decide
            have hyu2 : symp (r + a + u₂ + s) u₂ = 0 := by
              simp only [symp_add_left, hu2.2.2.2, hau2, symp_self, hu2.2.2.1]; decide
            have hyw : symp (r + a + u₂ + s) (a + u₂) = 0 := by rw [symp_add_right, hya, hyu2, add_zero]
            have hwa : symp (a + u₂) a = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm, hau2]
            have hyq : symp (r + a + u₂ + s) (r + a) = 1 := by
              rw [symp_add_right, hya, add_zero]
              simp only [symp_add_left, symp_self, symp_comm a r, ha.2.2.2, symp_comm u₂ r, hu2.2.2.2, hsr]; decide
            have hwq : symp (a + u₂) (r + a) = 1 := by
              simp only [symp_add_left, symp_add_right, symp_comm a r, ha.2.2.2, symp_self,
                symp_comm u₂ r, hu2.2.2.2, symp_comm u₂ a, hau2]; decide
            have haq : symp a (r + a) = 1 := by rw [symp_add_right, symp_comm, ha.2.2.2, symp_self, add_zero]
            have hy0 : r + a + u₂ + s ≠ 0 := fun h => by rw [h, symp_zero_left] at hyq; exact absurd hyq (by decide)
            have hw0 : a + u₂ ≠ 0 := fun h => hne ((pauli_add_eq_zero_iff a u₂).mp h).symm
            have hwy : a + u₂ ≠ r + a + u₂ + s := fun h => by
              have h1 : symp (r + a + u₂ + s) a = 1 := by rw [← h]; exact hwa
              rw [hya] at h1; exact absurd h1 (by decide)
            exact ⟨hy0, hw0, hwy, hyw, hya, hwa, hyq, hwq, haq⟩
          · rintro ⟨hy0, hw0, hwy, hyw, hya, hwa, hyq, hwq, haq⟩
            have hau2 : symp a u₂ = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm] at hwa; exact hwa
            have hra : symp r a = 1 := by rw [symp_add_right, symp_self, add_zero, symp_comm] at haq; exact haq
            have hru2 : symp r u₂ = 1 := by
              simp only [symp_add_left, symp_add_right, symp_comm a r, hra, symp_self, symp_comm u₂ a, hau2] at hwq
              rcases zmod2_cases (symp u₂ r) with h0 | h1
              · rw [h0] at hwq; exact absurd hwq (by decide)
              · rw [symp_comm]; exact h1
            have hsa : symp s a = 0 := by
              simp only [symp_add_left, hra, symp_self, symp_comm u₂ a, hau2] at hya
              rcases zmod2_cases (symp s a) with h0 | h1
              · exact h0
              · rw [h1] at hya; exact absurd hya (by decide)
            have hsu2 : symp s u₂ = 0 := by
              rw [symp_add_right, hya, zero_add] at hyw
              simp only [symp_add_left, hru2, hau2, symp_self] at hyw
              rcases zmod2_cases (symp s u₂) with h0 | h1
              · exact h0
              · rw [h1] at hyw; exact absurd hyw (by decide)
            have hsr : symp s r = 1 := by
              rw [symp_add_right, hya, add_zero] at hyq
              simp only [symp_add_left, symp_self, symp_comm a r, hra, symp_comm u₂ r, hru2] at hyq
              rcases zmod2_cases (symp s r) with h0 | h1
              · rw [h0] at hyq; exact absurd hyq (by decide)
              · exact h1
            have ha0 : a ≠ 0 := fun h => by rw [h, symp_zero_left] at hau2; exact absurd hau2 (by decide)
            have hu20 : u₂ ≠ 0 := fun h => by rw [h, symp_zero_right] at hau2; exact absurd hau2 (by decide)
            have has : a ≠ s := fun h => by rw [h, hsu2] at hau2; exact absurd hau2 (by decide)
            have hu2s : u₂ ≠ s := fun h => by rw [h, symp_comm, hsa] at hau2; exact absurd hau2 (by decide)
            have hne : u₂ ≠ a := fun h => by rw [h, symp_self] at hau2; exact absurd hau2 (by decide)
            exact ⟨hsr, ⟨ha0, has, hsa, hra⟩, ⟨hu20, hu2s, hsu2, hru2⟩, hne⟩
        by_cases hc : symp s r = 1 ∧ inT s r a ∧ inT s r u₂ ∧ u₂ ≠ a
        · rw [if_pos hc, if_pos (hcond.mp hc)]
        · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
      rw [hstep]
      -- Reorder `(a, q, w, y)` to `(y, w, a, q)`!
      calc (∑ a, ∑ q, ∑ w, ∑ y, _) = ∑ a, ∑ q, ∑ y, ∑ w, _ :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm
        _ = ∑ a, ∑ y, ∑ q, ∑ w, _ := Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ y, ∑ a, ∑ q, ∑ w, _ := Finset.sum_comm
        _ = ∑ y, ∑ a, ∑ w, ∑ q, _ := Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ y, ∑ w, ∑ a, ∑ q, _ := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    rw [hbij, ← P3_base_eq hunit]
    -- In `P3_base`, `q ↦ q + w` swaps `symp a q = 1` and `symp a q = 0` while preserving `trace4Int a q (a + w)`!
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    have hq_sym : (∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 0 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) =
        ∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 1 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0 := by
      refine Fintype.sum_equiv (Equiv.addRight w) _ _ fun q => ?_
      change (if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
                 symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 0 then _ else 0) =
        (if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
            symp y (q + w) = 1 ∧ symp w (q + w) = 1 ∧ symp a (q + w) = 1 then
          (trace4Int a (q + w) (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ (q + w) * cval ψ (q + w + w) else 0)
      rw [pauliIdx_add_cancel_right, trace4Int_shift_w]
      have hcond : (y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
                    symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 0) ↔
          (y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y (q + w) = 1 ∧ symp w (q + w) = 1 ∧ symp a (q + w) = 1) := by
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
          exact ⟨h1, h2, h3, h4, h5, h6,
            by rw [symp_add_right, h7, h4, add_zero],
            by rw [symp_add_right, h8, symp_self, add_zero],
            by rw [symp_add_right, h9, zero_add, symp_comm, h6]⟩
        · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
          rw [symp_add_right, h4, add_zero] at h7
          rw [symp_add_right, symp_self, add_zero] at h8
          rw [symp_add_right, symp_comm a w, h6] at h9
          have haq : symp a q = 0 := by
            rcases zmod2_cases (symp a q) with h0 | h1'
            · exact h0
            · rw [h1'] at h9; exact absurd h9 (by decide)
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, haq⟩
      by_cases hc : y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
          symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 0
      · rw [if_pos hc, if_pos (hcond.mp hc)]; ring
      · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
    have hq_split : (∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) =
        (∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 0 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) +
        (∑ q : PauliIdx 2,
        if y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
           symp y q = 1 ∧ symp w q = 1 ∧ symp a q = 1 then
          (trace4Int a q (a + w) : ℝ) * gval ψ y * cval ψ a * cval ψ (a + w) * cval ψ q * cval ψ (q + w) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hc : y ≠ 0 ∧ w ≠ 0 ∧ w ≠ y ∧ symp y w = 0 ∧ symp y a = 0 ∧ symp w a = 1 ∧
          symp y q = 1 ∧ symp w q = 1
      · rcases zmod2_cases (symp a q) with h0 | h1
        · rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2, h0⟩,
              if_neg (fun h => by rw [h0] at h; exact absurd h.2.2.2.2.2.2.2.2 (by decide)), add_zero]
        · rw [if_pos hc, if_neg (fun h => by rw [h1] at h; exact absurd h.2.2.2.2.2.2.2.2 (by decide)),
              if_pos ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2, h1⟩, zero_add]
      · rw [if_neg hc,
            if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩),
            if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩), add_zero]
    rw [hq_split, hq_sym]; ring
  linarith

/-- Piece 4 of `S_A`: `-24 + 12 F₄ - 4 T_ord`. -/
private lemma sos_A_P4 (hunit : IsUnitState ψ) :
    (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ *
          (- Yval ψ r u₂ * Yval ψ r (s + u + u₂) * Yval ψ (r + s) u * Yval ψ (r + s) (s + u + u₂)
           - Yval ψ (r + s) u₂ * Yval ψ (r + s) (s + u + u₂) * Yval ψ r u * Yval ψ r (s + u + u₂)) else 0) =
    -24 + 12 * F4 ψ - 4 * Tord ψ := by
  let Y := Yval ψ
  have hT_third := T_third_prop
  -- By `u ↔ u₂` symmetry, both terms are equal!
  have hsym_u : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) =
      ∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)) else 0 := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u₂ _ => ?_
    have hcomm : s + u₂ + u = s + u + u₂ := by abel
    by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u
    · rw [if_pos ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2.symm⟩, if_pos hc, hcomm]; ring
    · rw [if_neg (fun h => hc ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩), if_neg hc]
  have hsplit : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ *
          (- Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)
           - Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) =
      -2 * ∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)) else 0 := by
    have ha : (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ *
            (- Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)
             - Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) =
        -(∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)) else 0) -
        (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) := by
      simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u₂ _ => by split_ifs <;> ring
    rw [ha, hsym_u]; ring
  -- Reindex `u₂ ↦ uk = s + u + u₂`, rewrite using `sign_P4_eq`, and connect to `P4_s_prod_eq`!
  have hs_cross : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
      if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
        cval ψ u * cval ψ u₂ * (Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)) else 0) =
      ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2, ∑ u : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
        cval ψ (r + uk) * cval ψ (r + s + uk) *
          ((phaseRe (r + s + uk) u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u))) *
          ((phaseRe (r + uk) (s + uk + u) : ℝ) * cval ψ (s + uk + u) * cval ψ (r + s + u)) else 0 := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    have hstep : (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
          cval ψ u * cval ψ u₂ * (Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)) else 0) =
        ∑ u : PauliIdx 2, ∑ uk : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
          cval ψ (r + uk) * cval ψ (r + s + uk) *
            ((phaseRe (r + s + uk) u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u))) *
            ((phaseRe (r + uk) (s + uk + u) : ℝ) * cval ψ (s + uk + u) * cval ψ (r + s + u)) else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft (s + u)) _ _ fun u₂ => ?_
      change (if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then _ else 0) =
        (if symp s r = 1 ∧ inT s r (s + u + u₂) ∧ inT s r u ∧ u ≠ s + u + u₂ then
          cval ψ (r + (s + u + u₂)) * cval ψ (r + s + (s + u + u₂)) *
            ((phaseRe (r + s + (s + u + u₂)) u : ℝ) * cval ψ u * cval ψ (r + (s + (s + u + u₂) + u))) *
            ((phaseRe (r + (s + u + u₂)) (s + (s + u + u₂) + u) : ℝ) * cval ψ (s + (s + u + u₂) + u) * cval ψ (r + s + u)) else 0)
      have hback : s + (s + u + u₂) + u = u₂ := by
        calc s + (s + u + u₂) + u = (s + s) + (u + u) + u₂ := by abel
          _ = u₂ := by rw [pauliIdx_add_self, pauliIdx_add_self, zero_add, zero_add]
      have hiff : (symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u) ↔
          (symp s r = 1 ∧ inT s r (s + u + u₂) ∧ inT s r u ∧ u ≠ s + u + u₂) := by
        constructor
        · rintro ⟨hsr, hu, hu2, hne⟩
          have ht := hT_third s r u u₂ hsr hu hu2 hne
          exact ⟨hsr, ht.1, hu, ht.2.1.symm⟩
        · rintro ⟨hsr, huk, hu, hne⟩
          have ht := hT_third s r (s + u + u₂) u hsr huk hu hne
          rw [hback] at ht
          exact ⟨hsr, hu, ht.1, ht.2.2.1⟩
      by_cases hc : symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u
      · have hc' := hiff.mp hc
        have ht := hT_third s r (s + u + u₂) u hc'.1 hc'.2.1 hc'.2.2.1 hc'.2.2.2
        have hsgn := sign_P4_eq s r (s + u + u₂) u hc'.1 hc'.2.1.2.2.1 hc'.2.2.1.2.2.1
          hc'.2.1.2.2.2 hc'.2.2.1.2.2.2 ht.2.2.2
        have hsgnR : (phaseIm r (s + (s + u + u₂) + u) : ℝ) * (phaseIm r (s + u + u₂) : ℝ) *
            (phaseIm (r + s) u : ℝ) * (phaseIm (r + s) (s + u + u₂) : ℝ) =
            (phaseRe (r + s + (s + u + u₂)) u : ℝ) * (phaseRe (r + (s + u + u₂)) (s + (s + u + u₂) + u) : ℝ) := by
          exact_mod_cast hsgn
        rw [hback] at hsgnR
        rw [if_pos hc, if_pos hc', hback]
        simp only [Y]
        calc cval ψ u * cval ψ u₂ *
              ((phaseIm r u₂ : ℝ) * cval ψ (r + u₂) *
                ((phaseIm r (s + u + u₂) : ℝ) * cval ψ (r + (s + u + u₂))) *
                ((phaseIm (r + s) u : ℝ) * cval ψ (r + s + u)) *
                ((phaseIm (r + s) (s + u + u₂) : ℝ) * cval ψ (r + s + (s + u + u₂))))
            = ((phaseIm r u₂ : ℝ) * (phaseIm r (s + u + u₂) : ℝ) *
                (phaseIm (r + s) u : ℝ) * (phaseIm (r + s) (s + u + u₂) : ℝ)) *
              (cval ψ (r + (s + u + u₂)) * cval ψ (r + s + (s + u + u₂)) *
                cval ψ u * cval ψ (r + u₂) * cval ψ u₂ * cval ψ (r + s + u)) := by ring
          _ = ((phaseRe (r + s + (s + u + u₂)) u : ℝ) * (phaseRe (r + (s + u + u₂)) u₂ : ℝ)) *
              (cval ψ (r + (s + u + u₂)) * cval ψ (r + s + (s + u + u₂)) *
                cval ψ u * cval ψ (r + u₂) * cval ψ u₂ * cval ψ (r + s + u)) := by rw [hsgnR]
          _ = _ := by ring
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
    rw [hstep, Finset.sum_comm]
  -- Now prove the `rho² = rho` decomposition for fixed `(s, r, uk)` with `symp s r = 1 ∧ inT s r uk`:
  --   `(c_{zk} - Lz0) * (c_{yk} - Ly0) = ∑_{u ∈ T\{uk}} Lz(u) * (Ly(u) + Ly(s+uk+u))`!
  have hrho_decomp : ∀ s r uk : PauliIdx 2, symp s r = 1 → inT s r uk →
      (cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
      (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk)) =
      ∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
        ((phaseRe (r + s + uk) u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u))) *
        ((phaseRe (r + uk) (s + uk + u) : ℝ) * cval ψ (s + uk + u) * cval ψ (r + s + u) +
         (phaseRe (r + uk) u : ℝ) * cval ψ u * cval ψ (r + s + (s + uk + u))) else 0 := by
    intro s r uk hsr huk
    set yk := r + uk
    set zk := r + s + uk
    set vk := s + uk
    have hzk0 : zk ≠ 0 := fun h => by
      have : symp s zk = 0 := by rw [h, symp_zero_right]
      rw [symp_add_right, symp_add_right, hsr, symp_self, huk.2.2.1] at this; exact absurd this (by decide)
    have hyk0 : yk ≠ 0 := fun h => by
      have : symp s yk = 0 := by rw [h, symp_zero_right]
      rw [symp_add_right, hsr, huk.2.2.1] at this; exact absurd this (by decide)
    -- Show `∑_{u ∈ T\{uk}} Lz(u) = c_{zk} - Lz0` using `purity_comm_sum hunit hzk0`!
    have hLz_sum : (∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
        (phaseRe zk u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u)) else 0) =
        cval ψ zk - (phaseRe zk r : ℝ) * cval ψ r * cval ψ vk := by
      have hp := purity_comm_sum hunit hzk0
      have hr_in : r ≠ 0 ∧ r ≠ zk ∧ symp zk r = 0 := by
        have hr0 : r ≠ 0 := fun h => by rw [h, symp_zero_right] at hsr; exact absurd hsr (by decide)
        have hzr : symp zk r = 0 := by
          simp only [zk, symp_add_left, symp_self, hsr, symp_comm uk r, huk.2.2.2]; decide
        have hrzk : r ≠ zk := fun h => by
          have : s + uk = 0 := by
            have := congr_arg (r + ·) h; rw [pauliIdx_add_self] at this
            calc s + uk = r + (r + s + uk) := by
                  calc s + uk = (r + r) + (s + uk) := by rw [pauliIdx_add_self, zero_add]
                    _ = r + (r + s + uk) := by abel
              _ = 0 := this.symm
          exact huk.2.1 ((pauli_add_eq_zero_iff s uk).mp this).symm
        exact ⟨hr0, hrzk, hzr⟩
      have hvk_in : vk ≠ 0 ∧ vk ≠ zk ∧ symp zk vk = 0 := by
        have h1 : zk + r = vk := by
          calc r + s + uk + r = (r + r) + (s + uk) := by abel
            _ = s + uk := by rw [pauliIdx_add_self, zero_add]
        rw [← h1]
        exact ⟨fun h => hr_in.2.1 ((pauli_add_eq_zero_iff zk r).mp h).symm,
          fun h => hr_in.1 ((pauli_add_eq_left_iff zk r).mp h),
          by rw [symp_add_right, symp_self, zero_add]; exact hr_in.2.2⟩
      have hr_ne_vk : r ≠ vk := fun h => by
        have : symp s r = 0 := by rw [h, symp_add_right, symp_self, huk.2.2.1, add_zero]
        rw [hsr] at this; exact absurd this (by decide)
      -- Every `p ∈ zk^⊥ \ {0, zk}` is in `{r, vk}` OR in `T(s, r) \ {uk}` OR in `{zk + u | u ∈ T(s, r) \ {uk}}`!
      -- In fact, `p ↦ zk + p` maps `T(s, r) \ {uk}` to the remaining 2 elements of `zk^⊥ \ {0, zk, r, vk}`,
      -- with IDENTICAL summand `phaseRe zk p * c_p * c_{zk+p}`!
      have hsplit_z : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 then
          (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) =
          2 * ((phaseRe zk r : ℝ) * cval ψ r * cval ψ vk) +
          2 * (∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
            (phaseRe zk u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u)) else 0) := by
        -- Partition `zk^⊥ \ {0, zk}` by `symp s p ∈ {0, 1}`!
        --Wait: `symp s r = 1, symp s vk = 0`! Better: partition by `symp r p` or check the 6 elements!
        --Wait: `symp (s + r) p`? Even simpler: `T(s, r) \ {uk}` has `symp s u = 0 ∧ symp r u = 1`,
        --while `zk + u` has `symp s (zk + u) = symp s zk + 0 = 1` AND `symp r (zk + u) = 0 + 1 = 1`!
        --Check all 6 elements of `zk^⊥ \ {0, zk}` by `(symp s p, symp r p)`:
        --  - `r`: `(1, 0)`
        --  - `vk = zk + r`: `(0, 0)`!
        --  - `u ∈ T \ {uk}` (2 elts): `(0, 1)`!
        --  - `zk + u` (2 elts): `(1, 1)`!
        --WHOA!! `(symp s p, symp r p)` PARTITIONS THE 6 ELEMENTS OF `zk^⊥ \ {0, zk}` CLEANLY INTO `{r, vk}` (`symp r p = 0`) AND `{u, zk + u}` (`symp r p = 1`)!!
        have hpart_r0 : ∀ p : PauliIdx 2, p ≠ 0 → p ≠ zk → symp zk p = 0 → symp r p = 0 → p = r ∨ p = vk := by
          intro p hp0 hpzk hzkp hrp
          rcases mem_perp_inter_four zk r p hzk0 hr_in.1 hr_in.2.1 hr_in.2.2 hzkp hrp with rfl | rfl | rfl | rfl
          · exact absurd rfl hp0
          · exact absurd rfl hpzk
          · left; rfl
          · right; calc zk + r = (r + r) + (s + uk) := by simp only [zk]; abel
              _ = vk := by rw [pauliIdx_add_self, zero_add]
        have hpart_s0r1 : ∀ p : PauliIdx 2,
            (p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 0 ∧ symp r p = 1) ↔
            (inT s r p ∧ p ≠ uk) := fun p => by
          constructor
          · rintro ⟨hp0, _, hzkp, hsp, hrp⟩
            have hps : p ≠ s := fun h => by
              rw [h] at hzkp
              simp only [zk, symp_add_left, symp_comm r s, hsr, symp_self, symp_comm uk s, huk.2.2.1] at hzkp
              exact absurd hzkp (by decide)
            have hpuk : p ≠ uk := fun h => by
              rw [h] at hzkp
              simp only [zk, symp_add_left, huk.2.2.2, huk.2.2.1, symp_self] at hzkp
              exact absurd hzkp (by decide)
            exact ⟨⟨hp0, hps, hsp, hrp⟩, hpuk⟩
          · rintro ⟨⟨hp0, hps, hsp, hrp⟩, hpuk⟩
            have ht := hT_third s r uk p hsr huk ⟨hp0, hps, hsp, hrp⟩ hpuk
            have hzkp : symp zk p = 0 := by
              simp only [zk, symp_add_left, hrp, hsp, ht.2.2.2]; decide
            have hpzk : p ≠ zk := fun h => by
              have : symp s p = 1 := by rw [h]; simp only [zk, symp_add_right, hsr, symp_self, huk.2.2.1]; decide
              rw [hsp] at this; exact absurd this (by decide)
            exact ⟨hp0, hpzk, hzkp, hsp, hrp⟩
        have hsum_r0 : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp r p = 0 then
            (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) =
            2 * ((phaseRe zk r : ℝ) * cval ψ r * cval ψ vk) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
          have hvkin : vk ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨Ne.symm hr_ne_vk, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hvkin]
          have hrest : ∑ p ∈ (Finset.univ.erase r).erase vk,
              (if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp r p = 0 then
                (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have h1 : p ≠ vk := (Finset.mem_erase.mp hp).1
            have h2 : p ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
            rw [if_neg]
            rintro ⟨hp0, hpzk, hzkp, hrp⟩
            rcases hpart_r0 p hp0 hpzk hzkp hrp with rfl | rfl <;> [exact h2 rfl; exact h1 rfl]
          rw [hrest, add_zero]
          have hrr : symp r r = 0 := symp_self r
          have hrvk : symp r vk = 0 := by rw [symp_add_right, symp_comm r s, hsr, huk.2.2.2]; decide
          rw [if_pos ⟨hr_in.1, hr_in.2.1, hr_in.2.2, hrr⟩, if_pos ⟨hvk_in.1, hvk_in.2.1, hvk_in.2.2, hrvk⟩]
          have h1 : zk + r = vk := by
            calc r + s + uk + r = (r + r) + (s + uk) := by abel
              _ = s + uk := by rw [pauliIdx_add_self, zero_add]
          have h2 : zk + vk = r := by
            calc r + s + uk + (s + uk) = r + (s + s) + (uk + uk) := by abel
              _ = r := by rw [pauliIdx_add_self, pauliIdx_add_self, add_zero, add_zero]
          have hph : phaseRe zk vk = phaseRe zk r := by
            rw [← h1]; exact (phaseRe_comm_sym zk r hr_in.2.2).2.symm
          rw [h1, h2, hph]; ring
        have hsum_s1r1 : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 1 ∧ symp r p = 1 then
            (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) =
            ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 0 ∧ symp r p = 1 then
            (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0 := by
          refine Fintype.sum_equiv (Equiv.addLeft zk) _ _ fun p => ?_
          change (if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 1 ∧ symp r p = 1 then _ else 0) =
            (if zk + p ≠ 0 ∧ zk + p ≠ zk ∧ symp zk (zk + p) = 0 ∧ symp s (zk + p) = 0 ∧ symp r (zk + p) = 1 then
              (phaseRe zk (zk + p) : ℝ) * cval ψ (zk + p) * cval ψ (zk + (zk + p)) else 0)
          have hszk : symp s zk = 1 := by simp only [zk, symp_add_right, hsr, symp_self, huk.2.2.1]; decide
          have hrzk : symp r zk = 0 := by rw [symp_comm]; exact hr_in.2.2
          have hcond : (p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 1 ∧ symp r p = 1) ↔
              (zk + p ≠ 0 ∧ zk + p ≠ zk ∧ symp zk (zk + p) = 0 ∧ symp s (zk + p) = 0 ∧ symp r (zk + p) = 1) := by
            simp only [ne_eq, pauli_add_eq_zero_iff, pauli_add_eq_left_iff,
                symp_add_right zk zk p, symp_self, zero_add,
                symp_add_right s zk p, hszk, symp_add_right r zk p, hrzk]
            constructor
            · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨Ne.symm h2, h1, h3, by rw [h4]; decide, h5⟩
            · rintro ⟨h1, h2, h3, h4, h5⟩
              have hsp : symp s p = 1 := by
                rcases zmod2_cases (symp s p) with h0 | h1'
                · rw [h0] at h4; exact absurd h4 (by decide)
                · exact h1'
              exact ⟨h2, Ne.symm h1, h3, hsp, h5⟩
          by_cases hc : p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 1 ∧ symp r p = 1
          · rw [if_pos hc, if_pos (hcond.mp hc), pauliIdx_add_cancel_left, ← (phaseRe_comm_sym zk p hc.2.2.1).2]; ring
          · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
        have hsum_all : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 then
            (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) =
            (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp r p = 0 then
              (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) +
            (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 0 ∧ symp r p = 1 then
              (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) +
            (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 1 ∧ symp r p = 1 then
              (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) := by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hc : p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0
          · rcases zmod2_cases (symp r p) with hr0 | hr1
            · rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hc.2.2, hr0⟩,
                  if_neg (fun h => by rw [hr0] at h; exact absurd h.2.2.2.2 (by decide)),
                  if_neg (fun h => by rw [hr0] at h; exact absurd h.2.2.2.2 (by decide))]; ring
            · rcases zmod2_cases (symp s p) with hs0 | hs1
              · rw [if_pos hc, if_neg (fun h => by rw [hr1] at h; exact absurd h.2.2.2 (by decide)),
                    if_pos ⟨hc.1, hc.2.1, hc.2.2, hs0, hr1⟩,
                    if_neg (fun h => by rw [hs0] at h; exact absurd h.2.2.2.1 (by decide))]; ring
              · rw [if_pos hc, if_neg (fun h => by rw [hr1] at h; exact absurd h.2.2.2 (by decide)),
                    if_neg (fun h => by rw [hs1] at h; exact absurd h.2.2.2.1 (by decide)),
                    if_pos ⟨hc.1, hc.2.1, hc.2.2, hs1, hr1⟩]; ring
          · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩),
                if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩),
                if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]; ring
        have hsum_T : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ zk ∧ symp zk p = 0 ∧ symp s p = 0 ∧ symp r p = 1 then
            (phaseRe zk p : ℝ) * cval ψ p * cval ψ (zk + p) else 0) =
            ∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
              (phaseRe zk u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u)) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          have hidx : zk + u = r + (s + uk + u) := by simp only [zk]; abel
          rw [hidx]
          by_cases hc : inT s r u ∧ u ≠ uk
          · rw [if_pos ((hpart_s0r1 u).mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc ((hpart_s0r1 u).mp h)), if_neg hc]
        rw [hsum_all, hsum_r0, hsum_s1r1, hsum_T]; ring
      rw [hsplit_z] at hp; linarith
    -- By symmetry `r ↔ r + s`, the EXACT same formula holds for `yk = r + uk`!
    have hLy_sum : (∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
        (phaseRe yk u : ℝ) * cval ψ u * cval ψ (r + s + (s + uk + u)) else 0) =
        cval ψ yk - (phaseRe yk (r + s) : ℝ) * cval ψ (r + s) * cval ψ vk := by
      -- Exact same proof as `hLz_sum` with `r' = r + s`!
      have hp := purity_comm_sum hunit hyk0
      have hrs_sr : symp s (r + s) = 1 := by rw [symp_add_right, hsr, symp_self, add_zero]
      have hrr_in : r + s ≠ 0 ∧ r + s ≠ yk ∧ symp yk (r + s) = 0 := by
        have h1 : r + s ≠ 0 := fun h => by rw [h, symp_zero_right] at hrs_sr; exact absurd hrs_sr (by decide)
        have h2 : symp yk (r + s) = 0 := by
          simp only [yk, symp_add_left, symp_add_right, symp_self, symp_comm r s, hsr,
            symp_comm uk r, huk.2.2.2, symp_comm uk s, huk.2.2.1]; decide
        have h3 : r + s ≠ yk := fun h => by
          have : s + uk = 0 := by
            have := congr_arg (r + ·) h
            calc s + uk = r + (r + s) + (r + (r + uk)) := by
                  calc s + uk = ((r + r) + (r + r)) + (s + uk) := by rw [pauliIdx_add_self, zero_add]
                    _ = r + (r + s) + (r + (r + uk)) := by abel
              _ = r + (r + uk) + (r + (r + uk)) := by rw [h]
              _ = 0 := pauliIdx_add_self _
          exact huk.2.1 ((pauli_add_eq_zero_iff s uk).mp this).symm
        exact ⟨h1, h3, h2⟩
      have hvk_in : vk ≠ 0 ∧ vk ≠ yk ∧ symp yk vk = 0 := by
        have h1 : yk + (r + s) = vk := by
          calc r + uk + (r + s) = (r + r) + (s + uk) := by abel
            _ = s + uk := by rw [pauliIdx_add_self, zero_add]
        rw [← h1]
        exact ⟨fun h => hrr_in.2.1 ((pauli_add_eq_zero_iff yk (r + s)).mp h).symm,
          fun h => hrr_in.1 ((pauli_add_eq_left_iff yk (r + s)).mp h),
          by rw [symp_add_right, symp_self, zero_add]; exact hrr_in.2.2⟩
      have hrr_ne_vk : r + s ≠ vk := fun h => by
        have : symp s (r + s) = 0 := by rw [h, symp_add_right, symp_self, huk.2.2.1, add_zero]
        rw [hrs_sr] at this; exact absurd this (by decide)
      have hpart_r0 : ∀ p : PauliIdx 2, p ≠ 0 → p ≠ yk → symp yk p = 0 → symp (r + s) p = 0 → p = r + s ∨ p = vk := by
        intro p hp0 hpyk hykp hrrp
        rcases mem_perp_inter_four yk (r + s) p hyk0 hrr_in.1 hrr_in.2.1 hrr_in.2.2 hykp hrrp with rfl | rfl | rfl | rfl
        · exact absurd rfl hp0
        · exact absurd rfl hpyk
        · left; rfl
        · right; calc yk + (r + s) = (r + r) + (s + uk) := by simp only [yk]; abel
            _ = vk := by rw [pauliIdx_add_self, zero_add]
      have hpart_s0r1 : ∀ p : PauliIdx 2,
          (p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 0 ∧ symp (r + s) p = 1) ↔
          (inT s r p ∧ p ≠ uk) := fun p => by
        constructor
        · rintro ⟨hp0, _, hykp, hsp, hrrp⟩
          have hrp : symp r p = 1 := by rw [symp_add_left, hsp, add_zero] at hrrp; exact hrrp
          have hps : p ≠ s := fun h => by
            rw [h] at hykp
            simp only [yk, symp_add_left, symp_comm r s, hsr, symp_comm uk s, huk.2.2.1] at hykp
            exact absurd hykp (by decide)
          have hpuk : p ≠ uk := fun h => by
            rw [h] at hykp
            simp only [yk, symp_add_left, huk.2.2.2, symp_self] at hykp
            exact absurd hykp (by decide)
          exact ⟨⟨hp0, hps, hsp, hrp⟩, hpuk⟩
        · rintro ⟨⟨hp0, hps, hsp, hrp⟩, hpuk⟩
          have ht := hT_third s r uk p hsr huk ⟨hp0, hps, hsp, hrp⟩ hpuk
          have hykp : symp yk p = 0 := by simp only [yk, symp_add_left, hrp, ht.2.2.2]; decide
          have hpyk : p ≠ yk := fun h => by
            have : symp s p = 1 := by rw [h]; simp only [yk, symp_add_right, hsr, huk.2.2.1]; decide
            rw [hsp] at this; exact absurd this (by decide)
          exact ⟨hp0, hpyk, hykp, hsp, by rw [symp_add_left, hrp, hsp, add_zero]⟩
      have hsum_r0 : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp (r + s) p = 0 then
          (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) =
          2 * ((phaseRe yk (r + s) : ℝ) * cval ψ (r + s) * cval ψ vk) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (r + s))]
        have hvkin : vk ∈ Finset.univ.erase (r + s) := Finset.mem_erase.mpr ⟨Ne.symm hrr_ne_vk, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hvkin]
        have hrest : ∑ p ∈ (Finset.univ.erase (r + s)).erase vk,
            (if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp (r + s) p = 0 then
              (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have h1 : p ≠ vk := (Finset.mem_erase.mp hp).1
          have h2 : p ≠ r + s := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
          rw [if_neg]
          rintro ⟨hp0, hpyk, hykp, hrrp⟩
          rcases hpart_r0 p hp0 hpyk hykp hrrp with rfl | rfl <;> [exact h2 rfl; exact h1 rfl]
        rw [hrest, add_zero]
        have hrr : symp (r + s) (r + s) = 0 := symp_self _
        have hrvk : symp (r + s) vk = 0 := by
          simp only [vk, symp_add_left, symp_add_right, symp_comm r s, hsr, huk.2.2.2, symp_self, huk.2.2.1]; decide
        rw [if_pos ⟨hrr_in.1, hrr_in.2.1, hrr_in.2.2, hrr⟩, if_pos ⟨hvk_in.1, hvk_in.2.1, hvk_in.2.2, hrvk⟩]
        have h1 : yk + (r + s) = vk := by
          calc r + uk + (r + s) = (r + r) + (s + uk) := by abel
            _ = s + uk := by rw [pauliIdx_add_self, zero_add]
        have h2 : yk + vk = r + s := by
          calc r + uk + (s + uk) = r + s + (uk + uk) := by abel
            _ = r + s := by rw [pauliIdx_add_self, add_zero]
        have hph : phaseRe yk vk = phaseRe yk (r + s) := by
          rw [← h1]; exact (phaseRe_comm_sym yk (r + s) hrr_in.2.2).2.symm
        rw [h1, h2, hph]; ring
      have hsum_s1r1 : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 1 ∧ symp (r + s) p = 1 then
          (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) =
          ∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 0 ∧ symp (r + s) p = 1 then
          (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0 := by
        refine Fintype.sum_equiv (Equiv.addLeft yk) _ _ fun p => ?_
        change (if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 1 ∧ symp (r + s) p = 1 then _ else 0) =
          (if yk + p ≠ 0 ∧ yk + p ≠ yk ∧ symp yk (yk + p) = 0 ∧ symp s (yk + p) = 0 ∧ symp (r + s) (yk + p) = 1 then
            (phaseRe yk (yk + p) : ℝ) * cval ψ (yk + p) * cval ψ (yk + (yk + p)) else 0)
        have hsyk : symp s yk = 1 := by simp only [yk, symp_add_right, hsr, huk.2.2.1]; decide
        have hrryk : symp (r + s) yk = 0 := by rw [symp_comm]; exact hrr_in.2.2
        have hcond : (p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 1 ∧ symp (r + s) p = 1) ↔
            (yk + p ≠ 0 ∧ yk + p ≠ yk ∧ symp yk (yk + p) = 0 ∧ symp s (yk + p) = 0 ∧ symp (r + s) (yk + p) = 1) := by
          simp only [ne_eq, pauli_add_eq_zero_iff, pauli_add_eq_left_iff,
              symp_add_right yk yk p, symp_self, zero_add,
              symp_add_right s yk p, hsyk, symp_add_right (r + s) yk p, hrryk]
          constructor
          · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨Ne.symm h2, h1, h3, by rw [h4]; decide, h5⟩
          · rintro ⟨h1, h2, h3, h4, h5⟩
            have hsp : symp s p = 1 := by
              rcases zmod2_cases (symp s p) with h0 | h1'
              · rw [h0] at h4; exact absurd h4 (by decide)
              · exact h1'
            exact ⟨h2, Ne.symm h1, h3, hsp, h5⟩
        by_cases hc : p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 1 ∧ symp (r + s) p = 1
        · rw [if_pos hc, if_pos (hcond.mp hc), pauliIdx_add_cancel_left, ← (phaseRe_comm_sym yk p hc.2.2.1).2]; ring
        · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
      have hsum_all : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 then
          (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) =
          (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp (r + s) p = 0 then
            (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) +
          (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 0 ∧ symp (r + s) p = 1 then
            (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) +
          (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 1 ∧ symp (r + s) p = 1 then
            (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hc : p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0
        · rcases zmod2_cases (symp (r + s) p) with hr0 | hr1
          · rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hc.2.2, hr0⟩,
                if_neg (fun h => by rw [hr0] at h; exact absurd h.2.2.2.2 (by decide)),
                if_neg (fun h => by rw [hr0] at h; exact absurd h.2.2.2.2 (by decide))]; ring
          · rcases zmod2_cases (symp s p) with hs0 | hs1
            · rw [if_pos hc, if_neg (fun h => by rw [hr1] at h; exact absurd h.2.2.2 (by decide)),
                  if_pos ⟨hc.1, hc.2.1, hc.2.2, hs0, hr1⟩,
                  if_neg (fun h => by rw [hs0] at h; exact absurd h.2.2.2.1 (by decide))]; ring
            · rw [if_pos hc, if_neg (fun h => by rw [hr1] at h; exact absurd h.2.2.2 (by decide)),
                  if_neg (fun h => by rw [hs1] at h; exact absurd h.2.2.2.1 (by decide)),
                  if_pos ⟨hc.1, hc.2.1, hc.2.2, hs1, hr1⟩]; ring
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩),
              if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩),
              if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]; ring
      have hsum_T : (∑ p : PauliIdx 2, if p ≠ 0 ∧ p ≠ yk ∧ symp yk p = 0 ∧ symp s p = 0 ∧ symp (r + s) p = 1 then
          (phaseRe yk p : ℝ) * cval ψ p * cval ψ (yk + p) else 0) =
          ∑ u : PauliIdx 2, if inT s r u ∧ u ≠ uk then
            (phaseRe yk u : ℝ) * cval ψ u * cval ψ (r + s + (s + uk + u)) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have hidx : yk + u = r + s + (s + uk + u) := by
          calc r + uk + u = r + (s + s) + uk + u := by rw [pauliIdx_add_self, add_zero]
            _ = r + s + (s + uk + u) := by abel
        rw [hidx]
        by_cases hc : inT s r u ∧ u ≠ uk
        · rw [if_pos ((hpart_s0r1 u).mpr hc), if_pos hc]
        · rw [if_neg (fun h => hc ((hpart_s0r1 u).mp h)), if_neg hc]
      rw [hsum_all, hsum_r0, hsum_s1r1, hsum_T] at hp; linarith
    -- Multiply `hLz_sum` and `hLy_sum`! For each `u ∈ T\{uk}`, the sum over `v ∈ T\{uk}` is just `v = u` and `v = s + uk + u`!
    rw [← hLz_sum, ← hLy_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : inT s r u ∧ u ≠ uk
    · rw [if_pos hu, if_pos hu]
      have ht := hT_third s r uk u hsr huk hu.1 hu.2
      set u₂ := s + uk + u
      have hLy_2 : (∑ v : PauliIdx 2, if inT s r v ∧ v ≠ uk then
          (phaseRe yk v : ℝ) * cval ψ v * cval ψ (r + s + (s + uk + v)) else 0) =
          (phaseRe yk u₂ : ℝ) * cval ψ u₂ * cval ψ (r + s + u) +
          (phaseRe yk u : ℝ) * cval ψ u * cval ψ (r + s + u₂) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
        have hu2in : u₂ ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨ht.2.2.1, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hu2in]
        have hrest : ∑ v ∈ (Finset.univ.erase u).erase u₂,
            (if inT s r v ∧ v ≠ uk then
              (phaseRe yk v : ℝ) * cval ψ v * cval ψ (r + s + (s + uk + v)) else 0) = 0 := by
          refine Finset.sum_eq_zero fun v hv => ?_
          have hv2 : v ≠ u₂ := (Finset.mem_erase.mp hv).1
          have hv1 : v ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
          rw [if_neg]
          rintro ⟨hvt, hvuk⟩
          rcases T_set_eq_three s r uk u v hsr huk.1 huk.2.1 huk.2.2.1 huk.2.2.2
              hu.1.1 hu.1.2.1 hu.1.2.2.1 hu.1.2.2.2 hu.2 hvt.1 hvt.2.1 hvt.2.2.1 hvt.2.2.2 with rfl | rfl | rfl
          · exact hvuk rfl
          · exact hv1 rfl
          · exact hv2 rfl
        rw [hrest, add_zero, if_pos hu, if_pos ⟨ht.1, ht.2.1⟩]
        have hback : s + uk + u₂ = u := by
          calc s + uk + (s + uk + u) = (s + s) + (uk + uk) + u := by abel
            _ = u := by rw [pauliIdx_add_self, pauliIdx_add_self, zero_add, zero_add]
        rw [hback]; ring
      rw [hLy_2]
    · rw [if_neg hu, if_neg hu, zero_mul]
  -- Now sum `hrho_decomp` multiplied by `c_{r+uk} c_{r+s+uk}` over `(s, r, uk)`!
  have hs_prod_split : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk then
        cval ψ (r + uk) * cval ψ (r + s + uk) *
          (cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
          (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk)) else 0) =
      (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2, ∑ u : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
          cval ψ (r + uk) * cval ψ (r + s + uk) *
            ((phaseRe (r + s + uk) u : ℝ) * cval ψ u * cval ψ (r + (s + uk + u))) *
            ((phaseRe (r + uk) (s + uk + u) : ℝ) * cval ψ (s + uk + u) * cval ψ (r + s + u)) else 0) +
      (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2, ∑ u : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
          gval ψ u * ((phaseRe (r + s + uk) u : ℝ) * cval ψ (r + s + uk) * cval ψ (r + (s + uk + u))) *
            ((phaseRe (r + uk) u : ℝ) * cval ψ (r + uk) * cval ψ (r + s + (s + uk + u))) else 0) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun uk _ => ?_
    by_cases hc : symp s r = 1 ∧ inT s r uk
    · rw [if_pos hc]
      have hd := congr_arg (cval ψ (r + uk) * cval ψ (r + s + uk) * ·) (hrho_decomp s r uk hc.1 hc.2)
      rw [Finset.mul_sum] at hd
      have hl : cval ψ (r + uk) * cval ψ (r + s + uk) *
          (cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
          (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk)) =
          cval ψ (r + uk) * cval ψ (r + s + uk) *
            ((cval ψ (r + s + uk) - (phaseRe (r + s + uk) r : ℝ) * cval ψ r * cval ψ (s + uk)) *
             (cval ψ (r + uk) - (phaseRe (r + uk) (r + s) : ℝ) * cval ψ (r + s) * cval ψ (s + uk))) := by ring
      rw [hl, hd]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : inT s r u ∧ u ≠ uk
      · rw [if_pos hu, if_pos ⟨hc.1, hc.2, hu.1, hu.2⟩, if_pos ⟨hc.1, hc.2, hu.1, hu.2⟩]
        simp only [gval]; ring
      · rw [if_neg hu, if_neg (fun h => hu ⟨h.2.2.1, h.2.2.2⟩), if_neg (fun h => hu ⟨h.2.2.1, h.2.2.2⟩)]; ring
    · rw [if_neg hc]
      symm; refine Finset.sum_eq_zero fun u _ => ?_
      rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg (fun h => hc ⟨h.1, h.2.1⟩), add_zero]
  -- Evaluate `s_same = 2 * P2_core = 8 F₄ - 4 T_ord - 8`!
  have hs_same : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2, ∑ u : PauliIdx 2,
      if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
        gval ψ u * ((phaseRe (r + s + uk) u : ℝ) * cval ψ (r + s + uk) * cval ψ (r + (s + uk + u))) *
          ((phaseRe (r + uk) u : ℝ) * cval ψ (r + uk) * cval ψ (r + s + (s + uk + u))) else 0) =
      8 * F4 ψ - 4 * Tord ψ - 8 := by
    -- Rewrite phases using `phaseRe_comm_sym`, then EXACT same `fiber_T_pair_count` reindexing `(s, r, uk, u) ↦ (u, p = r + uk, q = r + s + uk + u, uk)`!
    have hrew : (∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ uk : PauliIdx 2, ∑ u : PauliIdx 2,
        if symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk then
          gval ψ u * ((phaseRe (r + s + uk) u : ℝ) * cval ψ (r + s + uk) * cval ψ (r + (s + uk + u))) *
            ((phaseRe (r + uk) u : ℝ) * cval ψ (r + uk) * cval ψ (r + s + (s + uk + u))) else 0) =
        ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, ∑ u : PauliIdx 2, ∑ uk : PauliIdx 2,
        if symp s r = 1 ∧ inT s r u ∧ inT s r uk ∧ uk ≠ u then
          gval ψ u * ((phaseRe u (r + uk) : ℝ) * cval ψ (r + uk) * cval ψ (u + (r + uk))) *
            ((phaseRe u (r + (s + u + uk)) : ℝ) * cval ψ (r + (s + u + uk)) * cval ψ (u + (r + (s + u + uk)))) else 0 := by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun uk _ => ?_
      by_cases hc : symp s r = 1 ∧ inT s r uk ∧ inT s r u ∧ u ≠ uk
      · have hc' : symp s r = 1 ∧ inT s r u ∧ inT s r uk ∧ uk ≠ u :=
          ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2.symm⟩
        have ht := hT_third s r uk u hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
        have hcm1 : symp u (r + uk) = 0 := by
          rw [symp_add_right, symp_comm u r, hc.2.2.1.2.2.2, symp_comm u uk, ht.2.2.2]; decide
        have hcm2 : symp u (r + s + uk) = 0 := by
          rw [symp_add_right, symp_add_right, symp_comm u r, hc.2.2.1.2.2.2, symp_comm u s,
              hc.2.2.1.2.2.1, symp_comm u uk, ht.2.2.2]; decide
        have hph1 : phaseRe (r + uk) u = phaseRe u (r + uk) := (phaseRe_comm_sym u (r + uk) hcm1).1.symm
        have hph2 : phaseRe (r + s + uk) u = phaseRe u (r + (s + u + uk)) := by
          have h1 := (phaseRe_comm_sym u (r + s + uk) hcm2).1.symm
          have h2 := (phaseRe_comm_sym u (r + s + uk) hcm2).2
          have he : u + (r + s + uk) = r + (s + u + uk) := by abel
          rw [h1, h2, he]
        have hi1 : r + s + (s + uk + u) = u + (r + uk) := by
          calc r + s + (s + uk + u) = (s + s) + (u + (r + uk)) := by abel
            _ = u + (r + uk) := by rw [pauliIdx_add_self, zero_add]
        have hi2 : r + (s + uk + u) = r + (s + u + uk) := by abel
        have hi3 : r + s + uk = u + (r + (s + u + uk)) := by
          calc r + s + uk = (u + u) + (r + s + uk) := by rw [pauliIdx_add_self, zero_add]
            _ = u + (r + (s + u + uk)) := by abel
        rw [if_pos hc, if_pos hc', hph1, hph2, hi1, hi2, hi3]; ring
      · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩)]
    rw [hrew, sum_T_pair_reidx (fun u p q => gval ψ u * ((phaseRe u p : ℝ) * cval ψ p * cval ψ (u + p)) *
        ((phaseRe u q : ℝ) * cval ψ q * cval ψ (u + q))), P2_core_eq hunit]; ring
  have hprod := P4_s_prod_eq hunit
  rw [hsplit, hs_cross]
  linarith

/-- **SOS Identity A (Cut 10)**: `28 F₄ - 12 T_ord - 40 ≥ 0`. -/
private lemma sos_A_nonneg (hunit : IsUnitState ψ) :
    0 ≤ 28 * F4 ψ - 12 * Tord ψ - 40 := by
  let Y := Yval ψ
  let B : PauliIdx 2 → PauliIdx 2 → PauliIdx 2 → ℝ := fun s r u =>
    ∑ v : PauliIdx 2,
      if inT s r v ∧ v ≠ u then
        Y r v * Y r (s + u + v) - Y (r + s) v * Y (r + s) (s + u + v)
      else 0
  let Q : PauliIdx 2 → PauliIdx 2 → ℝ := fun s r =>
    ∑ u : PauliIdx 2, if inT s r u then cval ψ u * B s r u else 0
  let S_A : ℝ := ∑ s : PauliIdx 2, ∑ r : PauliIdx 2, if symp s r = 1 then Q s r ^ 2 else 0
  have hnn : 0 ≤ S_A := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun r _ => by
    split_ifs <;> [exact sq_nonneg _; exact le_rfl]
  have hB_eval : ∀ s r u v : PauliIdx 2,
      symp s r = 1 → inT s r u → inT s r v → v ≠ u →
      B s r u = 2 * (Y r v * Y r (s + u + v) - Y (r + s) v * Y (r + s) (s + u + v)) := by
    intro s r u v hsr hu hv hvu
    have ht := T_third_prop s r u v hsr hu hv hvu
    set w := s + u + v
    simp only [B]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have hwin : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨ht.2.2.1, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hwin]
    have hrest : ∑ x ∈ (Finset.univ.erase v).erase w,
        (if inT s r x ∧ x ≠ u then
          Y r x * Y r (s + u + x) - Y (r + s) x * Y (r + s) (s + u + x) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      rw [if_neg]
      rintro ⟨hxt, hxu⟩
      rcases T_set_eq_three s r u v x hsr hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
          hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hvu hxt.1 hxt.2.1 hxt.2.2.1 hxt.2.2.2 with rfl | rfl | rfl
      · exact hxu rfl
      · exact hxv rfl
      · exact hxw rfl
    rw [hrest, add_zero, if_pos ⟨hv, hvu⟩, if_pos ⟨ht.1, ht.2.1⟩]
    have hsuw : s + u + w = v := by
      calc s + u + (s + u + v) = (s + s) + (u + u) + v := by abel
        _ = v := by rw [pauliIdx_add_self, pauliIdx_add_self, zero_add, zero_add]
    rw [hsuw]; ring
  have hB_sq : ∀ s r u : PauliIdx 2, symp s r = 1 → inT s r u →
      B s r u ^ 2 = 2 * ∑ v : PauliIdx 2,
        if inT s r v ∧ v ≠ u then
          (Y r v * Y r (s + u + v) - Y (r + s) v * Y (r + s) (s + u + v)) ^ 2
        else 0 := by
    intro s r u hsr hu
    have hmul : B s r u ^ 2 = ∑ v : PauliIdx 2,
        if inT s r v ∧ v ≠ u then
          B s r u * (Y r v * Y r (s + u + v) - Y (r + s) v * Y (r + s) (s + u + v))
        else 0 := by
      rw [sq]
      conv_lhs => rhs; simp only [B]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    rw [hmul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : inT s r v ∧ v ≠ u
    · rw [if_pos hv, if_pos hv, hB_eval s r u v hsr hu hv.1 hv.2]; ring
    · rw [if_neg hv, if_neg hv, mul_zero]
  have hQ_sq : ∀ s r : PauliIdx 2, symp s r = 1 →
      Q s r ^ 2 =
        2 * (∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
          if inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (Y r v ^ 2 * Y r (s + u + v) ^ 2 + Y (r + s) v ^ 2 * Y (r + s) (s + u + v) ^ 2) else 0) +
        2 * (∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
          if inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (-2 * (Y r v * Y r (s + u + v) * Y (r + s) v * Y (r + s) (s + u + v))) else 0) +
        4 * (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2 + Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) +
        4 * (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (- Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)
               - Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) := by
    intro s r hsr
    have hexp : Q s r ^ 2 =
        (∑ u : PauliIdx 2, if inT s r u then gval ψ u * B s r u ^ 2 else 0) +
        (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then cval ψ u * cval ψ u₂ * (B s r u * B s r u₂) else 0) := by
      simp only [Q, sq, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
      have hdiag : (if inT s r u then cval ψ u * B s r u else 0) *
          (if inT s r u then cval ψ u * B s r u else 0) =
          if inT s r u then gval ψ u * B s r u ^ 2 else 0 := by
        by_cases hu : inT s r u
        · rw [if_pos hu, if_pos hu]; simp only [gval]; ring
        · rw [if_neg hu, if_neg hu]; ring
      have hoff : ∑ u₂ ∈ Finset.univ.erase u,
          (if inT s r u then cval ψ u * B s r u else 0) *
          (if inT s r u₂ then cval ψ u₂ * B s r u₂ else 0) =
          ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then cval ψ u * cval ψ u₂ * (B s r u * B s r u₂) else 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
        have hz : (if inT s r u ∧ inT s r u ∧ u ≠ u then cval ψ u * cval ψ u * (B s r u * B s r u) else 0) = 0 :=
          if_neg (by simp)
        rw [hz, zero_add]
        refine Finset.sum_congr rfl fun u₂ hu₂ => ?_
        have hne : u₂ ≠ u := (Finset.mem_erase.mp hu₂).1
        by_cases hu : inT s r u
        · by_cases h2 : inT s r u₂
          · rw [if_pos hu, if_pos h2, if_pos ⟨hu, h2, hne⟩]; ring
          · rw [if_pos hu, if_neg h2, if_neg (fun h => h2 h.2.1), mul_zero]
        · rw [if_neg hu, zero_mul, if_neg (fun h => hu h.1)]
      rw [hdiag, hoff]
      congr 1
      by_cases hu : inT s r u
      · rw [if_pos hu, if_pos hu]; simp only [gval]; ring
      · rw [if_neg hu, if_neg hu]
    have hdiag_split : (∑ u : PauliIdx 2, if inT s r u then gval ψ u * B s r u ^ 2 else 0) =
        2 * (∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
          if inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (Y r v ^ 2 * Y r (s + u + v) ^ 2 + Y (r + s) v ^ 2 * Y (r + s) (s + u + v) ^ 2) else 0) +
        2 * (∑ u : PauliIdx 2, ∑ v : PauliIdx 2,
          if inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (-2 * (Y r v * Y r (s + u + v) * Y (r + s) v * Y (r + s) (s + u + v))) else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : inT s r u
      · rw [if_pos hu, hB_sq s r u hsr hu]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : inT s r v ∧ v ≠ u
        · rw [if_pos hv, if_pos ⟨hu, hv⟩, if_pos ⟨hu, hv⟩]; ring
        · rw [if_neg hv, if_neg (fun h => hv h.2), if_neg (fun h => hv h.2)]; ring
      · rw [if_neg hu]
        symm; refine Finset.sum_eq_zero fun v _ => ?_
        rw [if_neg (fun h => hu h.1), if_neg (fun h => hu h.1)]; ring
    have hoff_split : (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
        if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then cval ψ u * cval ψ u₂ * (B s r u * B s r u₂) else 0) =
        4 * (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2 + Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) +
        4 * (∑ u : PauliIdx 2, ∑ u₂ : PauliIdx 2,
          if inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (- Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)
               - Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u₂ _ => ?_
      by_cases hc : inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u
      · rw [if_pos hc, if_pos hc, if_pos hc,
            hB_eval s r u u₂ hsr hc.1 hc.2.1 hc.2.2,
            hB_eval s r u₂ u hsr hc.2.1 hc.1 hc.2.2.symm]
        have hcomm : s + u₂ + u = s + u + u₂ := by abel
        rw [hcomm]; ring
      · rw [if_neg hc, if_neg hc, if_neg hc]; ring
    rw [hexp, hdiag_split, hoff_split]; ring
  have hSA_split : S_A =
      2 * (∑ s, ∑ r, ∑ u, ∑ v, if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (Y r v ^ 2 * Y r (s + u + v) ^ 2 + Y (r + s) v ^ 2 * Y (r + s) (s + u + v) ^ 2) else 0) +
      2 * (∑ s, ∑ r, ∑ u, ∑ v, if symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u then
            gval ψ u * (-2 * (Y r v * Y r (s + u + v) * Y (r + s) v * Y (r + s) (s + u + v))) else 0) +
      4 * (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (Y r u * Y r u₂ * Y r (s + u + u₂) ^ 2 + Y (r + s) u * Y (r + s) u₂ * Y (r + s) (s + u + u₂) ^ 2) else 0) +
      4 * (∑ s, ∑ r, ∑ u, ∑ u₂, if symp s r = 1 ∧ inT s r u ∧ inT s r u₂ ∧ u₂ ≠ u then
            cval ψ u * cval ψ u₂ *
              (- Y r u₂ * Y r (s + u + u₂) * Y (r + s) u * Y (r + s) (s + u + u₂)
               - Y (r + s) u₂ * Y (r + s) (s + u + u₂) * Y r u * Y r (s + u + u₂)) else 0) := by
    simp only [S_A, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hsr : symp s r = 1
    · rw [if_pos hsr, hQ_sq s r hsr]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      by_cases h : inT s r u ∧ inT s r v ∧ v ≠ u
      · have hsr' : symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u := ⟨hsr, h⟩
        rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos hsr', if_pos hsr', if_pos hsr', if_pos hsr']
      · have hsr' : ¬ (symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u) := fun h' => h h'.2
        rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg hsr', if_neg hsr', if_neg hsr', if_neg hsr']
    · rw [if_neg hsr]
      symm; refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      have hsr' : ¬ (symp s r = 1 ∧ inT s r u ∧ inT s r v ∧ v ≠ u) := fun h => hsr h.1
      rw [if_neg hsr', if_neg hsr', if_neg hsr', if_neg hsr']; ring
  have hP1 := sos_A_P1 hunit
  have hP2 := sos_A_P2 hunit
  have hP3 := sos_A_P3 hunit
  have hP4 := sos_A_P4 hunit
  rw [hSA_split, hP1, hP2, hP3, hP4] at hnn
  linarith

end TwoQubit

end TwoQubitSOS

/-! ### Step 7: Main Theorem `F₂(|ψ⟩) ≥ 12/7` -/

/-- **Exact Degree-6 Rational SOS Lower Bound for Two-Qubit Pure States**:
    For EVERY 2-qubit unit pure state `|ψ⟩ ∈ (ℂ²)⊗²`,
      `pauliMoment4 2 ψ ≥ 12 / 7` (`≈ 1.714286`, exact global optimum of the degree-6
      Clifford-invariant SOS hierarchy, vs. Welch `8 / 5 = 1.600` and MUB fiducial `7 / 4 = 1.750`). -/
theorem pauliMoment4_two_ge_twelve_sevenths (ψ : QState 2) (hunit : IsUnitState ψ) :
    (12 / 7 : ℝ) ≤ pauliMoment4 2 ψ := by
  have hA := TwoQubitSOS.sos_A_nonneg hunit
  have hB := TwoQubitSOS.sos_B_nonneg hunit
  have hC := TwoQubitSOS.sos_C_nonneg hunit
  have hF4 := TwoQubitSOS.F4_eq_pauliMoment4 (ψ := ψ)
  linarith

end MultiQubitMUB
