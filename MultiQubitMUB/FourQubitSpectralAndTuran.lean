import Mathlib.Analysis.Matrix.Spectrum
import MultiQubitMUB.GeneralLowerBound

/-!
# 4-Qubit Spectral, Self-Duality, and Symplectic Turán Infrastructure

Establishes the complete analytic and combinatorial engine behind the theorem
`CD(W(7,2)) ≥ 1575 → F₄(|ψ⟩) > 31/16` (zero `sorry`, zero `native_decide`,
standard three axioms `[propext, Classical.choice, Quot.sound]` only):

1. **Unified 16×16 Hermitian Spectral Bound (`hermitian_max_eig_le_of_trace_bounds`)**:
   - `pauli_L1_le_of_contextuality_1575`: `∑_{p≠0} |c_p| ≤ 601919 / 10000`.
   - `pauli_Lout_le_of_contextuality_1575`: for EVERY Lagrangian `L`,
     `∑_{p ∉ L} |c_p| ≤ 594918 / 10000` (via 10-line character averaging `Tr(S_out³) ≤ 208320`).
2. **Global Polynomial, Coset-Deficit, Quartic MUB, Self-Dual Pythagoras, and 2D Bessel Bounds**:
   - `sum_h_le` (`≤ 1919 / 320000`) and `sum_w_ge` (`≥ 388592 / 30000`) under `F₄ ≤ 31/16`.
   - `val_B_le_excess`, `val_D_le_excess`, `val_A_le_excess`.
   - Pure-polynomial SOS contradictions `smax_k0_contra` (`0.0848`), `smax_k1_contra` (`0.0470`),
     and `smax_k2_contra` (`0.0190`).
   - Exact integer-coefficient 2D Bessel bound:
     `255 * W_anti(w) ≤ 120 * (17 S_{2w} + S₁² - 2 S₁ - 16) - (17 M - S₁ - 16)²`.
3. **Unified Symplectic Turán Theory on `𝔽₂⁸` (`symp_turan_14` .. `symp_turan_18`)**:
   - All five Turán thresholds (`A(Z₁₄) < 16`, `A(Z₁₅) < 20`, `A(Z₁₆) < 24`,
     `A(Z₁₇) < 28`, `A(Z₁₈) < 32`) plus the exact weighted 15-mask anticommutation lower bound
     `W_anti(w) ≥ 2 (1 + W_out)(5 + W_in)` via isotropic-radical induction (`r = 3 → 2 → 1 → 0`).
-/

namespace MultiQubitMUB

namespace FourQubitMUB

open scoped Classical
open Matrix

/-! ### Section 1: Unified 16×16 Hermitian Spectral Bound (`L₁` and `L_out`) -/

/-- Exact 15-variable trace-cubic lower bound: if `∑_{i=1}^{15} μ_i = 0` and `∑ μ_i² = R²`,
    then `∑ μ_i³ ≥ -(13 / √210) * R³`. -/
lemma sum_cube_ge_of_sum_zero_15 {ι : Type*} (s : Finset ι) (hs : s.card = 15) (μ : ι → ℝ)
    (h1 : ∑ i ∈ s, μ i = 0) {R : ℝ} (hR_nn : 0 ≤ R) (h2 : ∑ i ∈ s, (μ i) ^ 2 = R ^ 2) :
    -(13 / Real.sqrt 210) * R ^ 3 ≤ ∑ i ∈ s, (μ i) ^ 3 := by
  by_cases hR0 : R = 0
  · subst hR0
    have hzero : ∀ i ∈ s, μ i = 0 := fun i hi => by
      have hsq0 : (μ i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (μ j)).mp (by simpa using h2) i hi
      exact sq_eq_zero_iff.mp hsq0
    have h3 : ∑ i ∈ s, (μ i) ^ 3 = 0 := Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; norm_num
    rw [h3]; norm_num
  · have hR_pos : 0 < R := lt_of_le_of_ne hR_nn (Ne.symm hR0)
    have hs210_pos : 0 < Real.sqrt 210 := Real.sqrt_pos.mpr (by norm_num)
    have hs210_sq : Real.sqrt 210 ^ 2 = 210 := Real.sq_sqrt (by norm_num)
    let t : ℝ := R / Real.sqrt 210
    have ht_pos : 0 < t := div_pos hR_pos hs210_pos
    have ht_sq : 210 * t ^ 2 = R ^ 2 := by
      simp only [t, div_pow, hs210_sq]; field_simp
    have hge : ∀ k ∈ s, 0 ≤ μ k + 14 * t := by
      intro k hk
      have hcard_e : ((s.erase k).card : ℝ) = 14 := by
        rw [Finset.card_erase_of_mem hk, hs]; norm_num
      have hsum_e : ∑ j ∈ s.erase k, μ j = -μ k := by
        have := Finset.add_sum_erase s μ hk; linarith
      have hsq_e : ∑ j ∈ s.erase k, (μ j) ^ 2 = R ^ 2 - (μ k) ^ 2 := by
        have := Finset.add_sum_erase s (fun j => (μ j) ^ 2) hk; linarith
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s.erase k) (fun _ => (1 : ℝ)) μ
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard_e, hsum_e,
        hsq_e, neg_sq] at hcs
      have h15 : 15 * (μ k) ^ 2 ≤ 14 * R ^ 2 := by linarith
      have h14t_sq : (14 * t) ^ 2 = (14 / 15 : ℝ) * R ^ 2 := by nlinarith [ht_sq]
      have hmu_sq : (μ k) ^ 2 ≤ (14 * t) ^ 2 := by nlinarith [h15, h14t_sq]
      nlinarith [ht_pos]
    have hpt : ∀ i ∈ s, 0 ≤ (μ i) ^ 3 + 12 * t * (μ i) ^ 2 - 27 * t ^ 2 * μ i + 14 * t ^ 3 := by
      intro i hi
      have hfac : (μ i) ^ 3 + 12 * t * (μ i) ^ 2 - 27 * t ^ 2 * μ i + 14 * t ^ 3 =
          (μ i + 14 * t) * (μ i - t) ^ 2 := by ring
      rw [hfac]
      exact mul_nonneg (hge i hi) (sq_nonneg _)
    have hsum := Finset.sum_nonneg hpt
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, hs, nsmul_eq_mul, h1, h2] at hsum
    have h13 : 12 * t * R ^ 2 + (15 : ℝ) * (14 * t ^ 3) = (13 / Real.sqrt 210) * R ^ 3 := by
      have h210 : (15 : ℝ) * (14 * t ^ 3) = t * (210 * t ^ 2) := by ring
      rw [h210, ht_sq]; simp only [t]; ring
    push_cast at hsum; linarith

/-- **Unified 16×16 Hermitian Spectral Bound**:
    If Hermitian `A : QMat 4` has `Tr(A) = 0`, `Tr(A²).re = T₂`, `Tr(A³).re ≤ T₃`, and `lam0 > 0`
    satisfies `(16 / 15) * lam0² ≤ T₂ ≤ 16 * lam0²` and
    `T₃ < (224 / 225) * lam0³ - (lam0 / 5) * (T₂ - (16/15) lam0²) - (13 / √210) * (T₂ - (16/15) lam0²)^(3/2)`,
    then for EVERY unit state `ψ : QState 4`, `(innerProd ψ (matApply A ψ)).re ≤ lam0`. -/
lemma hermitian_max_eig_le_of_trace_bounds {A : QMat 4} (hAh : IsHermMat A)
    {T2 T3 lam0 : ℝ} (hlam0_pos : 0 < lam0)
    (htr1 : matTr A = 0)
    (htr2 : (matTr (matMul A A)).re = T2)
    (htr3 : (matTr (matMul A (matMul A A))).re ≤ T3)
    (_hdom : (16 / 15 : ℝ) * lam0 ^ 2 ≤ T2)
    (hT2_le : T2 ≤ 16 * lam0 ^ 2)
    (hstrict : T3 < (224 / 225 : ℝ) * lam0 ^ 3 - (lam0 / 5) * (T2 - (16 / 15) * lam0 ^ 2) -
      (13 / Real.sqrt 210) * Real.sqrt (T2 - (16 / 15) * lam0 ^ 2) ^ 3)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    (innerProd ψ (matApply A ψ)).re ≤ lam0 := by
  let M : Matrix (F2 4) (F2 4) ℂ := A
  have hMh : M.IsHermitian := by
    ext x y; change star (A y x) = A x y; rw [hAh x y, star_star]
  let e : F2 4 → ℝ := hMh.eigenvalues
  let U : Matrix (F2 4) (F2 4) ℂ := hMh.eigenvectorUnitary
  let D : Matrix (F2 4) (F2 4) ℂ := Matrix.diagonal (fun i => (e i : ℂ))
  have hU_mul_star : U * star U = 1 := Unitary.coe_mul_star_self hMh.eigenvectorUnitary
  have hstar_mul_U : star U * U = 1 := Unitary.coe_star_mul_self hMh.eigenvectorUnitary
  have hspec : M = U * D * star U := by
    have hs := hMh.spectral_theorem
    simpa only [Unitary.conjStarAlgAut_apply, U, D, e, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hs
  have hM2 : M * M = U * (D * D) * star U := by
    rw [hspec]
    calc U * D * star U * (U * D * star U)
        = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [hstar_mul_U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hM3 : M * (M * M) = U * (D * (D * D)) * star U := by
    rw [hM2, hspec]
    calc U * D * star U * (U * (D * D) * star U)
        = U * D * (star U * U) * (D * D) * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * (D * D)) * star U := by rw [hstar_mul_U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have htr_conj : ∀ X : Matrix (F2 4) (F2 4) ℂ, (U * X * star U).trace = X.trace := fun X => by
    rw [Matrix.trace_mul_cycle, hstar_mul_U, Matrix.one_mul]
  have he1 : ∑ i : F2 4, e i = 0 := by
    have h := htr1
    rw [show matTr A = M.trace from rfl, hspec, htr_conj, Matrix.trace_diagonal] at h
    have hre := congr_arg Complex.re h
    simpa [Complex.re_sum] using hre
  have he2 : ∑ i : F2 4, (e i) ^ 2 = T2 := by
    have h := htr2
    rw [show matMul A A = M * M from rfl, show matTr (M * M) = (M * M).trace from rfl,
        hM2, htr_conj, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at h
    rw [← h, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => by simp [sq]
  have he3 : ∑ i : F2 4, (e i) ^ 3 ≤ T3 := by
    have h := htr3
    rw [show matMul A (matMul A A) = M * (M * M) from rfl,
        show matTr (M * (M * M)) = (M * (M * M)).trace from rfl,
        hM3, htr_conj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal] at h
    have hsum : (∑ i : F2 4, (e i : ℂ) * ((e i : ℂ) * (e i : ℂ))).re = ∑ i : F2 4, (e i) ^ 3 := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
    linarith
  have he_le : ∀ i : F2 4, e i ≤ lam0 := by
    intro i0
    by_contra hgt; push Not at hgt
    let s := (Finset.univ : Finset (F2 4)).erase i0
    have hs_card : s.card = 15 := by
      simp only [s, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]; norm_num
    let l : ℝ := e i0
    have hl_pos : 0 < l := lt_trans hlam0_pos hgt
    let μ : F2 4 → ℝ := fun j => e j + l / 15
    have hμ1 : ∑ j ∈ s, μ j = 0 := by
      have hsum_e : ∑ j ∈ s, e j = -l := by
        have := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i0); linarith
      simp only [μ, Finset.sum_add_distrib, Finset.sum_const, hs_card, nsmul_eq_mul, hsum_e]
      push_cast; ring
    have hμ2 : ∑ j ∈ s, (μ j) ^ 2 = T2 - (16 / 15 : ℝ) * l ^ 2 := by
      have hsum_e : ∑ j ∈ s, e j = -l := by
        have := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i0); linarith
      have hsum_e2 : ∑ j ∈ s, (e j) ^ 2 = T2 - l ^ 2 := by
        have := Finset.add_sum_erase Finset.univ (fun j => (e j) ^ 2) (Finset.mem_univ i0); linarith
      have hexp : ∑ j ∈ s, (μ j) ^ 2 =
          (∑ j ∈ s, (e j) ^ 2) + (2 * l / 15) * (∑ j ∈ s, e j) + (s.card : ℝ) * (l / 15) ^ 2 := by
        have : ∀ j, (μ j) ^ 2 = (e j) ^ 2 + (2 * l / 15) * e j + (l / 15) ^ 2 := fun j => by
          simp only [μ]; ring
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      rw [hexp, hsum_e, hsum_e2, hs_card]; push_cast; ring
    have hR2_nn : 0 ≤ T2 - (16 / 15 : ℝ) * l ^ 2 := by
      rw [← hμ2]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    let R : ℝ := Real.sqrt (T2 - (16 / 15 : ℝ) * l ^ 2)
    have hR_sq : R ^ 2 = T2 - (16 / 15 : ℝ) * l ^ 2 := Real.sq_sqrt hR2_nn
    have hμ3 := sum_cube_ge_of_sum_zero_15 s hs_card μ hμ1 (Real.sqrt_nonneg _) (by rw [hμ2, hR_sq])
    have he3_eq : ∑ i : F2 4, (e i) ^ 3 =
        (224 / 225 : ℝ) * l ^ 3 - (l / 5) * R ^ 2 + ∑ j ∈ s, (μ j) ^ 3 := by
      rw [← Finset.add_sum_erase Finset.univ (fun i => (e i) ^ 3) (Finset.mem_univ i0)]
      have hterm : ∀ j ∈ s, (e j) ^ 3 =
          (μ j) ^ 3 - (l / 5) * (μ j) ^ 2 + (l ^ 2 / 75) * μ j - (l / 15) ^ 3 := fun j _ => by
        simp only [μ]; ring
      change e i0 ^ 3 + ∑ j ∈ s, (e j) ^ 3 = _
      rw [Finset.sum_congr rfl hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, hs_card, nsmul_eq_mul, hμ1, hμ2, ← hR_sq]
      push_cast; simp only [l]; ring
    have hl_bound : (224 / 225 : ℝ) * l ^ 3 - (l / 5) * R ^ 2 - (13 / Real.sqrt 210) * R ^ 3 ≤ T3 := by
      linarith
    let R0 : ℝ := Real.sqrt (T2 - (16 / 15 : ℝ) * lam0 ^ 2)
    have hR_le : R ≤ R0 := Real.sqrt_le_sqrt (by nlinarith)
    have hR3_le : R ^ 3 ≤ R0 ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hR_le 3
    have h13_pos : 0 < 13 / Real.sqrt 210 := by positivity
    have hpoly_inc : (224 / 225 : ℝ) * lam0 ^ 3 - (lam0 / 5) * (T2 - (16 / 15) * lam0 ^ 2) ≤
        (224 / 225 : ℝ) * l ^ 3 - (l / 5) * R ^ 2 := by
      rw [hR_sq]
      have hdiff : ((224 / 225 : ℝ) * l ^ 3 - (l / 5) * (T2 - (16 / 15) * l ^ 2)) -
          ((224 / 225 : ℝ) * lam0 ^ 3 - (lam0 / 5) * (T2 - (16 / 15) * lam0 ^ 2)) =
          (l - lam0) * ((272 / 225 : ℝ) * (l ^ 2 + l * lam0 + lam0 ^ 2) - T2 / 5) := by ring
      have hfac_pos : 0 ≤ (272 / 225 : ℝ) * (l ^ 2 + l * lam0 + lam0 ^ 2) - T2 / 5 := by
        nlinarith [hT2_le, hgt, hlam0_pos]
      have hmul : 0 ≤ (l - lam0) * ((272 / 225 : ℝ) * (l ^ 2 + l * lam0 + lam0 ^ 2) - T2 / 5) :=
        mul_nonneg (by linarith) hfac_pos
      linarith
    have h13_le : (13 / Real.sqrt 210) * R ^ 3 ≤ (13 / Real.sqrt 210) * R0 ^ 3 :=
      mul_le_mul_of_nonneg_left hR3_le (le_of_lt h13_pos)
    linarith
  let φ : QState 4 := star U *ᵥ ψ
  have hφ_norm : ∑ i : F2 4, Complex.normSq (φ i) = 1 := by
    have h1 : innerProd φ φ = innerProd ψ ψ := by
      have hdot : ∀ u v : F2 4 → ℂ, innerProd u v = dotProduct (star u) v := fun _ _ => rfl
      rw [hdot, hdot]
      simp only [φ, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose, star_star,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU_mul_star, Matrix.vecMul_one]
    rw [← innerProd_self_re, h1, hunit, Complex.one_re]
  have hray : innerProd ψ (matApply A ψ) = ∑ i : F2 4, (e i : ℂ) * (Complex.normSq (φ i) : ℂ) := by
    have hmat : matApply A ψ = M *ᵥ ψ := rfl
    rw [hmat, hspec]
    have hdot : ∀ u v : F2 4 → ℂ, innerProd u v = dotProduct (star u) v := fun _ _ => rfl
    rw [hdot]
    have hstep : dotProduct (star ψ) ((U * D * star U) *ᵥ ψ) = dotProduct (star φ) (D *ᵥ φ) := by
      have h1 : (U * D * star U) *ᵥ ψ = U *ᵥ (D *ᵥ φ) := by
        simp only [φ, Matrix.mul_assoc, Matrix.mulVec_mulVec]
      have h2 : star φ = star ψ ᵥ* U := by
        simp only [φ, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
      rw [h1, Matrix.dotProduct_mulVec, h2]
    rw [hstep]
    simp only [dotProduct, D, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc star (φ i) * ((e i : ℂ) * φ i)
        = (e i : ℂ) * (φ i * star (φ i)) := by ring
      _ = (e i : ℂ) * (Complex.normSq (φ i) : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
  rw [hray, Complex.re_sum]
  have hre : ∀ i : F2 4, ((e i : ℂ) * (Complex.normSq (φ i) : ℂ)).re = e i * Complex.normSq (φ i) := by
    intro i; rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hre]
  calc ∑ i : F2 4, e i * Complex.normSq (φ i)
      ≤ ∑ i : F2 4, lam0 * Complex.normSq (φ i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (he_le i) (Complex.normSq_nonneg _)
    _ = lam0 * ∑ i : F2 4, Complex.normSq (φ i) := (Finset.mul_sum _ _ _).symm
    _ = lam0 := by rw [hφ_norm, mul_one]

/-- Helper: expectation of `pauliExpand a` on `ψ`. -/
lemma innerProd_pauliExpand_re {n : ℕ} (a : PauliIdx n → ℝ) (ψ : QState n) :
    (innerProd ψ (matApply (pauliExpand a) ψ)).re =
      ∑ p : PauliIdx n, a p * (innerProd ψ (pauliApply p ψ)).re := by
  have happ : matApply (pauliExpand a) ψ = ∑ p : PauliIdx n, (a p : ℂ) • pauliApply p ψ := by
    ext x
    simp only [matApply, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, ← pauliMat_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [happ, innerProd_sum_right, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_lhs => rw [innerProd_smul_right, ← innerProd_pauliApply_self_real p ψ]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Helper: trace of the cube of `pauliExpand σ` (when `σ 0 = 0`) equals `32 * signCubeSum 4 σ`. -/
lemma matTr_cube_pauliExpand_four (σ : PauliIdx 4 → ℝ) (hσ0 : σ 0 = 0) :
    (matTr (matMul (pauliExpand σ) (matMul (pauliExpand σ) (pauliExpand σ)))).re =
      32 * signCubeSum 4 σ := by
  rw [matMul_pauliExpand_self, matTr_pauliExpand_mul]
  have h16 : ((2 : ℂ) ^ 4) = ((16 : ℝ) : ℂ) := by norm_num
  rw [h16, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4)), hσ0, zero_mul, zero_add]
  simp only [signCubeSum]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
  have hinner : ∑ p : PauliIdx 4, (pauliPhase q p).re * σ p * σ (q + p) =
      ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 4)).erase q, (pauliPhase q p).re * σ p * σ (q + p) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4)),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hq0, Finset.mem_univ q⟩),
        hσ0, pauliIdx_add_self, hσ0]
    ring
  rw [hinner]; ring

/-- **Spectral `L₁` Bound (`pauli_L1_le_of_contextuality_1575`)**:
    Under `CD(W(7,2)) ≥ 1575` (`∀ σ ∈ {±1}^{𝔽₂⁸\{0}}, signCubeSum 4 σ ≤ 6615`),
    every 4-qubit unit pure state satisfies `∑_{p≠0} |c_p| ≤ 601919 / 10000`. -/
theorem pauli_L1_le_of_contextuality_1575
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), |(innerProd ψ (pauliApply p ψ)).re| ≤
      (601919 / 10000 : ℝ) := by
  let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  let σ : PauliIdx 4 → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  have hσ0 : σ 0 = 0 := by simp [σ]
  have hσpm : ∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp
  let S := pauliExpand σ
  have htr1 : matTr S = 0 := by simp [S, matTr_pauliExpand, hσ0]
  have htr2 : (matTr (matMul S S)).re = 4080 := by
    rw [matTr_mul_self_herm (pauliExpand_herm σ), Complex.ofReal_re, frobSq_pauliExpand]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4)), hσ0, zero_pow (by norm_num), zero_add]
    have hsq : ∀ p ∈ Finset.univ.erase (0 : PauliIdx 4), (σ p) ^ 2 = 1 := fun p hp => by
      rcases hσpm p (Finset.mem_erase.mp hp).1 with h | h <;> rw [h] <;> norm_num
    rw [Finset.sum_congr rfl hsq, Finset.sum_const, nsmul_eq_mul, mul_one, card_PauliIdx_erase_zero]
    norm_num
  have htr3 : (matTr (matMul S (matMul S S))).re ≤ 211680 := by
    rw [matTr_cube_pauliExpand_four σ hσ0]
    linarith [hCD σ hσ0 hσpm]
  have h210_lo : (14.49137 : ℝ) < Real.sqrt 210 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hR_hi : Real.sqrt (4080 - (16 / 15 : ℝ) * (601919 / 10000 : ℝ) ^ 2) < (14.67643 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hstrict : (211680 : ℝ) <
      (224 / 225 : ℝ) * (601919 / 10000 : ℝ) ^ 3 -
      ((601919 / 10000 : ℝ) / 5) * (4080 - (16 / 15) * (601919 / 10000 : ℝ) ^ 2) -
      (13 / Real.sqrt 210) * Real.sqrt (4080 - (16 / 15) * (601919 / 10000 : ℝ) ^ 2) ^ 3 := by
    have h1 : 13 / Real.sqrt 210 < 13 / 14.49137 :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) h210_lo
    have h2 : Real.sqrt (4080 - (16 / 15 : ℝ) * (601919 / 10000 : ℝ) ^ 2) ^ 3 < (14.67643 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hR_hi (Real.sqrt_nonneg _) (by norm_num)
    have hprod : (13 / Real.sqrt 210) *
        Real.sqrt (4080 - (16 / 15 : ℝ) * (601919 / 10000 : ℝ) ^ 2) ^ 3 <
        (13 / 14.49137) * (14.67643 : ℝ) ^ 3 :=
      mul_lt_mul'' h1 h2 (by positivity) (by positivity)
    have hnum : (211680 : ℝ) <
        (224 / 225 : ℝ) * (601919 / 10000 : ℝ) ^ 3 -
        ((601919 / 10000 : ℝ) / 5) * (4080 - (16 / 15) * (601919 / 10000 : ℝ) ^ 2) -
        (13 / 14.49137) * (14.67643 : ℝ) ^ 3 := by norm_num
    linarith
  have hspec := hermitian_max_eig_le_of_trace_bounds (pauliExpand_herm σ) (by norm_num)
    htr1 htr2 htr3 (by norm_num) (by norm_num) hstrict hunit
  rw [innerProd_pauliExpand_re, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4)),
      hσ0, zero_mul, zero_add] at hspec
  have heq : ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), σ p * c p =
      ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), |c p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
    simp only [σ, hp0, ↓reduceIte]
    by_cases hcp : 0 ≤ c p
    · simp only [hcp, ↓reduceIte, one_mul, abs_of_nonneg hcp]
    · simp only [hcp, ↓reduceIte, neg_mul, one_mul, abs_of_neg (not_le.mp hcp)]
  rwa [heq] at hspec

/-! ### Section 1b: Isotropic Subspaces, Lagrangians, Consistent Characters, and `L_out` Bound -/

/-- `r`-dimensional isotropic subspace `R ⊆ 𝔽₂⁸` (represented as a `Finset (PauliIdx 4)`). -/
def IsIsoSub (r : ℕ) (R : Finset (PauliIdx 4)) : Prop :=
  (0 : PauliIdx 4) ∈ R ∧ R.card = 2 ^ r ∧
  (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) ∧ (∀ x ∈ R, ∀ y ∈ R, symp x y = 0)

/-- Lagrangian (`4`-dimensional maximal isotropic subspace of `𝔽₂⁸`, size `16`). -/
abbrev IsLagrangian (L : Finset (PauliIdx 4)) : Prop := IsIsoSub 4 L

/-- Symplectic character sum over all of `PauliIdx n`. -/
lemma sum_sympSign_all {n : ℕ} (y : PauliIdx n) :
    ∑ x : PauliIdx n, (sympSign x y : ℝ) = if y = 0 then (4 : ℝ) ^ n else 0 := by
  have h1 : ∀ x : PauliIdx n, (sympSign x y : ℝ) = ((chi x.1 y.2 * chi x.2 y.1 : ℤ) : ℝ) := fun x => by
    have hZ : sympSign x y = chi x.1 y.2 * chi x.2 y.1 := by
      simp only [sympSign, symp, chi]
      rcases zmod2_cases (dot x.1 y.2) with h1 | h1 <;> rcases zmod2_cases (dot x.2 y.1) with h2 | h2
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]; decide
    exact_mod_cast hZ
  simp_rw [h1, Int.cast_mul, Fintype.sum_prod_type]
  have hfact : (∑ a : F2 n, ∑ b : F2 n, (chi a y.2 : ℝ) * (chi b y.1 : ℝ)) =
      (∑ a : F2 n, (chi a y.2 : ℝ)) * (∑ b : F2 n, (chi b y.1 : ℝ)) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum]
  rw [hfact]
  have hc1 : (∑ a : F2 n, (chi a y.2 : ℝ)) = if y.2 = 0 then (2 : ℝ) ^ n else 0 := by
    rw [← Int.cast_sum, sum_chi]; split_ifs <;> simp
  have hc2 : (∑ b : F2 n, (chi b y.1 : ℝ)) = if y.1 = 0 then (2 : ℝ) ^ n else 0 := by
    rw [← Int.cast_sum, sum_chi]; split_ifs <;> simp
  rw [hc1, hc2]
  by_cases hy : y = 0
  · subst hy; simp only [Prod.fst_zero, Prod.snd_zero, ↓reduceIte]
    rw [← mul_pow]; norm_num
  · have hne : y.1 ≠ 0 ∨ y.2 ≠ 0 := by
      by_contra h; push Not at h; exact hy (Prod.ext h.1 h.2)
    rcases hne with h | h <;> simp [hy, h]

/-- Symplectic character sum over an isotropic subspace `R`. -/
lemma sum_sympSign_isoSub {r : ℕ} {R : Finset (PauliIdx 4)} (hR : IsIsoSub r R) (x : PauliIdx 4) :
    ∑ y ∈ R, (sympSign x y : ℝ) = if ∀ y ∈ R, symp x y = 0 then (2 : ℝ) ^ r else 0 := by
  split_ifs with hx
  · have h1 : ∀ y ∈ R, (sympSign x y : ℝ) = 1 := fun y hy => by simp [sympSign, hx y hy]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, hR.2.1, nsmul_eq_mul, mul_one]; norm_cast
  · 
    push Not at hx
    obtain ⟨y0, hy0R, hy0ne⟩ := hx
    have hy01 : symp x y0 = 1 := (zmod2_cases _).resolve_left hy0ne
    have hneg : ∑ y ∈ R, (sympSign x y : ℝ) = -(∑ y ∈ R, (sympSign x y : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun y _ => y + y0) ?_ ?_ ?_ ?_
      · intro y hy; exact hR.2.2.1 y hy y0 hy0R
      · intro a _ b _ h; have := congr_arg (· + y0) h; simpa [pauliIdx_add_cancel_right] using this
      · intro y hy; exact ⟨y + y0, hR.2.2.1 y hy y0 hy0R, pauliIdx_add_cancel_right y y0⟩
      · intro y _
        rw [sympSign_add_right]
        have hs : sympSign x y0 = -1 := by simp [sympSign, hy01]
        rw [hs]; push_cast; ring
    linarith

/-- Exact cardinality `|R^⊥| = 2^(8 - r)` and dimension bound `r ≤ 4` for any isotropic `R`. -/
lemma isoSub_perp_card {r : ℕ} {R : Finset (PauliIdx 4)} (hR : IsIsoSub r R) :
    r ≤ 4 ∧ (Finset.univ.filter fun x : PauliIdx 4 => ∀ y ∈ R, symp x y = 0).card * 2 ^ r = 256 := by
  let Rp := Finset.univ.filter fun x : PauliIdx 4 => ∀ y ∈ R, symp x y = 0
  have hsum : (∑ x : PauliIdx 4, ∑ y ∈ R, (sympSign x y : ℝ)) = 256 := by
    rw [Finset.sum_comm]
    have h0 := hR.1
    rw [← Finset.add_sum_erase _ _ h0, sum_sympSign_all]
    simp only [↓reduceIte]
    have hrest : ∑ y ∈ R.erase 0, ∑ x : PauliIdx 4, (sympSign x y : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [sum_sympSign_all]; simp [(Finset.mem_erase.mp hy).1]
    rw [hrest, add_zero]; norm_num
  have hsum2 : (∑ x : PauliIdx 4, ∑ y ∈ R, (sympSign x y : ℝ)) = (Rp.card : ℝ) * (2 : ℝ) ^ r := by
    simp_rw [sum_sympSign_isoSub hR]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hnat : Rp.card * 2 ^ r = 256 := by
    have hR_eq : ((Rp.card * 2 ^ r : ℕ) : ℝ) = (256 : ℝ) := by push_cast; linarith
    exact_mod_cast hR_eq
  have hsub : R ⊆ Rp := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => hR.2.2.2 x hx y hy⟩
  have hle : 2 ^ r ≤ Rp.card := by rw [← hR.2.1]; exact Finset.card_le_card hsub
  have hsq : 2 ^ r * 2 ^ r ≤ 256 := by
    calc 2 ^ r * 2 ^ r ≤ Rp.card * 2 ^ r := Nat.mul_le_mul_right _ hle
      _ = 256 := hnat
  have hr4 : r ≤ 4 := by
    by_contra h; push Not at h
    have h5 : 2 ^ 5 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
    have : 32 * 32 ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul h5 h5
    omega
  exact ⟨hr4, hnat⟩

/-- Extending an `r`-dim isotropic subspace `R` by any commuting `u ∉ R` gives an `(r+1)`-dim isotropic subspace. -/
lemma isoSub_extend_step {r : ℕ} {R : Finset (PauliIdx 4)} (hR : IsIsoSub r R)
    {u : PauliIdx 4} (huR : u ∉ R) (hcomm : ∀ x ∈ R, symp u x = 0) :
    IsIsoSub (r + 1) (R ∪ R.image (u + ·)) := by
  have hdisj : Disjoint R (R.image (u + ·)) := by
    rw [Finset.disjoint_left]
    intro z hzR hzI
    obtain ⟨x, hxR, rfl⟩ := Finset.mem_image.mp hzI
    have hu : u = (u + x) + x := (pauliIdx_add_cancel_right u x).symm
    exact huR (hu ▸ hR.2.2.1 _ hzR _ hxR)
  have hinj : Function.Injective (fun x : PauliIdx 4 => u + x) := fun a b h => by
    have := congr_arg (u + ·) h; simpa [pauliIdx_add_cancel_left] using this
  refine ⟨Finset.mem_union_left _ hR.1, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, hR.2.1, pow_succ]
    ring
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_left _ (hR.2.2.1 x hx y hy)
    · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x + y', hR.2.2.1 x hx y' hy', ?_⟩)
      abel
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x' + y, hR.2.2.1 x' hx' y hy, ?_⟩)
      abel
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      have heq : (u + x') + (u + y') = x' + y' := by
        calc (u + x') + (u + y') = (u + u) + (x' + y') := by abel
          _ = x' + y' := by rw [pauliIdx_add_self, zero_add]
      rw [heq]; exact Finset.mem_union_left _ (hR.2.2.1 x' hx' y' hy')
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact hR.2.2.2 x hx y hy
    · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      rw [symp_add_right, symp_comm x u, hcomm x hx, hR.2.2.2 x hx y' hy', add_zero]
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      rw [symp_add_left, hcomm y hy, hR.2.2.2 x' hx' y hy, zero_add]
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      rw [symp_add_left, symp_add_right, symp_add_right, symp_self, hcomm y' hy',
          symp_comm x' u, hcomm x' hx', hR.2.2.2 x' hx' y' hy']; simp

/-- Every `r`-dim isotropic subspace extends to a Lagrangian `L ⊇ R`. -/
lemma isoSub_extends_to_lagrangian :
    ∀ (k r : ℕ) (R : Finset (PauliIdx 4)), IsIsoSub r R → r + k = 4 →
      ∃ L : Finset (PauliIdx 4), IsLagrangian L ∧ R ⊆ L
  | 0, r, R, hR, hk => by
    have hr : r = 4 := by omega
    subst hr; exact ⟨R, hR, Finset.Subset.refl _⟩
  | k + 1, r, R, hR, hk => by
    let Rp := Finset.univ.filter fun x : PauliIdx 4 => ∀ y ∈ R, symp x y = 0
    have hcard := (isoSub_perp_card hR).2
    have hlt : R.card < Rp.card := by
      have h1 : R.card = 2 ^ r := hR.2.1
      have h2 : 2 ^ r * 2 ^ r < 256 := by
        have hr3 : r ≤ 3 := by omega
        have hp : 2 ^ r ≤ 8 := Nat.pow_le_pow_right (by norm_num) hr3
        nlinarith
      nlinarith
    have hne : (Rp \ R).Nonempty := Finset.sdiff_nonempty.mpr fun hsub =>
      not_le_of_gt hlt (Finset.card_le_card hsub)
    obtain ⟨u, hu⟩ := hne
    have huRp := (Finset.mem_sdiff.mp hu).1
    have huR := (Finset.mem_sdiff.mp hu).2
    have hcomm : ∀ x ∈ R, symp u x = 0 := (Finset.mem_filter.mp huRp).2
    have hR' := isoSub_extend_step hR huR hcomm
    obtain ⟨L, hL, hsub⟩ := isoSub_extends_to_lagrangian k (r + 1) _ hR' (by omega)
    exact ⟨L, hL, Finset.Subset.trans Finset.subset_union_left hsub⟩

/-- Clean version with span-orthogonality invariant: every isotropic `S` lies in a Lagrangian `L`. -/
lemma exists_lagrangian_superset (S : Finset (PauliIdx 4))
    (hS : ∀ x ∈ S, ∀ y ∈ S, symp x y = 0) :
    ∃ L : Finset (PauliIdx 4), IsLagrangian L ∧ S ⊆ L := by
  have hspan : ∀ (T : Finset (PauliIdx 4)), (∀ x ∈ T, ∀ y ∈ T, symp x y = 0) →
      ∃ r R, IsIsoSub r R ∧ T ⊆ R ∧
        (∀ u : PauliIdx 4, (∀ x ∈ T, symp u x = 0) → ∀ y ∈ R, symp u y = 0) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨0, {0}, ⟨Finset.mem_singleton_self 0, by simp, ?_, ?_⟩, Finset.empty_subset _, ?_⟩
      · intro x hx y hy; simp only [Finset.mem_singleton] at hx hy; simp [hx, hy]
      · intro x hx y hy; simp only [Finset.mem_singleton] at hx hy; simp [hx, hy, symp_self]
      · intro u _ y hy; simp only [Finset.mem_singleton] at hy; rw [hy, symp_zero_right]
    | insert a s ha ih =>
      intro hT
      have hs : ∀ x ∈ s, ∀ y ∈ s, symp x y = 0 := fun x hx y hy =>
        hT x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
      obtain ⟨r, R, hR, hsR, hR_orth⟩ := ih hs
      by_cases haR : a ∈ R
      · refine ⟨r, R, hR, Finset.insert_subset_iff.mpr ⟨haR, hsR⟩, fun u hu y hy =>
          hR_orth u (fun x hx => hu x (Finset.mem_insert_of_mem hx)) y hy⟩
      · have hacomm : ∀ y ∈ R, symp a y = 0 :=
          hR_orth a fun x hx => hT a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
        refine ⟨r + 1, R ∪ R.image (a + ·), isoSub_extend_step hR haR hacomm, ?_, ?_⟩
        · refine Finset.insert_subset_iff.mpr ⟨?_, Finset.Subset.trans hsR Finset.subset_union_left⟩
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0, hR.1, by simp⟩)
        · intro u hu y hy
          have hua : symp u a = 0 := hu a (Finset.mem_insert_self a s)
          have huR : ∀ z ∈ R, symp u z = 0 := hR_orth u fun x hx => hu x (Finset.mem_insert_of_mem hx)
          rcases Finset.mem_union.mp hy with hy | hy
          · exact huR y hy
          · obtain ⟨z, hzR, rfl⟩ := Finset.mem_image.mp hy
            rw [symp_add_right, hua, huR z hzR, add_zero]
  obtain ⟨r, R, hR, hSR, _⟩ := hspan S hS
  have hr4 := (isoSub_perp_card hR).1
  obtain ⟨L, hL, hRL⟩ := isoSub_extends_to_lagrangian (4 - r) r R hR (by omega)
  exact ⟨L, hL, Finset.Subset.trans hSR hRL⟩

/-- For any Lagrangian `L`, `L^⊥ = L`, and every `u ∉ L` anticommutes with EXACTLY `8` elements of `L`. -/
lemma lagrangian_perp_eq_and_card_anticomm {L : Finset (PauliIdx 4)} (hL : IsLagrangian L) :
    (∀ u : PauliIdx 4, (∀ p ∈ L, symp u p = 0) ↔ u ∈ L) ∧
    (∀ u : PauliIdx 4, u ∉ L → (L.filter fun p => symp u p = 1).card = 8) := by
  let Lp := Finset.univ.filter fun x : PauliIdx 4 => ∀ y ∈ L, symp x y = 0
  have hcard := (isoSub_perp_card hL).2
  have hLp16 : Lp.card = 16 := by change Lp.card * 2 ^ 4 = 256 at hcard; norm_num at hcard; omega
  have hsub : L ⊆ Lp := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => hL.2.2.2 x hx y hy⟩
  have heq : L = Lp := Finset.eq_of_subset_of_card_le hsub (by rw [hLp16, hL.2.1]; norm_num)
  have hiff : ∀ u : PauliIdx 4, (∀ p ∈ L, symp u p = 0) ↔ u ∈ L := fun u => by
    conv_rhs => rw [heq]
    simp [Lp]
  refine ⟨hiff, fun u hu => ?_⟩
  have hnot : ¬(∀ p ∈ L, symp u p = 0) := fun h => hu ((hiff u).mp h)
  have hsum : ∑ y ∈ L, (sympSign u y : ℝ) = 0 := by
    have hs := sum_sympSign_isoSub hL u
    split_ifs at hs
    exact hs
  let L0 := L.filter fun p => symp u p = 0
  let L1 := L.filter fun p => symp u p = 1
  have hsplit : ∑ p ∈ L, (sympSign u p : ℝ) = (L0.card : ℝ) - (L1.card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not L (fun p => symp u p = 0)]
    have hL1eq : L.filter (fun p => ¬symp u p = 0) = L1 := by
      ext p; simp only [L1, Finset.mem_filter]
      exact ⟨fun ⟨hp, hne⟩ => ⟨hp, (zmod2_cases _).resolve_left hne⟩,
             fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
    rw [hL1eq]
    have hs0 : ∑ p ∈ L0, (sympSign u p : ℝ) = (L0.card : ℝ) := by
      have : ∀ p ∈ L0, (sympSign u p : ℝ) = 1 := fun p hp => by simp [sympSign, (Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs1 : ∑ p ∈ L1, (sympSign u p : ℝ) = -(L1.card : ℝ) := by
      have : ∀ p ∈ L1, (sympSign u p : ℝ) = -1 := fun p hp => by
        simp [sympSign, (Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
    rw [hs0, hs1]; ring
  have htot : L0.card + L1.card = 16 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := L) (p := fun p => symp u p = 0)
    have hL1eq : L.filter (fun p => ¬symp u p = 0) = L1 := by
      ext p; simp only [L1, Finset.mem_filter]
      exact ⟨fun ⟨hp, hne⟩ => ⟨hp, (zmod2_cases _).resolve_left hne⟩,
             fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
    rw [hL1eq, hL.2.1] at h1; norm_num at h1; exact h1
  have hdiff : (L0.card : ℝ) = (L1.card : ℝ) := by linarith
  have hnat : L0.card = L1.card := by exact_mod_cast hdiff
  change L1.card = 8; omega

/-- Associativity of `pauliPhase` on `PauliIdx n`. -/
private lemma pauliPhase_assoc_local {n : ℕ} (a b c : PauliIdx n) :
    pauliPhase a b * pauliPhase (a + b) c = pauliPhase b c * pauliPhase a (b + c) := by
  let e0 : QState n := fun x => if x = 0 then 1 else 0
  have h1 : pauliApply a (pauliApply b (pauliApply c e0)) =
      (pauliPhase a b * pauliPhase (a + b) c) • pauliApply (a + b + c) e0 := by
    rw [pauliApply_comp a b _, pauliApply_comp (a + b) c _, smul_smul]
  have h2 : pauliApply a (pauliApply b (pauliApply c e0)) =
      (pauliPhase b c * pauliPhase a (b + c)) • pauliApply (a + b + c) e0 := by
    rw [pauliApply_comp b c e0, pauliApply_smul, pauliApply_comp a (b + c) e0, smul_smul, add_assoc]
  have heq : (pauliPhase a b * pauliPhase (a + b) c) • pauliApply (a + b + c) e0 =
      (pauliPhase b c * pauliPhase a (b + c)) • pauliApply (a + b + c) e0 := h1.symm.trans h2
  have hinn := congr_arg (innerProd (pauliApply (a + b + c) e0)) heq
  rw [innerProd_smul_right, innerProd_smul_right, innerProd_pauliApply_both] at hinn
  have he0 : innerProd e0 e0 = 1 := by
    simp only [innerProd, e0]; rw [Finset.sum_eq_single (0 : F2 n)]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ _) h
  simpa [he0] using hinn

private lemma pauliPhase_re_comm {p q : PauliIdx 4} (hs : symp p q = 0) :
    (pauliPhase p q).re = (pauliPhase q p).re := by
  have h := pauliPhase_comm p q
  simp only [sympSign, hs, ↓reduceIte, Int.cast_one, one_mul] at h
  rw [h]

private lemma pauliPhase_re_assoc {p q t : PauliIdx 4}
    (h1 : symp p q = 0) (h2 : symp (p + q) t = 0)
    (h3 : symp q t = 0) (h4 : symp p (q + t) = 0) :
    (pauliPhase p q).re * (pauliPhase (p + q) t).re =
      (pauliPhase q t).re * (pauliPhase p (q + t)).re := by
  have hre_coe : ∀ u v : PauliIdx 4, symp u v = 0 →
      ((pauliPhase u v).re : ℂ) = pauliPhase u v := fun u v hs => by
    rcases (pauliPhase_re_cases u v).1 hs with h | h <;> simp [h]
  have h := pauliPhase_assoc_local p q t
  rw [← hre_coe p q h1, ← hre_coe (p + q) t h2, ← hre_coe q t h3, ← hre_coe p (q + t) h4] at h
  have hre := congr_arg Complex.re h
  simpa only [← Complex.ofReal_mul, Complex.ofReal_re] using hre

private lemma symp_phase_cocycle_1 {a p y : PauliIdx 4}
    (hpa : symp p a = 0) (hap : symp a p = 0) (hay : symp a y = 0) (hpy : symp p y = 0)
    (hpay : symp (p + a) y = 0) (hapy : symp (a + p) y = 0)
    (hpa_y : symp p (a + y) = 0) (hap_y : symp a (p + y) = 0) :
    (pauliPhase p (a + y)).re * (pauliPhase a y).re =
      (pauliPhase a (p + y)).re * (pauliPhase p y).re := by
  have hass1 := pauliPhase_re_assoc hpa hpay hay hpa_y
  have hass2 := pauliPhase_re_assoc hap hapy hpy hap_y
  have hpa_ap : (pauliPhase p a).re = (pauliPhase a p).re := pauliPhase_re_comm hpa
  rw [add_comm p a] at hass1
  have h1 : (pauliPhase a p).re * ((pauliPhase a (p + y)).re * (pauliPhase p y).re) =
      (pauliPhase a p).re * ((pauliPhase p (a + y)).re * (pauliPhase a y).re) := by
    calc (pauliPhase a p).re * ((pauliPhase a (p + y)).re * (pauliPhase p y).re)
        = (pauliPhase a p).re * ((pauliPhase p y).re * (pauliPhase a (p + y)).re) := by ring
      _ = (pauliPhase a p).re * ((pauliPhase a p).re * (pauliPhase (a + p) y).re) := by rw [← hass2]
      _ = (pauliPhase a p).re * ((pauliPhase p a).re * (pauliPhase (a + p) y).re) := by rw [hpa_ap]
      _ = (pauliPhase a p).re * ((pauliPhase a y).re * (pauliPhase p (a + y)).re) := by rw [hass1]
      _ = _ := by ring
  rcases (pauliPhase_re_cases a p).1 hap with h | h
  · have hre : (pauliPhase a p).re = 1 := by simp [h]
    rw [hre, one_mul, one_mul] at h1; exact h1.symm
  · have hre : (pauliPhase a p).re = -1 := by simp [h]
    rw [hre] at h1; linarith

private lemma symp_phase_cocycle_2 {a x y : PauliIdx 4}
    (hax : symp a x = 0) (hay : symp a y = 0) (hyx : symp y x = 0)
    (hax_ay : symp (a + x) (a + y) = 0) (hx_ay : symp x (a + y) = 0)
    (ha_xay : symp a (x + (a + y)) = 0) (ha_ay : symp a (a + y) = 0)
    (hay_x : symp (a + y) x = 0) (ha_ayx : symp a (a + y + x) = 0) :
    (pauliPhase (a + x) (a + y)).re * (pauliPhase a x).re * (pauliPhase a y).re =
      (pauliPhase x y).re := by
  have hass1 := pauliPhase_re_assoc hax hax_ay hx_ay ha_xay
  have hass2 := pauliPhase_re_assoc ha_ay (by rw [pauliIdx_add_cancel_left]; exact hyx) hay_x ha_ayx
  rw [pauliIdx_add_cancel_left] at hass2
  have haay : (pauliPhase a (a + y)).re = (pauliPhase a y).re := by
    have h := pauliPhase_add_right a y
    simp only [sympSign, hay, ↓reduceIte, Int.cast_one, one_mul] at h
    rw [h]
  have hxy_comm : (pauliPhase y x).re = (pauliPhase x y).re := pauliPhase_re_comm hyx
  have hax_comm : (pauliPhase (a + y) x).re = (pauliPhase x (a + y)).re := pauliPhase_re_comm hay_x
  have hsum_comm : a + y + x = x + (a + y) := by abel
  rw [haay, hxy_comm, hax_comm, hsum_comm] at hass2
  have h1 : (pauliPhase (a + x) (a + y)).re * (pauliPhase a x).re =
      (pauliPhase a y).re * (pauliPhase x y).re := by
    calc (pauliPhase (a + x) (a + y)).re * (pauliPhase a x).re
        = (pauliPhase a x).re * (pauliPhase (a + x) (a + y)).re := by ring
      _ = (pauliPhase x (a + y)).re * (pauliPhase a (x + (a + y))).re := hass1
      _ = (pauliPhase a y).re * (pauliPhase x y).re := hass2.symm
  rw [h1]
  rcases (pauliPhase_re_cases a y).1 hay with h | h
  · have hre : (pauliPhase a y).re = 1 := by simp [h]
    rw [hre]; ring
  · have hre : (pauliPhase a y).re = -1 := by simp [h]
    rw [hre]; ring

/-- Every isotropic subspace `R` admits a consistent real Pauli character `χ : PauliIdx 4 → ℝ`
    with `χ 0 = 1`, `χ p ∈ {±1}` on `R`, and `(pauliPhase p q).re * χ p * χ q = χ (p + q)` on `R`. -/
lemma exists_consistent_char {r : ℕ} {R : Finset (PauliIdx 4)} (hR : IsIsoSub r R) :
    ∃ χ : PauliIdx 4 → ℝ, χ 0 = 1 ∧ (∀ p ∈ R, χ p = 1 ∨ χ p = -1) ∧
      (∀ p ∈ R, ∀ q ∈ R, (pauliPhase p q).re * χ p * χ q = χ (p + q)) := by
  -- Build by induction on `k` (size `2^k` sub-chain inside `R`)!
  have hstep : ∀ (k : ℕ) (S : Finset (PauliIdx 4)), IsIsoSub k S →
      ∃ χ : PauliIdx 4 → ℝ, χ 0 = 1 ∧ (∀ p ∈ S, χ p = 1 ∨ χ p = -1) ∧
        (∀ p ∈ S, ∀ q ∈ S, (pauliPhase p q).re * χ p * χ q = χ (p + q)) := by
    intro k
    induction k with
    | zero =>
      intro S hS
      have hS0 : S = {0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hS.1, fun x hx => by
        by_contra hne
        have h2 : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨0, hS.1, x, hx, Ne.symm hne⟩
        rw [hS.2.1] at h2; omega⟩
      refine ⟨fun _ => 1, rfl, fun _ _ => Or.inl rfl, fun p hp q hq => ?_⟩
      rw [hS0, Finset.mem_singleton] at hp hq; subst hp; subst hq
      simp [pauliPhase_zero_left]
    | succ k ih =>
      -- Wait: to go from `S` (`card = 2^(k+1)`) down to a codim-1 subgroup `S₀ ⊂ S`, pick any `v ∉ S^⊥`?
      -- Even easier: any `S` with `IsIsoSub (k+1) S` has a `k`-dim subgroup `S₀ ⊂ S` with `S = S₀ ∪ (u + S₀)`!
      -- Why? Because `S` has size `2^(k+1) ≥ 2`, pick `a ∈ S \ {0}`: `a ∉ {0}^⊥`? No, pick ANY `w : PauliIdx 4`
      -- such that `symp w a = 1` (exists since `a ≠ 0`!), then `S₀ := S.filter (symp w · = 0)` has `IsIsoSub k S₀`!!
      intro S hS
      have hcard_gt : 1 < S.card := by rw [hS.2.1]; exact Nat.one_lt_two_pow (Nat.succ_ne_zero k)
      obtain ⟨a, haS, ha0⟩ : ∃ a ∈ S, a ≠ 0 := by
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard_gt
        by_cases hx0 : x = 0
        · exact ⟨y, hy, fun h => hxy (hx0.trans h.symm)⟩
        · exact ⟨x, hx, hx0⟩
      -- Pick `w` with `symp w a = 1`!
      have hex_w : ∃ w : PauliIdx 4, symp w a = 1 := by
        by_contra hall; push Not at hall
        have h0 : ∀ w : PauliIdx 4, symp w a = 0 := fun w =>
          (zmod2_cases _).resolve_right (hall w)
        have hs := sum_sympSign_all a
        simp only [ha0, ↓reduceIte] at hs
        have hs1 : ∑ w : PauliIdx 4, (sympSign w a : ℝ) = 256 := by
          have : ∀ w : PauliIdx 4, (sympSign w a : ℝ) = 1 := fun w => by simp [sympSign, h0 w]
          rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_const, Finset.card_univ,
              card_PauliIdx, nsmul_eq_mul]; norm_num
        linarith
      obtain ⟨w, hwa⟩ := hex_w
      let S0 := S.filter fun x => symp w x = 0
      let S1 := S.filter fun x => symp w x = 1
      have hS_eq : S = S0 ∪ S0.image (a + ·) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_image, S0, Finset.mem_filter]
        constructor
        · intro hxS
          rcases zmod2_cases (symp w x) with hx0 | hx1
          · exact Or.inl ⟨hxS, hx0⟩
          · refine Or.inr ⟨a + x, ⟨hS.2.2.1 a haS x hxS, ?_⟩, pauliIdx_add_cancel_left a x⟩
            rw [symp_add_right, hwa, hx1]; decide
        · rintro (⟨hxS, _⟩ | ⟨y, ⟨hyS, _⟩, rfl⟩)
          · exact hxS
          · exact hS.2.2.1 a haS y hyS
      have ha_not_S0 : a ∉ S0 := by simp [S0, hwa]
      have hdisj : Disjoint S0 (S0.image (a + ·)) := by
        rw [Finset.disjoint_left]
        intro z hz0 hzI
        obtain ⟨y, hy0, rfl⟩ := Finset.mem_image.mp hzI
        have h1 : symp w (a + y) = 0 := (Finset.mem_filter.mp hz0).2
        have h2 : symp w y = 0 := (Finset.mem_filter.mp hy0).2
        rw [symp_add_right, hwa, h2, add_zero] at h1
        exact absurd h1 (by decide)
      have hinj : Function.Injective (fun x : PauliIdx 4 => a + x) := fun x y h => by
        have := congr_arg (a + ·) h; simpa [pauliIdx_add_cancel_left] using this
      have hS0_card : S0.card = 2 ^ k := by
        have h1 : S.card = S0.card + S0.card := by
          conv_lhs => rw [hS_eq]
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj]
        rw [hS.2.1, pow_succ] at h1; omega
      have hS0 : IsIsoSub k S0 := by
        refine ⟨Finset.mem_filter.mpr ⟨hS.1, symp_zero_right w⟩, hS0_card, ?_, ?_⟩
        · intro x hx y hy
          exact Finset.mem_filter.mpr ⟨hS.2.2.1 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1,
            by rw [symp_add_right, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, add_zero]⟩
        · intro x hx y hy
          exact hS.2.2.2 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
      obtain ⟨χ0, hχ0_zero, hχ0_pm, hχ0_mul⟩ := ih S0 hS0
      let χ : PauliIdx 4 → ℝ := fun p =>
        if p ∈ S0 then χ0 p else (pauliPhase a (a + p)).re * χ0 (a + p)
      have hre_coe : ∀ p q : PauliIdx 4, symp p q = 0 →
          ((pauliPhase p q).re : ℂ) = pauliPhase p q := fun p q hs => by
        rcases (pauliPhase_re_cases p q).1 hs with h | h <;> simp [h]
      have hph_pm : ∀ p q : PauliIdx 4, symp p q = 0 →
          (pauliPhase p q).re = 1 ∨ (pauliPhase p q).re = -1 := fun p q hs => by
        rcases (pauliPhase_re_cases p q).1 hs with h | h <;> simp [h]
      have hph_comm : ∀ p q : PauliIdx 4, symp p q = 0 →
          (pauliPhase p q).re = (pauliPhase q p).re := fun p q hs => by
        have h := pauliPhase_comm p q; simp only [sympSign, hs, ↓reduceIte, Int.cast_one, one_mul] at h
        rw [h]
      have hph_assoc_re : ∀ p q t : PauliIdx 4,
          symp p q = 0 → symp (p + q) t = 0 → symp q t = 0 → symp p (q + t) = 0 →
          (pauliPhase p q).re * (pauliPhase (p + q) t).re =
          (pauliPhase q t).re * (pauliPhase p (q + t)).re := fun p q t h1 h2 h3 h4 => by
        have h := pauliPhase_assoc_local p q t
        rw [← hre_coe p q h1, ← hre_coe (p + q) t h2, ← hre_coe q t h3, ← hre_coe p (q + t) h4] at h
        have hre := congr_arg Complex.re h
        simpa only [← Complex.ofReal_mul, Complex.ofReal_re] using hre
      have hχ_S0 : ∀ x ∈ S0, χ x = χ0 x := fun x hx => by simp [χ, hx]
      have hχ_aS0 : ∀ x ∈ S0, χ (a + x) = (pauliPhase a x).re * χ0 x := fun x hx => by
        have hnot : a + x ∉ S0 := fun hmem =>
          Finset.disjoint_left.mp hdisj hmem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        simp only [χ, hnot, ↓reduceIte, pauliIdx_add_cancel_left]
      refine ⟨χ, by rw [hχ_S0 0 hS0.1, hχ0_zero], ?_, ?_⟩
      · intro p hp
        rw [hS_eq] at hp
        rcases Finset.mem_union.mp hp with hp0 | hp1
        · rw [hχ_S0 p hp0]; exact hχ0_pm p hp0
        · obtain ⟨x, hx0, rfl⟩ := Finset.mem_image.mp hp1
          rw [hχ_aS0 x hx0]
          have h1 := hph_pm a x (hS.2.2.2 a haS x (Finset.mem_filter.mp hx0).1)
          have h2 := hχ0_pm x hx0
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
      · intro p hp q hq
        rw [hS_eq] at hp hq
        have hsAll : ∀ x ∈ S, ∀ y ∈ S, symp x y = 0 := hS.2.2.2
        rcases Finset.mem_union.mp hp with hp0 | hp1 <;> rcases Finset.mem_union.mp hq with hq0 | hq1
        · rw [hχ_S0 p hp0, hχ_S0 q hq0, hχ_S0 (p + q) (hS0.2.2.1 p hp0 q hq0)]
          exact hχ0_mul p hp0 q hq0
        · obtain ⟨y, hy0, rfl⟩ := Finset.mem_image.mp hq1
          have hpS : p ∈ S := (Finset.mem_filter.mp hp0).1
          have hyS : y ∈ S := (Finset.mem_filter.mp hy0).1
          have hpy0 : p + y ∈ S0 := hS0.2.2.1 p hp0 y hy0
          have hidx : p + (a + y) = a + (p + y) := by abel
          rw [hχ_S0 p hp0, hχ_aS0 y hy0, hidx, hχ_aS0 (p + y) hpy0, ← hχ0_mul p hp0 y hy0]
          have hkey := symp_phase_cocycle_1 (hsAll p hpS a haS) (hsAll a haS p hpS)
            (hsAll a haS y hyS) (hsAll p hpS y hyS)
            (hsAll _ (hS.2.2.1 p hpS a haS) y hyS) (hsAll _ (hS.2.2.1 a haS p hpS) y hyS)
            (hsAll p hpS _ (hS.2.2.1 a haS y hyS)) (hsAll a haS _ (hS.2.2.1 p hpS y hyS))
          calc (pauliPhase p (a + y)).re * χ0 p * ((pauliPhase a y).re * χ0 y)
              = ((pauliPhase p (a + y)).re * (pauliPhase a y).re) * χ0 p * χ0 y := by ring
            _ = ((pauliPhase a (p + y)).re * (pauliPhase p y).re) * χ0 p * χ0 y := by rw [hkey]
            _ = _ := by ring
        · obtain ⟨x, hx0, rfl⟩ := Finset.mem_image.mp hp1
          have hxS : x ∈ S := (Finset.mem_filter.mp hx0).1
          have hqS : q ∈ S := (Finset.mem_filter.mp hq0).1
          have hxq0 : x + q ∈ S0 := hS0.2.2.1 x hx0 q hq0
          rw [hχ_aS0 x hx0, hχ_S0 q hq0, add_assoc, hχ_aS0 (x + q) hxq0, ← hχ0_mul x hx0 q hq0]
          have hass := hph_assoc_re a x q (hsAll a haS x hxS)
            (hsAll _ (hS.2.2.1 a haS x hxS) q hqS) (hsAll x hxS q hqS)
            (hsAll a haS _ (hS.2.2.1 x hxS q hqS))
          calc (pauliPhase (a + x) q).re * ((pauliPhase a x).re * χ0 x) * χ0 q
              = ((pauliPhase a x).re * (pauliPhase (a + x) q).re) * χ0 x * χ0 q := by ring
            _ = ((pauliPhase x q).re * (pauliPhase a (x + q)).re) * χ0 x * χ0 q := by rw [hass]
            _ = _ := by ring
        · obtain ⟨x, hx0, rfl⟩ := Finset.mem_image.mp hp1
          obtain ⟨y, hy0, rfl⟩ := Finset.mem_image.mp hq1
          have hxS : x ∈ S := (Finset.mem_filter.mp hx0).1
          have hyS : y ∈ S := (Finset.mem_filter.mp hy0).1
          have hxy0 : x + y ∈ S0 := hS0.2.2.1 x hx0 y hy0
          have hidx : (a + x) + (a + y) = x + y := by
            calc (a + x) + (a + y) = (a + a) + (x + y) := by abel
              _ = x + y := by rw [pauliIdx_add_self, zero_add]
          rw [hχ_aS0 x hx0, hχ_aS0 y hy0, hidx, hχ_S0 (x + y) hxy0, ← hχ0_mul x hx0 y hy0]
          have hkey := symp_phase_cocycle_2 (hsAll a haS x hxS) (hsAll a haS y hyS) (hsAll y hyS x hxS)
            (hsAll _ (hS.2.2.1 a haS x hxS) _ (hS.2.2.1 a haS y hyS))
            (hsAll x hxS _ (hS.2.2.1 a haS y hyS))
            (hsAll a haS _ (hS.2.2.1 x hxS _ (hS.2.2.1 a haS y hyS)))
            (hsAll a haS _ (hS.2.2.1 a haS y hyS))
            (hsAll _ (hS.2.2.1 a haS y hyS) x hxS)
            (hsAll a haS _ (hS.2.2.1 _ (hS.2.2.1 a haS y hyS) x hxS))
          calc (pauliPhase (a + x) (a + y)).re * ((pauliPhase a x).re * χ0 x) * ((pauliPhase a y).re * χ0 y)
              = ((pauliPhase (a + x) (a + y)).re * (pauliPhase a x).re * (pauliPhase a y).re) * χ0 x * χ0 y := by ring
            _ = (pauliPhase x y).re * χ0 x * χ0 y := by rw [hkey]
  exact hstep r R hR

/-- **Spectral `L_out` Bound (`pauli_Lout_le_of_contextuality_1575`)**:
    Under `CD(W(7,2)) ≥ 1575`, for EVERY Lagrangian `L` (`|L| = 16`) and EVERY unit state `ψ`,
      `∑_{p ∉ L} |c_p| ≤ 594918 / 10000`.
    Proved via 10-line character averaging `Tr(S_out³) ≤ 208320` + `hermitian_max_eig_le_of_trace_bounds`! -/
theorem pauli_Lout_le_of_contextuality_1575
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    ∑ p ∈ Finset.univ \ L, |(innerProd ψ (pauliApply p ψ)).re| ≤ (594918 / 10000 : ℝ) := by
  let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  let σo : PauliIdx 4 → ℝ := fun p => if p ∈ L then 0 else if 0 ≤ c p then 1 else -1
  have hσo0 : σo 0 = 0 := by simp [σo, hL.1]
  have hσopm : ∀ p ∉ L, σo p = 1 ∨ σo p = -1 := fun p hp => by
    simp only [σo, hp, ↓reduceIte]; split_ifs <;> simp
  let Sout := pauliExpand σo
  have hcard_out : ((Finset.univ \ L).card : ℝ) = 240 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, card_PauliIdx, hL.2.1]; norm_num
  have htr1 : matTr Sout = 0 := by simp [Sout, matTr_pauliExpand, hσo0]
  have htr2 : (matTr (matMul Sout Sout)).re = 3840 := by
    rw [matTr_mul_self_herm (pauliExpand_herm σo), Complex.ofReal_re, frobSq_pauliExpand]
    rw [← Finset.sum_sdiff (Finset.subset_univ L)]
    have h0 : ∑ p ∈ L, (σo p) ^ 2 = 0 := Finset.sum_eq_zero fun p hp => by simp [σo, hp]
    have h1 : ∑ p ∈ Finset.univ \ L, (σo p) ^ 2 = 240 := by
      have hsq : ∀ p ∈ Finset.univ \ L, (σo p) ^ 2 = 1 := fun p hp => by
        rcases hσopm p (Finset.mem_sdiff.mp hp).2 with h | h <;> rw [h] <;> norm_num
      rw [Finset.sum_congr rfl hsq, Finset.sum_const, nsmul_eq_mul, mul_one, hcard_out]
    rw [h0, h1]; norm_num
  -- Step 1: Character-averaging proof of `Tr(Sout³).re ≤ 208320`!
  have htr3 : (matTr (matMul Sout (matMul Sout Sout))).re ≤ 208320 := by
    obtain ⟨χ0, hχ0_0, hχ0_pm, hχ0_mul⟩ := exists_consistent_char hL
    let μ : PauliIdx 4 → PauliIdx 4 → ℝ := fun x p =>
      if p ∈ L ∧ p ≠ 0 then (sympSign x p : ℝ) * χ0 p else 0
    have hμ0 : ∀ x, μ x 0 = 0 := fun x => by simp [μ]
    -- For every `x`, `σ_x := σo + μ x` is a valid `{±1}` sign assignment on `𝔽₂⁸ \ {0}`!
    have hcube_x : ∀ x : PauliIdx 4,
        (matTr (matMul (pauliExpand (fun p => σo p + μ x p))
          (matMul (pauliExpand (fun p => σo p + μ x p)) (pauliExpand (fun p => σo p + μ x p))))).re ≤
        211680 := by
      intro x
      have h0 : σo 0 + μ x 0 = 0 := by rw [hσo0, hμ0, add_zero]
      have hpm : ∀ p : PauliIdx 4, p ≠ 0 → σo p + μ x p = 1 ∨ σo p + μ x p = -1 := by
        intro p hp
        by_cases hpL : p ∈ L
        · simp only [σo, μ, hpL, hp, ne_eq, not_false_eq_true, and_self, ↓reduceIte, zero_add]
          have h1 : (sympSign x p : ℝ) = 1 ∨ (sympSign x p : ℝ) = -1 := by
            simp only [sympSign]; split_ifs <;> simp
          rcases h1 with h1 | h1 <;> rcases hχ0_pm p hpL with h2 | h2 <;> simp [h1, h2]
        · simp only [σo, μ, hpL, false_and, ↓reduceIte, add_zero]; split_ifs <;> simp
      rw [matTr_cube_pauliExpand_four _ h0]
      linarith [hCD _ h0 hpm]
    -- Expand `Tr((Sout + Mx)³) = Tr(Sout³) + 3 Tr(Sout² Mx) + 3 Tr(Sout Mx²) + Tr(Mx³)`!
    -- Even cleaner: directly expand in `PauliIdx 4` via `matTr_cube_pauliExpand_four`!
    -- Notice: `μ x` is supported on `L \ {0}` and `σo` is supported on `L^c`!
    -- For any `p, q`:
    --   - `Tr(Sout Mx²) = 0`: if `p, q ∈ L`, then `p + q ∈ L`, so `σo (p + q) = 0`!
    --   - `∑_x Tr(Sout² Mx) = 0`: linear in `μ x q = sympSign x q * χ0 q` (`q ∈ L \ {0}`), and `∑_x sympSign x q = 0`!
    --   - `Tr(Mx³) = 3360`: for `q ∈ L \ {0}` and `p ∈ L \ {0, q}`,
    --       `(pauliPhase q p).re * μ x q * μ x p * μ x (q + p) = 1`, and there are `15 * 14 = 210` pairs, `16 * 210 = 3360`!
    have hsum_x : ∑ x : PauliIdx 4,
        (matTr (matMul (pauliExpand (fun p => σo p + μ x p))
          (matMul (pauliExpand (fun p => σo p + μ x p)) (pauliExpand (fun p => σo p + μ x p))))).re =
        256 * (matTr (matMul Sout (matMul Sout Sout))).re + 256 * 3360 := by
      have hexp : ∀ x : PauliIdx 4,
          (matTr (matMul (pauliExpand (fun p => σo p + μ x p))
            (matMul (pauliExpand (fun p => σo p + μ x p)) (pauliExpand (fun p => σo p + μ x p))))).re =
          (matTr (matMul Sout (matMul Sout Sout))).re +
          3 * (matTr (matMul (matMul Sout Sout) (pauliExpand (μ x)))).re +
          3 * (matTr (matMul Sout (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re +
          (matTr (matMul (pauliExpand (μ x)) (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re := by
        intro x
        let M := pauliExpand (μ x)
        have hadd : pauliExpand (fun p => σo p + μ x p) = matAdd Sout M := pauliExpand_add σo (μ x)
        rw [hadd]
        have hcube : matTr (matMul (matAdd Sout M) (matMul (matAdd Sout M) (matAdd Sout M))) =
            matTr (matMul Sout (matMul Sout Sout)) +
            3 * matTr (matMul (matMul Sout Sout) M) +
            3 * matTr (matMul Sout (matMul M M)) +
            matTr (matMul M (matMul M M)) := by
          simp only [matMul_add_left, matMul_add_right, matTr_add]
          have t1 : matTr (matMul Sout (matMul Sout M)) = matTr (matMul (matMul Sout Sout) M) := by
            rw [matMul_assoc]
          have t2 : matTr (matMul Sout (matMul M Sout)) = matTr (matMul (matMul Sout Sout) M) := by
            rw [matTr_mul_comm Sout, matMul_assoc, matTr_mul_comm M, matMul_assoc]
          have t3 : matTr (matMul M (matMul Sout Sout)) = matTr (matMul (matMul Sout Sout) M) :=
            matTr_mul_comm M _
          have t4 : matTr (matMul M (matMul Sout M)) = matTr (matMul Sout (matMul M M)) := by
            rw [matTr_mul_comm M, matMul_assoc, matTr_mul_comm Sout, matMul_assoc, matTr_mul_comm]
          have t5 : matTr (matMul M (matMul M Sout)) = matTr (matMul Sout (matMul M M)) := by
            rw [← matMul_assoc, matTr_mul_comm]
          rw [t1, t2, t3, t4, t5]; ring
        rw [hcube]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; rfl
      simp_rw [hexp, Finset.sum_add_distrib]
      have hterm1 : ∑ _x : PauliIdx 4, (matTr (matMul Sout (matMul Sout Sout))).re =
          256 * (matTr (matMul Sout (matMul Sout Sout))).re := by
        rw [Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul]; norm_num
      have hterm2 : ∑ x : PauliIdx 4, 3 * (matTr (matMul (matMul Sout Sout) (pauliExpand (μ x)))).re = 0 := by
        rw [← Finset.mul_sum]
        suffices hz : ∑ x : PauliIdx 4, (matTr (matMul (matMul Sout Sout) (pauliExpand (μ x)))).re = 0 by
          rw [hz, mul_zero]
        have hS2 : matMul Sout Sout = pauliExpand (fun q => ∑ p : PauliIdx 4, (pauliPhase q p).re * σo p * σo (q + p)) :=
          matMul_pauliExpand_self σo
        simp_rw [hS2, matTr_pauliExpand_mul]
        have h16 : ((2 : ℂ) ^ 4) = ((16 : ℝ) : ℂ) := by norm_num
        simp_rw [h16, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        have h0 : ∀ q : PauliIdx 4, ∑ x : PauliIdx 4,
            (∑ p : PauliIdx 4, (pauliPhase q p).re * σo p * σo (q + p)) * μ x q = 0 := by
          intro q
          rw [← Finset.mul_sum]
          by_cases hq : q ∈ L ∧ q ≠ 0
          · have : ∑ x : PauliIdx 4, μ x q = (∑ x : PauliIdx 4, (sympSign x q : ℝ)) * χ0 q := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => by simp [μ, hq]
            rw [this, sum_sympSign_all]; simp [hq.2]
          · have : ∑ x : PauliIdx 4, μ x q = 0 := Finset.sum_eq_zero fun x _ => by simp [μ, hq]
            rw [this, mul_zero]
        rw [Finset.sum_eq_zero fun q _ => h0 q, mul_zero]
      have hterm3 : ∀ x : PauliIdx 4,
          (matTr (matMul Sout (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re = 0 := by
        intro x
        rw [matMul_pauliExpand_self, matTr_pauliExpand_mul]
        have h16 : ((2 : ℂ) ^ 4) = ((16 : ℝ) : ℂ) := by norm_num
        rw [h16, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
        suffices hz : ∑ q : PauliIdx 4, σo q * ∑ p : PauliIdx 4, (pauliPhase q p).re * μ x p * μ x (q + p) = 0 by
          rw [hz, mul_zero]
        refine Finset.sum_eq_zero fun q _ => ?_
        by_cases hqL : q ∈ L
        · simp [σo, hqL]
        · suffices h0 : ∑ p : PauliIdx 4, (pauliPhase q p).re * μ x p * μ x (q + p) = 0 by rw [h0, mul_zero]
          refine Finset.sum_eq_zero fun p _ => ?_
          by_cases hpL : p ∈ L
          · have hqpL : q + p ∉ L := fun hmem => hqL (by
              have := hL.2.2.1 _ hmem p hpL; rwa [pauliIdx_add_cancel_right] at this)
            simp [μ, hqpL]
          · simp [μ, hpL]
      have hterm4 : ∀ x : PauliIdx 4,
          (matTr (matMul (pauliExpand (μ x)) (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re = 3360 := by
        intro x
        rw [matTr_cube_pauliExpand_four (μ x) (hμ0 x)]
        simp only [signCubeSum]
        have hsum_L : ∑ q ∈ Finset.univ.erase (0 : PauliIdx 4),
            μ x q * ((1 / 2 : ℝ) * ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 4)).erase q,
              (pauliPhase q p).re * μ x p * μ x (q + p)) = 105 := by
          have hsub : L.erase 0 ⊆ Finset.univ.erase (0 : PauliIdx 4) := fun q hq =>
            Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hq).1, Finset.mem_univ _⟩
          rw [← Finset.sum_sdiff hsub]
          have hout : ∑ q ∈ (Finset.univ.erase (0 : PauliIdx 4)) \ (L.erase 0),
              μ x q * ((1 / 2 : ℝ) * ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 4)).erase q,
                (pauliPhase q p).re * μ x p * μ x (q + p)) = 0 := by
            refine Finset.sum_eq_zero fun q hq => ?_
            have hq0 : q ≠ 0 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hq).1).1
            have hqL : q ∉ L := fun h => (Finset.mem_sdiff.mp hq).2 (Finset.mem_erase.mpr ⟨hq0, h⟩)
            simp [μ, hqL]
          rw [hout, zero_add]
          have hin : ∀ q ∈ L.erase 0,
              μ x q * ((1 / 2 : ℝ) * ∑ p ∈ (Finset.univ.erase (0 : PauliIdx 4)).erase q,
                (pauliPhase q p).re * μ x p * μ x (q + p)) = 7 := by
            intro q hq
            have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
            have hqL : q ∈ L := (Finset.mem_erase.mp hq).2
            have hsub2 : (L.erase 0).erase q ⊆ (Finset.univ.erase (0 : PauliIdx 4)).erase q :=
              Finset.erase_subset_erase q hsub
            rw [← Finset.sum_sdiff hsub2]
            have hout2 : ∑ p ∈ ((Finset.univ.erase (0 : PauliIdx 4)).erase q) \ ((L.erase 0).erase q),
                (pauliPhase q p).re * μ x p * μ x (q + p) = 0 := by
              refine Finset.sum_eq_zero fun p hp => ?_
              have hpq : p ≠ q := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hp).1).1
              have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hp).1).2).1
              have hpL : p ∉ L := fun h => (Finset.mem_sdiff.mp hp).2
                (Finset.mem_erase.mpr ⟨hpq, Finset.mem_erase.mpr ⟨hp0, h⟩⟩)
              simp [μ, hpL]
            rw [hout2, zero_add]
            have hterm : ∀ p ∈ (L.erase 0).erase q,
                μ x q * ((pauliPhase q p).re * μ x p * μ x (q + p)) = 1 := by
              intro p hp
              have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
              have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
              have hpL : p ∈ L := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2
              have hqpL : q + p ∈ L := hL.2.2.1 q hqL p hpL
              have hqp0 : q + p ≠ 0 := fun hc => hpq (by
                have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
              simp only [μ, hqL, hq0, hpL, hp0, hqpL, hqp0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
              rw [sympSign_add_right]; push_cast
              have hss1 : (sympSign x q : ℝ) ^ 2 = 1 := by simp only [sympSign]; split_ifs <;> norm_num
              have hss2 : (sympSign x p : ℝ) ^ 2 = 1 := by simp only [sympSign]; split_ifs <;> norm_num
              have hχsq : (χ0 (q + p)) ^ 2 = 1 := by
                rcases hχ0_pm (q + p) hqpL with h | h <;> rw [h] <;> norm_num
              calc (sympSign x q : ℝ) * χ0 q * ((pauliPhase q p).re * ((sympSign x p : ℝ) * χ0 p) *
                      ((sympSign x q : ℝ) * (sympSign x p : ℝ) * χ0 (q + p)))
                  = (sympSign x q : ℝ) ^ 2 * (sympSign x p : ℝ) ^ 2 *
                      (((pauliPhase q p).re * χ0 q * χ0 p) * χ0 (q + p)) := by ring
                _ = 1 * 1 * (χ0 (q + p) * χ0 (q + p)) := by rw [hss1, hss2, hχ0_mul q hqL p hpL]
                _ = 1 := by linarith [hχsq]
            have hcard14 : (((L.erase 0).erase q).card : ℝ) = 14 := by
              rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num
            calc μ x q * ((1 / 2 : ℝ) * ∑ p ∈ (L.erase 0).erase q, (pauliPhase q p).re * μ x p * μ x (q + p))
                = (1 / 2 : ℝ) * (μ x q * ∑ p ∈ (L.erase 0).erase q, (pauliPhase q p).re * μ x p * μ x (q + p)) := by ring
              _ = (1 / 2 : ℝ) * ∑ p ∈ (L.erase 0).erase q, μ x q * ((pauliPhase q p).re * μ x p * μ x (q + p)) := by
                  rw [Finset.mul_sum]
              _ = (1 / 2 : ℝ) * ∑ _p ∈ (L.erase 0).erase q, (1 : ℝ) := by
                  rw [Finset.sum_congr rfl hterm]
              _ = 7 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard14]; norm_num
          have hcard15 : ((L.erase 0).card : ℝ) = 15 := by
            rw [Finset.card_erase_of_mem hL.1, hL.2.1]; norm_num
          rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, hcard15]; norm_num
        rw [hsum_L]; norm_num
      have hterm3_sum : ∑ x : PauliIdx 4, 3 * (matTr (matMul Sout (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [hterm3 x, mul_zero]
      have hterm4_sum : ∑ x : PauliIdx 4,
          (matTr (matMul (pauliExpand (μ x)) (matMul (pauliExpand (μ x)) (pauliExpand (μ x))))).re = 256 * 3360 := by
        rw [Finset.sum_congr rfl fun x _ => hterm4 x, Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul]
        norm_num
      rw [hterm1, hterm2, hterm3_sum, hterm4_sum]; ring
    have hsum_le : ∑ x : PauliIdx 4,
        (matTr (matMul (pauliExpand (fun p => σo p + μ x p))
          (matMul (pauliExpand (fun p => σo p + μ x p)) (pauliExpand (fun p => σo p + μ x p))))).re ≤
        256 * 211680 := by
      calc ∑ x : PauliIdx 4, _ ≤ ∑ _x : PauliIdx 4, (211680 : ℝ) := Finset.sum_le_sum fun x _ => hcube_x x
        _ = 256 * 211680 := by rw [Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul]; norm_num
    linarith
  -- Step 2: Apply `hermitian_max_eig_le_of_trace_bounds` at `(T2 = 3840, T3 = 208320, lam0 = 594918/10000)`!
  have h210_lo : (14.4913 : ℝ) < Real.sqrt 210 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hR_hi : Real.sqrt (3840 - (16 / 15 : ℝ) * (594918 / 10000 : ℝ) ^ 2) < (8.0702 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hstrict : (208320 : ℝ) <
      (224 / 225 : ℝ) * (594918 / 10000 : ℝ) ^ 3 -
      ((594918 / 10000 : ℝ) / 5) * (3840 - (16 / 15) * (594918 / 10000 : ℝ) ^ 2) -
      (13 / Real.sqrt 210) * Real.sqrt (3840 - (16 / 15) * (594918 / 10000 : ℝ) ^ 2) ^ 3 := by
    have h1 : 13 / Real.sqrt 210 < 13 / 14.4913 :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) h210_lo
    have h2 : Real.sqrt (3840 - (16 / 15 : ℝ) * (594918 / 10000 : ℝ) ^ 2) ^ 3 < (8.0702 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hR_hi (Real.sqrt_nonneg _) (by norm_num)
    have hprod : (13 / Real.sqrt 210) *
        Real.sqrt (3840 - (16 / 15 : ℝ) * (594918 / 10000 : ℝ) ^ 2) ^ 3 <
        (13 / 14.4913) * (8.0702 : ℝ) ^ 3 :=
      mul_lt_mul'' h1 h2 (by positivity) (by positivity)
    have hnum : (208320 : ℝ) <
        (224 / 225 : ℝ) * (594918 / 10000 : ℝ) ^ 3 -
        ((594918 / 10000 : ℝ) / 5) * (3840 - (16 / 15) * (594918 / 10000 : ℝ) ^ 2) -
        (13 / 14.4913) * (8.0702 : ℝ) ^ 3 := by norm_num
    linarith
  have hspec := hermitian_max_eig_le_of_trace_bounds (pauliExpand_herm σo) (by norm_num)
    htr1 htr2 htr3 (by norm_num) (by norm_num) hstrict hunit
  rw [innerProd_pauliExpand_re, ← Finset.sum_sdiff (Finset.subset_univ L)] at hspec
  have h0 : ∑ p ∈ L, σo p * c p = 0 := Finset.sum_eq_zero fun p hp => by simp [σo, hp]
  have heq : ∑ p ∈ Finset.univ \ L, σo p * c p = ∑ p ∈ Finset.univ \ L, |c p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpL : p ∉ L := (Finset.mem_sdiff.mp hp).2
    simp only [σo, hpL, ↓reduceIte]
    by_cases hcp : 0 ≤ c p
    · simp only [hcp, ↓reduceIte, one_mul, abs_of_nonneg hcp]
    · simp only [hcp, ↓reduceIte, neg_mul, one_mul, abs_of_neg (not_le.mp hcp)]
  rw [h0, add_zero, heq] at hspec; exact hspec

/-! ### Section 2: Global Polynomial Bounds, Self-Duality, Coset Identities, and 2D Bessel -/

/-- Exact quartic `h(x) = x (x - 1/4)² (x + 1/2) = x⁴ - (3/16) x² + (1/32) x`. -/
noncomputable def hPoly (x : ℝ) : ℝ := x * (x - 1 / 4) ^ 2 * (x + 1 / 2)

/-- Exact quartic `w(x) = (1 - 4x)³ (1 + (4/3) x) = 1 - (32/3) x + 32 x² - (256/3) x⁴`. -/
noncomputable def wPoly (x : ℝ) : ℝ := (1 - 4 * x) ^ 3 * (1 + (4 / 3) * x)

lemma hPoly_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hPoly x := by
  simp only [hPoly]; positivity

lemma hPoly_expand (x : ℝ) : hPoly x = x ^ 4 - (3 / 16) * x ^ 2 + (1 / 32) * x := by
  simp only [hPoly]; ring

lemma wPoly_expand (x : ℝ) : wPoly x = 1 - (32 / 3) * x + 32 * x ^ 2 - (256 / 3) * x ^ 4 := by
  simp only [wPoly]; ring

/-- Exact 4-qubit Parseval sum `∑_{p≠0} c_p² = 15` and `pauliMoment4 = 1 + ∑_{p≠0} c_p⁴`. -/
lemma sum_sq_and_fourth_four {ψ : QState 4} (hunit : IsUnitState ψ) :
    let U := Finset.univ.erase (0 : PauliIdx 4)
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    (∑ p ∈ U, (c p) ^ 2 = 15) ∧
    (pauliMoment4 4 ψ = 1 + ∑ p ∈ U, (c p) ^ 4) := by
  intro U c
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hns : ∀ p : PauliIdx 4, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
    fun p => innerProd_pauliApply_self_normSq p ψ
  constructor
  · have h := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4))] at h
    simp_rw [hns, hc0] at h
    have h24 : (2 : ℝ) ^ 4 = 16 := by norm_num
    rw [h24] at h; linarith
  · rw [pauliMoment4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4))]
    have h4 : ∀ p : PauliIdx 4, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2 = (c p) ^ 4 :=
      fun p => by rw [hns]; ring
    simp_rw [h4, hc0]; ring

/-- Global `h`-sum and `w`-sum bounds under `L₁ ≤ 601919/10000` and `F₄ ≤ 31/16`. -/
lemma global_h_and_w_bounds {ψ : QState 4} (hunit : IsUnitState ψ)
    (hL1 : ∑ p ∈ Finset.univ.erase (0 : PauliIdx 4), |(innerProd ψ (pauliApply p ψ)).re| ≤ (601919 / 10000 : ℝ))
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16) :
    let U := Finset.univ.erase (0 : PauliIdx 4)
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    (∑ p ∈ U, hPoly |c p| ≤ (1919 / 320000 : ℝ)) ∧
    ((388592 / 30000 : ℝ) ≤ ∑ p ∈ U, wPoly |c p|) := by
  intro U c
  obtain ⟨hsum2, hsum4⟩ := sum_sq_and_fourth_four hunit
  have hcard : (U.card : ℝ) = 255 := by rw [card_PauliIdx_erase_zero]; norm_num
  have habs2 : ∀ p, |c p| ^ 2 = (c p) ^ 2 := fun p => sq_abs (c p)
  have habs4 : ∀ p, |c p| ^ 4 = (c p) ^ 4 := fun p => by
    calc |c p| ^ 4 = (|c p| ^ 2) ^ 2 := by ring
      _ = ((c p) ^ 2) ^ 2 := by rw [sq_abs]
      _ = (c p) ^ 4 := by ring
  constructor
  · simp_rw [hPoly_expand, habs2, habs4, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    linarith
  · simp_rw [wPoly_expand, habs2, habs4, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    linarith

/-- **Global Quartic MUB Excess Identity (`val_B` core)**:
    For ANY Lagrangian `L`, writing `S₂ = ∑_{p ∈ L\{0}} c_p²`, `S₄ = ∑_{p ∈ L\{0}} c_p⁴`,
      `F₄ - 31/16 = (S₄ - S₂ / 8) + ∑_{q ∉ L} (|c_q| - 1/4)² (|c_q| + 1/4)²`,
    and `∑_{q ∉ L} (|c_q| - 1/4)² = 30 - S₂ - (1/2) L_out`. -/
lemma lagrangian_quartic_mub_identities {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
    let S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
    let Lout : ℝ := ∑ q ∈ Finset.univ \ L, |c q|
    (pauliMoment4 4 ψ - 31 / 16 =
      (S4 - S2 / 8) + ∑ q ∈ Finset.univ \ L, (|c q| - 1 / 4) ^ 2 * (|c q| + 1 / 4) ^ 2) ∧
    (∑ q ∈ Finset.univ \ L, (|c q| - 1 / 4) ^ 2 = (60 - Lout) / 2 - S2) ∧
    (∑ q ∈ Finset.univ \ L, (c q) ^ 2 = 15 - S2) := by
  intro c S2 S4 Lout
  obtain ⟨hsum2, hsum4⟩ := sum_sq_and_fourth_four hunit
  have hsub : L.erase 0 ⊆ Finset.univ.erase (0 : PauliIdx 4) := fun p hp =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hp).1, Finset.mem_univ _⟩
  have hsdiff : (Finset.univ.erase (0 : PauliIdx 4)) \ (L.erase 0) = Finset.univ \ L := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨hp0, hnot⟩; exact fun hpL => hnot ⟨hp0, hpL⟩
    · intro hpL; exact ⟨fun h0 => hpL (h0 ▸ hL.1), fun ⟨_, h⟩ => hpL h⟩
  have hcard_out : ((Finset.univ \ L).card : ℝ) = 240 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, card_PauliIdx, hL.2.1]; norm_num
  have h2out : ∑ q ∈ Finset.univ \ L, (c q) ^ 2 = 15 - S2 := by
    have h := Finset.sum_sdiff hsub (f := fun p => (c p) ^ 2)
    rw [hsdiff] at h; linarith
  have h4out : ∑ q ∈ Finset.univ \ L, (c q) ^ 4 = pauliMoment4 4 ψ - 1 - S4 := by
    have h := Finset.sum_sdiff hsub (f := fun p => (c p) ^ 4)
    rw [hsdiff] at h; linarith
  refine ⟨?_, ?_, h2out⟩
  · have hterm : ∀ q : PauliIdx 4,
        (|c q| - 1 / 4) ^ 2 * (|c q| + 1 / 4) ^ 2 = (c q) ^ 4 - (1 / 8) * (c q) ^ 2 + 1 / 256 := fun q => by
      have hsq : |c q| ^ 2 = (c q) ^ 2 := sq_abs (c q)
      calc (|c q| - 1 / 4) ^ 2 * (|c q| + 1 / 4) ^ 2 = (|c q| ^ 2 - 1 / 16) ^ 2 := by ring
        _ = ((c q) ^ 2 - 1 / 16) ^ 2 := by rw [hsq]
        _ = (c q) ^ 4 - (1 / 8) * (c q) ^ 2 + 1 / 256 := by ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard_out, h4out, h2out]
    ring
  · have hterm : ∀ q : PauliIdx 4, (|c q| - 1 / 4) ^ 2 = (c q) ^ 2 - (1 / 2) * |c q| + 1 / 16 := fun q => by
      nlinarith [sq_abs (c q)]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard_out, h2out]
    ring

/-- **Coset Self-Duality Identities (Quotient-Free!)**:
    For any Lagrangian `L`, let `s(x) := ∑_{q ∈ L} c_{x + q}²`. Then:
    1. `s(x) = 1 + ∑_{p ∈ L\{0}} (-1)^{ω(x, p)} c_p²` (so `1 - S₂ ≤ s(x) ≤ 1 + S₂` for all `x`),
    2. `∑_{x ∉ L} (s(x) - 1) = -16 S₂` and `∑_{x ∉ L} (s(x) - 1)² = 16 (16 S₄ - S₂²)`,
    3. Exact Pythagoras excess:
       `pauliMoment4 4 ψ - 31/16 = (2 S₄ - S₂/8 - S₂²/16) + (1/256) ∑_{x ∉ L} (s(x) - 16 c_x²)²`. -/
lemma lagrangian_coset_identities {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
    let S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
    let s : PauliIdx 4 → ℝ := fun x => ∑ q ∈ L, (c (x + q)) ^ 2
    (∀ x : PauliIdx 4, s x = 1 + ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2) ∧
    (∀ x : PauliIdx 4, 1 - S2 ≤ s x) ∧
    (∑ x ∈ Finset.univ \ L, (s x - 1) = -16 * S2) ∧
    (∑ x ∈ Finset.univ \ L, (s x - 1) ^ 2 = 16 * (16 * S4 - S2 ^ 2)) ∧
    (pauliMoment4 4 ψ - 31 / 16 =
      (2 * S4 - S2 / 8 - S2 ^ 2 / 16) +
        (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2) := by
  intro c S2 S4 s
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hns : ∀ p : PauliIdx 4, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
    fun p => innerProd_pauliApply_self_normSq p ψ
  have hcard_L : (L.card : ℝ) = 16 := by rw [hL.2.1]; norm_num
  have hcard_out : ((Finset.univ \ L).card : ℝ) = 240 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, card_PauliIdx, hL.2.1]; norm_num
  -- 1. Prove `s x = 1 + ∑_{p ∈ L\{0}} sympSign x p * c_p²` from `pauli_symp_self_dual`!
  have hs_wht : ∀ x : PauliIdx 4, s x = 1 + ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 := by
    intro x
    have h1 : ∑ p ∈ L, (sympSign x p : ℝ) * (16 * (c p) ^ 2) =
        ∑ q : PauliIdx 4, (∑ p ∈ L, (sympSign (x + q) p : ℝ)) * (c q) ^ 2 := by
      have hsd : ∀ p : PauliIdx 4, 16 * (c p) ^ 2 = ∑ q : PauliIdx 4, (sympSign q p : ℝ) * (c q) ^ 2 := by
        intro p
        have h := (pauli_symp_self_dual ψ p).symm
        simp_rw [hns] at h; norm_num at h; exact h
      simp_rw [hsd, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [sympSign_add_left]; push_cast; ring
    have h2 : ∑ q : PauliIdx 4, (∑ p ∈ L, (sympSign (x + q) p : ℝ)) * (c q) ^ 2 = 16 * s x := by
      have hperp := (lagrangian_perp_eq_and_card_anticomm hL).1
      have hterm : ∀ q : PauliIdx 4, (∑ p ∈ L, (sympSign (x + q) p : ℝ)) * (c q) ^ 2 =
          if x + q ∈ L then 16 * (c q) ^ 2 else 0 := fun q => by
        rw [sum_sympSign_isoSub hL (x + q)]
        split_ifs with h1 h2 h2
        · norm_num
        · exact absurd ((hperp (x + q)).mp h1) h2
        · exact absurd ((hperp (x + q)).mpr h2) h1
        · ring
      rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_filter, ← Finset.mul_sum]
      refine congr_arg (16 * ·) ?_
      dsimp only [s]
      refine Finset.sum_bij (fun q _ => x + q) ?_ ?_ ?_ ?_
      · intro q hq; exact (Finset.mem_filter.mp hq).2
      · intro q1 _ q2 _ h; have := congr_arg (x + ·) h; simpa [pauliIdx_add_cancel_left] using this
      · intro r hr
        exact ⟨x + r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [pauliIdx_add_cancel_left]⟩,
               pauliIdx_add_cancel_left x r⟩
      · intro q _; rw [pauliIdx_add_cancel_left]
    rw [h2, ← Finset.add_sum_erase _ _ hL.1] at h1
    have h0t : (sympSign x 0 : ℝ) * (16 * (c 0) ^ 2) = 16 := by simp [sympSign, symp_zero_right, hc0]
    rw [h0t] at h1
    have hmul : ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (16 * (c p) ^ 2) =
        16 * ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    rw [hmul] at h1; linarith
  -- 2. `1 - S2 ≤ s x` for all `x`!
  have hs_lb : ∀ x : PauliIdx 4, 1 - S2 ≤ s x := fun x => by
    rw [hs_wht x]
    have hle : ∑ p ∈ L.erase 0, (-(c p) ^ 2) ≤ ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 := by
      refine Finset.sum_le_sum fun p _ => ?_
      have hss : (sympSign x p : ℝ) = 1 ∨ (sympSign x p : ℝ) = -1 := by
        simp only [sympSign]; split_ifs <;> simp
      rcases hss with h | h <;> rw [h] <;> nlinarith [sq_nonneg (c p)]
    rw [Finset.sum_neg_distrib] at hle; linarith
  -- 3. `s x = 1 + S2` for `x ∈ L`, and sums over `x ∉ L`!
  have hs_in_L : ∀ x ∈ L, s x - 1 = S2 := fun x hx => by
    rw [hs_wht x]
    have h1 : ∀ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 = (c p) ^ 2 := fun p hp => by
      simp [sympSign, hL.2.2.2 x hx p (Finset.mem_erase.mp hp).2]
    rw [Finset.sum_congr rfl h1]; ring
  have hsum_all_1 : ∑ x : PauliIdx 4, (s x - 1) = 0 := by
    simp_rw [hs_wht, add_sub_cancel_left]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [← Finset.sum_mul, sum_sympSign_all]; simp [(Finset.mem_erase.mp hp).1]
  have hsum_out_1 : ∑ x ∈ Finset.univ \ L, (s x - 1) = -16 * S2 := by
    rw [← Finset.sum_sdiff (Finset.subset_univ L)] at hsum_all_1
    have hin : ∑ x ∈ L, (s x - 1) = 16 * S2 := by
      rw [Finset.sum_congr rfl hs_in_L, Finset.sum_const, nsmul_eq_mul, hcard_L]
    linarith
  have hsum_all_2 : ∑ x : PauliIdx 4, (s x - 1) ^ 2 = 256 * S4 := by
    have hexp2 : ∀ x : PauliIdx 4, (s x - 1) ^ 2 =
        ∑ p ∈ L.erase 0, ∑ q ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 * ((sympSign x q : ℝ) * (c q) ^ 2) := fun x => by
      rw [hs_wht x, add_sub_cancel_left, sq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun x _ => hexp2 x), Finset.sum_comm]
    have hswap : ∑ p ∈ L.erase 0, ∑ x : PauliIdx 4, ∑ q ∈ L.erase 0,
        (sympSign x p : ℝ) * (c p) ^ 2 * ((sympSign x q : ℝ) * (c q) ^ 2) =
        ∑ p ∈ L.erase 0, ∑ q ∈ L.erase 0,
          (∑ x : PauliIdx 4, (sympSign x (p + q) : ℝ)) * ((c p) ^ 2 * (c q) ^ 2) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sympSign_add_right]; push_cast; ring
    rw [hswap]
    have hdiag : ∀ p ∈ L.erase 0, ∑ q ∈ L.erase 0,
        (∑ x : PauliIdx 4, (sympSign x (p + q) : ℝ)) * ((c p) ^ 2 * (c q) ^ 2) = 256 * (c p) ^ 4 := by
      intro p hp
      rw [Finset.sum_eq_single p]
      · rw [pauliIdx_add_self, sum_sympSign_all]; simp; ring
      · intro q _ hqp
        have hne : p + q ≠ 0 := fun h => hqp (by
          have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this)
        rw [sum_sympSign_all]; simp [hne]
      · intro h; exact absurd hp h
    rw [Finset.sum_congr rfl hdiag, ← Finset.mul_sum]
  have hsum_out_2 : ∑ x ∈ Finset.univ \ L, (s x - 1) ^ 2 = 16 * (16 * S4 - S2 ^ 2) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ L)] at hsum_all_2
    have hin : ∑ x ∈ L, (s x - 1) ^ 2 = 16 * S2 ^ 2 := by
      have : ∀ x ∈ L, (s x - 1) ^ 2 = S2 ^ 2 := fun x hx => by rw [hs_in_L x hx]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard_L]
    linarith
  -- 4. Exact Pythagoras identity: `∑_{x ∉ L} (s x - 16 c_x²)² = 256 * (∑_{x ∉ L} c_x⁴) - 16 * ∑_{x ∉ L} s(x)²`!
  have hcross : ∑ x ∈ Finset.univ \ L, s x * (c x) ^ 2 = (1 / 16 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x) ^ 2 := by
    -- Since `s (x + q) = s x` for `q ∈ L`, summing over `q ∈ L` gives `16 * ∑_{x ∉ L} s x c_x² = ∑_{x ∉ L} s(x)²`!
    have hinv : ∀ x : PauliIdx 4, ∀ q ∈ L, s (x + q) = s x := fun x q hq => by
      simp only [s]
      refine Finset.sum_bij (fun r _ => q + r) ?_ ?_ ?_ ?_
      · intro r hr; exact hL.2.2.1 q hq r hr
      · intro a _ b _ h; have := congr_arg (q + ·) h; simpa [pauliIdx_add_cancel_left] using this
      · intro r hr; exact ⟨q + r, hL.2.2.1 q hq r hr, pauliIdx_add_cancel_left q r⟩
      · intro r _; rw [add_assoc]
    have hshift : ∀ q ∈ L, ∑ x ∈ Finset.univ \ L, s x * (c (x + q)) ^ 2 =
        ∑ x ∈ Finset.univ \ L, s x * (c x) ^ 2 := by
      intro q hq
      refine Finset.sum_bij (fun x _ => x + q) ?_ ?_ ?_ ?_
      · intro x hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => (Finset.mem_sdiff.mp hx).2 ?_⟩
        have := hL.2.2.1 _ hmem q hq; rwa [pauliIdx_add_cancel_right] at this
      · intro a _ b _ h; have := congr_arg (· + q) h; simpa [pauliIdx_add_cancel_right] using this
      · intro y hy
        refine ⟨y + q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => (Finset.mem_sdiff.mp hy).2 ?_⟩,
                pauliIdx_add_cancel_right y q⟩
        have := hL.2.2.1 _ hmem q hq; rwa [pauliIdx_add_cancel_right] at this
      · intro x _; rw [hinv x q hq]
    have hsum16 : ∑ q ∈ L, ∑ x ∈ Finset.univ \ L, s x * (c (x + q)) ^ 2 =
        16 * ∑ x ∈ Finset.univ \ L, s x * (c x) ^ 2 := by
      rw [Finset.sum_congr rfl hshift, Finset.sum_const, nsmul_eq_mul, hcard_L]
    rw [Finset.sum_comm] at hsum16
    have hlhs : ∑ x ∈ Finset.univ \ L, ∑ q ∈ L, s x * (c (x + q)) ^ 2 =
        ∑ x ∈ Finset.univ \ L, (s x) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum]; simp only [s, sq]
    linarith
  have hsum_s2 : ∑ x ∈ Finset.univ \ L, (s x) ^ 2 = 240 - 32 * S2 + 16 * (16 * S4 - S2 ^ 2) := by
    have hexp : ∑ x ∈ Finset.univ \ L, (s x - 1) ^ 2 =
        (∑ x ∈ Finset.univ \ L, (s x) ^ 2) - 2 * (∑ x ∈ Finset.univ \ L, (s x - 1)) -
        ((Finset.univ \ L).card : ℝ) := by
      have : ∀ x, (s x - 1) ^ 2 = (s x) ^ 2 - 2 * (s x - 1) - 1 := fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith [hexp, hcard_out, hsum_out_1, hsum_out_2]
  have h4out : ∑ x ∈ Finset.univ \ L, (c x) ^ 4 = pauliMoment4 4 ψ - 1 - S4 := by
    obtain ⟨_, hsum4⟩ := sum_sq_and_fourth_four hunit
    have hsub : L.erase 0 ⊆ Finset.univ.erase (0 : PauliIdx 4) := fun p hp =>
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hp).1, Finset.mem_univ _⟩
    have hsdiff : (Finset.univ.erase (0 : PauliIdx 4)) \ (L.erase 0) = Finset.univ \ L := by
      ext p; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨fun ⟨hp0, hn⟩ hpL => hn ⟨hp0, hpL⟩, fun hpL => ⟨fun h0 => hpL (h0 ▸ hL.1), fun ⟨_, h⟩ => hpL h⟩⟩
    have h := Finset.sum_sdiff hsub (f := fun p => (c p) ^ 4)
    rw [hsdiff] at h; linarith
  have hpyth : ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2 =
      256 * (pauliMoment4 4 ψ - 1 - S4) - ∑ x ∈ Finset.univ \ L, (s x) ^ 2 := by
    have hexp : ∀ x, (s x - 16 * (c x) ^ 2) ^ 2 = (s x) ^ 2 - 32 * (s x * (c x) ^ 2) + 256 * (c x) ^ 4 :=
      fun x => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith [hcross, h4out]
  refine ⟨hs_wht, hs_lb, hsum_out_1, hsum_out_2, ?_⟩
  linarith [hpyth, hsum_s2]

/-- **1-Line Self-Dual Pythagoras Bound (`val_D`)**:
    For ANY Lagrangian `L` and ANY single point `u ∉ L`,
      `pauliMoment4 4 ψ - 31/16 ≥ (2 S₄ - S₂/8 - S₂²/16) + (max(0, 1 - S₂ - 16 c_u²))² / 128`. -/
lemma val_D_le_excess {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ) {u : PauliIdx 4} (huL : u ∉ L) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
    let S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
    (2 * S4 - S2 / 8 - S2 ^ 2 / 16) + (max 0 (1 - S2 - 16 * (c u) ^ 2)) ^ 2 / 128 ≤
      pauliMoment4 4 ψ - 31 / 16 := by
  intro c S2 S4
  obtain ⟨hs_wht, hs_lb, _, _, hpyth⟩ := lagrangian_coset_identities hL hunit
  let s : PauliIdx 4 → ℝ := fun x => ∑ q ∈ L, (c (x + q)) ^ 2
  change ∀ x : PauliIdx 4, s x = 1 + ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 at hs_wht
  change ∀ x : PauliIdx 4, 1 - S2 ≤ s x at hs_lb
  change pauliMoment4 4 ψ - 31 / 16 = (2 * S4 - S2 / 8 - S2 ^ 2 / 16) + (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2 at hpyth
  let h : PauliIdx 4 → ℝ := fun x => if x ∈ L then 0 else s x - 16 * (c x) ^ 2
  have hh_coset_sum : ∀ a : PauliIdx 4, ∑ q ∈ L, h (a + q) = 0 := by
    intro a
    by_cases haL : a ∈ L
    · refine Finset.sum_eq_zero fun q hq => by simp [h, hL.2.2.1 a haL q hq]
    · have hout : ∀ q ∈ L, a + q ∉ L := fun q hq hmem => haL (by
        have := hL.2.2.1 _ hmem q hq; rwa [pauliIdx_add_cancel_right] at this)
      have hs_inv : ∀ q ∈ L, s (a + q) = s a := fun q hq => by
        rw [hs_wht (a + q), hs_wht a]
        refine congr_arg (1 + ·) (Finset.sum_congr rfl fun p hp => ?_)
        rw [sympSign_add_left]
        have : sympSign q p = 1 := by simp [sympSign, hL.2.2.2 q hq p (Finset.mem_erase.mp hp).2]
        rw [this, mul_one]
      have hterm : ∀ q ∈ L, h (a + q) = s a - 16 * (c (a + q)) ^ 2 := fun q hq => by
        simp only [h, hout q hq, ↓reduceIte, hs_inv q hq]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
      have hL16 : (L.card : ℝ) = 16 := by rw [hL.2.1]; norm_num
      rw [hL16]; simp only [s]; ring
  -- `W h = 16 h` at `u` (`∑_{x ∉ L} (-1)^{ω(u, x)} h(x) = 16 h(u)`)!
  have hWh_u : ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * h x = 16 * h u := by
    have hns : ∀ p : PauliIdx 4, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
      fun p => innerProd_pauliApply_self_normSq p ψ
    have hW_c2 : ∑ x : PauliIdx 4, (sympSign u x : ℝ) * (c x) ^ 2 = 16 * (c u) ^ 2 := by
      have hw := pauli_symp_self_dual ψ u
      have hcomm : ∀ x : PauliIdx 4, sympSign x u = sympSign u x := fun x => sympSign_comm x u
      simp_rw [hns, hcomm] at hw; norm_num at hw; exact hw
    have hW_c2_L : ∑ x ∈ L, (sympSign u x : ℝ) * (c x) ^ 2 = s u := by
      rw [← Finset.add_sum_erase _ _ hL.1, hs_wht u]
      have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
      have h0t : (sympSign u 0 : ℝ) * (c 0) ^ 2 = 1 := by simp [sympSign, symp_zero_right, hc0]
      rw [h0t]
    have hW_c2_out : ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * (c x) ^ 2 = 16 * (c u) ^ 2 - s u := by
      rw [← Finset.sum_sdiff (Finset.subset_univ L)] at hW_c2; linarith
    have hW_s_out : ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * s x = 0 := by
      -- Since `s` is constant on cosets of `L` and `u ∉ L`, `∑_{q ∈ L} sympSign u (x + q) = 0`!
      have h16 : 16 * ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * s x =
          ∑ q ∈ L, ∑ x ∈ Finset.univ \ L, (sympSign u (x + q) : ℝ) * s (x + q) := by
        have hsh : ∀ q ∈ L, ∑ x ∈ Finset.univ \ L, (sympSign u (x + q) : ℝ) * s (x + q) =
            ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * s x := fun q hq => by
          refine Finset.sum_bij (fun x _ => x + q) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro x hx
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => (Finset.mem_sdiff.mp hx).2 ?_⟩
            have := hL.2.2.1 _ hm q hq; rwa [pauliIdx_add_cancel_right] at this
          · intro a _ b _ he; have := congr_arg (· + q) he; simpa [pauliIdx_add_cancel_right] using this
          · intro y hy
            refine ⟨y + q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => (Finset.mem_sdiff.mp hy).2 ?_⟩,
                    pauliIdx_add_cancel_right y q⟩
            have := hL.2.2.1 _ hm q hq; rwa [pauliIdx_add_cancel_right] at this
        rw [Finset.sum_congr rfl hsh, Finset.sum_const, hL.2.1, nsmul_eq_mul]; norm_num
      rw [Finset.sum_comm] at h16
      have hzero : ∀ x ∈ Finset.univ \ L, ∑ q ∈ L, (sympSign u (x + q) : ℝ) * s (x + q) = 0 := by
        intro x _
        have hterm : ∀ q ∈ L, (sympSign u (x + q) : ℝ) * s (x + q) =
            (sympSign u q : ℝ) * ((sympSign u x : ℝ) * s x) := fun q hq => by
          rw [sympSign_add_right, hs_wht (x + q), hs_wht x]
          have hseq : ∑ p ∈ L.erase 0, (sympSign (x + q) p : ℝ) * (c p) ^ 2 =
              ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 :=
            Finset.sum_congr rfl fun p hp => by
              rw [sympSign_add_left]
              have : sympSign q p = 1 := by simp [sympSign, hL.2.2.2 q hq p (Finset.mem_erase.mp hp).2]
              rw [this, mul_one]
          rw [hseq]; push_cast; ring
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_sympSign_isoSub hL u]
        have hnot : ¬(∀ y ∈ L, symp u y = 0) := fun ha => huL ((lagrangian_perp_eq_and_card_anticomm hL).1 u |>.mp ha)
        split_ifs; ring
      rw [Finset.sum_eq_zero hzero] at h16; linarith
    have heq : ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * h x =
        ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * s x -
        16 * ∑ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * (c x) ^ 2 := by
      have hpt : ∀ x ∈ Finset.univ \ L, (sympSign u x : ℝ) * h x =
          (sympSign u x : ℝ) * s x - 16 * ((sympSign u x : ℝ) * (c x) ^ 2) := fun x hx => by
        simp only [h, (Finset.mem_sdiff.mp hx).2, ↓reduceIte]; ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq, hW_s_out, hW_c2_out]; simp only [h, huL, ↓reduceIte]; ring
  -- Explicit dual vector `v` on `Finset.univ \ L` with `⟨h, v⟩ = h u` and `∑ v² = 1/2`!
  let uL : Finset (PauliIdx 4) := L.image (u + ·)
  let v : PauliIdx 4 → ℝ := fun x =>
    (if x = u then (1 / 2 : ℝ) else 0) - (if x ∈ uL then (1 / 32 : ℝ) else 0) +
      (1 / 32 : ℝ) * (sympSign u x : ℝ)
  have huL_sub : uL ⊆ Finset.univ \ L := fun x hx => by
    obtain ⟨q, hqL, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => huL ?_⟩
    have := hL.2.2.1 _ hm q hqL; rwa [pauliIdx_add_cancel_right] at this
  have hinner : ∑ x ∈ Finset.univ \ L, h x * v x = h u := by
    have hpt : ∀ x ∈ Finset.univ \ L, h x * v x =
        (if x = u then (1 / 2 : ℝ) * h x else 0) -
        (if x ∈ uL then (1 / 32 : ℝ) * h x else 0) +
        (1 / 32 : ℝ) * ((sympSign u x : ℝ) * h x) := fun x _ => by
      simp only [v]; split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hWh_u]
    have ht1 : ∑ x ∈ Finset.univ \ L, (if x = u then (1 / 2 : ℝ) * h x else 0) = (1 / 2 : ℝ) * h u := by
      rw [Finset.sum_ite_eq']; simp [huL]
    have ht2 : ∑ x ∈ Finset.univ \ L, (if x ∈ uL then (1 / 32 : ℝ) * h x else 0) = 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr huL_sub,
          ← Finset.mul_sum]
      have himg : ∑ x ∈ uL, h x = ∑ q ∈ L, h (u + q) :=
        Finset.sum_image fun a _ b _ he => by
          have := congr_arg (u + ·) he; simpa [pauliIdx_add_cancel_left] using this
      rw [himg, hh_coset_sum u, mul_zero]
    rw [ht1, ht2]; ring
  have hv2 : ∑ x ∈ Finset.univ \ L, (v x) ^ 2 = 1 / 2 := by
    -- Compute `∑_{x ∈ univ \ L} v(x)² = 1/4 + (1/1024)*16 + (1/1024)*240 + 2*cross`!
    have hpt : ∀ x ∈ Finset.univ \ L, (v x) ^ 2 =
        (if x = u then (1 / 4 : ℝ) else 0) +
        (if x ∈ uL then (1 / 1024 : ℝ) else 0) +
        (1 / 1024 : ℝ) -
        (if x = u then (1 / 32 : ℝ) else 0) +
        (if x = u then (1 / 32 : ℝ) else 0) -
        (if x ∈ uL then (1 / 512 : ℝ) * (sympSign u x : ℝ) else 0) := by
      intro x _
      have hss2 : (sympSign u x : ℝ) ^ 2 = 1 := by simp only [sympSign]; split_ifs <;> norm_num
      have hu_in_uL : u ∈ uL := Finset.mem_image.mpr ⟨0, hL.1, by simp⟩
      have hss_u : (sympSign u u : ℝ) = 1 := by simp [sympSign, symp_self]
      by_cases hxu : x = u
      · subst hxu; simp only [v, ↓reduceIte, hu_in_uL, hss_u]; norm_num
      · by_cases hxuL : x ∈ uL
        · simp only [v, hxu, hxuL, ↓reduceIte]; nlinarith [hss2]
        · simp only [v, hxu, hxuL, ↓reduceIte]; nlinarith [hss2]
    rw [Finset.sum_congr rfl hpt]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard_out : ((Finset.univ \ L).card : ℝ) = 240 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, card_PauliIdx, hL.2.1]; norm_num
    have hcard_uL : (uL.card : ℝ) = 16 := by
      rw [Finset.card_image_of_injective L fun a b he => by
        have := congr_arg (u + ·) he; simpa [pauliIdx_add_cancel_left] using this, hL.2.1]; norm_num
    have h1 : ∑ x ∈ Finset.univ \ L, (if x = u then (1 / 4 : ℝ) else 0) = 1 / 4 := by
      rw [Finset.sum_ite_eq']; simp [huL]
    have h2 : ∑ x ∈ Finset.univ \ L, (if x ∈ uL then (1 / 1024 : ℝ) else 0) = 16 / 1024 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr huL_sub,
          Finset.sum_const, nsmul_eq_mul, hcard_uL]; ring
    have h3 : ∑ x ∈ Finset.univ \ L, (if x ∈ uL then (1 / 512 : ℝ) * (sympSign u x : ℝ) else 0) = 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr huL_sub,
          ← Finset.mul_sum]
      have himg : ∑ x ∈ uL, (sympSign u x : ℝ) = ∑ q ∈ L, (sympSign u q : ℝ) := by
        rw [Finset.sum_image fun a _ b _ he => by
          have := congr_arg (u + ·) he; simpa [pauliIdx_add_cancel_left] using this]
        refine Finset.sum_congr rfl fun q _ => by
          rw [sympSign_add_right]; simp [sympSign, symp_self]
      rw [himg, sum_sympSign_isoSub hL u]
      have hnot : ¬(∀ y ∈ L, symp u y = 0) := fun ha => huL ((lagrangian_perp_eq_and_card_anticomm hL).1 u |>.mp ha)
      split_ifs; ring
    rw [h1, h2, h3, hcard_out]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ \ L) h v
  rw [hinner, hv2] at hcs
  have hh_sq : ∑ x ∈ Finset.univ \ L, (h x) ^ 2 = ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by simp [h, (Finset.mem_sdiff.mp hx).2]
  rw [hh_sq] at hcs
  have hhu : h u = s u - 16 * (c u) ^ 2 := by simp [h, huL]
  have hmax_le : max 0 (1 - S2 - 16 * (c u) ^ 2) ^ 2 ≤ (h u) ^ 2 := by
    rw [hhu]
    by_cases hpos : 0 ≤ 1 - S2 - 16 * (c u) ^ 2
    · rw [max_eq_right hpos]
      have hge : 1 - S2 - 16 * (c u) ^ 2 ≤ s u - 16 * (c u) ^ 2 := by linarith [hs_lb u]
      nlinarith
    · rw [max_eq_left (le_of_not_ge hpos), zero_pow (by norm_num)]; exact sq_nonneg _
  linarith [hpyth, hcs, hmax_le]

set_option maxHeartbeats 400000 in
/-- **1-Line Coset-Deficit Bound (`val_A`)**:
    For ANY Lagrangian `L` with `S₂ < 1`, letting `q = √(1 - S₂)`,
      `pauliMoment4 4 ψ - 31/16 ≥ (2 S₄ - S₂/8 - S₂²/16) + (q³ / 32) * (60 - L_out - 2 S₂ - (2/(1+q)²)(16 S₄ - S₂²))`. -/
lemma val_A_le_excess {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ)
    (hS2_lt : ∑ p ∈ L.erase 0, ((innerProd ψ (pauliApply p ψ)).re) ^ 2 < 1) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
    let S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
    let Lout : ℝ := ∑ q ∈ Finset.univ \ L, |c q|
    let q : ℝ := Real.sqrt (1 - S2)
    (2 * S4 - S2 / 8 - S2 ^ 2 / 16) +
      (q ^ 3 / 32) * (60 - Lout - 2 * S2 - (2 / (1 + q) ^ 2) * (16 * S4 - S2 ^ 2)) ≤
      pauliMoment4 4 ψ - 31 / 16 := by
  intro c S2 S4 Lout q
  obtain ⟨hs_wht, hs_lb, hsum1, hsum2, hpyth⟩ := lagrangian_coset_identities hL hunit
  let s : PauliIdx 4 → ℝ := fun x => ∑ r ∈ L, (c (x + r)) ^ 2
  change ∀ x : PauliIdx 4, s x = 1 + ∑ p ∈ L.erase 0, (sympSign x p : ℝ) * (c p) ^ 2 at hs_wht
  change ∀ x : PauliIdx 4, 1 - S2 ≤ s x at hs_lb
  change ∑ x ∈ Finset.univ \ L, (s x - 1) = -16 * S2 at hsum1
  change ∑ x ∈ Finset.univ \ L, (s x - 1) ^ 2 = 16 * (16 * S4 - S2 ^ 2) at hsum2
  change pauliMoment4 4 ψ - 31 / 16 = (2 * S4 - S2 / 8 - S2 ^ 2 / 16) + (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2 at hpyth
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hq_sq : q ^ 2 = 1 - S2 := Real.sq_sqrt (by linarith)
  have hcard_out : ((Finset.univ \ L).card : ℝ) = 240 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L), Finset.card_univ, card_PauliIdx, hL.2.1]; norm_num
  -- Pointwise on each `x ∉ L`: `(s x - 16 c_x²)² = 256 (c_x² - s x / 16)² ≥ 16 s(x) (|c_x| - √(s x)/4)²`!
  -- Summing over `x ∉ L`, since `s x ≥ 1 - S2 = q²`:
  --   `(1/256) ∑_{x ∉ L} (s x - 16 c_x²)² ≥ (q³ / 512) ∑_{x ∉ L} (4 √(s x) - 16 |c_x|)`?
  -- Check exact scaling (each coset appears 16 times in `x ∉ L`!):
  --   `∑_{x ∉ L} (|c_x| - √(s x)/4)² = ∑_{x ∉ L} (c_x² - (√(s x)/2)|c_x| + s(x)/16)`
  --   And `∑_{x ∉ L} √(s x) |c_x| = (1/16) ∑_{x ∉ L} √(s x) L_{x+L}`!
  --   EVEN SIMPLER (direct pointwise inequality, ZERO coset sum needed!!):
  --   For every `x ∉ L`, let `m := √(s x) / 4 > 0`. Then:
  --     `(s x - 16 c_x²)² / 256 = (c_x² - m²)² = (|c_x| - m)² (|c_x| + m)² ≥ m² (|c_x| - m)²`
  --     `= (s x / 16) * (c_x² - 2 m |c_x| + m²)`
  --     Wait: `s x / 16 ≥ q² / 16` and `m = √(s x)/4 ≥ q / 4`,
  --     actually `m³ = s(x)^(3/2) / 64`, and on each coset `∑_{r ∈ L} (|c_{x+r}| - m)² = 2 m (4 √(s x) - L_{x+L})`,
  --     Wait: `∑_{x ∉ L} s(x) * c_x² = (1/16) ∑_{x ∉ L} s(x)²`!
  --     Let's multiply by `q / √(s x) ≤ 1` FIRST:
  --     `m² (|c_x| - m)² = (s x / 16) (|c_x| - √(s x)/4)² ≥ (q³ / 16) * (1 / √(s x)) * (|c_x| - √(s x)/4)²`?
  --     NO! Even simpler: `m² = (s x / 16) = (√(s x) / 16) * √(s x) ≥ (q / 16) * √(s x)`!
  --     Wait: for `s x ≥ q²`: `√(s x) ≥ q`, so `m² = s(x)/16 = (s(x) / (16 √(s x))) * √(s x) = (√(s x) / 16) * √(s x)`!
  --     We want `(q³ / 32) * (∑_{x ∉ L} (4 √(s x) / 16) - ∑_{x ∉ L} |c_x|)`!
  --     Check! Let `L_x := ∑_{r ∈ L} |c_{x + r}|`!
  --     Since `s(x + r) = s x` for `r ∈ L`:
  --       `∑_{x ∉ L} (s x - 16 c_x²)² / 256 = (1/16) ∑_{x ∉ L} ∑_{r ∈ L} (c_{x+r}² - m_x²)²`
  --       `≥ (1/16) ∑_{x ∉ L} (s x / 16) * ∑_{r ∈ L} (|c_{x+r}| - m_x)²`
  --       `= (1/16) ∑_{x ∉ L} (s x / 16) * (2 s x - (√(s x) / 2) L_x)`
  --       `= (1/16) ∑_{x ∉ L} (s(x)^(3/2) / 32) * (4 √(s x) - L_x)`!
  --     AND BY CAUCHY–SCHWARZ ON `L`, `L_x ≤ 4 √(s x)` ALWAYS (SO `4 √(s x) - L_x ≥ 0` ALWAYS!!)!
  --     Therefore `s(x)^(3/2) ≥ q³` gives:
  --       `≥ (1/16) * (q³ / 32) * ∑_{x ∉ L} (4 √(s x) - L_x) = (q³ / 32) * ((1/4) ∑_{x ∉ L} √(s x) - Lout)`!!
  have hs_pos : ∀ x : PauliIdx 4, 0 < s x := fun x => by linarith [hs_lb x]
  have hshift_sum : ∀ f : PauliIdx 4 → ℝ,
      ∑ x ∈ Finset.univ \ L, ∑ r ∈ L, f (x + r) = 16 * ∑ x ∈ Finset.univ \ L, f x := by
    intro f
    rw [Finset.sum_comm]
    have hsh : ∀ r ∈ L, ∑ x ∈ Finset.univ \ L, f (x + r) = ∑ x ∈ Finset.univ \ L, f x := fun r hr => by
      refine Finset.sum_bij (fun x _ => x + r) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => (Finset.mem_sdiff.mp hx).2 ?_⟩
        have := hL.2.2.1 _ hm r hr; rwa [pauliIdx_add_cancel_right] at this
      · intro a _ b _ he; have := congr_arg (· + r) he; simpa [pauliIdx_add_cancel_right] using this
      · intro y hy
        refine ⟨y + r, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hm => (Finset.mem_sdiff.mp hy).2 ?_⟩,
                pauliIdx_add_cancel_right y r⟩
        have := hL.2.2.1 _ hm r hr; rwa [pauliIdx_add_cancel_right] at this
    rw [Finset.sum_congr rfl hsh, Finset.sum_const, hL.2.1, nsmul_eq_mul]; norm_num
  have hs_inv : ∀ x : PauliIdx 4, ∀ r ∈ L, s (x + r) = s x := fun x r hr => by
    rw [hs_wht (x + r), hs_wht x]
    refine congr_arg (1 + ·) (Finset.sum_congr rfl fun p hp => ?_)
    rw [sympSign_add_left]
    have : sympSign r p = 1 := by simp [sympSign, hL.2.2.2 r hr p (Finset.mem_erase.mp hp).2]
    rw [this, mul_one]
  -- Lower bound `∑_{x ∉ L} (s x - 16 c_x²)² / 256 ≥ (q³ / 32) * ((1/4) ∑_{x ∉ L} √(s x) - Lout)`!
  have hcoset_lb : (q ^ 3 / 32) * ((1 / 4 : ℝ) * ∑ x ∈ Finset.univ \ L, Real.sqrt (s x) - Lout) ≤
      (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2 := by
    have h16 := hshift_sum (fun x => (s x - 16 * (c x) ^ 2) ^ 2)
    have hpt : ∀ x ∈ Finset.univ \ L,
        16 * (q ^ 3 / 32) * (4 * Real.sqrt (s x) - ∑ r ∈ L, |c (x + r)|) ≤
        (1 / 256 : ℝ) * ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 * 16 := by
      intro x _
      let m : ℝ := Real.sqrt (s x) / 4
      have hsq_pos : 0 < Real.sqrt (s x) := Real.sqrt_pos.mpr (hs_pos x)
      have hm_pos : 0 < m := by simp only [m]; positivity
      have hm2 : m ^ 2 = s x / 16 := by
        simp only [m, div_pow, Real.sq_sqrt (le_of_lt (hs_pos x))]; ring
      have hterm : ∀ r ∈ L,
          m ^ 2 * (|c (x + r)| - m) ^ 2 ≤ (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 / 256 := by
        intro r hr
        rw [hs_inv x r hr]
        have hfac : (s x - 16 * (c (x + r)) ^ 2) ^ 2 / 256 =
            (|c (x + r)| - m) ^ 2 * (|c (x + r)| + m) ^ 2 := by
          have habs : |c (x + r)| ^ 2 = (c (x + r)) ^ 2 := sq_abs _
          calc (s x - 16 * (c (x + r)) ^ 2) ^ 2 / 256
              = ((c (x + r)) ^ 2 - s x / 16) ^ 2 := by ring
            _ = (|c (x + r)| ^ 2 - m ^ 2) ^ 2 := by rw [habs, hm2]
            _ = (|c (x + r)| - m) ^ 2 * (|c (x + r)| + m) ^ 2 := by ring
        rw [hfac]
        have hge : m ^ 2 ≤ (|c (x + r)| + m) ^ 2 := by nlinarith [abs_nonneg (c (x + r)), hm_pos]
        nlinarith [sq_nonneg (|c (x + r)| - m)]
      have hsum_r := Finset.sum_le_sum hterm
      rw [← Finset.mul_sum, ← Finset.sum_div] at hsum_r
      have hdev : ∑ r ∈ L, (|c (x + r)| - m) ^ 2 =
          (Real.sqrt (s x) / 2) * (4 * Real.sqrt (s x) - ∑ r ∈ L, |c (x + r)|) := by
        have hsq : ∀ r ∈ L, (|c (x + r)| - m) ^ 2 = (c (x + r)) ^ 2 - 2 * m * |c (x + r)| + m ^ 2 :=
          fun r _ => by nlinarith [sq_abs (c (x + r))]
        rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        have hL16 : (L.card : ℝ) = 16 := by rw [hL.2.1]; norm_num
        have hss : ∑ r ∈ L, (c (x + r)) ^ 2 = s x := rfl
        rw [hL16, hss, hm2]
        have hsq_s : Real.sqrt (s x) * Real.sqrt (s x) = s x := Real.mul_self_sqrt (le_of_lt (hs_pos x))
        simp only [m]; nlinarith [hsq_s]
      have hgap_nn : 0 ≤ 4 * Real.sqrt (s x) - ∑ r ∈ L, |c (x + r)| := by
        have hnn : 0 ≤ ∑ r ∈ L, (|c (x + r)| - m) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        rw [hdev] at hnn
        have hsp : 0 < Real.sqrt (s x) / 2 := by positivity
        nlinarith
      have hq3_le : q ^ 3 ≤ Real.sqrt (s x) ^ 3 :=
        pow_le_pow_left₀ (le_of_lt hq_pos) (Real.sqrt_le_sqrt (hs_lb x)) 3
      have hm2_eq : m ^ 2 * (Real.sqrt (s x) / 2) = Real.sqrt (s x) ^ 3 / 32 := by
        have hsq_s : Real.sqrt (s x) ^ 2 = s x := Real.sq_sqrt (le_of_lt (hs_pos x))
        calc m ^ 2 * (Real.sqrt (s x) / 2) = (s x / 16) * (Real.sqrt (s x) / 2) := by rw [hm2]
          _ = (Real.sqrt (s x) ^ 2 / 16) * (Real.sqrt (s x) / 2) := by rw [hsq_s]
          _ = Real.sqrt (s x) ^ 3 / 32 := by ring
      rw [hdev, ← mul_assoc, hm2_eq] at hsum_r
      have h1 : (q ^ 3 / 32) * (4 * Real.sqrt (s x) - ∑ r ∈ L, |c (x + r)|) ≤
          (Real.sqrt (s x) ^ 3 / 32) * (4 * Real.sqrt (s x) - ∑ r ∈ L, |c (x + r)|) :=
        mul_le_mul_of_nonneg_right (by linarith) hgap_nn
      have h2 : ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 * 16 =
          16 * ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      rw [h2]; linarith
    have hsum := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hshift_sum (fun x => |c x|)] at hsum
    have hrhs : ∑ x ∈ Finset.univ \ L, (1 / 256 : ℝ) * ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 * 16 =
        16 * ((1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L, (s x - 16 * (c x) ^ 2) ^ 2) * 16 := by
      rw [← Finset.mul_sum]
      have hinner : ∑ x ∈ Finset.univ \ L, ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2 * 16 =
          (∑ x ∈ Finset.univ \ L, ∑ r ∈ L, (s (x + r) - 16 * (c (x + r)) ^ 2) ^ 2) * 16 := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
      rw [hinner, h16]; ring
    rw [hrhs] at hsum
    have : 16 * ((q ^ 3 / 32) * ((1 / 4 : ℝ) * ∑ x ∈ Finset.univ \ L, Real.sqrt (s x) - Lout)) =
        (1 / 16 : ℝ) * (16 * (q ^ 3 / 32) * (4 * ∑ x ∈ Finset.univ \ L, Real.sqrt (s x) - 16 * Lout)) := by ring
    linarith
  -- Elementary 2-line algebraic lower bound on `√(s x)`:
  --   `1 + (s x - 1)/2 - √(s x) = (s x - 1)² / (4 (1 + (s x - 1)/2 + √(s x))) ≤ (s x - 1)² / (2 (1 + q)²)`!
  have hsqrt_lb : ∀ x ∈ Finset.univ \ L,
      1 + (s x - 1) / 2 - (s x - 1) ^ 2 / (2 * (1 + q) ^ 2) ≤ Real.sqrt (s x) := by
    intro x _
    have hsx_ge : q ^ 2 ≤ s x := by rw [hq_sq]; exact hs_lb x
    have hrx_ge : q ≤ Real.sqrt (s x) := by rw [← Real.sqrt_sq (le_of_lt hq_pos)]; exact Real.sqrt_le_sqrt hsx_ge
    have hden_ge : (1 + q) ^ 2 / 2 ≤ 1 + (s x - 1) / 2 + Real.sqrt (s x) := by nlinarith [hsx_ge, hrx_ge]
    have hden_pos : 0 < 1 + (s x - 1) / 2 + Real.sqrt (s x) := by nlinarith [hq_pos, hden_ge]
    have hid : (1 + (s x - 1) / 2 - Real.sqrt (s x)) * (1 + (s x - 1) / 2 + Real.sqrt (s x)) =
        (s x - 1) ^ 2 / 4 := by
      have hsq : Real.sqrt (s x) ^ 2 = s x := Real.sq_sqrt (le_of_lt (hs_pos x))
      nlinarith [hsq]
    have h1q_pos : 0 < 2 * (1 + q) ^ 2 := by positivity
    rw [sub_le_iff_le_add', ← sub_le_iff_le_add]
    have hmul : (1 + (s x - 1) / 2 - Real.sqrt (s x)) * (2 * (1 + q) ^ 2) ≤ (s x - 1) ^ 2 := by
      have hnn : 0 ≤ 1 + (s x - 1) / 2 - Real.sqrt (s x) := by
        nlinarith [hid, hden_pos, sq_nonneg (s x - 1)]
      have hle := mul_le_mul_of_nonneg_left hden_ge hnn
      linarith
    exact (le_div_iff₀ h1q_pos).mpr hmul
  have hsum_sqrt := Finset.sum_le_sum hsqrt_lb
  have hsum_lhs : ∑ x ∈ Finset.univ \ L, (1 + (s x - 1) / 2 - (s x - 1) ^ 2 / (2 * (1 + q) ^ 2)) =
      240 + (-16 * S2) / 2 - (16 * (16 * S4 - S2 ^ 2)) / (2 * (1 + q) ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        hcard_out, ← Finset.sum_div, hsum1, ← Finset.sum_div, hsum2]
  rw [hsum_lhs] at hsum_sqrt
  have hD_le : 60 - Lout - 2 * S2 - (2 / (1 + q) ^ 2) * (16 * S4 - S2 ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x ∈ Finset.univ \ L, Real.sqrt (s x) - Lout := by
    have h1 : 60 - 2 * S2 - (2 / (1 + q) ^ 2) * (16 * S4 - S2 ^ 2) =
        (1 / 4 : ℝ) * (240 + (-16 * S2) / 2 - (16 * (16 * S4 - S2 ^ 2)) / (2 * (1 + q) ^ 2)) := by
      field_simp [ne_of_gt (show (0 : ℝ) < 1 + q by linarith)]; ring
    linarith
  have hmul_q : (q ^ 3 / 32) * (60 - Lout - 2 * S2 - (2 / (1 + q) ^ 2) * (16 * S4 - S2 ^ 2)) ≤
      (q ^ 3 / 32) * ((1 / 4 : ℝ) * ∑ x ∈ Finset.univ \ L, Real.sqrt (s x) - Lout) :=
    mul_le_mul_of_nonneg_left hD_le (by positivity)
  linarith only [hpyth, hcoset_lb, hmul_q]

/-- **Pure-Polynomial `SMAX_K0 = 848 / 10000` Contradiction (`k = 0` free points in `L`)**:
    Under `L_out ≤ 594918/10000` and `F₄ ≤ 31/16`, NO Lagrangian can have `S₂(L) ≤ 848/10000`. -/
lemma smax_k0_contra {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ)
    (hLout : ∑ q ∈ Finset.univ \ L, |(innerProd ψ (pauliApply q ψ)).re| ≤ (594918 / 10000 : ℝ))
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (hS2 : ∑ p ∈ L.erase 0, ((innerProd ψ (pauliApply p ψ)).re) ^ 2 ≤ (848 / 10000 : ℝ)) :
    False := by
  set c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
  set S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
  obtain ⟨hsum2, hsum4⟩ := sum_sq_and_fourth_four hunit
  obtain ⟨_, _, h2out⟩ := lagrangian_quartic_mub_identities hL hunit
  dsimp only at hsum2 hsum4 h2out
  have h4out : ∑ q ∈ Finset.univ \ L, (c q) ^ 4 ≤ 15 / 16 := by
    have hsub : L.erase 0 ⊆ Finset.univ.erase (0 : PauliIdx 4) := fun p hp =>
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hp).1, Finset.mem_univ _⟩
    have hsdiff : (Finset.univ.erase (0 : PauliIdx 4)) \ (L.erase 0) = Finset.univ \ L := by
      ext p; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨fun ⟨hp0, hn⟩ hpL => hn ⟨hp0, hpL⟩, fun hpL => ⟨fun h0 => hpL (h0 ▸ hL.1), fun ⟨_, h⟩ => hpL h⟩⟩
    have h := Finset.sum_sdiff hsub (f := fun p => (c p) ^ 4)
    rw [hsdiff] at h
    have hS4_nn : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  -- Hölder `(∑ c_q²)³ ≤ (∑ c_q⁴) * (∑ |c_q|)²` via 2-step Cauchy–Schwarz!
  have hcs1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ \ L)
    (fun q => Real.sqrt |c q|) (fun q => Real.sqrt |c q| * |c q|)
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ \ L)
    (fun q => |c q|) (fun q => (c q) ^ 2)
  have hl1 : ∀ q, Real.sqrt |c q| * (Real.sqrt |c q| * |c q|) = (c q) ^ 2 := fun q => by
    calc Real.sqrt |c q| * (Real.sqrt |c q| * |c q|) = (Real.sqrt |c q| * Real.sqrt |c q|) * |c q| := by ring
      _ = |c q| * |c q| := by rw [Real.mul_self_sqrt (abs_nonneg _)]
      _ = |c q| ^ 2 := by ring
      _ = (c q) ^ 2 := sq_abs (c q)
  have hl2 : ∀ q, Real.sqrt |c q| ^ 2 = |c q| := fun q => Real.sq_sqrt (abs_nonneg _)
  have hl3 : ∀ q, (Real.sqrt |c q| * |c q|) ^ 2 = |c q| * (c q) ^ 2 := fun q => by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
  have hl4 : ∀ q, ((c q) ^ 2) ^ 2 = (c q) ^ 4 := fun q => by ring
  simp_rw [hl1, hl2, hl3, sq_abs, hl4] at hcs1 hcs2
  have hholder : (∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 3 ≤
      (∑ q ∈ Finset.univ \ L, (c q) ^ 4) * (∑ q ∈ Finset.univ \ L, |c q|) ^ 2 := by
    have hnn1 : 0 ≤ ∑ q ∈ Finset.univ \ L, (c q) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hnnL : 0 ≤ ∑ q ∈ Finset.univ \ L, |c q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hmul : ((∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 2) ^ 2 ≤
        ((∑ q ∈ Finset.univ \ L, |c q|) * (∑ q ∈ Finset.univ \ L, |c q| * (c q) ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hcs1 2
    have h4 : (∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 4 ≤
        (∑ q ∈ Finset.univ \ L, |c q|) ^ 2 *
        ((∑ q ∈ Finset.univ \ L, (c q) ^ 2) * (∑ q ∈ Finset.univ \ L, (c q) ^ 4)) := by
      calc (∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 4
          = ((∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ (∑ q ∈ Finset.univ \ L, |c q|) ^ 2 * (∑ q ∈ Finset.univ \ L, |c q| * (c q) ^ 2) ^ 2 := by
            rw [← mul_pow]; exact hmul
        _ ≤ _ := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
    have hpos : 0 < ∑ q ∈ Finset.univ \ L, (c q) ^ 2 := by linarith [h2out, hS2]
    nlinarith
  have h15_ge : (15 - 848 / 10000 : ℝ) ≤ ∑ q ∈ Finset.univ \ L, (c q) ^ 2 := by linarith [h2out, hS2]
  have hcub : (15 - 848 / 10000 : ℝ) ^ 3 ≤ (∑ q ∈ Finset.univ \ L, (c q) ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h15_ge 3
  have hLout_sq : (∑ q ∈ Finset.univ \ L, |c q|) ^ 2 ≤ (594918 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hLout 2
  have hprod : (∑ q ∈ Finset.univ \ L, (c q) ^ 4) * (∑ q ∈ Finset.univ \ L, |c q|) ^ 2 ≤
      (15 / 16 : ℝ) * (594918 / 10000 : ℝ) ^ 2 :=
    mul_le_mul h4out hLout_sq (sq_nonneg _) (by norm_num)
  have hnum : (15 / 16 : ℝ) * (594918 / 10000 : ℝ) ^ 2 < (15 - 848 / 10000 : ℝ) ^ 3 := by norm_num
  linarith

/-- Helper: pure-polynomial lower bound on `val_A` (eliminating `√(1 - S₂)` in 1 line!). -/
private lemma val_A_poly_lb {L : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    {ψ : QState 4} (hunit : IsUnitState ψ)
    (hLout : ∑ q ∈ Finset.univ \ L, |(innerProd ψ (pauliApply q ψ)).re| ≤ (594918 / 10000 : ℝ))
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (hS2_le : ∑ p ∈ L.erase 0, ((innerProd ψ (pauliApply p ψ)).re) ^ 2 ≤ 254 / 1000) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
    let S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
    (7 / 4 + S2 / 4) * S4 - S2 / 8 - S2 ^ 2 / 16 +
      ((1 - (3 / 2) * S2 + (3 / 10) * S2 ^ 2) / 32) * (5082 / 10000 - 2 * S2) +
      ((1 - (3 / 2) * S2 + (3 / 10) * S2 ^ 2) / 64) * S2 ^ 2 ≤ 0 := by
  intro c S2 S4
  have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS4_nn : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => by positivity
  have hvA := val_A_le_excess hL hunit (by linarith : S2 < 1)
  dsimp only at hvA
  set q : ℝ := Real.sqrt (1 - S2)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hq_le1 : q ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hq_sq : q ^ 2 = 1 - S2 := Real.sq_sqrt (by linarith)
  -- `q ≥ 1 - S2/2 - S2²/5`, so `q³ = (1 - S2) q ≥ 1 - (3/2) S2 + (3/10) S2²`!
  have hq_lb : 1 - S2 / 2 - S2 ^ 2 / 5 ≤ q := by
    rw [Real.le_sqrt (by nlinarith) (by linarith)]
    have hfac : 1 - S2 - (1 - S2 / 2 - S2 ^ 2 / 5) ^ 2 = S2 ^ 2 * (3 / 20 - S2 / 5 - S2 ^ 2 / 25) := by ring
    have hpos : 0 ≤ 3 / 20 - S2 / 5 - S2 ^ 2 / 25 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg S2) hpos
    linarith
  have hq3_lb : 1 - (3 / 2 : ℝ) * S2 + (3 / 10) * S2 ^ 2 ≤ q ^ 3 := by
    have h1 : (1 - S2) * (1 - S2 / 2 - S2 ^ 2 / 5) ≤ (1 - S2) * q :=
      mul_le_mul_of_nonneg_left hq_lb (by linarith)
    have h2 : q ^ 3 = (1 - S2) * q := by nlinarith [hq_sq]
    nlinarith [sq_nonneg S2]
  -- `q³ / (1 + q)² ≤ (1 - S2) / 4` (since `(1 + q)² ≥ 4 q`) and `q³ / (1 + q)² ≥ q³ / 4` (since `1 + q ≤ 2`)!
  have hr_ub : q ^ 3 / (1 + q) ^ 2 ≤ (1 - S2) / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : 4 * q ≤ (1 + q) ^ 2 := by nlinarith [sq_nonneg (1 - q)]
    nlinarith [hq_sq, hq_pos]
  have hr_lb : q ^ 3 / 4 ≤ q ^ 3 / (1 + q) ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (1 + q) ^ 2 ≤ 4 := by nlinarith [hq_le1, hq_pos]
    nlinarith [pow_nonneg (le_of_lt hq_pos) 3]
  have hgap_ge : 5082 / 10000 - 2 * S2 ≤ 60 - (∑ x ∈ Finset.univ \ L, |c x|) - 2 * S2 := by linarith
  have hgap_nn : 0 ≤ 5082 / 10000 - 2 * S2 := by linarith
  have hvA_rew : (2 * S4 - S2 / 8 - S2 ^ 2 / 16) +
      (q ^ 3 / 32) * (60 - (∑ x ∈ Finset.univ \ L, |c x|) - 2 * S2 - (2 / (1 + q) ^ 2) * (16 * S4 - S2 ^ 2)) =
      (2 - q ^ 3 / (1 + q) ^ 2) * S4 - S2 / 8 - S2 ^ 2 / 16 +
      (q ^ 3 / 32) * (60 - (∑ x ∈ Finset.univ \ L, |c x|) - 2 * S2) +
      (q ^ 3 / (1 + q) ^ 2) / 16 * S2 ^ 2 := by ring
  rw [hvA_rew] at hvA
  have h1 : (7 / 4 + S2 / 4) * S4 ≤ (2 - q ^ 3 / (1 + q) ^ 2) * S4 :=
    mul_le_mul_of_nonneg_right (by linarith) hS4_nn
  have h2 : ((1 - (3 / 2) * S2 + (3 / 10) * S2 ^ 2) / 32) * (5082 / 10000 - 2 * S2) ≤
      (q ^ 3 / 32) * (60 - (∑ x ∈ Finset.univ \ L, |c x|) - 2 * S2) :=
    mul_le_mul (by linarith) hgap_ge hgap_nn (by positivity)
  have h3 : ((1 - (3 / 2) * S2 + (3 / 10) * S2 ^ 2) / 64) * S2 ^ 2 ≤
      (q ^ 3 / (1 + q) ^ 2) / 16 * S2 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg S2)
  linarith

/-- **Pure-Polynomial `SMAX_K1 = 47 / 1000` Contradiction (`k = 1` free point in `L`)**:
    If `T ⊆ L.erase 0` has `|L.erase 0 \ T| ≤ 1` and `∑_{p ∈ T} c_p² ≤ 47/1000`, then `False`. -/
lemma smax_k1_contra {L T : Finset (PauliIdx 4)} (hL : IsLagrangian L) (hT : T ⊆ L.erase 0)
    (hk : (L.erase 0 \ T).card ≤ 1)
    {ψ : QState 4} (hunit : IsUnitState ψ)
    (hLout : ∑ q ∈ Finset.univ \ L, |(innerProd ψ (pauliApply q ψ)).re| ≤ (594918 / 10000 : ℝ))
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (hs_in : ∑ p ∈ T, ((innerProd ψ (pauliApply p ψ)).re) ^ 2 ≤ (47 / 1000 : ℝ)) :
    False := by
  set c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set s_in : ℝ := ∑ p ∈ T, (c p) ^ 2
  set a : ℝ := ∑ p ∈ L.erase 0 \ T, (c p) ^ 2
  set S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
  set S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
  have hS2_eq : S2 = s_in + a := by
    have h := Finset.sum_sdiff hT (f := fun p => (c p) ^ 2); linarith
  have hs_nn : 0 ≤ s_in := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha_nn : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc4_nn : ∀ p : PauliIdx 4, 0 ≤ (c p) ^ 4 := fun p => by
    have : (c p) ^ 4 = ((c p) ^ 2) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  have hS4_ge : a ^ 2 ≤ S4 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (L.erase 0 \ T) (fun _ => (1 : ℝ)) (fun p => (c p) ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hcard_le : ((L.erase 0 \ T).card : ℝ) ≤ 1 := by exact_mod_cast hk
    have h4eq : ∀ p, ((c p) ^ 2) ^ 2 = (c p) ^ 4 := fun p => by ring
    simp_rw [h4eq] at hcs
    have hsub : ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 ≤ S4 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p _ _ => hc4_nn p
    have hsum_nn : 0 ≤ ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 := Finset.sum_nonneg fun p _ => hc4_nn p
    have h1 : ((L.erase 0 \ T).card : ℝ) * ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 ≤ 1 * S4 :=
      mul_le_mul hcard_le hsub hsum_nn (by norm_num)
    linarith
  by_cases ha_big : (14 / 100 : ℝ) ≤ a
  · obtain ⟨_, _, _, _, hpyth⟩ := lagrangian_coset_identities hL hunit
    dsimp only at hpyth
    have hnn : 0 ≤ (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L,
        ((∑ q ∈ L, (c (x + q)) ^ 2) - 16 * (c x) ^ 2) ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hquad_le : 2 * S4 - S2 / 8 - S2 ^ 2 / 16 ≤ 0 := by linarith
    have hpos : 0 < 2 * a ^ 2 - (s_in + a) / 8 - (s_in + a) ^ 2 / 16 :=
      by nlinarith only [ha_big, hs_in, hs_nn, ha_nn]
    rw [← hS2_eq] at hpos; linarith
  · push Not at ha_big
    have hpoly := val_A_poly_lb hL hunit hLout hF4 (by linarith : S2 ≤ 254 / 1000)
    dsimp only at hpoly
    -- `S2 ≤ 0.047 + a` and RHS is decreasing in `S2` (at fixed `S4 ≥ a²`)!
    -- Verify directly by explicit polynomial SOS in `(a, s_in)`!
    have hS2_le_s : S2 ≤ 47 / 1000 + a := by linarith
    have hS2_nn : 0 ≤ S2 := by linarith
    have hmon : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 254 / 1000 →
        (7 / 4 + y / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 ≤
        (7 / 4 + x / 4) * a ^ 2 - x / 8 - x ^ 2 / 16 +
        ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 32) * (5082 / 10000 - 2 * x) +
        ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 64) * x ^ 2 := by
      intro x y hx hxy hy
      -- Difference factored by `(y - x)`: derivative wrt `S2` is `< -0.15` on `[0, 0.254]`!
      have hdiff : ((7 / 4 + x / 4) * a ^ 2 - x / 8 - x ^ 2 / 16 +
          ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 32) * (5082 / 10000 - 2 * x) +
          ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 64) * x ^ 2) -
          ((7 / 4 + y / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2) =
          (y - x) * (1 / 8 - a ^ 2 / 4 + (3 * 5082 / 640000) + 1 / 16 +
            (x + y) * (-82623 / 1600000) +
            (x ^ 2 + x * y + y ^ 2) * (3 / 160 + 3 / 128) -
            (x + y) * (x ^ 2 + y ^ 2) * (3 / 640)) := by ring
      have ha2_le : a ^ 2 ≤ (14 / 100 : ℝ) ^ 2 := by nlinarith only [ha_nn, ha_big]
      have hxy_sum : x + y ≤ 508 / 1000 := by linarith
      have hxy2 : x ^ 2 + y ^ 2 ≤ 2 * (254 / 1000 : ℝ) ^ 2 := by nlinarith only [hx, hxy, hy]
      have hxy3 : (x + y) * (x ^ 2 + y ^ 2) ≤ (508 / 1000 : ℝ) * (2 * (254 / 1000 : ℝ) ^ 2) :=
        mul_le_mul hxy_sum hxy2 (by positivity) (by norm_num)
      have hxy_nn : 0 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx (le_trans hx hxy)]
      have hpos_f : 0 ≤ 1 / 8 - a ^ 2 / 4 + (3 * 5082 / 640000) + 1 / 16 +
            (x + y) * (-82623 / 1600000) +
            (x ^ 2 + x * y + y ^ 2) * (3 / 160 + 3 / 128) -
            (x + y) * (x ^ 2 + y ^ 2) * (3 / 640) := by linarith
      have hmul := mul_nonneg (sub_nonneg.mpr hxy) hpos_f
      linarith
    have hplug := hmon S2 (47 / 1000 + a) hS2_nn hS2_le_s (by linarith)
    have hS4_step : (7 / 4 + S2 / 4) * a ^ 2 ≤ (7 / 4 + S2 / 4) * S4 :=
      mul_le_mul_of_nonneg_left hS4_ge (by linarith)
    -- Now 1-variable degree-4 polynomial in `a ∈ [0, 0.14]` with min `+0.000185 > 0` at `a ≈ 0.0566`!
    -- Lower-bound the degree-3/4 terms linearly on `[0, 0.14]` (`y = 0.047 + a ∈ [0.047, 0.187]`)!
    set y : ℝ := 47 / 1000 + a with hy_eq
    have hy_lo : (47 / 1000 : ℝ) ≤ y := by linarith
    have hy_hi : y ≤ 187 / 1000 := by linarith
    have hP_pos : 0 < (7 / 4 + y / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 := by
      have hy4_nn : 0 ≤ y ^ 4 := by
        have : y ^ 4 = (y ^ 2) ^ 2 := by ring
        rw [this]; exact sq_nonneg _
      have hrem : (7 / 4 + y / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 =
          (7 / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          (1 / 32 - (3 / 64) * y + (3 / 320) * y ^ 2) * (5082 / 10000) -
          (1 / 16) * y + (7 / 64) * y ^ 2 +
          (a ^ 2 / 4) * y - (27 / 640) * y ^ 3 + (3 / 640) * y ^ 4 := by ring
      have hy3_ub : y ^ 3 ≤ 3 * (1036 / 10000 : ℝ) ^ 2 * y - 2 * (1036 / 10000 : ℝ) ^ 3 +
          (187 / 1000 + 2 * (1036 / 10000)) * (y - 1036 / 10000) ^ 2 := by
        have hfac : y ^ 3 - (3 * (1036 / 10000 : ℝ) ^ 2 * y - 2 * (1036 / 10000 : ℝ) ^ 3) =
            (y - 1036 / 10000) ^ 2 * (y + 2 * (1036 / 10000)) := by ring
        have hle := mul_le_mul_of_nonneg_left (show y + 2 * (1036 / 10000 : ℝ) ≤ 187 / 1000 + 2 * (1036 / 10000) by linarith)
          (sq_nonneg (y - 1036 / 10000))
        linarith
      have ha2y_lb : (47 / 4000 : ℝ) * a ^ 2 ≤ (a ^ 2 / 4) * y := by
        have h := mul_le_mul_of_nonneg_left hy_lo (show (0 : ℝ) ≤ a ^ 2 / 4 by positivity)
        linarith
      have hquad_pos : 0 < (7 / 4) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          (1 / 32 - (3 / 64) * y + (3 / 320) * y ^ 2) * (5082 / 10000) -
          (1 / 16) * y + (7 / 64) * y ^ 2 +
          (47 / 4000) * a ^ 2 -
          (27 / 640) * (3 * (1036 / 10000 : ℝ) ^ 2 * y - 2 * (1036 / 10000 : ℝ) ^ 3 +
            (187 / 1000 + 2 * (1036 / 10000)) * (y - 1036 / 10000) ^ 2) := by
        rw [hy_eq]
        nlinarith only [sq_nonneg (a - 566 / 10000)]
      rw [hrem]
      linarith only [hquad_pos, hy3_ub, ha2y_lb, hy4_nn]
    linarith

/-- **Pure-Polynomial `SMAX_K2 = 19 / 1000` Contradiction (`k = 2` free points in `L`)**:
    If `T ⊆ L.erase 0` has `|L.erase 0 \ T| ≤ 2` and `∑_{p ∈ T} c_p² ≤ 19/1000`, then `False`. -/
lemma smax_k2_contra {L T : Finset (PauliIdx 4)} (hL : IsLagrangian L) (hT : T ⊆ L.erase 0)
    (hk : (L.erase 0 \ T).card ≤ 2)
    {ψ : QState 4} (hunit : IsUnitState ψ)
    (hLout : ∑ q ∈ Finset.univ \ L, |(innerProd ψ (pauliApply q ψ)).re| ≤ (594918 / 10000 : ℝ))
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (hs_in : ∑ p ∈ T, ((innerProd ψ (pauliApply p ψ)).re) ^ 2 ≤ (19 / 1000 : ℝ)) :
    False := by
  set c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set s_in : ℝ := ∑ p ∈ T, (c p) ^ 2
  set a : ℝ := ∑ p ∈ L.erase 0 \ T, (c p) ^ 2
  set S2 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 2
  set S4 : ℝ := ∑ p ∈ L.erase 0, (c p) ^ 4
  have hS2_eq : S2 = s_in + a := by
    have h := Finset.sum_sdiff hT (f := fun p => (c p) ^ 2); linarith
  have hs_nn : 0 ≤ s_in := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha_nn : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc4_nn : ∀ p : PauliIdx 4, 0 ≤ (c p) ^ 4 := fun p => by
    have : (c p) ^ 4 = ((c p) ^ 2) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  have hS4_ge : a ^ 2 / 2 ≤ S4 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (L.erase 0 \ T) (fun _ => (1 : ℝ)) (fun p => (c p) ^ 2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hcard_le : ((L.erase 0 \ T).card : ℝ) ≤ 2 := by exact_mod_cast hk
    have h4eq : ∀ p, ((c p) ^ 2) ^ 2 = (c p) ^ 4 := fun p => by ring
    simp_rw [h4eq] at hcs
    have hsub : ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 ≤ S4 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p _ _ => hc4_nn p
    have hsum_nn : 0 ≤ ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 := Finset.sum_nonneg fun p _ => hc4_nn p
    have h1 : ((L.erase 0 \ T).card : ℝ) * ∑ p ∈ L.erase 0 \ T, (c p) ^ 4 ≤ 2 * S4 :=
      mul_le_mul hcard_le hsub hsum_nn (by norm_num)
    linarith
  by_cases ha_big : (23 / 100 : ℝ) ≤ a
  · obtain ⟨_, _, _, _, hpyth⟩ := lagrangian_coset_identities hL hunit
    dsimp only at hpyth
    have hnn : 0 ≤ (1 / 256 : ℝ) * ∑ x ∈ Finset.univ \ L,
        ((∑ q ∈ L, (c (x + q)) ^ 2) - 16 * (c x) ^ 2) ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hquad_le : 2 * S4 - S2 / 8 - S2 ^ 2 / 16 ≤ 0 := by linarith
    have hpos : 0 < 2 * (a ^ 2 / 2) - (s_in + a) / 8 - (s_in + a) ^ 2 / 16 :=
      by nlinarith only [ha_big, hs_in, hs_nn, ha_nn]
    rw [← hS2_eq] at hpos; linarith
  · push Not at ha_big
    have hpoly := val_A_poly_lb hL hunit hLout hF4 (by linarith : S2 ≤ 254 / 1000)
    dsimp only at hpoly
    have hS2_le_s : S2 ≤ 19 / 1000 + a := by linarith
    have hS2_nn : 0 ≤ S2 := by linarith
    have hmon : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 254 / 1000 →
        (7 / 4 + y / 4) * (a ^ 2 / 2) - y / 8 - y ^ 2 / 16 +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 ≤
        (7 / 4 + x / 4) * (a ^ 2 / 2) - x / 8 - x ^ 2 / 16 +
        ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 32) * (5082 / 10000 - 2 * x) +
        ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 64) * x ^ 2 := by
      intro x y hx hxy hy
      have hdiff : ((7 / 4 + x / 4) * (a ^ 2 / 2) - x / 8 - x ^ 2 / 16 +
          ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 32) * (5082 / 10000 - 2 * x) +
          ((1 - (3 / 2) * x + (3 / 10) * x ^ 2) / 64) * x ^ 2) -
          ((7 / 4 + y / 4) * (a ^ 2 / 2) - y / 8 - y ^ 2 / 16 +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2) =
          (y - x) * (1 / 8 - a ^ 2 / 8 + (3 * 5082 / 640000) + 1 / 16 +
            (x + y) * (-82623 / 1600000) +
            (x ^ 2 + x * y + y ^ 2) * (3 / 160 + 3 / 128) -
            (x + y) * (x ^ 2 + y ^ 2) * (3 / 640)) := by ring
      have ha2_le : a ^ 2 ≤ (23 / 100 : ℝ) ^ 2 := by nlinarith only [ha_nn, ha_big]
      have hxy_sum : x + y ≤ 508 / 1000 := by linarith
      have hxy2 : x ^ 2 + y ^ 2 ≤ 2 * (254 / 1000 : ℝ) ^ 2 := by nlinarith only [hx, hxy, hy]
      have hxy3 : (x + y) * (x ^ 2 + y ^ 2) ≤ (508 / 1000 : ℝ) * (2 * (254 / 1000 : ℝ) ^ 2) :=
        mul_le_mul hxy_sum hxy2 (by positivity) (by norm_num)
      have hxy_nn : 0 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx (le_trans hx hxy)]
      have hpos_f : 0 ≤ 1 / 8 - a ^ 2 / 8 + (3 * 5082 / 640000) + 1 / 16 +
            (x + y) * (-82623 / 1600000) +
            (x ^ 2 + x * y + y ^ 2) * (3 / 160 + 3 / 128) -
            (x + y) * (x ^ 2 + y ^ 2) * (3 / 640) := by linarith
      have hmul := mul_nonneg (sub_nonneg.mpr hxy) hpos_f
      linarith
    have hplug := hmon S2 (19 / 1000 + a) hS2_nn hS2_le_s (by linarith)
    have hS4_step : (7 / 4 + S2 / 4) * (a ^ 2 / 2) ≤ (7 / 4 + S2 / 4) * S4 :=
      mul_le_mul_of_nonneg_left hS4_ge (by linarith)
    set y : ℝ := 19 / 1000 + a with hy_eq
    have hy_lo : (19 / 1000 : ℝ) ≤ y := by linarith
    have hy_hi : y ≤ 249 / 1000 := by linarith
    have hP_pos : 0 < (7 / 4 + y / 4) * (a ^ 2 / 2) - y / 8 - y ^ 2 / 16 +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
        ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 := by
      have hy4_nn : 0 ≤ y ^ 4 := by
        have : y ^ 4 = (y ^ 2) ^ 2 := by ring
        rw [this]; exact sq_nonneg _
      have hrem : (7 / 4 + y / 4) * (a ^ 2 / 2) - y / 8 - y ^ 2 / 16 +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 32) * (5082 / 10000 - 2 * y) +
          ((1 - (3 / 2) * y + (3 / 10) * y ^ 2) / 64) * y ^ 2 =
          (7 / 8) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          (1 / 32 - (3 / 64) * y + (3 / 320) * y ^ 2) * (5082 / 10000) -
          (1 / 16) * y + (7 / 64) * y ^ 2 +
          (a ^ 2 / 8) * y - (27 / 640) * y ^ 3 + (3 / 640) * y ^ 4 := by ring
      have ha3_lb : 3 * (1113 / 10000 : ℝ) ^ 2 * a - 2 * (1113 / 10000 : ℝ) ^ 3 ≤ a ^ 3 := by
        have hfac : a ^ 3 - (3 * (1113 / 10000 : ℝ) ^ 2 * a - 2 * (1113 / 10000 : ℝ) ^ 3) =
            (a - 1113 / 10000) ^ 2 * (a + 2 * (1113 / 10000)) := by ring
        have hnn := mul_nonneg (sq_nonneg (a - 1113 / 10000)) (show (0 : ℝ) ≤ a + 2 * (1113 / 10000) by linarith)
        linarith
      have hy3_ub : y ^ 3 ≤ 3 * (1303 / 10000 : ℝ) ^ 2 * y - 2 * (1303 / 10000 : ℝ) ^ 3 +
          (249 / 1000 + 2 * (1303 / 10000)) * (y - 1303 / 10000) ^ 2 := by
        have hfac : y ^ 3 - (3 * (1303 / 10000 : ℝ) ^ 2 * y - 2 * (1303 / 10000 : ℝ) ^ 3) =
            (y - 1303 / 10000) ^ 2 * (y + 2 * (1303 / 10000)) := by ring
        have hle := mul_le_mul_of_nonneg_left (show y + 2 * (1303 / 10000 : ℝ) ≤ 249 / 1000 + 2 * (1303 / 10000) by linarith)
          (sq_nonneg (y - 1303 / 10000))
        linarith
      have ha2y_eq : (a ^ 2 / 8) * y = (19 / 8000 : ℝ) * a ^ 2 + a ^ 3 / 8 := by rw [hy_eq]; ring
      have hquad_pos : 0 < (7 / 8) * a ^ 2 - y / 8 - y ^ 2 / 16 +
          (1 / 32 - (3 / 64) * y + (3 / 320) * y ^ 2) * (5082 / 10000) -
          (1 / 16) * y + (7 / 64) * y ^ 2 +
          (19 / 8000) * a ^ 2 + (3 * (1113 / 10000 : ℝ) ^ 2 * a - 2 * (1113 / 10000 : ℝ) ^ 3) / 8 -
          (27 / 640) * (3 * (1303 / 10000 : ℝ) ^ 2 * y - 2 * (1303 / 10000 : ℝ) ^ 3 +
            (249 / 1000 + 2 * (1303 / 10000)) * (y - 1303 / 10000) ^ 2) := by
        rw [hy_eq]
        nlinarith only [sq_nonneg (a - 1113 / 10000)]
      rw [hrem, ha2y_eq]
      linarith only [hquad_pos, hy3_ub, ha3_lb, hy4_nn]
    linarith

/-- Weighted anticommutation sum `W_anti(w) = ∑_{p, q : ω(p, q) = 1} w p * w q`. -/
noncomputable def wAnti (w : PauliIdx 4 → ℝ) : ℝ :=
  ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, if symp p q = 1 then w p * w q else 0

/-- **Exact Integer-Coefficient 2D Bessel Self-Duality Inequality**:
    For ANY weight vector `w : PauliIdx 4 → ℝ` with `w 0 = 1`, letting
      `S₁ = ∑_p w_p`, `S₂w = ∑_p w_p²`, `M = ∑_p w_p f_p` (where `f 0 = 1`, `f p = 1 - 16 c_p²`),
    if `pauliMoment4 4 ψ ≤ 31 / 16` and `S₁ + 16 ≤ 17 * M`, then:
      `255 * wAnti w ≤ 120 * (17 * S₂w + S₁² - 2 * S₁ - 16) - (17 * M - S₁ - 16)²`. -/
theorem bessel2d_bound {ψ : QState 4} (hunit : IsUnitState ψ)
    (hF4 : pauliMoment4 4 ψ ≤ 31 / 16)
    (w : PauliIdx 4 → ℝ) (hw0 : w 0 = 1) :
    let c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let f : PauliIdx 4 → ℝ := fun p => if p = 0 then 1 else 1 - 16 * (c p) ^ 2
    let S1 : ℝ := ∑ p : PauliIdx 4, w p
    let S2w : ℝ := ∑ p : PauliIdx 4, (w p) ^ 2
    let M : ℝ := ∑ p : PauliIdx 4, w p * f p
    255 * wAnti w ≤ 120 * (17 * S2w + S1 ^ 2 - 2 * S1 - 16) - (17 * M - S1 - 16) ^ 2 := by
  intro c f S1 S2w M
  obtain ⟨hsum2, hsum4⟩ := sum_sq_and_fourth_four hunit
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hns : ∀ p : PauliIdx 4, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
    fun p => innerProd_pauliApply_self_normSq p ψ
  -- `W f = 16 f`!
  have hWf : ∀ q : PauliIdx 4, ∑ p : PauliIdx 4, (sympSign p q : ℝ) * f p = 16 * f q := by
    intro q
    have hf_eq : ∀ p : PauliIdx 4, f p = (if p = 0 then 16 else 0) + 1 - 16 * (c p) ^ 2 := fun p => by
      by_cases hp : p = 0
      · subst hp; simp [f, hc0]
      · simp [f, hp]
    simp_rw [hf_eq, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_one]
    have h1 : ∑ p : PauliIdx 4, (sympSign p q : ℝ) * (if p = 0 then (16 : ℝ) else 0) = 16 := by
      rw [Finset.sum_eq_single (0 : PauliIdx 4)]
      · simp [sympSign, symp_zero_left]
      · intro p _ hp; simp [hp]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : ∑ p : PauliIdx 4, (sympSign p q : ℝ) = if q = 0 then 256 else 0 := by
      rw [sum_sympSign_all]; norm_num
    have h3 : ∑ p : PauliIdx 4, (sympSign p q : ℝ) * (16 * (c p) ^ 2) = 16 * (16 * (c q) ^ 2) := by
      have hsd := pauli_symp_self_dual ψ q
      simp_rw [hns] at hsd; norm_num at hsd
      calc ∑ p : PauliIdx 4, (sympSign p q : ℝ) * (16 * (c p) ^ 2)
          = 16 * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * (c p) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ = 16 * (16 * (c q) ^ 2) := by rw [hsd]
    rw [h1, h2, h3]
    by_cases hq : q = 0
    · subst hq; simp [hc0]; norm_num
    · simp [hq]
  -- `∑_p f(p)² = 16 + 256 * (pauliMoment4 4 ψ - 31/16) ≤ 16`!
  have hf2 : ∑ p : PauliIdx 4, (f p) ^ 2 ≤ 16 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4))]
    have h0 : (f 0) ^ 2 = 1 := by simp [f]
    have hterm : ∀ p ∈ Finset.univ.erase (0 : PauliIdx 4),
        (f p) ^ 2 = 1 - 32 * (c p) ^ 2 + 256 * (c p) ^ 4 := fun p hp => by
      simp only [f, (Finset.mem_erase.mp hp).1, ↓reduceIte]; ring
    rw [h0, Finset.sum_congr rfl hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((Finset.univ.erase (0 : PauliIdx 4)).card : ℝ) = 255 := by
      rw [card_PauliIdx_erase_zero]; norm_num
    rw [hcard]; linarith
  -- Define `u2(q) = (P_+ e_0)(q) = (1/2) δ_{q,0} + 1/32` and `v1(q) = (P_+ w)(q) = (1/2) w(q) + (1/32) ∑_p (-1)^{ω(p,q)} w(p)`!
  let u2 : PauliIdx 4 → ℝ := fun q => (if q = 0 then (1 / 2 : ℝ) else 0) + 1 / 32
  let v1 : PauliIdx 4 → ℝ := fun q => (1 / 2 : ℝ) * w q + (1 / 32 : ℝ) * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p
  have hP_proj : ∀ g : PauliIdx 4 → ℝ,
      ∑ q : PauliIdx 4, f q * ((1 / 2 : ℝ) * g q + (1 / 32 : ℝ) * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * g p) =
      ∑ p : PauliIdx 4, g p * f p := by
    intro g
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hswap : ∑ q : PauliIdx 4, f q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * g p =
        16 * ∑ p : PauliIdx 4, g p * f p := by
      calc ∑ q : PauliIdx 4, f q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * g p
          = ∑ p : PauliIdx 4, g p * ∑ q : PauliIdx 4, (sympSign q p : ℝ) * f q := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
              rw [sympSign_comm p q]; ring
        _ = ∑ p : PauliIdx 4, g p * (16 * f p) := Finset.sum_congr rfl fun p _ => by rw [hWf p]
        _ = 16 * ∑ p : PauliIdx 4, g p * f p := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have h1 : ∑ q : PauliIdx 4, f q * ((1 / 2 : ℝ) * g q) = (1 / 2 : ℝ) * ∑ p : PauliIdx 4, g p * f p := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ q : PauliIdx 4, f q * ((1 / 32 : ℝ) * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * g p) =
        (1 / 32 : ℝ) * ∑ q : PauliIdx 4, f q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * g p := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2, hswap]; ring
  have hfu2 : ∑ q : PauliIdx 4, f q * u2 q = 1 := by
    have hu2_eq : ∀ q : PauliIdx 4, u2 q = (1 / 2 : ℝ) * (if q = 0 then (1 : ℝ) else 0) +
        (1 / 32 : ℝ) * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * (if p = 0 then (1 : ℝ) else 0) := fun q => by
      simp only [u2]
      rw [Finset.sum_eq_single (0 : PauliIdx 4)]
      · simp [sympSign, symp_zero_left]
      · intro p _ hp; simp [hp]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hu2_eq]; rw [hP_proj]
    rw [Finset.sum_eq_single (0 : PauliIdx 4)]
    · simp [f]
    · intro p _ hp; simp [hp]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hfv1 : ∑ q : PauliIdx 4, f q * v1 q = M := hP_proj w
  have hu2_sq : ∑ q : PauliIdx 4, (u2 q) ^ 2 = 17 / 32 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 4))]
    have h0 : (u2 0) ^ 2 = (17 / 32 : ℝ) ^ 2 := by simp [u2]; norm_num
    have hrest : ∑ q ∈ Finset.univ.erase (0 : PauliIdx 4), (u2 q) ^ 2 = 255 * (1 / 32 : ℝ) ^ 2 := by
      have ht : ∀ q ∈ Finset.univ.erase (0 : PauliIdx 4), (u2 q) ^ 2 = (1 / 32 : ℝ) ^ 2 := fun q hq => by
        simp [u2, (Finset.mem_erase.mp hq).1]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ.erase (0 : PauliIdx 4)).card : ℝ) = 255 := by
        rw [card_PauliIdx_erase_zero]; norm_num
      rw [hcard]
    rw [h0, hrest]; norm_num
  have hu2v1 : ∑ q : PauliIdx 4, u2 q * v1 q = (16 + S1) / 32 := by
    have hW2 : ∑ q : PauliIdx 4, ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p = 256 := by
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single (0 : PauliIdx 4)]
      · have h1 : ∀ q : PauliIdx 4, (sympSign 0 q : ℝ) * w 0 = 1 := fun q => by
          simp [sympSign, symp_zero_left, hw0]
        rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_const, Finset.card_univ, card_PauliIdx,
            nsmul_eq_mul]; norm_num
      · intro p _ hp
        rw [← Finset.sum_mul]
        have : ∑ q : PauliIdx 4, (sympSign p q : ℝ) = 0 := by
          have hs := sum_sympSign_all p; simp_rw [sympSign_comm p]; simp [hp] at hs; exact hs
        rw [this, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hv1_0 : v1 0 = (16 + S1) / 32 := by
      simp only [v1, hw0]
      have : ∑ p : PauliIdx 4, (sympSign p 0 : ℝ) * w p = S1 :=
        Finset.sum_congr rfl fun p _ => by simp [sympSign, symp_zero_right]
      rw [this]; ring
    have hpt : ∀ q : PauliIdx 4, u2 q * v1 q =
        (if q = 0 then (1 / 2 : ℝ) * v1 0 else 0) +
        (1 / 64 : ℝ) * w q + (1 / 1024 : ℝ) * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p := fun q => by
      by_cases hq : q = 0
      · subst hq; simp only [u2, v1, ↓reduceIte]; ring
      · simp only [u2, v1, hq, ↓reduceIte]; ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ q : PauliIdx 4, (if q = 0 then (1 / 2 : ℝ) * v1 0 else 0) = (1 / 2 : ℝ) * v1 0 := by
      rw [Finset.sum_ite_eq']; simp
    rw [h0, hv1_0, hW2]; ring
  have hv1_sq : ∑ q : PauliIdx 4, (v1 q) ^ 2 = S2w / 2 + S1 ^ 2 / 32 - wAnti w / 16 := by
    -- Compute `∑_q (1/2 w_q + 1/32 (W w)_q)² = (1/4) S2w + (1/32) ⟨w, W w⟩ + (1/1024) ‖W w‖²`!
    -- Since `W² = 256 I`, `‖W w‖² = 256 S2w`, so `(1/4 + 256/1024) S2w = (1/2) S2w`!
    -- And `⟨w, W w⟩ = ∑_{p,q} (-1)^{ω(p,q)} w_p w_q = S1² - 2 wAnti w`!
    have hW_norm : ∑ q : PauliIdx 4, (∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p) ^ 2 = 256 * S2w := by
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hswap : ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, ∑ r : PauliIdx 4,
          (sympSign p q : ℝ) * w p * ((sympSign r q : ℝ) * w r) =
          ∑ p : PauliIdx 4, ∑ r : PauliIdx 4,
            (∑ q : PauliIdx 4, (sympSign q (p + r) : ℝ)) * (w p * w r) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [sympSign_add_right, sympSign_comm q p, sympSign_comm q r]; push_cast; ring
      rw [hswap]
      have hdiag : ∀ p : PauliIdx 4, ∑ r : PauliIdx 4,
          (∑ q : PauliIdx 4, (sympSign q (p + r) : ℝ)) * (w p * w r) = 256 * (w p) ^ 2 := by
        intro p
        rw [Finset.sum_eq_single p]
        · rw [pauliIdx_add_self, sum_sympSign_all]; simp; ring
        · intro r _ hrp
          have hne : p + r ≠ 0 := fun h => hrp (by
            have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this)
          rw [sum_sympSign_all]; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [Finset.sum_congr rfl fun p _ => hdiag p, ← Finset.mul_sum]
    have hW_inner : ∑ q : PauliIdx 4, w q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p =
        S1 ^ 2 - 2 * wAnti w := by
      have hS1_sq : S1 ^ 2 = ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, w p * w q := by
        simp only [S1, sq, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      have hpt : ∀ p q : PauliIdx 4, (sympSign p q : ℝ) * (w p * w q) =
          w p * w q - 2 * (if symp p q = 1 then w p * w q else 0) := fun p q => by
        rcases zmod2_cases (symp p q) with h | h <;> simp [sympSign, h]; ring
      calc ∑ q : PauliIdx 4, w q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p
          = ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, (sympSign p q : ℝ) * (w p * w q) := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, (w p * w q - 2 * (if symp p q = 1 then w p * w q else 0)) :=
            Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hpt p q
        _ = S1 ^ 2 - 2 * wAnti w := by
            have hsub : ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, (w p * w q - 2 * (if symp p q = 1 then w p * w q else 0)) =
                (∑ p : PauliIdx 4, ∑ q : PauliIdx 4, w p * w q) -
                ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, 2 * (if symp p q = 1 then w p * w q else 0) := by
              simp_rw [Finset.sum_sub_distrib]
            have h2w : ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, 2 * (if symp p q = 1 then w p * w q else 0) = 2 * wAnti w := by
              rw [wAnti, Finset.mul_sum]
              exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
            rw [hsub, ← hS1_sq, h2w]
    have hexp : ∀ q : PauliIdx 4, (v1 q) ^ 2 =
        (1 / 4 : ℝ) * (w q) ^ 2 + (1 / 32 : ℝ) * (w q * ∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p) +
        (1 / 1024 : ℝ) * (∑ p : PauliIdx 4, (sympSign p q : ℝ) * w p) ^ 2 := fun q => by
      simp only [v1]; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hW_inner, hW_norm]; ring
  -- 1-line Cauchy–Schwarz on `f_perp = f - (32/17) u2` and `v1_perp = v1 - ((16 + S1)/17) u2`!
  let fp : PauliIdx 4 → ℝ := fun q => f q - (32 / 17 : ℝ) * u2 q
  let vp : PauliIdx 4 → ℝ := fun q => v1 q - ((16 + S1) / 17 : ℝ) * u2 q
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (PauliIdx 4)) fp vp
  have hfp_vp : ∑ q : PauliIdx 4, fp q * vp q = (17 * M - S1 - 16) / 17 := by
    have hexp : ∀ q, fp q * vp q = f q * v1 q - ((16 + S1) / 17) * (f q * u2 q) -
        (32 / 17) * (u2 q * v1 q) + ((32 * (16 + S1)) / 289) * (u2 q) ^ 2 := fun q => by
      simp only [fp, vp]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hfv1, hfu2, hu2v1, hu2_sq]; ring
  have hfp_sq : ∑ q : PauliIdx 4, (fp q) ^ 2 ≤ 240 / 17 := by
    have hexp : ∀ q, (fp q) ^ 2 = (f q) ^ 2 - (64 / 17) * (f q * u2 q) + (1024 / 289) * (u2 q) ^ 2 :=
      fun q => by simp only [fp]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hfu2, hu2_sq]; linarith
  have hvp_sq : ∑ q : PauliIdx 4, (vp q) ^ 2 =
      S2w / 2 + S1 ^ 2 / 32 - wAnti w / 16 - (16 + S1) ^ 2 / 544 := by
    have hexp : ∀ q, (vp q) ^ 2 = (v1 q) ^ 2 - (2 * (16 + S1) / 17) * (u2 q * v1 q) +
        ((16 + S1) ^ 2 / 289) * (u2 q) ^ 2 := fun q => by simp only [vp]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hv1_sq, hu2v1, hu2_sq]; ring
  have hvp_nn : 0 ≤ ∑ q : PauliIdx 4, (vp q) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs2 : ((17 * M - S1 - 16) / 17) ^ 2 ≤
      (240 / 17 : ℝ) * (S2w / 2 + S1 ^ 2 / 32 - wAnti w / 16 - (16 + S1) ^ 2 / 544) := by
    rw [hfp_vp, hvp_sq] at hcs
    have hvp_nn' : 0 ≤ S2w / 2 + S1 ^ 2 / 32 - wAnti w / 16 - (16 + S1) ^ 2 / 544 := hvp_sq ▸ hvp_nn
    exact le_trans hcs (mul_le_mul_of_nonneg_right hfp_sq hvp_nn')
  linarith

/-! ### Section 3: Unified Symplectic Turán Lemmas on `𝔽₂⁸` and Weighted 15-Mask Bound -/

/-- Exact weighted 15-mask anticommutation lower bound:
    Given a Lagrangian `L`, `S13 ⊆ L` of size `13`, `u ∉ L`, and 4 distinct extra points
    `ps : Fin 4 → PauliIdx 4` disjoint from `S13 ∪ {u}` with weights `ws : Fin 4 → ℝ` satisfying
    `0 ≤ ws j ≤ 1`, partitioning `{0,1,2,3}` into `I = {j | ps j ∈ L}` and `J = {j | ps j ∉ L}`,
    the indicator+weighted function `w` supported on `S13 ∪ {u} ∪ {ps j}` satisfies:
      `2 * (1 + W_out) * (5 + W_in) ≤ wAnti w`. -/
lemma weighted_mask_anticomm_lb {L S13 : Finset (PauliIdx 4)} (hL : IsLagrangian L)
    (hS13_sub : S13 ⊆ L) (hS13_card : S13.card = 13)
    {u : PauliIdx 4} (huL : u ∉ L)
    {ps : Fin 4 → PauliIdx 4} (hps_inj : Function.Injective ps)
    (hps_disj_S : ∀ j : Fin 4, ps j ∉ S13) (hps_ne_u : ∀ j : Fin 4, ps j ≠ u)
    {ws : Fin 4 → ℝ} (hws_lo : ∀ j, 0 ≤ ws j) (hws_hi : ∀ j, ws j ≤ 1) :
    let w : PauliIdx 4 → ℝ := fun p =>
      if p ∈ S13 ∨ p = u then 1
      else if h : ∃ j : Fin 4, ps j = p then ws (Classical.choose h) else 0
    let W_in : ℝ := ∑ j : Fin 4, if ps j ∈ L then ws j else 0
    let W_out : ℝ := ∑ j : Fin 4, if ps j ∉ L then ws j else 0
    2 * (1 + W_out) * (5 + W_in) ≤ wAnti w := by
  intro w W_in W_out
  have hw_nn : ∀ p : PauliIdx 4, 0 ≤ w p := fun p => by
    simp only [w]
    split_ifs with h1 h2
    · norm_num
    · exact hws_lo _
    · norm_num
  have hw_le1 : ∀ p : PauliIdx 4, w p ≤ 1 := fun p => by
    simp only [w]
    split_ifs with h1 h2
    · norm_num
    · exact hws_hi _
    · norm_num
  have hw_S13 : ∀ p ∈ S13, w p = 1 := fun p hp => by simp [w, hp]
  have hw_u : w u = 1 := by simp [w]
  have hw_ps : ∀ j : Fin 4, w (ps j) = ws j := fun j => by
    have hnot : ¬(ps j ∈ S13 ∨ ps j = u) := fun h => h.elim (hps_disj_S j) (hps_ne_u j)
    have hex : ∃ k : Fin 4, ps k = ps j := ⟨j, rfl⟩
    simp only [w, hnot, ↓reduceIte]
    split_ifs
    exact congr_arg ws (hps_inj (Classical.choose_spec hex))
  -- Total weight on `L` is `13 + W_in`!
  have hsum_L : ∑ p ∈ L, w p = 13 + W_in := by
    let Pin := Finset.univ.filter fun j : Fin 4 => ps j ∈ L
    let Q := S13 ∪ Pin.image ps
    have hQ_sub : Q ⊆ L := Finset.union_subset hS13_sub fun x hx => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx; exact (Finset.mem_filter.mp hj).2
    have hdisj : Disjoint S13 (Pin.image ps) := by
      rw [Finset.disjoint_left]; intro x hxS hxI
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxI; exact hps_disj_S j hxS
    rw [← Finset.sum_sdiff hQ_sub]
    have hzero : ∑ p ∈ L \ Q, w p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpL := (Finset.mem_sdiff.mp hp).1
      have hpQ := (Finset.mem_sdiff.mp hp).2
      have hpS : p ∉ S13 := fun h => hpQ (Finset.mem_union_left _ h)
      have hpu : p ≠ u := fun h => huL (h ▸ hpL)
      have hnot_ex : ¬(∃ j : Fin 4, ps j = p) := by
        rintro ⟨j, rfl⟩
        exact hpQ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpL⟩, rfl⟩))
      simp [w, hpS, hpu, hnot_ex]
    rw [hzero, zero_add, Finset.sum_union hdisj, Finset.sum_congr rfl hw_S13, Finset.sum_const,
        hS13_card, nsmul_eq_mul, mul_one]
    rw [Finset.sum_image (fun a _ b _ h => hps_inj h)]
    have hWin : ∑ j ∈ Pin, w (ps j) = W_in := by
      simp only [W_in, Pin, ← Finset.sum_filter]
      exact Finset.sum_congr rfl fun j _ => hw_ps j
    rw [hWin]; norm_num
  -- For EVERY `q ∉ L`, `∑_{p ∈ L, ω(q,p)=1} w p ≥ 5 + W_in`!
  have hanti_q : ∀ q : PauliIdx 4, q ∉ L → 5 + W_in ≤ ∑ p ∈ L, if symp q p = 1 then w p else 0 := by
    intro q hqL
    have hcard1 := (lagrangian_perp_eq_and_card_anticomm hL).2 q hqL
    have hcard0 : (L.filter fun p => symp q p = 0).card = 8 := by
      have htot := Finset.card_filter_add_card_filter_not (s := L) (p := fun p => symp q p = 0)
      have heq : L.filter (fun p => ¬symp q p = 0) = L.filter (fun p => symp q p = 1) := by
        ext p; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hp, hne⟩ => ⟨hp, (zmod2_cases _).resolve_left hne⟩,
               fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
      rw [heq, hcard1, hL.2.1] at htot; norm_num at htot; omega
    have hsplit : ∑ p ∈ L, w p =
        (∑ p ∈ L.filter (fun p => symp q p = 0), w p) +
        (∑ p ∈ L.filter (fun p => symp q p = 1), w p) := by
      rw [← Finset.sum_filter_add_sum_filter_not L (fun p => symp q p = 0)]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p; simp only [Finset.mem_filter]
      exact ⟨fun ⟨hp, hne⟩ => ⟨hp, (zmod2_cases _).resolve_left hne⟩,
             fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
    have hle8 : ∑ p ∈ L.filter (fun p => symp q p = 0), w p ≤ 8 := by
      calc ∑ p ∈ L.filter (fun p => symp q p = 0), w p
          ≤ ∑ _p ∈ L.filter (fun p => symp q p = 0), (1 : ℝ) := Finset.sum_le_sum fun p _ => hw_le1 p
        _ = 8 := by rw [Finset.sum_const, hcard0, nsmul_eq_mul]; norm_num
    rw [← Finset.sum_filter]; linarith
  -- Sum over `q ∈ {u} ∪ {ps j | ps j ∉ L}` (all outside `L`, disjoint from `L`!) and both directions `(q, p)` and `(p, q)`!
  let Pout := Finset.univ.filter fun j : Fin 4 => ps j ∉ L
  let Bout : Finset (PauliIdx 4) := insert u (Pout.image ps)
  have hBout_sub : Bout ⊆ Finset.univ \ L := by
    intro q hq
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hI
    · exact huL
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI; exact (Finset.mem_filter.mp hj).2
  have hsum_Bout : ∑ q ∈ Bout, w q = 1 + W_out := by
    have hu_not : u ∉ Pout.image ps := by
      intro h; obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h; exact hps_ne_u j hj
    rw [Finset.sum_insert hu_not, hw_u, Finset.sum_image (fun a _ b _ h => hps_inj h)]
    congr 1
    simp only [W_out, Pout, ← Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => hw_ps j
  -- Split `wAnti w` into `(q ∈ univ \ L, p ∈ L)` and `(p ∈ L, q ∈ univ \ L)`!
  have hterm_nn : ∀ p q : PauliIdx 4, 0 ≤ if symp p q = 1 then w p * w q else 0 := fun p q => by
    split_ifs
    · exact mul_nonneg (hw_nn p) (hw_nn q)
    · norm_num
  have hpair_ge : (∑ q ∈ Bout, ∑ p ∈ L, if symp q p = 1 then w q * w p else 0) +
      (∑ p ∈ L, ∑ q ∈ Bout, if symp p q = 1 then w p * w q else 0) ≤ wAnti w := by
    have h1 : ∑ q ∈ Finset.univ \ L, ∑ p ∈ Finset.univ, (if symp q p = 1 then w q * w p else 0) ≥
        ∑ q ∈ Bout, ∑ p ∈ L, if symp q p = 1 then w q * w p else 0 := by
      calc ∑ q ∈ Bout, ∑ p ∈ L, (if symp q p = 1 then w q * w p else 0)
          ≤ ∑ q ∈ Bout, ∑ p : PauliIdx 4, (if symp q p = 1 then w q * w p else 0) :=
            Finset.sum_le_sum fun q _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
              fun p _ _ => hterm_nn q p
        _ ≤ ∑ q ∈ Finset.univ \ L, ∑ p : PauliIdx 4, (if symp q p = 1 then w q * w p else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hBout_sub fun q _ _ =>
              Finset.sum_nonneg fun p _ => hterm_nn q p
    have h2 : ∑ p ∈ L, ∑ q ∈ Finset.univ, (if symp p q = 1 then w p * w q else 0) ≥
        ∑ p ∈ L, ∑ q ∈ Bout, if symp p q = 1 then w p * w q else 0 :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Bout)
        fun q _ _ => hterm_nn p q
    have hsplit : wAnti w =
        (∑ p ∈ L, ∑ q : PauliIdx 4, if symp p q = 1 then w p * w q else 0) +
        (∑ q ∈ Finset.univ \ L, ∑ p : PauliIdx 4, if symp q p = 1 then w q * w p else 0) := by
      simp only [wAnti]; rw [← Finset.sum_sdiff (Finset.subset_univ L)]; ring
    linarith
  have hsym : ∑ p ∈ L, ∑ q ∈ Bout, (if symp p q = 1 then w p * w q else 0) =
      ∑ q ∈ Bout, ∑ p ∈ L, if symp q p = 1 then w q * w p else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by
      rw [symp_comm p q, mul_comm (w p)]
  have hhalf : (1 + W_out) * (5 + W_in) ≤ ∑ q ∈ Bout, ∑ p ∈ L, if symp q p = 1 then w q * w p else 0 := by
    calc (1 + W_out) * (5 + W_in)
        = ∑ q ∈ Bout, w q * (5 + W_in) := by rw [← Finset.sum_mul, hsum_Bout]
      _ ≤ ∑ q ∈ Bout, w q * (∑ p ∈ L, if symp q p = 1 then w p else 0) :=
          Finset.sum_le_sum fun q hq =>
            mul_le_mul_of_nonneg_left (hanti_q q (Finset.mem_sdiff.mp (hBout_sub hq)).2) (hw_nn q)
      _ = ∑ q ∈ Bout, ∑ p ∈ L, if symp q p = 1 then w q * w p else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  linarith

/-- Unweighted anticommutation count `A(Z) = |{(p, q) ∈ Z × Z | ω(p, q) = 1}|` (as `ℕ`). -/
def antiCount (Z : Finset (PauliIdx 4)) : ℕ :=
  ∑ p ∈ Z, (Z.filter fun q => symp p q = 1).card

/-- `antiCount Z` matches `wAnti` of the indicator `1_Z`. -/
lemma wAnti_indicator_eq (Z : Finset (PauliIdx 4)) :
    wAnti (fun p => if p ∈ Z then 1 else 0) = (antiCount Z : ℝ) := by
  simp only [wAnti, antiCount, Nat.cast_sum]
  rw [← Finset.sum_sdiff (Finset.subset_univ Z)]
  have hout : ∑ p ∈ Finset.univ \ Z, ∑ q : PauliIdx 4,
      (if symp p q = 1 then (if p ∈ Z then (1 : ℝ) else 0) * (if q ∈ Z then 1 else 0) else 0) = 0 :=
    Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => by
      simp [(Finset.mem_sdiff.mp hp).2]
  rw [hout, zero_add]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_sdiff (Finset.subset_univ Z)]
  have hout2 : ∑ q ∈ Finset.univ \ Z,
      (if symp p q = 1 then (if p ∈ Z then (1 : ℝ) else 0) * (if q ∈ Z then 1 else 0) else 0) = 0 :=
    Finset.sum_eq_zero fun q hq => by simp [(Finset.mem_sdiff.mp hq).2]
  rw [hout2, zero_add]
  have hpt : ∀ q ∈ Z, (if symp p q = 1 then (if p ∈ Z then (1 : ℝ) else 0) * (if q ∈ Z then 1 else 0) else 0) =
      if symp p q = 1 then 1 else 0 := fun q hq => by simp [hp, hq]
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `antiCount Z` is always even. -/
lemma antiCount_even (Z : Finset (PauliIdx 4)) : Even (antiCount Z) := by
  -- Induction on `Z`: inserting `a ∉ s` increases `antiCount` by `2 * deg_s(a)`!
  induction Z using Finset.induction_on with
  | empty => exact ⟨0, by simp [antiCount]⟩
  | insert a s ha ih =>
    obtain ⟨k, hk⟩ := ih
    let da := (s.filter fun q => symp a q = 1).card
    have hstep : antiCount (insert a s) = antiCount s + 2 * da := by
      simp only [antiCount]
      rw [Finset.sum_insert ha]
      have ha_self : symp a a ≠ 1 := by rw [symp_self]; decide
      have hfa : ((insert a s).filter fun q => symp a q = 1).card = da := by
        rw [Finset.filter_insert]; simp only [ha_self, ↓reduceIte]; rfl
      have hfs : ∀ p ∈ s, ((insert a s).filter fun q => symp p q = 1).card =
          (s.filter fun q => symp p q = 1).card + (if symp a p = 1 then 1 else 0) := by
        intro p hp
        rw [Finset.filter_insert, symp_comm p a]
        by_cases h1 : symp a p = 1
        · simp only [h1, ↓reduceIte]
          rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)]
        · simp only [h1, ↓reduceIte, add_zero]
      rw [hfa, Finset.sum_congr rfl hfs, Finset.sum_add_distrib]
      have hsum_da : ∑ p ∈ s, (if symp a p = 1 then 1 else 0) = da := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      rw [hsum_da]; omega
    exact ⟨k + da, by omega⟩

/-- One-step deletion identity: for `u ∈ Z`, writing `Z' = Z.filter (symp u · = 0)` and
    `B = Z.filter (symp u · = 1)`, `antiCount Z = antiCount Z' + ∑_{w ∈ B} deg_Z(w) + ∑_{w ∈ B} deg_{Z'}(w)`. -/
lemma antiCount_split (Z : Finset (PauliIdx 4)) (u : PauliIdx 4) :
    let Z' := Z.filter fun x => symp u x = 0
    let B := Z.filter fun x => symp u x = 1
    antiCount Z = antiCount Z' +
      (∑ w ∈ B, (Z.filter fun y => symp w y = 1).card) +
      (∑ w ∈ B, (Z'.filter fun y => symp w y = 1).card) := by
  intro Z' B
  have hpart : Z = Z' ∪ B := by
    ext x; simp only [Z', B, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx; rcases zmod2_cases (symp u x) with h | h <;> [exact Or.inl ⟨hx, h⟩; exact Or.inr ⟨hx, h⟩]
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint Z' B := by
    rw [Finset.disjoint_left]; intro x hx0 hx1
    have h0 := (Finset.mem_filter.mp hx0).2
    have h1 := (Finset.mem_filter.mp hx1).2
    rw [h0] at h1; exact absurd h1 (by decide)
  have hsplit_deg : ∀ x ∈ Z', (Z.filter fun y => symp x y = 1).card =
      (Z'.filter fun y => symp x y = 1).card + (B.filter fun y => symp x y = 1).card := by
    intro x _
    conv_lhs => rw [hpart]
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  have hcross : ∑ x ∈ Z', (B.filter fun y => symp x y = 1).card =
      ∑ w ∈ B, (Z'.filter fun y => symp w y = 1).card := by
    have h1 : ∀ x ∈ Z', (B.filter fun y => symp x y = 1).card =
        ∑ w ∈ B, if symp x w = 1 then 1 else 0 := fun x _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ∀ w ∈ B, (Z'.filter fun y => symp w y = 1).card =
        ∑ x ∈ Z', if symp x w = 1 then 1 else 0 := fun w _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1; ext x; simp [symp_comm]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]
  simp only [antiCount]
  conv_lhs => arg 1; rw [hpart]
  rw [Finset.sum_union hdisj, Finset.sum_congr rfl hsplit_deg, Finset.sum_add_distrib, hcross]
  omega

/-- Base case `r = 3` of symplectic radical induction:
    If `IsIsoSub 3 R`, `Z ⊆ R^⊥`, and `∀ L, IsLagrangian L → (Z ∩ L).card ≤ s`, then
    writing `n₀ = (Z ∩ R).card`, there exist `n₁, n₂, n₃ ≤ 8` with `n₀ + n₁ + n₂ + n₃ = Z.card`,
    `n₀ + max n₁ (max n₂ n₃) ≤ s`, and `antiCount Z = 2 * (n₁ * n₂ + n₁ * n₃ + n₂ * n₃)`. -/
lemma turan_r3_decomp {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub 3 R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    {s : ℕ} (hs : ∀ L : Finset (PauliIdx 4), IsLagrangian L → (Z ∩ L).card ≤ s) :
    ∃ n1 n2 n3 : ℕ, n1 ≤ 8 ∧ n2 ≤ 8 ∧ n3 ≤ 8 ∧
      (Z ∩ R).card + n1 + n2 + n3 = Z.card ∧
      (Z ∩ R).card + n1 ≤ s ∧ (Z ∩ R).card + n2 ≤ s ∧ (Z ∩ R).card + n3 ≤ s ∧
      antiCount Z = 2 * (n1 * n2 + n1 * n3 + n2 * n3) := by
  let Rp := Finset.univ.filter fun x : PauliIdx 4 => ∀ y ∈ R, symp x y = 0
  have hRp_card : Rp.card = 32 := by
    have h := (isoSub_perp_card hR).2
    change Rp.card * 2 ^ 3 = 256 at h; norm_num at h; omega
  have hR_sub_Rp : R ⊆ Rp := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => hR.2.2.2 x hx y hy⟩
  have hne1 : (Rp \ R).Nonempty := Finset.sdiff_nonempty.mpr fun hsub => by
    have := Finset.card_le_card hsub; rw [hRp_card, hR.2.1] at this; omega
  obtain ⟨a, ha⟩ := hne1
  have haRp := (Finset.mem_sdiff.mp ha).1
  have haR := (Finset.mem_sdiff.mp ha).2
  have ha_comm : ∀ y ∈ R, symp a y = 0 := (Finset.mem_filter.mp haRp).2
  let L1 := R ∪ R.image (a + ·)
  have hL1 : IsLagrangian L1 := isoSub_extend_step hR haR ha_comm
  have hL1_sub_Rp : L1 ⊆ Rp := Finset.union_subset hR_sub_Rp fun x hx => by
    obtain ⟨y, hyR, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hzR => ?_⟩
    rw [symp_add_left, ha_comm z hzR, hR.2.2.2 y hyR z hzR, add_zero]
  have hne2 : (Rp \ L1).Nonempty := Finset.sdiff_nonempty.mpr fun hsub => by
    have := Finset.card_le_card hsub; rw [hRp_card, hL1.2.1] at this; omega
  obtain ⟨b, hb⟩ := hne2
  have hbRp := (Finset.mem_sdiff.mp hb).1
  have hbL1 := (Finset.mem_sdiff.mp hb).2
  have hb_comm : ∀ y ∈ R, symp b y = 0 := (Finset.mem_filter.mp hbRp).2
  have hbR : b ∉ R := fun h => hbL1 (Finset.mem_union_left _ h)
  have hab1 : symp a b = 1 := by
    rcases zmod2_cases (symp a b) with h0 | h1
    · exfalso
      have hbL1_comm : ∀ x ∈ L1, symp b x = 0 := by
        intro x hx; rcases Finset.mem_union.mp hx with hx | hx
        · exact hb_comm x hx
        · obtain ⟨y, hyR, rfl⟩ := Finset.mem_image.mp hx
          rw [symp_add_right, symp_comm b a, h0, hb_comm y hyR, add_zero]
      exact hbL1 ((lagrangian_perp_eq_and_card_anticomm hL1).1 b |>.mp hbL1_comm)
    · exact h1
  let L2 := R ∪ R.image (b + ·)
  let L3 := R ∪ R.image ((a + b) + ·)
  have hL2 : IsLagrangian L2 := isoSub_extend_step hR hbR hb_comm
  have habR : a + b ∉ R := fun h => hbL1 (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨a + b, h, pauliIdx_add_cancel_left a b⟩))
  have hab_comm : ∀ y ∈ R, symp (a + b) y = 0 := fun y hy => by
    rw [symp_add_left, ha_comm y hy, hb_comm y hy, add_zero]
  have hL3 : IsLagrangian L3 := isoSub_extend_step hR habR hab_comm
  let C1 := R.image (a + ·)
  let C2 := R.image (b + ·)
  let C3 := R.image ((a + b) + ·)
  have hcardC : ∀ c : PauliIdx 4, (R.image (c + ·)).card = 8 := fun c => by
    rw [Finset.card_image_of_injective _ fun x y h => by
      have := congr_arg (c + ·) h; simpa [pauliIdx_add_cancel_left] using this, hR.2.1]; norm_num
  -- Pairwise symp values between `R, C1, C2, C3`!
  have hsymp_12 : ∀ x ∈ C1, ∀ y ∈ C2, symp x y = 1 := by
    intro x hx y hy
    obtain ⟨rx, hrx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ry, hry, rfl⟩ := Finset.mem_image.mp hy
    rw [symp_add_left, symp_add_right, symp_add_right, hab1, ha_comm ry hry,
        symp_comm rx b, hb_comm rx hrx, hR.2.2.2 rx hrx ry hry]; simp
  have hsymp_13 : ∀ x ∈ C1, ∀ y ∈ C3, symp x y = 1 := by
    intro x hx y hy
    obtain ⟨rx, hrx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ry, hry, rfl⟩ := Finset.mem_image.mp hy
    rw [symp_add_left, symp_add_right, symp_add_right, symp_add_right, symp_add_right,
        symp_self, hab1, ha_comm ry hry, symp_comm rx a, ha_comm rx hrx,
        symp_comm rx b, hb_comm rx hrx, hR.2.2.2 rx hrx ry hry]; simp
  have hsymp_23 : ∀ x ∈ C2, ∀ y ∈ C3, symp x y = 1 := by
    intro x hx y hy
    obtain ⟨rx, hrx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ry, hry, rfl⟩ := Finset.mem_image.mp hy
    rw [symp_add_left, symp_add_right, symp_add_right, symp_add_right, symp_add_right,
        symp_comm b a, hab1, symp_self, hb_comm ry hry, symp_comm rx a, ha_comm rx hrx,
        symp_comm rx b, hb_comm rx hrx, hR.2.2.2 rx hrx ry hry]; simp
  -- Disjointness & union `Rp = R ∪ C1 ∪ C2 ∪ C3`!
  have hd01 : Disjoint R C1 := by
    rw [Finset.disjoint_left]; intro x hxR hx1
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx1
    exact haR (pauliIdx_add_cancel_right a r ▸ hR.2.2.1 _ hxR r hr)
  have hd02 : Disjoint R C2 := by
    rw [Finset.disjoint_left]; intro x hxR hx2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx2
    exact hbR (pauliIdx_add_cancel_right b r ▸ hR.2.2.1 _ hxR r hr)
  have hd03 : Disjoint R C3 := by
    rw [Finset.disjoint_left]; intro x hxR hx3
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx3
    exact habR (pauliIdx_add_cancel_right (a + b) r ▸ hR.2.2.1 _ hxR r hr)
  have hd12 : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h := hsymp_12 x hx1 x hx2; rw [symp_self] at h; exact absurd h (by decide)
  have hd13 : Disjoint C1 C3 := by
    rw [Finset.disjoint_left]; intro x hx1 hx3
    have h := hsymp_13 x hx1 x hx3; rw [symp_self] at h; exact absurd h (by decide)
  have hd23 : Disjoint C2 C3 := by
    rw [Finset.disjoint_left]; intro x hx2 hx3
    have h := hsymp_23 x hx2 x hx3; rw [symp_self] at h; exact absurd h (by decide)
  have hRp_eq : R ∪ C1 ∪ C2 ∪ C3 = Rp := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · refine Finset.union_subset (Finset.union_subset (Finset.union_subset hR_sub_Rp ?_) ?_) ?_
      · intro x hx; exact hL1_sub_Rp (Finset.mem_union_right _ hx)
      · intro x hx; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => by rw [symp_add_left, hb_comm y hy, hR.2.2.2 r hr y hy, add_zero]⟩
      · intro x hx; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy => by rw [symp_add_left, hab_comm y hy, hR.2.2.2 r hr y hy, add_zero]⟩
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd03, hd13⟩, hd23⟩),
          Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩),
          Finset.card_union_of_disjoint hd01, hR.2.1, hcardC, hcardC, hcardC, hRp_card]; norm_num
  let Z0 := Z ∩ R
  let Z1 := Z ∩ C1
  let Z2 := Z ∩ C2
  let Z3 := Z ∩ C3
  have hZ_sub_Rp : Z ⊆ Rp := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZ_perp x hx⟩
  have hZ_eq : Z = Z0 ∪ Z1 ∪ Z2 ∪ Z3 := by
    calc Z = Z ∩ Rp := (Finset.inter_eq_left.mpr hZ_sub_Rp).symm
      _ = Z ∩ (R ∪ C1 ∪ C2 ∪ C3) := by rw [hRp_eq]
      _ = Z0 ∪ Z1 ∪ Z2 ∪ Z3 := by simp only [Finset.inter_union_distrib_left, Z0, Z1, Z2, Z3]
  have hdZ01 : Disjoint Z0 Z1 := hd01.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdZ02 : Disjoint Z0 Z2 := hd02.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdZ03 : Disjoint Z0 Z3 := hd03.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdZ12 : Disjoint Z1 Z2 := hd12.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdZ13 : Disjoint Z1 Z3 := hd13.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdZ23 : Disjoint Z2 Z3 := hd23.mono Finset.inter_subset_right Finset.inter_subset_right
  refine ⟨Z1.card, Z2.card, Z3.card,
    by calc Z1.card ≤ C1.card := Finset.card_le_card Finset.inter_subset_right
      _ = 8 := hcardC a,
    by calc Z2.card ≤ C2.card := Finset.card_le_card Finset.inter_subset_right
      _ = 8 := hcardC b,
    by calc Z3.card ≤ C3.card := Finset.card_le_card Finset.inter_subset_right
      _ = 8 := hcardC (a + b), ?_, ?_, ?_, ?_, ?_⟩
  · conv_rhs => rw [hZ_eq]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hdZ03, hdZ13⟩, hdZ23⟩),
        Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdZ02, hdZ12⟩),
        Finset.card_union_of_disjoint hdZ01]
  · have h := hs L1 hL1
    have : Z ∩ L1 = Z0 ∪ Z1 := Finset.inter_union_distrib_left Z R C1
    rw [this, Finset.card_union_of_disjoint hdZ01] at h; exact h
  · have h := hs L2 hL2
    have : Z ∩ L2 = Z0 ∪ Z2 := Finset.inter_union_distrib_left Z R C2
    rw [this, Finset.card_union_of_disjoint hdZ02] at h; exact h
  · have h := hs L3 hL3
    have : Z ∩ L3 = Z0 ∪ Z3 := Finset.inter_union_distrib_left Z R C3
    rw [this, Finset.card_union_of_disjoint hdZ03] at h; exact h
  · -- Compute `antiCount Z` directly on `Z0 ∪ Z1 ∪ Z2 ∪ Z3`!
    have hdeg0 : ∀ x ∈ Z0, (Z.filter fun y => symp x y = 1).card = 0 := fun x hx =>
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun y hy => by
        rw [symp_comm, hZ_perp y hy x (Finset.mem_inter.mp hx).2]; decide)
    have hdeg1 : ∀ x ∈ Z1, (Z.filter fun y => symp x y = 1).card = Z2.card + Z3.card := by
      intro x hx
      have hxC1 := (Finset.mem_inter.mp hx).2
      have hflt : Z.filter (fun y => symp x y = 1) = Z2 ∪ Z3 := by
        ext y; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hyZ, h1⟩
          rw [hZ_eq] at hyZ
          rcases Finset.mem_union.mp hyZ with h012 | hy3
          · rcases Finset.mem_union.mp h012 with h01 | hy2
            · rcases Finset.mem_union.mp h01 with hy0 | hy1
              · rw [hZ_perp x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy0).2] at h1
                exact absurd h1 (by decide)
              · have := hL1.2.2.2 x (Finset.mem_union_right _ hxC1) y (Finset.mem_union_right _ (Finset.mem_inter.mp hy1).2)
                rw [this] at h1; exact absurd h1 (by decide)
            · exact Or.inl hy2
          · exact Or.inr hy3
        · rintro (hy2 | hy3)
          · exact ⟨(Finset.mem_inter.mp hy2).1, hsymp_12 x hxC1 y (Finset.mem_inter.mp hy2).2⟩
          · exact ⟨(Finset.mem_inter.mp hy3).1, hsymp_13 x hxC1 y (Finset.mem_inter.mp hy3).2⟩
      rw [hflt, Finset.card_union_of_disjoint hdZ23]
    have hdeg2 : ∀ x ∈ Z2, (Z.filter fun y => symp x y = 1).card = Z1.card + Z3.card := by
      intro x hx
      have hxC2 := (Finset.mem_inter.mp hx).2
      have hflt : Z.filter (fun y => symp x y = 1) = Z1 ∪ Z3 := by
        ext y; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hyZ, h1⟩
          rw [hZ_eq] at hyZ
          rcases Finset.mem_union.mp hyZ with h012 | hy3
          · rcases Finset.mem_union.mp h012 with h01 | hy2
            · rcases Finset.mem_union.mp h01 with hy0 | hy1
              · rw [hZ_perp x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy0).2] at h1
                exact absurd h1 (by decide)
              · exact Or.inl hy1
            · have := hL2.2.2.2 x (Finset.mem_union_right _ hxC2) y (Finset.mem_union_right _ (Finset.mem_inter.mp hy2).2)
              rw [this] at h1; exact absurd h1 (by decide)
          · exact Or.inr hy3
        · rintro (hy1 | hy3)
          · exact ⟨(Finset.mem_inter.mp hy1).1, by rw [symp_comm]; exact hsymp_12 y (Finset.mem_inter.mp hy1).2 x hxC2⟩
          · exact ⟨(Finset.mem_inter.mp hy3).1, hsymp_23 x hxC2 y (Finset.mem_inter.mp hy3).2⟩
      rw [hflt, Finset.card_union_of_disjoint hdZ13]
    have hdeg3 : ∀ x ∈ Z3, (Z.filter fun y => symp x y = 1).card = Z1.card + Z2.card := by
      intro x hx
      have hxC3 := (Finset.mem_inter.mp hx).2
      have hflt : Z.filter (fun y => symp x y = 1) = Z1 ∪ Z2 := by
        ext y; simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hyZ, h1⟩
          rw [hZ_eq] at hyZ
          rcases Finset.mem_union.mp hyZ with h012 | hy3
          · rcases Finset.mem_union.mp h012 with h01 | hy2
            · rcases Finset.mem_union.mp h01 with hy0 | hy1
              · rw [hZ_perp x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy0).2] at h1
                exact absurd h1 (by decide)
              · exact Or.inl hy1
            · exact Or.inr hy2
          · have := hL3.2.2.2 x (Finset.mem_union_right _ hxC3) y (Finset.mem_union_right _ (Finset.mem_inter.mp hy3).2)
            rw [this] at h1; exact absurd h1 (by decide)
        · rintro (hy1 | hy2)
          · exact ⟨(Finset.mem_inter.mp hy1).1, by rw [symp_comm]; exact hsymp_13 y (Finset.mem_inter.mp hy1).2 x hxC3⟩
          · exact ⟨(Finset.mem_inter.mp hy2).1, by rw [symp_comm]; exact hsymp_23 y (Finset.mem_inter.mp hy2).2 x hxC3⟩
      rw [hflt, Finset.card_union_of_disjoint hdZ12]
    simp only [antiCount]
    conv_lhs => arg 1; rw [hZ_eq]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hdZ03, hdZ13⟩, hdZ23⟩),
        Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdZ02, hdZ12⟩),
        Finset.sum_union hdZ01,
        Finset.sum_congr rfl hdeg0, Finset.sum_congr rfl hdeg1,
        Finset.sum_congr rfl hdeg2, Finset.sum_congr rfl hdeg3]
    simp only [Finset.sum_const, smul_eq_mul, mul_zero, zero_add]
    ring

/-- Ordered 3-variable quadratic lower bound for `r = 3, s ≤ 9`. -/
private lemma quad_3_s9_ordered {n0 a b c : ℕ} (hba : b ≤ a) (hcb : c ≤ b)
    (hn0 : n0 ≤ 8) (ha : n0 + a ≤ 9) :
    (11 ≤ n0 + a + b + c → n0 = 8 → 3 ≤ a * b + a * c + b * c) ∧
    (11 ≤ n0 + a + b + c → n0 = 7 → 4 ≤ a * b + a * c + b * c) ∧
    (11 ≤ n0 + a + b + c → n0 ≤ 6 → 6 ≤ a * b + a * c + b * c) ∧
    (12 ≤ n0 + a + b + c → 8 ≤ a * b + a * c + b * c) ∧
    (13 ≤ n0 + a + b + c → 12 ≤ a * b + a * c + b * c) ∧
    (14 ≤ n0 + a + b + c → 16 ≤ a * b + a * c + b * c) ∧
    (15 ≤ n0 + a + b + c → 17 ≤ a * b + a * c + b * c) := by
  refine ⟨fun hm h8 => ?_, fun hm h7 => ?_, fun hm h6 => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · have : a = 1 ∧ b = 1 ∧ c = 1 := by omega
    nlinarith
  · have : a = 2 ∧ 2 ≤ b + c := by omega
    nlinarith
  · by_cases ha2 : a ≤ 2
    · have : a = 2 ∧ b = 2 ∧ 1 ≤ c := by omega
      nlinarith
    · have : 3 ≤ a ∧ 2 ≤ b + c := by omega
      nlinarith
  · by_cases ha2 : a ≤ 2
    · have : a = 2 ∧ b = 2 ∧ 1 ≤ c := by omega
      nlinarith
    · have : 3 ≤ a ∧ 3 ≤ b + c := by omega
      nlinarith
  · by_cases ha2 : a ≤ 2
    · have : a = 2 ∧ b = 2 ∧ c = 2 := by omega
      nlinarith
    · have : 3 ≤ a ∧ 4 ≤ b + c := by omega
      nlinarith
  · by_cases ha3 : a ≤ 3
    · have : a = 3 ∧ b = 3 ∧ 2 ≤ c := by omega
      nlinarith
    · have : 4 ≤ a ∧ 5 ≤ b + c := by omega
      nlinarith
  · have : 3 ≤ a ∧ 6 ≤ b + c := by omega
    nlinarith

/-- Symmetric 3-variable quadratic lower bound for `r = 3, s ≤ 9`. -/
private lemma quad_3_s9_lb {n0 n1 n2 n3 : ℕ} (hn0 : n0 ≤ 8)
    (hs1 : n0 + n1 ≤ 9) (hs2 : n0 + n2 ≤ 9) (hs3 : n0 + n3 ≤ 9) :
    (11 ≤ n0 + n1 + n2 + n3 → n0 = 8 → 3 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (11 ≤ n0 + n1 + n2 + n3 → n0 = 7 → 4 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (11 ≤ n0 + n1 + n2 + n3 → n0 ≤ 6 → 6 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (12 ≤ n0 + n1 + n2 + n3 → 8 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (13 ≤ n0 + n1 + n2 + n3 → 12 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (14 ≤ n0 + n1 + n2 + n3 → 16 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
    (15 ≤ n0 + n1 + n2 + n3 → 17 ≤ n1 * n2 + n1 * n3 + n2 * n3) := by
  have hperm : ∀ a b c : ℕ, a + b + c = n1 + n2 + n3 →
      a * b + a * c + b * c = n1 * n2 + n1 * n3 + n2 * n3 →
      b ≤ a → c ≤ b → n0 + a ≤ 9 →
      (11 ≤ n0 + n1 + n2 + n3 → n0 = 8 → 3 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (11 ≤ n0 + n1 + n2 + n3 → n0 = 7 → 4 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (11 ≤ n0 + n1 + n2 + n3 → n0 ≤ 6 → 6 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (12 ≤ n0 + n1 + n2 + n3 → 8 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (13 ≤ n0 + n1 + n2 + n3 → 12 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (14 ≤ n0 + n1 + n2 + n3 → 16 ≤ n1 * n2 + n1 * n3 + n2 * n3) ∧
      (15 ≤ n0 + n1 + n2 + n3 → 17 ≤ n1 * n2 + n1 * n3 + n2 * n3) := by
    intro a b c hsum hq hba hcb ha
    have h := quad_3_s9_ordered hba hcb hn0 ha
    have hsum' : n0 + a + b + c = n0 + n1 + n2 + n3 := by omega
    rw [hsum', hq] at h; exact h
  rcases le_total n1 n2 with h12 | h21 <;> rcases le_total n2 n3 with h23 | h32 <;> rcases le_total n1 n3 with h13 | h31
  · exact hperm n3 n2 n1 (by ring) (by ring) h23 h12 hs3
  · exact hperm n3 n2 n1 (by ring) (by ring) h23 h12 hs3
  · exact hperm n2 n3 n1 (by ring) (by ring) h32 h13 hs2
  · exact hperm n2 n1 n3 (by ring) (by ring) h12 h31 hs2
  · exact hperm n3 n1 n2 (by ring) (by ring) h13 h21 hs3
  · exact hperm n1 n3 n2 (by ring) (by ring) h31 h23 hs1
  · exact hperm n1 n2 n3 (by ring) (by ring) h21 h32 hs1
  · exact hperm n1 n2 n3 (by ring) (by ring) h21 h32 hs1

/-- Computable lower bound for the 4-level symplectic radical induction at `s ≤ 9`. -/
private lemma turan_r3_s9 {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub 3 R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    (hs : ∀ L : Finset (PauliIdx 4), IsLagrangian L → (Z ∩ L).card ≤ 9) :
    (11 ≤ Z.card → (Z ∩ R).card = 8 → 6 ≤ antiCount Z) ∧
    (11 ≤ Z.card → (Z ∩ R).card = 7 → 8 ≤ antiCount Z) ∧
    (11 ≤ Z.card → (Z ∩ R).card ≤ 6 → 12 ≤ antiCount Z) ∧
    (12 ≤ Z.card → 16 ≤ antiCount Z) ∧
    (13 ≤ Z.card → 24 ≤ antiCount Z) ∧
    (14 ≤ Z.card → 32 ≤ antiCount Z) ∧
    (15 ≤ Z.card → 34 ≤ antiCount Z) := by
  obtain ⟨n1, n2, n3, _, _, _, hsum, hs1, hs2, hs3, hA⟩ := turan_r3_decomp hR hZ_perp hs
  set n0 := (Z ∩ R).card
  have hn0 : n0 ≤ 8 := by
    calc n0 ≤ R.card := Finset.card_le_card Finset.inter_subset_right
      _ = 8 := by rw [hR.2.1]; norm_num
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := quad_3_s9_lb hn0 hs1 hs2 hs3
  exact ⟨fun hm h8 => by have := q1 (by omega) h8; omega,
         fun hm h7 => by have := q2 (by omega) h7; omega,
         fun hm h6 => by have := q3 (by omega) h6; omega,
         fun hm => by have := q4 (by omega); omega,
         fun hm => by have := q5 (by omega); omega,
         fun hm => by have := q6 (by omega); omega,
         fun hm => by have := q7 (by omega); omega⟩

/-- Helper: general induction step from `r` to `r+1` using minimum nonzero degree `d`. -/
private lemma turan_step_cases {r : ℕ} {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub r R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    (_hZ_gt : 2 ^ r < Z.card) (hZ_not_iso : ∃ x ∈ Z, ∃ y ∈ Z, symp x y = 1) :
    (∃ v ∈ Z, v ∉ R ∧ ∀ y ∈ Z, symp v y = 0) ∨
    (∃ u ∈ Z, u ∉ R ∧ 1 ≤ (Z.filter fun y => symp u y = 1).card ∧
      (∀ x ∈ Z, 1 ≤ (Z.filter fun y => symp x y = 1).card →
        (Z.filter fun y => symp u y = 1).card ≤ (Z.filter fun y => symp x y = 1).card) ∧
      (Z.filter fun y => symp u y = 1).card * (Z.card - 2 ^ r) ≤ antiCount Z) := by
  by_cases hex_iso : ∃ v ∈ Z, v ∉ R ∧ ∀ y ∈ Z, symp v y = 0
  · exact Or.inl hex_iso
  · right
    push Not at hex_iso
    let Pos := Z.filter fun x => 1 ≤ (Z.filter fun y => symp x y = 1).card
    have hPos_ne : Pos.Nonempty := by
      obtain ⟨x, hx, y, hy, hxy⟩ := hZ_not_iso
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩⟩⟩
    obtain ⟨u, huPos, huMin⟩ := Finset.exists_min_image Pos (fun x => (Z.filter fun y => symp x y = 1).card) hPos_ne
    have huZ := (Finset.mem_filter.mp huPos).1
    have hu_d1 := (Finset.mem_filter.mp huPos).2
    have huR : u ∉ R := fun hmem => by
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hu_d1)
      have hyZ := (Finset.mem_filter.mp hy).1
      have h1 := (Finset.mem_filter.mp hy).2
      rw [symp_comm, hZ_perp y hyZ u hmem] at h1; exact absurd h1 (by decide)
    -- Every `x ∈ Z \ R` has `deg_Z(x) ≥ 1`, so `|Pos| ≥ |Z| - 2^r`!
    have hZ_sub : Z \ R ⊆ Pos := by
      intro x hx
      have hxZ := (Finset.mem_sdiff.mp hx).1
      have hxR := (Finset.mem_sdiff.mp hx).2
      obtain ⟨y, hyZ, hne⟩ := hex_iso x hxZ hxR
      have h1 : symp x y = 1 := (zmod2_cases _).resolve_left hne
      exact Finset.mem_filter.mpr ⟨hxZ, Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyZ, h1⟩⟩⟩
    have hPos_card : Z.card - 2 ^ r ≤ Pos.card := by
      have h1 : (Z \ R).card ≤ Pos.card := Finset.card_le_card hZ_sub
      have h2 : Z.card - R.card ≤ (Z \ R).card := Finset.le_card_sdiff R Z
      rw [hR.2.1] at h2; omega
    have hsum_lb : (Z.filter fun y => symp u y = 1).card * (Z.card - 2 ^ r) ≤ antiCount Z := by
      calc (Z.filter fun y => symp u y = 1).card * (Z.card - 2 ^ r)
          ≤ (Z.filter fun y => symp u y = 1).card * Pos.card := Nat.mul_le_mul_left _ hPos_card
        _ = ∑ _x ∈ Pos, (Z.filter fun y => symp u y = 1).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ x ∈ Pos, (Z.filter fun y => symp x y = 1).card :=
            Finset.sum_le_sum fun x hx => huMin x hx
        _ ≤ ∑ x ∈ Z, (Z.filter fun y => symp x y = 1).card :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    refine ⟨u, huZ, huR, hu_d1, fun x hxZ hx1 => huMin x (Finset.mem_filter.mpr ⟨hxZ, hx1⟩), hsum_lb⟩

/-- Helper: in `antiCount_split` for minimum-degree `u` (`deg = d`), we have BOTH
    `antiCount Z' + d² + d ≤ antiCount Z` AND `antiCount Z' + 2 * d * ((Z' ∩ (R ∪ (u + R))).card - 2^r) ≤ antiCount Z`! -/
private lemma turan_step_bounds {r : ℕ} {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub r R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    {u : PauliIdx 4} (huZ : u ∈ Z) (huR : u ∉ R)
    (huMin : ∀ x ∈ Z, 1 ≤ (Z.filter fun y => symp x y = 1).card →
      (Z.filter fun y => symp u y = 1).card ≤ (Z.filter fun y => symp x y = 1).card) :
    let d := (Z.filter fun y => symp u y = 1).card
    let Z' := Z.filter fun x => symp u x = 0
    let R' := R ∪ R.image (u + ·)
    IsIsoSub (r + 1) R' ∧
    (∀ x ∈ Z', ∀ y ∈ R', symp x y = 0) ∧
    Z'.card + d = Z.card ∧
    antiCount Z' + d * d + d ≤ antiCount Z ∧
    antiCount Z' + 2 * d * ((Z' ∩ R').card - 2 ^ r) ≤ antiCount Z := by
  intro d Z' R'
  let B := Z.filter fun x => symp u x = 1
  have hR' : IsIsoSub (r + 1) R' := isoSub_extend_step hR huR (fun x hx => hZ_perp u huZ x hx)
  have hZ'_perp : ∀ x ∈ Z', ∀ y ∈ R', symp x y = 0 := by
    intro x hx y hy
    have hxZ := (Finset.mem_filter.mp hx).1
    have hxu := (Finset.mem_filter.mp hx).2
    rcases Finset.mem_union.mp hy with hyR | hyI
    · exact hZ_perp x hxZ y hyR
    · obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp hyI
      rw [symp_add_right, symp_comm x u, hxu, hZ_perp x hxZ t htR, add_zero]
  have hcard_eq : Z'.card + d = Z.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Z) (p := fun x => symp u x = 0)
    have hBeq : Z.filter (fun x => ¬symp u x = 0) = B := by
      ext x; simp only [B, Finset.mem_filter]
      exact ⟨fun ⟨hx, hn⟩ => ⟨hx, (zmod2_cases _).resolve_left hn⟩,
             fun ⟨hx, h1⟩ => ⟨hx, by rw [h1]; decide⟩⟩
    rw [hBeq] at h; exact h
  have hsp := antiCount_split Z u
  change antiCount Z = antiCount Z' + (∑ w ∈ B, (Z.filter fun y => symp w y = 1).card) +
    (∑ w ∈ B, (Z'.filter fun y => symp w y = 1).card) at hsp
  -- Every `w ∈ B` anticommutes with `u ∈ Z'`, so `deg_Z(w) ≥ d` and `deg_{Z'}(w) ≥ 1`!
  have huZ' : u ∈ Z' := Finset.mem_filter.mpr ⟨huZ, symp_self u⟩
  have hdegZ_B : ∀ w ∈ B, d ≤ (Z.filter fun y => symp w y = 1).card := fun w hw =>
    huMin w (Finset.mem_filter.mp hw).1 (Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr
      ⟨huZ, by rw [symp_comm]; exact (Finset.mem_filter.mp hw).2⟩⟩)
  have hdegZ'_B1 : ∀ w ∈ B, 1 ≤ (Z'.filter fun y => symp w y = 1).card := fun w hw =>
    Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨huZ', by rw [symp_comm]; exact (Finset.mem_filter.mp hw).2⟩⟩
  have hb1 : antiCount Z' + d * d + d ≤ antiCount Z := by
    have s1 : d * d ≤ ∑ w ∈ B, (Z.filter fun y => symp w y = 1).card := by
      calc d * d = ∑ _w ∈ B, d := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hdegZ_B
    have s2 : d ≤ ∑ w ∈ B, (Z'.filter fun y => symp w y = 1).card := by
      calc d = ∑ _w ∈ B, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hdegZ'_B1
    omega
  -- Every `w ∈ B` anticommutes with ALL of `Z' ∩ (u + R)` (whose size is `≥ |Z' ∩ R'| - 2^r`)!
  have hb2 : antiCount Z' + 2 * d * ((Z' ∩ R').card - 2 ^ r) ≤ antiCount Z := by
    let K := Z' ∩ R.image (u + ·)
    have hK_card : (Z' ∩ R').card - 2 ^ r ≤ K.card := by
      have hun : Z' ∩ R' = (Z' ∩ R) ∪ K := Finset.inter_union_distrib_left Z' R (R.image (u + ·))
      have hle : (Z' ∩ R').card ≤ (Z' ∩ R).card + K.card := by rw [hun]; exact Finset.card_union_le _ _
      have hRle : (Z' ∩ R).card ≤ 2 ^ r := by
        calc (Z' ∩ R).card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
          _ = 2 ^ r := hR.2.1
      omega
    have hdeg_K : ∀ w ∈ B, K.card ≤ (Z'.filter fun y => symp w y = 1).card := fun w hw => by
      refine Finset.card_le_card fun y hy => ?_
      have hyZ' := (Finset.mem_inter.mp hy).1
      obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).2
      refine Finset.mem_filter.mpr ⟨hyZ', ?_⟩
      rw [symp_add_right, symp_comm w u, (Finset.mem_filter.mp hw).2,
          hZ_perp w (Finset.mem_filter.mp hw).1 t htR, add_zero]
    have hdeg_KZ : ∀ w ∈ B, K.card ≤ (Z.filter fun y => symp w y = 1).card := fun w hw =>
      le_trans (hdeg_K w hw) (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
    have s1 : d * K.card ≤ ∑ w ∈ B, (Z.filter fun y => symp w y = 1).card := by
      calc d * K.card = ∑ _w ∈ B, K.card := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hdeg_KZ
    have s2 : d * K.card ≤ ∑ w ∈ B, (Z'.filter fun y => symp w y = 1).card := by
      calc d * K.card = ∑ _w ∈ B, K.card := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hdeg_K
    have hm : 2 * d * ((Z' ∩ R').card - 2 ^ r) ≤ 2 * (d * K.card) := by
      calc 2 * d * ((Z' ∩ R').card - 2 ^ r) = 2 * (d * ((Z' ∩ R').card - 2 ^ r)) := by ring
        _ ≤ 2 * (d * K.card) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d hK_card)
    omega
  exact ⟨hR', hZ'_perp, hcard_eq, hb1, hb2⟩

/-- Level `r = 2` of symplectic radical induction at `s ≤ 9`. -/
private lemma turan_r2_s9 {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub 2 R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    (hs : ∀ L : Finset (PauliIdx 4), IsLagrangian L → (Z ∩ L).card ≤ 9) :
    (12 ≤ Z.card → 14 ≤ antiCount Z) ∧
    (13 ≤ Z.card → 18 ≤ antiCount Z) ∧
    (14 ≤ Z.card → 22 ≤ antiCount Z) ∧
    (15 ≤ Z.card → 30 ≤ antiCount Z) ∧
    (16 ≤ Z.card → 34 ≤ antiCount Z) := by
  have hcore : ∀ (m : ℕ), Z.card = m → 12 ≤ m →
      (m = 12 → 14 ≤ antiCount Z) ∧
      (m = 13 → 18 ≤ antiCount Z) ∧
      (m = 14 → 22 ≤ antiCount Z) ∧
      (m = 15 → 30 ≤ antiCount Z) ∧
      (16 ≤ m → 34 ≤ antiCount Z) := by
    intro m hm hm12
    have hnot_iso : ∃ x ∈ Z, ∃ y ∈ Z, symp x y = 1 := by
      by_contra hall; push Not at hall
      have hiso : ∀ x ∈ Z, ∀ y ∈ Z, symp x y = 0 := fun x hx y hy =>
        (zmod2_cases _).resolve_right (hall x hx y hy)
      obtain ⟨L, hL, hZL⟩ := exists_lagrangian_superset Z hiso
      have := hs L hL; rw [Finset.inter_eq_left.mpr hZL] at this; omega
    have hcase := turan_step_cases hR hZ_perp (by omega) hnot_iso
    rcases hcase with ⟨v, hvZ, hvR, hv_iso⟩ | ⟨u, huZ, huR, hd1, huMin, hsum_lb⟩
    · let R' := R ∪ R.image (v + ·)
      have hR' : IsIsoSub 3 R' := isoSub_extend_step hR hvR (fun x hx => hZ_perp v hvZ x hx)
      have hZ'_perp : ∀ x ∈ Z, ∀ y ∈ R', symp x y = 0 := by
        intro x hx y hy; rcases Finset.mem_union.mp hy with hyR | hyI
        · exact hZ_perp x hx y hyR
        · obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp hyI
          rw [symp_add_right, symp_comm x v, hv_iso x hx, hZ_perp x hx t htR, add_zero]
      obtain ⟨_, _, _, h12, h13, h14, h15⟩ := turan_r3_s9 hR' hZ'_perp hs
      refine ⟨fun h => by have := h12 (by omega); omega,
              fun h => by have := h13 (by omega); omega,
              fun h => by have := h14 (by omega); omega,
              fun h => by have := h15 (by omega); omega,
              fun h => by have := h15 (by omega); omega⟩
    · obtain ⟨hR', hZ'_perp, hcard_eq, hb1, hb2⟩ := turan_step_bounds hR hZ_perp huZ huR huMin
      set d := (Z.filter fun y => symp u y = 1).card
      set Z' := Z.filter fun x => symp u x = 0
      set R' := R ∪ R.image (u + ·)
      have hb2' : antiCount Z' + 2 * d * ((Z' ∩ R').card - 4) ≤ antiCount Z := hb2
      have hsum_lb' : d * (Z.card - 4) ≤ antiCount Z := hsum_lb
      have hs' : ∀ L, IsLagrangian L → (Z' ∩ L).card ≤ 9 := fun L hL =>
        le_trans (Finset.card_le_card (Finset.inter_subset_inter_right (Finset.filter_subset _ _))) (hs L hL)
      obtain ⟨hr11_8, hr11_7, hr11_6, hr12, hr13, hr14, _⟩ := turan_r3_s9 hR' hZ'_perp hs'
      have hR'_n0 : (Z' ∩ R').card ≤ 8 := by
        calc (Z' ∩ R').card ≤ R'.card := Finset.card_le_card Finset.inter_subset_right
          _ = 8 := by rw [hR'.2.1]; norm_num
      have hZ'_11 : 11 ≤ Z'.card → 14 ≤ antiCount Z := by
        intro h11
        by_cases h8 : (Z' ∩ R').card = 8
        · have := hr11_8 h11 h8
          have hmul : 8 ≤ 2 * d * ((Z' ∩ R').card - 4) := by
            rw [h8]; exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd1) (le_refl 4)
          omega
        · by_cases h7 : (Z' ∩ R').card = 7
          · have := hr11_7 h11 h7
            have hmul : 6 ≤ 2 * d * ((Z' ∩ R').card - 4) := by
              rw [h7]; exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd1) (le_refl 3)
            omega
          · have h6 : (Z' ∩ R').card ≤ 6 := by omega
            have := hr11_6 h11 h6
            have hmul : 1 ≤ d * d := Nat.mul_le_mul hd1 hd1
            omega
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · by_cases hd2 : 2 ≤ d
        · have : 16 ≤ d * (Z.card - 4) := Nat.mul_le_mul hd2 (show 8 ≤ Z.card - 4 by omega)
          omega
        · exact hZ'_11 (by omega)
      · by_cases hd2 : 2 ≤ d
        · have : 18 ≤ d * (Z.card - 4) := Nat.mul_le_mul hd2 (show 9 ≤ Z.card - 4 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr12 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 30 ≤ d * (Z.card - 4) := Nat.mul_le_mul hd3 (show 10 ≤ Z.card - 4 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr12 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr13 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 33 ≤ d * (Z.card - 4) := Nat.mul_le_mul hd3 (show 11 ≤ Z.card - 4 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr13 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr14 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 36 ≤ d * (Z.card - 4) := Nat.mul_le_mul hd3 (show 12 ≤ Z.card - 4 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr14 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr14 (by omega); rw [hd1_eq] at hb1; omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => (hcore Z.card rfl (by omega)).2.2.2.2 h⟩
  · rcases (show Z.card = 12 ∨ Z.card = 13 ∨ Z.card = 14 ∨ Z.card = 15 ∨ 16 ≤ Z.card by omega) with
      h1 | h1 | h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).1 h1
    · have := (hcore Z.card rfl (by omega)).2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 13 ∨ Z.card = 14 ∨ Z.card = 15 ∨ 16 ≤ Z.card by omega) with
      h1 | h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 14 ∨ Z.card = 15 ∨ 16 ≤ Z.card by omega) with h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 15 ∨ 16 ≤ Z.card by omega) with h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.2.2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega

/-- Level `r = 1` of symplectic radical induction at `s ≤ 9`. -/
private lemma turan_r1_s9 {R Z : Finset (PauliIdx 4)} (hR : IsIsoSub 1 R)
    (hZ_perp : ∀ x ∈ Z, ∀ y ∈ R, symp x y = 0)
    (hs : ∀ L : Finset (PauliIdx 4), IsLagrangian L → (Z ∩ L).card ≤ 9) :
    (13 ≤ Z.card → 16 ≤ antiCount Z) ∧
    (14 ≤ Z.card → 20 ≤ antiCount Z) ∧
    (15 ≤ Z.card → 24 ≤ antiCount Z) ∧
    (16 ≤ Z.card → 28 ≤ antiCount Z) ∧
    (17 ≤ Z.card → 36 ≤ antiCount Z) := by
  have hcore : ∀ (m : ℕ), Z.card = m → 13 ≤ m →
      (m = 13 → 16 ≤ antiCount Z) ∧
      (m = 14 → 20 ≤ antiCount Z) ∧
      (m = 15 → 24 ≤ antiCount Z) ∧
      (m = 16 → 28 ≤ antiCount Z) ∧
      (17 ≤ m → 36 ≤ antiCount Z) := by
    intro m hm hm13
    have hnot_iso : ∃ x ∈ Z, ∃ y ∈ Z, symp x y = 1 := by
      by_contra hall; push Not at hall
      have hiso : ∀ x ∈ Z, ∀ y ∈ Z, symp x y = 0 := fun x hx y hy =>
        (zmod2_cases _).resolve_right (hall x hx y hy)
      obtain ⟨L, hL, hZL⟩ := exists_lagrangian_superset Z hiso
      have := hs L hL; rw [Finset.inter_eq_left.mpr hZL] at this; omega
    have hcase := turan_step_cases hR hZ_perp (by omega) hnot_iso
    rcases hcase with ⟨v, hvZ, hvR, hv_iso⟩ | ⟨u, huZ, huR, hd1, huMin, hsum_lb⟩
    · let R' := R ∪ R.image (v + ·)
      have hR' : IsIsoSub 2 R' := isoSub_extend_step hR hvR (fun x hx => hZ_perp v hvZ x hx)
      have hZ'_perp : ∀ x ∈ Z, ∀ y ∈ R', symp x y = 0 := by
        intro x hx y hy; rcases Finset.mem_union.mp hy with hyR | hyI
        · exact hZ_perp x hx y hyR
        · obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp hyI
          rw [symp_add_right, symp_comm x v, hv_iso x hx, hZ_perp x hx t htR, add_zero]
      obtain ⟨_, h13, h14, h15, h16⟩ := turan_r2_s9 hR' hZ'_perp hs
      -- Wait: if `Z.card ≥ 17` and `IsIsoSub 2 R'`, we need `36 ≤ antiCount Z`!
      -- Check `r = 2, m ≥ 17`: `d ≥ 3 ⇒ 3 * 13 = 39 ≥ 36`, `d = 2 ⇒ |Z'| ≥ 15 ⇒ 30 + 6 = 36`, `d = 1 ⇒ |Z'| ≥ 16 ⇒ 34 + 2 = 36`!
      have h17_r2 : 17 ≤ Z.card → 36 ≤ antiCount Z := by
        intro h17
        have hc2 := turan_step_cases hR' hZ'_perp (by omega) hnot_iso
        rcases hc2 with ⟨v2, hv2Z, hv2R, hv2_iso⟩ | ⟨u2, hu2Z, hu2R, hd21, hu2Min, hsum2_lb⟩
        · let R2 := R' ∪ R'.image (v2 + ·)
          have hR2 : IsIsoSub 3 R2 := isoSub_extend_step hR' hv2R (fun x hx => hZ'_perp v2 hv2Z x hx)
          have hZ2_perp : ∀ x ∈ Z, ∀ y ∈ R2, symp x y = 0 := by
            intro x hx y hy; rcases Finset.mem_union.mp hy with hyR | hyI
            · exact hZ'_perp x hx y hyR
            · obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp hyI
              rw [symp_add_right, symp_comm x v2, hv2_iso x hx, hZ'_perp x hx t htR, add_zero]
          obtain ⟨n1, n2, n3, _, _, _, hsum, hs1, hs2, hs3, hA⟩ := turan_r3_decomp hR2 hZ2_perp hs
          have h18 : 18 ≤ n1 * n2 + n1 * n3 + n2 * n3 := by
            have hsum' : 17 ≤ (Z ∩ R2).card + n1 + n2 + n3 := by omega
            rcases le_total n1 n2 with h12 | h21 <;> rcases le_total n2 n3 with h23 | h32 <;> rcases le_total n1 n3 with h13 | h31
            · have : 3 ≤ n3 ∧ 8 ≤ n1 + n2 := by omega
              nlinarith
            · have : 3 ≤ n3 ∧ 8 ≤ n1 + n2 := by omega
              nlinarith
            · have : 3 ≤ n2 ∧ 8 ≤ n1 + n3 := by omega
              nlinarith
            · have : 3 ≤ n2 ∧ 8 ≤ n1 + n3 := by omega
              nlinarith
            · have : 3 ≤ n3 ∧ 8 ≤ n1 + n2 := by omega
              nlinarith
            · have : 3 ≤ n1 ∧ 8 ≤ n2 + n3 := by omega
              nlinarith
            · have : 3 ≤ n1 ∧ 8 ≤ n2 + n3 := by omega
              nlinarith
            · have : 3 ≤ n1 ∧ 8 ≤ n2 + n3 := by omega
              nlinarith
          omega
        · obtain ⟨hR2, hZ2_perp, hcard2, hb21, _⟩ := turan_step_bounds hR' hZ'_perp hu2Z hu2R hu2Min
          set d2 := (Z.filter fun y => symp u2 y = 1).card
          set Z2 := Z.filter fun x => symp u2 x = 0
          have hsum2_lb' : d2 * (Z.card - 4) ≤ antiCount Z := hsum2_lb
          have hs2 : ∀ L, IsLagrangian L → (Z2 ∩ L).card ≤ 9 := fun L hL =>
            le_trans (Finset.card_le_card (Finset.inter_subset_inter_right (Finset.filter_subset _ _))) (hs L hL)
          obtain ⟨_, _, _, _, _, hr14, hr15⟩ := turan_r3_s9 hR2 hZ2_perp hs2
          by_cases hd23 : 3 ≤ d2
          · have : 39 ≤ d2 * (Z.card - 4) := Nat.mul_le_mul hd23 (show 13 ≤ Z.card - 4 by omega)
            omega
          · by_cases hd22 : d2 = 2
            · have := hr14 (by omega); rw [hd22] at hb21; omega
            · have hd21_eq : d2 = 1 := by omega
              have := hr15 (by omega); rw [hd21_eq] at hb21; omega
      refine ⟨fun h => by have := h13 (by omega); omega,
              fun h => by have := h14 (by omega); omega,
              fun h => by have := h15 (by omega); omega,
              fun h => by have := h16 (by omega); omega,
              fun h => h17_r2 (by omega)⟩
    · obtain ⟨hR', hZ'_perp, hcard_eq, hb1, _⟩ := turan_step_bounds hR hZ_perp huZ huR huMin
      set d := (Z.filter fun y => symp u y = 1).card
      set Z' := Z.filter fun x => symp u x = 0
      have hsum_lb' : d * (Z.card - 2) ≤ antiCount Z := hsum_lb
      have hs' : ∀ L, IsLagrangian L → (Z' ∩ L).card ≤ 9 := fun L hL =>
        le_trans (Finset.card_le_card (Finset.inter_subset_inter_right (Finset.filter_subset _ _))) (hs L hL)
      obtain ⟨hr12, hr13, hr14, hr15, hr16⟩ := turan_r2_s9 hR' hZ'_perp hs'
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · by_cases hd2 : 2 ≤ d
        · have : 22 ≤ d * (Z.card - 2) := Nat.mul_le_mul hd2 (show 11 ≤ Z.card - 2 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr12 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd2 : 2 ≤ d
        · have : 24 ≤ d * (Z.card - 2) := Nat.mul_le_mul hd2 (show 12 ≤ Z.card - 2 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr13 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd2 : 2 ≤ d
        · have : 26 ≤ d * (Z.card - 2) := Nat.mul_le_mul hd2 (show 13 ≤ Z.card - 2 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr14 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 42 ≤ d * (Z.card - 2) := Nat.mul_le_mul hd3 (show 14 ≤ Z.card - 2 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr14 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr15 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 45 ≤ d * (Z.card - 2) := Nat.mul_le_mul hd3 (show 15 ≤ Z.card - 2 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr15 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr16 (by omega); rw [hd1_eq] at hb1; omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => (hcore Z.card rfl (by omega)).2.2.2.2 h⟩
  · rcases (show Z.card = 13 ∨ Z.card = 14 ∨ Z.card = 15 ∨ Z.card = 16 ∨ 17 ≤ Z.card by omega) with
      h1 | h1 | h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).1 h1
    · have := (hcore Z.card rfl (by omega)).2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 14 ∨ Z.card = 15 ∨ Z.card = 16 ∨ 17 ≤ Z.card by omega) with h1 | h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 15 ∨ Z.card = 16 ∨ 17 ≤ Z.card by omega) with h1 | h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.2.1 h1; omega
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega
  · rcases (show Z.card = 16 ∨ 17 ≤ Z.card by omega) with h1 | h1
    · exact (hcore Z.card rfl (by omega)).2.2.2.1 h1
    · have := (hcore Z.card rfl (by omega)).2.2.2.2 h1; omega

/-- Master `s ≤ 9` Symplectic Turán Theorem on `𝔽₂⁸` (Level `r = 0`, `R = {0}`):
    If `∀ L, IsLagrangian L → (Z ∩ L).card ≤ 9`, then
    `|Z| ≥ 14 ⇒ A(Z) ≥ 16`, `|Z| ≥ 15 ⇒ A(Z) ≥ 20`, `|Z| ≥ 16 ⇒ A(Z) ≥ 24`,
    `|Z| ≥ 17 ⇒ A(Z) ≥ 28`, `|Z| ≥ 18 ⇒ A(Z) ≥ 32`. -/
lemma symp_turan_le_nine (Z : Finset (PauliIdx 4))
    (hs : ∀ L : Finset (PauliIdx 4), IsLagrangian L → (Z ∩ L).card ≤ 9) :
    (Z.card = 14 → 16 ≤ antiCount Z) ∧
    (Z.card = 15 → 20 ≤ antiCount Z) ∧
    (Z.card = 16 → 24 ≤ antiCount Z) ∧
    (Z.card = 17 → 28 ≤ antiCount Z) ∧
    (Z.card = 18 → 32 ≤ antiCount Z) := by
  let R0 : Finset (PauliIdx 4) := {0}
  have hR0 : IsIsoSub 0 R0 := ⟨Finset.mem_singleton_self 0, by simp [R0],
    fun x hx y hy => by simp only [R0, Finset.mem_singleton] at hx hy ⊢; simp [hx, hy],
    fun x hx y hy => by simp only [R0, Finset.mem_singleton] at hx hy; simp [hx, hy, symp_self]⟩
  have hZ_perp : ∀ x ∈ Z, ∀ y ∈ R0, symp x y = 0 := fun x _ y hy => by
    simp only [R0, Finset.mem_singleton] at hy; rw [hy, symp_zero_right]
  have hnot_iso : 14 ≤ Z.card → ∃ x ∈ Z, ∃ y ∈ Z, symp x y = 1 := fun h14 => by
    by_contra hall; push Not at hall
    have hiso : ∀ x ∈ Z, ∀ y ∈ Z, symp x y = 0 := fun x hx y hy =>
      (zmod2_cases _).resolve_right (hall x hx y hy)
    obtain ⟨L, hL, hZL⟩ := exists_lagrangian_superset Z hiso
    have := hs L hL; rw [Finset.inter_eq_left.mpr hZL] at this; omega
  have hmain : 14 ≤ Z.card →
      (Z.card = 14 → 16 ≤ antiCount Z) ∧
      (Z.card = 15 → 20 ≤ antiCount Z) ∧
      (Z.card = 16 → 24 ≤ antiCount Z) ∧
      (Z.card = 17 → 28 ≤ antiCount Z) ∧
      (Z.card = 18 → 32 ≤ antiCount Z) := by
    intro h14
    have hcase := turan_step_cases hR0 hZ_perp (by omega) (hnot_iso h14)
    rcases hcase with ⟨v, hvZ, hvR, hv_iso⟩ | ⟨u, huZ, huR, hd1, huMin, hsum_lb⟩
    · let R' := R0 ∪ R0.image (v + ·)
      have hR' : IsIsoSub 1 R' := isoSub_extend_step hR0 hvR (fun x hx => hZ_perp v hvZ x hx)
      have hZ'_perp : ∀ x ∈ Z, ∀ y ∈ R', symp x y = 0 := by
        intro x hx y hy; rcases Finset.mem_union.mp hy with hyR | hyI
        · exact hZ_perp x hx y hyR
        · obtain ⟨t, htR, rfl⟩ := Finset.mem_image.mp hyI
          rw [symp_add_right, symp_comm x v, hv_iso x hx, hZ_perp x hx t htR, add_zero]
      obtain ⟨_, h14', h15', h16', h17'⟩ := turan_r1_s9 hR' hZ'_perp hs
      exact ⟨fun h => by have := h14' (by omega); omega,
             fun h => by have := h15' (by omega); omega,
             fun h => by have := h16' (by omega); omega,
             fun h => by have := h17' (by omega); omega,
             fun h => by have := h17' (by omega); omega⟩
    · obtain ⟨hR', hZ'_perp, hcard_eq, hb1, _⟩ := turan_step_bounds hR0 hZ_perp huZ huR huMin
      set d := (Z.filter fun y => symp u y = 1).card
      set Z' := Z.filter fun x => symp u x = 0
      have hsum_lb' : d * (Z.card - 1) ≤ antiCount Z := hsum_lb
      have hs' : ∀ L, IsLagrangian L → (Z' ∩ L).card ≤ 9 := fun L hL =>
        le_trans (Finset.card_le_card (Finset.inter_subset_inter_right (Finset.filter_subset _ _))) (hs L hL)
      obtain ⟨hr13, hr14, hr15, hr16, hr17⟩ := turan_r1_s9 hR' hZ'_perp hs'
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · by_cases hd2 : 2 ≤ d
        · have : 26 ≤ d * (Z.card - 1) := Nat.mul_le_mul hd2 (show 13 ≤ Z.card - 1 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr13 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd2 : 2 ≤ d
        · have : 28 ≤ d * (Z.card - 1) := Nat.mul_le_mul hd2 (show 14 ≤ Z.card - 1 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr14 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd2 : 2 ≤ d
        · have : 30 ≤ d * (Z.card - 1) := Nat.mul_le_mul hd2 (show 15 ≤ Z.card - 1 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr15 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd2 : 2 ≤ d
        · have : 32 ≤ d * (Z.card - 1) := Nat.mul_le_mul hd2 (show 16 ≤ Z.card - 1 by omega)
          omega
        · have hd1_eq : d = 1 := by omega
          have := hr16 (by omega); rw [hd1_eq] at hb1; omega
      · by_cases hd3 : 3 ≤ d
        · have : 51 ≤ d * (Z.card - 1) := Nat.mul_le_mul hd3 (show 17 ≤ Z.card - 1 by omega)
          omega
        · by_cases hd2 : d = 2
          · have := hr16 (by omega); rw [hd2] at hb1; omega
          · have hd1_eq : d = 1 := by omega
            have := hr17 (by omega); rw [hd1_eq] at hb1; omega
  exact ⟨fun h => (hmain (by omega)).1 h,
         fun h => (hmain (by omega)).2.1 h,
         fun h => (hmain (by omega)).2.2.1 h,
         fun h => (hmain (by omega)).2.2.2.1 h,
         fun h => (hmain (by omega)).2.2.2.2 h⟩

/-- Helper: `s ≥ 10` lower bound `2 * (|Z| - s) * (s - 8) ≤ antiCount Z` for any Lagrangian `L` with `s = |Z ∩ L|`. -/
private lemma antiCount_ge_of_lagrangian_inter (Z L : Finset (PauliIdx 4)) (hL : IsLagrangian L) :
    2 * (Z.card - (Z ∩ L).card) * ((Z ∩ L).card - 8) ≤ antiCount Z := by
  let S := Z ∩ L
  let T := Z \ L
  have hpart : Z = S ∪ T := by ext x; simp only [S, T, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hdisj : Disjoint S T := by rw [Finset.disjoint_left]; intro x hxS hxT; exact (Finset.mem_sdiff.mp hxT).2 (Finset.mem_inter.mp hxS).2
  have hTcard : T.card = Z.card - S.card := by
    have : Z.card = S.card + T.card := by conv_lhs => rw [hpart]; exact Finset.card_union_of_disjoint hdisj
    omega
  -- Every `u ∈ T` (`u ∉ L`) anticommutes with at least `S.card - 8` elements of `S ⊆ L`!
  have hu_lb : ∀ u ∈ T, S.card - 8 ≤ (S.filter fun p => symp u p = 1).card := by
    intro u hu
    have huL : u ∉ L := (Finset.mem_sdiff.mp hu).2
    have hcard1 := (lagrangian_perp_eq_and_card_anticomm hL).2 u huL
    have hcard0 : (L.filter fun p => symp u p = 0).card = 8 := by
      have htot := Finset.card_filter_add_card_filter_not (s := L) (p := fun p => symp u p = 0)
      have heq : L.filter (fun p => ¬symp u p = 0) = L.filter (fun p => symp u p = 1) := by
        ext p; simp only [Finset.mem_filter]
        exact ⟨fun ⟨hp, hn⟩ => ⟨hp, (zmod2_cases _).resolve_left hn⟩,
               fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
      rw [heq, hcard1, hL.2.1] at htot; norm_num at htot; omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun p => symp u p = 0)
    have hS1 : S.filter (fun p => ¬symp u p = 0) = S.filter (fun p => symp u p = 1) := by
      ext p; simp only [Finset.mem_filter]
      exact ⟨fun ⟨hp, hn⟩ => ⟨hp, (zmod2_cases _).resolve_left hn⟩,
             fun ⟨hp, h1⟩ => ⟨hp, by rw [h1]; decide⟩⟩
    have hS0_le : (S.filter fun p => symp u p = 0).card ≤ 8 := by
      calc (S.filter fun p => symp u p = 0).card
          ≤ (L.filter fun p => symp u p = 0).card := Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_right)
        _ = 8 := hcard0
    rw [hS1] at hsplit; omega
  have hsum_T : T.card * (S.card - 8) ≤ ∑ u ∈ T, (S.filter fun p => symp u p = 1).card := by
    calc T.card * (S.card - 8) = ∑ _u ∈ T, (S.card - 8) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hu_lb
  have hsym : ∑ p ∈ S, (T.filter fun u => symp p u = 1).card = ∑ u ∈ T, (S.filter fun p => symp u p = 1).card := by
    have h1 : ∀ p ∈ S, (T.filter fun u => symp p u = 1).card = ∑ u ∈ T, if symp p u = 1 then 1 else 0 := fun p _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ∀ u ∈ T, (S.filter fun p => symp u p = 1).card = ∑ p ∈ S, if symp p u = 1 then 1 else 0 := fun u _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1; ext p; simp [symp_comm]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]
  have hle_S : ∑ p ∈ S, (T.filter fun u => symp p u = 1).card ≤ ∑ p ∈ S, (Z.filter fun q => symp p q = 1).card :=
    Finset.sum_le_sum fun p _ => Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
  have hle_T : ∑ u ∈ T, (S.filter fun p => symp u p = 1).card ≤ ∑ u ∈ T, (Z.filter fun q => symp u q = 1).card :=
    Finset.sum_le_sum fun u _ => Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)
  have hA_split : antiCount Z = (∑ p ∈ S, (Z.filter fun q => symp p q = 1).card) +
      (∑ u ∈ T, (Z.filter fun q => symp u q = 1).card) := by
    simp only [antiCount]; conv_lhs => arg 1; rw [hpart]
    exact Finset.sum_union hdisj
  rw [hTcard] at hsum_T
  have h2 : 2 * (Z.card - S.card) * (S.card - 8) = 2 * ((Z.card - S.card) * (S.card - 8)) := by ring
  change 2 * (Z.card - S.card) * (S.card - 8) ≤ antiCount Z
  omega

/-- **All 5 Symplectic Turán Theorems on `𝔽₂⁸`** (unified from `symp_turan_le_nine` + `antiCount_ge_of_lagrangian_inter`):
    1. `|Z| = 14 ∧ A(Z) < 16 ⇒ ∃ L Lag, |Z ∩ L| ≥ 13`
    2. `|Z| = 15 ∧ A(Z) < 20 ⇒ ∃ L Lag, |Z ∩ L| ≥ 14`
    3. `|Z| = 16 ∧ A(Z) < 24 ⇒ ∃ L Lag, |Z ∩ L| ≥ 15`
    4. `|Z| = 17 ∧ A(Z) < 28 ⇒ ∃ L Lag, |Z ∩ L| = 16`
    5. `|Z| = 18 ∧ A(Z) < 32 ⇒ False` -/
lemma symp_turan_unified (Z : Finset (PauliIdx 4)) :
    (Z.card = 14 → antiCount Z < 16 → ∃ L, IsLagrangian L ∧ 13 ≤ (Z ∩ L).card) ∧
    (Z.card = 15 → antiCount Z < 20 → ∃ L, IsLagrangian L ∧ 14 ≤ (Z ∩ L).card) ∧
    (Z.card = 16 → antiCount Z < 24 → ∃ L, IsLagrangian L ∧ 15 ≤ (Z ∩ L).card) ∧
    (Z.card = 17 → antiCount Z < 28 → ∃ L, IsLagrangian L ∧ 16 ≤ (Z ∩ L).card) ∧
    (Z.card = 18 → antiCount Z < 32 → False) := by
  -- Helper: either `∀ L, |Z ∩ L| ≤ 9`, or pick a Lagrangian `L` maximizing `|Z ∩ L| ≥ 10`!
  have hmax : (∀ L, IsLagrangian L → (Z ∩ L).card ≤ 9) ∨
      ∃ L, IsLagrangian L ∧ 10 ≤ (Z ∩ L).card ∧ ∀ L', IsLagrangian L' → (Z ∩ L').card ≤ (Z ∩ L).card := by
    by_cases h : ∀ L, IsLagrangian L → (Z ∩ L).card ≤ 9
    · exact Or.inl h
    · right
      push Not at h
      let Lags := Finset.univ.filter fun L : Finset (PauliIdx 4) => IsLagrangian L
      have hne : Lags.Nonempty := by
        obtain ⟨L, hL, _⟩ := h; exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩⟩
      obtain ⟨L, hLm, hLmax⟩ := Finset.exists_max_image Lags (fun L => (Z ∩ L).card) hne
      obtain ⟨L0, hL0, h10⟩ := h
      have hge10 : 10 ≤ (Z ∩ L).card := le_trans h10 (hLmax L0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL0⟩))
      exact ⟨L, (Finset.mem_filter.mp hLm).2, hge10, fun L' hL' => hLmax L' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL'⟩)⟩
  rcases hmax with h9 | ⟨L, hL, hs10, hLmax⟩
  · obtain ⟨t14, t15, t16, t17, t18⟩ := symp_turan_le_nine Z h9
    exact ⟨fun hm hA => absurd (t14 hm) (not_le_of_gt hA),
           fun hm hA => absurd (t15 hm) (not_le_of_gt hA),
           fun hm hA => absurd (t16 hm) (not_le_of_gt hA),
           fun hm hA => absurd (t17 hm) (not_le_of_gt hA),
           fun hm hA => absurd (t18 hm) (not_le_of_gt hA)⟩
  · have hlb := antiCount_ge_of_lagrangian_inter Z L hL
    have hs16 : (Z ∩ L).card ≤ 16 := by
      calc (Z ∩ L).card ≤ L.card := Finset.card_le_card Finset.inter_subset_right
        _ = 16 := by rw [hL.2.1]; norm_num
    refine ⟨fun hm hA => ⟨L, hL, ?_⟩, fun hm hA => ⟨L, hL, ?_⟩, fun hm hA => ⟨L, hL, ?_⟩,
            fun hm hA => ⟨L, hL, ?_⟩, fun hm hA => ?_⟩
    · set s := (Z ∩ L).card; rw [hm] at hlb
      by_contra hlt; push Not at hlt
      have : s = 10 ∨ s = 11 ∨ s = 12 := by omega
      rcases this with h | h | h <;> (rw [h] at hlb; omega)
    · set s := (Z ∩ L).card; rw [hm] at hlb
      by_contra hlt; push Not at hlt
      have : s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 := by omega
      rcases this with h | h | h | h <;> (rw [h] at hlb; omega)
    · set s := (Z ∩ L).card; rw [hm] at hlb
      by_contra hlt; push Not at hlt
      have : s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 := by omega
      rcases this with h | h | h | h | h <;> (rw [h] at hlb; omega)
    · set s := (Z ∩ L).card; rw [hm] at hlb
      by_contra hlt; push Not at hlt
      have : s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 := by omega
      rcases this with h | h | h | h | h | h <;> (rw [h] at hlb; omega)
    · set s := (Z ∩ L).card; rw [hm] at hlb
      have : s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 := by omega
      rcases this with h | h | h | h | h | h | h <;> (rw [h] at hlb; omega)

end FourQubitMUB
end MultiQubitMUB
