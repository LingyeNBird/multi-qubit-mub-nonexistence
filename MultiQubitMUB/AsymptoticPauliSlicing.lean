import MultiQubitMUB.AsymptoticChar2Theory

/-!
# Stage 17 — Pauli-Slicing Renormalization (`n → n - 1`), Two-State Support-Disjointness
  Uncertainty Functional `𝒥ₘ`, Dual Symplectic-Quadratic Identity, and Unconditional
  `17 / 8 = 2.125 > 2` Constant-Gap Theorems

Formalizes four unconditional general-`n` / general-`m` pure-theory theorem groups from Stage 17
(zero `sorry`, zero `native_decide`, zero `set_option`, standard three Lean axioms
`[propext, Classical.choice, Quot.sound]` only, zero edits to upstream modules):

1. **Two-State Pauli Support-Disjointness Functional `𝒥ₘ` & Complex-Symmetric Self-Duality (ALL `m`)**:
   - `pauliCrossOverlap4_eq_pauliOverlap4`: `∑_r |⟨φ₁ | P_r | φ₂⟩|⁴ = ∑_r c_r(φ₁)² c_r(φ₂)² = Gₘ(φ₁, φ₂)`.
   - `pauliOverlap4_eq_one_add_supportOverlap`: `Gₘ(φ₁, φ₂) = 1 + C(φ₁, φ₂)` for unit states.
   - `twoStateJ_ge_two_sub_inv_add_overlap`: `2 - 1 / (2ᵐ + 1) + C(φ₁, φ₂) ≤ 𝒥ₘ(φ₁, φ₂)`.
   - `pauliOverlap4_eq_sum_symPauliNormSq` & `twoStateJ_eq_dual_symPauli`: exact complex-symmetric
     self-duality `Gₘ(φ₁, φ₂) = ∑_{Q₀(p)=0} w_p(φ₁) w_p(φ₂)` and
     `𝒥ₘ(φ₁, φ₂) = (1/8) ∑_{Q₀(p)=0} (w_p(φ₁) + w_p(φ₂))² + ∑_{Q₀(p)=0} w_p(φ₁) w_p(φ₂)`.

2. **Exact Pauli-Slicing Renormalization Identity (ALL `m`, Theorem 17.1)**:
   - `pauliMoment4_slicing_identity`: for EVERY `(m + 1)`-qubit state decomposed on qubit `0` as
     `ψ (Fin.cons 0 x) = √w₀ • φ₀ x`, `ψ (Fin.cons 1 x) = √w₁ • φ₁ x`,
       `F_{m+1}(ψ) = 2 w₀⁴ Fₘ(φ₀) + 2 w₁⁴ Fₘ(φ₁) + 20 w₀² w₁² Gₘ(φ₀, φ₁) + 8 w₀² w₁² Q_phase(φ₀, φ₁)`.

3. **Explicit Elementary Clifford Conjugation & Unconditional Universal Reduction (ALL `m`, Theorem 17.2)**:
   - `exists_clifford_to_Z0`: explicit composition of single-qubit `S_k`, `H_k`, qubit swap, and
     involutive CNOT basis-change conjugating ANY `q ≠ 0` to `Z₀ = (0, e₀)` while preserving
     `IsUnitState` and `pauliMoment4`.
   - `pauliMoment4_ge_twoStateJ_universal`: for EVERY `m : ℕ` and EVERY unit state `ψ : QState (m + 1)`,
     there exist unit states `φ₀, φ₁ : QState m` such that
       `(1 - 1 / √(2^{m+1} + 1))⁴ · 𝒥ₘ(φ₀, φ₁) ≤ F_{m+1}(ψ)`.

4. **Hyperplane & Quadric Mass Concentration + Unconditional `17 / 8 = 2.125 > 2` Constant-Gap Theorems (ALL `m`)**:
   - `sum_pauliSq_hyperplane` & `sum_pauliSq_quadric`: exact mass splits on `q^⊥` and `Q_p = 0`.
   - `twoStateJ_ge_of_hyperplane` & `twoStateJ_ge_of_quadric`: exact general-pair lower bounds.
   - `twoStateJ_ge_seventeen_eighths_of_real` & `twoStateJ_gt_two_of_real`: whenever EITHER `φ₁` or `φ₂`
     is Clifford-equivalent to a real state (`∃ p, w_p = 1`),
       `17 / 8 - (16 D - 18) / (8 (D - 1) (D + 2)) ≤ 𝒥ₘ(φ₁, φ₂)` (`∀ m ≥ 2`), strictly `> 2` for ALL `m ≥ 4`.
   - `twoStateJ_ge_seventeen_eighths_of_stabilizer` & `twoStateJ_gt_two_of_stabilizer`: whenever EITHER
     `φ₁` or `φ₂` has ANY stabilizer symmetry (`∃ q ≠ 0, c_q² = 1`),
       `17 / 8 - (12 D - 17) / (8 (D² - 2)) ≤ 𝒥ₘ(φ₁, φ₂)` (`∀ m ≥ 2`), strictly `> 2` for ALL `m ≥ 4`.
-/

namespace MultiQubitMUB

open scoped Classical
open FourQubitCD
open GeneralContextualityLift
open AsymptoticContextuality
open AsymptoticBarriers
open AsymptoticChar2Theory

namespace AsymptoticPauliSlicing

/-! ### Part 1: Two-State Disjointness Functional `𝒥ₘ` & Complex-Symmetric Self-Duality -/

/-- Two-state Pauli-squared overlap `Gₘ(φ₁, φ₂) = ∑_r c_r(φ₁)² c_r(φ₂)²`. -/
noncomputable def pauliOverlap4 {m : ℕ} (φ₁ φ₂ : QState m) : ℝ :=
  ∑ r : PauliIdx m,
    (innerProd φ₁ (pauliApply r φ₁)).re ^ 2 * (innerProd φ₂ (pauliApply r φ₂)).re ^ 2

/-- Two-state cross-Pauli 4th moment `∑_r |⟨φ₁ | P_r | φ₂⟩|⁴`. -/
noncomputable def pauliCrossOverlap4 {m : ℕ} (φ₁ φ₂ : QState m) : ℝ :=
  ∑ r : PauliIdx m, Complex.normSq (innerProd φ₁ (pauliApply r φ₂)) ^ 2

/-- Relative-phase quartic term `Q_phase(φ₁, φ₂) = ∑_r ((Re z_r)² - (Im z_r)²)²`,
    where `z_r = ⟨φ₁ | P_r | φ₂⟩`. -/
noncomputable def pauliCrossPhaseTerm {m : ℕ} (φ₁ φ₂ : QState m) : ℝ :=
  ∑ r : PauliIdx m,
    ((innerProd φ₁ (pauliApply r φ₂)).re ^ 2 - (innerProd φ₁ (pauliApply r φ₂)).im ^ 2) ^ 2

/-- Non-identity Pauli support overlap `C(φ₁, φ₂) = ∑_{r ≠ 0} c_r(φ₁)² c_r(φ₂)²`. -/
noncomputable def pauliSupportOverlap {m : ℕ} (φ₁ φ₂ : QState m) : ℝ :=
  ∑ r ∈ nzPts m,
    (innerProd φ₁ (pauliApply r φ₁)).re ^ 2 * (innerProd φ₂ (pauliApply r φ₂)).re ^ 2

/-- Two-state Pauli-support-disjointness uncertainty functional
    `𝒥ₘ(φ₁, φ₂) = (Fₘ(φ₁) + Fₘ(φ₂)) / 8 + (5 / 4) Gₘ(φ₁, φ₂)`. -/
noncomputable def twoStateJ {m : ℕ} (φ₁ φ₂ : QState m) : ℝ :=
  (pauliMoment4 m φ₁ + pauliMoment4 m φ₂) / 8 + (5 / 4 : ℝ) * pauliOverlap4 φ₁ φ₂

lemma pauliMoment4_eq_sum_re_pow4 {m : ℕ} (φ : QState m) :
    pauliMoment4 m φ = ∑ r : PauliIdx m, (innerProd φ (pauliApply r φ)).re ^ 4 := by
  simp only [pauliMoment4]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hre := innerProd_pauliApply_self_real r φ
  have hns : Complex.normSq (innerProd φ (pauliApply r φ)) =
      (innerProd φ (pauliApply r φ)).re ^ 2 := by
    conv_lhs => rw [← hre]
    rw [Complex.normSq_ofReal, sq]
  rw [hns]; ring

lemma pauliExpect_sq_sum_eq_dim {m : ℕ} {φ : QState m} (hunit : IsUnitState φ) :
    ∑ r : PauliIdx m, (innerProd φ (pauliApply r φ)).re ^ 2 = (2 : ℝ) ^ m := by
  have h := sum_normSq_pauliExpect hunit
  have heq : ∑ r : PauliIdx m, Complex.normSq (innerProd φ (pauliApply r φ)) =
      ∑ r : PauliIdx m, (innerProd φ (pauliApply r φ)).re ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    have hre := innerProd_pauliApply_self_real r φ
    conv_lhs => rw [← hre]
    rw [Complex.normSq_ofReal, sq]
  linarith

lemma sum_nz_pauliExpect_sq {m : ℕ} {φ : QState m} (hunit : IsUnitState φ) :
    ∑ r ∈ nzPts m, (innerProd φ (pauliApply r φ)).re ^ 2 = (2 : ℝ) ^ m - 1 := by
  have h := pauliExpect_sq_sum_eq_dim hunit
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)), pauliExpect_zero_re hunit] at h
  change 1 ^ 2 + ∑ r ∈ nzPts m, (innerProd φ (pauliApply r φ)).re ^ 2 = (2 : ℝ) ^ m at h
  linarith

/-- Symplectic WHT of cross-Pauli squared overlaps:
    `|⟨φ₁ | P_r | φ₂⟩|² = (1 / 2ᵐ) ∑_s (-1)^{ω(r, s)} c_s(φ₁) c_s(φ₂)`. -/
lemma crossOverlap_normSq_eq_sympWHT {m : ℕ} (φ₁ φ₂ : QState m) (r : PauliIdx m) :
    Complex.normSq (innerProd φ₁ (pauliApply r φ₂)) =
      (1 / (2 : ℝ) ^ m) *
        ∑ s : PauliIdx m, (sympSign r s : ℝ) *
          ((innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re) := by
  let d : ℝ := (2 : ℝ) ^ m
  have hd_ne : d ≠ 0 := by positivity
  let ψ₂ : QState m := pauliApply r φ₂
  have htr_ov : matTr (matMul (stateProj φ₁) (stateProj ψ₂)) =
      (Complex.normSq (innerProd φ₁ ψ₂) : ℂ) := by
    rw [matTr_stateProj_mul]
    have hap : matApply (stateProj ψ₂) φ₁ = innerProd ψ₂ φ₁ • ψ₂ := by
      ext x; simp only [matApply, stateProj, Pi.smul_apply, smul_eq_mul, innerProd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    rw [hap, innerProd_smul_right, innerProd_conj_symm φ₁ ψ₂, mul_comm, Complex.star_def,
        Complex.mul_conj]
  have hscale : matTr (matMul (matSmul ((2 : ℂ) ^ m) (stateProj φ₁))
        (matSmul ((2 : ℂ) ^ m) (stateProj ψ₂))) =
      ((2 : ℂ) ^ m) ^ 2 * matTr (matMul (stateProj φ₁) (stateProj ψ₂)) := by
    simp only [matTr, matMul, matSmul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
  rw [stateProj_eq_pauliExpand φ₁, stateProj_eq_pauliExpand ψ₂, matTr_pauliExpand_mul, htr_ov] at hscale
  have hre := congr_arg Complex.re hscale
  have hconj_c : ∀ s : PauliIdx m,
      (innerProd ψ₂ (pauliApply s ψ₂)).re =
        (sympSign r s : ℝ) * (innerProd φ₂ (pauliApply s φ₂)).re := fun s => by
    have hc : innerProd ψ₂ (pauliApply s ψ₂) =
        (sympSign r s : ℂ) * innerProd φ₂ (pauliApply s φ₂) := by
      simp only [ψ₂]
      rw [pauliApply_comm s r φ₂, innerProd_smul_right, innerProd_pauliApply_both, sympSign_comm]
    have hcr := congr_arg Complex.re hc
    have hreal := innerProd_pauliApply_self_real s φ₂
    rw [hcr]
    conv_lhs => rw [← hreal]
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hL : ((2 : ℂ) ^ m * ∑ s : PauliIdx m,
      (((innerProd φ₁ (pauliApply s φ₁)).re * (innerProd ψ₂ (pauliApply s ψ₂)).re : ℝ) : ℂ)).re =
      d * ∑ s : PauliIdx m, (sympSign r s : ℝ) *
        ((innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re) := by
    have h2c : (2 : ℂ) ^ m = (d : ℂ) := by simp [d]
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun s _ => by rw [hconj_c s]; ring
  have hR : (((2 : ℂ) ^ m) ^ 2 * (Complex.normSq (innerProd φ₁ ψ₂) : ℂ)).re =
      d ^ 2 * Complex.normSq (innerProd φ₁ ψ₂) := by
    have h2c : ((2 : ℂ) ^ m) ^ 2 = ((d ^ 2 : ℝ) : ℂ) := by simp [d]
    rw [h2c, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hL, hR] at hre
  have hdiv : d * Complex.normSq (innerProd φ₁ ψ₂) =
      ∑ s : PauliIdx m, (sympSign r s : ℝ) *
        ((innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re) :=
    mul_left_cancel₀ hd_ne (by linear_combination -hre)
  calc Complex.normSq (innerProd φ₁ ψ₂) = (1 / d) * (d * Complex.normSq (innerProd φ₁ ψ₂)) := by
        field_simp [hd_ne]
    _ = _ := by rw [hdiv]

/-- General Parseval inner-product identity for the symplectic WHT on `PauliIdx m`:
    `∑_r (∑_s (-1)^{ω(r,s)} f s) (∑_t (-1)^{ω(r,t)} g t) = (2ᵐ)² ∑_s f s * g s`. -/
lemma sympWHT_parseval_inner {m : ℕ} (f g : PauliIdx m → ℝ) :
    ∑ r : PauliIdx m,
      (∑ s : PauliIdx m, (sympSign r s : ℝ) * f s) *
      (∑ t : PauliIdx m, (sympSign r t : ℝ) * g t) =
      ((2 : ℝ) ^ m) ^ 2 * ∑ s : PauliIdx m, f s * g s := by
  let d : ℝ := (2 : ℝ) ^ m
  calc ∑ r : PauliIdx m,
        (∑ s : PauliIdx m, (sympSign r s : ℝ) * f s) *
        (∑ t : PauliIdx m, (sympSign r t : ℝ) * g t)
      = ∑ r : PauliIdx m, ∑ s : PauliIdx m, ∑ t : PauliIdx m,
          (sympSign (s + t) r : ℝ) * (f s * g t) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        have hs : (sympSign r s : ℝ) * (sympSign r t : ℝ) = (sympSign (s + t) r : ℝ) := by
          rw [sympSign_comm (s + t) r, sympSign_add_right, Int.cast_mul]
        calc (sympSign r s : ℝ) * f s * ((sympSign r t : ℝ) * g t)
            = ((sympSign r s : ℝ) * (sympSign r t : ℝ)) * (f s * g t) := by ring
          _ = _ := by rw [hs]
    _ = ∑ s : PauliIdx m, ∑ t : PauliIdx m,
          (∑ r : PauliIdx m, (sympSign (s + t) r : ℝ)) * (f s * g t) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => (Finset.sum_mul ..).symm
    _ = ∑ s : PauliIdx m, ∑ t : PauliIdx m, (if s = t then d ^ 2 else 0) * (f s * g t) := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        congr 1
        have hz := sum_sympSign_univ (s + t)
        have hcast : ∑ r : PauliIdx m, (sympSign (s + t) r : ℝ) =
            ((∑ r : PauliIdx m, sympSign (s + t) r : ℤ) : ℝ) := by rw [Int.cast_sum]
        rw [hcast, hz]
        have hiff : s + t = 0 ↔ s = t := by
          constructor
          · intro h; have := congr_arg (· + t) h; simpa [pauliIdx_add_cancel_right] using this
          · intro h; rw [h, pauliIdx_add_self]
        simp only [hiff]
        split_ifs
        · dsimp only [d]; push_cast
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
        · simp
    _ = d ^ 2 * ∑ s : PauliIdx m, f s * g s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_eq_single s]
        · simp
        · intro t _ ht; simp [ht.symm]
        · intro h; exact absurd (Finset.mem_univ s) h

/-- **Exact Cross-Pauli Parseval Identity (`∑_r |⟨φ₁ | P_r | φ₂⟩|⁴ = Gₘ(φ₁, φ₂)`, ALL `m`)**. -/
theorem pauliCrossOverlap4_eq_pauliOverlap4 {m : ℕ} (φ₁ φ₂ : QState m) :
    pauliCrossOverlap4 φ₁ φ₂ = pauliOverlap4 φ₁ φ₂ := by
  let d : ℝ := (2 : ℝ) ^ m
  have hd_ne : d ≠ 0 := by positivity
  let f : PauliIdx m → ℝ := fun s =>
    (innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re
  have h1 : pauliCrossOverlap4 φ₁ φ₂ =
      (1 / d ^ 2) * ∑ r : PauliIdx m,
        (∑ s : PauliIdx m, (sympSign r s : ℝ) * f s) *
        (∑ t : PauliIdx m, (sympSign r t : ℝ) * f t) := by
    rw [pauliCrossOverlap4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [crossOverlap_normSq_eq_sympWHT]
    dsimp only [d, f]; ring
  rw [h1, sympWHT_parseval_inner f f]
  have hf2 : ∑ s : PauliIdx m, f s * f s = pauliOverlap4 φ₁ φ₂ := by
    simp only [pauliOverlap4, f]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [hf2]
  dsimp only [d]
  field_simp [hd_ne]

/-- **Decomposition `Gₘ(φ₁, φ₂) = 1 + C(φ₁, φ₂)` (ALL `m`, Unit States)**. -/
theorem pauliOverlap4_eq_one_add_supportOverlap {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) :
    pauliOverlap4 φ₁ φ₂ = 1 + pauliSupportOverlap φ₁ φ₂ := by
  rw [pauliOverlap4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
      pauliExpect_zero_re h1, pauliExpect_zero_re h2]
  simp [pauliSupportOverlap, nzPts]

/-- **Universal Cauchy–Schwarz Floor for `𝒥ₘ` (`2 - 1/(2ᵐ + 1) + C ≤ 𝒥ₘ`, ALL `m`)**:
    For EVERY `m : ℕ` and EVERY pair of unit states `φ₁ φ₂ : QState m`,
      `2 - 1 / (2ᵐ + 1) + pauliSupportOverlap φ₁ φ₂ ≤ twoStateJ φ₁ φ₂`. -/
theorem twoStateJ_ge_two_sub_inv_add_overlap {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) :
    2 - 1 / ((2 : ℝ) ^ m + 1) + pauliSupportOverlap φ₁ φ₂ ≤ twoStateJ φ₁ φ₂ := by
  let D : ℝ := (2 : ℝ) ^ m
  have hD_pos : 0 < D := by positivity
  have hD1_pos : 0 < D + 1 := by linarith
  by_cases hm0 : m = 0
  · subst hm0
    have hnz : nzPts 0 = ∅ := by
      ext r; simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty,
        iff_false, not_not]
      ext i <;> exact Fin.elim0 i
    have hF1 : pauliMoment4 0 φ₁ = 1 := by
      rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 0))]
      change (innerProd φ₁ (pauliApply 0 φ₁)).re ^ 4 + ∑ r ∈ nzPts 0, _ = 1
      rw [hnz, Finset.sum_empty, add_zero, pauliExpect_zero_re h1]; ring
    have hF2 : pauliMoment4 0 φ₂ = 1 := by
      rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx 0))]
      change (innerProd φ₂ (pauliApply 0 φ₂)).re ^ 4 + ∑ r ∈ nzPts 0, _ = 1
      rw [hnz, Finset.sum_empty, add_zero, pauliExpect_zero_re h2]; ring
    rw [twoStateJ, pauliOverlap4_eq_one_add_supportOverlap h1 h2, pauliSupportOverlap, hnz,
        Finset.sum_empty, hF1, hF2]
    norm_num
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hD_ge2 : (2 : ℝ) ≤ D := by
      have : (2 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm1
      dsimp only [D]; exact_mod_cast this
    have hD2m1_pos : 0 < D ^ 2 - 1 := by nlinarith
    have hcard : ((nzPts m).card : ℝ) = D ^ 2 - 1 := by
      simpa only [nzPts, D] using card_PauliIdx_erase_zero m
    let x : PauliIdx m → ℝ := fun r => (innerProd φ₁ (pauliApply r φ₁)).re ^ 2
    let y : PauliIdx m → ℝ := fun r => (innerProd φ₂ (pauliApply r φ₂)).re ^ 2
    have hsum_xy : ∑ r ∈ nzPts m, (x r + y r) = 2 * (D - 1) := by
      rw [Finset.sum_add_distrib, sum_nz_pauliExpect_sq h1, sum_nz_pauliExpect_sq h2]
      dsimp only [D]; ring
    have hcs : (2 * (D - 1)) ^ 2 / (D ^ 2 - 1) ≤ ∑ r ∈ nzPts m, (x r + y r) ^ 2 := by
      have h0 := Finset.sum_mul_sq_le_sq_mul_sq (nzPts m) (fun _ => (1 : ℝ)) (fun r => x r + y r)
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, hsum_xy] at h0
      exact (div_le_iff₀ hD2m1_pos).mpr (by linarith)
    have hF1 : pauliMoment4 m φ₁ = 1 + ∑ r ∈ nzPts m, x r ^ 2 := by
      rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
          pauliExpect_zero_re h1]
      change 1 ^ 4 + ∑ r ∈ nzPts m, (innerProd φ₁ (pauliApply r φ₁)).re ^ 4 =
        1 + ∑ r ∈ nzPts m, x r ^ 2
      have : ∀ r ∈ nzPts m, (innerProd φ₁ (pauliApply r φ₁)).re ^ 4 = x r ^ 2 := fun r _ => by
        dsimp only [x]; ring
      rw [Finset.sum_congr rfl this]; ring
    have hF2 : pauliMoment4 m φ₂ = 1 + ∑ r ∈ nzPts m, y r ^ 2 := by
      rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
          pauliExpect_zero_re h2]
      change 1 ^ 4 + ∑ r ∈ nzPts m, (innerProd φ₂ (pauliApply r φ₂)).re ^ 4 =
        1 + ∑ r ∈ nzPts m, y r ^ 2
      have : ∀ r ∈ nzPts m, (innerProd φ₂ (pauliApply r φ₂)).re ^ 4 = y r ^ 2 := fun r _ => by
        dsimp only [y]; ring
      rw [Finset.sum_congr rfl this]; ring
    have hexp : ∑ r ∈ nzPts m, (x r + y r) ^ 2 =
        ∑ r ∈ nzPts m, x r ^ 2 + ∑ r ∈ nzPts m, y r ^ 2 + 2 * pauliSupportOverlap φ₁ φ₂ := by
      have ht : ∀ r ∈ nzPts m, (x r + y r) ^ 2 = x r ^ 2 + y r ^ 2 + 2 * (x r * y r) := fun _ _ => by ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    have hJ : twoStateJ φ₁ φ₂ =
        3 / 2 + (∑ r ∈ nzPts m, (x r + y r) ^ 2) / 8 + pauliSupportOverlap φ₁ φ₂ := by
      rw [twoStateJ, pauliOverlap4_eq_one_add_supportOverlap h1 h2, hF1, hF2, hexp]; ring
    have hratio : 3 / 2 + ((2 * (D - 1)) ^ 2 / (D ^ 2 - 1)) / 8 = 2 - 1 / (D + 1) := by
      have hDm1_ne : D - 1 ≠ 0 := by linarith
      have hD1_ne : D + 1 ≠ 0 := by linarith
      have hD2_ne : D ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp [hD2_ne, hD1_ne]; ring
    rw [hJ]
    linarith

/-- **Theorem 17.3(a) — Complex-Symmetric Self-Duality of `Gₘ(φ₁, φ₂)` (ALL `m`)**:
    `Gₘ(φ₁, φ₂) = ∑_{p ∈ symPts m} w_p(φ₁) · w_p(φ₂)`. -/
theorem pauliOverlap4_eq_sum_symPauliNormSq {m : ℕ} (φ₁ φ₂ : QState m) :
    pauliOverlap4 φ₁ φ₂ = ∑ p ∈ symPts m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p := by
  let d : ℝ := (2 : ℝ) ^ m
  have hd_ne : d ≠ 0 := by positivity
  have hall : ∑ p ∈ symPts m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p =
      ∑ p : PauliIdx m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p := by
    refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
    have hq : quadForm0 p ≠ 0 := by simpa [symPts] using hp
    simp [symPauliNormSq, symPauliExpect_eq_zero_of_antisym φ₁ hq]
  rw [hall]
  let f : PauliIdx m → ℝ := fun q =>
    (if quadForm0 q = 0 then (1 : ℝ) else -1) * (innerProd φ₁ (pauliApply q φ₁)).re ^ 2
  let g : PauliIdx m → ℝ := fun q =>
    (if quadForm0 q = 0 then (1 : ℝ) else -1) * (innerProd φ₂ (pauliApply q φ₂)).re ^ 2
  have hquad_sign : ∀ p q : PauliIdx m,
      (if quadForm p q = 0 then (1 : ℝ) else -1) =
        (sympSign p q : ℝ) * (if quadForm0 q = 0 then (1 : ℝ) else -1) := fun p q => by
    simp only [quadForm, sympSign]
    rcases zmod2_cases (quadForm0 q) with h1 | h1 <;> rcases zmod2_cases (symp p q) with h2 | h2
    all_goals simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]
  have hwp : ∀ (φ : QState m) (p : PauliIdx m),
      symPauliNormSq φ p = (1 / d) * ∑ q : PauliIdx m, (sympSign p q : ℝ) *
        ((if quadForm0 q = 0 then (1 : ℝ) else -1) * (innerProd φ (pauliApply q φ)).re ^ 2) := fun φ p => by
    rw [symPauliNormSq_eq_sympWHT]
    dsimp only [d]; congr 1
    refine Finset.sum_congr rfl fun q _ => by rw [hquad_sign p q]; ring
  have hprod : ∑ p : PauliIdx m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p =
      (1 / d ^ 2) * ∑ p : PauliIdx m,
        (∑ q : PauliIdx m, (sympSign p q : ℝ) * f q) *
        (∑ r : PauliIdx m, (sympSign p r : ℝ) * g r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hwp φ₁ p, hwp φ₂ p]
    dsimp only [f, g]; ring
  rw [hprod, sympWHT_parseval_inner f g]
  have hfg : ∑ q : PauliIdx m, f q * g q = pauliOverlap4 φ₁ φ₂ := by
    simp only [pauliOverlap4, f, g]
    refine Finset.sum_congr rfl fun q _ => by split_ifs <;> ring
  rw [hfg]
  dsimp only [d]
  field_simp [hd_ne]

/-- **Theorem 17.3(b) — Exact Dual Representation of `𝒥ₘ` on `symPts m` (`Q₀(p) = 0`, ALL `m`)**:
    `𝒥ₘ(φ₁, φ₂) = (1 / 8) ∑_{Q₀(p)=0} (w_p(φ₁) + w_p(φ₂))² + ∑_{Q₀(p)=0} w_p(φ₁) w_p(φ₂)`. -/
theorem twoStateJ_eq_dual_symPauli {m : ℕ} (φ₁ φ₂ : QState m) :
    twoStateJ φ₁ φ₂ =
      (1 / 8 : ℝ) * ∑ p ∈ symPts m, (symPauliNormSq φ₁ p + symPauliNormSq φ₂ p) ^ 2 +
      ∑ p ∈ symPts m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p := by
  have hF : ∀ φ : QState m, pauliMoment4 m φ = ∑ p ∈ symPts m, symPauliNormSq φ p ^ 2 := fun φ => by
    have h := pauliOverlap4_eq_sum_symPauliNormSq φ φ
    have hL : pauliOverlap4 φ φ = pauliMoment4 m φ := by
      rw [pauliOverlap4, pauliMoment4_eq_sum_re_pow4]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [hL] at h
    rw [h]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [twoStateJ, hF φ₁, hF φ₂, pauliOverlap4_eq_sum_symPauliNormSq φ₁ φ₂]
  have hexp : ∑ p ∈ symPts m, (symPauliNormSq φ₁ p + symPauliNormSq φ₂ p) ^ 2 =
      ∑ p ∈ symPts m, symPauliNormSq φ₁ p ^ 2 +
      ∑ p ∈ symPts m, symPauliNormSq φ₂ p ^ 2 +
      2 * ∑ p ∈ symPts m, symPauliNormSq φ₁ p * symPauliNormSq φ₂ p := by
    have ht : ∀ p ∈ symPts m,
        (symPauliNormSq φ₁ p + symPauliNormSq φ₂ p) ^ 2 =
          symPauliNormSq φ₁ p ^ 2 + symPauliNormSq φ₂ p ^ 2 +
            2 * (symPauliNormSq φ₁ p * symPauliNormSq φ₂ p) := fun _ _ => by ring
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp]; ring

/-! ### Part 2: Exact Pauli-Slicing Renormalization Identity (`n = m + 1 → m`, Theorem 17.1) -/

/-- Equivalence splitting `F2 (m + 1)` into head bit `ZMod 2` and tail `F2 m`. -/
def f2SplitEquiv (m : ℕ) : (ZMod 2 × F2 m) ≃ F2 (m + 1) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by ext <;> simp
  right_inv x := by simp [Fin.cons_self_tail]

/-- Equivalence splitting `PauliIdx (m + 1)` into qubit-0 Pauli `(a₀, b₀)` and `PauliIdx m`. -/
def pauliSplitEquiv (m : ℕ) : ((ZMod 2 × ZMod 2) × PauliIdx m) ≃ PauliIdx (m + 1) where
  toFun t := (Fin.cons t.1.1 t.2.1, Fin.cons t.1.2 t.2.2)
  invFun p := ((p.1 0, p.2 0), (Fin.tail p.1, Fin.tail p.2))
  left_inv t := by rcases t with ⟨⟨a0, b0⟩, ⟨a, b⟩⟩; ext <;> simp
  right_inv p := by rcases p with ⟨a, b⟩; ext <;> simp [Fin.cons_self_tail]

lemma dot_cons {m : ℕ} (a0 b0 : ZMod 2) (a b : F2 m) :
    dot (Fin.cons a0 a) (Fin.cons b0 b) = a0 * b0 + dot a b := by
  simp [dot, Fin.sum_univ_succ]

lemma chi_cons {m : ℕ} (b0 x0 : ZMod 2) (b x : F2 m) :
    chi (Fin.cons b0 b) (Fin.cons x0 x) = (if b0 * x0 = 0 then 1 else -1) * chi b x := by
  simp only [chi, dot_cons]
  rcases zmod2_cases (b0 * x0) with h1 | h1 <;> rcases zmod2_cases (dot b x) with h2 | h2
  all_goals simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]

lemma cons_add_cons {m : ℕ} (a0 b0 : ZMod 2) (a b : F2 m) :
    (Fin.cons a0 a : F2 (m + 1)) + Fin.cons b0 b = Fin.cons (a0 + b0) (a + b) := by
  ext i; refine Fin.cases ?_ ?_ i <;> simp

/-- Qubit-0 `|0⟩` unnormalized slice of `ψ : QState (m + 1)`. -/
def slice0 {m : ℕ} (ψ : QState (m + 1)) : QState m := fun x => ψ (Fin.cons 0 x)

/-- Qubit-0 `|1⟩` unnormalized slice of `ψ : QState (m + 1)`. -/
def slice1 {m : ℕ} (ψ : QState (m + 1)) : QState m := fun x => ψ (Fin.cons 1 x)

lemma innerProd_split {m : ℕ} (ψ φ : QState (m + 1)) :
    innerProd ψ φ = innerProd (slice0 ψ) (slice0 φ) + innerProd (slice1 ψ) (slice1 φ) := by
  simp only [innerProd, slice0, slice1]
  rw [← Fintype.sum_equiv (f2SplitEquiv m) _ _ (fun _ => rfl), Fintype.sum_prod_type, sum_zmod2]
  rfl

/-- Exact 4-sector decomposition of Pauli expectations on `m + 1` qubits into `m`-qubit slices. -/
lemma pauliExpect_sectors {m : ℕ} (ψ : QState (m + 1)) (r : PauliIdx m) :
    let s0 := slice0 ψ
    let s1 := slice1 ψ
    (innerProd ψ (pauliApply (Fin.cons 0 r.1, Fin.cons 0 r.2) ψ)).re =
      (innerProd s0 (pauliApply r s0)).re + (innerProd s1 (pauliApply r s1)).re ∧
    (innerProd ψ (pauliApply (Fin.cons 0 r.1, Fin.cons 1 r.2) ψ)).re =
      (innerProd s0 (pauliApply r s0)).re - (innerProd s1 (pauliApply r s1)).re ∧
    (innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 0 r.2) ψ)).re =
      2 * (innerProd s0 (pauliApply r s1)).re ∧
    (innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ)).re ^ 2 =
      (2 * (innerProd s0 (pauliApply r s1)).im) ^ 2 := by
  intro s0 s1
  have hph00 : pauliPh (Fin.cons (0 : ZMod 2) r.1, Fin.cons (0 : ZMod 2) r.2) = pauliPh r := by
    simp [pauliPh, dot_cons]
  have hph01 : pauliPh (Fin.cons (0 : ZMod 2) r.1, Fin.cons (1 : ZMod 2) r.2) = pauliPh r := by
    simp [pauliPh, dot_cons]
  have hph10 : pauliPh (Fin.cons (1 : ZMod 2) r.1, Fin.cons (0 : ZMod 2) r.2) = pauliPh r := by
    simp [pauliPh, dot_cons]
  have hph11 : pauliPh (Fin.cons (1 : ZMod 2) r.1, Fin.cons (1 : ZMod 2) r.2) =
      (if dot r.1 r.2 = 0 then Complex.I else -Complex.I) * pauliPh r := by
    simp only [pauliPh, dot_cons, one_mul]
    rcases zmod2_cases (dot r.1 r.2) with h | h
    · simp [h]
    · simp [h, show (1 : ZMod 2) + 1 = 0 by decide]
  have h_I : innerProd ψ (pauliApply (Fin.cons 0 r.1, Fin.cons 0 r.2) ψ) =
      innerProd s0 (pauliApply r s0) + innerProd s1 (pauliApply r s1) := by
    rw [innerProd_split]
    refine congr_arg₂ (· + ·) ?_ ?_
    · simp only [innerProd]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, slice0, pauliApply, hph00, chi_cons, cons_add_cons, zero_mul, ↓reduceIte,
        zero_add, one_mul]
    · simp only [innerProd]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s1, slice1, pauliApply, hph00, chi_cons, cons_add_cons, zero_mul, ↓reduceIte,
        add_zero, one_mul]
  have h_Z : innerProd ψ (pauliApply (Fin.cons 0 r.1, Fin.cons 1 r.2) ψ) =
      innerProd s0 (pauliApply r s0) - innerProd s1 (pauliApply r s1) := by
    rw [innerProd_split, sub_eq_add_neg]
    refine congr_arg₂ (· + ·) ?_ ?_
    · simp only [innerProd]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, slice0, pauliApply, hph01, chi_cons, cons_add_cons, mul_zero, ↓reduceIte,
        zero_add, one_mul]
    · simp only [innerProd]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s1, slice1, pauliApply, hph01, chi_cons, cons_add_cons, mul_one,
        show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, add_zero, neg_one_mul, Int.cast_neg]
      ring
  have h_X : innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 0 r.2) ψ) =
      innerProd s0 (pauliApply r s1) + star (innerProd s0 (pauliApply r s1)) := by
    rw [innerProd_split]
    refine congr_arg₂ (· + ·) ?_ ?_
    · simp only [innerProd]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, s1, slice0, slice1, pauliApply, hph10, chi_cons, cons_add_cons, zero_mul,
        ↓reduceIte, zero_add, one_mul]
    · rw [innerProd_pauliApply_right r s0 s1, innerProd_conj_symm]
      refine congr_arg star ?_
      simp only [innerProd]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, s1, slice0, slice1, pauliApply, hph10, chi_cons, cons_add_cons, zero_mul,
        ↓reduceIte, show (1 : ZMod 2) + 1 = 0 by decide, one_mul]
  have h_Y : innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ) =
      (if dot r.1 r.2 = 0 then Complex.I else -Complex.I) *
        (innerProd s0 (pauliApply r s1) - star (innerProd s0 (pauliApply r s1))) := by
    rw [innerProd_split]
    have h0 : innerProd s0 (slice0 (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ)) =
        (if dot r.1 r.2 = 0 then Complex.I else -Complex.I) * innerProd s0 (pauliApply r s1) := by
      simp only [innerProd, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, s1, slice0, slice1, pauliApply, hph11, chi_cons, cons_add_cons, mul_zero,
        ↓reduceIte, zero_add, one_mul]
      ring
    have h1 : innerProd s1 (slice1 (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ)) =
        -(if dot r.1 r.2 = 0 then Complex.I else -Complex.I) *
          star (innerProd s0 (pauliApply r s1)) := by
      rw [innerProd_pauliApply_right r s0 s1, innerProd_conj_symm]
      have hstar : -(if dot r.1 r.2 = 0 then Complex.I else -Complex.I) =
          star (if dot r.1 r.2 = 0 then Complex.I else -Complex.I) := by
        split_ifs <;> simp
      rw [hstar, ← star_mul]
      refine congr_arg (star : ℂ → ℂ) ?_
      simp only [innerProd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [s0, s1, slice0, slice1, pauliApply, hph11, chi_cons, cons_add_cons, mul_one,
        show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, show (1 : ZMod 2) + 1 = 0 by decide,
        neg_one_mul, Int.cast_neg, star_mul', star_neg]
      split_ifs
      · simp; ring
      · simp; ring
    rw [h0, h1]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_I, Complex.add_re]
  · rw [h_Z, Complex.sub_re]
  · rw [h_X, Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  · rw [h_Y]
    set z := innerProd s0 (pauliApply r s1)
    have hsub : z - star z = (2 * z.im : ℝ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [hsub]
    split_ifs <;> simp

/-- **Theorem 17.1 — Exact Pauli-Slicing Renormalization Identity (ALL `m : ℕ`)**:
    Whenever `ψ : QState (m + 1)` decomposes on qubit `0` as
      `ψ (Fin.cons 0 x) = √w₀ • φ₀ x`,  `ψ (Fin.cons 1 x) = √w₁ • φ₁ x`  (`0 ≤ w₀, 0 ≤ w₁`),
    its Pauli 4th moment obeys the exact positive-definite identity
      `F_{m+1}(ψ) = 2 w₀⁴ Fₘ(φ₀) + 2 w₁⁴ Fₘ(φ₁) + 20 w₀² w₁² Gₘ(φ₀, φ₁) + 8 w₀² w₁² Q_phase(φ₀, φ₁)`. -/
theorem pauliMoment4_slicing_identity {m : ℕ} {ψ : QState (m + 1)}
    {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) {φ₀ φ₁ : QState m}
    (h0 : slice0 ψ = ((Real.sqrt w₀ : ℝ) : ℂ) • φ₀)
    (h1 : slice1 ψ = ((Real.sqrt w₁ : ℝ) : ℂ) • φ₁) :
    pauliMoment4 (m + 1) ψ =
      2 * w₀ ^ 4 * pauliMoment4 m φ₀ + 2 * w₁ ^ 4 * pauliMoment4 m φ₁ +
      20 * w₀ ^ 2 * w₁ ^ 2 * pauliOverlap4 φ₀ φ₁ +
      8 * w₀ ^ 2 * w₁ ^ 2 * pauliCrossPhaseTerm φ₀ φ₁ := by
  rw [pauliMoment4_eq_sum_re_pow4,
      ← Fintype.sum_equiv (pauliSplitEquiv m) _ _ (fun _ => rfl),
      Fintype.sum_prod_type, Finset.sum_comm]
  have hsq0 : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw₀
  have hsq1 : Real.sqrt w₁ ^ 2 = w₁ := Real.sq_sqrt hw₁
  have hsc0 : ∀ r : PauliIdx m,
      (innerProd (slice0 ψ) (pauliApply r (slice0 ψ))).re =
        w₀ * (innerProd φ₀ (pauliApply r φ₀)).re := fun r => by
    rw [h0, pauliApply_smul, innerProd_smul_left, innerProd_smul_right]
    simp only [Complex.star_def, Complex.conj_ofReal]
    have hre := innerProd_pauliApply_self_real r φ₀
    conv_lhs => rw [← hre]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc Real.sqrt w₀ * (Real.sqrt w₀ * (innerProd φ₀ (pauliApply r φ₀)).re)
        = Real.sqrt w₀ ^ 2 * (innerProd φ₀ (pauliApply r φ₀)).re := by ring
      _ = w₀ * (innerProd φ₀ (pauliApply r φ₀)).re := by rw [hsq0]
  have hsc1 : ∀ r : PauliIdx m,
      (innerProd (slice1 ψ) (pauliApply r (slice1 ψ))).re =
        w₁ * (innerProd φ₁ (pauliApply r φ₁)).re := fun r => by
    rw [h1, pauliApply_smul, innerProd_smul_left, innerProd_smul_right]
    simp only [Complex.star_def, Complex.conj_ofReal]
    have hre := innerProd_pauliApply_self_real r φ₁
    conv_lhs => rw [← hre]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc Real.sqrt w₁ * (Real.sqrt w₁ * (innerProd φ₁ (pauliApply r φ₁)).re)
        = Real.sqrt w₁ ^ 2 * (innerProd φ₁ (pauliApply r φ₁)).re := by ring
      _ = w₁ * (innerProd φ₁ (pauliApply r φ₁)).re := by rw [hsq1]
  have hsc01 : ∀ r : PauliIdx m,
      innerProd (slice0 ψ) (pauliApply r (slice1 ψ)) =
        ((Real.sqrt w₀ * Real.sqrt w₁ : ℝ) : ℂ) * innerProd φ₀ (pauliApply r φ₁) := fun r => by
    rw [h0, h1, pauliApply_smul, innerProd_smul_left, innerProd_smul_right]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]; ring
  have hterm : ∀ r : PauliIdx m,
      ∑ ab : ZMod 2 × ZMod 2,
          (innerProd ψ (pauliApply (pauliSplitEquiv m (ab, r)) ψ)).re ^ 4 =
        2 * w₀ ^ 4 * (innerProd φ₀ (pauliApply r φ₀)).re ^ 4 +
        2 * w₁ ^ 4 * (innerProd φ₁ (pauliApply r φ₁)).re ^ 4 +
        12 * w₀ ^ 2 * w₁ ^ 2 *
          ((innerProd φ₀ (pauliApply r φ₀)).re ^ 2 * (innerProd φ₁ (pauliApply r φ₁)).re ^ 2) +
        8 * w₀ ^ 2 * w₁ ^ 2 * Complex.normSq (innerProd φ₀ (pauliApply r φ₁)) ^ 2 +
        8 * w₀ ^ 2 * w₁ ^ 2 *
          ((innerProd φ₀ (pauliApply r φ₁)).re ^ 2 - (innerProd φ₀ (pauliApply r φ₁)).im ^ 2) ^ 2 := fun r => by
    rw [Fintype.sum_prod_type, sum_zmod2, sum_zmod2, sum_zmod2]
    dsimp only [pauliSplitEquiv, Equiv.coe_fn_mk]
    obtain ⟨hI, hZ, hX, hY2⟩ := pauliExpect_sectors ψ r
    have hY4 : (innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ)).re ^ 4 =
        (2 * (innerProd (slice0 ψ) (pauliApply r (slice1 ψ))).im) ^ 4 := by
      calc _ = ((innerProd ψ (pauliApply (Fin.cons 1 r.1, Fin.cons 1 r.2) ψ)).re ^ 2) ^ 2 := by ring
        _ = ((2 * (innerProd (slice0 ψ) (pauliApply r (slice1 ψ))).im) ^ 2) ^ 2 := by rw [hY2]
        _ = _ := by ring
    rw [hI, hZ, hX, hY4, hsc0 r, hsc1 r, hsc01 r]
    set z := innerProd φ₀ (pauliApply r φ₁)
    set s := Real.sqrt w₀ * Real.sqrt w₁
    have hre_s : (((s : ℝ) : ℂ) * z).re = s * z.re := by simp
    have him_s : (((s : ℝ) : ℂ) * z).im = s * z.im := by simp
    have hs4 : s ^ 4 = w₀ ^ 2 * w₁ ^ 2 := by
      calc s ^ 4 = (Real.sqrt w₀ ^ 2) ^ 2 * (Real.sqrt w₁ ^ 2) ^ 2 := by dsimp only [s]; ring
        _ = w₀ ^ 2 * w₁ ^ 2 := by rw [hsq0, hsq1]
    have hns : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq_apply, sq]
    rw [hre_s, him_s, hns]
    have hxy : (2 * (s * z.re)) ^ 4 + (2 * (s * z.im)) ^ 4 =
        s ^ 4 * (8 * (z.re ^ 2 + z.im ^ 2) ^ 2 + 8 * (z.re ^ 2 - z.im ^ 2) ^ 2) := by ring
    calc (w₀ * (innerProd φ₀ (pauliApply r φ₀)).re + w₁ * (innerProd φ₁ (pauliApply r φ₁)).re) ^ 4 +
          (w₀ * (innerProd φ₀ (pauliApply r φ₀)).re - w₁ * (innerProd φ₁ (pauliApply r φ₁)).re) ^ 4 +
          ((2 * (s * z.re)) ^ 4 + (2 * (s * z.im)) ^ 4)
        = 2 * w₀ ^ 4 * (innerProd φ₀ (pauliApply r φ₀)).re ^ 4 +
          2 * w₁ ^ 4 * (innerProd φ₁ (pauliApply r φ₁)).re ^ 4 +
          12 * w₀ ^ 2 * w₁ ^ 2 *
            ((innerProd φ₀ (pauliApply r φ₀)).re ^ 2 * (innerProd φ₁ (pauliApply r φ₁)).re ^ 2) +
          s ^ 4 * (8 * (z.re ^ 2 + z.im ^ 2) ^ 2 + 8 * (z.re ^ 2 - z.im ^ 2) ^ 2) := by
            rw [hxy]; ring
      _ = _ := by rw [hs4]; ring
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← pauliMoment4_eq_sum_re_pow4 φ₀, ← pauliMoment4_eq_sum_re_pow4 φ₁]
  change 2 * w₀ ^ 4 * pauliMoment4 m φ₀ + 2 * w₁ ^ 4 * pauliMoment4 m φ₁ +
    12 * w₀ ^ 2 * w₁ ^ 2 * pauliOverlap4 φ₀ φ₁ +
    8 * w₀ ^ 2 * w₁ ^ 2 * pauliCrossOverlap4 φ₀ φ₁ +
    8 * w₀ ^ 2 * w₁ ^ 2 * pauliCrossPhaseTerm φ₀ φ₁ = _
  rw [pauliCrossOverlap4_eq_pauliOverlap4 φ₀ φ₁]; ring

/-- Exact reduction from a small-`Z₀` expectation `|⟨ψ | Z₀ | ψ⟩| ≤ δ` to `𝒥ₘ`. -/
lemma pauliMoment4_ge_twoStateJ_of_Z0_bound {m : ℕ} {ψ : QState (m + 1)} (hunit : IsUnitState ψ)
    {δ : ℝ} (hδ1 : δ ≤ 1)
    (hZ0 : |(innerProd ψ (pauliApply (0, eVec 0) ψ)).re| ≤ δ) :
    ∃ φ₀ φ₁ : QState m, IsUnitState φ₀ ∧ IsUnitState φ₁ ∧
      (1 - δ) ^ 4 * twoStateJ φ₀ φ₁ ≤ pauliMoment4 (m + 1) ψ := by
  let w₀ : ℝ := (innerProd (slice0 ψ) (slice0 ψ)).re
  let w₁ : ℝ := (innerProd (slice1 ψ) (slice1 ψ)).re
  have hw₀ : 0 ≤ w₀ := innerProd_self_re_nonneg (slice0 ψ)
  have hw₁ : 0 ≤ w₁ := innerProd_self_re_nonneg (slice1 ψ)
  have hsum_w : w₀ + w₁ = 1 := by
    have h := congr_arg Complex.re (innerProd_split ψ ψ)
    rw [hunit, Complex.one_re, Complex.add_re] at h
    exact h.symm
  have hdiff_w : w₀ - w₁ = (innerProd ψ (pauliApply (0, eVec 0) ψ)).re := by
    have h0 : ((0 : F2 (m + 1)), eVec (0 : Fin (m + 1))) =
        ((Fin.cons (0 : ZMod 2) (0 : F2 m) : F2 (m + 1)),
         (Fin.cons (1 : ZMod 2) (0 : F2 m) : F2 (m + 1))) := by
      ext i <;> refine Fin.cases ?_ ?_ i <;> simp [eVec]
    rw [h0]
    have hsec := (pauliExpect_sectors ψ (0 : PauliIdx m)).2.1
    simp only [Prod.fst_zero, Prod.snd_zero, pauliApply_zero] at hsec
    exact hsec.symm
  have hw₀_ge : (1 - δ) / 2 ≤ w₀ := by
    have h1 : -δ ≤ w₀ - w₁ := by rw [hdiff_w]; exact neg_le_of_abs_le hZ0
    linarith
  have hw₁_ge : (1 - δ) / 2 ≤ w₁ := by
    have h1 : w₀ - w₁ ≤ δ := by rw [hdiff_w]; exact le_of_abs_le hZ0
    linarith
  have h1mδ : 0 ≤ 1 - δ := by linarith
  -- Construct unit states `φ₀, φ₁` (handling degenerate `w = 0` cleanly with `stdBasis 0`)!
  let e0 : QState m := fun x => if x = 0 then 1 else 0
  have he0_unit : IsUnitState e0 := by
    simp [IsUnitState, innerProd, e0]
  let φ₀ : QState m := if w₀ = 0 then e0 else ((1 / Real.sqrt w₀ : ℝ) : ℂ) • slice0 ψ
  let φ₁ : QState m := if w₁ = 0 then e0 else ((1 / Real.sqrt w₁ : ℝ) : ℂ) • slice1 ψ
  have hmk : ∀ (s : QState m) (w : ℝ), w = (innerProd s s).re → 0 ≤ w →
      let φ : QState m := if w = 0 then e0 else ((1 / Real.sqrt w : ℝ) : ℂ) • s
      IsUnitState φ ∧ s = ((Real.sqrt w : ℝ) : ℂ) • φ := fun s w hw hwnn => by
    dsimp only
    by_cases hw0 : w = 0
    · simp only [hw0, ↓reduceIte, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
      refine ⟨he0_unit, ?_⟩
      have hss : innerProd s s = 0 := by
        apply Complex.ext
        · rw [← hw, hw0]; simp
        · simp [innerProd_self_eq_sum_normSq]
      exact (innerProd_self_eq_zero_iff s).mp hss
    · simp only [hw0, ↓reduceIte]
      have hwpos : 0 < w := lt_of_le_of_ne hwnn (Ne.symm hw0)
      have hsq_pos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwpos
      have hsq_ne : Real.sqrt w ≠ 0 := ne_of_gt hsq_pos
      constructor
      · rw [IsUnitState, innerProd_smul_left, innerProd_smul_right]
        simp only [Complex.star_def, Complex.conj_ofReal]
        have hss : innerProd s s = (w : ℂ) := by
          rw [hw]; apply Complex.ext <;> simp [innerProd_self_eq_sum_normSq]
        rw [hss, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : 1 / Real.sqrt w * (1 / Real.sqrt w * w) = 1 := by
          have hsq2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hwnn
          field_simp [hsq_ne]; linarith
        rw [this]; simp
      · ext x; simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul]
        have : Real.sqrt w * (1 / Real.sqrt w) = 1 := by field_simp [hsq_ne]
        rw [this]; simp
  obtain ⟨hφ₀_unit, hs0_eq⟩ := hmk (slice0 ψ) w₀ rfl hw₀
  obtain ⟨hφ₁_unit, hs1_eq⟩ := hmk (slice1 ψ) w₁ rfl hw₁
  refine ⟨φ₀, φ₁, hφ₀_unit, hφ₁_unit, ?_⟩
  rw [pauliMoment4_slicing_identity hw₀ hw₁ hs0_eq hs1_eq]
  have hF0_nn : 0 ≤ pauliMoment4 m φ₀ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF1_nn : 0 ≤ pauliMoment4 m φ₁ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG_nn : 0 ≤ pauliOverlap4 φ₀ φ₁ := Finset.sum_nonneg fun _ _ => by positivity
  have hQ_nn : 0 ≤ pauliCrossPhaseTerm φ₀ φ₁ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw₀4 : ((1 - δ) / 2) ^ 4 ≤ w₀ ^ 4 := pow_le_pow_left₀ (by linarith) hw₀_ge 4
  have hw₁4 : ((1 - δ) / 2) ^ 4 ≤ w₁ ^ 4 := pow_le_pow_left₀ (by linarith) hw₁_ge 4
  have hw01 : ((1 - δ) / 2) ^ 4 ≤ w₀ ^ 2 * w₁ ^ 2 := by
    have h02 : ((1 - δ) / 2) ^ 2 ≤ w₀ ^ 2 := pow_le_pow_left₀ (by linarith) hw₀_ge 2
    have h12 : ((1 - δ) / 2) ^ 2 ≤ w₁ ^ 2 := pow_le_pow_left₀ (by linarith) hw₁_ge 2
    calc ((1 - δ) / 2) ^ 4 = ((1 - δ) / 2) ^ 2 * ((1 - δ) / 2) ^ 2 := by ring
      _ ≤ w₀ ^ 2 * w₁ ^ 2 := mul_le_mul h02 h12 (sq_nonneg _) (sq_nonneg _)
  have h1' : (1 - δ) ^ 4 / 8 * pauliMoment4 m φ₀ ≤ 2 * w₀ ^ 4 * pauliMoment4 m φ₀ := by
    have : (1 - δ) ^ 4 / 8 ≤ 2 * w₀ ^ 4 := by linarith
    exact mul_le_mul_of_nonneg_right this hF0_nn
  have h2' : (1 - δ) ^ 4 / 8 * pauliMoment4 m φ₁ ≤ 2 * w₁ ^ 4 * pauliMoment4 m φ₁ := by
    have : (1 - δ) ^ 4 / 8 ≤ 2 * w₁ ^ 4 := by linarith
    exact mul_le_mul_of_nonneg_right this hF1_nn
  have h3' : (1 - δ) ^ 4 * (5 / 4) * pauliOverlap4 φ₀ φ₁ ≤
      20 * w₀ ^ 2 * w₁ ^ 2 * pauliOverlap4 φ₀ φ₁ := by
    have : (1 - δ) ^ 4 * (5 / 4) ≤ 20 * w₀ ^ 2 * w₁ ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hG_nn
  have h4' : 0 ≤ 8 * w₀ ^ 2 * w₁ ^ 2 * pauliCrossPhaseTerm φ₀ φ₁ := by positivity
  rw [twoStateJ]; linarith

/-! ### Part 3: Explicit Elementary Clifford Conjugation & Unconditional Universal Reduction (Theorem 17.2) -/

/-- General invariance principle: any unitary transformation `U : QState n → QState n`
    whose Pauli conjugation permutes `PauliIdx n` via an equivalence `σ` up to unit phase
    preserves `pauliMoment4` and transports `|c_p|²`. -/
lemma pauliMoment4_eq_of_clifford {n : ℕ} (U : QState n → QState n) (σ : PauliIdx n ≃ PauliIdx n)
    (hunit_U : ∀ φ ψ, innerProd (U φ) (U ψ) = innerProd φ ψ)
    (hconj : ∀ (p : PauliIdx n) (ψ : QState n),
      ∃ s : ℂ, Complex.normSq s = 1 ∧ U (pauliApply p ψ) = s • pauliApply (σ p) (U ψ))
    (ψ : QState n) :
    (∀ p : PauliIdx n,
      (innerProd (U ψ) (pauliApply (σ p) (U ψ))).re ^ 2 = (innerProd ψ (pauliApply p ψ)).re ^ 2) ∧
    pauliMoment4 n (U ψ) = pauliMoment4 n ψ := by
  have hsq : ∀ p : PauliIdx n,
      (innerProd (U ψ) (pauliApply (σ p) (U ψ))).re ^ 2 = (innerProd ψ (pauliApply p ψ)).re ^ 2 := fun p => by
    obtain ⟨s, hs, hUp⟩ := hconj p ψ
    have heq : innerProd ψ (pauliApply p ψ) = s * innerProd (U ψ) (pauliApply (σ p) (U ψ)) := by
      rw [← hunit_U ψ (pauliApply p ψ), hUp, innerProd_smul_right]
    have hns := congr_arg Complex.normSq heq
    rw [map_mul, hs, one_mul] at hns
    have hr1 := innerProd_pauliApply_self_real p ψ
    have hr2 := innerProd_pauliApply_self_real (σ p) (U ψ)
    have hns1 : Complex.normSq (innerProd ψ (pauliApply p ψ)) =
        (innerProd ψ (pauliApply p ψ)).re ^ 2 := by
      conv_lhs => rw [← hr1]
      rw [Complex.normSq_ofReal, ← sq]
    have hns2 : Complex.normSq (innerProd (U ψ) (pauliApply (σ p) (U ψ))) =
        (innerProd (U ψ) (pauliApply (σ p) (U ψ))).re ^ 2 := by
      conv_lhs => rw [← hr2]
      rw [Complex.normSq_ofReal, ← sq]
    linarith
  refine ⟨hsq, ?_⟩
  rw [pauliMoment4_eq_sum_re_pow4, pauliMoment4_eq_sum_re_pow4]
  refine (Fintype.sum_equiv σ _ _ fun p => ?_).symm
  have h := hsq p
  calc (innerProd ψ (pauliApply p ψ)).re ^ 4
      = ((innerProd ψ (pauliApply p ψ)).re ^ 2) ^ 2 := by ring
    _ = ((innerProd (U ψ) (pauliApply (σ p) (U ψ))).re ^ 2) ^ 2 := by rw [h]
    _ = (innerProd (U ψ) (pauliApply (σ p) (U ψ))).re ^ 4 := by ring

/-- Elementary Clifford Gate 1: Single-qubit phase gate `S_k` on qubit `k`. -/
def cliffordPhase {n : ℕ} (k : Fin n) (ψ : QState n) : QState n :=
  fun x => (if x k = 0 then (1 : ℂ) else Complex.I) * ψ x

/-- Symplectic action of `S_k`: `(a, b) ↦ (a, b + a_k e_k)` (involution on `PauliIdx n`). -/
def phaseIdxEquiv {n : ℕ} (k : Fin n) : PauliIdx n ≃ PauliIdx n where
  toFun p := (p.1, Function.update p.2 k (p.1 k + p.2 k))
  invFun p := (p.1, Function.update p.2 k (p.1 k + p.2 k))
  left_inv p := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik; simp [← add_assoc, show ∀ c : ZMod 2, c + c = 0 from fun c => by
          rcases zmod2_cases c with rfl | rfl <;> decide]
      · simp [hik]
  right_inv p := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik; simp [← add_assoc, show ∀ c : ZMod 2, c + c = 0 from fun c => by
          rcases zmod2_cases c with rfl | rfl <;> decide]
      · simp [hik]

lemma cliffordPhase_unitary {n : ℕ} (k : Fin n) (φ ψ : QState n) :
    innerProd (cliffordPhase k φ) (cliffordPhase k ψ) = innerProd φ ψ := by
  simp only [innerProd, cliffordPhase]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x k = 0
  · simp [hx]
  · simp [hx]
    calc -(Complex.I * (starRingEnd ℂ) (φ x) * (Complex.I * ψ x))
        = -(Complex.I ^ 2) * ((starRingEnd ℂ) (φ x) * ψ x) := by ring
      _ = (starRingEnd ℂ) (φ x) * ψ x := by rw [Complex.I_sq]; ring

lemma cliffordPhase_conj {n : ℕ} (k : Fin n) (p : PauliIdx n) (ψ : QState n) :
    ∃ s : ℂ, Complex.normSq s = 1 ∧
      cliffordPhase k (pauliApply p ψ) = s • pauliApply (phaseIdxEquiv k p) (cliffordPhase k ψ) := by
  rcases p with ⟨a, b⟩
  let b' : F2 n := Function.update b k (a k + b k)
  have hdot_ab : dot a (Function.update b k (a k + b k)) = dot a b + a k := by
    have h1 : dot a b' - dot a b = a k * (a k + b k) - a k * b k := by
      simp only [dot, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single k]
      · simp [b']
      · intro i _ hik; simp [b', hik]
      · intro h; exact absurd (Finset.mem_univ k) h
    have h2 : a k * (a k + b k) - a k * b k = a k := by
      rcases zmod2_cases (a k) with ha | ha <;> rcases zmod2_cases (b k) with hb | hb <;>
        simp [ha, hb]
    rw [h2] at h1
    rw [eq_add_of_sub_eq h1, add_comm]
  have hdot_bx : ∀ x : F2 n, dot (Function.update b k (a k + b k)) x = dot b x + a k * x k := fun x => by
    have h1 : dot b' x - dot b x = (a k + b k) * x k - b k * x k := by
      simp only [dot, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single k]
      · simp [b']
      · intro i _ hik; simp [b', hik]
      · intro h; exact absurd (Finset.mem_univ k) h
    have h2 : (a k + b k) * x k - b k * x k = a k * x k := by ring
    rw [h2] at h1
    rw [eq_add_of_sub_eq h1, add_comm]
  refine ⟨if a k = 0 then 1 else if dot a b = 0 then -1 else 1, by split_ifs <;> simp, ?_⟩
  ext x
  simp only [cliffordPhase, pauliApply, Pi.smul_apply, smul_eq_mul, phaseIdxEquiv, Equiv.coe_fn_mk,
    pauliPh, chi, hdot_ab, hdot_bx, Pi.add_apply]
  rcases zmod2_cases (a k) with ha | ha <;> rcases zmod2_cases (x k) with hx | hx <;>
    rcases zmod2_cases (dot a b) with hab | hab <;> rcases zmod2_cases (dot b x) with hbx | hbx
  all_goals simp [ha, hx, hab, hbx, show (1 : ZMod 2) + 1 = 0 by decide,
    show (1 : ZMod 2) ≠ 0 by decide]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

/-- Elementary Clifford Gate 2: Single-qubit Hadamard gate `H_k` on qubit `k`. -/
noncomputable def cliffordHadamard {n : ℕ} (k : Fin n) (ψ : QState n) : QState n :=
  fun x => ((1 / Real.sqrt 2 : ℝ) : ℂ) *
    (if x k = 0 then ψ x + ψ (x + eVec k) else ψ (x + eVec k) - ψ x)

/-- Symplectic action of `H_k`: swaps `a k` and `b k` (involution on `PauliIdx n`). -/
def hadamardIdxEquiv {n : ℕ} (k : Fin n) : PauliIdx n ≃ PauliIdx n where
  toFun p := (Function.update p.1 k (p.2 k), Function.update p.2 k (p.1 k))
  invFun p := (Function.update p.1 k (p.2 k), Function.update p.2 k (p.1 k))
  left_inv p := by
    ext i <;> by_cases hik : i = k <;> simp [hik]
  right_inv p := by
    ext i <;> by_cases hik : i = k <;> simp [hik]

lemma cliffordHadamard_unitary {n : ℕ} (k : Fin n) (φ ψ : QState n) :
    innerProd (cliffordHadamard k φ) (cliffordHadamard k ψ) = innerProd φ ψ := by
  let S0 : Finset (F2 n) := Finset.univ.filter fun x : F2 n => x k = 0
  let S1 : Finset (F2 n) := Finset.univ.filter fun x : F2 n => ¬x k = 0
  have hsplit : ∀ f : F2 n → ℂ, ∑ x : F2 n, f x = ∑ x ∈ S0, (f x + f (x + eVec k)) := fun f => by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : F2 n => x k = 0),
        Finset.sum_add_distrib]
    congr 1
    refine (Finset.sum_nbij (· + eVec k) ?_ ?_ ?_ (fun _ _ => rfl)).symm
    · intro x hx
      have hx0 : x k = 0 := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [eVec, hx0]⟩
    · intro x₁ _ x₂ _ h
      have := congr_arg (· + eVec k) h; simpa [f2_add_cancel_right] using this
    · intro y hy
      have hy1 : y k ≠ 0 := (Finset.mem_filter.mp hy).2
      have hy1' : y k = 1 := (zmod2_cases (y k)).resolve_left hy1
      refine ⟨y + eVec k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, f2_add_cancel_right y _⟩
      simp [eVec, hy1', show (1 : ZMod 2) + 1 = 0 by decide]
  simp only [innerProd]
  rw [hsplit, hsplit]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 : x k = 0 := (Finset.mem_filter.mp hx).2
  have hx1 : (x + eVec k) k ≠ 0 := by simp [eVec, hx0]
  have hsq2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_mul]
    have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hne]; linarith
    rw [this]; push_cast; rfl
  simp only [cliffordHadamard, hx0, hx1, ↓reduceIte, f2_add_cancel_right, star_mul, star_add,
    star_sub, Complex.star_def, Complex.conj_ofReal]
  calc ((starRingEnd ℂ) (φ x) + (starRingEnd ℂ) (φ (x + eVec k))) * ((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ x + ψ (x + eVec k))) +
      ((starRingEnd ℂ) (φ x) - (starRingEnd ℂ) (φ (x + eVec k))) * ((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * (ψ x - ψ (x + eVec k)))
      = (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) *
          (2 * ((starRingEnd ℂ) (φ x) * ψ x + (starRingEnd ℂ) (φ (x + eVec k)) * ψ (x + eVec k))) := by ring
    _ = _ := by rw [hsq2]; ring

lemma cliffordHadamard_conj {n : ℕ} (k : Fin n) (p : PauliIdx n) (ψ : QState n) :
    ∃ s : ℂ, Complex.normSq s = 1 ∧
      cliffordHadamard k (pauliApply p ψ) = s • pauliApply (hadamardIdxEquiv k p) (cliffordHadamard k ψ) := by
  rcases p with ⟨a, b⟩
  let a' : F2 n := Function.update a k (b k)
  let b' : F2 n := Function.update b k (a k)
  have hdot_ab : dot a' b' = dot a b := by
    simp only [dot]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik; simp [a', b', mul_comm]
    · simp [a', b', hik]
  -- Express `dot b' x` explicitly via `dot b x`.
  have hdot_b' : ∀ x : F2 n, dot b' x = dot b x + b k * x k + a k * x k := fun x => by
    have h1 : dot b x - dot b' x = b k * x k - a k * x k := by
      simp only [dot, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single k]
      · simp [b']
      · intro i _ hik; simp [b', hik]
      · intro h; exact absurd (Finset.mem_univ k) h
    have h2 : ∀ u v : ZMod 2, u - v = u + v := fun u v => by
      rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;> decide
    have h3 : dot b x + dot b' x = b k * x k + a k * x k := by simpa [h2] using h1
    rcases zmod2_cases (dot b x) with hdb | hdb <;> rcases zmod2_cases (dot b' x) with hdb' | hdb' <;>
      rcases zmod2_cases (b k * x k) with hbx | hbx <;> rcases zmod2_cases (a k * x k) with hax | hax
    all_goals simp [hdb, hdb', hbx, hax, show (1 : ZMod 2) + 1 = 0 by decide] at h3 ⊢
  have hadd_e : ∀ x : F2 n, x + eVec k + a = (x + a) + eVec k := fun _ => by abel
  have hupd_eq : ∀ x : F2 n, a' = a + (if a k = b k then 0 else eVec k) := fun _ => by
    ext i
    by_cases hik : i = k
    · subst hik
      rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
        simp [a', eVec, ha, hb, show (1 : ZMod 2) + 1 = 0 by decide]
    · split_ifs <;> simp [a', eVec, hik]
  refine ⟨if a k = 1 ∧ b k = 1 then -1 else 1, by split_ifs <;> simp, ?_⟩
  ext x
  simp only [cliffordHadamard, pauliApply, Pi.smul_apply, smul_eq_mul, hadamardIdxEquiv,
    Equiv.coe_fn_mk, chi]
  have hph : pauliPh (a', b') = pauliPh (a, b) := by simp only [pauliPh, hdot_ab]
  have hdb_e : dot b (x + eVec k) = dot b x + b k := by
    rw [dot_add_right, dot_eVec_right]
  have hdb' := hdot_b' x
  have ha'x : x + a' = x + a + (if a k = b k then 0 else eVec k) := by
    rw [hupd_eq x, add_assoc]
  have ha'xe : x + a' + eVec k = x + a + (if a k = b k then eVec k else 0) := by
    rw [ha'x]
    split_ifs
    · rw [add_zero]
    · rw [f2_add_cancel_right, add_zero]
  have hxak : (x + a') k = x k + b k := by simp [a']
  dsimp only [a', b'] at hph hdb' ha'x ha'xe hxak
  rw [hph, hdb_e, hdb', hxak, ha'xe, ha'x, hadd_e x]
  rcases zmod2_cases (a k) with ha | ha <;> rcases zmod2_cases (b k) with hb | hb <;>
    rcases zmod2_cases (x k) with hx | hx <;> rcases zmod2_cases (dot b x) with hdb | hdb
  all_goals simp [ha, hb, hx, hdb, show (1 : ZMod 2) + 1 = 0 by decide,
    show (1 : ZMod 2) ≠ 0 by decide, add_zero]
  all_goals ring

/-- Elementary Clifford Gate 3: Qubit permutation `0 ↔ i`. -/
def cliffordSwap {m : ℕ} (i : Fin (m + 1)) (ψ : QState (m + 1)) : QState (m + 1) :=
  fun x => ψ (x ∘ Equiv.swap 0 i)

def swapIdxEquiv {m : ℕ} (i : Fin (m + 1)) : PauliIdx (m + 1) ≃ PauliIdx (m + 1) where
  toFun p := (p.1 ∘ Equiv.swap 0 i, p.2 ∘ Equiv.swap 0 i)
  invFun p := (p.1 ∘ Equiv.swap 0 i, p.2 ∘ Equiv.swap 0 i)
  left_inv p := by ext j <;> simp
  right_inv p := by ext j <;> simp

lemma cliffordSwap_unitary {m : ℕ} (i : Fin (m + 1)) (φ ψ : QState (m + 1)) :
    innerProd (cliffordSwap i φ) (cliffordSwap i ψ) = innerProd φ ψ := by
  simp only [innerProd, cliffordSwap]
  let e : F2 (m + 1) ≃ F2 (m + 1) :=
    { toFun := fun x => x ∘ Equiv.swap 0 i
      invFun := fun x => x ∘ Equiv.swap 0 i
      left_inv := fun x => by ext j; simp
      right_inv := fun x => by ext j; simp }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma cliffordSwap_conj {m : ℕ} (i : Fin (m + 1)) (p : PauliIdx (m + 1)) (ψ : QState (m + 1)) :
    ∃ s : ℂ, Complex.normSq s = 1 ∧
      cliffordSwap i (pauliApply p ψ) = s • pauliApply (swapIdxEquiv i p) (cliffordSwap i ψ) := by
  refine ⟨1, by simp, ?_⟩
  ext x
  have hdot : ∀ u v : F2 (m + 1), dot (u ∘ Equiv.swap 0 i) (v ∘ Equiv.swap 0 i) = dot u v := fun u v => by
    simp only [dot, Function.comp_apply]
    exact Fintype.sum_equiv (Equiv.swap (0 : Fin (m + 1)) i) _ _ (fun _ => rfl)
  have hdot2 : dot p.2 (x ∘ Equiv.swap 0 i) = dot (p.2 ∘ Equiv.swap 0 i) x := by
    rw [← hdot (p.2 ∘ Equiv.swap 0 i) x]
    congr 1; ext j; simp
  simp only [cliffordSwap, pauliApply, swapIdxEquiv, Equiv.coe_fn_mk, one_smul, pauliPh, chi]
  rw [hdot p.1 p.2, hdot2]
  have hadd : (x ∘ Equiv.swap 0 i) + p.1 = (x + (p.1 ∘ Equiv.swap 0 i)) ∘ Equiv.swap 0 i := by
    ext j; simp
  rw [hadd]

/-- Elementary Clifford Gate 4: Involutive CNOT basis-change mapping `(0, b) ↦ (0, e₀)` when `b 0 = 1`. -/
def zMapL {m : ℕ} (b : F2 (m + 1)) (x : F2 (m + 1)) : F2 (m + 1) :=
  Function.update x 0 (dot b x)

def zMapLT {m : ℕ} (b : F2 (m + 1)) (y : F2 (m + 1)) : F2 (m + 1) :=
  fun j => if j = 0 then y 0 else y j + b j * y 0

lemma zMapL_add {m : ℕ} (b x y : F2 (m + 1)) : zMapL b (x + y) = zMapL b x + zMapL b y := by
  ext j
  by_cases hj : j = 0
  · subst hj; simp [zMapL, dot_add_right]
  · simp [zMapL, hj]

lemma zMapL_invol {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1) (x : F2 (m + 1)) :
    zMapL b (zMapL b x) = x := by
  ext j
  by_cases hj : j = 0
  · subst hj
    simp only [zMapL, Function.update_self]
    have hdot : dot b (Function.update x 0 (dot b x)) =
        b 0 * dot b x + ∑ i : Fin m, b i.succ * x i.succ := by
      simp [dot, Fin.sum_univ_succ]
    have hdot0 : dot b x = b 0 * x 0 + ∑ i : Fin m, b i.succ * x i.succ := by
      simp [dot, Fin.sum_univ_succ]
    rw [hdot, hb0, one_mul, hdot0, hb0, one_mul, add_assoc]
    have hself : ∀ c : ZMod 2, c + c = 0 := fun c => by rcases zmod2_cases c with rfl | rfl <;> decide
    rw [hself, add_zero]
  · simp [zMapL, hj]

lemma zMapLT_invol {m : ℕ} (b y : F2 (m + 1)) : zMapLT b (zMapLT b y) = y := by
  ext j
  by_cases hj : j = 0
  · subst hj; simp [zMapLT]
  · simp only [zMapLT, hj, ↓reduceIte]
    have hself : ∀ c : ZMod 2, c + c = 0 := fun c => by rcases zmod2_cases c with rfl | rfl <;> decide
    rw [add_assoc, hself, add_zero]

lemma dot_zMapL {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1) (x y : F2 (m + 1)) :
    dot (zMapL b x) y = dot x (zMapLT b y) := by
  simp only [dot, zMapL, zMapLT, Fin.sum_univ_succ, Function.update_self, ↓reduceIte,
    Fin.succ_ne_zero]
  have hupd : ∀ i : Fin m,
      Function.update x 0 (b 0 * x 0 + ∑ j : Fin m, b j.succ * x j.succ) i.succ = x i.succ :=
    fun i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
  simp_rw [hupd]
  have h1 : (b 0 * x 0 + ∑ i : Fin m, b i.succ * x i.succ) * y 0 +
      ∑ i : Fin m, x i.succ * y i.succ =
      x 0 * y 0 + ∑ i : Fin m, (b i.succ * x i.succ * y 0 + x i.succ * y i.succ) := by
    rw [hb0, one_mul, add_mul, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
  have h2 : x 0 * y 0 + ∑ i : Fin m, x i.succ * (y i.succ + b i.succ * y 0) =
      x 0 * y 0 + ∑ i : Fin m, (b i.succ * x i.succ * y 0 + x i.succ * y i.succ) := by
    congr 1; refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]

def cliffordZMap {m : ℕ} (b : F2 (m + 1)) (ψ : QState (m + 1)) : QState (m + 1) :=
  fun x => ψ (zMapL b x)

def zMapIdxEquiv {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1) : PauliIdx (m + 1) ≃ PauliIdx (m + 1) where
  toFun p := (zMapL b p.1, zMapLT b p.2)
  invFun p := (zMapL b p.1, zMapLT b p.2)
  left_inv p := by ext i; exact congr_fun (zMapL_invol hb0 p.1) i; exact congr_fun (zMapLT_invol b p.2) i
  right_inv p := by ext i; exact congr_fun (zMapL_invol hb0 p.1) i; exact congr_fun (zMapLT_invol b p.2) i

lemma cliffordZMap_unitary {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1) (φ ψ : QState (m + 1)) :
    innerProd (cliffordZMap b φ) (cliffordZMap b ψ) = innerProd φ ψ := by
  simp only [innerProd, cliffordZMap]
  let e : F2 (m + 1) ≃ F2 (m + 1) :=
    { toFun := zMapL b, invFun := zMapL b,
      left_inv := zMapL_invol hb0, right_inv := zMapL_invol hb0 }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma cliffordZMap_conj {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1)
    (p : PauliIdx (m + 1)) (ψ : QState (m + 1)) :
    ∃ s : ℂ, Complex.normSq s = 1 ∧
      cliffordZMap b (pauliApply p ψ) = s • pauliApply (zMapIdxEquiv hb0 p) (cliffordZMap b ψ) := by
  refine ⟨1, by simp, ?_⟩
  ext x
  simp only [cliffordZMap, pauliApply, zMapIdxEquiv, Equiv.coe_fn_mk, one_smul, pauliPh, chi]
  have h1 : dot (zMapL b p.1) (zMapLT b p.2) = dot p.1 p.2 := by
    rw [← dot_zMapL hb0 (zMapL b p.1) p.2, zMapL_invol hb0]
  have h2 : dot (zMapLT b p.2) x = dot p.2 (zMapL b x) := by
    rw [dot_comm, ← dot_zMapL hb0 x p.2, dot_comm]
  have h3 : zMapL b (x + zMapL b p.1) = zMapL b x + p.1 := by
    rw [zMapL_add, zMapL_invol hb0]
  rw [h1, h2, h3]

lemma zMapLT_self {m : ℕ} {b : F2 (m + 1)} (hb0 : b 0 = 1) :
    zMapLT b b = eVec 0 := by
  ext j
  by_cases hj : j = 0
  · subst hj; simp [zMapLT, eVec, hb0]
  · simp only [zMapLT, eVec, hj, ↓reduceIte, Pi.single_eq_of_ne hj, hb0, mul_one]
    rcases zmod2_cases (b j) with h | h <;> simp [h, show (1 : ZMod 2) + 1 = 0 by decide]

/-- Fold single-qubit `S_k` and `H_k` over any subset of qubits `S` to turn any `q = (a, b)`
    into a pure-`Z` Pauli `(0, b')` while preserving `IsUnitState` and `pauliMoment4`. -/
lemma exists_clifford_to_pureZ {n : ℕ} (q : PauliIdx n) (hq : q ≠ 0)
    (ψ : QState n) (hunit : IsUnitState ψ) :
    ∃ (ψ' : QState n) (b' : F2 n), b' ≠ 0 ∧
      IsUnitState ψ' ∧ pauliMoment4 n ψ' = pauliMoment4 n ψ ∧
      (innerProd ψ' (pauliApply (0, b') ψ')).re ^ 2 = (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
  -- Strong induction on the number of qubits `k` with `q.1 k ≠ 0`!
  suffices h : ∀ (r : ℕ) (q : PauliIdx n),
      (Finset.univ.filter fun k : Fin n => q.1 k ≠ 0).card = r → q ≠ 0 →
      ∀ ψ : QState n, IsUnitState ψ →
      ∃ (ψ' : QState n) (b' : F2 n), b' ≠ 0 ∧
        IsUnitState ψ' ∧ pauliMoment4 n ψ' = pauliMoment4 n ψ ∧
        (innerProd ψ' (pauliApply (0, b') ψ')).re ^ 2 = (innerProd ψ (pauliApply q ψ)).re ^ 2 by
    exact h _ q rfl hq ψ hunit
  intro r
  induction r with
  | zero =>
    intro q hcard hq ψ hunit
    have ha0 : q.1 = 0 := by
      ext k
      by_contra hk
      have hmem : k ∈ Finset.univ.filter (fun i : Fin n => q.1 i ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      have hpos : 0 < (Finset.univ.filter fun i : Fin n => q.1 i ≠ 0).card :=
        Finset.card_pos.mpr ⟨k, hmem⟩
      omega
    have hb0 : q.2 ≠ 0 := by
      intro hb
      apply hq
      ext i
      · exact congr_fun ha0 i
      · exact congr_fun hb i
    refine ⟨ψ, q.2, hb0, hunit, rfl, ?_⟩
    have hqeq : (0, q.2) = q := Prod.ext ha0.symm rfl
    rw [hqeq]
  | succ r ih =>
    intro q hcard hq ψ hunit
    have hne : (Finset.univ.filter fun k : Fin n => q.1 k ≠ 0).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨k, hk⟩ := hne
    have hak : q.1 k = 1 := (zmod2_cases (q.1 k)).resolve_left (Finset.mem_filter.mp hk).2
    -- Step A: if `q.2 k = 1`, apply `S_k` to make `(q₁.1 k, q₁.2 k) = (1, 0)`; else keep `(ψ, q)`!
    have hstepA : ∃ (ψ₁ : QState n) (q₁ : PauliIdx n),
        q₁.1 = q.1 ∧ q₁.2 k = 0 ∧ IsUnitState ψ₁ ∧ pauliMoment4 n ψ₁ = pauliMoment4 n ψ ∧
        (innerProd ψ₁ (pauliApply q₁ ψ₁)).re ^ 2 = (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
      by_cases hbk : q.2 k = 0
      · exact ⟨ψ, q, rfl, hbk, hunit, rfl, rfl⟩
      · have hbk1 : q.2 k = 1 := (zmod2_cases (q.2 k)).resolve_left hbk
        obtain ⟨hsq, hF⟩ := pauliMoment4_eq_of_clifford (cliffordPhase k) (phaseIdxEquiv k)
          (cliffordPhase_unitary k) (cliffordPhase_conj k) ψ
        refine ⟨cliffordPhase k ψ, phaseIdxEquiv k q, rfl, ?_, ?_, hF, hsq q⟩
        · simp [phaseIdxEquiv, hak, hbk1, show (1 : ZMod 2) + 1 = 0 by decide]
        · rw [IsUnitState, cliffordPhase_unitary]; exact hunit
    obtain ⟨ψ₁, q₁, hq1_fst, hq1_bk, hunit₁, hF₁, hsq₁⟩ := hstepA
    -- Step B: apply `H_k` to swap `(q₁.1 k, q₁.2 k) = (1, 0) ↦ (0, 1)`!
    obtain ⟨hsq₂, hF₂⟩ := pauliMoment4_eq_of_clifford (cliffordHadamard k) (hadamardIdxEquiv k)
      (cliffordHadamard_unitary k) (cliffordHadamard_conj k) ψ₁
    let q₂ := hadamardIdxEquiv k q₁
    have hq2_ne : q₂ ≠ 0 := by
      intro h0
      have h2k : q₂.2 k = 0 := congr_fun (congr_arg Prod.snd h0) k
      have h2k1 : q₂.2 k = 1 := by simp [q₂, hadamardIdxEquiv, hq1_fst, hak]
      rw [h2k1] at h2k
      exact (show (1 : ZMod 2) ≠ 0 by decide) h2k
    have hfilt : (Finset.univ.filter fun i : Fin n => q₂.1 i ≠ 0) =
        (Finset.univ.filter fun i : Fin n => q.1 i ≠ 0).erase k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, q₂,
        hadamardIdxEquiv, Equiv.coe_fn_mk]
      by_cases hik : i = k
      · subst hik; simp [hq1_bk]
      · simp [hik, hq1_fst]
    have hcard₂ : (Finset.univ.filter fun i : Fin n => q₂.1 i ≠ 0).card = r := by
      rw [hfilt, Finset.card_erase_of_mem hk, hcard]; omega
    have hunit₂ : IsUnitState (cliffordHadamard k ψ₁) := by
      rw [IsUnitState, cliffordHadamard_unitary]; exact hunit₁
    obtain ⟨ψ', b', hb', hunit', hF', hsq'⟩ := ih q₂ hcard₂ hq2_ne (cliffordHadamard k ψ₁) hunit₂
    exact ⟨ψ', b', hb', hunit', by rw [hF', hF₂, hF₁], by rw [hsq', hsq₂ q₁, hsq₁]⟩

/-- **Explicit Elementary Clifford Conjugation (`q ≠ 0 ↦ Z₀`, ALL `m : ℕ`)**:
    For EVERY non-zero Pauli `q ≠ 0` and EVERY unit state `ψ : QState (m + 1)`, there exists a
    Clifford-equivalent unit state `ψ'` with identical `pauliMoment4` whose `Z₀ = (0, e₀)` squared
    expectation equals `c_q(ψ)²`. -/
theorem exists_clifford_to_Z0 {m : ℕ} (q : PauliIdx (m + 1)) (hq : q ≠ 0)
    (ψ : QState (m + 1)) (hunit : IsUnitState ψ) :
    ∃ ψ' : QState (m + 1), IsUnitState ψ' ∧
      pauliMoment4 (m + 1) ψ' = pauliMoment4 (m + 1) ψ ∧
      (innerProd ψ' (pauliApply (0, eVec 0) ψ')).re ^ 2 = (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
  obtain ⟨ψ₁, b₁, hb₁, hunit₁, hF₁, hsq₁⟩ := exists_clifford_to_pureZ q hq ψ hunit
  have hex : ∃ i : Fin (m + 1), b₁ i ≠ 0 := by
    by_contra h; push Not at h; exact hb₁ (funext h)
  obtain ⟨i, hi⟩ := hex
  -- Swap qubit `i ↔ 0` so `b₂ 0 = 1`!
  obtain ⟨hsq₂, hF₂⟩ := pauliMoment4_eq_of_clifford (cliffordSwap i) (swapIdxEquiv i)
    (cliffordSwap_unitary i) (cliffordSwap_conj i) ψ₁
  let ψ₂ := cliffordSwap i ψ₁
  let b₂ : F2 (m + 1) := b₁ ∘ Equiv.swap 0 i
  have hb₂0 : b₂ 0 = 1 := by
    have : b₂ 0 = b₁ i := by simp [b₂]
    rw [this]; exact (zmod2_cases (b₁ i)).resolve_left hi
  have hswap_q : swapIdxEquiv i (0, b₁) = (0, b₂) := by ext j <;> simp [swapIdxEquiv, b₂]
  have hunit₂ : IsUnitState ψ₂ := by rw [IsUnitState, cliffordSwap_unitary]; exact hunit₁
  -- Apply `cliffordZMap b₂` to map `(0, b₂) ↦ (0, eVec 0)`!
  obtain ⟨hsq₃, hF₃⟩ := pauliMoment4_eq_of_clifford (cliffordZMap b₂) (zMapIdxEquiv hb₂0)
    (cliffordZMap_unitary hb₂0) (cliffordZMap_conj hb₂0) ψ₂
  have hzmap_q : zMapIdxEquiv hb₂0 (0, b₂) = (0, eVec 0) := by
    refine Prod.ext ?_ (zMapLT_self hb₂0)
    ext j; by_cases hj : j = 0 <;> simp [zMapIdxEquiv, zMapL, hj, dot_zero_right]
  refine ⟨cliffordZMap b₂ ψ₂, ?_, by rw [hF₃, hF₂, hF₁], ?_⟩
  · rw [IsUnitState, cliffordZMap_unitary hb₂0]; exact hunit₂
  · rw [← hzmap_q, hsq₃ (0, b₂), ← hswap_q, hsq₂ (0, b₁), hsq₁]

/-- Pigeonhole minimum non-zero Pauli expectation: for EVERY unit state `ψ : QState (m + 1)`,
    there exists `q ≠ 0` with `c_q(ψ)² ≤ 1 / (2^{m+1} + 1)`. -/
lemma exists_small_pauliExpect {m : ℕ} {ψ : QState (m + 1)} (hunit : IsUnitState ψ) :
    ∃ q : PauliIdx (m + 1), q ≠ 0 ∧
      (innerProd ψ (pauliApply q ψ)).re ^ 2 ≤ 1 / ((2 : ℝ) ^ (m + 1) + 1) := by
  let d : ℝ := (2 : ℝ) ^ (m + 1)
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ (m + 1) := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_pos m)
    dsimp only [d]; exact_mod_cast this
  have hcard : ((nzPts (m + 1)).card : ℝ) = d ^ 2 - 1 := by
    simpa only [nzPts, d] using card_PauliIdx_erase_zero (m + 1)
  have hsum : ∑ q ∈ nzPts (m + 1), (innerProd ψ (pauliApply q ψ)).re ^ 2 = d - 1 :=
    sum_nz_pauliExpect_sq hunit
  have hne : (nzPts (m + 1)).Nonempty := by
    refine ⟨(0, eVec 0), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    intro h0
    have h1 : (eVec (0 : Fin (m + 1))) 0 = 0 := congr_fun (congr_arg Prod.snd h0) 0
    simp [eVec] at h1
  by_contra hall
  push Not at hall
  have hgt : ∑ q ∈ nzPts (m + 1), (1 / (d + 1) : ℝ) <
      ∑ q ∈ nzPts (m + 1), (innerProd ψ (pauliApply q ψ)).re ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun q hq => hall q (Finset.mem_erase.mp hq).1
  rw [Finset.sum_const, nsmul_eq_mul, hcard, hsum] at hgt
  have hd1_ne : d + 1 ≠ 0 := by linarith
  have heq : (d ^ 2 - 1) * (1 / (d + 1)) = d - 1 := by field_simp [hd1_ne]; ring
  linarith

/-- **Theorem 17.2 — Unconditional Universal Reduction (`F_{m+1}^* ≥ (1 - 1/√(d+1))⁴ · 𝒥ₘ^*`, ALL `m`)**:
    For EVERY `m : ℕ` and EVERY `(m + 1)`-qubit unit state `ψ` (ZERO flatness or near-Welch hypotheses!),
    there exist `m`-qubit unit states `φ₀, φ₁` such that
      `(1 - 1 / √(2^{m+1} + 1))⁴ · 𝒥ₘ(φ₀, φ₁) ≤ pauliMoment4 (m + 1) ψ`. -/
theorem pauliMoment4_ge_twoStateJ_universal {m : ℕ} {ψ : QState (m + 1)} (hunit : IsUnitState ψ) :
    ∃ φ₀ φ₁ : QState m, IsUnitState φ₀ ∧ IsUnitState φ₁ ∧
      (1 - 1 / Real.sqrt ((2 : ℝ) ^ (m + 1) + 1)) ^ 4 * twoStateJ φ₀ φ₁ ≤
        pauliMoment4 (m + 1) ψ := by
  obtain ⟨q, hq_ne, hq_le⟩ := exists_small_pauliExpect hunit
  obtain ⟨ψ', hunit', hF', hsq'⟩ := exists_clifford_to_Z0 q hq_ne ψ hunit
  let δ : ℝ := 1 / Real.sqrt ((2 : ℝ) ^ (m + 1) + 1)
  have hd1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) + 1 := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by positivity
    linarith
  have hsq_ge1 : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (m + 1) + 1) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hd1_ge1
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    exact (div_le_one (by linarith)).mpr hsq_ge1
  have hZ0 : |(innerProd ψ' (pauliApply (0, eVec 0) ψ')).re| ≤ δ := by
    have hsq_le : (innerProd ψ' (pauliApply (0, eVec 0) ψ')).re ^ 2 ≤ δ ^ 2 := by
      rw [hsq']
      have hδ2 : δ ^ 2 = 1 / ((2 : ℝ) ^ (m + 1) + 1) := by
        dsimp only [δ]; rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]
      rw [hδ2]; exact hq_le
    have hδ_nn : 0 ≤ δ := by dsimp only [δ]; positivity
    exact abs_le_of_sq_le_sq hsq_le hδ_nn
  obtain ⟨φ₀, φ₁, h0, h1, hle⟩ := pauliMoment4_ge_twoStateJ_of_Z0_bound hunit' hδ1 hZ0
  exact ⟨φ₀, φ₁, h0, h1, by rwa [hF'] at hle⟩

/-! ### Part 4: Hyperplane & Quadric Mass Concentration + `17 / 8 = 2.125 > 2` Constant-Gap Theorems -/

/-- Exact hyperplane mass split via Bell self-duality (`ALL m, q ≠ 0`). -/
theorem sum_pauliSq_hyperplane {m : ℕ} {φ : QState m} (hunit : IsUnitState φ)
    {q : PauliIdx m} (hq : q ≠ 0) :
    let D : ℝ := (2 : ℝ) ^ m
    let cq2 : ℝ := (innerProd φ (pauliApply q φ)).re ^ 2
    ∑ r ∈ (nzPts m).filter (fun r => symp q r = 0), (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D - 2 + D * cq2) / 2 ∧
    ∑ r ∈ (nzPts m).filter (fun r => ¬symp q r = 0), (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D - D * cq2) / 2 := by
  intro D cq2
  let S0 := (nzPts m).filter (fun r => symp q r = 0)
  let S1 := (nzPts m).filter (fun r => ¬symp q r = 0)
  have hadd : ∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 +
      ∑ r ∈ S1, (innerProd φ (pauliApply r φ)).re ^ 2 = D - 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_nz_pauliExpect_sq hunit]
  have hsd := pauli_symp_self_dual φ q
  have hre_ns : ∀ r : PauliIdx m, Complex.normSq (innerProd φ (pauliApply r φ)) =
      (innerProd φ (pauliApply r φ)).re ^ 2 := fun r => by
    have hre := innerProd_pauliApply_self_real r φ
    conv_lhs => rw [← hre]
    rw [Complex.normSq_ofReal, ← sq]
  simp_rw [hre_ns, sympSign_comm _ q] at hsd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
      show sympSign q 0 = 1 by simp [sympSign, symp_zero_right],
      Int.cast_one, one_mul, pauliExpect_zero_re hunit, one_pow] at hsd
  change 1 + ∑ r ∈ nzPts m, (sympSign q r : ℝ) * (innerProd φ (pauliApply r φ)).re ^ 2 = D * cq2 at hsd
  rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => symp q r = 0)] at hsd
  have hs0 : ∑ r ∈ S0, (sympSign q r : ℝ) * (innerProd φ (pauliApply r φ)).re ^ 2 =
      ∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 :=
    Finset.sum_congr rfl fun r hr => by simp [sympSign, (Finset.mem_filter.mp hr).2]
  have hs1 : ∑ r ∈ S1, (sympSign q r : ℝ) * (innerProd φ (pauliApply r φ)).re ^ 2 =
      -∑ r ∈ S1, (innerProd φ (pauliApply r φ)).re ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => by simp [sympSign, (Finset.mem_filter.mp hr).2]
  have hsub : ∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 -
      ∑ r ∈ S1, (innerProd φ (pauliApply r φ)).re ^ 2 = D * cq2 - 1 := by
    have : 1 + (∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 +
        -∑ r ∈ S1, (innerProd φ (pauliApply r φ)).re ^ 2) = D * cq2 := by
      simpa only [S0, S1, hs0, hs1] using hsd
    linarith
  have _ := hq
  exact ⟨by linarith, by linarith⟩

/-- Exact hyperbolic-quadric mass split via Theorem B (`ALL m, p : PauliIdx m`). -/
theorem sum_pauliSq_quadric {m : ℕ} {φ : QState m} (hunit : IsUnitState φ) (p : PauliIdx m) :
    let D : ℝ := (2 : ℝ) ^ m
    let wp : ℝ := symPauliNormSq φ p
    ∑ r ∈ (nzPts m).filter (fun r => quadForm p r = 0), (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D - 2 + D * wp) / 2 ∧
    ∑ r ∈ (nzPts m).filter (fun r => ¬quadForm p r = 0), (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D - D * wp) / 2 := by
  intro D wp
  let Q0 := (nzPts m).filter (fun r => quadForm p r = 0)
  let Q1 := (nzPts m).filter (fun r => ¬quadForm p r = 0)
  have hadd : ∑ r ∈ Q0, (innerProd φ (pauliApply r φ)).re ^ 2 +
      ∑ r ∈ Q1, (innerProd φ (pauliApply r φ)).re ^ 2 = D - 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_nz_pauliExpect_sq hunit]
  have hw := symPauliNormSq_eq_sympWHT φ p
  have hD_ne : D ≠ 0 := by positivity
  have hsd : ∑ r : PauliIdx m, (if quadForm p r = 0 then (1 : ℝ) else -1) *
      (innerProd φ (pauliApply r φ)).re ^ 2 = D * wp := by
    have h1 : D * symPauliNormSq φ p =
        ∑ r : PauliIdx m, (if quadForm p r = 0 then (1 : ℝ) else -1) *
          (innerProd φ (pauliApply r φ)).re ^ 2 := by
      rw [hw]; dsimp only [D]; field_simp [hD_ne]
    exact h1.symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
      show quadForm p 0 = 0 by simp [quadForm, quadForm0, dot_zero_left, symp_zero_right],
      pauliExpect_zero_re hunit] at hsd
  simp only [↓reduceIte, one_mul, one_pow] at hsd
  change 1 + ∑ r ∈ nzPts m, (if quadForm p r = 0 then (1 : ℝ) else -1) *
      (innerProd φ (pauliApply r φ)).re ^ 2 = D * wp at hsd
  rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => quadForm p r = 0)] at hsd
  have hq0 : ∑ r ∈ Q0, (if quadForm p r = 0 then (1 : ℝ) else -1) *
      (innerProd φ (pauliApply r φ)).re ^ 2 =
      ∑ r ∈ Q0, (innerProd φ (pauliApply r φ)).re ^ 2 :=
    Finset.sum_congr rfl fun r hr => by simp [(Finset.mem_filter.mp hr).2]
  have hq1 : ∑ r ∈ Q1, (if quadForm p r = 0 then (1 : ℝ) else -1) *
      (innerProd φ (pauliApply r φ)).re ^ 2 =
      -∑ r ∈ Q1, (innerProd φ (pauliApply r φ)).re ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => by simp [(Finset.mem_filter.mp hr).2]
  have hsub : ∑ r ∈ Q0, (innerProd φ (pauliApply r φ)).re ^ 2 -
      ∑ r ∈ Q1, (innerProd φ (pauliApply r φ)).re ^ 2 = D * wp - 1 := by
    have : 1 + (∑ r ∈ Q0, (innerProd φ (pauliApply r φ)).re ^ 2 +
        -∑ r ∈ Q1, (innerProd φ (pauliApply r φ)).re ^ 2) = D * wp := by
      simpa only [Q0, Q1, hq0, hq1] using hsd
    linarith
  exact ⟨by linarith, by linarith⟩

lemma card_nz_filter_symp {m : ℕ} {q : PauliIdx m} (hq : q ≠ 0) :
    (((nzPts m).filter (fun r => symp q r = 0)).card : ℝ) = ((2 : ℝ) ^ m) ^ 2 / 2 - 1 ∧
    (((nzPts m).filter (fun r => ¬symp q r = 0)).card : ℝ) = ((2 : ℝ) ^ m) ^ 2 / 2 := by
  let S0 := (nzPts m).filter (fun r => symp q r = 0)
  let S1 := (nzPts m).filter (fun r => ¬symp q r = 0)
  have hadd : (S0.card : ℝ) + (S1.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 - 1 := by
    have h1 := Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => symp q r = 0) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [h1]; exact card_PauliIdx_erase_zero m
  have hsum : ∑ r : PauliIdx m, (sympSign q r : ℝ) = 0 := by
    have hz := sum_sympSign_univ q
    have hcast : ∑ r : PauliIdx m, (sympSign q r : ℝ) = ((∑ r : PauliIdx m, sympSign q r : ℤ) : ℝ) := by
      rw [Int.cast_sum]
    rw [hcast, hz]; simp [hq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
      show sympSign q 0 = 1 by simp [sympSign, symp_zero_right], Int.cast_one] at hsum
  change 1 + ∑ r ∈ nzPts m, (sympSign q r : ℝ) = 0 at hsum
  rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => symp q r = 0)] at hsum
  have hs0 : ∑ r ∈ S0, (sympSign q r : ℝ) = (S0.card : ℝ) := by
    have : ∀ r ∈ S0, (sympSign q r : ℝ) = 1 := fun r hr => by simp [sympSign, (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hs1 : ∑ r ∈ S1, (sympSign q r : ℝ) = -(S1.card : ℝ) := by
    have : ∀ r ∈ S1, (sympSign q r : ℝ) = -1 := fun r hr => by simp [sympSign, (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hsub : (S0.card : ℝ) - (S1.card : ℝ) = -1 := by
    have : 1 + ((S0.card : ℝ) + -(S1.card : ℝ)) = 0 := by simpa only [S0, S1, hs0, hs1] using hsum
    linarith
  exact ⟨by linarith, by linarith⟩

lemma card_nz_filter_quadForm {m : ℕ} {p : PauliIdx m} (hp : quadForm0 p = 0) :
    (((nzPts m).filter (fun r => quadForm p r = 0)).card : ℝ) =
      ((2 : ℝ) ^ m - 1) * ((2 : ℝ) ^ m + 2) / 2 ∧
    (((nzPts m).filter (fun r => ¬quadForm p r = 0)).card : ℝ) =
      (2 : ℝ) ^ m * ((2 : ℝ) ^ m - 1) / 2 := by
  let Q0 := (nzPts m).filter (fun r => quadForm p r = 0)
  let Q1 := (nzPts m).filter (fun r => ¬quadForm p r = 0)
  have hadd : (Q0.card : ℝ) + (Q1.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 - 1 := by
    have h1 := Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => quadForm p r = 0) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [h1]; exact card_PauliIdx_erase_zero m
  have hsum : ∑ r : PauliIdx m, (if quadForm p r = 0 then (1 : ℝ) else -1) = (2 : ℝ) ^ m := by
    have hq := sum_quadChar p
    have hcast : ∑ r : PauliIdx m, (if quadForm p r = 0 then (1 : ℝ) else -1) =
        ((∑ r : PauliIdx m, (if quadForm p r = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      refine Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
    rw [hcast, hq, hp]; simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
      show quadForm p 0 = 0 by simp [quadForm, quadForm0, dot_zero_left, symp_zero_right]] at hsum
  simp only [↓reduceIte] at hsum
  change 1 + ∑ r ∈ nzPts m, (if quadForm p r = 0 then (1 : ℝ) else -1) = (2 : ℝ) ^ m at hsum
  rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun r => quadForm p r = 0)] at hsum
  have hq0 : ∑ r ∈ Q0, (if quadForm p r = 0 then (1 : ℝ) else -1) = (Q0.card : ℝ) := by
    have : ∀ r ∈ Q0, (if quadForm p r = 0 then (1 : ℝ) else -1) = 1 := fun r hr => by
      simp [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hq1 : ∑ r ∈ Q1, (if quadForm p r = 0 then (1 : ℝ) else -1) = -(Q1.card : ℝ) := by
    have : ∀ r ∈ Q1, (if quadForm p r = 0 then (1 : ℝ) else -1) = -1 := fun r hr => by
      simp [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hsub : (Q0.card : ℝ) - (Q1.card : ℝ) = (2 : ℝ) ^ m - 1 := by
    have : 1 + ((Q0.card : ℝ) + -(Q1.card : ℝ)) = (2 : ℝ) ^ m := by
      simpa only [Q0, Q1, hq0, hq1] using hsum
    linarith
  exact ⟨by linarith, by linarith⟩

/-- Shared 1-line Cauchy–Schwarz partition engine on `nzPts m` for any predicate `P`. -/
lemma twoStateJ_ge_of_partition {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) (P : PauliIdx m → Prop) [DecidablePred P]
    {M0 M1 N0 N1 : ℝ} (hN0 : 0 < N0) (hN1 : 0 < N1)
    (hc0 : (((nzPts m).filter P).card : ℝ) = N0)
    (hc1 : (((nzPts m).filter (fun r => ¬P r)).card : ℝ) = N1)
    (hM0 : ∑ r ∈ (nzPts m).filter P,
      ((innerProd φ₁ (pauliApply r φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply r φ₂)).re ^ 2) = M0)
    (hM1 : ∑ r ∈ (nzPts m).filter (fun r => ¬P r),
      ((innerProd φ₁ (pauliApply r φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply r φ₂)).re ^ 2) = M1) :
    3 / 2 + (M0 ^ 2 / N0 + M1 ^ 2 / N1) / 8 ≤ twoStateJ φ₁ φ₂ := by
  let x : PauliIdx m → ℝ := fun r => (innerProd φ₁ (pauliApply r φ₁)).re ^ 2
  let y : PauliIdx m → ℝ := fun r => (innerProd φ₂ (pauliApply r φ₂)).re ^ 2
  have hF1 : pauliMoment4 m φ₁ = 1 + ∑ r ∈ nzPts m, x r ^ 2 := by
    rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
        pauliExpect_zero_re h1, one_pow]
    change 1 + ∑ r ∈ nzPts m, (innerProd φ₁ (pauliApply r φ₁)).re ^ 4 =
      1 + ∑ r ∈ nzPts m, x r ^ 2
    congr 1; refine Finset.sum_congr rfl fun r _ => by dsimp only [x]; ring
  have hF2 : pauliMoment4 m φ₂ = 1 + ∑ r ∈ nzPts m, y r ^ 2 := by
    rw [pauliMoment4_eq_sum_re_pow4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
        pauliExpect_zero_re h2, one_pow]
    change 1 + ∑ r ∈ nzPts m, (innerProd φ₂ (pauliApply r φ₂)).re ^ 4 =
      1 + ∑ r ∈ nzPts m, y r ^ 2
    congr 1; refine Finset.sum_congr rfl fun r _ => by dsimp only [y]; ring
  have hJ : twoStateJ φ₁ φ₂ =
      3 / 2 + (∑ r ∈ nzPts m, (x r + y r) ^ 2) / 8 + pauliSupportOverlap φ₁ φ₂ := by
    have hexp : ∑ r ∈ nzPts m, (x r + y r) ^ 2 =
        ∑ r ∈ nzPts m, x r ^ 2 + ∑ r ∈ nzPts m, y r ^ 2 + 2 * pauliSupportOverlap φ₁ φ₂ := by
      have ht : ∀ r ∈ nzPts m, (x r + y r) ^ 2 = x r ^ 2 + y r ^ 2 + 2 * (x r * y r) := fun _ _ => by ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
    rw [twoStateJ, pauliOverlap4_eq_one_add_supportOverlap h1 h2, hF1, hF2, hexp]; ring
  have hC_nn : 0 ≤ pauliSupportOverlap φ₁ φ₂ := Finset.sum_nonneg fun _ _ => by positivity
  have hcs0 : M0 ^ 2 / N0 ≤ ∑ r ∈ (nzPts m).filter P, (x r + y r) ^ 2 := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq ((nzPts m).filter P) (fun _ => (1 : ℝ)) (fun r => x r + y r)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hc0] at h0
    rw [show ∑ r ∈ (nzPts m).filter P, (x r + y r) = M0 from hM0] at h0
    exact (div_le_iff₀ hN0).mpr (by linarith)
  have hcs1 : M1 ^ 2 / N1 ≤ ∑ r ∈ (nzPts m).filter (fun r => ¬P r), (x r + y r) ^ 2 := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq ((nzPts m).filter (fun r => ¬P r))
      (fun _ => (1 : ℝ)) (fun r => x r + y r)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hc1] at h0
    rw [show ∑ r ∈ (nzPts m).filter (fun r => ¬P r), (x r + y r) = M1 from hM1] at h0
    exact (div_le_iff₀ hN1).mpr (by linarith)
  have hsplit : ∑ r ∈ nzPts m, (x r + y r) ^ 2 =
      ∑ r ∈ (nzPts m).filter P, (x r + y r) ^ 2 +
      ∑ r ∈ (nzPts m).filter (fun r => ¬P r), (x r + y r) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not (nzPts m) P (fun r => (x r + y r) ^ 2)).symm
  rw [hJ, hsplit]; linarith

/-- **Theorem 17.4(a) — General Hyperplane Lower Bound on `𝒥ₘ` (ALL `m ≥ 1`, `q ≠ 0`)**:
    With `S = (c_q(φ₁)² + c_q(φ₂)²) / 2`,
      `3 / 2 + ((D - 2 + D * S)² / (D²/2 - 1) + (D - D * S)² / (D²/2)) / 8 ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_of_hyperplane {m : ℕ} (hm : 1 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) {q : PauliIdx m} (hq : q ≠ 0) :
    let D : ℝ := (2 : ℝ) ^ m
    let S : ℝ := ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 +
                  (innerProd φ₂ (pauliApply q φ₂)).re ^ 2) / 2
    3 / 2 + ((D - 2 + D * S) ^ 2 / (D ^ 2 / 2 - 1) + (D - D * S) ^ 2 / (D ^ 2 / 2)) / 8 ≤
      twoStateJ φ₁ φ₂ := by
  intro D S
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have : (2 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  obtain ⟨hc0, hc1⟩ := card_nz_filter_symp hq
  obtain ⟨hp0, hp1⟩ := sum_pauliSq_hyperplane h1 hq
  obtain ⟨hq0, hq1⟩ := sum_pauliSq_hyperplane h2 hq
  dsimp only [D, S]
  refine twoStateJ_ge_of_partition h1 h2 (fun r => symp q r = 0)
    (by dsimp only [D] at hD_ge2; nlinarith) (by dsimp only [D] at hD_ge2; nlinarith) hc0 hc1 ?_ ?_
  · rw [Finset.sum_add_distrib, hp0, hq0]; ring
  · rw [Finset.sum_add_distrib, hp1, hq1]; ring

/-- **Theorem 17.4(b) — General Hyperbolic-Quadric Lower Bound on `𝒥ₘ` (ALL `m ≥ 1`, `p ∈ symPts m`)**:
    With `W = (w_p(φ₁) + w_p(φ₂)) / 2`,
      `3 / 2 + ((D - 2 + D * W)² / ((D - 1)(D + 2)/2) + (D - D * W)² / (D(D - 1)/2)) / 8 ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_of_quadric {m : ℕ} (hm : 1 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) {p : PauliIdx m} (hp : quadForm0 p = 0) :
    let D : ℝ := (2 : ℝ) ^ m
    let W : ℝ := (symPauliNormSq φ₁ p + symPauliNormSq φ₂ p) / 2
    3 / 2 + ((D - 2 + D * W) ^ 2 / ((D - 1) * (D + 2) / 2) +
             (D - D * W) ^ 2 / (D * (D - 1) / 2)) / 8 ≤
      twoStateJ φ₁ φ₂ := by
  intro D W
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have : (2 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  obtain ⟨hc0, hc1⟩ := card_nz_filter_quadForm hp
  obtain ⟨hp0, hp1⟩ := sum_pauliSq_quadric h1 p
  obtain ⟨hq0, hq1⟩ := sum_pauliSq_quadric h2 p
  dsimp only [D, W]
  refine twoStateJ_ge_of_partition h1 h2 (fun r => quadForm p r = 0)
    (by dsimp only [D] at hD_ge2; nlinarith) (by dsimp only [D] at hD_ge2; nlinarith) hc0 hc1 ?_ ?_
  · rw [Finset.sum_add_distrib, hp0, hq0]; ring
  · rw [Finset.sum_add_distrib, hp1, hq1]; ring

/-- **Theorem 17.4(c) — Unconditional `17 / 8 = 2.125 > 2` Constant-Gap Theorem for Real-Sliced Pairs (`ALL m ≥ 2`)**:
    Whenever EITHER `φ₁` or `φ₂` is Clifford-equivalent to a real state (`∃ p, w_p = 1`),
      `17 / 8 - (16 D - 18) / (8 (D - 1) (D + 2)) ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_seventeen_eighths_of_real {m : ℕ} (hm : 2 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (hreal : ∃ p : PauliIdx m, symPauliNormSq φ₁ p = 1 ∨ symPauliNormSq φ₂ p = 1) :
    let D : ℝ := (2 : ℝ) ^ m
    17 / 8 - (16 * D - 18) / (8 * (D - 1) * (D + 2)) ≤ twoStateJ φ₁ φ₂ := by
  intro D
  have hD_ge4 : (4 : ℝ) ≤ D := by
    have : (4 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  obtain ⟨p, hp_one⟩ := hreal
  have hp0 : quadForm0 p = 0 := by
    by_contra hne
    rcases hp_one with h | h
    · have : symPauliNormSq φ₁ p = 0 := by simp [symPauliNormSq, symPauliExpect_eq_zero_of_antisym φ₁ hne]
      linarith
    · have : symPauliNormSq φ₂ p = 0 := by simp [symPauliNormSq, symPauliExpect_eq_zero_of_antisym φ₂ hne]
      linarith
  have hbase := twoStateJ_ge_of_quadric (by omega) h1 h2 hp0
  dsimp only at hbase
  let W : ℝ := (symPauliNormSq φ₁ p + symPauliNormSq φ₂ p) / 2
  have hw1_nn : 0 ≤ symPauliNormSq φ₁ p := Complex.normSq_nonneg _
  have hw2_nn : 0 ≤ symPauliNormSq φ₂ p := Complex.normSq_nonneg _
  have hW_ge : (1 / 2 : ℝ) ≤ W := by
    dsimp only [W]
    rcases hp_one with h | h <;> linarith
  -- Monotonicity in `t := W - 1/2 ≥ 0`: quadratic + linear terms are BOTH non-negative for `D ≥ 4`!
  let t : ℝ := W - 1 / 2
  have ht_nn : 0 ≤ t := by dsimp only [t]; linarith
  let N0 : ℝ := (D - 1) * (D + 2) / 2
  let N1 : ℝ := D * (D - 1) / 2
  have hN0_pos : 0 < N0 := by dsimp only [N0]; nlinarith
  have hN1_pos : 0 < N1 := by dsimp only [N1]; nlinarith
  have hN0_ne : N0 ≠ 0 := ne_of_gt hN0_pos
  have hN1_ne : N1 ≠ 0 := ne_of_gt hN1_pos
  have hmono : (3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1 ≤
      (D - 2 + D * W) ^ 2 / N0 + (D - D * W) ^ 2 / N1 := by
    have hW_eq : W = 1 / 2 + t := by dsimp only [t]; ring
    rw [hW_eq]
    have hdiff : ((D - 2 + D * (1 / 2 + t)) ^ 2 / N0 + (D - D * (1 / 2 + t)) ^ 2 / N1) -
        ((3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1) =
        (D * t) ^ 2 * (1 / N0 + 1 / N1) +
        2 * (D * t) * ((3 * D / 2 - 2) / N0 - (D / 2) / N1) := by
      field_simp [hN0_ne, hN1_ne]; ring
    have hlin_nn : 0 ≤ (3 * D / 2 - 2) / N0 - (D / 2) / N1 := by
      have hDm1_ne : D - 1 ≠ 0 := by linarith
      have hDp2_ne : D + 2 ≠ 0 := by linarith
      have hD_ne : D ≠ 0 := by linarith
      have hrew : (3 * D / 2 - 2) / N0 - (D / 2) / N1 = (2 * D - 6) / ((D - 1) * (D + 2)) := by
        dsimp only [N0, N1]; field_simp [hDm1_ne, hDp2_ne, hD_ne]; ring
      rw [hrew]
      exact div_nonneg (by linarith) (by nlinarith)
    have h1_nn : 0 ≤ (D * t) ^ 2 * (1 / N0 + 1 / N1) := by positivity
    have h2_nn : 0 ≤ 2 * (D * t) * ((3 * D / 2 - 2) / N0 - (D / 2) / N1) :=
      mul_nonneg (by positivity) hlin_nn
    linarith
  have hclose : 3 / 2 + ((3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1) / 8 =
      17 / 8 - (16 * D - 18) / (8 * (D - 1) * (D + 2)) := by
    have hDm1_ne : D - 1 ≠ 0 := by linarith
    have hDp2_ne : D + 2 ≠ 0 := by linarith
    have hD_ne : D ≠ 0 := by linarith
    dsimp only [N0, N1]; field_simp [hDm1_ne, hDp2_ne, hD_ne]; ring
  dsimp only [D, W, N0, N1] at hmono hclose ⊢
  linarith

/-- Strict `> 2` constant separation for ALL `m ≥ 4` whenever either state is Clifford-real. -/
theorem twoStateJ_gt_two_of_real {m : ℕ} (hm : 4 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (hreal : ∃ p : PauliIdx m, symPauliNormSq φ₁ p = 1 ∨ symPauliNormSq φ₂ p = 1) :
    2 < twoStateJ φ₁ φ₂ := by
  have h := twoStateJ_ge_seventeen_eighths_of_real (by omega) h1 h2 hreal
  dsimp only at h
  let D : ℝ := (2 : ℝ) ^ m
  have hD_ge16 : (16 : ℝ) ≤ D := by
    have : (16 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  have hgap : (2 : ℝ) < 17 / 8 - (16 * D - 18) / (8 * (D - 1) * (D + 2)) := by
    have hden_pos : 0 < 8 * (D - 1) * (D + 2) := by nlinarith
    have hlt : (16 * D - 18) / (8 * (D - 1) * (D + 2)) < 1 / 8 := by
      rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    linarith
  dsimp only [D] at hgap
  linarith

/-- **Theorem 17.4(d) — Unconditional `17 / 8 = 2.125 > 2` Constant-Gap Theorem for Stabilizer-Sliced Pairs (`ALL m ≥ 2`)**:
    Whenever EITHER `φ₁` or `φ₂` has ANY non-identity stabilizer symmetry (`∃ q ≠ 0, c_q² = 1`),
      `17 / 8 - (12 D - 17) / (8 (D² - 2)) ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_seventeen_eighths_of_stabilizer {m : ℕ} (hm : 2 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (hstab : ∃ q : PauliIdx m, q ≠ 0 ∧
      ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 = 1 ∨ (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 = 1)) :
    let D : ℝ := (2 : ℝ) ^ m
    17 / 8 - (12 * D - 17) / (8 * (D ^ 2 - 2)) ≤ twoStateJ φ₁ φ₂ := by
  intro D
  have hD_ge4 : (4 : ℝ) ≤ D := by
    have : (4 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  obtain ⟨q, hq_ne, hq_one⟩ := hstab
  have hbase := twoStateJ_ge_of_hyperplane (by omega) h1 h2 hq_ne
  dsimp only at hbase
  let S : ℝ := ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 +
                (innerProd φ₂ (pauliApply q φ₂)).re ^ 2) / 2
  have hS_ge : (1 / 2 : ℝ) ≤ S := by
    dsimp only [S]
    have hnn1 : 0 ≤ (innerProd φ₁ (pauliApply q φ₁)).re ^ 2 := sq_nonneg _
    have hnn2 : 0 ≤ (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 := sq_nonneg _
    rcases hq_one with h | h <;> linarith
  let t : ℝ := S - 1 / 2
  have ht_nn : 0 ≤ t := by dsimp only [t]; linarith
  let N0 : ℝ := D ^ 2 / 2 - 1
  let N1 : ℝ := D ^ 2 / 2
  have hN0_pos : 0 < N0 := by dsimp only [N0]; nlinarith
  have hN1_pos : 0 < N1 := by dsimp only [N1]; nlinarith
  have hN0_ne : N0 ≠ 0 := ne_of_gt hN0_pos
  have hN1_ne : N1 ≠ 0 := ne_of_gt hN1_pos
  have hmono : (3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1 ≤
      (D - 2 + D * S) ^ 2 / N0 + (D - D * S) ^ 2 / N1 := by
    have hS_eq : S = 1 / 2 + t := by dsimp only [t]; ring
    rw [hS_eq]
    have hdiff : ((D - 2 + D * (1 / 2 + t)) ^ 2 / N0 + (D - D * (1 / 2 + t)) ^ 2 / N1) -
        ((3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1) =
        (D * t) ^ 2 * (1 / N0 + 1 / N1) +
        2 * (D * t) * ((3 * D / 2 - 2) / N0 - (D / 2) / N1) := by
      field_simp [hN0_ne, hN1_ne]; ring
    have hlin_nn : 0 ≤ (3 * D / 2 - 2) / N0 - (D / 2) / N1 := by
      have hD2m2_ne : D ^ 2 - 2 ≠ 0 := by nlinarith
      have hD_ne : D ≠ 0 := by linarith
      have hrew : (3 * D / 2 - 2) / N0 - (D / 2) / N1 = (2 * (D - 1) ^ 2) / (D * (D ^ 2 - 2)) := by
        dsimp only [N0, N1]; field_simp [hD2m2_ne, hD_ne]; ring
      rw [hrew]
      exact div_nonneg (by positivity) (by nlinarith)
    have h1_nn : 0 ≤ (D * t) ^ 2 * (1 / N0 + 1 / N1) := by positivity
    have h2_nn : 0 ≤ 2 * (D * t) * ((3 * D / 2 - 2) / N0 - (D / 2) / N1) :=
      mul_nonneg (by positivity) hlin_nn
    linarith
  have hclose : 3 / 2 + ((3 * D / 2 - 2) ^ 2 / N0 + (D / 2) ^ 2 / N1) / 8 =
      17 / 8 - (12 * D - 17) / (8 * (D ^ 2 - 2)) := by
    have hD2m2_ne : D ^ 2 - 2 ≠ 0 := by nlinarith
    have hD_ne : D ≠ 0 := by linarith
    dsimp only [N0, N1]; field_simp [hD2m2_ne, hD_ne]; ring
  dsimp only [D, S, N0, N1] at hmono hclose ⊢
  linarith

/-- Strict `> 2` constant separation for ALL `m ≥ 4` whenever either state has any stabilizer symmetry. -/
theorem twoStateJ_gt_two_of_stabilizer {m : ℕ} (hm : 4 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (hstab : ∃ q : PauliIdx m, q ≠ 0 ∧
      ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 = 1 ∨ (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 = 1)) :
    2 < twoStateJ φ₁ φ₂ := by
  have h := twoStateJ_ge_seventeen_eighths_of_stabilizer (by omega) h1 h2 hstab
  dsimp only at h
  let D : ℝ := (2 : ℝ) ^ m
  have hD_ge16 : (16 : ℝ) ≤ D := by
    have : (16 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  have hgap : (2 : ℝ) < 17 / 8 - (12 * D - 17) / (8 * (D ^ 2 - 2)) := by
    have hden_pos : 0 < 8 * (D ^ 2 - 2) := by nlinarith
    have hlt : (12 * D - 17) / (8 * (D ^ 2 - 2)) < 1 / 8 := by
      rw [div_lt_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 8)]
      nlinarith
    linarith
  linarith

end AsymptoticPauliSlicing

-- Re-export main Stage 17 theorems at `MultiQubitMUB` root namespace for clean Audit access.
export AsymptoticPauliSlicing (
  pauliOverlap4
  pauliCrossOverlap4
  pauliCrossPhaseTerm
  pauliSupportOverlap
  twoStateJ
  slice0
  slice1
  pauliCrossOverlap4_eq_pauliOverlap4
  pauliOverlap4_eq_one_add_supportOverlap
  twoStateJ_ge_two_sub_inv_add_overlap
  pauliOverlap4_eq_sum_symPauliNormSq
  twoStateJ_eq_dual_symPauli
  pauliMoment4_slicing_identity
  exists_clifford_to_Z0
  pauliMoment4_ge_twoStateJ_universal
  sum_pauliSq_hyperplane
  sum_pauliSq_quadric
  twoStateJ_ge_of_hyperplane
  twoStateJ_ge_of_quadric
  twoStateJ_ge_seventeen_eighths_of_real
  twoStateJ_gt_two_of_real
  twoStateJ_ge_seventeen_eighths_of_stabilizer
  twoStateJ_gt_two_of_stabilizer
)

end MultiQubitMUB

