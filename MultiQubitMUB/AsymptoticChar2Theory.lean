import MultiQubitMUB.AsymptoticBarriers

/-!
# General-`n` Characteristic-2 Gowers-`U³` Decomposition, Complex-Symmetric Duality,
  3B Quartic Trace Sandwich, and Universal `O^ε(4m - 2, 2)` `R_{4m}`-Ideal Projection

Formalizes five groups of unconditional general-`n` / general-`m` pure-theory theorems from
Stages 15–16 (zero `sorry`, zero `native_decide`, standard three Lean axioms
`[propext, Classical.choice, Quot.sound]` only, zero edits to upstream modules):

1. **Exact Characteristic-2 Gowers-`U³(𝔽₂ⁿ)` Box-Sum Decomposition & Real-State Floor (ALL `n`)**:
   - `gowersBox_im_zero`: the quartic Gowers box `∑ x, ψ x * star (ψ (x+a)) * star (ψ (x+u)) * ψ (x+a+u)`
     is automatically REAL in characteristic 2.
   - `pauliMoment4_eq_gowersBox_sum`: `pauliMoment4 n ψ = 2ⁿ * ∑ a, ∑ u, (gowersBox ψ a u)²`.
   - `pauliMoment4_sub_welch_eq_gowers`: exact positive-definite 4-term Welch-surplus decomposition
     `Fₙ(ψ) - 2d/(d+1) = E_{r0} + E_{ra} + E_K + E_H`.
   - `pauliMoment4_real_state_ge`: every real unit state satisfies the sharp bound
     `pauliMoment4 n ψ ≥ 3 d / (d + 2)` (`→ 3`).

2. **Exact Characteristic-2 Individual-Coset Energy Floor Theorem (ALL `n`)**:
   - `indivCosetAbsEnergy_eq`: `S_indiv,Abs(ψ) = 4 d (∑_a r_a² - 3 r_0² + 2 ∑_x p_x⁴)`.
   - `indivCosetReEnergy_eq`: `S_indiv,Re(ψ) = 2 d ∑_a r_a² + 2 E_K - 8 d r_0² + 8 d ∑_x p_x⁴ - 2 d |∑_x ψ_x⁴|²`.
   - `indivCosetReEnergy_ge`: unconditional floor `S_indiv,Re(ψ) ≥ 2 d ((1 - r_0)² / (d - 1) - 4 r_0²)`.
   - `indivCosetReEnergy_ge_welch_floor`: at Welch IPR `r_0 = 2 / (d + 1)`,
     `S_indiv,Re(ψ) ≥ 2 d (d - 17) / (d + 1)²` (failing at `n = 3, d = 8` where `d - 17 = -9`,
     strictly positive for all `n ≥ 5`, and `→ 2`).

3. **Complex-Symmetric `Σ = |ψ⟩⟨ψ*|` Parseval Duality, Rank-1 Identity & Takagi Flatness Bound (ALL `n`)**:
   - `symPauliExpect_eq_zero_of_antisym`: `⟨ψ* | P_p | ψ⟩ = 0` for every antisymmetric Pauli (`Q₀(p) ≠ 0`).
   - `symPauliNormSq_eq_sympWHT`: `|⟨ψ* | P_p | ψ⟩|² = (1/d) ∑_q (-1)^{ω(p,q) + Q₀(q)} c_q(ψ)²`.
   - `sum_symPauliNormSq_eq_dim`: `∑_{Q₀(p)=0} |⟨ψ* | P_p | ψ⟩|² = d`.
   - `sum_symPauliNormSq_sub_ideal_sq`: `∑_{Q₀(p)=0} (|⟨ψ* | P_p | ψ⟩|² - 2/(d+1))² = Fₙ(ψ) - 2d/(d+1)`.
   - `symPauliExpect_sq_sum_eq`: `∑_{Q₀(p)=0} (⟨ψ* | P_p | ψ⟩)² = d · (⟨ψ* | ψ⟩)²` (`Σ² = c̃₀ Σ`).
   - `pauliMoment4_sub_welch_ge_symPauliAlpha`: `4 d / (d + 1) * (1 - α̃ₙ(ψ)) ≤ Fₙ(ψ) - 2 d / (d + 1)`.

4. **Exact 3B Symplectic Autocorrelation Identity & Quartic Trace Sandwich (ALL `n ≥ 1`)**:
   - `signMat_sq_eq_pauliExpand`: `S(σ)² = (d² - 1) I + ∑_{r ≠ 0} A_r(σ) P_r`.
   - `matTr_signMat_cube_eq_autocorr`: `(Tr(S(σ)³)).re = d ∑_{r ≠ 0} σ_r A_r(σ)`.
   - `matTr_signMat_fourth_eq_autocorr`: `(Tr(S(σ)⁴)).re = d ((d² - 1)² + ∑_{r ≠ 0} A_r(σ)²)`.
   - `pauliAlpha_pow_four_le_signMat_fourth` and `signMat_fourth_le_sq_of_alpha_bound`:
     exact sandwich `(αₙ*)⁴ ≤ max_σ Tr(S(σ)⁴) / T₂² ≤ (αₙ*)²`.

5. **Stage 15 Universal `O^ε(4m - 2, 2)` `R_{4m}`-Ideal Projection, Stabilizer Identity,
   `C₂(4m, 2r) > 0` Sign-Flip (`t ≥ 16`), and Fermat Two-Squares `ℤ₄`-Rigidity**:
   - `qChuVandermonde_telescoping`: universal `q = 2` Chu–Vandermonde identity for ALL `ν, a, d`.
   - `orthProjCoeff_bidiagonal_recurrence`: exact Witt upper-bidiagonal annihilation (`M₁ Q = 0`).
   - `orthProjCoeff_sum_eq_stabilizer_ratio` and `orthProjCoeff_sum_nonneg`:
     exact stabilizer evaluation `∑_{j=0}^ν c_j(s, ε, d) = ∏_{i=0}^{ν-1} (d - 2ⁱ) / (d + 2^{2s-2-i}) ≥ 0`
     for all `s ≥ 1`, `ε ∈ {1, -1}`, and `d = 2ⁿ`.
   - `c2_cancellation_pos_ge_16`: exact `d⁻²` coefficient `C₂(4m, 2r) > 0` for ALL `m ≥ 4` (`t = 4m ≥ 16`)
     and ALL `1 ≤ r ≤ 2m - 1`.
   - `int_sq_add_sq_eq_pow_four`: Fermat two-squares descent `R² + I² = 4ᵐ → (R = ±2ᵐ ∧ I = 0) ∨ (R = 0 ∧ I = ±2ᵐ)`.
-/

namespace MultiQubitMUB

open scoped Classical
open FourQubitCD
open GeneralContextualityLift
open AsymptoticContextuality
open AsymptoticBarriers

namespace AsymptoticChar2Theory

/-! ### Part 1: Characteristic-2 Gowers-`U³(𝔽₂ⁿ)` Box-Sum Decomposition & Real-State Floor -/

/-- Computational-basis Born probability `p_x = |ψ_x|²`. -/
noncomputable def probDist {n : ℕ} (ψ : QState n) (x : F2 n) : ℝ :=
  Complex.normSq (ψ x)

/-- Probability autocorrelation `r_a = ∑_x p_x p_{x + a}`. -/
noncomputable def probAutocorr {n : ℕ} (ψ : QState n) (a : F2 n) : ℝ :=
  ∑ x : F2 n, probDist ψ x * probDist ψ (x + a)

/-- Complex-valued characteristic-2 Gowers box sum
    `∑_x ψ_x ψ_{x+a}* ψ_{x+u}* ψ_{x+a+u}`. -/
def gowersBoxC {n : ℕ} (ψ : QState n) (a u : F2 n) : ℂ :=
  ∑ x : F2 n, ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)

/-- Real characteristic-2 Gowers box sum `H(a, u) = Re(gowersBoxC ψ a u)`. -/
def gowersBox {n : ℕ} (ψ : QState n) (a u : F2 n) : ℝ :=
  (gowersBoxC ψ a u).re

/-- Characteristic-2 squared-amplitude overlap `K(a) = Re(∑_x ψ_x² (ψ_{x+a}*)²) = H(a, a)`. -/
def sqOverlap {n : ℕ} (ψ : QState n) (a : F2 n) : ℝ :=
  gowersBox ψ a a

/-- **Characteristic-2 Reality of Gowers Boxes (ALL `n`)**:
    Because `x ↦ x + a` is an involution in `𝔽₂ⁿ`, `gowersBoxC ψ a u` is self-conjugate,
    so its imaginary part vanishes identically. -/
theorem gowersBox_im_zero {n : ℕ} (ψ : QState n) (a u : F2 n) :
    (gowersBoxC ψ a u).im = 0 := by
  have hconj : star (gowersBoxC ψ a u) = gowersBoxC ψ a u := by
    simp only [gowersBoxC, star_sum, star_mul, star_star]
    refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
    have h1 : x + a + a = x := f2_add_cancel_right x a
    have h2 : x + a + u + a = x + u := by
      calc x + a + u + a = (x + u) + (a + a) := by abel
        _ = x + u := by rw [f2_add_self, add_zero]
    change star (ψ (x + a + u)) * (ψ (x + u) * (ψ (x + a) * star (ψ x))) =
      ψ (x + a) * star (ψ (x + a + a)) * star (ψ (x + a + u)) * ψ (x + a + a + u)
    rw [h1]
    ring
  have him : -(gowersBoxC ψ a u).im = (gowersBoxC ψ a u).im := by
    have := congr_arg Complex.im hconj
    simpa [Complex.star_def] using this
  linarith

lemma gowersBoxC_eq_ofReal {n : ℕ} (ψ : QState n) (a u : F2 n) :
    gowersBoxC ψ a u = (gowersBox ψ a u : ℂ) := by
  apply Complex.ext
  · simp [gowersBox]
  · simp [gowersBox_im_zero]

lemma gowersBox_zero_right {n : ℕ} (ψ : QState n) (a : F2 n) :
    gowersBox ψ a 0 = probAutocorr ψ a := by
  have hC : gowersBoxC ψ a 0 = (probAutocorr ψ a : ℂ) := by
    simp only [gowersBoxC, probAutocorr, probDist, add_zero, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ψ x * star (ψ x) = (Complex.normSq (ψ x) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hxa : ψ (x + a) * star (ψ (x + a)) = (Complex.normSq (ψ (x + a)) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    calc ψ x * star (ψ (x + a)) * star (ψ x) * ψ (x + a)
        = (ψ x * star (ψ x)) * (ψ (x + a) * star (ψ (x + a))) := by ring
      _ = _ := by rw [hx, hxa]
  rw [gowersBox, hC, Complex.ofReal_re]

lemma gowersBox_zero_left {n : ℕ} (ψ : QState n) (u : F2 n) :
    gowersBox ψ 0 u = probAutocorr ψ u := by
  have hC : gowersBoxC ψ 0 u = (probAutocorr ψ u : ℂ) := by
    simp only [gowersBoxC, probAutocorr, probDist, add_zero, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ψ x * star (ψ x) = (Complex.normSq (ψ x) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hxu : ψ (x + u) * star (ψ (x + u)) = (Complex.normSq (ψ (x + u)) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    calc ψ x * star (ψ x) * star (ψ (x + u)) * ψ (x + u)
        = (ψ x * star (ψ x)) * (ψ (x + u) * star (ψ (x + u))) := by ring
      _ = _ := by rw [hx, hxu]
  rw [gowersBox, hC, Complex.ofReal_re]

lemma sqOverlap_eq_re_sum_sq {n : ℕ} (ψ : QState n) (a : F2 n) :
    sqOverlap ψ a = (∑ x : F2 n, (ψ x) ^ 2 * (star (ψ (x + a))) ^ 2).re := by
  simp only [sqOverlap, gowersBox, gowersBoxC]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [f2_add_cancel_right]; ring

lemma sum_probAutocorr_eq_one {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    ∑ a : F2 n, probAutocorr ψ a = 1 := by
  have hsum_p : ∑ x : F2 n, probDist ψ x = 1 := by
    have h := innerProd_self_re ψ
    rw [hunit, Complex.one_re] at h
    simpa [probDist] using h.symm
  simp only [probAutocorr]
  rw [Finset.sum_comm]
  have hinner : ∀ x : F2 n, ∑ a : F2 n, probDist ψ x * probDist ψ (x + a) = probDist ψ x := fun x => by
    rw [← Finset.mul_sum]
    have hsh : ∑ a : F2 n, probDist ψ (x + a) = ∑ y : F2 n, probDist ψ y :=
      Fintype.sum_equiv (Equiv.addLeft x) _ _ fun _ => rfl
    rw [hsh, hsum_p, mul_one]
  simp_rw [hinner]
  exact hsum_p

/-- Helper: Walsh–Hadamard Parseval on `𝔽₂ⁿ`:
    `∑_u (∑_b (-1)^{b·u} f b)² = 2ⁿ * ∑_b (f b)²`. -/
private lemma f2_wht_parseval {n : ℕ} (f : F2 n → ℝ) :
    ∑ u : F2 n, (∑ b : F2 n, (chi b u : ℝ) * f b) ^ 2 = (2 : ℝ) ^ n * ∑ b : F2 n, (f b) ^ 2 := by
  calc ∑ u : F2 n, (∑ b : F2 n, (chi b u : ℝ) * f b) ^ 2
      = ∑ u : F2 n, ∑ b : F2 n, ∑ b' : F2 n, (chi (b + b') u : ℝ) * (f b * f b') := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [chi_add_left]; push_cast; ring
    _ = ∑ b : F2 n, ∑ b' : F2 n, (∑ u : F2 n, (chi (b + b') u : ℝ)) * (f b * f b') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => (Finset.sum_mul ..).symm
    _ = ∑ b : F2 n, ∑ b' : F2 n, (if b = b' then (2 : ℝ) ^ n else 0) * (f b * f b') := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        congr 1
        have hsc : ∑ u : F2 n, (chi (b + b') u : ℝ) = ((∑ u : F2 n, chi u (b + b') : ℤ) : ℝ) := by
          rw [Int.cast_sum]; refine Finset.sum_congr rfl fun u _ => by rw [chi_comm]
        rw [hsc, sum_chi]
        have hiff : b + b' = 0 ↔ b = b' := by
          constructor
          · intro h; have := congr_arg (· + b') h; simpa [f2_add_cancel_right] using this
          · intro h; rw [h, f2_add_self]
        by_cases h : b = b'
        · subst h; simp [f2_add_self]
        · have hne : b + b' ≠ 0 := fun hc => h (hiff.mp hc)
          simp [h, hne]
    _ = (2 : ℝ) ^ n * ∑ b : F2 n, (f b) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single b]
        · simp [sq]
        · intro b' _ hb'; simp [hb'.symm]
        · intro h; exact absurd (Finset.mem_univ b) h

/-- Exact row WHT of squared Pauli expectations:
    `∑_b (-1)^{b·u} |⟨ψ | P_{a, b} | ψ⟩|² = 2ⁿ * gowersBox ψ a u`. -/
lemma sum_chi_pauliExpect_normSq {n : ℕ} (ψ : QState n) (a u : F2 n) :
    ∑ b : F2 n, (chi b u : ℝ) * Complex.normSq (innerProd ψ (pauliApply (a, b) ψ)) =
      (2 : ℝ) ^ n * gowersBox ψ a u := by
  have hC : ((∑ b : F2 n, (chi b u : ℝ) * Complex.normSq (innerProd ψ (pauliApply (a, b) ψ)) : ℝ) : ℂ) =
      (((2 : ℝ) ^ n * gowersBox ψ a u : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, ← gowersBoxC_eq_ofReal]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    have hterm : ∀ b : F2 n,
        (Complex.normSq (innerProd ψ (pauliApply (a, b) ψ)) : ℂ) =
          ∑ x : F2 n, ∑ y : F2 n,
            (chi b (x + y) : ℂ) * (star (ψ x) * ψ (x + a) * ψ y * star (ψ (y + a))) := fun b => by
      rw [← Complex.mul_conj]
      simp only [innerProd, pauliApply, map_sum, map_mul]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hph : pauliPh (a, b) * (starRingEnd ℂ) (pauliPh (a, b)) = 1 := by
        rw [mul_comm, ← Complex.star_def, pauliPh_mul_star]
      have hchi : (starRingEnd ℂ) (chi b y : ℂ) = (chi b y : ℂ) := by simp
      rw [hchi, chi_add_right]
      push_cast
      calc star (ψ x) * (pauliPh (a, b) * (chi b x : ℂ) * ψ (x + a)) *
            ((starRingEnd ℂ) (star (ψ y)) *
              ((starRingEnd ℂ) (pauliPh (a, b)) * (chi b y : ℂ) * (starRingEnd ℂ) (ψ (y + a))))
          = (pauliPh (a, b) * (starRingEnd ℂ) (pauliPh (a, b))) *
              ((chi b x : ℂ) * (chi b y : ℂ)) *
              (star (ψ x) * ψ (x + a) * ψ y * star (ψ (y + a))) := by
            simp only [Complex.star_def, Complex.conj_conj]; ring
        _ = _ := by rw [hph, one_mul]
    simp_rw [hterm]
    calc ∑ b : F2 n, ((chi b u : ℝ) : ℂ) * ∑ x : F2 n, ∑ y : F2 n,
            (chi b (x + y) : ℂ) * (star (ψ x) * ψ (x + a) * ψ y * star (ψ (y + a)))
        = ∑ x : F2 n, ∑ y : F2 n,
            (∑ b : F2 n, (chi b (x + y + u) : ℂ)) *
              (star (ψ x) * ψ (x + a) * ψ y * star (ψ (y + a))) := by
          conv_lhs =>
            arg 2; ext b
            rw [Finset.mul_sum]
            arg 2; ext x
            rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [chi_add_right b (x + y) u]; push_cast; ring
      _ = ∑ x : F2 n, ∑ y : F2 n,
            (if y = x + u then (2 : ℂ) ^ n else 0) *
              (star (ψ x) * ψ (x + a) * ψ y * star (ψ (y + a))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          congr 1
          have hsc : ∑ b : F2 n, (chi b (x + y + u) : ℂ) =
              ((∑ b : F2 n, chi b (x + y + u) : ℤ) : ℂ) := by rw [Int.cast_sum]
          rw [hsc, sum_chi]
          have hiff : x + y + u = 0 ↔ y = x + u := by
            constructor
            · intro h
              have h1 := congr_arg (· + (x + u)) h
              have h2 : (x + y + u) + (x + u) = y := by
                calc (x + y + u) + (x + u) = y + (x + x) + (u + u) := by abel
                  _ = y := by rw [f2_add_self, f2_add_self, add_zero, add_zero]
              simpa [h2] using h1
            · intro h; subst h
              calc x + (x + u) + u = (x + x) + (u + u) := by abel
                _ = 0 := by rw [f2_add_self, f2_add_self, add_zero]
          simp only [hiff]; split_ifs <;> simp
      _ = (2 : ℂ) ^ n * gowersBoxC ψ a u := by
          simp only [gowersBoxC, Finset.mul_sum]
          refine Fintype.sum_equiv (Equiv.addRight u) _ _ fun x => ?_
          rw [Finset.sum_eq_single (x + u)]
          · have hxu : x + u + u = x := f2_add_cancel_right x u
            simp only [↓reduceIte]
            change (2 : ℂ) ^ n * (star (ψ x) * ψ (x + a) * ψ (x + u) * star (ψ (x + u + a))) =
              (2 : ℂ) ^ n * (ψ (x + u) * star (ψ (x + u + a)) * star (ψ (x + u + u)) * ψ (x + u + a + u))
            rw [hxu]
            have h4 : x + u + a + u = x + a := by
              calc x + u + a + u = x + a + (u + u) := by abel
                _ = x + a := by rw [f2_add_self, add_zero]
            rw [h4]; ring
          · intro y _ hy; simp [hy]
          · intro h; exact absurd (Finset.mem_univ _) h
  exact Complex.ofReal_injective hC

/-- **Exact Characteristic-2 Gowers-`U³(𝔽₂ⁿ)` Identity (ALL `n : ℕ`)**:
    For EVERY `n`-qubit state `ψ`,
      `pauliMoment4 n ψ = 2ⁿ * ∑ a : F2 n, ∑ u : F2 n, (gowersBox ψ a u)²`. -/
theorem pauliMoment4_eq_gowersBox_sum {n : ℕ} (ψ : QState n) :
    pauliMoment4 n ψ = (2 : ℝ) ^ n * ∑ a : F2 n, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  have hrow : ∀ a : F2 n,
      ∑ b : F2 n, (Complex.normSq (innerProd ψ (pauliApply (a, b) ψ))) ^ 2 =
        d * ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := fun a => by
    have hp := f2_wht_parseval (fun b => Complex.normSq (innerProd ψ (pauliApply (a, b) ψ)))
    have hlin : ∑ u : F2 n, (∑ b : F2 n, (chi b u : ℝ) *
          Complex.normSq (innerProd ψ (pauliApply (a, b) ψ))) ^ 2 =
        d ^ 2 * ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [sum_chi_pauliExpect_normSq ψ a u]; simp only [d]; ring
    rw [hlin] at hp
    have hcancel : d * (∑ b : F2 n, (Complex.normSq (innerProd ψ (pauliApply (a, b) ψ))) ^ 2) =
        d * (d * ∑ u : F2 n, (gowersBox ψ a u) ^ 2) := by
      have : d * (d * ∑ u : F2 n, (gowersBox ψ a u) ^ 2) = d ^ 2 * ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := by ring
      rw [this, ← hp]
    exact mul_left_cancel₀ hd_ne hcancel
  simp only [pauliMoment4, Fintype.sum_prod_type]
  simp_rw [hrow, ← Finset.mul_sum]
  rfl

/-- **Exact Positive-Definite 3A Welch-Surplus Decomposition (ALL `n ≥ 1`)**:
    For EVERY `n ≥ 1` and EVERY unit state `ψ : QState n` (`d = 2ⁿ`),
      `pauliMoment4 n ψ - 2 d / (d + 1) =`
        `(d (d + 1) / (d - 1)) * (r₀ - 2 / (d + 1))²`
        `+ 2 d * ∑_{a ≠ 0} (r_a - (1 - r₀) / (d - 1))²`
        `+ d * ∑_{a ≠ 0} K(a)²`
        `+ d * ∑_{a ≠ 0} ∑_{u ≠ 0, u ≠ a} H(a, u)²`. -/
theorem pauliMoment4_sub_welch_eq_gowers {n : ℕ} (hn : 1 ≤ n) {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let S : Finset (F2 n) := Finset.univ.erase 0
    let r0 : ℝ := probAutocorr ψ 0
    pauliMoment4 n ψ - 2 * d / (d + 1) =
      (d * (d + 1) / (d - 1)) * (r0 - 2 / (d + 1)) ^ 2 +
      2 * d * ∑ a ∈ S, (probAutocorr ψ a - (1 - r0) / (d - 1)) ^ 2 +
      d * ∑ a ∈ S, (sqOverlap ψ a) ^ 2 +
      d * ∑ a ∈ S, ∑ u ∈ S.erase a, (gowersBox ψ a u) ^ 2 := by
  intro d S r0
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hd1_ne : d + 1 ≠ 0 := by linarith
  have hdm1_ne : d - 1 ≠ 0 := by linarith
  have hcardS : (S.card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hsum_ra : ∑ a ∈ S, probAutocorr ψ a = 1 - r0 := by
    have h := sum_probAutocorr_eq_one hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))] at h
    linarith
  -- Split `∑_a ∑_u H(a, u)²` into `(0,0)`, `(0, u≠0)`, `(a≠0, 0)`, `(a≠0, a)`, `(a≠0, u≠0, u≠a)`!
  have hsplit : ∑ a : F2 n, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 =
      r0 ^ 2 + 2 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2 + ∑ a ∈ S, (sqOverlap ψ a) ^ 2 +
      ∑ a ∈ S, ∑ u ∈ S.erase a, (gowersBox ψ a u) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    have ha0 : ∑ u : F2 n, (gowersBox ψ 0 u) ^ 2 = r0 ^ 2 + ∑ u ∈ S, (probAutocorr ψ u) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), gowersBox_zero_left]
      congr 1
      exact Finset.sum_congr rfl fun u _ => by rw [gowersBox_zero_left]
    have hanz : ∑ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 =
        ∑ a ∈ S, (probAutocorr ψ a) ^ 2 + ∑ a ∈ S, (sqOverlap ψ a) ^ 2 +
        ∑ a ∈ S, ∑ u ∈ S.erase a, (gowersBox ψ a u) ^ 2 := by
      have hterm : ∀ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 =
          (probAutocorr ψ a) ^ 2 + (sqOverlap ψ a) ^ 2 +
          ∑ u ∈ S.erase a, (gowersBox ψ a u) ^ 2 := fun a ha => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
            ← Finset.add_sum_erase _ _ ha, gowersBox_zero_right]
        simp only [sqOverlap]; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
    change ∑ u : F2 n, (gowersBox ψ 0 u) ^ 2 + ∑ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 = _
    rw [ha0, hanz]; ring
  have hvar : ∑ a ∈ S, (probAutocorr ψ a - (1 - r0) / (d - 1)) ^ 2 =
      ∑ a ∈ S, (probAutocorr ψ a) ^ 2 - (1 - r0) ^ 2 / (d - 1) := by
    have hexp : ∑ a ∈ S, (probAutocorr ψ a - (1 - r0) / (d - 1)) ^ 2 =
        ∑ a ∈ S, (probAutocorr ψ a) ^ 2 -
        2 * ((1 - r0) / (d - 1)) * ∑ a ∈ S, probAutocorr ψ a +
        (S.card : ℝ) * ((1 - r0) / (d - 1)) ^ 2 := by
      have ht : ∀ a ∈ S, (probAutocorr ψ a - (1 - r0) / (d - 1)) ^ 2 =
          (probAutocorr ψ a) ^ 2 - 2 * ((1 - r0) / (d - 1)) * probAutocorr ψ a +
          ((1 - r0) / (d - 1)) ^ 2 := fun a _ => by ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hexp, hsum_ra, hcardS]
    field_simp [hdm1_ne]; ring
  rw [pauliMoment4_eq_gowersBox_sum, hsplit, hvar]
  field_simp [hd1_ne, hdm1_ne]; ring

/-- **Sharp General-`n` Real-State Lower Bound (`Fₙ(ψ) ≥ 3 d / (d + 2) → 3`, ALL `n ≥ 1`)**:
    For every real unit state (`(ψ x).im = 0`), `sqOverlap ψ a = probAutocorr ψ a`, immediately
    forcing `pauliMoment4 n ψ ≥ 3 d / (d + 2)` (tight at `n = 1` with `3/2` and `n = 2` with `2`). -/
theorem pauliMoment4_real_state_ge {n : ℕ} (hn : 1 ≤ n) {ψ : QState n}
    (hunit : IsUnitState ψ) (hreal : ∀ x : F2 n, (ψ x).im = 0) :
    3 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 2) ≤ pauliMoment4 n ψ := by
  let d : ℝ := (2 : ℝ) ^ n
  let S : Finset (F2 n) := Finset.univ.erase 0
  let r0 : ℝ := probAutocorr ψ 0
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hdm1_pos : 0 < d - 1 := by linarith
  have hdm1_ne : d - 1 ≠ 0 := ne_of_gt hdm1_pos
  have hd2_pos : 0 < d + 2 := by linarith
  have hcardS : (S.card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hK_eq_r : ∀ a : F2 n, sqOverlap ψ a = probAutocorr ψ a := fun a => by
    rw [sqOverlap_eq_re_sum_sq]
    have hC : ∑ x : F2 n, (ψ x) ^ 2 * (star (ψ (x + a))) ^ 2 = (probAutocorr ψ a : ℂ) := by
      simp only [probAutocorr, probDist, Complex.ofReal_sum, Complex.ofReal_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx : ψ x = ((ψ x).re : ℂ) := Complex.ext rfl (by simp [hreal x])
      have hxa : ψ (x + a) = ((ψ (x + a)).re : ℂ) := Complex.ext rfl (by simp [hreal (x + a)])
      rw [hx, hxa]
      simp [Complex.normSq_apply, sq]
    rw [hC, Complex.ofReal_re]
  have hsum_ra : ∑ a ∈ S, probAutocorr ψ a = 1 - r0 := by
    have h := sum_probAutocorr_eq_one hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))] at h
    linarith
  have hcs : (1 - r0) ^ 2 / (d - 1) ≤ ∑ a ∈ S, (probAutocorr ψ a) ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => probAutocorr ψ a)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcardS, hsum_ra] at hcs0
    exact (div_le_iff₀ hdm1_pos).mpr (by linarith)
  have hF_ge : d * (r0 ^ 2 + 3 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2) ≤ pauliMoment4 n ψ := by
    rw [pauliMoment4_eq_gowersBox_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    have ha0 : ∑ u : F2 n, (gowersBox ψ 0 u) ^ 2 = r0 ^ 2 + ∑ u ∈ S, (probAutocorr ψ u) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), gowersBox_zero_left]
      congr 1; exact Finset.sum_congr rfl fun u _ => by rw [gowersBox_zero_left]
    have hanz : 2 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2 ≤ ∑ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := by
      have ht : ∀ a ∈ S, 2 * (probAutocorr ψ a) ^ 2 ≤ ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := fun a ha => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
            ← Finset.add_sum_erase _ _ ha, gowersBox_zero_right]
        have hsq : (gowersBox ψ a a) ^ 2 = (probAutocorr ψ a) ^ 2 := by rw [← sqOverlap, hK_eq_r a]
        have hnn : 0 ≤ ∑ u ∈ S.erase a, (gowersBox ψ a u) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      calc 2 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2
          = ∑ a ∈ S, 2 * (probAutocorr ψ a) ^ 2 := Finset.mul_sum ..
        _ ≤ ∑ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2 := Finset.sum_le_sum ht
    change r0 ^ 2 + 3 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2 ≤
      ∑ u : F2 n, (gowersBox ψ 0 u) ^ 2 + ∑ a ∈ S, ∑ u : F2 n, (gowersBox ψ a u) ^ 2
    linarith
  have hquad : 3 * d / (d + 2) ≤ d * (r0 ^ 2 + 3 * ((1 - r0) ^ 2 / (d - 1))) := by
    have hdiff : d * (r0 ^ 2 + 3 * ((1 - r0) ^ 2 / (d - 1))) - 3 * d / (d + 2) =
        (d * (d + 2) / (d - 1)) * (r0 - 3 / (d + 2)) ^ 2 := by
      field_simp [hdm1_ne, ne_of_gt hd2_pos]; ring
    have hnn : 0 ≤ (d * (d + 2) / (d - 1)) * (r0 - 3 / (d + 2)) ^ 2 := by positivity
    linarith
  calc 3 * d / (d + 2)
      ≤ d * (r0 ^ 2 + 3 * ((1 - r0) ^ 2 / (d - 1))) := hquad
    _ ≤ d * (r0 ^ 2 + 3 * ∑ a ∈ S, (probAutocorr ψ a) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ pauliMoment4 n ψ := hF_ge

/-! ### Part 2: Exact Characteristic-2 Individual-Coset Energy Floor Theorem (Theorem A) -/

/-- Individual 4-element affine 2-plane coset modulus-squared energy:
    `S_indiv,Abs(ψ) = 4 d * ∑_{a ≠ 0} ∑_{u ≠ 0, u ≠ a} ∑_x |ψ_x ψ_{x+a}* ψ_{x+u}* ψ_{x+a+u}|²`. -/
noncomputable def indivCosetAbsEnergy {n : ℕ} (ψ : QState n) : ℝ :=
  let S : Finset (F2 n) := Finset.univ.erase 0
  4 * (2 : ℝ) ^ n * ∑ a ∈ S, ∑ u ∈ S.erase a,
    ∑ x : F2 n, Complex.normSq (ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u))

/-- Individual 4-element affine 2-plane coset real-part squared energy:
    `S_indiv,Re(ψ) = 4 d * ∑_{a ≠ 0} ∑_{u ≠ 0, u ≠ a} ∑_x (Re(ψ_x ψ_{x+a}* ψ_{x+u}* ψ_{x+a+u}))²`. -/
noncomputable def indivCosetReEnergy {n : ℕ} (ψ : QState n) : ℝ :=
  let S : Finset (F2 n) := Finset.univ.erase 0
  4 * (2 : ℝ) ^ n * ∑ a ∈ S, ∑ u ∈ S.erase a,
    ∑ x : F2 n, ((ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)).re) ^ 2

/-- **Exact Individual-Coset Modulus Energy Identity (ALL `n : ℕ`)**:
    `indivCosetAbsEnergy ψ = 4 d * (∑_a r_a² - 3 r₀² + 2 ∑_x p_x⁴)`. -/
theorem indivCosetAbsEnergy_eq {n : ℕ} (ψ : QState n) :
    indivCosetAbsEnergy ψ =
      4 * (2 : ℝ) ^ n *
        (∑ a : F2 n, (probAutocorr ψ a) ^ 2 - 3 * (probAutocorr ψ 0) ^ 2 +
          2 * ∑ x : F2 n, (probDist ψ x) ^ 4) := by
  let S : Finset (F2 n) := Finset.univ.erase 0
  have hf : ∀ a u x : F2 n,
      Complex.normSq (ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)) =
        probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) := fun a u x => by
    simp only [map_mul, Complex.star_def, Complex.normSq_conj, probDist]
  -- Full unrestricted sum over `(a, u, x)` equals `∑_a r_a²`!
  have hfull : ∑ a : F2 n, ∑ u : F2 n, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
      ∑ a : F2 n, (probAutocorr ψ a) ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [probAutocorr, sq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun u => ?_
    change probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
      probDist ψ x * probDist ψ (x + a) * (probDist ψ (x + u) * probDist ψ (x + u + a))
    have : x + a + u = x + u + a := by abel
    rw [this]; ring
  -- Boundary sums: `a = 0`, `u = 0`, `u = a`, and `a = u = 0`!
  have ha0 : ∑ u : F2 n, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + 0) * probDist ψ (x + u) * probDist ψ (x + 0 + u) =
      (probAutocorr ψ 0) ^ 2 := by
    rw [probAutocorr, sq, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun u => ?_
    change probDist ψ x * probDist ψ (x + 0) * probDist ψ (x + u) * probDist ψ (x + 0 + u) =
      probDist ψ x * probDist ψ (x + 0) * (probDist ψ (x + u) * probDist ψ (x + u + 0))
    simp only [add_zero]; ring
  have hu0 : ∑ a : F2 n, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + a) * probDist ψ (x + 0) * probDist ψ (x + a + 0) =
      (probAutocorr ψ 0) ^ 2 := by
    rw [probAutocorr, sq, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun a => ?_
    change probDist ψ x * probDist ψ (x + a) * probDist ψ (x + 0) * probDist ψ (x + a + 0) =
      probDist ψ x * probDist ψ (x + 0) * (probDist ψ (x + a) * probDist ψ (x + a + 0))
    simp only [add_zero]; ring
  have hua : ∑ a : F2 n, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + a) * probDist ψ (x + a) * probDist ψ (x + a + a) =
      (probAutocorr ψ 0) ^ 2 := by
    rw [probAutocorr, sq, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun a => ?_
    change probDist ψ x * probDist ψ (x + a) * probDist ψ (x + a) * probDist ψ (x + a + a) =
      probDist ψ x * probDist ψ (x + 0) * (probDist ψ (x + a) * probDist ψ (x + a + 0))
    simp only [f2_add_cancel_right, add_zero]; ring
  have h00 : ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + 0) * probDist ψ (x + 0) * probDist ψ (x + 0 + 0) =
      ∑ x : F2 n, (probDist ψ x) ^ 4 := by
    refine Finset.sum_congr rfl fun x _ => by simp only [add_zero]; ring
  -- Decompose `hfull` by peeling `a = 0`, then `u = 0` and `u = a` for `a ∈ S`!
  have hsplit : ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
      ∑ a : F2 n, (probAutocorr ψ a) ^ 2 - 3 * (probAutocorr ψ 0) ^ 2 +
      2 * ∑ x : F2 n, (probDist ψ x) ^ 4 := by
    have h1 := hfull
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), ha0] at h1
    have h2 : ∑ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
        probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
        ∑ a ∈ S, ∑ x : F2 n,
          probDist ψ x * probDist ψ (x + a) * probDist ψ (x + 0) * probDist ψ (x + a + 0) +
        ∑ a ∈ S, ∑ x : F2 n,
          probDist ψ x * probDist ψ (x + a) * probDist ψ (x + a) * probDist ψ (x + a + a) +
        ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
          probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) := by
      have ht : ∀ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
          probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
          (∑ x : F2 n, probDist ψ x * probDist ψ (x + a) * probDist ψ (x + 0) * probDist ψ (x + a + 0)) +
          (∑ x : F2 n, probDist ψ x * probDist ψ (x + a) * probDist ψ (x + a) * probDist ψ (x + a + a)) +
          ∑ u ∈ S.erase a, ∑ x : F2 n,
            probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) := fun a ha => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
            ← Finset.add_sum_erase _ _ ha]; ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hu0' : ∑ a ∈ S, ∑ x : F2 n,
        probDist ψ x * probDist ψ (x + a) * probDist ψ (x + 0) * probDist ψ (x + a + 0) =
        (probAutocorr ψ 0) ^ 2 - ∑ x : F2 n, (probDist ψ x) ^ 4 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), h00] at hu0
      linarith
    have hua' : ∑ a ∈ S, ∑ x : F2 n,
        probDist ψ x * probDist ψ (x + a) * probDist ψ (x + a) * probDist ψ (x + a + a) =
        (probAutocorr ψ 0) ^ 2 - ∑ x : F2 n, (probDist ψ x) ^ 4 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), h00] at hua
      linarith
    change (probAutocorr ψ 0) ^ 2 + ∑ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
      probDist ψ x * probDist ψ (x + a) * probDist ψ (x + u) * probDist ψ (x + a + u) =
      ∑ a : F2 n, (probAutocorr ψ a) ^ 2 at h1
    linarith
  simp only [indivCosetAbsEnergy, hf]
  rw [hsplit]

/-- **Exact Characteristic-2 Individual-Coset Real-Part Energy Identity (Theorem A, ALL `n : ℕ`)**:
    For EVERY `n`-qubit state `ψ`,
      `indivCosetReEnergy ψ = 2 d ∑_a r_a² + 2 d ∑_{a ≠ 0} K(a)² - 8 d r₀² + 8 d ∑_x p_x⁴ - 2 d |∑_x ψ_x⁴|²`. -/
theorem indivCosetReEnergy_eq {n : ℕ} (ψ : QState n) :
    let d : ℝ := (2 : ℝ) ^ n
    let S : Finset (F2 n) := Finset.univ.erase 0
    indivCosetReEnergy ψ =
      2 * d * ∑ a : F2 n, (probAutocorr ψ a) ^ 2 +
      2 * d * ∑ a ∈ S, (sqOverlap ψ a) ^ 2 -
      8 * d * (probAutocorr ψ 0) ^ 2 +
      8 * d * ∑ x : F2 n, (probDist ψ x) ^ 4 -
      2 * d * Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) := by
  intro d S
  let φ : QState n := fun x => (ψ x) ^ 2
  have hre_sq : ∀ z : ℂ, z.re ^ 2 = (1 / 2 : ℝ) * Complex.normSq z + (1 / 2 : ℝ) * (z ^ 2).re := fun z => by
    simp only [Complex.normSq_apply, sq, Complex.mul_re]; ring
  have hsplit_re : indivCosetReEnergy ψ =
      (1 / 2 : ℝ) * indivCosetAbsEnergy ψ +
      2 * d * (∑ a ∈ S, ∑ u ∈ S.erase a,
        ∑ x : F2 n, (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re) := by
    simp only [indivCosetReEnergy, indivCosetAbsEnergy]
    have hsum : ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
          ((ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)).re) ^ 2 =
        (1 / 2 : ℝ) * ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
          Complex.normSq (ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)) +
        (1 / 2 : ℝ) * ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
          (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re := by
      have ht : ∀ a u x : F2 n,
          ((ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)).re) ^ 2 =
          (1 / 2 : ℝ) * Complex.normSq (ψ x * star (ψ (x + a)) * star (ψ (x + u)) * ψ (x + a + u)) +
          (1 / 2 : ℝ) * (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re := fun a u x => by
        rw [hre_sq]
        congr 2; congr 1
        simp only [φ, star_pow]; ring
      simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum]; ring
  -- Now evaluate the exact double-angle sum `∑_{a ∈ S} ∑_{u ∈ S.erase a} ∑_x Re(φ_x φ_{x+a}* φ_{x+u}* φ_{x+a+u})`!
  have hfull_phi : ∑ a : F2 n, ∑ u : F2 n, ∑ x : F2 n,
      (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re =
      ∑ a : F2 n, (sqOverlap ψ a) ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hK_im : (∑ x : F2 n, φ x * star (φ (x + a))).im = 0 := by
      have := gowersBox_im_zero ψ a a
      simp only [gowersBoxC] at this
      have heq : (∑ x : F2 n, φ x * star (φ (x + a))) =
          ∑ x : F2 n, ψ x * star (ψ (x + a)) * star (ψ (x + a)) * ψ (x + a + a) := by
        refine Finset.sum_congr rfl fun x _ => by
          rw [f2_add_cancel_right]; simp only [φ, star_pow]; ring
      rw [heq]; exact this
    have hK_eq : ∑ x : F2 n, φ x * star (φ (x + a)) = (sqOverlap ψ a : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re, sqOverlap_eq_re_sum_sq]
        congr 1; refine Finset.sum_congr rfl fun x _ => by simp only [φ, star_pow]
      · rw [Complex.ofReal_im]; exact hK_im
    have hC : ∑ u : F2 n, ∑ x : F2 n,
          φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u) =
        ((sqOverlap ψ a) ^ 2 : ℂ) := by
      have h1 : ∑ u : F2 n, ∑ x : F2 n,
            φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u) =
          (∑ x : F2 n, φ x * star (φ (x + a))) * (∑ y : F2 n, star (φ y) * φ (y + a)) := by
        rw [Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun u => ?_
        change φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u) =
          φ x * star (φ (x + a)) * (star (φ (x + u)) * φ (x + u + a))
        have : x + a + u = x + u + a := by abel
        rw [this]; ring
      have h2 : ∑ y : F2 n, star (φ y) * φ (y + a) = ∑ x : F2 n, φ x * star (φ (x + a)) := by
        refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun y => ?_
        change star (φ y) * φ (y + a) = φ (y + a) * star (φ (y + a + a))
        rw [f2_add_cancel_right]; ring
      rw [h1, h2, hK_eq]; ring
    have hre := congr_arg Complex.re hC
    rw [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
    simpa only [Complex.re_sum] using hre
  have hphi_a0 : ∑ u : F2 n, ∑ x : F2 n,
      (φ x * star (φ (x + 0)) * star (φ (x + u)) * φ (x + 0 + u)).re =
      (probAutocorr ψ 0) ^ 2 := by
    have hterm : ∀ u x : F2 n,
        (φ x * star (φ (x + 0)) * star (φ (x + u)) * φ (x + 0 + u)).re =
          (probDist ψ x) ^ 2 * (probDist ψ (x + u)) ^ 2 := fun u x => by
      simp only [add_zero, φ]
      have hx : (ψ x) ^ 2 * star ((ψ x) ^ 2) = ((probDist ψ x) ^ 2 : ℂ) := by
        rw [star_pow, show (ψ x) ^ 2 * star (ψ x) ^ 2 = (ψ x * star (ψ x)) ^ 2 by ring,
            Complex.star_def, Complex.mul_conj]; simp [probDist]
      have hxu : (ψ (x + u)) ^ 2 * star ((ψ (x + u)) ^ 2) = ((probDist ψ (x + u)) ^ 2 : ℂ) := by
        rw [star_pow, show (ψ (x + u)) ^ 2 * star (ψ (x + u)) ^ 2 = (ψ (x + u) * star (ψ (x + u))) ^ 2 by ring,
            Complex.star_def, Complex.mul_conj]; simp [probDist]
      have hc : (ψ x) ^ 2 * star ((ψ x) ^ 2) * star ((ψ (x + u)) ^ 2) * (ψ (x + u)) ^ 2 =
          (((probDist ψ x) ^ 2 * (probDist ψ (x + u)) ^ 2 : ℝ) : ℂ) := by
        calc (ψ x) ^ 2 * star ((ψ x) ^ 2) * star ((ψ (x + u)) ^ 2) * (ψ (x + u)) ^ 2
            = ((ψ x) ^ 2 * star ((ψ x) ^ 2)) * ((ψ (x + u)) ^ 2 * star ((ψ (x + u)) ^ 2)) := by ring
          _ = _ := by rw [hx, hxu]; push_cast; rfl
      rw [hc, Complex.ofReal_re]
    simp_rw [hterm]
    rw [probAutocorr, sq, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun u => by
      change probDist ψ x ^ 2 * probDist ψ (x + u) ^ 2 =
        probDist ψ x * probDist ψ (x + 0) * (probDist ψ (x + u) * probDist ψ (x + u + 0))
      simp only [add_zero]; ring
  have hphi_u0 : ∑ a : F2 n, ∑ x : F2 n,
      (φ x * star (φ (x + a)) * star (φ (x + 0)) * φ (x + a + 0)).re =
      (probAutocorr ψ 0) ^ 2 := by
    have heq : ∀ a x : F2 n,
        φ x * star (φ (x + a)) * star (φ (x + 0)) * φ (x + a + 0) =
          φ x * star (φ (x + 0)) * star (φ (x + a)) * φ (x + 0 + a) := fun a x => by
      simp only [add_zero]; ring
    simp_rw [heq]; exact hphi_a0
  have hphi_ua : ∑ a : F2 n, ∑ x : F2 n,
      (φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a)).re =
      Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) := by
    have hC : ∑ a : F2 n, ∑ x : F2 n,
          φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a) =
        (Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) : ℂ) := by
      rw [← Complex.mul_conj, Finset.sum_mul, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun a => ?_
      change φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a) =
        (ψ x) ^ 4 * (starRingEnd ℂ) ((ψ (x + a)) ^ 4)
      simp only [f2_add_cancel_right, φ, Complex.star_def, map_pow]; ring
    have hre := congr_arg Complex.re hC
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    exact hre
  have hphi_00 : ∑ x : F2 n,
      (φ x * star (φ (x + 0)) * star (φ (x + 0)) * φ (x + 0 + 0)).re =
      ∑ x : F2 n, (probDist ψ x) ^ 4 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [add_zero, φ]
    have hx : (ψ x) ^ 2 * star ((ψ x) ^ 2) = ((probDist ψ x) ^ 2 : ℂ) := by
      rw [star_pow, show (ψ x) ^ 2 * star (ψ x) ^ 2 = (ψ x * star (ψ x)) ^ 2 by ring,
          Complex.star_def, Complex.mul_conj]; simp [probDist]
    have hc : (ψ x) ^ 2 * star ((ψ x) ^ 2) * star ((ψ x) ^ 2) * (ψ x) ^ 2 =
        (((probDist ψ x) ^ 4 : ℝ) : ℂ) := by
      calc (ψ x) ^ 2 * star ((ψ x) ^ 2) * star ((ψ x) ^ 2) * (ψ x) ^ 2
          = ((ψ x) ^ 2 * star ((ψ x) ^ 2)) * ((ψ x) ^ 2 * star ((ψ x) ^ 2)) := by ring
        _ = _ := by rw [hx]; push_cast; ring
    rw [hc, Complex.ofReal_re]
  have hphi_inner : ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
      (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re =
      ∑ a ∈ S, (sqOverlap ψ a) ^ 2 - (probAutocorr ψ 0) ^ 2 -
      Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) + 2 * ∑ x : F2 n, (probDist ψ x) ^ 4 := by
    have hK0 : sqOverlap ψ 0 = probAutocorr ψ 0 := gowersBox_zero_right ψ 0
    have h1 := hfull_phi
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), hphi_a0] at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), hK0] at h1
    have h2 : ∑ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
        (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re =
        ∑ a ∈ S, ∑ x : F2 n, (φ x * star (φ (x + a)) * star (φ (x + 0)) * φ (x + a + 0)).re +
        ∑ a ∈ S, ∑ x : F2 n, (φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a)).re +
        ∑ a ∈ S, ∑ u ∈ S.erase a, ∑ x : F2 n,
          (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re := by
      have ht : ∀ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
          (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re =
          (∑ x : F2 n, (φ x * star (φ (x + a)) * star (φ (x + 0)) * φ (x + a + 0)).re) +
          (∑ x : F2 n, (φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a)).re) +
          ∑ u ∈ S.erase a, ∑ x : F2 n,
            (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re := fun a ha => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
            ← Finset.add_sum_erase _ _ ha]; ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hu0' : ∑ a ∈ S, ∑ x : F2 n,
        (φ x * star (φ (x + a)) * star (φ (x + 0)) * φ (x + a + 0)).re =
        (probAutocorr ψ 0) ^ 2 - ∑ x : F2 n, (probDist ψ x) ^ 4 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), hphi_00] at hphi_u0
      linarith
    have hua' : ∑ a ∈ S, ∑ x : F2 n,
        (φ x * star (φ (x + a)) * star (φ (x + a)) * φ (x + a + a)).re =
        Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) - ∑ x : F2 n, (probDist ψ x) ^ 4 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), hphi_00] at hphi_ua
      linarith
    change (probAutocorr ψ 0) ^ 2 + ∑ a ∈ S, ∑ u : F2 n, ∑ x : F2 n,
      (φ x * star (φ (x + a)) * star (φ (x + u)) * φ (x + a + u)).re =
      (probAutocorr ψ 0) ^ 2 + ∑ a ∈ S, (sqOverlap ψ a) ^ 2 at h1
    linarith
  rw [hsplit_re, indivCosetAbsEnergy_eq, hphi_inner]
  ring

/-- **Unconditional Individual-Coset Real-Part Floor (ALL `n ≥ 1`, ZERO Flatness Assumptions)**:
    For EVERY unit state `ψ : QState n` (`d = 2ⁿ`, `r₀ = probAutocorr ψ 0`),
      `2 d * ((1 - r₀)² / (d - 1) - 4 r₀²) ≤ indivCosetReEnergy ψ`. -/
theorem indivCosetReEnergy_ge {n : ℕ} (hn : 1 ≤ n) {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let r0 : ℝ := probAutocorr ψ 0
    2 * d * ((1 - r0) ^ 2 / (d - 1) - 4 * r0 ^ 2) ≤ indivCosetReEnergy ψ := by
  intro d r0
  let S : Finset (F2 n) := Finset.univ.erase 0
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hdm1_pos : 0 < d - 1 := by linarith
  have hcardS : (S.card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hsum_ra : ∑ a ∈ S, probAutocorr ψ a = 1 - r0 := by
    have h := sum_probAutocorr_eq_one hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))] at h
    linarith
  have hcs : (1 - r0) ^ 2 / (d - 1) ≤ ∑ a ∈ S, (probAutocorr ψ a) ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => probAutocorr ψ a)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcardS, hsum_ra] at hcs0
    exact (div_le_iff₀ hdm1_pos).mpr (by linarith)
  have hsum_r2 : r0 ^ 2 + (1 - r0) ^ 2 / (d - 1) ≤ ∑ a : F2 n, (probAutocorr ψ a) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    linarith
  -- Triangle inequality: `|∑_x ψ_x⁴|² ≤ (∑_x |ψ_x|⁴)² = r₀²`!
  have hpsi4_le : Complex.normSq (∑ x : F2 n, (ψ x) ^ 4) ≤ r0 ^ 2 := by
    have hnorm : ‖∑ x : F2 n, (ψ x) ^ 4‖ ≤ r0 := by
      have htri := norm_sum_le (Finset.univ : Finset (F2 n)) (fun x => (ψ x) ^ 4)
      have hterm : ∑ x : F2 n, ‖(ψ x) ^ 4‖ = r0 := by
        simp only [r0, probAutocorr, probDist, add_zero, norm_pow]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hns : Complex.normSq (ψ x) = ‖ψ x‖ ^ 2 := (Complex.normSq_eq_norm_sq (ψ x))
        rw [hns]; ring
      rwa [hterm] at htri
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hEK_nn : 0 ≤ ∑ a ∈ S, (sqOverlap ψ a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp4_nn : 0 ≤ ∑ x : F2 n, (probDist ψ x) ^ 4 := Finset.sum_nonneg fun _ _ => by positivity
  rw [indivCosetReEnergy_eq]
  have hd_nn : 0 ≤ 2 * d := by positivity
  nlinarith

/-- **Characteristic-2 Welch-IPR Coset Floor (`2 d (d - 17) / (d + 1)² → 2`)**:
    At the Welch IPR `r₀ = 2 / (d + 1)`, every unit state satisfies
      `2 d (d - 17) / (d + 1)² ≤ indivCosetReEnergy ψ`,
    which is negative at `n = 3` (`d = 8`, `d - 17 = -9`, allowing Hoggar's `S_indiv,Re = 0`),
    strictly positive for EVERY `n ≥ 5` (`d ≥ 32`), and approaches `2` as `n → ∞`. -/
theorem indivCosetReEnergy_ge_welch_floor {n : ℕ} (hn : 1 ≤ n) {ψ : QState n}
    (hunit : IsUnitState ψ) (hr0 : probAutocorr ψ 0 = 2 / ((2 : ℝ) ^ n + 1)) :
    let d : ℝ := (2 : ℝ) ^ n
    2 * d * (d - 17) / (d + 1) ^ 2 ≤ indivCosetReEnergy ψ := by
  intro d
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hdm1_ne : d - 1 ≠ 0 := by linarith
  have hd1_ne : d + 1 ≠ 0 := by linarith
  have h := indivCosetReEnergy_ge hn hunit
  dsimp only at h
  rw [hr0] at h
  have heq : 2 * d * ((1 - 2 / (d + 1)) ^ 2 / (d - 1) - 4 * (2 / (d + 1)) ^ 2) =
      2 * d * (d - 17) / (d + 1) ^ 2 := by
    field_simp [hdm1_ne, hd1_ne]; ring
  rwa [heq] at h

/-! ### Part 3: Complex-Symmetric `Σ = |ψ⟩⟨ψ*|` Parseval Duality & Takagi Flatness Bound -/

/-- Set of symmetric Pauli indices `{p ∈ 𝔽₂²ⁿ : Q₀(p) = 0}` (cardinality `d (d + 1) / 2`). -/
def symPts (n : ℕ) : Finset (PauliIdx n) :=
  Finset.univ.filter fun p : PauliIdx n => quadForm0 p = 0

/-- Complex-symmetric Pauli expectation `c̃_p(ψ) = ⟨ψ* | P_p | ψ⟩`. -/
def symPauliExpect {n : ℕ} (ψ : QState n) (p : PauliIdx n) : ℂ :=
  innerProd (fun x => star (ψ x)) (pauliApply p ψ)

/-- Squared modulus `w_p(ψ) = |⟨ψ* | P_p | ψ⟩|²`. -/
noncomputable def symPauliNormSq {n : ℕ} (ψ : QState n) (p : PauliIdx n) : ℝ :=
  Complex.normSq (symPauliExpect ψ p)

/-- Complex-symmetric `L₁` sum `∑_{Q₀(p)=0} |⟨ψ* | P_p | ψ⟩|`. -/
noncomputable def symPauliL1 {n : ℕ} (ψ : QState n) : ℝ :=
  ∑ p ∈ symPts n, ‖symPauliExpect ψ p‖

/-- Complex-symmetric flatness ratio `α̃ₙ(ψ) = (1/d) √(2/(d+1)) ∑_{Q₀(p)=0} |⟨ψ* | P_p | ψ⟩|`. -/
noncomputable def symPauliAlpha {n : ℕ} (ψ : QState n) : ℝ :=
  symPauliL1 ψ / ((2 : ℝ) ^ n * Real.sqrt (((2 : ℝ) ^ n + 1) / 2))

lemma symPauliExpect_eq_star_kramers {n : ℕ} (ψ : QState n) (p : PauliIdx n) :
    symPauliExpect ψ p = star (innerProd ψ (kramersConj p ψ)) := by
  rw [symPauliExpect, kramersConj, innerProd_pauliApply_right p (fun x => star (ψ x)) ψ,
      innerProd_conj_symm]

/-- **Vanishing on Antisymmetric Paulis (ALL `n`)**:
    For every `p` with `Q₀(p) ≠ 0`, `⟨ψ* | P_p | ψ⟩ = 0` identically. -/
theorem symPauliExpect_eq_zero_of_antisym {n : ℕ} (ψ : QState n) {p : PauliIdx n}
    (hp : quadForm0 p ≠ 0) : symPauliExpect ψ p = 0 := by
  have hp1 : quadForm0 p = 1 := (zmod2_cases (quadForm0 p)).resolve_left hp
  rw [symPauliExpect_eq_star_kramers, innerProd_kramersConj_zero hp1 ψ, star_zero]

/-- Cardinality of the symmetric Pauli set `symPts n`: `|(symPts n)| = d (d + 1) / 2`. -/
lemma card_symPts_real (n : ℕ) :
    ((symPts n).card : ℝ) = (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) / 2 := by
  have hq := sum_quadChar (0 : PauliIdx n)
  have hq0_eq : ∀ p : PauliIdx n, quadForm (0 : PauliIdx n) p = quadForm0 p := fun p => by
    simp [quadForm, symp_zero_left]
  have hsum_char : (∑ p : PauliIdx n, (if quadForm0 p = 0 then (1 : ℤ) else -1)) = (2 : ℤ) ^ n := by
    simp_rw [← hq0_eq]
    simpa [quadForm0, dot_zero_left] using hq
  let S0 := symPts n
  let S1 := Finset.univ.filter fun p : PauliIdx n => ¬quadForm0 p = 0
  have hadd : (S0.card : ℤ) + (S1.card : ℤ) = ((2 ^ n * 2 ^ n : ℕ) : ℤ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun p : PauliIdx n => quadForm0 p = 0) (fun _ => (1 : ℕ))
    have h2 : S0.card + S1.card = 2 ^ n * 2 ^ n := by
      simpa only [S0, S1, symPts, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
        card_PauliIdx] using h1
    exact_mod_cast h2
  have hsub : (S0.card : ℤ) - (S1.card : ℤ) = (2 : ℤ) ^ n := by
    rw [← hsum_char, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => quadForm0 p = 0)]
    have hs0 : ∑ p ∈ S0, (if quadForm0 p = 0 then (1 : ℤ) else -1) = (S0.card : ℤ) := by
      have : ∀ p ∈ S0, (if quadForm0 p = 0 then (1 : ℤ) else -1) = 1 := fun p hp => by
        simp [(Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs1 : ∑ p ∈ S1, (if quadForm0 p = 0 then (1 : ℤ) else -1) = -(S1.card : ℤ) := by
      have : ∀ p ∈ S1, (if quadForm0 p = 0 then (1 : ℤ) else -1) = -1 := fun p hp => by
        simp [(Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
    change (S0.card : ℤ) - (S1.card : ℤ) = ∑ p ∈ S0, _ + ∑ p ∈ S1, _
    rw [hs0, hs1]; ring
  have h2card : (2 : ℤ) * (S0.card : ℤ) = (2 : ℤ) ^ n * ((2 : ℤ) ^ n + 1) := by
    have : ((2 ^ n * 2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by push_cast; rfl
    linarith
  have hR : (2 : ℝ) * (S0.card : ℝ) = (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) := by exact_mod_cast h2card
  linarith

/-- **Exact Characteristic-2 Symplectic Parseval Duality (`w_p = (1/d) ∑_q (-1)^{Q₀(q)+ω(p,q)} c_q²`, ALL `n`)**:
    For EVERY `n`-qubit state `ψ` and EVERY `p : PauliIdx n`,
      `symPauliNormSq ψ p = (1 / 2ⁿ) * ∑ q, (-1)^{Q_p(q)} * c_q(ψ)²`. -/
theorem symPauliNormSq_eq_sympWHT {n : ℕ} (ψ : QState n) (p : PauliIdx n) :
    symPauliNormSq ψ p =
      (1 / (2 : ℝ) ^ n) *
        ∑ q : PauliIdx n, (if quadForm p q = 0 then (1 : ℝ) else -1) *
          (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  let φ : QState n := kramersConj p ψ
  -- `matTr (matMul (stateProj ψ) (stateProj φ)) = Complex.normSq (innerProd ψ φ)`!
  have htr_ov : matTr (matMul (stateProj ψ) (stateProj φ)) =
      (Complex.normSq (innerProd ψ φ) : ℂ) := by
    rw [matTr_stateProj_mul]
    have hap : matApply (stateProj φ) ψ = innerProd φ ψ • φ := by
      ext x; simp only [matApply, stateProj, Pi.smul_apply, smul_eq_mul, innerProd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    rw [hap, innerProd_smul_right, innerProd_conj_symm ψ φ, mul_comm, Complex.star_def,
        Complex.mul_conj]
  -- Expand both projectors in the Pauli basis and multiply traces!
  have hscale : matTr (matMul (matSmul ((2 : ℂ) ^ n) (stateProj ψ))
        (matSmul ((2 : ℂ) ^ n) (stateProj φ))) =
      ((2 : ℂ) ^ n) ^ 2 * matTr (matMul (stateProj ψ) (stateProj φ)) := by
    simp only [matTr, matMul, matSmul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
  rw [stateProj_eq_pauliExpand ψ, stateProj_eq_pauliExpand φ, matTr_pauliExpand_mul, htr_ov] at hscale
  have hre := congr_arg Complex.re hscale
  have hL : ((2 : ℂ) ^ n * ∑ q : PauliIdx n,
      (((innerProd ψ (pauliApply q ψ)).re * (innerProd φ (pauliApply q φ)).re : ℝ) : ℂ)).re =
      d * ∑ q : PauliIdx n, (if quadForm p q = 0 then (1 : ℝ) else -1) *
        (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
    have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have hk := congr_arg Complex.re (pauliExpect_kramersConj p q ψ)
    have hkr : (innerProd φ (pauliApply q φ)).re =
        (if quadForm p q = 0 then (1 : ℝ) else -1) * (innerProd ψ (pauliApply q ψ)).re := by
      dsimp only [φ]
      rw [hk]
      split_ifs <;> simp
    rw [hkr]; ring
  have hR : (((2 : ℂ) ^ n) ^ 2 * (Complex.normSq (innerProd ψ φ) : ℂ)).re =
      d ^ 2 * symPauliNormSq ψ p := by
    have h2c : ((2 : ℂ) ^ n) ^ 2 = ((d ^ 2 : ℝ) : ℂ) := by simp [d]
    have hns : Complex.normSq (innerProd ψ φ) = symPauliNormSq ψ p := by
      rw [symPauliNormSq, symPauliExpect_eq_star_kramers, Complex.star_def, Complex.normSq_conj]
    rw [h2c, ← Complex.ofReal_mul, Complex.ofReal_re, hns]
  rw [hL, hR] at hre
  have hdiv : d * symPauliNormSq ψ p =
      ∑ q : PauliIdx n, (if quadForm p q = 0 then (1 : ℝ) else -1) *
        (innerProd ψ (pauliApply q ψ)).re ^ 2 :=
    mul_left_cancel₀ hd_ne (by linear_combination -hre)
  calc symPauliNormSq ψ p = (1 / d) * (d * symPauliNormSq ψ p) := by field_simp [hd_ne]
    _ = _ := by rw [hdiv]

/-- **Total Symmetric Pauli Mass (`∑_{Q₀(p)=0} w_p = d`, ALL `n`)**. -/
theorem sum_symPauliNormSq_eq_dim {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    ∑ p ∈ symPts n, symPauliNormSq ψ p = (2 : ℝ) ^ n := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  -- First extend the sum to all `PauliIdx n`, since `w_p = 0` for `Q₀(p) ≠ 0`!
  have hall : ∑ p ∈ symPts n, symPauliNormSq ψ p = ∑ p : PauliIdx n, symPauliNormSq ψ p := by
    refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
    have hq : quadForm0 p ≠ 0 := by simpa [symPts] using hp
    rw [symPauliNormSq, symPauliExpect_eq_zero_of_antisym ψ hq, map_zero]
  rw [hall]
  simp_rw [symPauliNormSq_eq_sympWHT ψ, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ q : PauliIdx n,
      ∑ p : PauliIdx n, (if quadForm p q = 0 then (1 : ℝ) else -1) *
        (innerProd ψ (pauliApply q ψ)).re ^ 2 =
      (if q = 0 then d ^ 2 else 0) * (innerProd ψ (pauliApply q ψ)).re ^ 2 := fun q => by
    rw [← Finset.sum_mul]
    congr 1
    have hsplit : ∀ p : PauliIdx n,
        (if quadForm p q = 0 then (1 : ℝ) else -1) =
          (if quadForm0 q = 0 then (1 : ℝ) else -1) * (sympSign q p : ℝ) := fun p => by
      simp only [quadForm, sympSign, symp_comm p q]
      rcases zmod2_cases (quadForm0 q) with h1 | h1 <;> rcases zmod2_cases (symp q p) with h2 | h2
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide]
    simp_rw [hsplit, ← Finset.mul_sum]
    have hss : ∑ p : PauliIdx n, (sympSign q p : ℝ) = if q = 0 then d ^ 2 else 0 := by
      have hz := sum_sympSign_univ q
      have hcast : ∑ p : PauliIdx n, (sympSign q p : ℝ) = ((∑ p : PauliIdx n, sympSign q p : ℤ) : ℝ) := by
        rw [Int.cast_sum]
      rw [hcast, hz]
      split_ifs
      · simp only [Int.cast_pow, Int.cast_ofNat, d]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
      · simp
    rw [hss]
    by_cases hq0 : q = 0
    · subst hq0; simp [quadForm0, dot_zero_left]
    · simp [hq0]
  simp_rw [hinner]
  rw [Finset.sum_eq_single (0 : PauliIdx n)]
  · simp only [↓reduceIte, pauliExpect_zero_re hunit, one_pow, mul_one, d]
    field_simp [show (2 : ℝ) ^ n ≠ 0 by positivity]
  · intro q _ hq; simp [hq]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Exact Complex-Symmetric Parseval Flatness Theorem (Theorem B, ALL `n`)**:
    For EVERY unit state `ψ : QState n` (`d = 2ⁿ`),
      `∑_{Q₀(p)=0} (|⟨ψ* | P_p | ψ⟩|² - 2 / (d + 1))² = pauliMoment4 n ψ - 2 d / (d + 1)`. -/
theorem sum_symPauliNormSq_sub_ideal_sq {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    ∑ p ∈ symPts n, (symPauliNormSq ψ p - 2 / (d + 1)) ^ 2 =
      pauliMoment4 n ψ - 2 * d / (d + 1) := by
  intro d
  have hd_ne : d ≠ 0 := by positivity
  have hd1_ne : d + 1 ≠ 0 := by positivity
  -- First prove Parseval: `∑_{p ∈ symPts n} w_p² = pauliMoment4 n ψ`!
  have hsum_w2 : ∑ p ∈ symPts n, (symPauliNormSq ψ p) ^ 2 = pauliMoment4 n ψ := by
    have hall : ∑ p ∈ symPts n, (symPauliNormSq ψ p) ^ 2 = ∑ p : PauliIdx n, (symPauliNormSq ψ p) ^ 2 := by
      refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
      have hq : quadForm0 p ≠ 0 := by simpa [symPts] using hp
      rw [symPauliNormSq, symPauliExpect_eq_zero_of_antisym ψ hq, map_zero, zero_pow (by norm_num)]
    rw [hall]
    let g : PauliIdx n → ℝ := fun q =>
      (if quadForm0 q = 0 then (1 : ℝ) else -1) * (innerProd ψ (pauliApply q ψ)).re ^ 2
    have hwp : ∀ p : PauliIdx n, symPauliNormSq ψ p = (1 / d) * ∑ q : PauliIdx n, (sympSign p q : ℝ) * g q := fun p => by
      rw [symPauliNormSq_eq_sympWHT ψ p]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      dsimp only [g]
      have hsign : (if quadForm p q = 0 then (1 : ℝ) else -1) =
          (sympSign p q : ℝ) * (if quadForm0 q = 0 then (1 : ℝ) else -1) := by
        simp only [quadForm, sympSign]
        rcases zmod2_cases (quadForm0 q) with h1 | h1 <;> rcases zmod2_cases (symp p q) with h2 | h2
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide]
      rw [hsign]; ring
    simp_rw [hwp, mul_pow, ← Finset.mul_sum]
    have hparseval : ∑ p : PauliIdx n, (∑ q : PauliIdx n, (sympSign p q : ℝ) * g q) ^ 2 =
        d ^ 2 * ∑ q : PauliIdx n, (g q) ^ 2 := by
      calc ∑ p : PauliIdx n, (∑ q : PauliIdx n, (sympSign p q : ℝ) * g q) ^ 2
          = ∑ p : PauliIdx n, ∑ q : PauliIdx n, ∑ r : PauliIdx n,
              (sympSign (q + r) p : ℝ) * (g q * g r) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [sympSign_add_left, sympSign_comm q p, sympSign_comm r p]; push_cast; ring
        _ = ∑ q : PauliIdx n, ∑ r : PauliIdx n,
              (∑ p : PauliIdx n, (sympSign (q + r) p : ℝ)) * (g q * g r) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => (Finset.sum_mul ..).symm
        _ = ∑ q : PauliIdx n, ∑ r : PauliIdx n,
              (if q = r then d ^ 2 else 0) * (g q * g r) := by
            refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
            congr 1
            have hz := sum_sympSign_univ (q + r)
            have hcast : ∑ p : PauliIdx n, (sympSign (q + r) p : ℝ) =
                ((∑ p : PauliIdx n, sympSign (q + r) p : ℤ) : ℝ) := by rw [Int.cast_sum]
            rw [hcast, hz]
            have hiff : q + r = 0 ↔ q = r := by
              constructor
              · intro h; have := congr_arg (· + r) h; simpa [pauliIdx_add_cancel_right] using this
              · intro h; rw [h, pauliIdx_add_self]
            simp only [hiff]
            split_ifs
            · dsimp only [d]
              push_cast
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
            · simp
        _ = d ^ 2 * ∑ q : PauliIdx n, (g q) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_eq_single q]
            · simp [sq]
            · intro r _ hr; simp [hr.symm]
            · intro h; exact absurd (Finset.mem_univ q) h
    rw [hparseval]
    have hg2 : ∑ q : PauliIdx n, (g q) ^ 2 = pauliMoment4 n ψ := by
      simp only [pauliMoment4, g]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hre := innerProd_pauliApply_self_real q ψ
      have hns : Complex.normSq (innerProd ψ (pauliApply q ψ)) =
          (innerProd ψ (pauliApply q ψ)).re ^ 2 := by
        conv_lhs => rw [← hre]
        rw [Complex.normSq_ofReal, sq]
      rw [hns]
      split_ifs <;> ring
    rw [hg2]; field_simp [hd_ne]
  -- Expand `∑ (w_p - 2/(d+1))²` using `sum_symPauliNormSq_eq_dim` and `card_symPts_real`!
  have hexp : ∑ p ∈ symPts n, (symPauliNormSq ψ p - 2 / (d + 1)) ^ 2 =
      ∑ p ∈ symPts n, (symPauliNormSq ψ p) ^ 2 -
      (4 / (d + 1)) * ∑ p ∈ symPts n, symPauliNormSq ψ p +
      ((symPts n).card : ℝ) * (2 / (d + 1)) ^ 2 := by
    have ht : ∀ p ∈ symPts n, (symPauliNormSq ψ p - 2 / (d + 1)) ^ 2 =
        (symPauliNormSq ψ p) ^ 2 - (4 / (d + 1)) * symPauliNormSq ψ p + (2 / (d + 1)) ^ 2 :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hexp, hsum_w2, sum_symPauliNormSq_eq_dim hunit, card_symPts_real]
  field_simp [hd1_ne]; ring

/-- **Complex-Symmetric Rank-1 Quadratic Identity (`Σ² = c̃₀ Σ`, ALL `n`)**:
    For EVERY `n`-qubit state `ψ`,
      `∑_{Q₀(p)=0} (⟨ψ* | P_p | ψ⟩)² = 2ⁿ * (⟨ψ* | ψ⟩)²`. -/
theorem symPauliExpect_sq_sum_eq {n : ℕ} (ψ : QState n) :
    ∑ p ∈ symPts n, (symPauliExpect ψ p) ^ 2 = (2 : ℂ) ^ n * (symPauliExpect ψ 0) ^ 2 := by
  have hall : ∑ p ∈ symPts n, (symPauliExpect ψ p) ^ 2 = ∑ p : PauliIdx n, (symPauliExpect ψ p) ^ 2 := by
    refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
    have hq : quadForm0 p ≠ 0 := by simpa [symPts] using hp
    rw [symPauliExpect_eq_zero_of_antisym ψ hq, zero_pow (by norm_num)]
  rw [hall]
  have hexp : ∀ a b : F2 n, (symPauliExpect ψ (a, b)) ^ 2 =
      ∑ x : F2 n, ∑ y : F2 n,
        (chi b (a + x + y) : ℂ) * (ψ x * ψ (x + a) * ψ y * ψ (y + a)) := fun a b => by
    simp only [symPauliExpect, innerProd, pauliApply, star_star, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hph2 : pauliPh (a, b) * pauliPh (a, b) = (chi b a : ℂ) := pauliPh_sq (a, b)
    have hchi3 : (chi b a : ℂ) * (chi b x : ℂ) * (chi b y : ℂ) = (chi b (a + x + y) : ℂ) := by
      rw [chi_add_right, chi_add_right]; push_cast; ring
    calc ψ x * (pauliPh (a, b) * (chi b x : ℂ) * ψ (x + a)) *
          (ψ y * (pauliPh (a, b) * (chi b y : ℂ) * ψ (y + a)))
        = (pauliPh (a, b) * pauliPh (a, b)) * (chi b x : ℂ) * (chi b y : ℂ) *
            (ψ x * ψ (x + a) * ψ y * ψ (y + a)) := by ring
      _ = _ := by rw [hph2, hchi3]
  calc ∑ p : PauliIdx n, (symPauliExpect ψ p) ^ 2
      = ∑ a : F2 n, ∑ b : F2 n, (symPauliExpect ψ (a, b)) ^ 2 := Fintype.sum_prod_type _
    _ = ∑ a : F2 n, ∑ b : F2 n, ∑ x : F2 n, ∑ y : F2 n,
          (chi b (a + x + y) : ℂ) * (ψ x * ψ (x + a) * ψ y * ψ (y + a)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hexp a b
    _ = ∑ a : F2 n, ∑ x : F2 n, ∑ y : F2 n,
          (∑ b : F2 n, (chi b (a + x + y) : ℂ)) * (ψ x * ψ (x + a) * ψ y * ψ (y + a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => (Finset.sum_mul ..).symm
    _ = ∑ a : F2 n, ∑ x : F2 n, ∑ y : F2 n,
          (if y = x + a then (2 : ℂ) ^ n else 0) * (ψ x * ψ (x + a) * ψ y * ψ (y + a)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_
        congr 1
        have hsc : ∑ b : F2 n, (chi b (a + x + y) : ℂ) =
            ((∑ b : F2 n, chi b (a + x + y) : ℤ) : ℂ) := by rw [Int.cast_sum]
        rw [hsc, sum_chi]
        have hiff : a + x + y = 0 ↔ y = x + a := by
          constructor
          · intro h
            have h1 := congr_arg (· + (x + a)) h
            have h2 : (a + x + y) + (x + a) = y := by
              calc (a + x + y) + (x + a) = y + (x + x) + (a + a) := by abel
                _ = y := by rw [f2_add_self, f2_add_self, add_zero, add_zero]
            simpa [h2] using h1
          · intro h; subst h
            calc a + x + (x + a) = (a + a) + (x + x) := by abel
              _ = 0 := by rw [f2_add_self, f2_add_self, add_zero]
        simp only [hiff]; split_ifs <;> simp
    _ = (2 : ℂ) ^ n * ∑ a : F2 n, ∑ x : F2 n, (ψ x) ^ 2 * (ψ (x + a)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (x + a)]
        · simp only [↓reduceIte, f2_add_cancel_right]; ring
        · intro y _ hy; simp [hy]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = (2 : ℂ) ^ n * (symPauliExpect ψ 0) ^ 2 := by
        congr 1
        have h0 : symPauliExpect ψ 0 = ∑ x : F2 n, (ψ x) ^ 2 := by
          simp only [symPauliExpect, innerProd, pauliApply_zero, star_star]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [h0, sq, Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun _ => rfl

/-- **Takagi Complex-Symmetric Flatness Lower Bound (Theorem B, ALL `n`)**:
    For EVERY unit state `ψ : QState n` (`d = 2ⁿ`),
      `(4 d / (d + 1)) * (1 - symPauliAlpha ψ) ≤ pauliMoment4 n ψ - 2 d / (d + 1)`.
    Hence any uniform bound `limsup α̃ₙ* < 1` directly implies `liminf Fₙ* > 2`. -/
theorem pauliMoment4_sub_welch_ge_symPauliAlpha {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    (4 * d / (d + 1)) * (1 - symPauliAlpha ψ) ≤ pauliMoment4 n ψ - 2 * d / (d + 1) := by
  intro d
  have hd_pos : 0 < d := by positivity
  have hd1_pos : 0 < d + 1 := by linarith
  let a : ℝ := Real.sqrt (2 / (d + 1))
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = 2 / (d + 1) := Real.sq_sqrt (by positivity)
  have hterm : ∀ p ∈ symPts n,
      a ^ 2 * (‖symPauliExpect ψ p‖ - a) ^ 2 ≤ (symPauliNormSq ψ p - a ^ 2) ^ 2 := fun p _ => by
    have hns : symPauliNormSq ψ p = ‖symPauliExpect ψ p‖ ^ 2 :=
      Complex.normSq_eq_norm_sq (symPauliExpect ψ p)
    rw [hns]
    have hfac : (‖symPauliExpect ψ p‖ ^ 2 - a ^ 2) ^ 2 =
        (‖symPauliExpect ψ p‖ + a) ^ 2 * (‖symPauliExpect ψ p‖ - a) ^ 2 := by ring
    rw [hfac]
    have hge : a ^ 2 ≤ (‖symPauliExpect ψ p‖ + a) ^ 2 := by
      have hn0 : 0 ≤ ‖symPauliExpect ψ p‖ := norm_nonneg _
      nlinarith
    exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)
  have hsum_le : a ^ 2 * ∑ p ∈ symPts n, (‖symPauliExpect ψ p‖ - a) ^ 2 ≤
      ∑ p ∈ symPts n, (symPauliNormSq ψ p - 2 / (d + 1)) ^ 2 := by
    rw [Finset.mul_sum, ← ha2]
    exact Finset.sum_le_sum hterm
  have hsum_sq : ∑ p ∈ symPts n, (‖symPauliExpect ψ p‖ - a) ^ 2 =
      2 * d * (1 - symPauliAlpha ψ) := by
    have hexp : ∑ p ∈ symPts n, (‖symPauliExpect ψ p‖ - a) ^ 2 =
        ∑ p ∈ symPts n, symPauliNormSq ψ p - 2 * a * symPauliL1 ψ +
        ((symPts n).card : ℝ) * a ^ 2 := by
      have ht : ∀ p ∈ symPts n, (‖symPauliExpect ψ p‖ - a) ^ 2 =
          symPauliNormSq ψ p - 2 * a * ‖symPauliExpect ψ p‖ + a ^ 2 := fun p _ => by
        simp only [symPauliNormSq, Complex.normSq_eq_norm_sq]; ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, symPauliL1]
    rw [hexp, sum_symPauliNormSq_eq_dim hunit, card_symPts_real, ha2]
    have hprod : a * (d * Real.sqrt ((d + 1) / 2)) = d := by
      have hs : Real.sqrt (2 / (d + 1)) * Real.sqrt ((d + 1) / 2) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have : (2 / (d + 1)) * ((d + 1) / 2) = 1 := by field_simp [ne_of_gt hd1_pos]
        rw [this, Real.sqrt_one]
      dsimp only [a]
      calc Real.sqrt (2 / (d + 1)) * (d * Real.sqrt ((d + 1) / 2))
          = d * (Real.sqrt (2 / (d + 1)) * Real.sqrt ((d + 1) / 2)) := by ring
        _ = d := by rw [hs, mul_one]
    have hden_ne : d * Real.sqrt ((d + 1) / 2) ≠ 0 := by positivity
    have hL1_eq : symPauliL1 ψ = symPauliAlpha ψ * (d * Real.sqrt ((d + 1) / 2)) := by
      dsimp only [symPauliAlpha, d]; field_simp [hden_ne]
    rw [hL1_eq]
    have hterm2 : 2 * a * (symPauliAlpha ψ * (d * Real.sqrt ((d + 1) / 2))) =
        2 * d * symPauliAlpha ψ := by
      calc 2 * a * (symPauliAlpha ψ * (d * Real.sqrt ((d + 1) / 2)))
          = 2 * symPauliAlpha ψ * (a * (d * Real.sqrt ((d + 1) / 2))) := by ring
        _ = 2 * d * symPauliAlpha ψ := by rw [hprod]; ring
    rw [hterm2]
    field_simp [ne_of_gt hd1_pos]; ring
  rw [← sum_symPauliNormSq_sub_ideal_sq hunit]
  calc (4 * d / (d + 1)) * (1 - symPauliAlpha ψ)
      = a ^ 2 * (2 * d * (1 - symPauliAlpha ψ)) := by rw [ha2]; ring
    _ = a ^ 2 * ∑ p ∈ symPts n, (‖symPauliExpect ψ p‖ - a) ^ 2 := by rw [hsum_sq]
    _ ≤ ∑ p ∈ symPts n, (symPauliNormSq ψ p - 2 / (d + 1)) ^ 2 := hsum_le

/-! ### Part 4: Exact 3B Symplectic Autocorrelation Identity & Quartic Trace Sandwich -/

/-- Pure Boolean symplectic autocorrelation
    `A_r(σ) = ∑_{p ∈ (nzPts n).erase r} Re(pauliPhase r p) * σ p * σ (r + p)`. -/
noncomputable def sympAutocorr (n : ℕ) (σ : PauliIdx n → ℝ) (r : PauliIdx n) : ℝ :=
  ∑ p ∈ (nzPts n).erase r, (pauliPhase r p).re * σ p * σ (r + p)

/-- **Exact Square Expansion of `S(σ)` (ALL `n : ℕ`)**:
    For every `±1` sign assignment `σ` (`σ 0 = 0`),
      `S(σ)² = (d² - 1) I + ∑_{r ≠ 0} A_r(σ) P_r`. -/
theorem signMat_sq_eq_pauliExpand (n : ℕ) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    matMul (pauliExpand σ) (pauliExpand σ) =
      pauliExpand (fun r => if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) := by
  rw [matMul_pauliExpand_self]
  congr 1; ext r
  by_cases hr : r = 0
  · subst hr
    simp only [↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0t : (pauliPhase (0 : PauliIdx n) 0).re * σ 0 * σ (0 + 0) = 0 := by simp [h0]
    have hrest : ∑ p ∈ nzPts n, (pauliPhase 0 p).re * σ p * σ (0 + p) = ((2 : ℝ) ^ n) ^ 2 - 1 := by
      have ht : ∀ p ∈ nzPts n, (pauliPhase 0 p).re * σ p * σ (0 + p) = 1 := fun p hp => by
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
        rw [pauliPhase_zero_left, Complex.one_re, zero_add, one_mul]
        rcases hpm p hp0 with h | h <;> rw [h] <;> norm_num
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact card_PauliIdx_erase_zero n
    change (pauliPhase (0 : PauliIdx n) 0).re * σ 0 * σ (0 + 0) +
      ∑ p ∈ nzPts n, (pauliPhase 0 p).re * σ p * σ (0 + p) = _
    rw [h0t, zero_add, hrest]
  · have hrU : r ∈ nzPts n := Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
    simp only [hr, ↓reduceIte, sympAutocorr]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    change (pauliPhase r 0).re * σ 0 * σ (r + 0) +
      ∑ p ∈ nzPts n, (pauliPhase r p).re * σ p * σ (r + p) = _
    rw [← Finset.add_sum_erase _ _ hrU]
    have ht0 : (pauliPhase r 0).re * σ 0 * σ (r + 0) = 0 := by simp [h0]
    have htr : (pauliPhase r r).re * σ r * σ (r + r) = 0 := by rw [pauliIdx_add_self, h0]; ring
    rw [ht0, htr, zero_add, zero_add]

/-- **Exact Cubic Trace via Symplectic Autocorrelation (ALL `n : ℕ`)**:
    `(Tr(S(σ)³)).re = d ∑_{r ≠ 0} σ_r A_r(σ)`. -/
theorem matTr_signMat_cube_eq_autocorr (n : ℕ) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    (matTr (matMul (pauliExpand σ) (matMul (pauliExpand σ) (pauliExpand σ)))).re =
      (2 : ℝ) ^ n * ∑ r ∈ nzPts n, σ r * sympAutocorr n σ r := by
  rw [signMat_sq_eq_pauliExpand n h0 hpm, matTr_pauliExpand_mul]
  have hre : ((2 : ℂ) ^ n * ∑ r : PauliIdx n,
      ((σ r * (if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) : ℝ) : ℂ)).re =
      (2 : ℝ) ^ n * ∑ r : PauliIdx n,
        σ r * (if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) := by
    have h2c : (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) := by simp
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  simp only [h0, zero_mul, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun r hr => by simp [(Finset.mem_erase.mp hr).1]

/-- **Exact Quartic Trace via Symplectic Autocorrelation (ALL `n : ℕ`)**:
    `(Tr(S(σ)⁴)).re = d * ((d² - 1)² + ∑_{r ≠ 0} A_r(σ)²)`. -/
theorem matTr_signMat_fourth_eq_autocorr (n : ℕ) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let S := pauliExpand σ
    (matTr (matMul (matMul S S) (matMul S S))).re =
      (2 : ℝ) ^ n * ((((2 : ℝ) ^ n) ^ 2 - 1) ^ 2 + ∑ r ∈ nzPts n, (sympAutocorr n σ r) ^ 2) := by
  intro S
  dsimp only [S]
  rw [signMat_sq_eq_pauliExpand n h0 hpm, matTr_pauliExpand_mul]
  have hre : ((2 : ℂ) ^ n * ∑ r : PauliIdx n,
      (((if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) *
        (if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) : ℝ) : ℂ)).re =
      (2 : ℝ) ^ n * ∑ r : PauliIdx n,
        (if r = 0 then ((2 : ℝ) ^ n) ^ 2 - 1 else sympAutocorr n σ r) ^ 2 := by
    have h2c : (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) := by simp
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 1; refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  simp only [↓reduceIte]
  congr 1; congr 1
  refine Finset.sum_congr rfl fun r hr => by simp [(Finset.mem_erase.mp hr).1]

/-- Matrix-free Rayleigh-to-quartic-trace inequality:
    for ANY Hermitian `A : QMat n` and unit state `ψ`, `(⟨ψ | A | ψ⟩.re)⁴ ≤ (Tr(A⁴)).re`. -/
lemma rayleigh_pow_four_le_matTr_fourth {n : ℕ} {A : QMat n} (hA : IsHermMat A)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    ((innerProd ψ (matApply A ψ)).re) ^ 4 ≤
      (matTr (matMul (matMul A A) (matMul A A))).re := by
  -- Step 1: `(⟨ψ | A ψ⟩.re)² ≤ ‖A ψ‖² = (⟨A ψ | A ψ⟩).re` (Cauchy–Schwarz on `𝔽₂ⁿ`).
  have h1 : ((innerProd ψ (matApply A ψ)).re) ^ 2 ≤ (innerProd (matApply A ψ) (matApply A ψ)).re := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (F2 n))
      (fun x => ‖ψ x‖) (fun x => ‖matApply A ψ x‖)
    have hre_le : |(innerProd ψ (matApply A ψ)).re| ≤
        ∑ x : F2 n, ‖ψ x‖ * ‖matApply A ψ x‖ := by
      calc |(innerProd ψ (matApply A ψ)).re|
          ≤ ‖innerProd ψ (matApply A ψ)‖ := Complex.abs_re_le_norm _
        _ ≤ ∑ x : F2 n, ‖star (ψ x) * matApply A ψ x‖ := norm_sum_le _ _
        _ = ∑ x : F2 n, ‖ψ x‖ * ‖matApply A ψ x‖ := by
            refine Finset.sum_congr rfl fun x _ => by rw [norm_mul, norm_star]
    have hsq_le : ((innerProd ψ (matApply A ψ)).re) ^ 2 ≤
        (∑ x : F2 n, ‖ψ x‖ ^ 2) * (∑ x : F2 n, ‖matApply A ψ x‖ ^ 2) := by
      calc ((innerProd ψ (matApply A ψ)).re) ^ 2
          = |(innerProd ψ (matApply A ψ)).re| ^ 2 := (sq_abs _).symm
        _ ≤ (∑ x : F2 n, ‖ψ x‖ * ‖matApply A ψ x‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hre_le 2
        _ ≤ _ := hcs
    have hψn : ∑ x : F2 n, ‖ψ x‖ ^ 2 = 1 := by
      have h := innerProd_self_re ψ
      rw [hunit, Complex.one_re] at h
      simpa [Complex.normSq_eq_norm_sq] using h.symm
    have hAψn : ∑ x : F2 n, ‖matApply A ψ x‖ ^ 2 = (innerProd (matApply A ψ) (matApply A ψ)).re := by
      rw [innerProd_self_re]
      refine Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
    rw [hψn, one_mul, hAψn] at hsq_le
    exact hsq_le
  -- Step 2: `((⟨A ψ | A ψ⟩).re)² = (Tr(|ψ⟩⟨ψ| · A²).re)² ≤ frobSq(|ψ⟩⟨ψ|) * frobSq(A²) = (Tr(A⁴)).re`!
  have h2 : ((innerProd (matApply A ψ) (matApply A ψ)).re) ^ 2 ≤
      (matTr (matMul (matMul A A) (matMul A A))).re := by
    let B := matMul A A
    have hBh : IsHermMat B := fun x y => by
      simp only [B, matMul, star_sum, star_mul]
      refine Finset.sum_congr rfl fun z _ => by rw [hA z y, hA x z]
    have htrB : matTr (matMul (stateProj ψ) B) = innerProd (matApply A ψ) (matApply A ψ) :=
      matTr_stateProj_mul_sq ψ hA
    have htrB2 : (matTr (matMul B B)).re = frobSq B := by
      have := congr_arg Complex.re (matTr_mul_self_herm hBh)
      simpa using this
    have hfrob_proj : frobSq (stateProj ψ) = 1 := by
      have := congr_arg Complex.re (matTr_mul_self_herm (stateProj_herm ψ))
      rw [stateProj_idem hunit] at this
      have htr1 : matTr (stateProj ψ) = 1 := by
        have h : matTr (stateProj ψ) = innerProd ψ ψ := by
          simp only [matTr, stateProj, innerProd]
          refine Finset.sum_congr rfl fun x _ => mul_comm _ _
        rw [h, hunit]
      rw [htr1] at this; simpa using this.symm
    -- Frobenius Cauchy–Schwarz on `Tr(|ψ⟩⟨ψ| B) = ∑_{x,y} ψ_x ψ_y* B_{y,x}`!
    have hcs_frob : ((matTr (matMul (stateProj ψ) B)).re) ^ 2 ≤ frobSq (stateProj ψ) * frobSq B := by
      have hnorm : |(matTr (matMul (stateProj ψ) B)).re| ≤
          ∑ p : F2 n × F2 n, ‖stateProj ψ p.1 p.2‖ * ‖B p.2 p.1‖ := by
        calc |(matTr (matMul (stateProj ψ) B)).re|
            ≤ ‖matTr (matMul (stateProj ψ) B)‖ := Complex.abs_re_le_norm _
          _ = ‖∑ p : F2 n × F2 n, stateProj ψ p.1 p.2 * B p.2 p.1‖ := by
              simp only [matTr, matMul, Fintype.sum_prod_type]
          _ ≤ ∑ p : F2 n × F2 n, ‖stateProj ψ p.1 p.2 * B p.2 p.1‖ := norm_sum_le _ _
          _ = ∑ p : F2 n × F2 n, ‖stateProj ψ p.1 p.2‖ * ‖B p.2 p.1‖ := by
              refine Finset.sum_congr rfl fun p _ => norm_mul _ _
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (F2 n × F2 n))
        (fun p => ‖stateProj ψ p.1 p.2‖) (fun p => ‖B p.2 p.1‖)
      have hf1 : ∑ p : F2 n × F2 n, ‖stateProj ψ p.1 p.2‖ ^ 2 = frobSq (stateProj ψ) := by
        rw [frobSq, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          (Complex.normSq_eq_norm_sq _).symm
      have hf2 : ∑ p : F2 n × F2 n, ‖B p.2 p.1‖ ^ 2 = frobSq B := by
        rw [frobSq, Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
          (Complex.normSq_eq_norm_sq _).symm
      calc ((matTr (matMul (stateProj ψ) B)).re) ^ 2
          = |(matTr (matMul (stateProj ψ) B)).re| ^ 2 := (sq_abs _).symm
        _ ≤ (∑ p : F2 n × F2 n, ‖stateProj ψ p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hnorm 2
        _ ≤ _ := hcs
        _ = frobSq (stateProj ψ) * frobSq B := by rw [hf1, hf2]
    rw [htrB, hfrob_proj, one_mul, ← htrB2] at hcs_frob
    exact hcs_frob
  have h1_nn : 0 ≤ ((innerProd ψ (matApply A ψ)).re) ^ 2 := sq_nonneg _
  calc ((innerProd ψ (matApply A ψ)).re) ^ 4
      = (((innerProd ψ (matApply A ψ)).re) ^ 2) ^ 2 := by ring
    _ ≤ ((innerProd (matApply A ψ) (matApply A ψ)).re) ^ 2 := pow_le_pow_left₀ h1_nn h1 2
    _ ≤ (matTr (matMul (matMul A A) (matMul A A))).re := h2

/-- **3B Quartic Trace Sandwich — Lower Half (`(αₙ(ψ))⁴ ≤ Tr(S(σ_ψ)⁴) / T₂²`, ALL `n ≥ 1`)**:
    For EVERY unit state `ψ : QState n`, choosing the sign assignment `σ_p = sgn(c_p(ψ))` yields
    `(pauliAlpha ψ)⁴ ≤ (Tr(S(σ)⁴)).re / T₂²` where `T₂ = d (d² - 1)`. -/
theorem pauliAlpha_pow_four_le_signMat_fourth {n : ℕ} (hn : 1 ≤ n)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let T2 : ℝ := d * (d ^ 2 - 1)
    ∃ σ : PauliIdx n → ℝ, σ 0 = 0 ∧ (∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) ∧
      (pauliAlpha ψ) ^ 4 ≤
        (matTr (matMul (matMul (pauliExpand σ) (pauliExpand σ))
                       (matMul (pauliExpand σ) (pauliExpand σ)))).re / T2 ^ 2 := by
  intro d T2
  let σ : PauliIdx n → ℝ := fun p =>
    if p = 0 then 0 else if 0 ≤ (innerProd ψ (pauliApply p ψ)).re then 1 else -1
  have h0 : σ 0 = 0 := by simp [σ]
  have hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp
  refine ⟨σ, h0, hpm, ?_⟩
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hT2_pos : 0 < T2 := by dsimp only [T2]; nlinarith
  have hray_eq : (innerProd ψ (matApply (pauliExpand σ) ψ)).re = pauliL1 ψ := by
    have hlin : innerProd ψ (matApply (pauliExpand σ) ψ) =
        ∑ p : PauliIdx n, (σ p : ℂ) * innerProd ψ (pauliApply p ψ) := by
      have hap : matApply (pauliExpand σ) ψ = ∑ p : PauliIdx n, (σ p : ℂ) • pauliApply p ψ := by
        ext x
        simp only [matApply, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]; congr 1
        exact congr_fun (pauliMat_apply p ψ) x
      rw [hap, innerProd_sum_right]
      refine Finset.sum_congr rfl fun p _ => innerProd_smul_right _ _ _
    rw [hlin, Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0t : ((σ 0 : ℂ) * innerProd ψ (pauliApply 0 ψ)).re = 0 := by simp [h0]
    rw [h0t, zero_add]
    simp only [pauliL1]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
    have hre := innerProd_pauliApply_self_real p ψ
    conv_lhs => rw [← hre]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [σ, hp0, ↓reduceIte]
    split_ifs with hnn
    · rw [one_mul, abs_of_nonneg hnn]
    · push Not at hnn; rw [abs_of_neg hnn]; ring
  have h4 := rayleigh_pow_four_le_matTr_fourth (pauliExpand_herm σ) hunit
  rw [hray_eq] at h4
  have hpow : (pauliAlpha ψ) ^ 4 = (pauliL1 ψ) ^ 4 / T2 ^ 2 := by
    simp only [pauliAlpha, div_pow]
    have hs4 : (Real.sqrt T2) ^ 4 = T2 ^ 2 := by
      calc (Real.sqrt T2) ^ 4 = ((Real.sqrt T2) ^ 2) ^ 2 := by ring
        _ = T2 ^ 2 := by rw [Real.sq_sqrt (le_of_lt hT2_pos)]
    dsimp only [T2, d] at hs4 ⊢
    rw [hs4]
  rw [hpow]
  exact div_le_div_of_nonneg_right h4 (sq_nonneg T2)

/-- **3B Quartic Trace Sandwich — Upper Half (`Tr(S(σ)⁴) / T₂² ≤ α_max²`, ALL `n ≥ 1`)**:
    If every unit state `φ : QState n` satisfies `pauliAlpha φ ≤ α_max`, then
    for EVERY `±1` sign assignment `σ` (`σ 0 = 0`),
      `(Tr(S(σ)⁴)).re / T₂² ≤ α_max²`. -/
theorem signMat_fourth_le_sq_of_alpha_bound {n : ℕ} (hn : 1 ≤ n)
    {α_max : ℝ}
    (hbound : ∀ φ : QState n, IsUnitState φ → pauliAlpha φ ≤ α_max)
    {σ : PauliIdx n → ℝ} (h0 : σ 0 = 0)
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let d : ℝ := (2 : ℝ) ^ n
    let T2 : ℝ := d * (d ^ 2 - 1)
    let S := pauliExpand σ
    (matTr (matMul (matMul S S) (matMul S S))).re / T2 ^ 2 ≤ α_max ^ 2 := by
  intro d T2 S
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    dsimp only [d]; exact_mod_cast this
  have hT2_pos : 0 < T2 := by dsimp only [T2]; nlinarith
  have hS_frob : frobSq S = T2 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)), h0]
    have ht : ∀ p ∈ nzPts n, (σ p) ^ 2 = 1 := fun p hp => by
      rcases hpm p (Finset.mem_erase.mp hp).1 with h | h <;> rw [h] <;> norm_num
    change (2 : ℝ) ^ n * (0 ^ 2 + ∑ p ∈ nzPts n, (σ p) ^ 2) = T2
    rw [zero_pow (by norm_num), zero_add, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul,
        mul_one, nzPts, card_PauliIdx_erase_zero n]
  -- Spectral theorem on `M = Matrix.of S` (identical pattern to `exists_unit_state_rayleigh_ge_cube`)!
  let M : Matrix (F2 n) (F2 n) ℂ := Matrix.of S
  have hM : M.IsHermitian := by
    ext x y; simp only [Matrix.conjTranspose_apply, M, Matrix.of_apply, S]
    rw [pauliExpand_herm σ x y, star_star]
  have hmul : ∀ X Y : QMat n, Matrix.of (matMul X Y) = Matrix.of X * Matrix.of Y := fun X Y => by
    ext x y; simp [matMul, Matrix.mul_apply]
  have htr : ∀ X : QMat n, matTr X = (Matrix.of X).trace := fun X => by
    simp [matTr, Matrix.trace, Matrix.diag]
  let ev : F2 n → ℝ := hM.eigenvalues
  let U := hM.eigenvectorUnitary
  let D : Matrix (F2 n) (F2 n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ ev)
  have hspec : M = Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U D := hM.spectral_theorem
  have htr_conj : ∀ X : Matrix (F2 n) (F2 n) ℂ,
      (Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U X).trace = X.trace := fun X => by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    have hU : (star (U : Matrix (F2 n) (F2 n) ℂ)) * (U : Matrix (F2 n) (F2 n) ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hU, Matrix.one_mul]
  have hfrob_eq : frobSq S = ∑ i : F2 n, (ev i) ^ 2 := by
    have h1 : (frobSq S : ℂ) = (M * M).trace := by
      rw [← matTr_mul_self_herm (pauliExpand_herm σ), htr, hmul]
    have h2 : M * M = Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U (D * D) := by
      conv_lhs => rw [hspec]
      rw [map_mul]
    have h3 : (D * D).trace = ∑ i : F2 n, (((ev i) ^ 2 : ℝ) : ℂ) := by
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, sq]
    rw [h2, htr_conj, h3, ← Complex.ofReal_sum] at h1
    exact Complex.ofReal_injective h1
  have h4_eq : (matTr (matMul (matMul S S) (matMul S S))).re = ∑ i : F2 n, (ev i) ^ 4 := by
    have h1 : matTr (matMul (matMul S S) (matMul S S)) = ((M * M) * (M * M)).trace := by
      rw [htr, hmul, hmul]
    have h2 : (M * M) * (M * M) =
        Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U ((D * D) * (D * D)) := by
      conv_lhs => rw [hspec]
      rw [map_mul, map_mul]
    have h3 : ((D * D) * (D * D)).trace = ∑ i : F2 n, (((ev i) ^ 4 : ℝ) : ℂ) := by
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2, htr_conj, h3, ← Complex.ofReal_sum, Complex.ofReal_re]
  -- Every eigenvalue satisfies `|ev i| ≤ α_max * √T2`!
  have hev_le : ∀ i : F2 n, (ev i) ^ 2 ≤ α_max ^ 2 * T2 := fun i => by
    let φ : QState n := ⇑(hM.eigenvectorBasis i)
    have hunit : IsUnitState φ := by
      have hnorm : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
      have hinn : @inner ℂ _ _ (hM.eigenvectorBasis i) (hM.eigenvectorBasis i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
      have hinner_eq : innerProd φ φ =
          @inner ℂ _ _ (hM.eigenvectorBasis i) (hM.eigenvectorBasis i) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [innerProd, dotProduct, Pi.star_apply, φ]
        refine Finset.sum_congr rfl fun x _ => mul_comm _ _
      rw [IsUnitState, hinner_eq, hinn]
    have hray : (innerProd φ (matApply S φ)).re = ev i := by
      have hev := hM.eigenvalues_eq i
      have hdot : dotProduct (star φ) (Matrix.mulVec M φ) = innerProd φ (matApply S φ) := by
        simp only [dotProduct, Matrix.mulVec, innerProd, matApply, Pi.star_apply, M, Matrix.of_apply]
      simpa [ev, φ, hdot] using hev.symm
    have habs : |ev i| ≤ pauliL1 φ := by
      rw [← hray]
      have hlin : (innerProd φ (matApply S φ)).re =
          ∑ p ∈ nzPts n, σ p * (innerProd φ (pauliApply p φ)).re := by
        have hap : matApply S φ = ∑ p : PauliIdx n, (σ p : ℂ) • pauliApply p φ := by
          ext x
          simp only [matApply, S, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]; congr 1
          exact congr_fun (pauliMat_apply p φ) x
        rw [hap, innerProd_sum_right, Complex.re_sum,
            ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
        have h0t : (innerProd φ ((σ 0 : ℂ) • pauliApply 0 φ)).re = 0 := by
          rw [innerProd_smul_right, h0]; simp
        rw [h0t, zero_add]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [innerProd_smul_right]
        conv_lhs => rw [← innerProd_pauliApply_self_real]
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hlin, pauliL1]
      calc |∑ p ∈ nzPts n, σ p * (innerProd φ (pauliApply p φ)).re|
          ≤ ∑ p ∈ nzPts n, |σ p * (innerProd φ (pauliApply p φ)).re| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ p ∈ nzPts n, |(innerProd φ (pauliApply p φ)).re| := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [abs_mul]
            have h1 : |σ p| = 1 := by
              rcases hpm p (Finset.mem_erase.mp hp).1 with h | h <;> rw [h] <;> norm_num
            rw [h1, one_mul]
    have hL1_le : pauliL1 φ ≤ α_max * Real.sqrt T2 := by
      have hb := hbound φ hunit
      simp only [pauliAlpha] at hb
      exact (div_le_iff₀ (Real.sqrt_pos.mpr hT2_pos)).mp hb
    have habs_le : |ev i| ≤ α_max * Real.sqrt T2 := le_trans habs hL1_le
    calc (ev i) ^ 2 = |ev i| ^ 2 := (sq_abs _).symm
      _ ≤ (α_max * Real.sqrt T2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_le 2
      _ = α_max ^ 2 * T2 := by rw [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)]
  have htr4_le : (matTr (matMul (matMul S S) (matMul S S))).re ≤ α_max ^ 2 * T2 ^ 2 := by
    rw [h4_eq]
    calc ∑ i : F2 n, (ev i) ^ 4
        = ∑ i : F2 n, (ev i) ^ 2 * (ev i) ^ 2 := Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i : F2 n, (α_max ^ 2 * T2) * (ev i) ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hev_le i) (sq_nonneg _)
      _ = (α_max ^ 2 * T2) * ∑ i : F2 n, (ev i) ^ 2 := (Finset.mul_sum ..).symm
      _ = α_max ^ 2 * T2 ^ 2 := by rw [← hfrob_eq, hS_frob]; ring
  exact (div_le_iff₀ (sq_pos_of_pos hT2_pos)).mpr htr4_le

/-! ### Part 5: Stage 15 Universal `O^ε(4m - 2, 2)` Projection, Stabilizer Identity,
    `C₂(4m, 2r) > 0` Sign-Flip (`t ≥ 16`), and Fermat Two-Squares `ℤ₄`-Rigidity -/

/-- Gaussian `2`-binomial coefficient `qBin2 n j = ∏_{i=0}^{j-1} (2^{n-i} - 1) / (2^{i+1} - 1)`
    (defined as `0` for `j > n`). -/
noncomputable def qBin2 (n j : ℕ) : ℝ :=
  if j ≤ n then
    ∏ i ∈ Finset.range j, (((2 : ℝ) ^ (n - i) - 1) / ((2 : ℝ) ^ (i + 1) - 1))
  else 0

lemma qBin2_zero (n : ℕ) : qBin2 n 0 = 1 := by simp [qBin2]

lemma qBin2_self (n : ℕ) : qBin2 n n = 1 := by
  simp only [qBin2, le_refl, ↓reduceIte]
  have hnum : ∏ i ∈ Finset.range n, ((2 : ℝ) ^ (n - i) - 1) =
      ∏ i ∈ Finset.range n, ((2 : ℝ) ^ (i + 1) - 1) := by
    have hrev := Finset.prod_range_reflect (fun i => (2 : ℝ) ^ (i + 1) - 1) n
    rw [← hrev]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hlt : i < n := Finset.mem_range.mp hi
    have heq : n - 1 - i + 1 = n - i := by omega
    rw [heq]
  rw [Finset.prod_div_distrib, hnum]
  have hne : ∏ i ∈ Finset.range n, ((2 : ℝ) ^ (i + 1) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by
      have : (2 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
        have h2 : 2 ≤ 2 ^ (i + 1) := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_pos i)
        exact_mod_cast h2
      linarith
  exact div_self hne

/-- `q = 2` Pascal recurrence: `qBin2 (n + 1) (j + 1) = qBin2 n (j + 1) + 2^{n - j} * qBin2 n j`. -/
lemma qBin2_succ_succ (n j : ℕ) (hj : j ≤ n) :
    qBin2 (n + 1) (j + 1) = qBin2 n (j + 1) + (2 : ℝ) ^ (n - j) * qBin2 n j := by
  by_cases hjeq : j = n
  · subst hjeq
    rw [qBin2_self, qBin2_self, Nat.sub_self, pow_zero, one_mul]
    simp [qBin2]
  · have hlt : j < n := Nat.lt_of_le_of_ne hj hjeq
    have hj1 : j + 1 ≤ n := hlt
    have hj1' : j + 1 ≤ n + 1 := Nat.le_succ_of_le hj1
    simp only [qBin2, hj, hj1, hj1', ↓reduceIte]
    -- Factor out the common `j`-term prefix `∏_{i=0}^{j-1} (2^{n-i} - 1) / (2^{i+1} - 1)`!
    have hden_ne : (2 : ℝ) ^ (j + 1) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have h2 : 2 ≤ 2 ^ (j + 1) := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_pos j)
        exact_mod_cast h2
      linarith
    have hnum_shift : ∏ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ (n + 1 - i) - 1) =
        ((2 : ℝ) ^ (n + 1) - 1) * ∏ i ∈ Finset.range j, ((2 : ℝ) ^ (n - i) - 1) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub, mul_comm]
    have hnum_n : ∏ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ (n - i) - 1) =
        ((2 : ℝ) ^ (n - j) - 1) * ∏ i ∈ Finset.range j, ((2 : ℝ) ^ (n - i) - 1) := by
      rw [Finset.prod_range_succ]; ring
    have hden_split : ∏ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ (i + 1) - 1) =
        ((2 : ℝ) ^ (j + 1) - 1) * ∏ i ∈ Finset.range j, ((2 : ℝ) ^ (i + 1) - 1) := by
      rw [Finset.prod_range_succ]; ring
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_div_distrib,
        hnum_shift, hnum_n, hden_split]
    have hpow : (2 : ℝ) ^ (n - j) * (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    have hden_p_ne : ∏ i ∈ Finset.range j, ((2 : ℝ) ^ (i + 1) - 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        have : (2 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
          have h2 : 2 ≤ 2 ^ (i + 1) := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_pos i)
          exact_mod_cast h2
        linarith
    rw [← hpow]
    field_simp [hden_ne, hden_p_ne]
    ring

/-- Term `j` of the universal `q = 2` Chu–Vandermonde identity (for arbitrary `ν : ℕ`, `a d : ℝ`). -/
noncomputable def qCVTerm (ν : ℕ) (a d : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * (2 : ℝ) ^ (j * (j - 1) / 2) * qBin2 ν j *
    (∏ i ∈ Finset.range j, (a / (2 : ℝ) ^ i + 1)) /
    (∏ i ∈ Finset.range j, (d + a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i))

/-- **Universal `q = 2` Chu–Vandermonde Telescoping Identity (ALL `ν : ℕ`, ALL `a, d : ℝ`)**:
    Whenever every denominator factor `d + a · 2^{ν-1-i} ≠ 0`,
      `∑_{j=0}^ν qCVTerm ν a d j = ∏_{i=0}^{ν-1} (d - 2ⁱ) / (d + a · 2^{ν-1} / 2ⁱ)`. -/
theorem qChuVandermonde_telescoping (ν : ℕ) (a d : ℝ)
    (hden : ∀ i < ν, d + a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i ≠ 0) :
    ∑ j ∈ Finset.range (ν + 1), qCVTerm ν a d j =
      ∏ i ∈ Finset.range ν, ((d - (2 : ℝ) ^ i) / (d + a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i)) := by
  induction ν with
  | zero =>
    simp [qCVTerm, qBin2_zero]
  | succ m ih =>
    have hden_m : ∀ i < m, d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i ≠ 0 := fun i hi => by
      have hm1 : 1 ≤ m := by omega
      have h1 := hden (i + 1) (by omega)
      have heq : (2 : ℝ) ^ m / (2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i := by
        have : m = (m - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ, pow_succ]
        field_simp
      simpa only [Nat.succ_sub_one, mul_div_assoc, heq] using h1
    have hlead_ne : d + a * (2 : ℝ) ^ m ≠ 0 := by
      have h0 := hden 0 (Nat.succ_pos m)
      simpa using h0
    -- Key telescoping identity for every `j ≤ m`:
    --   `(d + a * 2^m) * qCVTerm (m + 1) a d (j + 1)`
    --     `= (d + a * 2^m / 2^(j + 1)) * qCVTerm m a d (j + 1) - (a * 2^m / 2^j + 2^m) * qCVTerm m a d j`!
    have htele : ∀ j ≤ m,
        (d + a * (2 : ℝ) ^ m) * qCVTerm (m + 1) a d (j + 1) =
          (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1)) * qCVTerm m a d (j + 1) -
          (a * (2 : ℝ) ^ m / (2 : ℝ) ^ j + (2 : ℝ) ^ m) * qCVTerm m a d j := fun j hj => by
      -- Express denominator of `qCVTerm (m + 1) a d (j + 1)` cleanly!
      have hden_shift : ∏ i ∈ Finset.range (j + 1), (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ i) =
          (d + a * (2 : ℝ) ^ m) * ∏ i ∈ Finset.range j, (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i) := by
        rw [Finset.prod_range_succ']
        simp only [pow_zero, div_one, mul_comm (d + a * (2 : ℝ) ^ m)]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi_lt : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
        have hm1 : m = (m - 1) + 1 := by omega
        conv_lhs => rw [hm1, pow_succ, pow_succ]
        field_simp
      have hden_j_ne : ∏ i ∈ Finset.range j, (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => hden_m i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)
      have htri : (j + 1) * j / 2 = j * (j - 1) / 2 + j := by
        cases j with
        | zero => simp
        | succ k =>
          have h1 : (k + 1 + 1) * (k + 1) = (k + 1) * k + (k + 1) * 2 := by ring
          rw [Nat.add_sub_cancel, h1, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
      have hcancel_l : ∀ x y z : ℝ, z ≠ 0 → z * (x / (z * y)) = x / y := fun x y z hz => by
        rw [← mul_div_assoc, mul_div_mul_left _ _ hz]
      have hcancel_r : ∀ x y z : ℝ, z ≠ 0 → z * (x / (y * z)) = x / y := fun x y z hz => by
        rw [mul_comm y z, hcancel_l x y z hz]
      by_cases hjeq : j = m
      · subst j
        have hq0 : qBin2 m (m + 1) = 0 := by simp [qBin2]
        have h2m_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
        have hpow_tri : (2 : ℝ) ^ ((m + 1) * m / 2) = (2 : ℝ) ^ (m * (m - 1) / 2) * (2 : ℝ) ^ m := by
          rw [htri, pow_add]
        simp only [qCVTerm, Nat.add_sub_cancel, hq0, mul_zero, zero_mul, zero_div, zero_sub,
          qBin2_self, mul_one]
        rw [hden_shift, hcancel_l _ _ _ hlead_ne,
          Finset.prod_range_succ (fun i => a / (2 : ℝ) ^ i + 1) m,
          hpow_tri, pow_succ (-1 : ℝ)]
        field_simp [hden_j_ne, h2m_ne]
      · have hjlt : j < m := Nat.lt_of_le_of_ne hj hjeq
        have hden_last_eq : d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ j =
            d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1) := by
          have hm1 : m = (m - 1) + 1 := by omega
          conv_rhs => rw [hm1, pow_succ, pow_succ]
          field_simp
        have hden_last_ne : d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ j ≠ 0 := hden_m j hjlt
        have hden_m_j1 : ∏ i ∈ Finset.range (j + 1), (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i) =
            (∏ i ∈ Finset.range j, (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i)) *
            (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1)) := by
          rw [Finset.prod_range_succ, hden_last_eq]
        have hpow_tri : (2 : ℝ) ^ ((j + 1) * j / 2) = (2 : ℝ) ^ (j * (j - 1) / 2) * (2 : ℝ) ^ j := by
          rw [htri, pow_add]
        have hpow_split : (2 : ℝ) ^ (m - j) * (2 : ℝ) ^ j = (2 : ℝ) ^ m := by
          rw [← pow_add]; congr 1; omega
        have h2j_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
        have hsub : (2 : ℝ) ^ (m - j) = (2 : ℝ) ^ m / (2 : ℝ) ^ j := by
          rw [eq_div_iff h2j_ne]; exact hpow_split
        have hlast_ne' : d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1) ≠ 0 := by
          rwa [← hden_last_eq]
        simp only [qCVTerm, Nat.add_sub_cancel]
        rw [hden_shift, hden_m_j1, hcancel_l _ _ _ hlead_ne, hcancel_r _ _ _ hlast_ne',
          qBin2_succ_succ m j hj, hsub,
          Finset.prod_range_succ (fun i => a / (2 : ℝ) ^ i + 1) j, hpow_tri, pow_succ (-1 : ℝ)]
        field_simp [hden_j_ne, h2j_ne]
        ring
    -- Sum `htele` over `j = 0 .. m` and watch the `a * 2^m / 2^j * qCVTerm` terms telescope identically!
    have hsum_step : (d + a * (2 : ℝ) ^ m) * ∑ j ∈ Finset.range (m + 2), qCVTerm (m + 1) a d j =
        (d - (2 : ℝ) ^ m) * ∑ j ∈ Finset.range (m + 1), qCVTerm m a d j := by
      rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
      have h0_eq : (d + a * (2 : ℝ) ^ m) * qCVTerm (m + 1) a d 0 =
          (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ 0) * qCVTerm m a d 0 := by
        simp [qCVTerm, qBin2_zero]
      rw [h0_eq]
      have hsum_t : ∑ j ∈ Finset.range (m + 1), (d + a * (2 : ℝ) ^ m) * qCVTerm (m + 1) a d (j + 1) =
          ∑ j ∈ Finset.range (m + 1),
            ((d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1)) * qCVTerm m a d (j + 1) -
             (a * (2 : ℝ) ^ m / (2 : ℝ) ^ j + (2 : ℝ) ^ m) * qCVTerm m a d j) :=
        Finset.sum_congr rfl fun j hj => htele j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [hsum_t]
      -- Split into `d * sum - 2^m * sum + telescope`!
      let F : ℕ → ℝ := fun k => (a * (2 : ℝ) ^ m / (2 : ℝ) ^ k) * qCVTerm m a d k
      have hrearr : ∑ j ∈ Finset.range (m + 1),
            ((d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1)) * qCVTerm m a d (j + 1) -
             (a * (2 : ℝ) ^ m / (2 : ℝ) ^ j + (2 : ℝ) ^ m) * qCVTerm m a d j) =
          d * (∑ j ∈ Finset.range (m + 1), qCVTerm m a d (j + 1)) -
          (2 : ℝ) ^ m * (∑ j ∈ Finset.range (m + 1), qCVTerm m a d j) +
          ∑ j ∈ Finset.range (m + 1), (F (j + 1) - F j) := by
        have ht : ∀ j : ℕ,
            (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ (j + 1)) * qCVTerm m a d (j + 1) -
              (a * (2 : ℝ) ^ m / (2 : ℝ) ^ j + (2 : ℝ) ^ m) * qCVTerm m a d j =
            d * qCVTerm m a d (j + 1) - (2 : ℝ) ^ m * qCVTerm m a d j + (F (j + 1) - F j) := fun j => by
          dsimp only [F]; ring
        simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hrearr, Finset.sum_range_sub F (m + 1)]
      have hFm1 : F (m + 1) = 0 := by simp [F, qCVTerm, qBin2]
      have hqm1 : qCVTerm m a d (m + 1) = 0 := by simp [qCVTerm, qBin2]
      have hshift_d : d * qCVTerm m a d 0 + d * ∑ j ∈ Finset.range (m + 1), qCVTerm m a d (j + 1) =
          d * ∑ j ∈ Finset.range (m + 1), qCVTerm m a d j := by
        have h1 : ∑ j ∈ Finset.range (m + 1), qCVTerm m a d (j + 1) + qCVTerm m a d 0 =
            ∑ j ∈ Finset.range (m + 2), qCVTerm m a d j := (Finset.sum_range_succ' _ _).symm
        have h2 : ∑ j ∈ Finset.range (m + 2), qCVTerm m a d j =
            ∑ j ∈ Finset.range (m + 1), qCVTerm m a d j := by
          rw [Finset.sum_range_succ, hqm1, add_zero]
        rw [← mul_add, add_comm, h1, h2]
      have hF0 : (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ 0) * qCVTerm m a d 0 =
          d * qCVTerm m a d 0 + F 0 := by dsimp only [F]; ring
      rw [hF0, hFm1]
      linarith
    -- Now divide by `d + a * 2^m` and apply `ih`!
    have hRHS_step : ∏ i ∈ Finset.range (m + 1), ((d - (2 : ℝ) ^ i) / (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ i)) =
        ((d - (2 : ℝ) ^ m) / (d + a * (2 : ℝ) ^ m)) *
        ∏ i ∈ Finset.range m, ((d - (2 : ℝ) ^ i) / (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i)) := by
      have hnum_r : ∏ i ∈ Finset.range (m + 1), (d - (2 : ℝ) ^ i) =
          (d - (2 : ℝ) ^ m) * ∏ i ∈ Finset.range m, (d - (2 : ℝ) ^ i) := by
        rw [Finset.prod_range_succ]; ring
      have hden_r : ∏ i ∈ Finset.range (m + 1), (d + a * (2 : ℝ) ^ m / (2 : ℝ) ^ i) =
          (d + a * (2 : ℝ) ^ m) * ∏ i ∈ Finset.range m, (d + a * (2 : ℝ) ^ (m - 1) / (2 : ℝ) ^ i) := by
        rw [Finset.prod_range_succ']
        simp only [pow_zero, div_one, mul_comm (d + a * (2 : ℝ) ^ m)]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi_lt : i < m := Finset.mem_range.mp hi
        have hm1 : m = (m - 1) + 1 := by omega
        conv_lhs => rw [hm1, pow_succ, pow_succ]
        field_simp
      rw [Finset.prod_div_distrib, Finset.prod_div_distrib, hnum_r, hden_r]
      exact mul_div_mul_comm _ _ _ _
    rw [Nat.add_sub_cancel, hRHS_step, ← ih hden_m]
    have hmul_eq : (d + a * (2 : ℝ) ^ m) * ∑ j ∈ Finset.range (m + 2), qCVTerm (m + 1) a d j =
        (d + a * (2 : ℝ) ^ m) *
          (((d - (2 : ℝ) ^ m) / (d + a * (2 : ℝ) ^ m)) *
            ∑ j ∈ Finset.range (m + 1), qCVTerm m a d j) := by
      rw [hsum_step, ← mul_assoc, mul_div_cancel₀ _ hlead_ne]
    exact mul_left_cancel₀ hlead_ne hmul_eq

/-- Witt index `ν(s, ε)` of `O^ε(2s, 2)`: `s` when `ε = 1`, `s - 1` when `ε = -1`. -/
def wittIdx (s : ℕ) (ε : ℤ) : ℕ :=
  if ε = 1 then s else s - 1

/-- Number `N_j(s, ε)` of `j`-dimensional totally singular subspaces in `O^ε(2s, 2)`. -/
noncomputable def orthSubspaceCount (s : ℕ) (ε : ℤ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (((2 : ℝ) ^ (s - i) - (ε : ℝ)) * ((2 : ℝ) ^ (s - 1 - i) + (ε : ℝ))) /
      ((2 : ℝ) ^ (i + 1) - 1)

/-- Coefficient `c_j(s, ε, d)` of `M_j` in the exact `R_{4m}`-ideal orthogonal projector
    `Q_orth^{(4m, 2r)}(d)` (`s = 2m - 1`, `ε = (-1)^{m - r}`). -/
noncomputable def orthProjCoeff (s : ℕ) (ε : ℤ) (d : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * (2 : ℝ) ^ (j * (j - 1) / 2) * orthSubspaceCount s ε j /
    ∏ i ∈ Finset.range j, (d + (2 : ℝ) ^ (2 * s - 2 - i))

/-- **Exact Witt Upper-Bidiagonal Annihilation Recurrence (`M₁ Q = 0`, ALL `s ≥ 1`, `ε ∈ {±1}`)**:
    For every `0 ≤ j < wittIdx s ε`, the coefficients `c_j = orthProjCoeff s ε d j` satisfy
      `(2^{j+1} - 1) (d + 2^{2s - 2 - j}) c_{j+1} + 2^j (2^{s-j} - ε) (2^{s-1-j} + ε) c_j = 0`. -/
theorem orthProjCoeff_bidiagonal_recurrence {s : ℕ} (hs : 1 ≤ s) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {d : ℝ} (hd : 0 ≤ d) {j : ℕ} (hj : j < wittIdx s ε) :
    ((2 : ℝ) ^ (j + 1) - 1) * (d + (2 : ℝ) ^ (2 * s - 2 - j)) * orthProjCoeff s ε d (j + 1) +
      (2 : ℝ) ^ j * ((2 : ℝ) ^ (s - j) - (ε : ℝ)) * ((2 : ℝ) ^ (s - 1 - j) + (ε : ℝ)) *
        orthProjCoeff s ε d j = 0 := by
  have hden_j1 : ∏ i ∈ Finset.range (j + 1), (d + (2 : ℝ) ^ (2 * s - 2 - i)) =
      (∏ i ∈ Finset.range j, (d + (2 : ℝ) ^ (2 * s - 2 - i))) * (d + (2 : ℝ) ^ (2 * s - 2 - j)) :=
    Finset.prod_range_succ _ j
  have hN_j1 : orthSubspaceCount s ε (j + 1) =
      orthSubspaceCount s ε j *
        ((((2 : ℝ) ^ (s - j) - (ε : ℝ)) * ((2 : ℝ) ^ (s - 1 - j) + (ε : ℝ))) /
          ((2 : ℝ) ^ (j + 1) - 1)) :=
    Finset.prod_range_succ _ j
  have htri : (j + 1) * j / 2 = j * (j - 1) / 2 + j := by
    cases j with
    | zero => simp
    | succ k =>
      have h1 : (k + 1 + 1) * (k + 1) = (k + 1) * k + (k + 1) * 2 := by ring
      rw [Nat.add_sub_cancel, h1, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  have hden_p_ne : ∏ i ∈ Finset.range j, (d + (2 : ℝ) ^ (2 * s - 2 - i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  have hden_last_ne : d + (2 : ℝ) ^ (2 * s - 2 - j) ≠ 0 := by positivity
  have h2j1_ne : (2 : ℝ) ^ (j + 1) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      have h2 : 2 ≤ 2 ^ (j + 1) := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_pos j)
      exact_mod_cast h2
    linarith
  have hpow_tri : (2 : ℝ) ^ ((j + 1) * j / 2) = (2 : ℝ) ^ (j * (j - 1) / 2) * (2 : ℝ) ^ j := by
    rw [htri, pow_add]
  have _ := hs; have _ := hε; have _ := hj
  simp only [orthProjCoeff, hden_j1, hN_j1, Nat.add_sub_cancel, hpow_tri, pow_succ (-1 : ℝ)]
  field_simp [hden_p_ne, hden_last_ne, h2j1_ne]
  ring

/-- **Universal General-`t = 4m` Stabilizer Evaluation Identity (Stage 15, ALL `s ≥ 1`, `ε ∈ {±1}`, `d ≥ 0`)**:
    For every `s ≥ 1`, `ε ∈ {1, -1}`, and `d ≥ 0`,
      `∑_{j=0}^{ν} orthProjCoeff s ε d j = ∏_{i=0}^{ν-1} (d - 2ⁱ) / (d + 2^{2s - 2 - i})`. -/
theorem orthProjCoeff_sum_eq_stabilizer_ratio {s : ℕ} (hs : 1 ≤ s) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {d : ℝ} (hd : 0 ≤ d) :
    ∑ j ∈ Finset.range (wittIdx s ε + 1), orthProjCoeff s ε d j =
      ∏ i ∈ Finset.range (wittIdx s ε), ((d - (2 : ℝ) ^ i) / (d + (2 : ℝ) ^ (2 * s - 2 - i))) := by
  let ν := wittIdx s ε
  let a : ℝ := if ε = 1 then (2 : ℝ) ^ (s - 1) else (2 : ℝ) ^ s
  have ha_shift : ∀ i < ν, a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i = (2 : ℝ) ^ (2 * s - 2 - i) := fun i hi => by
    rcases hε with rfl | rfl
    · have hν : ν = s := by simp [ν, wittIdx]
      have ha : a = (2 : ℝ) ^ (s - 1) := by simp [a]
      rw [hν] at hi ⊢; rw [ha]
      have hexp : (s - 1) + (s - 1) = (2 * s - 2 - i) + i := by omega
      have h2i_ne : (2 : ℝ) ^ i ≠ 0 := by positivity
      rw [div_eq_iff h2i_ne, ← pow_add, ← pow_add, hexp]
    · have hν : ν = s - 1 := by simp [ν, wittIdx]
      have ha : a = (2 : ℝ) ^ s := by simp [a]
      rw [hν] at hi ⊢; rw [ha]
      have hexp : s + (s - 1 - 1) = (2 * s - 2 - i) + i := by omega
      have h2i_ne : (2 : ℝ) ^ i ≠ 0 := by positivity
      rw [div_eq_iff h2i_ne, ← pow_add, ← pow_add, hexp]
  have hterm_eq : ∀ j ∈ Finset.range (ν + 1), orthProjCoeff s ε d j = qCVTerm ν a d j := fun j hj => by
    have hjle : j ≤ ν := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hN_eq : orthSubspaceCount s ε j =
        qBin2 ν j * ∏ i ∈ Finset.range j, (a / (2 : ℝ) ^ i + 1) := by
      simp only [orthSubspaceCount, qBin2, hjle, ↓reduceIte, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hilt : i < ν := lt_of_lt_of_le (Finset.mem_range.mp hi) hjle
      have h2i_ne : (2 : ℝ) ^ i ≠ 0 := by positivity
      rcases hε with rfl | rfl
      · have hν : ν = s := by simp [ν, wittIdx]
        have ha : a = (2 : ℝ) ^ (s - 1) := by simp [a]
        rw [hν] at hilt ⊢; rw [ha]
        have hdiv : (2 : ℝ) ^ (s - 1) / (2 : ℝ) ^ i = (2 : ℝ) ^ (s - 1 - i) := by
          rw [div_eq_iff h2i_ne, ← pow_add]; congr 1; omega
        rw [hdiv]; simp only [Int.cast_one]; ring
      · have hν : ν = s - 1 := by simp [ν, wittIdx]
        have ha : a = (2 : ℝ) ^ s := by simp [a]
        rw [hν] at hilt ⊢; rw [ha]
        have hdiv : (2 : ℝ) ^ s / (2 : ℝ) ^ i = (2 : ℝ) ^ (s - i) := by
          rw [div_eq_iff h2i_ne, ← pow_add]; congr 1; omega
        rw [hdiv]; simp only [Int.cast_neg, Int.cast_one]
        have hsub_eq : s - 1 - i = s - 1 - i := rfl
        ring
    have hden_eq : ∏ i ∈ Finset.range j, (d + (2 : ℝ) ^ (2 * s - 2 - i)) =
        ∏ i ∈ Finset.range j, (d + a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [ha_shift i (lt_of_lt_of_le (Finset.mem_range.mp hi) hjle)]
    simp only [orthProjCoeff, qCVTerm, hN_eq, hden_eq]; ring
  rw [Finset.sum_congr rfl hterm_eq]
  have hden_pos : ∀ i < ν, d + a * (2 : ℝ) ^ (ν - 1) / (2 : ℝ) ^ i ≠ 0 := fun i hi => by
    rw [ha_shift i hi]; positivity
  rw [qChuVandermonde_telescoping ν a d hden_pos]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [ha_shift i (Finset.mem_range.mp hi)]

/-- **Universal Stabilizer Non-Negativity for ALL `n ∈ ℕ`, `s ≥ 1`, `ε ∈ {±1}`**:
    At every qubit dimension `d = 2ⁿ`, `0 ≤ ∑_{j=0}^ν orthProjCoeff s ε (2ⁿ) j`. -/
theorem orthProjCoeff_sum_nonneg {s : ℕ} (hs : 1 ≤ s) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (wittIdx s ε + 1), orthProjCoeff s ε ((2 : ℝ) ^ n) j := by
  rw [orthProjCoeff_sum_eq_stabilizer_ratio hs hε (by positivity)]
  by_cases hlt : n < wittIdx s ε
  · have hzero : ∏ i ∈ Finset.range (wittIdx s ε),
        (((2 : ℝ) ^ n - (2 : ℝ) ^ i) / ((2 : ℝ) ^ n + (2 : ℝ) ^ (2 * s - 2 - i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hlt) (by simp)
    rw [hzero]
  · push Not at hlt
    refine Finset.prod_nonneg fun i hi => ?_
    have hi_le : i ≤ n := le_trans (le_of_lt (Finset.mem_range.mp hi)) hlt
    have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ n := by
      have : 2 ^ i ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hi_le
      exact_mod_cast this
    exact div_nonneg (by linarith) (by positivity)

/-- Exact universal `d⁻²` asymptotic coefficient `C₂(4m, 2r)` of `E_orth(4m, 2r; d) / p₀`
    from the Stage 15 exact `2^{4m-4}` cancellation theorem. -/
noncomputable def c2Coeff (m r : ℕ) : ℝ :=
  let t : ℝ := 4 * (m : ℝ)
  let k : ℝ := 2 * (r : ℝ)
  let a : ℝ := t - k
  let ε : ℝ := (-1 : ℝ) ^ (m + r)
  ((2 : ℝ) ^ (4 * m - 3) - ε * (2 : ℝ) ^ (2 * m - 1)) -
    a * (a - 1) / 2 - k * (k - 1) / 2 -
    (a * (a - 1) * (a - 2) * k + a * k * (k - 1) * (k - 2)) / 12 -
    a * k * (1 + (t - 2) * (t - 3) / 4)

/-- **Stage 15 Exact `C₂(4m, 2r)` Permanent Sign-Flip Theorem (ALL `m ≥ 4`, i.e., `t = 4m ≥ 16`)**:
    For EVERY `m ≥ 4` and EVERY even cut `k = 2r` (`1 ≤ r ≤ 2m - 1`), `0 < c2Coeff m r`. -/
theorem c2_cancellation_pos_ge_16 {m r : ℕ} (hm : 4 ≤ m) (hr1 : 1 ≤ r) (hr2 : r ≤ 2 * m - 1) :
    0 < c2Coeff m r := by
  let t : ℝ := 4 * (m : ℝ)
  let k : ℝ := 2 * (r : ℝ)
  let a : ℝ := t - k
  have hm_r : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht_ge : (16 : ℝ) ≤ t := by dsimp only [t]; linarith
  have hk_ge : (2 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    dsimp only [k]; linarith
  have ha_ge : (2 : ℝ) ≤ a := by
    have hr_le : (r : ℝ) ≤ 2 * (m : ℝ) - 1 := by
      have : r + 1 ≤ 2 * m := by omega
      have h' : (r : ℝ) + 1 ≤ 2 * (m : ℝ) := by exact_mod_cast this
      linarith
    dsimp only [a, t, k]; linarith
  have hak_sum : a + k = t := by dsimp only [a]; ring
  -- Bound `ε * 2^{2m-1} ≤ 2^{2m-1}` and polynomial terms by `t^4 / 12 + 3 t^2 / 4`!
  have hε_le : (-1 : ℝ) ^ (m + r) ≤ 1 := by
    rcases Nat.even_or_odd (m + r) with h | h
    · rw [h.neg_one_pow]
    · rw [h.neg_one_pow]; norm_num
  have hε_term : (-1 : ℝ) ^ (m + r) * (2 : ℝ) ^ (2 * m - 1) ≤ (2 : ℝ) ^ (2 * m - 1) :=
    mul_le_of_le_one_left (by positivity) hε_le
  have hab_le : a * k ≤ t ^ 2 / 4 := by
    have : (a - k) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith [hak_sum]
  have hpoly1 : a * (a - 1) / 2 + k * (k - 1) / 2 ≤ t ^ 2 / 2 := by
    nlinarith [hak_sum, ha_ge, hk_ge]
  have hpoly2 : (a * (a - 1) * (a - 2) * k + a * k * (k - 1) * (k - 2)) / 12 ≤ t ^ 4 / 48 := by
    have h1 : a * (a - 1) * (a - 2) * k ≤ a ^ 3 * k := by
      have h0 : a * (a - 1) * (a - 2) ≤ a ^ 3 := by nlinarith [ha_ge]
      exact mul_le_mul_of_nonneg_right h0 (by linarith)
    have h2 : a * k * (k - 1) * (k - 2) ≤ a * k ^ 3 := by
      have h0 : k * (k - 1) * (k - 2) ≤ k ^ 3 := by nlinarith [hk_ge]
      nlinarith [ha_ge]
    have h3 : a ^ 3 * k + a * k ^ 3 = (a * k) * (a ^ 2 + k ^ 2) := by ring
    have h4 : a ^ 2 + k ^ 2 ≤ t ^ 2 := by nlinarith [hak_sum, ha_ge, hk_ge]
    have h5 : (a * k) * (a ^ 2 + k ^ 2) ≤ (t ^ 2 / 4) * t ^ 2 :=
      mul_le_mul hab_le h4 (by positivity) (by positivity)
    linarith
  have hpoly3 : a * k * (1 + (t - 2) * (t - 3) / 4) ≤ t ^ 2 / 4 + t ^ 4 / 16 := by
    have h1 : (t - 2) * (t - 3) / 4 ≤ t ^ 2 / 4 := by nlinarith [ht_ge]
    have h2 : a * k * (1 + (t - 2) * (t - 3) / 4) ≤ (t ^ 2 / 4) * (1 + t ^ 2 / 4) :=
      mul_le_mul hab_le (by linarith) (by nlinarith [ht_ge]) (by positivity)
    linarith
  -- Exponential dominance: `3 t^2 / 4 + t^4 / 12 < 2^{4m-3} - 2^{2m-1}` for ALL `m ≥ 4`!
  have hexp_dom : ∀ k : ℕ, 4 ≤ k →
      (3 / 4 : ℝ) * (4 * (k : ℝ)) ^ 2 + (1 / 12 : ℝ) * (4 * (k : ℝ)) ^ 4 <
        (2 : ℝ) ^ (4 * k - 3) - (2 : ℝ) ^ (2 * k - 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk_r : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hstep_pow1 : (2 : ℝ) ^ (4 * (k + 1) - 3) = 16 * (2 : ℝ) ^ (4 * k - 3) := by
        have : 4 * (k + 1) - 3 = (4 * k - 3) + 4 := by omega
        rw [this, pow_add]; norm_num; ring
      have hstep_pow2 : (2 : ℝ) ^ (2 * (k + 1) - 1) = 4 * (2 : ℝ) ^ (2 * k - 1) := by
        have : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
        rw [this, pow_add]; norm_num; ring
      have hrhs_ge : 16 * ((2 : ℝ) ^ (4 * k - 3) - (2 : ℝ) ^ (2 * k - 1)) ≤
          (2 : ℝ) ^ (4 * (k + 1) - 3) - (2 : ℝ) ^ (2 * (k + 1) - 1) := by
        rw [hstep_pow1, hstep_pow2]
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k - 1) := by positivity
        linarith
      have hpoly_step : (3 / 4 : ℝ) * (4 * ((k + 1 : ℕ) : ℝ)) ^ 2 +
            (1 / 12 : ℝ) * (4 * ((k + 1 : ℕ) : ℝ)) ^ 4 ≤
          16 * ((3 / 4 : ℝ) * (4 * (k : ℝ)) ^ 2 + (1 / 12 : ℝ) * (4 * (k : ℝ)) ^ 4) := by
        push_cast
        have h1 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by linarith
        have h2 : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
        have h4 : ((k : ℝ) + 1) ^ 4 ≤ 16 * (k : ℝ) ^ 4 := by
          calc ((k : ℝ) + 1) ^ 4 = (((k : ℝ) + 1) ^ 2) ^ 2 := by ring
            _ ≤ (4 * (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
            _ = 16 * (k : ℝ) ^ 4 := by ring
        nlinarith
      linarith
  have hdom := hexp_dom m hm
  dsimp only [c2Coeff]
  change 0 < ((2 : ℝ) ^ (4 * m - 3) - (-1 : ℝ) ^ (m + r) * (2 : ℝ) ^ (2 * m - 1)) -
    a * (a - 1) / 2 - k * (k - 1) / 2 -
    (a * (a - 1) * (a - 2) * k + a * k * (k - 1) * (k - 2)) / 12 -
    a * k * (1 + (t - 2) * (t - 3) / 4)
  linarith

/-- **Fermat Two-Squares Descent for Powers of `4` (Theorem C Arithmetic Core, ALL `m : ℕ`)**:
    For every `m : ℕ` and integers `R I : ℤ`,
      `R² + I² = 4ᵐ → ((R = 2ᵐ ∨ R = -2ᵐ) ∧ I = 0) ∨ (R = 0 ∧ (I = 2ᵐ ∨ I = -2ᵐ))`.
    Combined with `signMat_offdiag_even_re_im`, this forces every even-`n` Pauli-MUB fiducial
    to be a `ℤ₄`-phase state `i^{h(x) + 2 q(x)}` with `h` bent. -/
theorem int_sq_add_sq_eq_pow_four :
    ∀ (m : ℕ) (R I : ℤ), R ^ 2 + I ^ 2 = (4 : ℤ) ^ m →
      ((R = (2 : ℤ) ^ m ∨ R = -((2 : ℤ) ^ m)) ∧ I = 0) ∨
      (R = 0 ∧ (I = (2 : ℤ) ^ m ∨ I = -((2 : ℤ) ^ m))) := by
  intro m
  induction m with
  | zero =>
    intro R I h
    have h1 : R ^ 2 + I ^ 2 = 1 := by simpa using h
    have hR1 : -1 ≤ R := by nlinarith
    have hR2 : R ≤ 1 := by nlinarith
    have hI1 : -1 ≤ I := by nlinarith
    have hI2 : I ≤ 1 := by nlinarith
    have hR : R = -1 ∨ R = 0 ∨ R = 1 := by omega
    have hI : I = -1 ∨ I = 0 ∨ I = 1 := by omega
    rcases hR with rfl | rfl | rfl <;> rcases hI with rfl | rfl | rfl <;> simp_all
  | succ m ih =>
    intro R I h
    have hmod : (R ^ 2 + I ^ 2) % 4 = 0 := by
      rw [h, pow_succ]; omega
    have hsq_mod : ∀ z : ℤ, (z % 2 = 0 → z ^ 2 % 4 = 0) ∧ (z % 2 ≠ 0 → z ^ 2 % 4 = 1) := fun z => by
      constructor
      · intro h0
        set q := z / 2
        have hz : z = 2 * q := by omega
        have hsq : z ^ 2 = 4 * (q ^ 2) := by rw [hz]; ring
        omega
      · intro h1
        set q := z / 2
        have hz : z = 2 * q + 1 := by omega
        have hsq : z ^ 2 = 4 * (q ^ 2 + q) + 1 := by rw [hz]; ring
        omega
    have hReven : R % 2 = 0 := by
      by_contra hodd
      have hRsq := (hsq_mod R).2 hodd
      have hIsq : I ^ 2 % 4 = 0 ∨ I ^ 2 % 4 = 1 := by
        by_cases hi : I % 2 = 0
        · exact Or.inl ((hsq_mod I).1 hi)
        · exact Or.inr ((hsq_mod I).2 hi)
      omega
    have hIeven : I % 2 = 0 := by
      by_contra hodd
      have hIsq := (hsq_mod I).2 hodd
      have hRsq := (hsq_mod R).1 hReven
      omega
    let R' : ℤ := R / 2
    let I' : ℤ := I / 2
    have hR2 : R = 2 * R' := by omega
    have hI2 : I = 2 * I' := by omega
    have hsub : R' ^ 2 + I' ^ 2 = (4 : ℤ) ^ m := by
      have h4 : 4 * (R' ^ 2 + I' ^ 2) = 4 * (4 : ℤ) ^ m := by
        calc 4 * (R' ^ 2 + I' ^ 2) = (2 * R') ^ 2 + (2 * I') ^ 2 := by ring
          _ = R ^ 2 + I ^ 2 := by rw [← hR2, ← hI2]
          _ = (4 : ℤ) ^ (m + 1) := h
          _ = 4 * (4 : ℤ) ^ m := by rw [pow_succ]; ring
      linarith
    rcases ih R' I' hsub with ⟨hR', hI'⟩ | ⟨hR', hI'⟩
    · left
      refine ⟨?_, by rw [hI2, hI']; ring⟩
      rcases hR' with hR' | hR'
      · left; rw [hR2, hR', pow_succ]; ring
      · right; rw [hR2, hR', pow_succ]; ring
    · right
      refine ⟨by rw [hR2, hR']; ring, ?_⟩
      rcases hI' with hI' | hI'
      · left; rw [hI2, hI', pow_succ]; ring
      · right; rw [hI2, hI', pow_succ]; ring

end AsymptoticChar2Theory

-- Re-export main theorems at `MultiQubitMUB` root namespace for clean Audit access.
export AsymptoticChar2Theory (
  probDist
  probAutocorr
  gowersBoxC
  gowersBox
  sqOverlap
  gowersBox_im_zero
  pauliMoment4_eq_gowersBox_sum
  pauliMoment4_sub_welch_eq_gowers
  pauliMoment4_real_state_ge
  indivCosetAbsEnergy
  indivCosetReEnergy
  indivCosetAbsEnergy_eq
  indivCosetReEnergy_eq
  indivCosetReEnergy_ge
  indivCosetReEnergy_ge_welch_floor
  symPts
  symPauliExpect
  symPauliNormSq
  symPauliL1
  symPauliAlpha
  symPauliExpect_eq_zero_of_antisym
  symPauliNormSq_eq_sympWHT
  sum_symPauliNormSq_eq_dim
  sum_symPauliNormSq_sub_ideal_sq
  symPauliExpect_sq_sum_eq
  pauliMoment4_sub_welch_ge_symPauliAlpha
  sympAutocorr
  signMat_sq_eq_pauliExpand
  matTr_signMat_cube_eq_autocorr
  matTr_signMat_fourth_eq_autocorr
  rayleigh_pow_four_le_matTr_fourth
  pauliAlpha_pow_four_le_signMat_fourth
  signMat_fourth_le_sq_of_alpha_bound
  qBin2
  qCVTerm
  qChuVandermonde_telescoping
  wittIdx
  orthSubspaceCount
  orthProjCoeff
  orthProjCoeff_bidiagonal_recurrence
  orthProjCoeff_sum_eq_stabilizer_ratio
  orthProjCoeff_sum_nonneg
  c2Coeff
  c2_cancellation_pos_ge_16
  int_sq_add_sq_eq_pow_four
)

end MultiQubitMUB
