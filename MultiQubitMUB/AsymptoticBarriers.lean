import MultiQubitMUB.AsymptoticContextuality
import Mathlib.Analysis.Matrix.Spectrum

/-!
# General-`n` Asymptotic Barriers, Exact Bidirectional Equivalence, and Arithmetic Obstructions

Formalizes four groups of general-`n` pure-theory theorems (zero `sorry`, zero `native_decide`,
standard three Lean axioms `[propext, Classical.choice, Quot.sound]` only):

1. **Elementary Non-Squareness of `2ⁿ + 1`, Strict Spectral Contextuality Inequality, and
   3-Line Cubic-Trace No-Pauli-SIC Proof (`n ≥ 2, n ≠ 3`)**:
   - `pow_two_add_one_ne_sq`: `∀ n ≠ 3, ∀ k : ℕ, 2ⁿ + 1 ≠ k²`.
   - `sqrt_pow_two_add_one_ne_rat`: `√(2ⁿ + 1) ∉ ℚ` for every `n ≠ 3`.
   - `signCubeSum_lt_spectral` and `frustPairs_gt_spectral`: strict inequality
     `1 - 2 ρₙ(s) < 2 √(2ⁿ + 1) / (2ⁿ + 2)` for every `n ≥ 2, n ≠ 3` and every sign assignment `s`.
   - `no_pauli_sic_via_cubic_trace`: elementary cubic-trace proof of `2 d / (d + 1) < pauliMoment4 n ψ`
     for all `n ≥ 2, n ≠ 3` (`d = 2ⁿ`) via `Tr(ρ³) = 1` vs. `signCubeSum_lt_spectral`.

2. **Complete Quantitative Bidirectional Equivalence (`Fₙ → Welch ⇒ αₙ → 1` and `cₙ → 2 ⇒ αₙ → 1`)**:
   - `pauliL1_ge_of_pauliMoment4` and `pauliAlpha_ge_of_pauliMoment4`: for every `n ≥ 1` and unit
     state `|ψ⟩`,
       `√((d - 1) / d) - ((d + 1) / (2 √(d (d - 1)))) * (Fₙ(ψ) - 2 d / (d + 1)) ≤ αₙ(ψ)`,
     tight with exact equality at Welch equality.
   - `exists_unit_state_rayleigh_ge_cube`: via the Hermitian spectral theorem, every Hermitian
     `A : QMat n` has a unit eigenvector `|ψ⟩` with `(Tr(A³)).re ≤ ⟨ψ | A | ψ⟩.re * frobSq A`.
   - `exists_unit_state_pauliL1_ge_of_signCubeSum` and `exists_unit_state_pauliAlpha_ge_of_frustPairs`:
     for every `n ≥ 2` and sign assignment `s`, the top eigenvector `|ψ₁⟩` of the shifted sign
     operator `rₜ = (1/d) I + (1/(d√(d+1))) S(s)` satisfies BOTH Frobenius proximity
       `frobSq (rₜ - |ψ₁⟩⟨ψ₁|) ≤ 2 (1 - (Tr(rₜ³)).re)`
     AND the exact linear `αₙ` lower bound
       `√((d - 1) / d) * ((d + 2) / (2 √(d + 1))) * (1 - 2 ρₙ(s)) ≤ αₙ(ψ₁)`,
     completing the exact quantitative bidirectional equivalence `limsup αₙ* = 1 ↔ limsup cₙ* = 2`
     together with `AsymptoticContextuality.signCubeSum_ge_of_L1`.

3. **Pure-`c_p²` / Bell-Sampling LP Meta-Obstruction (`qSIC` & `sympWHT`)**:
   - For every `n ≥ 1`, the flat pseudo-SIC distribution `qSIC n` satisfies `qSIC n p ≥ 0`,
     `∑ p, qSIC n p = 1`, exact symplectic WHT self-duality `sympWHT (qSIC n) r = 2ⁿ * qSIC n r`,
     non-negative symplectic WHT for EVERY power `k : ℕ` (`0 ≤ sympWHT ((qSIC n)^k) r`), and
     `d² ∑ p, (qSIC n p)² = 2 d / (d + 1)`.
   - Consequently, no unsigned / pure-`c_p²` linear relaxation (including Bell-difference sampling
     and Delsarte-type moment LPs) can ever certify `pauliMoment4 n ψ > 2 d / (d + 1)`.

4. **Gaussian-Integer Parity Congruence & Stabilizer-Basis IPR Obstruction**:
   - `signMat_diag_odd_int`, `signMat_offdiag_even_re_im`, `signMat_add_id_half_gaussInt`:
     for every `n ≥ 2` and every `±1` Pauli sign assignment `σ`, the sign matrix `S(σ) = ∑_{p≠0} σ_p P_p`
     satisfies `(S(σ) + I) / 2 ∈ M_d(ℤ[i])` (odd integer diagonal, even Gaussian-integer off-diagonal).
   - `compBasisIPR_eq_sum_Z_pauliSq`, `compBasisIPR_eq_welch_of_flat_pauli`,
     `compBasisIPR_sub_welch_sq_le`:
     for every state `|ψ⟩`, the computational-basis inverse participation ratio
     `compBasisIPR ψ := d ∑_x |ψ_x|⁴` equals `∑_b c_{(0,b)}(ψ)²`, so any Welch-approaching state
     must satisfy `compBasisIPR ψ → 2` (quantitatively `(compBasisIPR ψ - 2 d / (d + 1))² ≤ (d - 1) * (Fₙ(ψ) - 2 d / (d + 1))`),
     strictly separating Welch-approaching states from flat-amplitude phase states (`Alltop.lean`, `I₂ = 1`).
-/

namespace MultiQubitMUB

open scoped Classical
open FourQubitCD
open GeneralContextualityLift
open AsymptoticContextuality

namespace AsymptoticBarriers

/-! ### Shared Helper: Shifted Pauli Sign Operator `rₜ` and Its Cubic Trace -/

/-- Shifted Pauli sign operator `rₜ(σ) = (1/d) I + (1/(d √(d+1))) ∑_{p ≠ 0} σ_p P_p`. -/
noncomputable def shiftedSignCoeff (n : ℕ) (σ : PauliIdx n → ℝ) (p : PauliIdx n) : ℝ :=
  if p = 0 then 1 / (2 : ℝ) ^ n else (1 / ((2 : ℝ) ^ n * Real.sqrt ((2 : ℝ) ^ n + 1))) * σ p

/-- Matrix form of the shifted Pauli sign operator `rₜ(σ)`. -/
noncomputable def shiftedSignOp (n : ℕ) (σ : PauliIdx n → ℝ) : QMat n :=
  pauliExpand (shiftedSignCoeff n σ)

lemma shiftedSignOp_herm (n : ℕ) (σ : PauliIdx n → ℝ) :
    IsHermMat (shiftedSignOp n σ) :=
  pauliExpand_herm (shiftedSignCoeff n σ)

lemma frobSq_shiftedSignOp (n : ℕ) {σ : PauliIdx n → ℝ}
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    frobSq (shiftedSignOp n σ) = 1 := by
  let d : ℝ := (2 : ℝ) ^ n
  let U : Finset (PauliIdx n) := nzPts n
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hsq : (Real.sqrt (d + 1)) ^ 2 = d + 1 := Real.sq_sqrt (le_of_lt hd1_pos)
  have hcardU : (U.card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  rw [shiftedSignOp, frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  have ha0 : (shiftedSignCoeff n σ 0) ^ 2 = 1 / d ^ 2 := by
    simp only [shiftedSignCoeff, ↓reduceIte, d]; ring
  have hrest : ∑ p ∈ U, (shiftedSignCoeff n σ p) ^ 2 = (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
    have ht : ∀ p ∈ U, (shiftedSignCoeff n σ p) ^ 2 = 1 / (d ^ 2 * (d + 1)) := fun p hp => by
      have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
      have hσ2 : (σ p) ^ 2 = 1 := by rcases hpm p hp0 with h | h <;> rw [h] <;> norm_num
      simp only [shiftedSignCoeff, hp0, ↓reduceIte, d, mul_pow, div_pow, one_pow, hσ2, mul_one, hsq]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcardU]
  change d * ((shiftedSignCoeff n σ 0) ^ 2 + ∑ p ∈ U, (shiftedSignCoeff n σ p) ^ 2) = 1
  rw [ha0, hrest]
  field_simp [hd_ne, hd1_ne]; ring

lemma matTr_shiftedSignOp_cube (n : ℕ) {σ : PauliIdx n → ℝ}
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let d : ℝ := (2 : ℝ) ^ n
    (matTr (matMul (shiftedSignOp n σ) (matMul (shiftedSignOp n σ) (shiftedSignOp n σ)))).re =
      (d + 3 * d * (d - 1) +
        (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) / d ^ 3 := by
  intro d
  let r : ℝ := 1 / Real.sqrt (d + 1)
  let U : Finset (PauliIdx n) := nzPts n
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
  have hσ_sq : ∀ p ∈ U, (σ p) ^ 2 = 1 := fun p hp => by
    rcases hpm p (Finset.mem_erase.mp hp).1 with h | h <;> rw [h] <;> norm_num
  have hcardU : (U.card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  let a : PauliIdx n → ℝ := shiftedSignCoeff n σ
  have ha_eq : ∀ p : PauliIdx n, a p = if p = 0 then 1 / d else (r / d) * σ p := fun p => by
    by_cases hp : p = 0
    · simp [a, shiftedSignCoeff, hp, d]
    · simp only [a, shiftedSignCoeff, hp, ↓reduceIte, r, d]; field_simp [hd_ne, hs_ne]
  let a2 : PauliIdx n → ℝ := fun q =>
    if q = 0 then 1 / d
    else (2 * r / d ^ 2) * σ q +
      (2 * r ^ 2 / d ^ 2) * ((1 / 2 : ℝ) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))
  have hrt2 : matMul (shiftedSignOp n σ) (shiftedSignOp n σ) = pauliExpand a2 := by
    rw [shiftedSignOp, matMul_pauliExpand_self]
    congr 1; ext q
    by_cases hq : q = 0
    · subst hq
      simp only [a2, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
      have ht0 : (pauliPhase (0 : PauliIdx n) 0).re * a 0 * a (0 + 0) = 1 / d ^ 2 := by
        rw [pauliPhase_zero_left, Complex.one_re, add_zero, ha_eq 0]; simp; ring
      have hrest : ∑ p ∈ U, (pauliPhase 0 p).re * a p * a (0 + p) =
          (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
        have ht : ∀ p ∈ U, (pauliPhase 0 p).re * a p * a (0 + p) =
            1 / (d ^ 2 * (d + 1)) := fun p hp => by
          have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
          rw [pauliPhase_zero_left, Complex.one_re, zero_add, one_mul, ha_eq p]
          simp only [hp0, ↓reduceIte]
          have : (r / d * σ p) * (r / d * σ p) = (r ^ 2 / d ^ 2) * (σ p) ^ 2 := by ring
          rw [this, hσ_sq p hp, hr2]; field_simp [hd_ne, hd1_ne]
        rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcardU]
      change (pauliPhase (0 : PauliIdx n) 0).re * a 0 * a (0 + 0) +
        ∑ p ∈ U, (pauliPhase 0 p).re * a p * a (0 + p) = 1 / d
      rw [ht0, hrest]; field_simp [hd_ne, hd1_ne]; ring
    · have hqU : q ∈ Finset.univ.erase (0 : PauliIdx n) :=
        Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
      simp only [a2, hq, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)),
          ← Finset.add_sum_erase _ _ hqU]
      have ht0 : (pauliPhase q 0).re * a 0 * a (q + 0) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_zero_right, Complex.one_re, add_zero, ha_eq 0, ha_eq q]
        simp only [↓reduceIte, hq]; ring
      have htq : (pauliPhase q q).re * a q * a (q + q) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self, ha_eq q, ha_eq 0]
        simp only [↓reduceIte, hq]; ring
      have hrest : ∑ p ∈ U.erase q, (pauliPhase q p).re * a p * a (q + p) =
          (r ^ 2 / d ^ 2) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have hqp0 : q + p ≠ 0 := fun hc => hpq (by
          have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
        rw [ha_eq p, ha_eq (q + p)]
        simp only [hp0, hqp0, ↓reduceIte]; ring
      change (pauliPhase q 0).re * a 0 * a (q + 0) +
        ((pauliPhase q q).re * a q * a (q + q) +
          ∑ p ∈ U.erase q, (pauliPhase q p).re * a p * a (q + p)) = _
      rw [ht0, htq, hrest]; ring
  rw [hrt2, shiftedSignOp, matTr_pauliExpand_mul]
  have hre : ((2 : ℂ) ^ n * ∑ p : PauliIdx n, ((a p * a2 p : ℝ) : ℂ)).re =
      d * ∑ p : PauliIdx n, a p * a2 p := by
    have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  change ((2 : ℂ) ^ n * ∑ p : PauliIdx n, ((a p * a2 p : ℝ) : ℂ)).re = _
  rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  have h0' : a 0 * a2 0 = 1 / d ^ 2 := by rw [ha_eq 0]; simp [a2]; ring
  have hrest : ∑ q ∈ U, a q * a2 q =
      (d ^ 2 - 1) * (2 * r ^ 2 / d ^ 3) + (2 * r ^ 3 / d ^ 3) * signCubeSum n σ := by
    have ht : ∀ q ∈ U, a q * a2 q =
        2 * r ^ 2 / d ^ 3 +
          (2 * r ^ 3 / d ^ 3) * (σ q * ((1 / 2 : ℝ) *
            ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))) := fun q hq => by
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      rw [ha_eq q]
      simp only [a2, hq0, ↓reduceIte]
      have hlin : (r / d * σ q) * (2 * r / d ^ 2 * σ q +
            2 * r ^ 2 / d ^ 2 * ((1 / 2 : ℝ) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))) =
          (2 * r ^ 2 / d ^ 3) * (σ q) ^ 2 +
            (2 * r ^ 3 / d ^ 3) * (σ q * ((1 / 2 : ℝ) *
              ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))) := by ring
      rw [hlin, hσ_sq q hq, mul_one]
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        hcardU, ← Finset.mul_sum]
    rfl
  have hr3 : r ^ 3 = 1 / ((d + 1) * Real.sqrt (d + 1)) := by
    calc r ^ 3 = r ^ 2 * r := by ring
      _ = (1 / (d + 1)) * (1 / Real.sqrt (d + 1)) := by rw [hr2]
      _ = 1 / ((d + 1) * Real.sqrt (d + 1)) := by rw [one_div_mul_one_div]
  change d * (a 0 * a2 0 + ∑ q ∈ U, a q * a2 q) = _
  rw [h0', hrest, hr2, hr3]
  field_simp [hd_ne, hd1_ne, hs_ne]; ring

/-! ### Part 1: Elementary Non-Squareness of `2ⁿ + 1`, Strict Spectral Contextuality, & 3-Line No-Pauli-SIC -/

/-- **Elementary Diophantine Lemma**: `2ⁿ + 1` is a perfect square if and only if `n = 3` (`9 = 3²`).
    Hence for EVERY `n ≠ 3`, `2ⁿ + 1 ≠ k²` for all `k : ℕ`. -/
theorem pow_two_add_one_ne_sq {n : ℕ} (hn3 : n ≠ 3) (k : ℕ) :
    2 ^ n + 1 ≠ k ^ 2 := by
  intro h
  have hk1 : 1 ≤ k := by
    by_contra hk0; push Not at hk0
    have hk' : k = 0 := by omega
    rw [hk'] at h; simp at h
  have hprod : (k - 1) * (k + 1) = 2 ^ n := by
    have h1 : (k - 1) * (k + 1) + 1 = k ^ 2 := by zify [hk1]; ring
    omega
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨k + 1, hprod.symm⟩
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨k - 1, by rw [mul_comm]; exact hprod.symm⟩
  have hdiff : 2 ^ a + 2 = 2 ^ b := by omega
  rcases Nat.lt_trichotomy a 1 with ha0 | rfl | ha2
  · have ha' : a = 0 := by omega
    subst ha'
    have hb3 : 2 ^ b = 3 := by simpa using hdiff.symm
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · interval_cases b <;> norm_num at hb3
    · have : 4 ≤ 2 ^ b := calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb2
      omega
  · have hb4 : 2 ^ b = 2 ^ 2 := by norm_num at hdiff ⊢; omega
    have hb2 : b = 2 := Nat.pow_right_injective (by norm_num) hb4
    subst hb2
    have hn8 : 2 ^ n = 2 ^ 3 := by
      rw [← hprod, ha, hb]; norm_num
    exact hn3 (Nat.pow_right_injective (by norm_num) hn8)
  · have hab : a < b := by
      by_contra hba; push Not at hba
      have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba
      omega
    have h4a : 4 ∣ 2 ^ a := by
      have : 2 ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    have h4b : 4 ∣ 2 ^ b := by
      have : 2 ^ 2 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    obtain ⟨pa, hpa⟩ := h4a
    obtain ⟨pb, hpb⟩ := h4b
    omega

/-- **Irrationality of `√(2ⁿ + 1)` (ALL `n ≠ 3`)**: `√(2ⁿ + 1)` is never rational for `n ≠ 3`. -/
theorem sqrt_pow_two_add_one_ne_rat {n : ℕ} (hn3 : n ≠ 3) (q : ℚ) :
    Real.sqrt ((2 : ℝ) ^ n + 1) ≠ (q : ℝ) := by
  intro hq
  have hd1_nn : (0 : ℝ) ≤ (2 : ℝ) ^ n + 1 := by positivity
  have hsqR : ((2 : ℝ) ^ n + 1) = ((q ^ 2 : ℚ) : ℝ) := by
    have h1 := congr_arg (fun x : ℝ => x ^ 2) hq
    rw [Real.sq_sqrt hd1_nn] at h1
    simpa [Rat.cast_pow] using h1
  have hsqQ : ((2 ^ n + 1 : ℕ) : ℚ) = q ^ 2 := by
    apply Rat.cast_injective (α := ℝ)
    simpa [Nat.cast_add, Nat.cast_pow] using hsqR
  have hmulQ : ((2 ^ n + 1 : ℕ) : ℚ) * (q.den : ℚ) ^ 2 = (q.num : ℚ) ^ 2 := by
    rw [hsqQ, ← mul_pow, Rat.mul_den_eq_num]
  have hmulZ : ((2 ^ n + 1 : ℕ) : ℤ) * (q.den : ℤ) ^ 2 = q.num ^ 2 := by
    exact_mod_cast hmulQ
  have hmulN : (2 ^ n + 1) * q.den ^ 2 = q.num.natAbs ^ 2 := by
    have hZ : (((2 ^ n + 1) * q.den ^ 2 : ℕ) : ℤ) = ((q.num.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact hmulZ
    exact_mod_cast hZ
  have hcop : Nat.Coprime (q.num.natAbs ^ 2) (q.den ^ 2) := q.reduced.pow 2 2
  have hdvd1 : q.den ^ 2 ∣ 1 := by
    have hdvd : q.den ^ 2 ∣ q.num.natAbs ^ 2 := ⟨2 ^ n + 1, by rw [mul_comm]; exact hmulN.symm⟩
    exact hcop.symm.dvd_of_dvd_mul_left (by simpa using hdvd)
  have hden1 : q.den ^ 2 = 1 := Nat.eq_one_of_dvd_one hdvd1
  rw [hden1, mul_one] at hmulN
  exact pow_two_add_one_ne_sq hn3 q.num.natAbs hmulN

/-- **Strict Spectral Contextuality Bound on `signCubeSum` (ALL `n ≥ 2, n ≠ 3`)**:
    For every `n ∈ {2} ∪ {4, 5, 6, …}` and every `±1` sign assignment `σ` (`σ 0 = 0`),
      `signCubeSum n σ < ((2ⁿ)² - 1) * (2ⁿ / 2 - 1) * √(2ⁿ + 1)`. -/
theorem signCubeSum_lt_spectral {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    (σ : PauliIdx n → ℝ) (h0 : σ 0 = 0)
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    signCubeSum n σ <
      (((2 : ℝ) ^ n) ^ 2 - 1) * ((2 : ℝ) ^ n / 2 - 1) * Real.sqrt ((2 : ℝ) ^ n + 1) := by
  refine lt_of_le_of_ne (signCubeSum_le_spectral (by omega) σ h0 hpm) fun heq => ?_
  have hbr := (signCubeSum_eq_frustPairs_all (by omega) h0 hpm).2
  set s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
  let q_lhs : ℚ :=
    (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℚ) / 2 - (frustPairs (nzPts n) s : ℚ)
  have hq_lhs : signCubeSum n σ = (q_lhs : ℝ) := by
    rw [hbr]; simp [q_lhs]
  let q_fac : ℚ := (((2 : ℚ) ^ n) ^ 2 - 1) * ((2 : ℚ) ^ n / 2 - 1)
  have hq_fac : (((2 : ℝ) ^ n) ^ 2 - 1) * ((2 : ℝ) ^ n / 2 - 1) = (q_fac : ℝ) := by
    simp [q_fac]
  have hd_ge4 : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
    have : (4 : ℕ) ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast this
  have hfac_ne : (q_fac : ℝ) ≠ 0 := by
    rw [← hq_fac]; nlinarith only [hd_ge4]
  have hsqrt : Real.sqrt ((2 : ℝ) ^ n + 1) = ((q_lhs / q_fac : ℚ) : ℝ) := by
    rw [hq_lhs, hq_fac] at heq
    rw [Rat.cast_div]
    exact (eq_div_iff hfac_ne).mpr (by linarith)
  exact sqrt_pow_two_add_one_ne_rat hn3 (q_lhs / q_fac) hsqrt

/-- **Strict Spectral Contextuality Density Inequality (ALL `n ≥ 2, n ≠ 3`)**:
    For every `n ∈ {2} ∪ {4, 5, 6, …}` and every sign assignment `s` on `W(2n-1, 2)`,
      `1 - 2 * ρₙ(s) < 2 * √(2ⁿ + 1) / (2ⁿ + 2)`. -/
theorem frustPairs_gt_spectral {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    1 - 2 * (frustPairs (nzPts n) s : ℝ) /
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) <
      2 * Real.sqrt ((2 : ℝ) ^ n + 1) / ((2 : ℝ) ^ n + 2) := by
  refine lt_of_le_of_ne (frustPairs_ge_spectral hn hs) fun heq => ?_
  let q_lhs : ℚ :=
    1 - 2 * (frustPairs (nzPts n) s : ℚ) /
      (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℚ)
  let q_rat : ℚ := q_lhs * ((2 : ℚ) ^ n + 2) / 2
  have hd2_ne : (2 : ℝ) ^ n + 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt ((2 : ℝ) ^ n + 1) = (q_rat : ℝ) := by
    have hlhs : 1 - 2 * (frustPairs (nzPts n) s : ℝ) /
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) = (q_lhs : ℝ) := by
      simp [q_lhs]
    rw [hlhs] at heq
    have hmul : (q_lhs : ℝ) * ((2 : ℝ) ^ n + 2) = 2 * Real.sqrt ((2 : ℝ) ^ n + 1) := by
      exact (eq_div_iff hd2_ne).mp heq
    have hcast : (q_rat : ℝ) = (q_lhs : ℝ) * ((2 : ℝ) ^ n + 2) / 2 := by
      simp [q_rat]
    rw [hcast, hmul]; ring
  exact sqrt_pow_two_add_one_ne_rat hn3 q_rat hsqrt

/-- **3-Line Cubic-Trace No-Pauli-SIC Theorem (ALL `n ≥ 2, n ≠ 3`)**:
    Elementary self-contained proof that NO unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n` achieves the Welch/SIC
    bound `2 d / (d + 1)` for `n ∈ {2} ∪ {4, 5, 6, …}`: equality forces `|ψ⟩⟨ψ| = rₜ(σ)` and hence
    `1 = Tr(rₜ³)`, forcing `signCubeSum n σ = (d² - 1)(d/2 - 1)√(d+1)`, contradicting
    `signCubeSum_lt_spectral`. -/
theorem no_pauli_sic_via_cubic_trace {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1) < pauliMoment4 n ψ := by
  let d : ℝ := (2 : ℝ) ^ n
  let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hsub := pauliMoment4_sub_welch hunit
  change pauliMoment4 n ψ - 2 * d / (d + 1) =
    ∑ p ∈ nzPts n, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 at hsub
  have hle : 2 * d / (d + 1) ≤ pauliMoment4 n ψ := by
    have hnn : 0 ≤ ∑ p ∈ nzPts n, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  refine lt_of_le_of_ne hle fun heq => ?_
  change 2 * d / (d + 1) = pauliMoment4 n ψ at heq
  have hsum0 : ∑ p ∈ nzPts n, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 = 0 := by linarith
  have hflat : ∀ p ∈ nzPts n, (c p) ^ 2 = 1 / (d + 1) := fun p hp => by
    have hsq0 : ((c p) ^ 2 - 1 / (d + 1)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun q _ => sq_nonneg _).mp hsum0 p hp
    have := sq_eq_zero_iff.mp hsq0
    linarith
  let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  have hσ0 : σ 0 = 0 := by simp [σ]
  have hσpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp
  have hproj_eq : stateProj ψ = shiftedSignOp n σ := by
    have hsp := stateProj_eq_pauliExpand ψ
    have hcoeff : ∀ p : PauliIdx n, c p = d * shiftedSignCoeff n σ p := fun p => by
      by_cases hp : p = 0
      · subst hp
        rw [show c 0 = 1 from pauliExpect_zero_re hunit]
        simp only [shiftedSignCoeff, ↓reduceIte]
        change (1 : ℝ) = d * (1 / d); field_simp [hd_ne]
      · have hpU : p ∈ nzPts n := Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩
        have hcp2 : (c p) ^ 2 = (1 / Real.sqrt (d + 1)) ^ 2 := by
          rw [hflat p hpU, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
        have habs : |c p| = 1 / Real.sqrt (d + 1) := by
          have hr_pos : 0 < 1 / Real.sqrt (d + 1) := div_pos one_pos hs_pos
          nlinarith [sq_abs (c p), abs_nonneg (c p)]
        simp only [shiftedSignCoeff, σ, hp, ↓reduceIte]
        change c p = d * (1 / (d * Real.sqrt (d + 1)) * if 0 ≤ c p then 1 else -1)
        by_cases hcp : 0 ≤ c p
        · simp only [hcp, ↓reduceIte, mul_one]
          rw [← abs_of_nonneg hcp, habs]; field_simp [hd_ne, hs_ne]
        · push Not at hcp
          simp only [not_le.mpr hcp, ↓reduceIte, mul_neg, mul_one]
          have hneg : c p = -|c p| := by rw [abs_of_neg hcp]; ring
          rw [hneg, habs]; field_simp [hd_ne, hs_ne]
    have hsmul : matSmul (d : ℂ) (stateProj ψ) = matSmul (d : ℂ) (shiftedSignOp n σ) := by
      calc matSmul (d : ℂ) (stateProj ψ)
          = pauliExpand c := by simpa [d, c] using hsp
        _ = pauliExpand (fun p => d * shiftedSignCoeff n σ p) := by
            congr 1; exact funext hcoeff
        _ = matSmul (d : ℂ) (shiftedSignOp n σ) := pauliExpand_smul d _
    ext x y
    have hxy := congr_fun (congr_fun hsmul x) y
    simp only [matSmul] at hxy
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hd_ne) hxy
  have htr_one : (matTr (matMul (shiftedSignOp n σ)
      (matMul (shiftedSignOp n σ) (shiftedSignOp n σ)))).re = 1 := by
    rw [← hproj_eq, stateProj_idem hunit, stateProj_idem hunit]
    have htr : matTr (stateProj ψ) = 1 := by
      have : matTr (stateProj ψ) = innerProd ψ ψ := by
        simp only [matTr, stateProj, innerProd]
        refine Finset.sum_congr rfl fun x _ => mul_comm _ _
      rw [this, hunit]
    rw [htr, Complex.one_re]
  have htr_cube := matTr_shiftedSignOp_cube n hσpm
  dsimp only at htr_cube
  rw [htr_one] at htr_cube
  have hS_eq : signCubeSum n σ = (d ^ 2 - 1) * (d / 2 - 1) * Real.sqrt (d + 1) := by
    have h1 : d + 3 * d * (d - 1) + (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ = d ^ 3 := by
      have := (eq_div_iff (pow_ne_zero 3 hd_ne)).mp htr_cube
      linarith
    have h2 : (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ = d * (d - 1) * (d - 2) := by
      linarith
    have h3 : (d + 1) * Real.sqrt (d + 1) / (2 * d) *
        ((2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) =
        (d + 1) * Real.sqrt (d + 1) / (2 * d) * (d * (d - 1) * (d - 2)) :=
      congr_arg _ h2
    have hlhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) *
        ((2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) = signCubeSum n σ := by
      field_simp [hd_ne, hd1_ne, hs_ne]
    have hrhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) * (d * (d - 1) * (d - 2)) =
        (d ^ 2 - 1) * (d / 2 - 1) * Real.sqrt (d + 1) := by
      field_simp [hd_ne]; ring
    linarith
  exact ne_of_lt (signCubeSum_lt_spectral hn hn3 σ hσ0 hσpm) hS_eq

/-! ### Part 2: Complete Quantitative Bidirectional Equivalence (`Fₙ → Welch ⇒ αₙ → 1` and `cₙ → 2 ⇒ αₙ → 1`) -/

/-- Non-identity Pauli `L₁` norm `L₁(ψ) = ∑_{p ≠ 0} |⟨ψ | P_p | ψ⟩|`. -/
noncomputable def pauliL1 {n : ℕ} (ψ : QState n) : ℝ :=
  ∑ p ∈ nzPts n, |(innerProd ψ (pauliApply p ψ)).re|

/-- Normalized Pauli `L₁` ratio `αₙ(ψ) = L₁(ψ) / √(d (d² - 1)) ∈ [0, 1]`. -/
noncomputable def pauliAlpha {n : ℕ} (ψ : QState n) : ℝ :=
  pauliL1 ψ / Real.sqrt ((2 : ℝ) ^ n * (((2 : ℝ) ^ n) ^ 2 - 1))

/-- **Quantitative `Fₙ → L₁` Bound (ALL `n ≥ 1`)**:
    For every unit pure state `ψ : QState n` (`d = 2ⁿ`),
      `√(d + 1) * ((d - 1) - ((d + 1) / 2) * (pauliMoment4 n ψ - 2 d / (d + 1))) ≤ pauliL1 ψ`. -/
theorem pauliL1_ge_of_pauliMoment4 {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    Real.sqrt (d + 1) * ((d - 1) - ((d + 1) / 2) * (pauliMoment4 n ψ - 2 * d / (d + 1))) ≤
      pauliL1 ψ := by
  intro d
  let r : ℝ := 1 / Real.sqrt (d + 1)
  let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  have hd_pos : 0 < d := by positivity
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
  have hsum_sq : ∑ p ∈ nzPts n, (c p) ^ 2 = d - 1 := by
    have h := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))] at h
    have hns : ∀ p, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
      fun p => innerProd_pauliApply_self_normSq p ψ
    have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
    simp_rw [hns, hc0] at h
    change 1 ^ 2 + ∑ p ∈ nzPts n, (c p) ^ 2 = d at h
    linarith
  have hcard : ((nzPts n).card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  have hexp : ∑ p ∈ nzPts n, (|c p| - r) ^ 2 = 2 * (d - 1) - 2 * r * pauliL1 ψ := by
    have ht : ∀ p ∈ nzPts n, (|c p| - r) ^ 2 = (c p) ^ 2 - 2 * r * |c p| + r ^ 2 := fun p _ => by
      have : |c p| ^ 2 = (c p) ^ 2 := sq_abs (c p)
      linarith [sub_sq |c p| r]
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hsum_sq, hcard, hr2]
    change (d - 1) - 2 * r * pauliL1 ψ + (d ^ 2 - 1) * (1 / (d + 1)) = _
    field_simp [hd1_ne]; ring
  have heps := eps_ge_div_d_add_one hunit
  change (∑ p ∈ nzPts n, (|c p| - r) ^ 2) / (d + 1) ≤ pauliMoment4 n ψ - 2 * d / (d + 1) at heps
  have hD2_le : 2 * (d - 1) - 2 * r * pauliL1 ψ ≤ (d + 1) * (pauliMoment4 n ψ - 2 * d / (d + 1)) := by
    have h1 := (div_le_iff₀ hd1_pos).mp heps
    rw [← hexp]; linarith
  have h2r : 2 * (d - 1) - (d + 1) * (pauliMoment4 n ψ - 2 * d / (d + 1)) ≤ 2 * r * pauliL1 ψ := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left h2r (le_of_lt (show 0 < Real.sqrt (d + 1) / 2 by positivity))
  have hrhs : Real.sqrt (d + 1) / 2 * (2 * r * pauliL1 ψ) = pauliL1 ψ := by
    simp only [r]; field_simp [hs_ne]
  have hlhs : Real.sqrt (d + 1) / 2 * (2 * (d - 1) - (d + 1) * (pauliMoment4 n ψ - 2 * d / (d + 1))) =
      Real.sqrt (d + 1) * ((d - 1) - ((d + 1) / 2) * (pauliMoment4 n ψ - 2 * d / (d + 1))) := by
    ring
  linarith

/-- **Quantitative `Fₙ → Welch ⇒ αₙ → 1` Equivalence Half (ALL `n ≥ 1`)**:
    For every `n ≥ 1` and every unit pure state `ψ : QState n` (`d = 2ⁿ`),
      `√((d - 1) / d) - ((d + 1) / (2 √(d (d - 1)))) * (pauliMoment4 n ψ - 2 d / (d + 1)) ≤ pauliAlpha ψ`.
    In particular, any sequence of states with `pauliMoment4 n ψₙ → 2` satisfies `pauliAlpha ψₙ → 1`. -/
theorem pauliAlpha_ge_of_pauliMoment4 {n : ℕ} (hn : 1 ≤ n) {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    Real.sqrt ((d - 1) / d) -
        ((d + 1) / (2 * Real.sqrt (d * (d - 1)))) * (pauliMoment4 n ψ - 2 * d / (d + 1)) ≤
      pauliAlpha ψ := by
  intro d
  have hd_ge2 : (2 : ℝ) ≤ d := by
    have : (2 : ℕ) ≤ 2 ^ n := calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hd_pos : 0 < d := by linarith
  have hd_sub_pos : 0 < d - 1 := by linarith
  have hd1_pos : 0 < d + 1 := by linarith
  have hdd1_pos : 0 < d * (d - 1) := mul_pos hd_pos hd_sub_pos
  have hT2_pos : 0 < d * (d ^ 2 - 1) := by nlinarith only [hd_ge2]
  have hfac : Real.sqrt (d * (d ^ 2 - 1)) = Real.sqrt (d * (d - 1)) * Real.sqrt (d + 1) := by
    rw [show d * (d ^ 2 - 1) = (d * (d - 1)) * (d + 1) by ring,
        Real.sqrt_mul (le_of_lt hdd1_pos)]
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd1_pos)
  have hsdd_ne : Real.sqrt (d * (d - 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdd1_pos)
  have hL1 := pauliL1_ge_of_pauliMoment4 hunit
  dsimp only at hL1
  have hdiv := div_le_div_of_nonneg_right hL1 (le_of_lt (Real.sqrt_pos.mpr hT2_pos))
  change _ ≤ pauliL1 ψ / Real.sqrt (d * (d ^ 2 - 1))
  refine le_trans ?_ hdiv
  rw [hfac]
  have hsq1 : (d - 1) / Real.sqrt (d * (d - 1)) = Real.sqrt ((d - 1) / d) := by
    have hmul : Real.sqrt (d * (d - 1)) = Real.sqrt d * Real.sqrt (d - 1) :=
      Real.sqrt_mul (le_of_lt hd_pos) _
    rw [hmul, Real.sqrt_div (le_of_lt hd_sub_pos)]
    have hsqd : Real.sqrt (d - 1) * Real.sqrt (d - 1) = d - 1 :=
      Real.mul_self_sqrt (le_of_lt hd_sub_pos)
    have hne1 : Real.sqrt (d - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_sub_pos)
    have hne2 : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
    calc (d - 1) / (Real.sqrt d * Real.sqrt (d - 1))
        = (Real.sqrt (d - 1) * Real.sqrt (d - 1)) / (Real.sqrt d * Real.sqrt (d - 1)) := by rw [hsqd]
      _ = Real.sqrt (d - 1) / Real.sqrt d := by field_simp [hne1, hne2]
  rw [← hsq1]
  have hsimp : Real.sqrt (d + 1) * ((d - 1) - (d + 1) / 2 * (pauliMoment4 n ψ - 2 * d / (d + 1))) /
      (Real.sqrt (d * (d - 1)) * Real.sqrt (d + 1)) =
      (d - 1) / Real.sqrt (d * (d - 1)) -
        (d + 1) / (2 * Real.sqrt (d * (d - 1))) * (pauliMoment4 n ψ - 2 * d / (d + 1)) := by
    field_simp [hs_ne, hsdd_ne]
  linarith

/-- **Hermitian Spectral Cubic-Rayleigh Theorem (ALL `n : ℕ`)**:
    For EVERY Hermitian `A : QMat n`, there exists a unit eigenvector `ψ : QState n` whose
    Rayleigh quotient `λ₁ = (⟨ψ | A | ψ⟩).re` satisfies `(Tr(A³)).re ≤ λ₁ * frobSq A`. -/
theorem exists_unit_state_rayleigh_ge_cube {n : ℕ} {A : QMat n} (hA : IsHermMat A) :
    ∃ ψ : QState n, IsUnitState ψ ∧
      (matTr (matMul A (matMul A A))).re ≤ (innerProd ψ (matApply A ψ)).re * frobSq A := by
  let M : Matrix (F2 n) (F2 n) ℂ := Matrix.of A
  have hM : M.IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, M, Matrix.of_apply]
    rw [hA x y, star_star]
  have hmul : ∀ X Y : QMat n, Matrix.of (matMul X Y) = Matrix.of X * Matrix.of Y := by
    intro X Y; ext x y; simp [matMul, Matrix.mul_apply]
  have htr : ∀ X : QMat n, matTr X = (Matrix.of X).trace := by
    intro X; simp [matTr, Matrix.trace, Matrix.diag]
  let ev : F2 n → ℝ := hM.eigenvalues
  let U := hM.eigenvectorUnitary
  let D : Matrix (F2 n) (F2 n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ ev)
  have hspec : M = Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U D := hM.spectral_theorem
  have htr_conj : ∀ X : Matrix (F2 n) (F2 n) ℂ,
      (Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U X).trace = X.trace := by
    intro X
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    have hU : (star (U : Matrix (F2 n) (F2 n) ℂ)) * (U : Matrix (F2 n) (F2 n) ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hU, Matrix.one_mul]
  have hfrob_eq : frobSq A = ∑ i : F2 n, (ev i) ^ 2 := by
    have h1 : (frobSq A : ℂ) = (M * M).trace := by
      rw [← matTr_mul_self_herm hA, htr, hmul]
    have h2 : M * M = Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U (D * D) := by
      conv_lhs => rw [hspec]
      rw [map_mul]
    have h3 : (D * D).trace = ∑ i : F2 n, (((ev i) ^ 2 : ℝ) : ℂ) := by
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, sq]
    rw [h2, htr_conj, h3, ← Complex.ofReal_sum] at h1
    exact Complex.ofReal_injective h1
  have hcube_eq : (matTr (matMul A (matMul A A))).re = ∑ i : F2 n, (ev i) ^ 3 := by
    have h1 : matTr (matMul A (matMul A A)) = (M * (M * M)).trace := by
      rw [htr, hmul, hmul]
    have h2 : M * (M * M) = Unitary.conjStarAlgAut ℂ (Matrix (F2 n) (F2 n) ℂ) U (D * (D * D)) := by
      conv_lhs => rw [hspec]
      rw [map_mul, map_mul]
    have h3 : (D * (D * D)).trace = ∑ i : F2 n, (((ev i) ^ 3 : ℝ) : ℂ) := by
      simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2, htr_conj, h3, ← Complex.ofReal_sum, Complex.ofReal_re]
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ ev Finset.univ_nonempty
  let ψ : QState n := ⇑(hM.eigenvectorBasis i_max)
  have hunit : IsUnitState ψ := by
    have hnorm : ‖hM.eigenvectorBasis i_max‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i_max
    have hinn : @inner ℂ _ _ (hM.eigenvectorBasis i_max) (hM.eigenvectorBasis i_max) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
    have hinner_eq : innerProd ψ ψ =
        @inner ℂ _ _ (hM.eigenvectorBasis i_max) (hM.eigenvectorBasis i_max) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [innerProd, dotProduct, Pi.star_apply, ψ]
      refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [IsUnitState, hinner_eq, hinn]
  have hray : (innerProd ψ (matApply A ψ)).re = ev i_max := by
    have hev := hM.eigenvalues_eq i_max
    have hdot : dotProduct (star ψ) (Matrix.mulVec M ψ) = innerProd ψ (matApply A ψ) := by
      simp only [dotProduct, Matrix.mulVec, innerProd, matApply, Pi.star_apply, M, Matrix.of_apply]
    simpa [ev, ψ, hdot] using hev.symm
  refine ⟨ψ, hunit, ?_⟩
  rw [hcube_eq, hfrob_eq, hray, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : ev i ≤ ev i_max := hi_max i (Finset.mem_univ i)
  have hsq_nn : 0 ≤ (ev i) ^ 2 := sq_nonneg (ev i)
  calc (ev i) ^ 3 = ev i * (ev i) ^ 2 := by ring
    _ ≤ ev i_max * (ev i) ^ 2 := mul_le_mul_of_nonneg_right hle hsq_nn

/-- **Exact Linear `signCubeSum → pauliL1` & Frobenius Proximity Theorem (ALL `n ≥ 1`)**:
    For every `n ≥ 1` and every `±1` Pauli sign assignment `σ` (`σ 0 = 0`), there exists a unit
    pure state `ψ : QState n` (the top eigenvector of `rₜ(σ)`) simultaneously satisfying:
    1. Frobenius proximity: `frobSq (matSub (shiftedSignOp n σ) (stateProj ψ)) ≤ 2 * (1 - (Tr(rₜ³)).re)`.
    2. Exact `pauliL1` lower bound:
         `√(d + 1) * (d * (Tr(rₜ³)).re - 1) ≤ pauliL1 ψ`. -/
theorem exists_unit_state_pauliL1_ge_of_signCubeSum {n : ℕ}
    (σ : PauliIdx n → ℝ)
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let d : ℝ := (2 : ℝ) ^ n
    let tr3 : ℝ :=
      (d + 3 * d * (d - 1) +
        (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) / d ^ 3
    ∃ ψ : QState n, IsUnitState ψ ∧
      frobSq (matSub (shiftedSignOp n σ) (stateProj ψ)) ≤ 2 * (1 - tr3) ∧
      Real.sqrt (d + 1) * (d * tr3 - 1) ≤ pauliL1 ψ := by
  intro d tr3
  let rt := shiftedSignOp n σ
  have hrt_h : IsHermMat rt := shiftedSignOp_herm n σ
  have hrt_frob : frobSq rt = 1 := frobSq_shiftedSignOp n hpm
  have hrt_cube : (matTr (matMul rt (matMul rt rt))).re = tr3 := matTr_shiftedSignOp_cube n hpm
  obtain ⟨ψ, hunit, hray⟩ := exists_unit_state_rayleigh_ge_cube hrt_h
  rw [hrt_cube, hrt_frob, mul_one] at hray
  refine ⟨ψ, hunit, ?_, ?_⟩
  · -- Part 1: Frobenius proximity `frobSq (rt - |ψ⟩⟨ψ|) = 2 * (1 - λ₁) ≤ 2 * (1 - tr3)`
    let P := stateProj ψ
    have hPh : IsHermMat P := stateProj_herm ψ
    have hP2 : matMul P P = P := stateProj_idem hunit
    have hdiff_h : IsHermMat (matSub rt P) := fun x y => by
      simp only [matSub, star_sub, ← hrt_h x y, ← hPh x y]
    have htrP : matTr P = 1 := by
      have : matTr P = innerProd ψ ψ := by
        simp only [matTr, P, stateProj, innerProd]
        refine Finset.sum_congr rfl fun x _ => mul_comm _ _
      rw [this, hunit]
    have htr_diff : matTr (matMul (matSub rt P) (matSub rt P)) =
        matTr (matMul rt rt) - 2 * matTr (matMul P rt) + matTr (matMul P P) := by
      rw [matMul_sub_left, matMul_sub_right, matMul_sub_right, matTr_sub, matTr_sub, matTr_sub,
          matTr_mul_comm rt P]; ring
    have hfrob_diff : frobSq (matSub rt P) = 2 * (1 - (innerProd ψ (matApply rt ψ)).re) := by
      have hC : (frobSq (matSub rt P) : ℂ) =
          (1 : ℂ) - 2 * innerProd ψ (matApply rt ψ) + 1 := by
        rw [← matTr_mul_self_herm hdiff_h, htr_diff, matTr_mul_self_herm hrt_h, hrt_frob,
            matTr_stateProj_mul, hP2, htrP]; norm_cast
      have hre := congr_arg Complex.re hC
      simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.one_re,
        Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
      linarith
    rw [hfrob_diff]; linarith
  · -- Part 2: Exact Pauli expansion of `λ₁ = (⟨ψ | rt | ψ⟩).re` gives `L₁ ≥ √(d+1) (d λ₁ - 1)`
    have hd_pos : 0 < d := by positivity
    have hd_ne : d ≠ 0 := ne_of_gt hd_pos
    have hd1_pos : 0 < d + 1 := by linarith
    have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
    have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
    have hlam_eq : (innerProd ψ (matApply rt ψ)).re =
        1 / d + (1 / (d * Real.sqrt (d + 1))) *
          ∑ p ∈ nzPts n, σ p * (innerProd ψ (pauliApply p ψ)).re := by
      have happly : matApply rt ψ =
          ∑ p : PauliIdx n, (shiftedSignCoeff n σ p : ℂ) • pauliApply p ψ := by
        ext x
        simp only [matApply, rt, shiftedSignOp, pauliExpand, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => by
          simp_rw [mul_assoc, ← Finset.mul_sum]; congr 1
          exact congr_fun (pauliMat_apply p ψ) x
      rw [happly, innerProd_sum_right]
      simp only [innerProd_smul_right, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
      have h0' : shiftedSignCoeff n σ 0 * (innerProd ψ (pauliApply 0 ψ)).re = 1 / d := by
        rw [pauliExpect_zero_re hunit]; simp [shiftedSignCoeff, d]
      have hrest' : ∑ p ∈ nzPts n, shiftedSignCoeff n σ p * (innerProd ψ (pauliApply p ψ)).re =
          (1 / (d * Real.sqrt (d + 1))) * ∑ p ∈ nzPts n, σ p * (innerProd ψ (pauliApply p ψ)).re := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
        simp only [shiftedSignCoeff, hp0, ↓reduceIte, d]; ring
      change shiftedSignCoeff n σ 0 * (innerProd ψ (pauliApply 0 ψ)).re +
        ∑ p ∈ nzPts n, shiftedSignCoeff n σ p * (innerProd ψ (pauliApply p ψ)).re = _
      rw [h0', hrest']
    have hsum_le : ∑ p ∈ nzPts n, σ p * (innerProd ψ (pauliApply p ψ)).re ≤ pauliL1 ψ := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
      rcases hpm p hp0 with h | h
      · rw [h, one_mul]; exact le_abs_self _
      · rw [h, neg_one_mul]; exact neg_le_abs _
    have hsum_eq : ∑ p ∈ nzPts n, σ p * (innerProd ψ (pauliApply p ψ)).re =
        Real.sqrt (d + 1) * (d * (innerProd ψ (matApply rt ψ)).re - 1) := by
      rw [hlam_eq]; field_simp [hd_ne, hs_ne]; ring
    have hmono : Real.sqrt (d + 1) * (d * tr3 - 1) ≤
        Real.sqrt (d + 1) * (d * (innerProd ψ (matApply rt ψ)).re - 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hray, hd_pos]) (le_of_lt hs_pos)
    linarith

/-- **Quantitative `cₙ → 2 ⇒ αₙ → 1` Equivalence Half (ALL `n ≥ 2`)**:
    For EVERY `n ≥ 2` and EVERY sign assignment `s` on `W(2n-1, 2)`, letting `d = 2ⁿ` and
    `L = (d² - 1)(d/2 - 1)(d + 2)`, there exists a unit pure state `ψ : QState n` satisfying:
      `√((d - 1) / d) * ((d + 2) / (2 √(d + 1))) * (1 - 2 ρₙ(s)) ≤ pauliAlpha ψ`.
    In particular, if `1 - 2 ρₙ(sₙ) = cₙ / √d` with `cₙ → 2`, then `pauliAlpha ψₙ → 1` linearly
    with no square-root loss (achieving exact equality `α₃ = √(7/8)` on the Hoggar SIC at `n = 3`)!
    Together with `AsymptoticContextuality.signCubeSum_ge_of_L1`, this establishes the exact
    quantitative bidirectional equivalence `limsup αₙ* = 1 ⟺ limsup cₙ* = 2`. -/
theorem exists_unit_state_pauliAlpha_ge_of_frustPairs {n : ℕ} (hn : 2 ≤ n)
    {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    let d : ℝ := (2 : ℝ) ^ n
    let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
    ∃ ψ : QState n, IsUnitState ψ ∧
      Real.sqrt ((d - 1) / d) * ((d + 2) / (2 * Real.sqrt (d + 1))) *
        (1 - 2 * (frustPairs (nzPts n) s : ℝ) / L) ≤ pauliAlpha ψ := by
  intro d L
  let σ : PauliIdx n → ℝ := fun p => (s p : ℝ)
  have hσ0 : σ 0 = 0 := by simp [σ, hs.1]
  have hσpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    rcases hs.2 p hp with h | h <;> simp [σ, h]
  obtain ⟨ψ, hunit, _, hL1⟩ := exists_unit_state_pauliL1_ge_of_signCubeSum σ hσpm
  refine ⟨ψ, hunit, ?_⟩
  have hd_ge4 : (4 : ℝ) ≤ d := by
    have : (4 : ℕ) ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hd_pos : 0 < d := by linarith
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hd_sub_pos : 0 < d - 1 := by linarith
  have hd2_sub_pos : 0 < d - 2 := by linarith
  have hd2_sub_ne : d - 2 ≠ 0 := ne_of_gt hd2_sub_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hT2_pos : 0 < d * (d ^ 2 - 1) := by nlinarith only [hd_ge4]
  have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real hn
  have hL_pos : 0 < L := by
    rw [hL_eq]; exact mul_pos (mul_pos (by nlinarith only [hd_ge4]) (by linarith only [hd_ge4])) (by linarith only [hd_ge4])
  have hbr := (signCubeSum_eq_frustPairs_all (by omega) hσ0 hσpm).2
  have hseq : (fun p : PauliIdx n => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = s := by
    ext p; by_cases hp : p = 0
    · subst hp; simp [hs.1]
    · simp only [hp, ↓reduceIte]
      rcases hs.2 p hp with h | h
      · simp [σ, h]
      · simp only [σ, h]; norm_num
  rw [hseq] at hbr
  have hgap_eq : 1 - 2 * (frustPairs (nzPts n) s : ℝ) / L = 2 * signCubeSum n σ / L := by
    field_simp [ne_of_gt hL_pos]; linarith
  -- Define normalized spectral ratio `β = signCubeSum n σ / S_max ≤ 1`
  let Smax : ℝ := (d ^ 2 - 1) * (d / 2 - 1) * Real.sqrt (d + 1)
  have hSmax_pos : 0 < Smax :=
    mul_pos (mul_pos (by nlinarith only [hd_ge4]) (by linarith only [hd_ge4])) hs_pos
  have hSmax_ne : Smax ≠ 0 := ne_of_gt hSmax_pos
  let β : ℝ := signCubeSum n σ / Smax
  have hβ_le1 : β ≤ 1 := (div_le_one hSmax_pos).mpr (signCubeSum_le_spectral (by omega) σ hσ0 hσpm)
  have hS_eq_β : signCubeSum n σ = β * Smax := (div_mul_cancel₀ _ hSmax_ne).symm
  -- Exact identity: `d * tr3 - 1 = (d - 1) * (β + 2 * (1 - β) / d) ≥ (d - 1) * β`!
  set tr3 : ℝ :=
    (d + 3 * d * (d - 1) +
      (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) / d ^ 3
  have htr3_ident : d * tr3 - 1 = (d - 1) * (β + 2 * (1 - β) / d) := by
    simp only [tr3, hS_eq_β, Smax]
    field_simp [hd_ne, hd1_ne, hs_ne]; ring
  have htr3_ge : (d - 1) * β ≤ d * tr3 - 1 := by
    rw [htr3_ident]
    have hrem_nn : 0 ≤ 2 * (1 - β) / d := div_nonneg (by linarith) (le_of_lt hd_pos)
    nlinarith only [hrem_nn, hd_sub_pos]
  have hL1_ge_β : Real.sqrt (d + 1) * ((d - 1) * β) ≤ pauliL1 ψ := by
    have h1 : Real.sqrt (d + 1) * ((d - 1) * β) ≤ Real.sqrt (d + 1) * (d * tr3 - 1) :=
      mul_le_mul_of_nonneg_left htr3_ge (le_of_lt hs_pos)
    exact le_trans h1 hL1
  have hβ_gap : ((d + 2) / (2 * Real.sqrt (d + 1))) * (1 - 2 * (frustPairs (nzPts n) s : ℝ) / L) = β := by
    rw [hgap_eq, hL_eq]
    simp only [β, Smax]
    have hd2_ne : d + 2 ≠ 0 := by linarith
    have hfac_ne : d ^ 2 - 1 ≠ 0 := by nlinarith only [hd_ge4]
    field_simp [hd2_ne, hfac_ne, hd2_sub_ne, hs_ne]
  rw [mul_assoc, hβ_gap]
  change Real.sqrt ((d - 1) / d) * β ≤ pauliL1 ψ / Real.sqrt (d * (d ^ 2 - 1))
  have hdiv := div_le_div_of_nonneg_right hL1_ge_β (le_of_lt (Real.sqrt_pos.mpr hT2_pos))
  refine le_trans ?_ hdiv
  have hdd1_pos : 0 < d * (d - 1) := mul_pos hd_pos hd_sub_pos
  have hfac : Real.sqrt (d * (d ^ 2 - 1)) = Real.sqrt (d * (d - 1)) * Real.sqrt (d + 1) := by
    rw [show d * (d ^ 2 - 1) = (d * (d - 1)) * (d + 1) by ring,
        Real.sqrt_mul (le_of_lt hdd1_pos)]
  have hsq1 : (d - 1) / Real.sqrt (d * (d - 1)) = Real.sqrt ((d - 1) / d) := by
    have hmul : Real.sqrt (d * (d - 1)) = Real.sqrt d * Real.sqrt (d - 1) :=
      Real.sqrt_mul (le_of_lt hd_pos) _
    rw [hmul, Real.sqrt_div (le_of_lt hd_sub_pos)]
    have hsqd : Real.sqrt (d - 1) * Real.sqrt (d - 1) = d - 1 :=
      Real.mul_self_sqrt (le_of_lt hd_sub_pos)
    have hne1 : Real.sqrt (d - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_sub_pos)
    have hne2 : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
    calc (d - 1) / (Real.sqrt d * Real.sqrt (d - 1))
        = (Real.sqrt (d - 1) * Real.sqrt (d - 1)) / (Real.sqrt d * Real.sqrt (d - 1)) := by rw [hsqd]
      _ = Real.sqrt (d - 1) / Real.sqrt d := by field_simp [hne1, hne2]
  have hsdd_ne : Real.sqrt (d * (d - 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdd1_pos)
  rw [hfac, ← hsq1]
  have heq : Real.sqrt (d + 1) * ((d - 1) * β) / (Real.sqrt (d * (d - 1)) * Real.sqrt (d + 1)) =
      (d - 1) / Real.sqrt (d * (d - 1)) * β := by
    field_simp [hs_ne, hsdd_ne]
  linarith

/-! ### Part 3: Pure-`c_p²` / Bell-Sampling LP Meta-Obstruction (`qSIC` & `sympWHT`) -/

/-- Flat pseudo-SIC probability distribution on `𝔽₂²ⁿ`: `q(0) = 1/d`, `q(p ≠ 0) = 1 / (d (d + 1))`. -/
noncomputable def qSIC (n : ℕ) (p : PauliIdx n) : ℝ :=
  if p = 0 then 1 / (2 : ℝ) ^ n else 1 / ((2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1))

/-- Symplectic Walsh–Hadamard transform `f̂(r) = ∑_p (-1)^{ω(r, p)} f(p)`. -/
noncomputable def sympWHT {n : ℕ} (f : PauliIdx n → ℝ) (r : PauliIdx n) : ℝ :=
  ∑ p : PauliIdx n, (sympSign r p : ℝ) * f p

/-- Orthogonality of symplectic characters on `𝔽₂²ⁿ`. -/
lemma sum_sympSign {n : ℕ} (r : PauliIdx n) :
    ∑ p : PauliIdx n, (sympSign r p : ℝ) = if r = 0 then ((2 : ℝ) ^ n) ^ 2 else 0 := by
  by_cases hr : r = 0
  · subst hr
    simp only [↓reduceIte, sympSign, symp_zero_left, Int.cast_one, Finset.sum_const,
      Finset.card_univ, card_PauliIdx, nsmul_eq_mul, mul_one]
    push_cast; ring
  · simp only [hr, ↓reduceIte]
    have hex : ∃ v : PauliIdx n, symp r v = 1 := by
      by_cases h1 : r.1 ≠ 0
      · have hi : ∃ i : Fin n, r.1 i ≠ 0 := by
          by_contra h; push Not at h; exact h1 (funext h)
        obtain ⟨i, hi⟩ := hi
        refine ⟨(0, eVec i), ?_⟩
        simp only [symp, dot_zero_right, add_zero, dot_eVec_right]
        exact (zmod2_cases (r.1 i)).resolve_left hi
      · push Not at h1
        have h2 : r.2 ≠ 0 := fun h2 => hr (Prod.ext h1 h2)
        have hi : ∃ i : Fin n, r.2 i ≠ 0 := by
          by_contra h; push Not at h; exact h2 (funext h)
        obtain ⟨i, hi⟩ := hi
        refine ⟨(eVec i, 0), ?_⟩
        simp only [symp, dot_zero_right, zero_add, dot_eVec_right]
        exact (zmod2_cases (r.2 i)).resolve_left hi
    obtain ⟨v, hv⟩ := hex
    have hshift : ∑ p : PauliIdx n, (sympSign r p : ℝ) =
        ∑ p : PauliIdx n, (sympSign r (p + v) : ℝ) :=
      (Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)).symm
    have hneg : ∑ p : PauliIdx n, (sympSign r (p + v) : ℝ) =
        -(∑ p : PauliIdx n, (sympSign r p : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [sympSign_add_right]
      have hrv : sympSign r v = -1 := by
        simp [sympSign, hv, show (1 : ZMod 2) ≠ 0 by decide]
      rw [hrv]; push_cast; ring
    linarith

/-- Symplectic WHT of any two-valued function `f(p) = if p = 0 then a else b`. -/
lemma sympWHT_two_valued {n : ℕ} (a b : ℝ) (r : PauliIdx n) :
    sympWHT (fun p : PauliIdx n => if p = 0 then a else b) r =
      (a - b) + b * (if r = 0 then ((2 : ℝ) ^ n) ^ 2 else 0) := by
  have hsplit : ∀ p : PauliIdx n,
      (sympSign r p : ℝ) * (if p = 0 then a else b) =
        (if p = 0 then a - b else 0) + b * (sympSign r p : ℝ) := fun p => by
    by_cases hp : p = 0
    · subst hp; simp [sympSign, symp_zero_right]
    · simp [hp]; ring
  simp only [sympWHT]
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_sympSign, Finset.sum_ite_eq' Finset.univ (0 : PauliIdx n)]
  simp

theorem qSIC_nonneg (n : ℕ) (p : PauliIdx n) : 0 ≤ qSIC n p := by
  simp only [qSIC]; split_ifs <;> positivity

theorem sum_qSIC_eq_one (n : ℕ) : ∑ p : PauliIdx n, qSIC n p = 1 := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  have hd1_ne : d + 1 ≠ 0 := by positivity
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  have h0 : qSIC n 0 = 1 / d := by simp [qSIC, d]
  have hcard : ((nzPts n).card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  have hrest : ∑ p ∈ nzPts n, qSIC n p = (d ^ 2 - 1) * (1 / (d * (d + 1))) := by
    have ht : ∀ p ∈ nzPts n, qSIC n p = 1 / (d * (d + 1)) := fun p hp => by
      have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
      simp [qSIC, hp0, d]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcard]
  change qSIC n 0 + ∑ p ∈ nzPts n, qSIC n p = 1
  rw [h0, hrest]; field_simp [hd_ne, hd1_ne]; ring

/-- **Exact Symplectic Self-Duality of `qSIC`**: `sympWHT (qSIC n) r = 2ⁿ * qSIC n r`. -/
theorem sympWHT_qSIC_eq (n : ℕ) (r : PauliIdx n) :
    sympWHT (qSIC n) r = (2 : ℝ) ^ n * qSIC n r := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  have hd1_ne : d + 1 ≠ 0 := by positivity
  change sympWHT (fun p : PauliIdx n => if p = 0 then 1 / d else 1 / (d * (d + 1))) r = _
  rw [sympWHT_two_valued]
  by_cases hr : r = 0
  · subst hr; simp only [↓reduceIte, qSIC, d]; field_simp [hd_ne, hd1_ne]; ring
  · simp only [hr, ↓reduceIte, qSIC, d, mul_zero, add_zero]; field_simp [hd_ne, hd1_ne]; ring

/-- **Higher-Moment Non-Negativity Meta-Obstruction**: for EVERY `n : ℕ`, EVERY exponent `k : ℕ`,
    and EVERY `r : PauliIdx n`, the symplectic WHT of `(qSIC n)^k` is non-negative.
    Thus every pure-`c_p²` / Bell-difference-sampling linear relaxation accepts `qSIC n`. -/
theorem sympWHT_qSIC_pow_nonneg (n k : ℕ) (r : PauliIdx n) :
    0 ≤ sympWHT (fun p : PauliIdx n => (qSIC n p) ^ k) r := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_pos : 0 < d := by positivity
  have hfun : (fun p : PauliIdx n => (qSIC n p) ^ k) =
      (fun p : PauliIdx n => if p = 0 then (1 / d) ^ k else (1 / (d * (d + 1))) ^ k) := by
    ext p; by_cases hp : p = 0 <;> simp [qSIC, hp, d]
  rw [hfun, sympWHT_two_valued]
  have hle : 1 / (d * (d + 1)) ≤ 1 / d := by
    rw [div_le_div_iff₀ (by positivity) hd_pos]
    nlinarith
  have hpow : (1 / (d * (d + 1))) ^ k ≤ (1 / d) ^ k :=
    pow_le_pow_left₀ (by positivity) hle k
  have h2 : 0 ≤ (1 / (d * (d + 1))) ^ k * (if r = 0 then d ^ 2 else 0) := by
    split_ifs <;> positivity
  linarith

/-- `qSIC n` achieves the exact Welch/SIC 4th moment `2 d / (d + 1)`. -/
theorem qSIC_moment4_eq_welch (n : ℕ) :
    ((2 : ℝ) ^ n) ^ 2 * ∑ p : PauliIdx n, (qSIC n p) ^ 2 =
      2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1) := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd_ne : d ≠ 0 := by positivity
  have hd1_ne : d + 1 ≠ 0 := by positivity
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
  have h0 : (qSIC n 0) ^ 2 = 1 / d ^ 2 := by simp [qSIC, d]
  have hcard : ((nzPts n).card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  have hrest : ∑ p ∈ nzPts n, (qSIC n p) ^ 2 = (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1) ^ 2)) := by
    have ht : ∀ p ∈ nzPts n, (qSIC n p) ^ 2 = 1 / (d ^ 2 * (d + 1) ^ 2) := fun p hp => by
      have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
      simp only [qSIC, hp0, ↓reduceIte, d, div_pow, one_pow, mul_pow]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcard]
  change d ^ 2 * ((qSIC n 0) ^ 2 + ∑ p ∈ nzPts n, (qSIC n p) ^ 2) = 2 * d / (d + 1)
  rw [h0, hrest]; field_simp [hd_ne, hd1_ne]; ring

/-! ### Part 4: Gaussian-Integer Parity Congruence & Stabilizer-Basis IPR Obstruction -/

private lemma pauliExpand_apply_add {n : ℕ} (a : PauliIdx n → ℝ) (x u : F2 n) :
    pauliExpand a x (x + u) =
      ∑ b : F2 n, (a (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) := by
  simp only [pauliExpand, pauliMat, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u]
  · refine Finset.sum_congr rfl fun b _ => by simp [mul_assoc]
  · intro u' _ hu'
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : x + u ≠ x + u' := fun h => hu' (by
      have := congr_arg (x + ·) h; simpa [f2_add_cancel_left] using this.symm)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Diagonal Parity of Pauli Sign Matrices (ALL `n ≥ 1`)**:
    Every diagonal entry `(pauliExpand σ) x x` of a `±1` Pauli sign matrix (`σ 0 = 0`) is an
    odd real integer `2 m + 1`. -/
theorem signMat_diag_odd_int {n : ℕ} (hn : 1 ≤ n) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) (x : F2 n) :
    ∃ m : ℤ, pauliExpand σ x x = ((2 * m + 1 : ℤ) : ℂ) := by
  let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
  have hs_cast : ∀ p : PauliIdx n, (σ p : ℂ) = (s p : ℂ) := fun p => by
    by_cases hp : p = 0
    · subst hp; simp [s, h0]
    · simp only [s, hp, ↓reduceIte]
      rcases hpm p hp with h | h
      · simp [h]
      · rw [h]; norm_num
  have hdiag : pauliExpand σ x x =
      ((∑ b ∈ Finset.univ.erase (0 : F2 n), s (0, b) * chi b x : ℤ) : ℂ) := by
    have hx := pauliExpand_apply_add σ x 0
    rw [add_zero] at hx
    rw [hx, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    have h0term : (σ ((0 : F2 n), (0 : F2 n)) : ℂ) * pauliPh ((0 : F2 n), (0 : F2 n)) * (chi (0 : F2 n) x : ℂ) = 0 := by
      have : ((0 : F2 n), (0 : F2 n)) = (0 : PauliIdx n) := rfl
      rw [this, h0]; simp
    rw [h0term, zero_add, Int.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hs_cast (0, b)]
    simp [pauliPh, dot_zero_left]
  let S := Finset.univ.erase (0 : F2 n)
  have hpm_b : ∀ b ∈ S, s (0, b) * chi b x = 1 ∨ s (0, b) * chi b x = -1 := fun b hb => by
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have hp0 : ((0 : F2 n), b) ≠ (0 : PauliIdx n) := fun hc => hb0 (congr_arg Prod.snd hc)
    have hs1 : s (0, b) = 1 ∨ s (0, b) = -1 := by
      simp only [s, hp0, ↓reduceIte]; split_ifs <;> simp
    rcases hs1 with h1 | h1 <;> rcases chi_eq_one_or_neg_one b x with h2 | h2 <;> simp [h1, h2]
  have hpar := sum_signs_parity S (fun b => s (0, b) * chi b x) hpm_b
  have hcard : S.card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
  have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  obtain ⟨k, hk⟩ := h2dvd
  have hk_pos : 1 ≤ k := by
    have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hodd : (∑ b ∈ S, s (0, b) * chi b x) % 2 = 1 := by
    rw [hpar, hcard, hk]; omega
  refine ⟨(∑ b ∈ S, s (0, b) * chi b x) / 2, ?_⟩
  rw [hdiag]
  change ((∑ b ∈ S, s (0, b) * chi b x : ℤ) : ℂ) = _
  congr 1; omega

/-- **Off-Diagonal Evenness of Pauli Sign Matrices (ALL `n ≥ 2`)**:
    Every off-diagonal entry `(pauliExpand σ) x y` (`x ≠ y`) of a `±1` Pauli sign matrix has
    BOTH real and imaginary parts even integers: `S_{x, y} = 2 m + 2 l i`. -/
theorem signMat_offdiag_even_re_im {n : ℕ} (hn : 2 ≤ n) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1)
    {x y : F2 n} (hxy : x ≠ y) :
    ∃ m l : ℤ, pauliExpand σ x y = ((2 * m : ℤ) : ℂ) + ((2 * l : ℤ) : ℂ) * Complex.I := by
  let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
  have hs_cast : ∀ p : PauliIdx n, (σ p : ℂ) = (s p : ℂ) := fun p => by
    by_cases hp : p = 0
    · subst hp; simp [s, h0]
    · simp only [s, hp, ↓reduceIte]
      rcases hpm p hp with h | h
      · simp [h]
      · rw [h]; norm_num
  let u : F2 n := x + y
  have hu0 : u ≠ 0 := fun hc => hxy (by
    have := congr_arg (x + ·) hc; simpa [u, f2_add_cancel_left] using this.symm)
  have hy_eq : y = x + u := by simp [u, f2_add_cancel_left]
  rw [hy_eq, pauliExpand_apply_add]
  let B0 := Finset.univ.filter fun b : F2 n => dot u b = 0
  let B1 := Finset.univ.filter fun b : F2 n => ¬dot u b = 0
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : F2 n => dot u b = 0)]
  have hsum0 : ∑ b ∈ B0, (σ (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) =
      ((∑ b ∈ B0, s (u, b) * chi b x : ℤ) : ℂ) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hdb : dot u b = 0 := (Finset.mem_filter.mp hb).2
    rw [hs_cast (u, b)]
    simp [pauliPh, hdb]
  have hsum1 : ∑ b ∈ B1, (σ (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) =
      ((∑ b ∈ B1, s (u, b) * chi b x : ℤ) : ℂ) * Complex.I := by
    rw [Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hdb : dot u b ≠ 0 := (Finset.mem_filter.mp hb).2
    rw [hs_cast (u, b)]
    simp only [pauliPh, hdb, ↓reduceIte, Int.cast_mul]; ring
  have hpm_all : ∀ b : F2 n, s (u, b) * chi b x = 1 ∨ s (u, b) * chi b x = -1 := fun b => by
    have hp0 : (u, b) ≠ (0 : PauliIdx n) := fun hc => hu0 (congr_arg Prod.fst hc)
    have hs1 : s (u, b) = 1 ∨ s (u, b) = -1 := by
      simp only [s, hp0, ↓reduceIte]; split_ifs <;> simp
    rcases hs1 with h1 | h1 <;> rcases chi_eq_one_or_neg_one b x with h2 | h2 <;> simp [h1, h2]
  -- Prove `Even B1.card` via `even_card_dot_one ⊤ u`, then `Even B0.card` from `B0.card + B1.card = 2ⁿ`!
  have hdim_top : 2 ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2 n)) := by
    rw [finrank_top, Module.finrank_fin_fun]; exact hn
  have hB1_eq : B1 = Finset.univ.filter (fun b : F2 n => b ∈ (⊤ : Submodule (ZMod 2) (F2 n)) ∧ dot b u = 1) := by
    ext b
    simp only [B1, Finset.mem_filter, Finset.mem_univ, Submodule.mem_top, true_and, dot_comm b u]
    constructor
    · intro h; exact (zmod2_cases (dot u b)).resolve_left h
    · intro h; rw [h]; decide
  have hB1_even : Even B1.card := by
    rw [hB1_eq]; exact even_card_dot_one ⊤ u hdim_top
  have hcard_sum : B0.card + B1.card = 2 ^ n := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : F2 n => dot u b = 0) (fun _ => (1 : ℕ))
    simpa only [B0, B1, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, card_F2] using h1
  have hB0_even : Even B0.card := by
    have h2n_even : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    obtain ⟨p, hp⟩ := even_iff_two_dvd.mp h2n_even
    obtain ⟨q, hq⟩ := even_iff_two_dvd.mp hB1_even
    exact even_iff_two_dvd.mpr ⟨p - q, by omega⟩
  have hpar0 : (∑ b ∈ B0, s (u, b) * chi b x) % 2 = 0 := by
    rw [sum_signs_parity B0 _ (fun b _ => hpm_all b)]
    obtain ⟨q, hq⟩ := even_iff_two_dvd.mp hB0_even
    rw [hq]; omega
  have hpar1 : (∑ b ∈ B1, s (u, b) * chi b x) % 2 = 0 := by
    rw [sum_signs_parity B1 _ (fun b _ => hpm_all b)]
    obtain ⟨q, hq⟩ := even_iff_two_dvd.mp hB1_even
    rw [hq]; omega
  let m : ℤ := (∑ b ∈ B0, s (u, b) * chi b x) / 2
  let l : ℤ := (∑ b ∈ B1, s (u, b) * chi b x) / 2
  refine ⟨m, l, ?_⟩
  change ∑ b ∈ B0, (σ (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) +
      ∑ b ∈ B1, (σ (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) = _
  rw [hsum0, hsum1]
  have hm : ∑ b ∈ B0, s (u, b) * chi b x = 2 * m := by omega
  have hl : ∑ b ∈ B1, s (u, b) * chi b x = 2 * l := by omega
  rw [hm, hl]

/-- **Gaussian-Integer Congruence Theorem (`(S(σ) + I) / 2 ∈ M_d(ℤ[i])`, ALL `n ≥ 2`)**:
    For EVERY `n ≥ 2` and EVERY `±1` Pauli sign assignment `σ` (`σ 0 = 0`), every matrix entry
    `(pauliExpand σ + matId n) x y` is divisible by `2` in the Gaussian integers `ℤ[i]`. -/
theorem signMat_add_id_half_gaussInt {n : ℕ} (hn : 2 ≤ n) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1)
    (x y : F2 n) :
    ∃ g : GI, pauliExpand σ x y + matId n x y = 2 * giToComplex g := by
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨m, hm⟩ := signMat_diag_odd_int (by omega) h0 hpm x
    refine ⟨⟨m + 1, 0⟩, ?_⟩
    simp only [hm, matId, ↓reduceIte, giToComplex_mk]
    push_cast; ring
  · obtain ⟨m, l, hml⟩ := signMat_offdiag_even_re_im hn h0 hpm hxy
    refine ⟨⟨m, l⟩, ?_⟩
    simp only [hml, matId, hxy, ↓reduceIte, add_zero, giToComplex_mk]
    push_cast; ring

/-- Computational-basis inverse participation ratio `I₂(ψ) = 2ⁿ ∑_x |ψ_x|⁴`. -/
noncomputable def compBasisIPR {n : ℕ} (ψ : QState n) : ℝ :=
  (2 : ℝ) ^ n * ∑ x : F2 n, (Complex.normSq (ψ x)) ^ 2

/-- **Stabilizer-Basis IPR Parseval Identity (ALL `n : ℕ`)**:
    For EVERY state `ψ : QState n`, the computational-basis IPR equals the sum of squared `Z`-type
    Pauli expectation values:
      `compBasisIPR ψ = ∑ b : F2 n, (⟨ψ | P_{(0, b)} | ψ⟩.re)²`. -/
theorem compBasisIPR_eq_sum_Z_pauliSq {n : ℕ} (ψ : QState n) :
    compBasisIPR ψ = ∑ b : F2 n, (innerProd ψ (pauliApply (0, b) ψ)).re ^ 2 := by
  have hZb : ∀ b : F2 n,
      (innerProd ψ (pauliApply (0, b) ψ)).re =
        ∑ x : F2 n, (chi b x : ℝ) * Complex.normSq (ψ x) := fun b => by
    have hC : innerProd ψ (pauliApply (0, b) ψ) =
        ((∑ x : F2 n, (chi b x : ℝ) * Complex.normSq (ψ x) : ℝ) : ℂ) := by
      simp only [innerProd, pauliApply, pauliPh, dot_zero_left, ↓reduceIte, one_mul, add_zero,
        Complex.ofReal_sum, Complex.ofReal_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hns : star (ψ x) * ψ x = (Complex.normSq (ψ x) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj]
      calc star (ψ x) * ((chi b x : ℂ) * ψ x)
          = (chi b x : ℂ) * (star (ψ x) * ψ x) := by ring
        _ = ((chi b x : ℝ) : ℂ) * (Complex.normSq (ψ x) : ℂ) := by rw [hns]; simp
    rw [hC, Complex.ofReal_re]
  simp_rw [hZb, sq]
  calc compBasisIPR ψ
      = ∑ x : F2 n, (2 : ℝ) ^ n * (Complex.normSq (ψ x) * Complex.normSq (ψ x)) := by
        simp only [compBasisIPR, Finset.mul_sum, sq]
    _ = ∑ x : F2 n, ∑ y : F2 n,
          (if x + y = 0 then (2 : ℝ) ^ n else 0) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · simp [f2_add_self]
        · intro y _ hy
          have hne : x + y ≠ 0 := fun hc => hy (by
            have := congr_arg (x + ·) hc; simpa [f2_add_cancel_left] using this)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = ∑ x : F2 n, ∑ y : F2 n,
          (∑ b : F2 n, (chi b (x + y) : ℝ)) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        congr 1
        have hsc : ∑ b : F2 n, (chi b (x + y) : ℝ) = ((∑ b : F2 n, chi b (x + y) : ℤ) : ℝ) := by
          rw [Int.cast_sum]
        rw [hsc, sum_chi]
        split_ifs <;> simp
    _ = ∑ b : F2 n, (∑ x : F2 n, (chi b x : ℝ) * Complex.normSq (ψ x)) *
          (∑ y : F2 n, (chi b y : ℝ) * Complex.normSq (ψ y)) := by
        symm
        calc ∑ b : F2 n, (∑ x : F2 n, (chi b x : ℝ) * Complex.normSq (ψ x)) *
              (∑ y : F2 n, (chi b y : ℝ) * Complex.normSq (ψ y))
            = ∑ b : F2 n, ∑ x : F2 n, ∑ y : F2 n,
                (chi b (x + y) : ℝ) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [chi_add_right]; push_cast; ring
          _ = ∑ x : F2 n, ∑ b : F2 n, ∑ y : F2 n,
                (chi b (x + y) : ℝ) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) :=
              Finset.sum_comm
          _ = ∑ x : F2 n, ∑ y : F2 n, ∑ b : F2 n,
                (chi b (x + y) : ℝ) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ x : F2 n, ∑ y : F2 n,
                (∑ b : F2 n, (chi b (x + y) : ℝ)) * (Complex.normSq (ψ x) * Complex.normSq (ψ y)) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.sum_mul ..).symm

/-- **Exact Welch-State IPR Formula (ALL `n : ℕ`)**:
    Any unit state with flat `Z`-type Pauli expectations `c_{(0,b)}² = 1 / (d + 1)` (`b ≠ 0`) has
    exact computational-basis IPR `compBasisIPR ψ = 2 d / (d + 1)` (`→ 2`, strictly separating
    Welch states from flat-amplitude phase states where `I₂ = 1`). -/
theorem compBasisIPR_eq_welch_of_flat_pauli {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ)
    (hflat : ∀ b : F2 n, b ≠ 0 → (innerProd ψ (pauliApply (0, b) ψ)).re ^ 2 = 1 / ((2 : ℝ) ^ n + 1)) :
    compBasisIPR ψ = 2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1) := by
  let d : ℝ := (2 : ℝ) ^ n
  have hd1_ne : d + 1 ≠ 0 := by positivity
  rw [compBasisIPR_eq_sum_Z_pauliSq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
  have h0 : (innerProd ψ (pauliApply ((0 : F2 n), (0 : F2 n)) ψ)).re ^ 2 = 1 := by
    have : ((0 : F2 n), (0 : F2 n)) = (0 : PauliIdx n) := rfl
    rw [this, pauliExpect_zero_re hunit]; norm_num
  have hcard : ((Finset.univ.erase (0 : F2 n)).card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hrest : ∑ b ∈ Finset.univ.erase (0 : F2 n), (innerProd ψ (pauliApply (0, b) ψ)).re ^ 2 =
      (d - 1) * (1 / (d + 1)) := by
    rw [Finset.sum_congr rfl (fun b hb => hflat b (Finset.mem_erase.mp hb).1),
        Finset.sum_const, nsmul_eq_mul, hcard]
  rw [h0, hrest]; field_simp [hd1_ne]; ring

/-- **Quantitative Welch-Approach IPR Separation (ALL `n : ℕ`)**:
    For EVERY unit state `ψ : QState n` (`d = 2ⁿ`),
      `(compBasisIPR ψ - 2 d / (d + 1))² ≤ (d - 1) * (pauliMoment4 n ψ - 2 d / (d + 1))`.
    Hence any sequence with `pauliMoment4 n ψₙ - 2 d / (d + 1) = o(1/d)` forces `compBasisIPR ψₙ → 2`. -/
theorem compBasisIPR_sub_welch_sq_le {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    (compBasisIPR ψ - 2 * d / (d + 1)) ^ 2 ≤
      (d - 1) * (pauliMoment4 n ψ - 2 * d / (d + 1)) := by
  intro d
  have hd1_ne : d + 1 ≠ 0 := by positivity
  let S : Finset (F2 n) := Finset.univ.erase (0 : F2 n)
  let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  have hcard : (S.card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1]; push_cast; rfl
  have hdiff : compBasisIPR ψ - 2 * d / (d + 1) =
      ∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1)) := by
    rw [compBasisIPR_eq_sum_Z_pauliSq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have h0 : (c (0, 0)) ^ 2 = 1 := by
      have : ((0 : F2 n), (0 : F2 n)) = (0 : PauliIdx n) := rfl
      rw [this]; dsimp only [c]; rw [pauliExpect_zero_re hunit]; norm_num
    change (c (0, 0)) ^ 2 + ∑ b ∈ S, (c (0, b)) ^ 2 - 2 * d / (d + 1) =
      ∑ b ∈ S, (c (0, b)) ^ 2 - (d - 1) * (1 / (d + 1))
    rw [h0]; field_simp [hd1_ne]; ring
  have hcs : (∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1))) ^ 2 ≤
      (S.card : ℝ) * ∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1)) ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun b => (c (0, b)) ^ 2 - 1 / (d + 1))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs0
    exact hcs0
  have hsub_le : ∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1)) ^ 2 ≤
      ∑ p ∈ nzPts n, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 := by
    let img : Finset (PauliIdx n) := S.image (fun b => ((0 : F2 n), b))
    have himg_sub : img ⊆ nzPts n := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
      exact Finset.mem_erase.mpr ⟨fun hc => hb0 (congr_arg Prod.snd hc), Finset.mem_univ _⟩
    have himg_eq : ∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1)) ^ 2 =
        ∑ p ∈ img, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 := by
      symm
      exact Finset.sum_image (fun b₁ _ b₂ _ h => congr_arg Prod.snd h)
    rw [himg_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => sq_nonneg _)
  rw [hdiff, pauliMoment4_sub_welch hunit]
  have hd_sub_nn : 0 ≤ d - 1 := by
    have h1 : (1 : ℝ) ≤ d := by
      have : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      dsimp only [d]; exact_mod_cast this
    linarith
  calc (∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1))) ^ 2
      ≤ (d - 1) * ∑ b ∈ S, ((c (0, b)) ^ 2 - 1 / (d + 1)) ^ 2 := by rwa [hcard] at hcs
    _ ≤ (d - 1) * ∑ p ∈ nzPts n, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsub_le hd_sub_nn

end AsymptoticBarriers

-- Re-export main theorems at `MultiQubitMUB` root namespace for clean Audit access.
export AsymptoticBarriers (
  pow_two_add_one_ne_sq
  sqrt_pow_two_add_one_ne_rat
  signCubeSum_lt_spectral
  frustPairs_gt_spectral
  no_pauli_sic_via_cubic_trace
  pauliL1
  pauliAlpha
  pauliL1_ge_of_pauliMoment4
  pauliAlpha_ge_of_pauliMoment4
  exists_unit_state_rayleigh_ge_cube
  exists_unit_state_pauliL1_ge_of_signCubeSum
  exists_unit_state_pauliAlpha_ge_of_frustPairs
  qSIC
  sympWHT
  qSIC_nonneg
  sum_qSIC_eq_one
  sympWHT_qSIC_eq
  sympWHT_qSIC_pow_nonneg
  qSIC_moment4_eq_welch
  signMat_diag_odd_int
  signMat_offdiag_even_re_im
  signMat_add_id_half_gaussInt
  compBasisIPR
  compBasisIPR_eq_sum_Z_pauliSq
  compBasisIPR_eq_welch_of_flat_pauli
  compBasisIPR_sub_welch_sq_le
)

end MultiQubitMUB
