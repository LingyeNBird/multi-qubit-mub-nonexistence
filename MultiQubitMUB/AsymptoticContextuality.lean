import MultiQubitMUB.GeneralContextualityLift

/-!
# Asymptotic Pauli Contextuality (`1 - 2ρₙ = Θ(2⁻ⁿ/²)`) and the `c = 2` Barrier Equivalence

Proves four general-`n` pure-theory theorems (zero `sorry`, zero `native_decide`,
standard three Lean axioms `[propext, Classical.choice, Quot.sound]` only):

1. **Universal Spectral Contextuality Upper Bounds (`signCubeSum_le_spectral`,
   `frustPairs_ge_spectral`, `elliptic_frustPairs_ge_spectral`)**:
   Using only the shifted Pauli sign operator `rt = (1/d) I + (1/(d√(d+1))) ∑_{p≠0} σ_p P_p`
   (`frobSq rt = 1`, `Tr(rt³) ≤ 1`) and its Kramers elliptic-quadric restriction (`frobSq rtc = 1/2`,
   `Tr(rtc³) ≤ 1/4`), proves for EVERY `n ≥ 2` on `W(2n-1, 2)` and EVERY `n ≥ 3` on EVERY elliptic
   quadric `Q⁻(2n-1, 2)`:
     `1 - 2 ρₙ(s) ≤ 2 √(2ⁿ + 1) / (2ⁿ + 2) < 2 · 2⁻ⁿ/²`,
   reproducing exact `CD(W(5,2)) ≥ 63` and `CD(Q⁻(5,2)) ≥ 9` at `n = 3`, beating `5/17` for all
   `n ≥ 5`, and establishing `lim_{n → ∞} ρₙ = 1/2`.

2. **Matrix-Free `c = 2` Barrier Equivalence (`matTr_cube_ge_of_rayleigh`,
   `signCubeSum_ge_of_L1`, `pauliMoment4_ge_of_contextuality_const`)**:
   Purely matrix-free rank-1 block decomposition `S = μ P + X + B` proves unconditionally:
     `μ³ - (frobSq S - μ²)^(3/2) ≤ (Tr(S³)).re`  whenever `0 ≤ μ` and `frobSq S ≤ 2 μ²`.
   Consequently, any general-`n` contextuality upper bound `1 - 2 ρₙ(σ) ≤ c · 2⁻ⁿ/²` with `c < 2`
   forces `pauliMoment4 n ψ ≥ 1 + (d - 1)² / (x² d (d + 1)) → 1 + 1/x² > 2` (where
   `x³ - (1 - x²)^(3/2) = c/2`, `x < 1`).

3. **Exact Asymptotic Lower Bound `1 - 2 ρₙ = Ω(2⁻ⁿ/²)` (`avg_pauliExpect_z4Phase_eq_centralBinom`,
   `exists_signAssign_omega_inv_sqrt`)**:
   By exact finite averaging over all `4^(2ⁿ)` `ℤ₄`-phase states `|ψ_f⟩ = d⁻¹/² ∑_x i^{f(x)} |x⟩`
   (reducing every Pauli expectation `a ≠ 0` to a `d`-step symmetric `±1` random walk of exact mean
   `C(d, d/2) / 2^d`), combined with `(4m + 1) (C(2m, m) / 2^(2m))² ≥ 5/4` and
   `matTr_cube_ge_of_rayleigh`, proves unconditionally for EVERY `n ≥ 4`:
     `∃ s, IsSignAssign s ∧ (1 / 7) / √(2ⁿ) ≤ 1 - 2 ρₙ(s)`.
   Combined with Theorem 1, this completely resolves the exact asymptotic scaling `1 - 2 ρₙ = Θ(2⁻ⁿ/²)`.

4. **Exact All-`n` Spike Frustration Formula & Asymptotic Suboptimality (`frustPairs_spikeSign_all`,
   `spikeSign_frust_gap_eq`, `spikeSign_strictly_suboptimal_asymptotic`)**:
   Generalizes the linear-functional fiber proof to all `n ≥ 2`:
     `1 - 2 ρₙ(spikeSign n) = 9 (2ⁿ - 2) / ((2ⁿ + 1)(2ⁿ + 2)) = Θ(2⁻ⁿ)`,
   proving unconditionally that `spikeSign n` is strictly suboptimal for all `n ≥ 12`.
-/

namespace MultiQubitMUB

open scoped Classical
open FourQubitCD
open GeneralContextualityLift

namespace AsymptoticContextuality

/-! ### Part 1: Universal Spectral Contextuality Upper Bounds (`W(2n-1, 2)` and `Q⁻(2n-1, 2)`) -/

/-- **Universal Spectral Upper Bound on `signCubeSum` (ALL `n ≥ 1`)**:
    For every `n ≥ 1` and every `±1` sign assignment `σ : PauliIdx n → ℝ` (`σ 0 = 0`),
      `signCubeSum n σ ≤ ((2^n)^2 - 1) * (2^n / 2 - 1) * √(2^n + 1)`. -/
theorem signCubeSum_le_spectral {n : ℕ} (_hn : 1 ≤ n)
    (σ : PauliIdx n → ℝ) (_h0 : σ 0 = 0)
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    signCubeSum n σ ≤
      (((2 : ℝ) ^ n) ^ 2 - 1) * ((2 : ℝ) ^ n / 2 - 1) * Real.sqrt ((2 : ℝ) ^ n + 1) := by
  let d : ℝ := (2 : ℝ) ^ n
  let r : ℝ := 1 / Real.sqrt (d + 1)
  let U : Finset (PauliIdx n) := Finset.univ.erase (0 : PauliIdx n)
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
  let a : PauliIdx n → ℝ := fun p => if p = 0 then 1 / d else (r / d) * σ p
  let rt := pauliExpand a
  have hrt_frob : frobSq rt = 1 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have ha0 : (a 0) ^ 2 = 1 / d ^ 2 := by simp [a]
    have hrest : ∑ p ∈ U, (a p) ^ 2 = (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
      have ht : ∀ p ∈ U, (a p) ^ 2 = 1 / (d ^ 2 * (d + 1)) := fun p hp => by
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
        simp only [a, hp0, ↓reduceIte, mul_pow, div_pow, hσ_sq p hp, mul_one, hr2]
        field_simp [hd_ne, hd1_ne]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcardU]
    rw [ha0, hrest]; field_simp [hd_ne, hd1_ne]; ring
  let a2 : PauliIdx n → ℝ := fun q =>
    if q = 0 then 1 / d
    else (2 * r / d ^ 2) * σ q +
      (2 * r ^ 2 / d ^ 2) * ((1 / 2 : ℝ) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))
  have hrt2 : matMul rt rt = pauliExpand a2 := by
    rw [matMul_pauliExpand_self]
    congr 1; ext q
    by_cases hq : q = 0
    · subst hq
      simp only [a2, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
      have ht0 : (pauliPhase (0 : PauliIdx n) 0).re * a 0 * a (0 + 0) = 1 / d ^ 2 := by
        simp [a, pauliPhase_zero_left]; ring
      have hrest : ∑ p ∈ U, (pauliPhase 0 p).re * a p * a (0 + p) =
          (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
        have ht : ∀ p ∈ U, (pauliPhase 0 p).re * a p * a (0 + p) =
            1 / (d ^ 2 * (d + 1)) := fun p hp => by
          have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
          rw [pauliPhase_zero_left, Complex.one_re, zero_add, one_mul]
          simp only [a, hp0, ↓reduceIte]
          have : (r / d * σ p) * (r / d * σ p) = (r ^ 2 / d ^ 2) * (σ p) ^ 2 := by ring
          rw [this, hσ_sq p hp, hr2]; field_simp [hd_ne, hd1_ne]
        rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, hcardU]
      rw [ht0, hrest]; field_simp [hd_ne, hd1_ne]; ring
    · have hqU : q ∈ U := Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
      simp only [a2, hq, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)),
          ← Finset.add_sum_erase _ _ hqU]
      have ht0 : (pauliPhase q 0).re * a 0 * a (q + 0) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_zero_right, Complex.one_re, add_zero]
        simp only [a, ↓reduceIte, hq]; ring
      have htq : (pauliPhase q q).re * a q * a (q + q) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self]
        simp only [a, ↓reduceIte, hq]; ring
      have hrest : ∑ p ∈ U.erase q, (pauliPhase q p).re * a p * a (q + p) =
          (r ^ 2 / d ^ 2) * ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have hqp0 : q + p ≠ 0 := fun hc => hpq (by
          have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
        simp only [a, hp0, hqp0, ↓reduceIte]; ring
      rw [ht0, htq, hrest]; ring
  have htr3 : (matTr (matMul rt (matMul rt rt))).re =
      (d + 3 * d * (d - 1) + (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ) / d ^ 3 := by
    rw [hrt2, matTr_pauliExpand_mul]
    have hre : ((2 : ℂ) ^ n * ∑ p : PauliIdx n, ((a p * a2 p : ℝ) : ℂ)).re =
        d * ∑ p : PauliIdx n, a p * a2 p := by
      have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
      rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0' : a 0 * a2 0 = 1 / d ^ 2 := by simp [a, a2]; ring
    have hrest : ∑ q ∈ U, a q * a2 q =
        (d ^ 2 - 1) * (2 * r ^ 2 / d ^ 3) + (2 * r ^ 3 / d ^ 3) * signCubeSum n σ := by
      have ht : ∀ q ∈ U, a q * a2 q =
          2 * r ^ 2 / d ^ 3 +
            (2 * r ^ 3 / d ^ 3) * (σ q * ((1 / 2 : ℝ) *
              ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p))) := fun q hq => by
        have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
        simp only [a, a2, hq0, ↓reduceIte]
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
    rw [h0', hrest, hr2, hr3]; field_simp [hd_ne, hd1_ne, hs_ne]; ring
  have hle1 : (matTr (matMul rt (matMul rt rt))).re ≤ 1 := by
    have h := matTr_cube_re_le rt
    rw [hrt_frob, Real.sqrt_one, one_pow] at h; exact h
  rw [htr3] at hle1
  have h1 : d + 3 * d * (d - 1) + (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ ≤ d ^ 3 := by
    simpa only [one_mul] using (div_le_iff₀ (pow_pos hd_pos 3)).mp hle1
  have h2 : (2 * d / ((d + 1) * Real.sqrt (d + 1))) * signCubeSum n σ ≤ d * (d - 1) * (d - 2) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left h2
    (le_of_lt (show 0 < (d + 1) * Real.sqrt (d + 1) / (2 * d) by positivity))
  have hlhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) *
      (2 * d / ((d + 1) * Real.sqrt (d + 1)) * signCubeSum n σ) = signCubeSum n σ := by
    field_simp [hd_ne, hd1_ne, hs_ne]
  have hrhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) * (d * (d - 1) * (d - 2)) =
      (d ^ 2 - 1) * (d / 2 - 1) * Real.sqrt (d + 1) := by
    field_simp [hd_ne]; ring
  linarith

/-- Total number of ordered distinct commuting pairs in `W(2n-1, 2)` equals
    `(d^2 - 1) * (d/2 - 1) * (d + 2)` in `ℝ` (`d = 2^n`, `n ≥ 2`). -/
lemma totalCommPairs_real {n : ℕ} (hn : 2 ≤ n) :
    (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) =
      (((2 : ℝ) ^ n) ^ 2 - 1) * ((2 : ℝ) ^ n / 2 - 1) * ((2 : ℝ) ^ n + 2) := by
  have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2 ≤ 2 ^ (2 * n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]
  push_cast
  have hp1 : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by rw [pow_mul']
  have hp2 : (2 : ℝ) ^ (2 * n - 1) = ((2 : ℝ) ^ n) ^ 2 / 2 := by
    have heq : 2 * (2 : ℝ) ^ (2 * n - 1) = (2 : ℝ) ^ (2 * n) := by
      conv_rhs => rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_succ]
      ring
    linarith [hp1]
  rw [hp1, hp2]; ring

/-- **Universal Spectral Contextuality Density Bound (ALL `n ≥ 2`)**:
    For every `n ≥ 2` and every `s : PauliIdx n → ℤ` with `IsSignAssign s`,
      `1 - 2 * ρₙ(s) ≤ 2 √(2ⁿ + 1) / (2ⁿ + 2)`.
    In particular, `ρ₃ ≥ 1/5` (`CD(W(5,2)) ≥ 63` exact), `ρ₅ ≥ 0.33104 > 5/17`, and `lim ρₙ = 1/2`. -/
theorem frustPairs_ge_spectral {n : ℕ} (hn : 2 ≤ n) {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    1 - 2 * (frustPairs (nzPts n) s : ℝ) /
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) ≤
      2 * Real.sqrt ((2 : ℝ) ^ n + 1) / ((2 : ℝ) ^ n + 2) := by
  let d : ℝ := (2 : ℝ) ^ n
  let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
  let σ : PauliIdx n → ℝ := fun p => (s p : ℝ)
  have h0 : σ 0 = 0 := by simp [σ, hs.1]
  have hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    rcases hs.2 p hp with h | h <;> simp [σ, h]
  have hbridge := (signCubeSum_eq_frustPairs_all (by omega) h0 hpm).2
  have hseq : (fun p : PauliIdx n => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = s := by
    ext p; by_cases hp : p = 0
    · subst hp; simp [hs.1]
    · simp only [hp, ↓reduceIte]
      rcases hs.2 p hp with h | h
      · simp [σ, h]
      · simp only [σ, h]; norm_num
  rw [hseq] at hbridge
  have hspec := signCubeSum_le_spectral (by omega) σ h0 hpm
  have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real hn
  have hd_ge4 : (4 : ℝ) ≤ d := by
    have : (4 : ℕ) ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hfac_pos : 0 < (d ^ 2 - 1) * (d / 2 - 1) := by nlinarith only [hd_ge4]
  have hd2_pos : 0 < d + 2 := by linarith
  have hL_pos : 0 < L := by rw [hL_eq]; exact mul_pos hfac_pos hd2_pos
  have h1 : 1 - 2 * (frustPairs (nzPts n) s : ℝ) / L = 2 * signCubeSum n σ / L := by
    field_simp [ne_of_gt hL_pos]; linarith
  rw [h1]
  calc 2 * signCubeSum n σ / L
      ≤ 2 * ((d ^ 2 - 1) * (d / 2 - 1) * Real.sqrt (d + 1)) / L := by
        gcongr
    _ = 2 * Real.sqrt (d + 1) / (d + 2) := by
        have h1' : d ^ 2 - 1 ≠ 0 := by nlinarith only [hd_ge4]
        have h2' : d - 2 ≠ 0 := by linarith only [hd_ge4]
        rw [hL_eq]; field_simp [h1', h2', ne_of_gt hd2_pos]

/-- Strict universal `c = 2` spectral barrier: `1 - 2 ρₙ(s) < 2 / √(2ⁿ)` for all `n ≥ 2`. -/
theorem frustPairs_ge_spectral_two_inv_sqrt {n : ℕ} (hn : 2 ≤ n)
    {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    1 - 2 * (frustPairs (nzPts n) s : ℝ) /
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) <
      2 / Real.sqrt ((2 : ℝ) ^ n) := by
  refine lt_of_le_of_lt (frustPairs_ge_spectral hn hs) ?_
  let d : ℝ := (2 : ℝ) ^ n
  have hd_pos : 0 < d := by positivity
  have hs_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have hd2_pos : 0 < d + 2 := by linarith
  rw [div_lt_div_iff₀ hd2_pos hs_pos]
  have hsq : (Real.sqrt (d + 1) * Real.sqrt d) ^ 2 < (d + 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (le_of_lt hd_pos)]
    nlinarith
  have hlt : Real.sqrt (d + 1) * Real.sqrt d < d + 2 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (d + 1)) (Real.sqrt_nonneg d)]
  linarith

/-- Sign-cube sum restricted to an elliptic quadric `Q⁻(2n-1, 2)` centered at `c0` (`Q_0(c0) = 1`). -/
noncomputable def ellipticSignCubeSum {n : ℕ} (c0 : PauliIdx n) (σ : PauliIdx n → ℝ) : ℝ :=
  ∑ q ∈ Qminus c0,
    σ q * ((1 / 2 : ℝ) * ∑ p ∈ (Qminus c0).erase q, (pauliPhase q p).re * σ p * σ (q + p))

/-- **Universal Kramers Spectral Upper Bound on Elliptic Quadrics `Q⁻(2n-1, 2)` (ALL `n ≥ 3`)**:
    For every `n ≥ 3`, every elliptic center `c0` (`quadForm0 c0 = 1`), and every `±1` sign assignment `σ`,
      `ellipticSignCubeSum c0 σ ≤ (d/2 - 1)(d + 1)(d/4 - 1) √(d + 1)`. -/
theorem ellipticSignCubeSum_le_spectral {n : ℕ} (hn : 3 ≤ n)
    {c0 : PauliIdx n} (hc0 : quadForm0 c0 = 1)
    (σ : PauliIdx n → ℝ) (hpm : ∀ p ∈ Qminus c0, σ p = 1 ∨ σ p = -1) :
    let d : ℝ := (2 : ℝ) ^ n
    ellipticSignCubeSum c0 σ ≤ (d / 2 - 1) * (d + 1) * (d / 4 - 1) * Real.sqrt (d + 1) := by
  intro d
  let r : ℝ := 1 / Real.sqrt (d + 1)
  let Qm : Finset (PauliIdx n) := Qminus c0
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr hd1_pos
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
  have hσ_sq : ∀ p ∈ Qm, (σ p) ^ 2 = 1 := fun p hp => by
    rcases hpm p hp with h | h <;> rw [h] <;> norm_num
  have hQm_eq : Qm = Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c0 p = 0 := by
    ext p; simp [Qm, Qminus, nzPts, and_comm]
  have hcardQm : (Qm.card : ℝ) = (d / 2 - 1) * (d + 1) := by
    rw [hQm_eq]
    have hZ := card_elliptic_quadric hn hc0
    have hR : ((Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c0 p = 0).card : ℝ) =
        ((2 : ℝ) ^ (n - 1) - 1) * (d + 1) := by
      have hcast := congr_arg (Int.cast (R := ℝ)) hZ
      push_cast at hcast; simpa [d] using hcast
    have h2 : (2 : ℝ) ^ (n - 1) = d / 2 := by
      have : d = 2 * (2 : ℝ) ^ (n - 1) := by
        simp only [d]; conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        ring
      linarith
    rw [hR, h2]
  let a : PauliIdx n → ℝ := fun p =>
    if p = 0 then 1 / d else if quadForm c0 p = 0 then (r / d) * σ p else 0
  let rtc := pauliExpand a
  have ha_supp : ∀ p : PauliIdx n, quadForm c0 p ≠ 0 → a p = 0 := fun p hp => by
    have hp0 : p ≠ 0 := fun h => hp (h ▸ quadForm_zero c0)
    simp [a, hp0, hp]
  have hrtc_frob : frobSq rtc = 1 / 2 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have ha0 : (a 0) ^ 2 = 1 / d ^ 2 := by simp [a]
    have hrest : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (a p) ^ 2 =
        (Qm.card : ℝ) * (1 / (d ^ 2 * (d + 1))) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase 0) (fun p => quadForm c0 p = 0)]
      have hz : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => ¬quadForm c0 p = 0),
          (a p) ^ 2 = 0 := Finset.sum_eq_zero fun p hp => by
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).1
        simp [a, hp0, (Finset.mem_filter.mp hp).2]
      rw [hz, add_zero]
      have hflt : (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => quadForm c0 p = 0) = Qm := by
        ext p; simp [Qm, Qminus, nzPts]
      rw [hflt]
      have ht : ∀ p ∈ Qm, (a p) ^ 2 = 1 / (d ^ 2 * (d + 1)) := fun p hp => by
        rw [hQm_eq] at hp
        obtain ⟨hp0, hpQ⟩ := (Finset.mem_filter.mp hp).2
        simp only [a, hp0, hpQ, ↓reduceIte, mul_pow, div_pow, hσ_sq p (hQm_eq ▸ hp), mul_one, hr2]
        field_simp [hd_ne, hd1_ne]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
    rw [ha0, hrest, hcardQm]; field_simp [hd_ne, hd1_ne]; ring
  -- Evaluate `(matTr (rtc^3)).re` directly via `matMul_pauliExpand_self` + `matTr_pauliExpand_mul`!
  have htr3_le : (matTr (matMul rtc (matMul rtc rtc))).re ≤ 1 / 4 :=
    matTr_cube_kramers_le hc0 ha_supp hrtc_frob
  rw [matMul_pauliExpand_self, matTr_pauliExpand_mul] at htr3_le
  have hre : ((2 : ℂ) ^ n * ∑ q : PauliIdx n,
      ((a q * ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) : ℝ) : ℂ)).re =
      d * ∑ q : PauliIdx n, a q * ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) := by
    have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre] at htr3_le
  -- Compute the `q = 0` term and the `q ∈ Qm` terms!
  have hq0 : a 0 * ∑ p : PauliIdx n, (pauliPhase (0 : PauliIdx n) p).re * a p * a (0 + p) =
      1 / (2 * d ^ 2) := by
    have hsum : ∑ p : PauliIdx n, (pauliPhase (0 : PauliIdx n) p).re * a p * a (0 + p) =
        ∑ p : PauliIdx n, (a p) ^ 2 := Finset.sum_congr rfl fun p _ => by
      rw [pauliPhase_zero_left, Complex.one_re, zero_add, one_mul, sq]
    have hsq : ∑ p : PauliIdx n, (a p) ^ 2 = 1 / (2 * d) := by
      have hf := hrtc_frob; rw [frobSq_pauliExpand] at hf
      have : d * ∑ p : PauliIdx n, (a p) ^ 2 = 1 / 2 := hf
      field_simp [hd_ne] at this ⊢; linarith
    rw [hsum, hsq]; simp only [a, ↓reduceIte]; ring
  have hq_rest : ∑ q ∈ Finset.univ.erase (0 : PauliIdx n),
      a q * ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) =
      (Qm.card : ℝ) * (2 * r ^ 2 / d ^ 3) + (2 * r ^ 3 / d ^ 3) * ellipticSignCubeSum c0 σ := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase 0) (fun q => quadForm c0 q = 0)]
    have hz : ∑ q ∈ (Finset.univ.erase (0 : PauliIdx n)).filter (fun q => ¬quadForm c0 q = 0),
        a q * ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) = 0 :=
      Finset.sum_eq_zero fun q hq => by
        rw [ha_supp q (Finset.mem_filter.mp hq).2, zero_mul]
    rw [hz, add_zero]
    have hflt : (Finset.univ.erase (0 : PauliIdx n)).filter (fun q => quadForm c0 q = 0) = Qm := by
      ext q; simp [Qm, Qminus, nzPts]
    rw [hflt]
    have ht : ∀ q ∈ Qm, a q * ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) =
        2 * r ^ 2 / d ^ 3 +
          (2 * r ^ 3 / d ^ 3) * (σ q * ((1 / 2 : ℝ) *
            ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p))) := by
      intro q hq
      have hq' := hQm_eq ▸ hq
      obtain ⟨hq0, hqQ⟩ := (Finset.mem_filter.mp hq').2
      have hinner : ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p) =
          (2 * r / d ^ 2) * σ q +
            (r ^ 2 / d ^ 2) * ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
        have hqU : q ∈ Finset.univ.erase (0 : PauliIdx n) := Finset.mem_erase.mpr ⟨hq0, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hqU]
        have hp0 : (pauliPhase q 0).re * a 0 * a (q + 0) = (r / d ^ 2) * σ q := by
          rw [pauliPhase_zero_right, Complex.one_re, add_zero]
          simp only [a, ↓reduceIte, hq0, hqQ]; ring
        have hpq : (pauliPhase q q).re * a q * a (q + q) = (r / d ^ 2) * σ q := by
          rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self]
          simp only [a, ↓reduceIte, hq0, hqQ]; ring
        have hrem : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).erase q,
            (pauliPhase q p).re * a p * a (q + p) =
            (r ^ 2 / d ^ 2) * ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p) := by
          rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ.erase 0).erase q) (fun p => quadForm c0 p = 0)]
          have hz' : ∑ p ∈ ((Finset.univ.erase (0 : PauliIdx n)).erase q).filter (fun p => ¬quadForm c0 p = 0),
              (pauliPhase q p).re * a p * a (q + p) = 0 := Finset.sum_eq_zero fun p hp => by
            rw [ha_supp p (Finset.mem_filter.mp hp).2]; ring
          rw [hz', add_zero]
          have hf2 : ((Finset.univ.erase (0 : PauliIdx n)).erase q).filter (fun p => quadForm c0 p = 0) =
              Qm.erase q := by
            ext p; simp only [Qm, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
              and_true]; tauto
          rw [hf2, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
          have hpQm := hQm_eq ▸ (Finset.mem_erase.mp hp).2
          obtain ⟨hp0', hpQ⟩ := (Finset.mem_filter.mp hpQm).2
          have hqp0 : q + p ≠ 0 := fun hc => hpne (by
            have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
          rcases zmod2_cases (symp q p) with hsp | hsp
          · have hqpQ : quadForm c0 (q + p) = 0 := by rw [quadForm_add, hqQ, hpQ, hsp]; simp
            simp only [a, hp0', hpQ, hqp0, hqpQ, ↓reduceIte]; ring
          · rw [(pauliPhase_re_cases q p).2 hsp]; ring
        rw [hp0, hpq, hrem]; ring
      rw [hinner]
      simp only [a, hq0, hqQ, ↓reduceIte]
      have hlin : (r / d * σ q) * (2 * r / d ^ 2 * σ q +
            r ^ 2 / d ^ 2 * ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p)) =
          (2 * r ^ 2 / d ^ 3) * (σ q) ^ 2 +
            (2 * r ^ 3 / d ^ 3) * (σ q * ((1 / 2 : ℝ) *
              ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p))) := by ring
      rw [hlin, hσ_sq q hq, mul_one]
    rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)), hq0, hq_rest, hcardQm] at htr3_le
  have hr3 : r ^ 3 = 1 / ((d + 1) * Real.sqrt (d + 1)) := by
    calc r ^ 3 = r ^ 2 * r := by ring
      _ = (1 / (d + 1)) * (1 / Real.sqrt (d + 1)) := by rw [hr2]
      _ = 1 / ((d + 1) * Real.sqrt (d + 1)) := by rw [one_div_mul_one_div]
  rw [hr2, hr3] at htr3_le
  have hclean : 1 / (2 * d) + (d - 2) / d ^ 2 +
      (2 / (d ^ 2 * (d + 1) * Real.sqrt (d + 1))) * ellipticSignCubeSum c0 σ ≤ 1 / 4 := by
    have heq : d * (1 / (2 * d ^ 2) + (d / 2 - 1) * (d + 1) * (2 * (1 / (d + 1)) / d ^ 3) +
        2 * (1 / ((d + 1) * Real.sqrt (d + 1))) / d ^ 3 * ellipticSignCubeSum c0 σ) =
        1 / (2 * d) + (d - 2) / d ^ 2 +
        (2 / (d ^ 2 * (d + 1) * Real.sqrt (d + 1))) * ellipticSignCubeSum c0 σ := by
      field_simp [hd_ne, hd1_ne, hs_ne]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hclean (le_of_lt (show 0 < 4 * d ^ 2 by positivity))
  have hstep : 2 * d + 4 * (d - 2) + (8 / ((d + 1) * Real.sqrt (d + 1))) * ellipticSignCubeSum c0 σ ≤ d ^ 2 := by
    have hl : 4 * d ^ 2 * (1 / (2 * d) + (d - 2) / d ^ 2 +
        2 / (d ^ 2 * (d + 1) * Real.sqrt (d + 1)) * ellipticSignCubeSum c0 σ) =
        2 * d + 4 * (d - 2) + (8 / ((d + 1) * Real.sqrt (d + 1))) * ellipticSignCubeSum c0 σ := by
      field_simp [hd_ne, hd1_ne, hs_ne]; ring
    have hr : 4 * d ^ 2 * (1 / 4 : ℝ) = d ^ 2 := by ring
    linarith
  have h2 : (8 / ((d + 1) * Real.sqrt (d + 1))) * ellipticSignCubeSum c0 σ ≤ (d - 2) * (d - 4) := by
    linarith
  have hmul2 := mul_le_mul_of_nonneg_left h2
    (le_of_lt (show 0 < (d + 1) * Real.sqrt (d + 1) / 8 by positivity))
  have hl2 : (d + 1) * Real.sqrt (d + 1) / 8 *
      (8 / ((d + 1) * Real.sqrt (d + 1)) * ellipticSignCubeSum c0 σ) = ellipticSignCubeSum c0 σ := by
    field_simp [hd1_ne, hs_ne]
  have hr2' : (d + 1) * Real.sqrt (d + 1) / 8 * ((d - 2) * (d - 4)) =
      (d / 2 - 1) * (d + 1) * (d / 4 - 1) * Real.sqrt (d + 1) := by ring
  linarith

/-- **Universal Kramers Elliptic-Quadric Frustration-Density Bound (ALL `n ≥ 3`)**:
    For every `n ≥ 3`, every elliptic center `c0` (`quadForm0 c0 = 1`), and every `IsSignAssign s`,
    letting `L_Q = (2^(n-1) - 1)(2^n + 1) * 2(2^(n-2) - 1)(2^(n-1) + 1)` be the total ordered
    commuting distinct pairs in `Q⁻(2n-1, 2)`,
      `1 - 2 * frustPairs (Qminus c0) s / L_Q ≤ 2 √(2ⁿ + 1) / (2ⁿ + 2) < 2 / √(2ⁿ)`. -/
theorem elliptic_frustPairs_ge_spectral {n : ℕ} (hn : 3 ≤ n)
    {c0 : PauliIdx n} (hc0 : quadForm0 c0 = 1)
    {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    let Lq : ℝ := (((2 ^ (n - 1) - 1) * (2 ^ n + 1) * (2 * ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1))) : ℕ) : ℝ)
    1 - 2 * (frustPairs (Qminus c0) s : ℝ) / Lq ≤
      2 * Real.sqrt ((2 : ℝ) ^ n + 1) / ((2 : ℝ) ^ n + 2) := by
  intro Lq
  let d : ℝ := (2 : ℝ) ^ n
  let Qm : Finset (PauliIdx n) := Qminus c0
  let σ : PauliIdx n → ℝ := fun p => (s p : ℝ)
  have hQm_eq : Qm = Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c0 p = 0 := by
    ext p; simp [Qm, Qminus, nzPts, and_comm]
  have hpm : ∀ p ∈ Qm, σ p = 1 ∨ σ p = -1 := fun p hp => by
    have hp0 : p ≠ 0 := (Finset.mem_filter.mp (hQm_eq ▸ hp)).2.1
    rcases hs.2 p hp0 with h | h <;> simp [σ, h]
  let C := (Qm ×ˢ Qm).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0
  have hC_card : C.card = (2 ^ (n - 1) - 1) * (2 ^ n + 1) * (2 * ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1))) := by
    have hbij : C.card = ∑ q ∈ Qm, (Qm.filter fun p => p ≠ q ∧ symp q p = 0).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun pq _ => ⟨pq.1, pq.2⟩) ?_ ?_ ?_
      · rintro ⟨q, p⟩ hqp
        simp only [C, Finset.mem_filter, Finset.mem_product] at hqp
        simp only [Finset.mem_sigma, Finset.mem_filter]
        exact ⟨hqp.1.1, hqp.1.2, hqp.2.1.symm, hqp.2.2⟩
      · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2
      · rintro ⟨q, p⟩ hqp
        simp only [Finset.mem_sigma, Finset.mem_filter] at hqp
        exact ⟨(q, p), by simp [C, hqp.1, hqp.2.1, hqp.2.2.1.symm, hqp.2.2.2], rfl⟩
    rw [hbij]
    have hinner : ∀ q ∈ Qm, (Qm.filter fun p => p ≠ q ∧ symp q p = 0).card =
        2 * ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1)) := by
      intro q hq
      obtain ⟨hq0, hqQ⟩ := (Finset.mem_filter.mp (hQm_eq ▸ hq)).2
      have hflt : Qm.filter (fun p => p ≠ q ∧ symp q p = 0) =
          Finset.univ.filter (fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ quadForm c0 p = 0 ∧ symp q p = 0) := by
        ext p; simp only [Qm, Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
          true_and, and_true]; tauto
      rw [hflt]; exact card_elliptic_lines_at hn hc0 hq0 hqQ
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    congr 1
    have hZ := card_elliptic_quadric hn hc0
    rw [← hQm_eq] at hZ
    have hge1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    zify [hge1]; exact hZ
  have hbridge : ellipticSignCubeSum c0 σ = (C.card : ℝ) / 2 - (frustPairs Qm s : ℝ) := by
    have hsum_eq : ellipticSignCubeSum c0 σ =
        (1 / 2 : ℝ) * ∑ pq ∈ C, ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) := by
      unfold ellipticSignCubeSum
      have h1 : ∀ q ∈ Qm,
          σ q * ((1 / 2 : ℝ) * ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p)) =
          (1 / 2 : ℝ) * ∑ p ∈ Qm,
            if q ≠ p ∧ symp q p = 0 then ((gammaSgn q p * s q * s p * s (q + p) : ℤ) : ℝ) else 0 := by
        intro q hq
        rw [← mul_assoc, mul_comm (σ q), mul_assoc, Finset.mul_sum]
        refine congr_arg ((1 / 2 : ℝ) * ·) ?_
        rw [← Finset.add_sum_erase Qm _ hq]
        simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hqp : q ≠ p := Ne.symm (Finset.mem_erase.mp hp).1
        rcases zmod2_cases (symp q p) with hsp | hsp
        · simp only [hqp, hsp, not_false_eq_true, and_self, ↓reduceIte,
            pauliPhase_re_eq_gammaSgn hsp, σ]
          push_cast; ring
        · simp only [hqp, hsp, show (1 : ZMod 2) ≠ 0 by decide, and_false, ↓reduceIte,
            (pauliPhase_re_cases q p).2 hsp]; ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_product']
      exact congr_arg ((1 / 2 : ℝ) * ·) (Finset.sum_filter _ _).symm
    have hsum_val : ∑ pq ∈ C, ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) =
        (C.card : ℝ) - 2 * (frustPairs Qm s : ℝ) := by
      have ht : ∀ pq ∈ C,
          ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) =
          1 - 2 * (if gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1 then (1 : ℝ) else 0) := by
        intro pq hpq
        simp only [C, Finset.mem_filter, Finset.mem_product] at hpq
        have hp0 : pq.1 ≠ 0 := (Finset.mem_filter.mp (hQm_eq ▸ hpq.1.1)).2.1
        have hq0 : pq.2 ≠ 0 := (Finset.mem_filter.mp (hQm_eq ▸ hpq.1.2)).2.1
        have hpq0 : pq.1 + pq.2 ≠ 0 := fun h => hpq.2.1 (by
          have := congr_arg (pq.1 + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
        rcases gammaSgn_eq_pm1 pq.1 pq.2 with h1 | h1 <;>
        rcases hs.2 pq.1 hp0 with h2 | h2 <;>
        rcases hs.2 pq.2 hq0 with h3 | h3 <;>
        rcases hs.2 (pq.1 + pq.2) hpq0 with h4 | h4 <;>
        simp [h1, h2, h3, h4] <;> norm_num
      rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
          ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2; refine congr_arg (Nat.cast : ℕ → ℝ) ?_
      unfold frustPairs; refine congr_arg Finset.card (Finset.ext fun pq => ?_)
      simp only [C, Finset.mem_filter]; tauto
    rw [hsum_eq, hsum_val]; ring
  have hLq_eq : Lq = (d / 2 - 1) * (d + 1) * (d / 4 - 1) * (d + 2) := by
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
    dsimp only [Lq]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    have h2n1 : (2 : ℝ) ^ (n - 1) = d / 2 := by
      have : d = 2 * (2 : ℝ) ^ (n - 1) := by
        simp only [d]; conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        ring
      linarith
    have h2n2 : (2 : ℝ) ^ (n - 2) = d / 4 := by
      have : d = 4 * (2 : ℝ) ^ (n - 2) := by
        simp only [d]; conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
        ring
      linarith
    rw [h2n1, h2n2]; ring
  have hd_ge8 : (8 : ℝ) ≤ d := by
    have : (8 : ℕ) ≤ 2 ^ n := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hfac_pos : 0 < (d / 2 - 1) * (d + 1) * (d / 4 - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hd2_pos : 0 < d + 2 := by linarith
  have hLq_pos : 0 < Lq := by rw [hLq_eq]; exact mul_pos hfac_pos hd2_pos
  have hC_cast : (C.card : ℝ) = Lq := by rw [hC_card]
  have h1 : 1 - 2 * (frustPairs Qm s : ℝ) / Lq = 2 * ellipticSignCubeSum c0 σ / Lq := by
    rw [hbridge, hC_cast]; field_simp [ne_of_gt hLq_pos]
  have hspec := ellipticSignCubeSum_le_spectral hn hc0 σ hpm
  dsimp only at hspec
  rw [h1]
  calc 2 * ellipticSignCubeSum c0 σ / Lq
      ≤ 2 * ((d / 2 - 1) * (d + 1) * (d / 4 - 1) * Real.sqrt (d + 1)) / Lq := by gcongr
    _ = 2 * Real.sqrt (d + 1) / (d + 2) := by
        have h1' : d - 2 ≠ 0 := by linarith only [hd_ge8]
        have h2' : d + 1 ≠ 0 := by linarith only [hd_ge8]
        have h3' : d - 4 ≠ 0 := by linarith only [hd_ge8]
        rw [hLq_eq]; field_simp [h1', h2', h3', ne_of_gt hd2_pos]

/-! ### Part 2: Matrix-Free `c = 2` Barrier Equivalence (`∀ n ≥ 2`) -/

private lemma innerProd_matApply_herm_real {n : ℕ} {S : QMat n} (hS : IsHermMat S) (ψ : QState n) :
    innerProd ψ (matApply S ψ) = (((innerProd ψ (matApply S ψ)).re : ℝ) : ℂ) := by
  have hconj : star (innerProd ψ (matApply S ψ)) = innerProd ψ (matApply S ψ) := by
    simp only [innerProd, matApply, star_sum, star_mul, Finset.mul_sum, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← hS y x]; ring
  apply Complex.ext
  · simp
  · have him := congr_arg Complex.im hconj
    simp only [Complex.star_def, Complex.conj_im] at him
    simp; linarith

private lemma isHermMat_mul_three {n : ℕ} {P S : QMat n} (hP : IsHermMat P) (hS : IsHermMat S) :
    IsHermMat (matMul P (matMul S P)) := by
  intro x y
  simp only [matMul, star_sum, star_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hP w y, ← hS z w, ← hP x z]; ring

private lemma matTr_three_zero_of_PQ {n : ℕ} {P Q X Y Z : QMat n}
    (hQP : matMul Q P = fun _ _ => 0) (hPX : matMul P X = X) (hZQ : matMul Z Q = Z) :
    matTr (matMul X (matMul Y Z)) = 0 := by
  calc matTr (matMul X (matMul Y Z))
      = matTr (matMul (matMul P X) (matMul Y (matMul Z Q))) := by rw [hPX, hZQ]
    _ = matTr (matMul P (matMul (matMul X (matMul Y Z)) Q)) := by simp only [matMul_assoc]
    _ = matTr (matMul (matMul (matMul X (matMul Y Z)) Q) P) := matTr_mul_comm _ _
    _ = matTr (matMul (matMul X (matMul Y Z)) (matMul Q P)) := by rw [matMul_assoc]
    _ = 0 := by rw [hQP]; simp [matMul, matTr]

private lemma matTr_three_zero_of_mul_zero {n : ℕ} {X Y Z : QMat n}
    (hXY : matMul X Y = fun _ _ => 0) :
    matTr (matMul X (matMul Y Z)) = 0 := by
  rw [← matMul_assoc, hXY]; simp [matMul, matTr]

private lemma matTr_cube_block_identity {n : ℕ}
    {P Q S A B X1 X2 : QMat n} {μ t : ℝ} {cBX : ℂ}
    (hP2 : matMul P P = P) (hPQ : matMul P Q = fun _ _ => 0) (hQP : matMul Q P = fun _ _ => 0)
    (hP_tr : matTr P = 1) (hA_eq : A = matSmul (μ : ℂ) P)
    (hS_decomp : S = matAdd (matAdd A B) (matAdd X1 X2))
    (hS2_eq : matMul S S =
      matAdd (matAdd (matAdd (matMul A A) (matMul X1 X2)) (matAdd (matMul B B) (matMul X2 X1)))
        (matAdd (matAdd (matMul A X1) (matMul X1 B)) (matAdd (matMul B X2) (matMul X2 A))))
    (hAP : matMul P A = A) (hAP_r : matMul A P = A)
    (hQB : matMul Q B = B) (hBQ : matMul B Q = B)
    (hPX1 : matMul P X1 = X1) (hX1Q : matMul X1 Q = X1)
    (hQX2 : matMul Q X2 = X2) (hX2P : matMul X2 P = X2)
    (hAB : matMul A B = fun _ _ => 0) (hBA : matMul B A = fun _ _ => 0)
    (hAX2 : matMul A X2 = fun _ _ => 0) (hX1A : matMul X1 A = fun _ _ => 0)
    (hBX1 : matMul B X1 = fun _ _ => 0) (hX2B : matMul X2 B = fun _ _ => 0)
    (hX1X1 : matMul X1 X1 = fun _ _ => 0) (hX2X2 : matMul X2 X2 = fun _ _ => 0)
    (hX1X2_tr : matTr (matMul X1 X2) = (t : ℂ))
    (hX1BX2_tr : matTr (matMul B (matMul X2 X1)) = cBX) :
    matTr (matMul S (matMul S S)) =
      ((μ ^ 3 + 3 * μ * t : ℝ) : ℂ) + 3 * cBX + matTr (matMul B (matMul B B)) := by
  set S2 := matAdd (matAdd (matAdd (matMul A A) (matMul X1 X2)) (matAdd (matMul B B) (matMul X2 X1)))
      (matAdd (matAdd (matMul A X1) (matMul X1 B)) (matAdd (matMul B X2) (matMul X2 A)))
  have h1 : matTr (matMul A (matMul A A)) = ((μ ^ 3 : ℝ) : ℂ) := by
    simp only [hA_eq, matMul_smul_left, matMul_smul_right, hP2, matTr_smul, hP_tr]
    push_cast; ring
  have h2 : matTr (matMul A (matMul X1 X2)) = ((μ * t : ℝ) : ℂ) := by
    rw [hA_eq, matMul_smul_left, matTr_smul, ← matMul_assoc P X1 X2, hPX1, hX1X2_tr]
    push_cast; ring
  have htrA : matTr (matMul A S2) = ((μ ^ 3 + μ * t : ℝ) : ℂ) := by
    simp only [S2, matMul_add_right, matTr_add]
    rw [h1, h2, matTr_three_zero_of_mul_zero hAB, matTr_three_zero_of_mul_zero hAX2,
      matTr_three_zero_of_PQ hQP hAP hX1Q, matTr_three_zero_of_PQ hQP hAP hBQ,
      matTr_three_zero_of_mul_zero hAB, matTr_three_zero_of_mul_zero hAX2]
    push_cast; ring
  have htrB : matTr (matMul B S2) = matTr (matMul B (matMul B B)) + cBX := by
    simp only [S2, matMul_add_right, matTr_add]
    rw [matTr_three_zero_of_mul_zero hBA, matTr_three_zero_of_mul_zero hBX1, hX1BX2_tr,
      matTr_three_zero_of_mul_zero hBA, matTr_three_zero_of_mul_zero hBX1,
      matTr_three_zero_of_PQ hPQ hQB hX2P, matTr_three_zero_of_PQ hPQ hQB hAP_r]
    ring
  have htrX1 : matTr (matMul X1 S2) = cBX + ((μ * t : ℝ) : ℂ) := by
    simp only [S2, matMul_add_right, matTr_add]
    have h21 : matTr (matMul X1 (matMul B X2)) = cBX := by
      rw [matTr_mul_comm X1, matMul_assoc, hX1BX2_tr]
    have h22 : matTr (matMul X1 (matMul X2 A)) = ((μ * t : ℝ) : ℂ) := by
      rw [← matMul_assoc, matTr_mul_comm _ A, h2]
    rw [matTr_three_zero_of_mul_zero hX1A, matTr_three_zero_of_mul_zero hX1X1,
      matTr_three_zero_of_PQ hQP hPX1 hBQ, matTr_three_zero_of_PQ hQP hPX1 hX1Q,
      matTr_three_zero_of_mul_zero hX1A, matTr_three_zero_of_mul_zero hX1X1, h21, h22]
    ring
  have htrX2 : matTr (matMul X2 S2) = ((μ * t : ℝ) : ℂ) + cBX := by
    simp only [S2, matMul_add_right, matTr_add]
    have h27 : matTr (matMul X2 (matMul A X1)) = ((μ * t : ℝ) : ℂ) := by
      rw [matTr_mul_comm X2, matMul_assoc, h2]
    have h28 : matTr (matMul X2 (matMul X1 B)) = cBX := by
      rw [← matMul_assoc, matTr_mul_comm _ B, hX1BX2_tr]
    rw [matTr_three_zero_of_PQ hPQ hQX2 hAP_r, matTr_three_zero_of_PQ hPQ hQX2 hX2P,
      matTr_three_zero_of_mul_zero hX2B, matTr_three_zero_of_mul_zero hX2X2,
      h27, h28, matTr_three_zero_of_mul_zero hX2B, matTr_three_zero_of_mul_zero hX2X2]
    ring
  rw [hS2_eq]
  change matTr (matMul S S2) = _
  rw [hS_decomp, matMul_add_left, matMul_add_left, matMul_add_left, matTr_add, matTr_add, matTr_add,
      htrA, htrB, htrX1, htrX2]
  push_cast; ring

/-- **Matrix-Free Rank-1 Block Lower Bound on `Tr(S³)` (Zero Spectral Theorem!)**:
    For ANY Hermitian `S : QMat n` and ANY unit vector `ψ : QState n`, letting
    `μ = (⟨ψ | S | ψ⟩).re` and `T2 = frobSq S`, whenever `0 ≤ μ` and `T2 ≤ 2 * μ²`,
      `μ³ - (√(T2 - μ²))³ ≤ (Tr(S³)).re`. -/
theorem matTr_cube_ge_of_rayleigh {n : ℕ} {S : QMat n} (hS : IsHermMat S)
    {ψ : QState n} (hunit : IsUnitState ψ)
    (hμ_nn : 0 ≤ (innerProd ψ (matApply S ψ)).re)
    (hdom : frobSq S ≤ 2 * (innerProd ψ (matApply S ψ)).re ^ 2) :
    let μ : ℝ := (innerProd ψ (matApply S ψ)).re
    μ ^ 3 - (Real.sqrt (frobSq S - μ ^ 2)) ^ 3 ≤ (matTr (matMul S (matMul S S))).re := by
  intro μ
  let P := stateProj ψ
  let Q := matSub (matId n) P
  have hPh : IsHermMat P := stateProj_herm ψ
  have hQh : IsHermMat Q := isHermMat_sub (isHermMat_id n) hPh
  have hP2 : matMul P P = P := stateProj_idem hunit
  have hPQ : matMul P Q = fun _ _ => 0 := by
    simp only [Q, matMul_sub_right, matMul_id_right, hP2]; ext x y; simp [matSub]
  have hQP : matMul Q P = fun _ _ => 0 := by
    simp only [Q, matMul_sub_left, matMul_id_left, hP2]; ext x y; simp [matSub]
  have hQ2 : matMul Q Q = Q := by
    simp only [Q, matMul_sub_left, matMul_sub_right, matMul_id_left, matMul_id_right, hP2]
    ext x y; simp [matSub]
  have hPQ_add : matAdd P Q = matId n := by ext x y; simp [Q, matAdd, matSub]
  have hzero_l : ∀ M : QMat n, matMul (fun _ _ => (0 : ℂ)) M = fun _ _ => 0 := fun _ => by
    ext x y; simp [matMul]
  have hzero_r : ∀ M : QMat n, matMul M (fun _ _ => (0 : ℂ)) = fun _ _ => 0 := fun _ => by
    ext x y; simp [matMul]
  have htr_zero : matTr (n := n) (fun _ _ => (0 : ℂ)) = 0 := by simp [matTr]
  -- Decompose `S = A + X1 + X2 + B` where `A = P S P = μ P`, `X1 = P S Q`, `X2 = Q S P`, `B = Q S Q`!
  let A := matMul P (matMul S P)
  let X1 := matMul P (matMul S Q)
  let X2 := matMul Q (matMul S P)
  let B := matMul Q (matMul S Q)
  have hAh : IsHermMat A := isHermMat_mul_three hPh hS
  have hBh : IsHermMat B := isHermMat_mul_three hQh hS
  have hA_eq : A = matSmul (μ : ℂ) P := by
    ext x y
    have hcalc : A x y = innerProd ψ (matApply S ψ) * P x y := by
      simp only [A, matMul, P, stateProj, innerProd, matApply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
    rw [hcalc, innerProd_matApply_herm_real hS ψ]; rfl
  have hP_tr : matTr P = 1 := by
    have : matTr P = innerProd ψ ψ := by
      simp only [matTr, P, stateProj, innerProd]
      refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [this, hunit]
  have hS_decomp : S = matAdd (matAdd A B) (matAdd X1 X2) := by
    have h1 : S = matMul (matAdd P Q) (matMul S (matAdd P Q)) := by
      rw [hPQ_add, matMul_id_left, matMul_id_right]
    rw [h1]; simp only [matMul_add_left, matMul_add_right]
    ext x y; simp only [A, B, X1, X2, matAdd]; ring
  -- Define `v = Q (S ψ)` and `t = ⟨v | v⟩.re ≥ 0`!
  let v : QState n := matApply Q (matApply S ψ)
  let t : ℝ := (innerProd v v).re
  have ht_nn : 0 ≤ t := innerProd_self_re_nonneg v
  -- Exact trace `Tr(X1 * X2) = t` and `Tr(X1 * B * X2) = ⟨v | B | v⟩`!
  have hmatApply_mul : ∀ (M N : QMat n) (u : QState n),
      matApply (matMul M N) u = matApply M (matApply N u) := fun M N u => by
    ext x; simp only [matApply, matMul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => mul_assoc _ _ _
  have htr_stateProj : ∀ M : QMat n, matTr (matMul P M) = innerProd ψ (matApply M ψ) := fun M => by
    simp only [matTr, matMul, P, stateProj, innerProd, matApply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hSa : ∀ a b : QState n, innerProd a (matApply S b) = innerProd (matApply S a) b := fun a b => by
    simp only [innerProd, matApply, Finset.mul_sum, star_sum, star_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [← hS x y]; ring
  have hQa : ∀ a b : QState n, innerProd a (matApply Q b) = innerProd (matApply Q a) b := fun a b => by
    simp only [innerProd, matApply, Finset.mul_sum, star_sum, star_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [← hQh x y]; ring
  have hX1X2_tr : matTr (matMul X1 X2) = (t : ℂ) := by
    have h1 : matMul X1 X2 = matMul (matMul P (matMul S (matMul Q S))) P := by
      simp only [X1, X2, matMul_assoc, ← matMul_assoc Q Q, hQ2]
    rw [h1, matTr_mul_comm _ P, ← matMul_assoc P P, hP2, htr_stateProj]
    have hinner : innerProd ψ (matApply (matMul S (matMul Q S)) ψ) = innerProd v v := by
      rw [hmatApply_mul, hmatApply_mul, hSa]
      have hQQ : matApply Q (matApply Q (matApply S ψ)) = matApply Q (matApply S ψ) := by
        rw [← hmatApply_mul, hQ2]
      rw [← hQQ, hQa]
    rw [hinner, innerProd_self_eq_sum_normSq, ← innerProd_self_re]
  have hX1BX2_tr : matTr (matMul B (matMul X2 X1)) = innerProd v (matApply B v) := by
    have h1 : matMul B (matMul X2 X1) = matMul B (matMul Q (matMul S (matMul P (matMul S Q)))) := by
      simp only [X1, X2, matMul_assoc, ← matMul_assoc P P, hP2]
    rw [h1, matTr_mul_comm B, matMul_assoc, matMul_assoc, matMul_assoc, matMul_assoc]
    have h2 : matTr (matMul Q (matMul S (matMul P (matMul S (matMul Q B))))) =
        matTr (matMul P (matMul S (matMul Q (matMul B (matMul Q S))))) := by
      calc matTr (matMul Q (matMul S (matMul P (matMul S (matMul Q B)))))
          = matTr (matMul (matMul Q S) (matMul P (matMul S (matMul Q B)))) := by simp only [matMul_assoc]
        _ = matTr (matMul (matMul P (matMul S (matMul Q B))) (matMul Q S)) := matTr_mul_comm _ _
        _ = _ := by simp only [matMul_assoc]
    rw [h2, htr_stateProj]
    simp only [hmatApply_mul]
    rw [hSa, hQa]
  -- Pairwise multiplication table for `{A, B, X1, X2}`!
  have hAB : matMul A B = fun _ _ => 0 := by
    simp only [A, B, matMul_assoc, ← matMul_assoc P Q, hPQ, hzero_l, hzero_r]
  have hBA : matMul B A = fun _ _ => 0 := by
    simp only [A, B, matMul_assoc, ← matMul_assoc Q P, hQP, hzero_l, hzero_r]
  have hAX2 : matMul A X2 = fun _ _ => 0 := by
    simp only [A, X2, matMul_assoc, ← matMul_assoc P Q, hPQ, hzero_l, hzero_r]
  have hX1A : matMul X1 A = fun _ _ => 0 := by
    simp only [A, X1, matMul_assoc, ← matMul_assoc Q P, hQP, hzero_l, hzero_r]
  have hBX1 : matMul B X1 = fun _ _ => 0 := by
    simp only [B, X1, matMul_assoc, ← matMul_assoc Q P, hQP, hzero_l, hzero_r]
  have hX2B : matMul X2 B = fun _ _ => 0 := by
    simp only [B, X2, matMul_assoc, ← matMul_assoc P Q, hPQ, hzero_l, hzero_r]
  have hX1X1 : matMul X1 X1 = fun _ _ => 0 := by
    simp only [X1, matMul_assoc, ← matMul_assoc Q P, hQP, hzero_l, hzero_r]
  have hX2X2 : matMul X2 X2 = fun _ _ => 0 := by
    simp only [X2, matMul_assoc, ← matMul_assoc P Q, hPQ, hzero_l, hzero_r]
  -- Exact Frobenius identity: `frobSq S = μ² + 2 t + frobSq B`!
  have hFrob_eq : frobSq S = μ ^ 2 + 2 * t + frobSq B := by
    have htr2 : matTr (matMul S S) = (((μ ^ 2 + 2 * t + frobSq B : ℝ) : ℂ)) := by
      conv_lhs => rw [hS_decomp]
      simp only [matMul_add_left, matMul_add_right, matTr_add, hAB, hBA, hAX2, hX1A, hBX1, hX2B,
        hX1X1, hX2X2, htr_zero, add_zero, zero_add]
      have hAX1_tr : matTr (matMul A X1) = 0 := by
        rw [matTr_mul_comm, hX1A, htr_zero]
      have hX2A_tr : matTr (matMul X2 A) = 0 := by
        rw [matTr_mul_comm, hAX2, htr_zero]
      have hBX2_tr : matTr (matMul B X2) = 0 := by
        rw [matTr_mul_comm, hX2B, htr_zero]
      have hX1B_tr : matTr (matMul X1 B) = 0 := by
        rw [matTr_mul_comm, hBX1, htr_zero]
      have hAA : matTr (matMul A A) = ((μ ^ 2 : ℝ) : ℂ) := by
        rw [hA_eq, matMul_smul_left, matMul_smul_right, hP2, matTr_smul, matTr_smul, hP_tr]
        push_cast; ring
      have hBB : matTr (matMul B B) = (frobSq B : ℂ) := matTr_mul_self_herm hBh
      have hX2X1 : matTr (matMul X2 X1) = (t : ℂ) := by rw [matTr_mul_comm, hX1X2_tr]
      rw [hAX1_tr, hX2A_tr, hBX2_tr, hX1B_tr, hAA, hBB, hX1X2_tr, hX2X1]
      push_cast; ring
    rw [matTr_mul_self_herm hS] at htr2
    exact Complex.ofReal_injective htr2
  -- Exact cubic trace identity: `Tr(S³) = μ³ + 3 μ t + 3 ⟨v | B | v⟩ + Tr(B³)`!
  have hS2_eq : matMul S S =
      matAdd (matAdd (matAdd (matMul A A) (matMul X1 X2)) (matAdd (matMul B B) (matMul X2 X1)))
        (matAdd (matAdd (matMul A X1) (matMul X1 B)) (matAdd (matMul B X2) (matMul X2 A))) := by
    conv_lhs => rw [hS_decomp]
    simp only [matMul_add_left, matMul_add_right, hAB, hBA, hAX2, hX1A, hBX1, hX2B, hX1X1, hX2X2]
    ext x y; simp only [matAdd]; ring
  have htr3_eq : matTr (matMul S (matMul S S)) =
      ((μ ^ 3 + 3 * μ * t : ℝ) : ℂ) + 3 * innerProd v (matApply B v) +
        matTr (matMul B (matMul B B)) :=
    matTr_cube_block_identity hP2 hPQ hQP hP_tr hA_eq hS_decomp hS2_eq
      (by simp only [A, ← matMul_assoc, hP2]) (by simp only [A, matMul_assoc, hP2])
      (by simp only [B, ← matMul_assoc, hQ2]) (by simp only [B, matMul_assoc, hQ2])
      (by simp only [X1, ← matMul_assoc, hP2]) (by simp only [X1, matMul_assoc, hQ2])
      (by simp only [X2, ← matMul_assoc, hQ2]) (by simp only [X2, matMul_assoc, hP2])
      hAB hBA hAX2 hX1A hBX1 hX2B hX1X1 hX2X2 hX1X2_tr hX1BX2_tr
  -- Bound `(innerProd v (matApply B v)).re ≥ -√(frobSq B) * t` via `normSq_matTr_mul_le`!
  let b : ℝ := frobSq B
  have hb_nn : 0 ≤ b := frobSq_nonneg B
  have hvBv_lb : -(Real.sqrt b * t) ≤ (innerProd v (matApply B v)).re := by
    have htr_v : matTr (matMul (stateProj v) B) = innerProd v (matApply B v) := by
      simp only [matTr, matMul, stateProj, innerProd, matApply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have hf_v : frobSq (stateProj v) = t ^ 2 := by
      simp only [frobSq, stateProj, map_mul, Complex.star_def, Complex.normSq_conj, t, innerProd_self_re, sq]
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum]
    have hcs := normSq_matTr_mul_le (stateProj v) B
    rw [htr_v, hf_v] at hcs
    have hre : (innerProd v (matApply B v)).re ^ 2 ≤ Complex.normSq (innerProd v (matApply B v)) := by
      rw [Complex.normSq_apply]; nlinarith
    have hsq : (innerProd v (matApply B v)).re ^ 2 ≤ (Real.sqrt b * t) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb_nn]; nlinarith
    nlinarith [mul_nonneg (Real.sqrt_nonneg b) ht_nn]
  -- Bound `(matTr (B^3)).re ≥ -(√b)^3` via `matTr_cube_re_le (-B)`!
  have hB3_lb : -(Real.sqrt b) ^ 3 ≤ (matTr (matMul B (matMul B B))).re := by
    have h := matTr_cube_re_le (matSmul (-1 : ℂ) B)
    have hf : frobSq (matSmul (-1 : ℂ) B) = b := by
      rw [frobSq_smul]; simp [b]
    have htr : matTr (matMul (matSmul (-1 : ℂ) B) (matMul (matSmul (-1 : ℂ) B) (matSmul (-1 : ℂ) B))) =
        -matTr (matMul B (matMul B B)) := by
      simp only [matMul_smul_left, matMul_smul_right, matTr_smul]; ring
    rw [hf, htr, Complex.neg_re] at h
    linarith
  -- Combine with `b ≤ frobSq S - μ² ≤ μ²`!
  have hb_le1 : b ≤ frobSq S - μ ^ 2 := by linarith
  have hb_le2 : b ≤ μ ^ 2 := by linarith
  have hsb_le_μ : Real.sqrt b ≤ μ := by
    rw [Real.sqrt_le_iff]; exact ⟨hμ_nn, hb_le2⟩
  have hsb_le_rest : Real.sqrt b ≤ Real.sqrt (frobSq S - μ ^ 2) := Real.sqrt_le_sqrt hb_le1
  have hsb3_le : (Real.sqrt b) ^ 3 ≤ (Real.sqrt (frobSq S - μ ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg b) hsb_le_rest 3
  have hre3 := congr_arg Complex.re htr3_eq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero] at hre3
  have hterm_nn : 0 ≤ 3 * (μ - Real.sqrt b) * t := by nlinarith
  linarith

/-- **Matrix-Free `L₁ → signCubeSum` Lower Bound (ALL `n ≥ 1`)**:
    For any unit state `ψ : QState n`, letting `c p = (⟨ψ | P_p | ψ⟩).re`,
    `L1 = ∑_{p ≠ 0} |c p|`, `σ p = if p = 0 then 0 else if 0 ≤ c p then 1 else -1`,
    and `T2 = d * (d² - 1)`: whenever `T2 ≤ 2 * L1²`,
      `L1³ - (√(T2 - L1²))³ ≤ 2 d * signCubeSum n σ`. -/
theorem signCubeSum_ge_of_L1 {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ)
    (hdom : (2 : ℝ) ^ n * (((2 : ℝ) ^ n) ^ 2 - 1) ≤
      2 * (∑ p ∈ nzPts n, |(innerProd ψ (pauliApply p ψ)).re|) ^ 2) :
    let d : ℝ := (2 : ℝ) ^ n
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
    let L1 : ℝ := ∑ p ∈ nzPts n, |c p|
    L1 ^ 3 - (Real.sqrt (d * (d ^ 2 - 1) - L1 ^ 2)) ^ 3 ≤ 2 * d * signCubeSum n σ := by
  intro d c σ L1
  let S := pauliExpand σ
  have hSh : IsHermMat S := pauliExpand_herm σ
  have hσ_sq : ∀ p ∈ nzPts n, (σ p) ^ 2 = 1 := fun p hp => by
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
    simp only [σ, hp0, ↓reduceIte]; split_ifs <;> norm_num
  have hS_frob : frobSq S = d * (d ^ 2 - 1) := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0 : (σ 0) ^ 2 = 0 := by simp [σ]
    have hrest : ∑ p ∈ nzPts n, (σ p) ^ 2 = d ^ 2 - 1 := by
      rw [Finset.sum_congr rfl hσ_sq, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact card_PauliIdx_erase_zero n
    rw [h0, zero_add]; exact congr_arg (d * ·) hrest
  have hμ_eq : (innerProd ψ (matApply S ψ)).re = L1 := by
    have happly : matApply S ψ = ∑ p : PauliIdx n, (σ p : ℂ) • pauliApply p ψ := by
      ext x
      simp only [matApply, S, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => by
        simp_rw [mul_assoc, ← Finset.mul_sum]; congr 1
        exact congr_fun (pauliMat_apply p ψ) x
    rw [happly, innerProd_sum_right]
    simp only [innerProd_smul_right, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    simp only [σ, ↓reduceIte, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
    simp only [hp0, ↓reduceIte]
    by_cases hcp : 0 ≤ c p
    · simp only [hcp, ↓reduceIte, one_mul, abs_of_nonneg hcp]; rfl
    · push Not at hcp; simp only [not_le.mpr hcp, ↓reduceIte, neg_mul, one_mul, abs_of_neg hcp]; rfl
  have htr3_eq : (matTr (matMul S (matMul S S))).re = 2 * d * signCubeSum n σ := by
    rw [matMul_pauliExpand_self, matTr_pauliExpand_mul]
    have hre : ((2 : ℂ) ^ n * ∑ q : PauliIdx n,
        ((σ q * ∑ p : PauliIdx n, (pauliPhase q p).re * σ p * σ (q + p) : ℝ) : ℂ)).re =
        d * ∑ q : PauliIdx n, σ q * ∑ p : PauliIdx n, (pauliPhase q p).re * σ p * σ (q + p) := by
      have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
      rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hσ0 : σ 0 = 0 := by simp [σ]
    rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)), hσ0, zero_mul, zero_add]
    have hsum : ∑ q ∈ nzPts n, σ q *
        ∑ p : PauliIdx n, (pauliPhase q p).re * σ p * σ (q + p) =
        2 * signCubeSum n σ := by
      rw [signCubeSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)), hσ0, mul_zero, zero_mul, zero_add]
      rw [← Finset.add_sum_erase _ _ hq, pauliIdx_add_self, hσ0, mul_zero, zero_add]
      ring
    change d * ∑ q ∈ nzPts n, σ q * ∑ p : PauliIdx n, (pauliPhase q p).re * σ p * σ (q + p) = _
    rw [hsum]; ring
  have hL1_nn : 0 ≤ L1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hray := matTr_cube_ge_of_rayleigh hSh hunit (hμ_eq ▸ hL1_nn) (by rwa [hS_frob, hμ_eq])
  dsimp only at hray
  rwa [hμ_eq, hS_frob, htr3_eq] at hray

/-- **The `c = 2` Barrier Equivalence Theorem (ALL `n ≥ 2`)**:
    Suppose every `±1` Pauli sign assignment on `W(2n-1, 2)` satisfies
      `1 - 2 ρₙ(σ) ≤ c / √(2ⁿ)`,
    and let `x ∈ [1/√2, 1)` satisfy `c / 2 ≤ x³ - (√(1 - x²))³` (such `x < 1` exists for every `c < 2`!).
    Then for EVERY unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n` (`d = 2ⁿ`):
      `1 + (d - 1)² / (x² * d * (d + 1)) ≤ pauliMoment4 n ψ`.
    In particular, any uniform bound `c < 2` forces `liminf_{n → ∞} min_ψ pauliMoment4 n ψ ≥ 1 + 1/x² > 2`! -/
theorem pauliMoment4_ge_of_contextuality_const {n : ℕ} (hn : 2 ≤ n)
    {c x : ℝ} (hx_lo : 1 / 2 ≤ x ^ 2) (hx_pos : 0 < x) (hx_lt1 : x ≤ 1)
    (hcx : c / 2 ≤ x ^ 3 - (Real.sqrt (1 - x ^ 2)) ^ 3)
    (hCD : ∀ s : PauliIdx n → ℤ, IsSignAssign s →
      1 - 2 * (frustPairs (nzPts n) s : ℝ) /
          (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) ≤
        c / Real.sqrt ((2 : ℝ) ^ n))
    {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    1 + (d - 1) ^ 2 / (x ^ 2 * d * (d + 1)) ≤ pauliMoment4 n ψ := by
  intro d
  set c_p : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set L1 : ℝ := ∑ p ∈ nzPts n, |c_p p|
  have hd_pos : 0 < d := by positivity
  have hd_ge4 : (4 : ℝ) ≤ d := by
    have : (4 : ℕ) ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hT2_pos : 0 < d * (d ^ 2 - 1) := by nlinarith only [hd_ge4]
  have hL1_nn : 0 ≤ L1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- Step 1: Prove `L1 ≤ x * √(d * (d² - 1))`!
  have hL1_le : L1 ≤ x * Real.sqrt (d * (d ^ 2 - 1)) := by
    by_contra hgt; push Not at hgt
    let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c_p p then 1 else -1
    let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if 0 ≤ c_p p then 1 else -1
    have hs : IsSignAssign s :=
      ⟨by simp [s], fun p hp => by simp only [s, hp, ↓reduceIte]; split_ifs <;> simp⟩
    have h0 : σ 0 = 0 := by simp [σ]
    have hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
      simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp
    have hdom : d * (d ^ 2 - 1) ≤ 2 * L1 ^ 2 := by
      have h1 : x ^ 2 * (d * (d ^ 2 - 1)) < L1 ^ 2 := by
        have hsq : (x * Real.sqrt (d * (d ^ 2 - 1))) ^ 2 < L1 ^ 2 := by
          nlinarith only [hgt, mul_nonneg (le_of_lt hx_pos) (Real.sqrt_nonneg (d * (d ^ 2 - 1)))]
        rwa [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)] at hsq
      nlinarith only [h1, hx_lo, hT2_pos]
    have hcube := signCubeSum_ge_of_L1 hunit hdom
    dsimp only at hcube
    -- Bridge `signCubeSum n σ` to `1 - 2 ρₙ(s)` and upper-bound by `(c / 2) * (√T2)³`!
    let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
    have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real hn
    have hL_pos : 0 < L := by
      rw [hL_eq]; exact mul_pos (mul_pos (by nlinarith only [hd_ge4]) (by linarith only [hd_ge4])) (by linarith only [hd_ge4])
    have hbr := (signCubeSum_eq_frustPairs_all (by omega) h0 hpm).2
    have hseq : (fun p : PauliIdx n => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = s := by
      ext p; by_cases hp : p = 0
      · subst hp; simp [s]
      · simp only [s, σ, hp, ↓reduceIte]
        by_cases hcp : 0 ≤ c_p p
        · simp [hcp]
        · simp only [hcp, ↓reduceIte]; norm_num
    rw [hseq] at hbr
    have hrho := hCD s hs
    have hS_ub : 2 * d * signCubeSum n σ ≤ (c / 2) * (Real.sqrt (d * (d ^ 2 - 1))) ^ 3 := by
      have h1 : 2 * signCubeSum n σ ≤ (c / Real.sqrt d) * L := by
        have h2 : 1 - 2 * (frustPairs (nzPts n) s : ℝ) / L = 2 * signCubeSum n σ / L := by
          field_simp [ne_of_gt hL_pos]; linarith only [hbr]
        rw [h2, div_le_iff₀ hL_pos] at hrho; exact hrho
      have h2 : 2 * d * signCubeSum n σ ≤ c * Real.sqrt d * L := by
        have hm := mul_le_mul_of_nonneg_left h1 (le_of_lt hd_pos)
        have hsq : d * (c / Real.sqrt d * L) = c * Real.sqrt d * L := by
          have hs_ne : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd_pos)
          have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (le_of_lt hd_pos)
          calc d * (c / Real.sqrt d * L)
              = (Real.sqrt d * Real.sqrt d) * (c / Real.sqrt d * L) := by rw [hsd]
            _ = c * Real.sqrt d * L := by field_simp [hs_ne]
        linarith only [hm, hsq]
      -- Show `L ≤ (1/2) * d * (d² - 1) * √(d² - 1)` so `√d * L ≤ (1/2) * (√(d(d²-1)))³`!
      have hL_le : Real.sqrt d * L ≤ (1 / 2 : ℝ) * (Real.sqrt (d * (d ^ 2 - 1))) ^ 3 := by
        have hfac : (Real.sqrt (d * (d ^ 2 - 1))) ^ 3 =
            Real.sqrt d * (d * (d ^ 2 - 1) * Real.sqrt (d ^ 2 - 1)) := by
          have hmul : Real.sqrt (d * (d ^ 2 - 1)) = Real.sqrt d * Real.sqrt (d ^ 2 - 1) :=
            Real.sqrt_mul (le_of_lt hd_pos) _
          calc (Real.sqrt (d * (d ^ 2 - 1))) ^ 3
              = (Real.sqrt (d * (d ^ 2 - 1))) ^ 2 * Real.sqrt (d * (d ^ 2 - 1)) := by ring
            _ = (d * (d ^ 2 - 1)) * (Real.sqrt d * Real.sqrt (d ^ 2 - 1)) := by
                rw [Real.sq_sqrt (le_of_lt hT2_pos), hmul]
            _ = _ := by ring
        rw [hfac, hL_eq]
        have hcmp : (d / 2 - 1) * (d + 2) ≤ (1 / 2 : ℝ) * d * Real.sqrt (d ^ 2 - 1) := by
          have hsq : ((d / 2 - 1) * (d + 2)) ^ 2 ≤ ((1 / 2 : ℝ) * d * Real.sqrt (d ^ 2 - 1)) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith only [hd_ge4])]
            nlinarith only [hd_ge4]
          have hr_nn : 0 ≤ (1 / 2 : ℝ) * d * Real.sqrt (d ^ 2 - 1) :=
            mul_nonneg (by linarith only [hd_ge4]) (Real.sqrt_nonneg _)
          nlinarith only [hsq, hr_nn]
        have hnn : 0 ≤ Real.sqrt d * (d ^ 2 - 1) :=
          mul_nonneg (Real.sqrt_nonneg d) (by nlinarith only [hd_ge4])
        have hmul := mul_le_mul_of_nonneg_left hcmp hnn
        linarith only [hmul]
      have hc_nn : 0 ≤ c := by
        have hL1_pos : 0 < L1 := lt_trans (mul_pos hx_pos (Real.sqrt_pos.mpr hT2_pos)) hgt
        have h1' : 0 < L1 ^ 3 - (Real.sqrt (d * (d ^ 2 - 1) - L1 ^ 2)) ^ 3 := by
          have hlt2 : d * (d ^ 2 - 1) - L1 ^ 2 < L1 ^ 2 := by
            have hsq : (x * Real.sqrt (d * (d ^ 2 - 1))) ^ 2 < L1 ^ 2 := by
              nlinarith only [hgt, mul_nonneg (le_of_lt hx_pos) (Real.sqrt_nonneg (d * (d ^ 2 - 1)))]
            rw [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)] at hsq
            nlinarith only [hsq, hx_lo, hT2_pos]
          have hs_lt : Real.sqrt (d * (d ^ 2 - 1) - L1 ^ 2) < L1 := by
            rw [Real.sqrt_lt' hL1_pos]; exact hlt2
          have hpow := pow_lt_pow_left₀ hs_lt (Real.sqrt_nonneg _) (by norm_num : 3 ≠ 0)
          linarith only [hpow]
        have hpos_rhs : 0 < c * Real.sqrt d * L := by linarith only [h1', hcube, h2]
        have hsdL_pos : 0 < Real.sqrt d * L := mul_pos (Real.sqrt_pos.mpr hd_pos) hL_pos
        by_contra hneg; push Not at hneg
        have : c * (Real.sqrt d * L) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hsdL_pos)
        linarith only [hpos_rhs, this]
      have hcm := mul_le_mul_of_nonneg_left hL_le hc_nn
      linarith only [h2, hcm]
    -- Now compare `L1³ - (√(T2 - L1²))³` with `(x³ - (√(1 - x²))³) * (√T2)³`!
    set sT := Real.sqrt (d * (d ^ 2 - 1))
    have hsT_pos : 0 < sT := Real.sqrt_pos.mpr hT2_pos
    have hsT_sq : sT ^ 2 = d * (d ^ 2 - 1) := Real.sq_sqrt (le_of_lt hT2_pos)
    have hL1_cube_gt : (x * sT) ^ 3 < L1 ^ 3 :=
      pow_lt_pow_left₀ hgt (mul_nonneg (le_of_lt hx_pos) (le_of_lt hsT_pos)) (by norm_num)
    have hrest_le : Real.sqrt (d * (d ^ 2 - 1) - L1 ^ 2) ≤ Real.sqrt (1 - x ^ 2) * sT := by
      have h1 : Real.sqrt (1 - x ^ 2) * sT = Real.sqrt ((1 - x ^ 2) * (d * (d ^ 2 - 1))) :=
        (Real.sqrt_mul (by nlinarith only [hx_pos, hx_lt1]) _).symm
      rw [h1]
      apply Real.sqrt_le_sqrt
      have hsq : (x * sT) ^ 2 < L1 ^ 2 := by
        nlinarith only [hgt, mul_nonneg (le_of_lt hx_pos) (le_of_lt hsT_pos)]
      rw [mul_pow, hsT_sq] at hsq
      linarith only [hsq]
    have hrest3_le : (Real.sqrt (d * (d ^ 2 - 1) - L1 ^ 2)) ^ 3 ≤ (Real.sqrt (1 - x ^ 2) * sT) ^ 3 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hrest_le 3
    have hscale : (x * sT) ^ 3 - (Real.sqrt (1 - x ^ 2) * sT) ^ 3 =
        (x ^ 3 - (Real.sqrt (1 - x ^ 2)) ^ 3) * sT ^ 3 := by ring
    have hcx_mul : (c / 2) * sT ^ 3 ≤ (x ^ 3 - (Real.sqrt (1 - x ^ 2)) ^ 3) * sT ^ 3 :=
      mul_le_mul_of_nonneg_right hcx (pow_nonneg (le_of_lt hsT_pos) 3)
    linarith only [hcube, hS_ub, hL1_cube_gt, hrest3_le, hscale, hcx_mul]
  -- Step 2: Apply Hölder `(d - 1)³ ≤ L1² * (pauliMoment4 n ψ - 1)`!
  have hc0 : c_p 0 = 1 := pauliExpect_zero_re hunit
  have hsum2 : ∑ p ∈ nzPts n, (c_p p) ^ 2 = d - 1 := by
    have h := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))] at h
    have hns : ∀ p, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c_p p) ^ 2 :=
      fun p => innerProd_pauliApply_self_normSq p ψ
    simp_rw [hns] at h
    change (c_p 0) ^ 2 + ∑ p ∈ nzPts n, (c_p p) ^ 2 = d at h
    rw [hc0] at h; linarith
  have hmom : pauliMoment4 n ψ = 1 + ∑ p ∈ nzPts n, (c_p p) ^ 4 := by
    rw [pauliMoment4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have hns : ∀ p, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2 = (c_p p) ^ 4 := fun p => by
      rw [innerProd_pauliApply_self_normSq]; ring
    simp_rw [hns]
    change (c_p 0) ^ 4 + ∑ p ∈ nzPts n, (c_p p) ^ 4 = 1 + ∑ p ∈ nzPts n, (c_p p) ^ 4
    rw [hc0]; ring
  set S3 := ∑ p ∈ nzPts n, |c_p p| ^ 3
  set S4 := ∑ p ∈ nzPts n, (c_p p) ^ 4
  have hcs1 : (d - 1) ^ 2 ≤ L1 * S3 := by
    rw [← hsum2]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (nzPts n) (fun p => Real.sqrt |c_p p|)
      (fun p => Real.sqrt |c_p p| * |c_p p|)
    have hlhs : ∑ p ∈ nzPts n, Real.sqrt |c_p p| * (Real.sqrt |c_p p| * |c_p p|) = ∑ p ∈ nzPts n, (c_p p) ^ 2 :=
      Finset.sum_congr rfl fun p _ => by
        calc Real.sqrt |c_p p| * (Real.sqrt |c_p p| * |c_p p|)
            = (Real.sqrt |c_p p| * Real.sqrt |c_p p|) * |c_p p| := by ring
          _ = |c_p p| * |c_p p| := by rw [Real.mul_self_sqrt (abs_nonneg _)]
          _ = (c_p p) ^ 2 := by rw [← sq, sq_abs]
    have hr1 : ∑ p ∈ nzPts n, (Real.sqrt |c_p p|) ^ 2 = L1 :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (abs_nonneg _)
    have hr2' : ∑ p ∈ nzPts n, (Real.sqrt |c_p p| * |c_p p|) ^ 2 = S3 :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]; ring
    rwa [hlhs, hr1, hr2'] at h
  have hcs2 : S3 ^ 2 ≤ (d - 1) * S4 := by
    rw [← hsum2]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (nzPts n) (fun p => |c_p p|) (fun p => (c_p p) ^ 2)
    have hlhs : ∑ p ∈ nzPts n, |c_p p| * (c_p p) ^ 2 = S3 :=
      Finset.sum_congr rfl fun p _ => by rw [← sq_abs (c_p p)]; ring
    have hr1 : ∑ p ∈ nzPts n, |c_p p| ^ 2 = ∑ p ∈ nzPts n, (c_p p) ^ 2 :=
      Finset.sum_congr rfl fun p _ => sq_abs _
    have hr2' : ∑ p ∈ nzPts n, ((c_p p) ^ 2) ^ 2 = S4 :=
      Finset.sum_congr rfl fun p _ => by ring
    rwa [hlhs, hr1, hr2'] at h
  have hS4_nn : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => by positivity
  have hL1_sq_le : L1 ^ 2 ≤ x ^ 2 * d * (d ^ 2 - 1) := by
    have hsq : L1 ^ 2 ≤ (x * Real.sqrt (d * (d ^ 2 - 1))) ^ 2 :=
      pow_le_pow_left₀ hL1_nn hL1_le 2
    rw [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)] at hsq; linarith
  have h4 : (d - 1) ^ 4 ≤ L1 ^ 2 * ((d - 1) * S4) := by
    have hsq1 : ((d - 1) ^ 2) ^ 2 ≤ (L1 * S3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcs1 2
    calc (d - 1) ^ 4 = ((d - 1) ^ 2) ^ 2 := by ring
      _ ≤ L1 ^ 2 * S3 ^ 2 := by rw [mul_pow] at hsq1; exact hsq1
      _ ≤ L1 ^ 2 * ((d - 1) * S4) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
  have h3 : (d - 1) ^ 3 ≤ L1 ^ 2 * S4 := by nlinarith
  have h3' : (d - 1) ^ 3 ≤ x ^ 2 * d * (d ^ 2 - 1) * S4 :=
    le_trans h3 (mul_le_mul_of_nonneg_right hL1_sq_le hS4_nn)
  have hden_pos : 0 < x ^ 2 * d * (d + 1) := by positivity
  have hdiv : (d - 1) ^ 2 / (x ^ 2 * d * (d + 1)) ≤ S4 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  rw [hmom]; linarith

/-! ### Part 3: Exact Finite `ℤ₄`-Phase Averaging & Asymptotic Lower Bound `1 - 2ρₙ = Ω(2⁻ⁿ/²)` -/

/-- Fourth root of unity `i^z` for `z : ZMod 4`. -/
def z4Pow (z : ZMod 4) : ℂ :=
  match z.val with
  | 0 => 1
  | 1 => Complex.I
  | 2 => -1
  | _ => -Complex.I

private lemma zmod4_cases (z : ZMod 4) : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private lemma z4Pow_0 : z4Pow 0 = 1 := rfl
private lemma z4Pow_1 : z4Pow 1 = Complex.I := rfl
private lemma z4Pow_2 : z4Pow 2 = -1 := rfl
private lemma z4Pow_3 : z4Pow 3 = -Complex.I := rfl

private lemma z4Pow_normSq (z : ZMod 4) : Complex.normSq (z4Pow z) = 1 := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl <;>
    simp [z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3, Complex.normSq_I]

private lemma star_z4Pow_mul (x y : ZMod 4) : star (z4Pow x) * z4Pow y = z4Pow (y - x) := by
  rcases zmod4_cases x with rfl | rfl | rfl | rfl <;>
  rcases zmod4_cases y with rfl | rfl | rfl | rfl <;>
  first
  | (change star (z4Pow _) * z4Pow _ = z4Pow 0; simp [z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3])
  | (change star (z4Pow _) * z4Pow _ = z4Pow 1; simp [z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3])
  | (change star (z4Pow _) * z4Pow _ = z4Pow 2; simp [z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3])
  | (change star (z4Pow _) * z4Pow _ = z4Pow 3; simp [z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3])

/-- `ℤ₄`-phase pure state `|ψ_f⟩ = 2^(-n/2) ∑_x i^{f(x)} |x⟩` (`f : F2 n → ZMod 4`). -/
noncomputable def z4PhaseState {n : ℕ} (f : F2 n → ZMod 4) : QState n :=
  fun x => (((1 / Real.sqrt ((2 : ℝ) ^ n)) : ℝ) : ℂ) * z4Pow (f x)

lemma z4PhaseState_unit {n : ℕ} (f : F2 n → ZMod 4) : IsUnitState (z4PhaseState f) := by
  rw [IsUnitState, innerProd_self_eq_sum_normSq]
  have hd_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsum : ∑ x : F2 n, Complex.normSq (z4PhaseState f x) = 1 := by
    have ht : ∀ x : F2 n, Complex.normSq (z4PhaseState f x) = 1 / (2 : ℝ) ^ n := fun x => by
      simp only [z4PhaseState, map_mul, Complex.normSq_ofReal, z4Pow_normSq, mul_one, ← sq,
        div_pow, one_pow, Real.sq_sqrt (le_of_lt hd_pos)]
    rw [Finset.sum_congr rfl fun x _ => ht x, Finset.sum_const, Finset.card_univ, card_F2, nsmul_eq_mul]
    push_cast; field_simp [ne_of_gt hd_pos]
  rw [hsum, Complex.ofReal_one]

/-- Explicit bijection `Bool × Bool ≃ ZMod 4` mapping two independent `±1` coins to `ZMod 4`
    such that `boolSgn u + boolSgn v = (z4Pow (enc (u, v)) + star (z4Pow (enc (u, v)))).re`! -/
private def encBoolZ4 : Bool × Bool ≃ ZMod 4 where
  toFun
    | (false, false) => 0
    | (false, true)  => 1
    | (true,  true)  => 2
    | (true,  false) => 3
  invFun z :=
    match z.val with
    | 0 => (false, false)
    | 1 => (false, true)
    | 2 => (true, true)
    | _ => (true, false)
  left_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl
  right_inv := by intro z; fin_cases z <;> rfl

private def boolSgn (b : Bool) : ℤ := if b then -1 else 1

private lemma encBoolZ4_symm_0 : encBoolZ4.symm 0 = (false, false) := rfl
private lemma encBoolZ4_symm_1 : encBoolZ4.symm 1 = (false, true) := rfl
private lemma encBoolZ4_symm_2 : encBoolZ4.symm 2 = (true, true) := rfl
private lemma encBoolZ4_symm_3 : encBoolZ4.symm 3 = (true, false) := rfl

private lemma z4Pow_pair_eq_boolSgn (c : ZMod 2) (s : ZMod 2) (δ : ZMod 4) :
    let ph : ℂ := if c = 0 then 1 else Complex.I
    let cs : ℤ := if s = 0 then 1 else -1
    let ch : ℤ := if c = 0 then 1 else -1
    let sh : ZMod 4 := (if c = 1 then 1 else 0) + (if s = 1 then 2 else 0)
    (ph * (cs : ℂ) * (z4Pow δ + (ch : ℂ) * z4Pow (-δ))).re =
      ((boolSgn (encBoolZ4.symm (δ + sh)).1 + boolSgn (encBoolZ4.symm (δ + sh)).2 : ℤ) : ℝ) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hneg0 : (-0 : ZMod 4) = 0 := rfl
  have hneg1 : (-1 : ZMod 4) = 3 := rfl
  have hneg2 : (-2 : ZMod 4) = 2 := rfl
  have hneg3 : (-3 : ZMod 4) = 1 := rfl
  have ha11 : (1 : ZMod 4) + 1 = 2 := rfl
  have ha12 : (1 : ZMod 4) + 2 = 3 := rfl
  have ha13 : (1 : ZMod 4) + 3 = 0 := rfl
  have ha21 : (2 : ZMod 4) + 1 = 3 := rfl
  have ha22 : (2 : ZMod 4) + 2 = 0 := rfl
  have ha23 : (2 : ZMod 4) + 3 = 1 := rfl
  have ha31 : (3 : ZMod 4) + 1 = 0 := rfl
  have ha32 : (3 : ZMod 4) + 2 = 1 := rfl
  have ha33 : (3 : ZMod 4) + 3 = 2 := rfl
  rcases zmod2_cases c with rfl | rfl <;>
  rcases zmod2_cases s with rfl | rfl <;>
  rcases zmod4_cases δ with rfl | rfl | rfl | rfl <;>
  (dsimp only;
   simp only [h01, h10, ↓reduceIte, hneg0, hneg1, hneg2, hneg3, add_zero, zero_add,
     ha11, ha12, ha13, ha21, ha22, ha23, ha31, ha32, ha33,
     z4Pow_0, z4Pow_1, z4Pow_2, z4Pow_3,
     encBoolZ4_symm_0, encBoolZ4_symm_1, encBoolZ4_symm_2, encBoolZ4_symm_3, boolSgn];
   norm_num)

/-- Exact telescoping identity: `∑_{w : α → Bool} |∑_x boolSgn (w x)| = 2m * C(2m, m)` when `|α| = 2m`. -/
private lemma sum_abs_boolSgn_eq_centralBinom {α : Type*} [DecidableEq α] [Fintype α] {m : ℕ}
    (hcard : Fintype.card α = 2 * m) :
    (∑ w : α → Bool, |(∑ x : α, (boolSgn (w x) : ℝ))|) =
      ((2 * m * Nat.choose (2 * m) m : ℕ) : ℝ) := by
  -- Group `w : α → Bool` by the finset `S = {x | w x = true}` (card `k ∈ 0..2m`)!
  let toSet : (α → Bool) ≃ Finset α :=
    { toFun := fun w => Finset.univ.filter fun x => w x = true
      invFun := fun S x => decide (x ∈ S)
      left_inv := fun w => by ext x; simp
      right_inv := fun S => by ext x; simp }
  have h1 : (∑ w : α → Bool, |(∑ x : α, (boolSgn (w x) : ℝ))|) =
      ∑ S : Finset α, |((2 * m : ℝ) - 2 * (S.card : ℝ))| := by
    refine Fintype.sum_equiv toSet _ _ fun w => ?_
    congr 1
    have hsp := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset α)
      (fun x => w x = true) (fun x => (boolSgn (w x) : ℝ))
    have hT : ∑ x ∈ Finset.univ.filter (fun x => w x = true), (boolSgn (w x) : ℝ) =
        -((toSet w).card : ℝ) := by
      have ht : ∀ x ∈ Finset.univ.filter (fun x => w x = true), (boolSgn (w x) : ℝ) = -1 := fun x hx => by
        simp [boolSgn, (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]; simp [toSet]
    have hF : ∑ x ∈ Finset.univ.filter (fun x => ¬w x = true), (boolSgn (w x) : ℝ) =
        ((Finset.univ.filter fun x => ¬w x = true).card : ℝ) := by
      have ht : ∀ x ∈ Finset.univ.filter (fun x => ¬w x = true), (boolSgn (w x) : ℝ) = 1 := fun x hx => by
        simp [boolSgn, (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (p := fun x => w x = true)
    have hcu : (Finset.univ : Finset α).card = 2 * m := by rw [Finset.card_univ, hcard]
    have hcR : ((toSet w).card : ℝ) + ((Finset.univ.filter fun x => ¬w x = true).card : ℝ) = (2 * m : ℝ) := by
      have : (toSet w).card + (Finset.univ.filter fun x => ¬w x = true).card = 2 * m := by
        simpa [toSet] using hc.trans hcu
      exact_mod_cast this
    linarith
  rw [h1]
  -- Partition `Finset α` by cardinality `k ∈ range (2 * m + 1)`!
  have h2 : ∑ S : Finset α, |((2 * m : ℝ) - 2 * (S.card : ℝ))| =
      ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) k : ℝ) * |((2 * m : ℝ) - 2 * (k : ℝ))| := by
    have hpart : (Finset.univ : Finset (Finset α)) =
        (Finset.range (2 * m + 1)).biUnion fun k => Finset.powersetCard k (Finset.univ : Finset α) := by
      ext S; simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_powersetCard, Finset.subset_univ, true_and, true_iff]
      exact ⟨S.card, Nat.lt_succ_of_le (by rw [← hcard]; exact Finset.card_le_univ S), rfl⟩
    have hdisj : Set.PairwiseDisjoint (Finset.range (2 * m + 1) : Set ℕ)
        (fun k => Finset.powersetCard k (Finset.univ : Finset α)) := by
      intro k1 _ k2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]; intro S h1 h2
      exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
    rw [hpart, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ht : ∀ S ∈ Finset.powersetCard k (Finset.univ : Finset α),
        |((2 * m : ℝ) - 2 * (S.card : ℝ))| = |((2 * m : ℝ) - 2 * (k : ℝ))| := fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
        Finset.card_univ, hcard]
  rw [h2]
  -- Evaluate `∑_{k=0}^{2m} C(2m, k) * |2m - 2k| = 2m * C(2m, m)` by telescoping!
  cases m with
  | zero => simp
  | succ r =>
    let m' := r + 1
    change ∑ k ∈ Finset.range (2 * m' + 1),
        (Nat.choose (2 * m') k : ℝ) * |((2 * m' : ℝ) - 2 * (k : ℝ))| =
        ((2 * m' * Nat.choose (2 * m') m' : ℕ) : ℝ)
    -- Split `range (2*m' + 1)` into `k < m'`, `k = m'`, and `m' < k`!
    have hsplit : ∑ k ∈ Finset.range (2 * m' + 1),
        (Nat.choose (2 * m') k : ℝ) * |((2 * m' : ℝ) - 2 * (k : ℝ))| =
        2 * ∑ k ∈ Finset.range m', (Nat.choose (2 * m') k : ℝ) * ((2 * m' : ℝ) - 2 * (k : ℝ)) := by
      have hhi : ∑ k ∈ Finset.Ico (m' + 1) (2 * m' + 1),
          (Nat.choose (2 * m') k : ℝ) * |((2 * m' : ℝ) - 2 * (k : ℝ))| =
          ∑ k ∈ Finset.range m', (Nat.choose (2 * m') k : ℝ) * ((2 * m' : ℝ) - 2 * (k : ℝ)) := by
        refine Finset.sum_bij (fun k _ => 2 * m' - k) ?_ ?_ ?_ ?_
        · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
        · intro k1 hk1 k2 hk2 h; rw [Finset.mem_Ico] at hk1 hk2; omega
        · intro j hj; rw [Finset.mem_range] at hj
          exact ⟨2 * m' - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro k hk; rw [Finset.mem_Ico] at hk
          rw [Nat.choose_symm (by omega)]
          have hk_ge : (2 * m' : ℝ) ≤ 2 * (k : ℝ) := by
            have : 2 * m' ≤ 2 * k := by omega
            exact_mod_cast this
          have hsub : ((2 * m' - k : ℕ) : ℝ) = (2 * m' : ℝ) - (k : ℝ) := by
            rw [Nat.cast_sub (by omega)]; push_cast; rfl
          rw [hsub, abs_of_nonpos (by linarith)]; ring
      have hlo : ∑ k ∈ Finset.range m',
          (Nat.choose (2 * m') k : ℝ) * |((2 * m' : ℝ) - 2 * (k : ℝ))| =
          ∑ k ∈ Finset.range m', (Nat.choose (2 * m') k : ℝ) * ((2 * m' : ℝ) - 2 * (k : ℝ)) :=
        Finset.sum_congr rfl fun k hk => by
          have : k < m' := Finset.mem_range.mp hk
          have : 2 * (k : ℝ) ≤ 2 * (m' : ℝ) := by exact_mod_cast (show 2 * k ≤ 2 * m' by omega)
          rw [abs_of_nonneg (by linarith)]
      have hdecomp : Finset.range (2 * m' + 1) =
          Finset.range m' ∪ ({m'} ∪ Finset.Ico (m' + 1) (2 * m' + 1)) := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
        omega
      have hd1 : Disjoint (Finset.range m') ({m'} ∪ Finset.Ico (m' + 1) (2 * m' + 1)) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at hk1 hk2
        omega
      have hd2 : Disjoint ({m'} : Finset ℕ) (Finset.Ico (m' + 1) (2 * m' + 1)) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_singleton, Finset.mem_Ico] at hk1 hk2; omega
      rw [hdecomp, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, hlo, hhi]
      simp [sub_self]; ring
    rw [hsplit]
    -- Telescope `C(2m', k) * (2m' - 2k) = 2m' * (C(2m'-1, k) - C(2m'-1, k-1))`!
    have htele : ∀ t : ℕ, t ≤ m' →
        ∑ k ∈ Finset.range t, (Nat.choose (2 * m') k : ℝ) * ((2 * m' : ℝ) - 2 * (k : ℝ)) =
        (2 * m' : ℝ) * (Nat.choose (2 * m' - 1) (t - 1) : ℝ) * (if t = 0 then 0 else 1) := by
      intro t ht
      induction t with
      | zero => simp
      | succ s ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        cases s with
        | zero =>
          simp [Nat.choose_zero_right]
        | succ u =>
          have hne1 : u + 1 ≠ 0 := Nat.succ_ne_zero u
          have hne2 : u + 1 + 1 ≠ 0 := Nat.succ_ne_zero (u + 1)
          simp only [hne1, hne2, ↓reduceIte, mul_one, Nat.add_sub_cancel]
          -- Use `C(2m', u+1) * (u+1) = 2m' * C(2m'-1, u)` and `C(2m', u+1) = C(2m'-1, u) + C(2m'-1, u+1)`!
          have h1 : (Nat.choose (2 * m') (u + 1) : ℝ) =
              (Nat.choose (2 * m' - 1) u : ℝ) + (Nat.choose (2 * m' - 1) (u + 1) : ℝ) := by
            have hn : 2 * m' = (2 * m' - 1) + 1 := by omega
            conv_lhs => rw [hn, Nat.choose_succ_succ]
            push_cast; rfl
          have h2 : ((u : ℝ) + 1) * (Nat.choose (2 * m') (u + 1) : ℝ) =
              (2 * m' : ℝ) * (Nat.choose (2 * m' - 1) u : ℝ) := by
            have hn : 2 * m' = (2 * m' - 1) + 1 := by omega
            have hnat := Nat.add_one_mul_choose_eq (2 * m' - 1) u
            rw [← hn] at hnat
            have hc := congr_arg (Nat.cast (R := ℝ)) hnat
            push_cast at hc; linarith
          push_cast; nlinarith only [h1, h2]
    rw [htele m' le_rfl]
    have hm_ne : m' ≠ 0 := Nat.succ_ne_zero r
    simp only [hm_ne, ↓reduceIte, mul_one]
    -- Finally `2 * (2m' * C(2m'-1, m'-1)) = 2m' * C(2m', m')`!
    have hmid : 2 * (Nat.choose (2 * m' - 1) (m' - 1) : ℝ) = (Nat.choose (2 * m') m' : ℝ) := by
      have h1 : m' * Nat.choose (2 * m') m' = 2 * m' * Nat.choose (2 * m' - 1) (m' - 1) := by
        have hn : 2 * m' = (2 * m' - 1) + 1 := by omega
        have hm' : m' = (m' - 1) + 1 := by omega
        have hnat := Nat.add_one_mul_choose_eq (2 * m' - 1) (m' - 1)
        rw [← hn, ← hm'] at hnat; linarith
      have h2 : Nat.choose (2 * m') m' = 2 * Nat.choose (2 * m' - 1) (m' - 1) := by
        have hm_pos : 0 < m' := Nat.succ_pos r
        have : m' * Nat.choose (2 * m') m' = m' * (2 * Nat.choose (2 * m' - 1) (m' - 1)) := by
          linarith
        exact Nat.eq_of_mul_eq_mul_left hm_pos this
      exact_mod_cast h2.symm
    push_cast; rw [← hmid]; ring

private lemma z4Phase_pair_equiv_exists {n : ℕ} {a b : F2 n} {k : Fin n} (hk : a k = 1) :
    let sh : F2 n → ZMod 4 := fun x =>
      (if dot a b = 1 then 1 else 0) + (if dot b x = 1 then 2 else 0)
    ∃ e : (F2 n → ZMod 4) ≃ ({x : F2 n // x k = 0} → ZMod 4) × (F2 n → Bool),
      (∀ f x, x k = 0 → (e f).2 x = (encBoolZ4.symm (f (x + a) - f x + sh x)).1) ∧
      (∀ f x, x k ≠ 0 → (e f).2 x = (encBoolZ4.symm (f x - f (x + a) + sh (x + a))).2) := by
  intro sh
  have hflip0 : ∀ x : F2 n, x k = 0 → (x + a) k = 1 := fun x hx => by simp [Pi.add_apply, hx, hk]
  have hflip1 : ∀ x : F2 n, x k ≠ 0 → (x + a) k = 0 := fun x hx => by
    have hx1 : x k = 1 := (zmod2_cases (x k)).resolve_left hx
    simp [Pi.add_apply, hx1, hk]; decide
  refine ⟨{
    toFun := fun f =>
      (fun x => f x.1,
       fun x => if x k = 0
         then (encBoolZ4.symm (f (x + a) - f x + sh x)).1
         else (encBoolZ4.symm (f x - f (x + a) + sh (x + a))).2)
    invFun := fun gw x =>
      if hx : x k = 0 then gw.1 ⟨x, hx⟩
      else gw.1 ⟨x + a, hflip1 x hx⟩ +
        encBoolZ4 (gw.2 (x + a), gw.2 x) - sh (x + a)
    left_inv := fun f => by
      ext x
      by_cases hx : x k = 0
      · simp [hx]
      · have hx1 : (x + a) k = 0 := hflip1 x hx
        have hxa_a : (x + a) + a = x := f2_add_cancel_right x a
        simp only [hx, ↓reduceDIte, ↓reduceIte, hx1, hxa_a, Prod.mk.eta, Equiv.apply_symm_apply]
        ring
    right_inv := fun ⟨g, w⟩ => by
      apply Prod.ext
      · ext ⟨x, hx⟩; simp [hx]
      · ext x
        by_cases hx : x k = 0
        · have hxa1 : (x + a) k ≠ 0 := by rw [hflip0 x hx]; decide
          have hxa_a : (x + a) + a = x := f2_add_cancel_right x a
          simp only [hx, hxa1, ↓reduceDIte, ↓reduceIte, hxa_a]
          have hsimp : g ⟨x, hx⟩ + encBoolZ4 (w x, w (x + a)) - sh x - g ⟨x, hx⟩ + sh x =
              encBoolZ4 (w x, w (x + a)) := by ring
          rw [hsimp, Equiv.symm_apply_apply]
        · have hxa0 : (x + a) k = 0 := hflip1 x hx
          simp only [hx, hxa0, ↓reduceDIte, ↓reduceIte]
          have hsimp : g ⟨x + a, hxa0⟩ + encBoolZ4 (w (x + a), w x) - sh (x + a) -
              g ⟨x + a, hxa0⟩ + sh (x + a) = encBoolZ4 (w (x + a), w x) := by ring
          rw [hsimp, Equiv.symm_apply_apply] },
    fun f x hx => by simp [hx],
    fun f x hx => by simp [hx]⟩

private lemma z4Phase_pauliExpect_eq_sum_boolSgn {n : ℕ} {a b : F2 n} {k : Fin n} (hk : a k = 1)
    (f : F2 n → ZMod 4) (w : F2 n → Bool)
    (hw0 : ∀ x, x k = 0 →
      w x = (encBoolZ4.symm (f (x + a) - f x +
        ((if dot a b = 1 then 1 else 0) + (if dot b x = 1 then 2 else 0)))).1)
    (hw1 : ∀ x, x k ≠ 0 →
      w x = (encBoolZ4.symm (f x - f (x + a) +
        ((if dot a b = 1 then 1 else 0) + (if dot b (x + a) = 1 then 2 else 0)))).2) :
    (innerProd (z4PhaseState f) (pauliApply (a, b) (z4PhaseState f))).re =
      (∑ x : F2 n, (boolSgn (w x) : ℝ)) / (2 : ℝ) ^ n := by
  have hd_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hflip0 : ∀ x : F2 n, x k = 0 → (x + a) k = 1 := fun x hx => by simp [Pi.add_apply, hx, hk]
  have hflip1 : ∀ x : F2 n, x k ≠ 0 → (x + a) k = 0 := fun x hx => by
    have hx1 : x k = 1 := (zmod2_cases (x k)).resolve_left hx
    simp [Pi.add_apply, hx1, hk]; decide
  have hbase : innerProd (z4PhaseState f) (pauliApply (a, b) (z4PhaseState f)) =
      (((1 / (2 : ℝ) ^ n : ℝ) : ℂ)) *
        ∑ x : F2 n, pauliPh (a, b) * (chi b x : ℂ) * z4Pow (f (x + a) - f x) := by
    simp only [innerProd, pauliApply, z4PhaseState, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul, Complex.star_def, Complex.conj_ofReal]
    have hsc : (((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)) =
        ((1 / (2 : ℝ) ^ n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1
      rw [← sq, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd_pos)]
    calc ((starRingEnd ℂ) (z4Pow (f x)) * ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)) *
          (pauliPh (a, b) * (chi b x : ℂ) * (((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * z4Pow (f (x + a))))
        = (((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)) *
            (pauliPh (a, b) * (chi b x : ℂ) * (star (z4Pow (f x)) * z4Pow (f (x + a)))) := by
          simp only [Complex.star_def]; ring
      _ = _ := by rw [hsc, star_z4Pow_mul]
  rw [hbase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, one_div_mul_eq_div]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (F2 n)) (fun x => x k = 0)]
  have hpair1 : ∑ x ∈ Finset.univ.filter (fun x : F2 n => ¬x k = 0),
      pauliPh (a, b) * (chi b x : ℂ) * z4Pow (f (x + a) - f x) =
      ∑ x ∈ Finset.univ.filter (fun x : F2 n => x k = 0),
        pauliPh (a, b) * (chi b x : ℂ) * ((chi b a : ℂ) * z4Pow (-(f (x + a) - f x))) := by
    refine Finset.sum_bij (fun x _ => x + a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hflip1 x hx
    · intro x1 _ x2 _ h; have := congr_arg (· + a) h; simpa [f2_add_cancel_right] using this
    · intro y hy
      refine ⟨y + a, ?_, f2_add_cancel_right y a⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hflip0 y hy]; decide
    · intro x _
      rw [f2_add_cancel_right, chi_add_right]
      have hneg : f (x + a) - f x = -(f x - f (x + a)) := by ring
      have hsq : (chi b a : ℂ) * (chi b a : ℂ) = 1 := by
        rw [← Int.cast_mul, chi_mul_self, Int.cast_one]
      rw [hneg]; push_cast
      calc pauliPh (a, b) * (chi b x : ℂ) * z4Pow (-(f x - f (x + a)))
          = pauliPh (a, b) * (chi b x : ℂ) * ((chi b a : ℂ) * (chi b a : ℂ)) * z4Pow (-(f x - f (x + a))) := by
            rw [hsq, mul_one]
        _ = _ := by ring
  rw [hpair1, ← Finset.sum_add_distrib, Complex.re_sum]
  conv_rhs =>
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (F2 n)) (fun x => x k = 0)]
  have hpair2 : ∑ x ∈ Finset.univ.filter (fun x : F2 n => ¬x k = 0), (boolSgn (w x) : ℝ) =
      ∑ x ∈ Finset.univ.filter (fun x : F2 n => x k = 0), (boolSgn (w (x + a)) : ℝ) := by
    refine Finset.sum_bij (fun x _ => x + a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hflip1 x hx
    · intro x1 _ x2 _ h; have := congr_arg (· + a) h; simpa [f2_add_cancel_right] using this
    · intro y hy
      refine ⟨y + a, ?_, f2_add_cancel_right y a⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hflip0 y hy]; decide
    · intro x _; rw [f2_add_cancel_right]
  rw [hpair2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx0 : x k = 0 := (Finset.mem_filter.mp hx).2
  have hxa1 : (x + a) k ≠ 0 := by rw [hflip0 x hx0]; decide
  have hxa_a : (x + a) + a = x := f2_add_cancel_right x a
  have hL : pauliPh (a, b) * (chi b x : ℂ) * z4Pow (f (x + a) - f x) +
      pauliPh (a, b) * (chi b x : ℂ) * ((chi b a : ℂ) * z4Pow (-(f (x + a) - f x))) =
      pauliPh (a, b) * (chi b x : ℂ) * (z4Pow (f (x + a) - f x) + (chi b a : ℂ) * z4Pow (-(f (x + a) - f x))) := by
    ring
  rw [hL]
  have hlem := z4Pow_pair_eq_boolSgn (dot a b) (dot b x) (f (x + a) - f x)
  dsimp only at hlem
  have he1 := hw0 x hx0
  have he2 : w (x + a) = (encBoolZ4.symm (f (x + a) - f x +
      ((if dot a b = 1 then 1 else 0) + (if dot b x = 1 then 2 else 0)))).2 := by
    simpa [hxa_a] using hw1 (x + a) hxa1
  rw [he1, he2]
  have hph : pauliPh (a, b) = if dot a b = 0 then 1 else Complex.I := rfl
  have hcs : chi b x = if dot b x = 0 then 1 else -1 := rfl
  have hch : chi b a = if dot a b = 0 then 1 else -1 := by simp [chi, dot_comm]
  rw [hph, hcs, hch]
  simpa [Int.cast_add] using hlem

/-- **Exact Finite `ℤ₄`-Phase Averaging Identity (ALL `n ≥ 1`, ALL `a ≠ 0`, ALL `b`)**:
    Over all `4^(2^n)` functions `f : F2 n → ZMod 4`, the exact average of `|⟨ψ_f | P_{a,b} | ψ_f⟩|`
    equals the central binomial probability `C(2^n, 2^(n-1)) / 2^(2^n)`! -/
theorem avg_pauliExpect_z4Phase_eq_centralBinom {n : ℕ} (hn : 1 ≤ n)
    {a : F2 n} (ha : a ≠ 0) (b : F2 n) :
    ∑ f : F2 n → ZMod 4, |(innerProd (z4PhaseState f) (pauliApply (a, b) (z4PhaseState f))).re| =
      (4 : ℝ) ^ (2 ^ n) * ((Nat.choose (2 ^ n) (2 ^ (n - 1)) : ℝ) / (2 : ℝ) ^ (2 ^ n)) := by
  have hd_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hd_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt hd_pos
  have hexk : ∃ k : Fin n, a k = 1 := by
    by_contra hall; push Not at hall
    exact ha (funext fun i => (zmod2_cases (a i)).resolve_right (hall i))
  obtain ⟨k, hk⟩ := hexk
  have hH0_card : Fintype.card {x : F2 n // x k = 0} = 2 ^ (n - 1) := by
    have hbij : (Finset.univ.filter fun x : F2 n => x k = 0).card =
        (Finset.univ.filter fun x : F2 n => x k = 1).card := by
      refine Finset.card_bij (fun x _ => x + a) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        simp [Pi.add_apply, hx, hk]
      · intro x1 _ x2 _ h; have := congr_arg (· + a) h; simpa [f2_add_cancel_right] using this
      · intro y hy
        refine ⟨y + a, ?_, f2_add_cancel_right y a⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        simp [Pi.add_apply, hy, hk]; decide
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (F2 n)))
      (p := fun x => x k = 0)
    have h1eq : Finset.univ.filter (fun x : F2 n => ¬x k = 0) =
        Finset.univ.filter (fun x : F2 n => x k = 1) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases zmod2_cases (x k) with h | h <;> simp [h]
    rw [h1eq, ← hbij, Finset.card_univ, card_F2] at htot
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    have hfcard : (Finset.univ.filter fun x : F2 n => x k = 0).card = 2 ^ (n - 1) := by omega
    rw [Fintype.card_subtype]; exact hfcard
  obtain ⟨e, he1_all, he2_all⟩ := z4Phase_pair_equiv_exists (b := b) hk
  have hexpect : ∀ f : F2 n → ZMod 4,
      (innerProd (z4PhaseState f) (pauliApply (a, b) (z4PhaseState f))).re =
        (∑ x : F2 n, (boolSgn ((e f).2 x) : ℝ)) / (2 : ℝ) ^ n := fun f =>
    z4Phase_pauliExpect_eq_sum_boolSgn hk f (e f).2 (he1_all f) (he2_all f)
  simp_rw [hexpect, abs_div, abs_of_pos hd_pos, ← Finset.sum_div]
  have hsum_e : ∑ f : F2 n → ZMod 4, |∑ x : F2 n, (boolSgn ((e f).2 x) : ℝ)| =
      ∑ p : ({x : F2 n // x k = 0} → ZMod 4) × (F2 n → Bool), |∑ x : F2 n, (boolSgn (p.2 x) : ℝ)| :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hsum_e, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard_H0_fun : Fintype.card ({x : F2 n // x k = 0} → ZMod 4) = 4 ^ (2 ^ (n - 1)) := by
    rw [Fintype.card_fun, ZMod.card, hH0_card]
  rw [hcard_H0_fun]
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hcb_sum : (∑ w : F2 n → Bool, |(∑ x : F2 n, (boolSgn (w x) : ℝ))|) =
      ((2 * 2 ^ (n - 1) * Nat.choose (2 * 2 ^ (n - 1)) (2 ^ (n - 1)) : ℕ) : ℝ) :=
    sum_abs_boolSgn_eq_centralBinom (α := F2 n) (m := 2 ^ (n - 1)) (by rw [card_F2, h2n])
  rw [hcb_sum, ← h2n]
  push_cast
  have hpow4 : ((4 : ℝ) ^ (2 ^ (n - 1))) * (2 : ℝ) ^ (2 ^ n) = (4 : ℝ) ^ (2 ^ n) := by
    have h4eq : (4 : ℝ) ^ (2 ^ n) = (4 : ℝ) ^ (2 ^ (n - 1)) * (4 : ℝ) ^ (2 ^ (n - 1)) := by
      rw [← pow_add, show 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n by omega]
    have h2eq : (2 : ℝ) ^ (2 ^ n) = (4 : ℝ) ^ (2 ^ (n - 1)) := by
      rw [h2n, pow_mul]; norm_num
    rw [h4eq, h2eq]
  field_simp [hd_ne, ne_of_gt (show (0 : ℝ) < (2 : ℝ) ^ (2 ^ n) by positivity)]
  rw [← hpow4]; ring

/-- Elementary 3-line induction: `(4m + 1) * (C(2m, m) / 2^(2m))² ≥ 5 / 4` for ALL `m ≥ 1`! -/
lemma centralBinom_sq_ge {m : ℕ} (hm : 1 ≤ m) :
    (5 / 4 : ℝ) ≤ (4 * (m : ℝ) + 1) * ((Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m)) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.choose]
  | succ k hk ih =>
    have hrec : (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) / (2 : ℝ) ^ (2 * (k + 1)) =
        ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) * ((Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)) := by
      have hnat : (k + 1) * Nat.choose (2 * k + 2) (k + 1) = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by
        have h1 := Nat.add_one_mul_choose_eq (2 * k + 1) k
        have h2 : Nat.choose (2 * k + 1) k = Nat.choose (2 * k + 1) (k + 1) := by
          rw [← Nat.choose_symm (by omega : k ≤ 2 * k + 1)]; congr 1; omega
        have h3 : Nat.choose (2 * k + 2) (k + 1) = 2 * Nat.choose (2 * k + 1) k := by
          rw [Nat.choose_succ_succ, ← h2]; omega
        have h4 : (k + 1) * Nat.choose (2 * k + 1) k = (2 * k + 1) * Nat.choose (2 * k) k := by
          have ha := Nat.choose_succ_right_eq (2 * k + 1) k
          have hb := Nat.add_one_mul_choose_eq (2 * k) k
          -- Simpler: use `(2k+1 - k) * C(2k+1, k) = (k+1) * C(2k+1, k+1)` and `h1`!
          have hc : (2 * k + 1) * Nat.choose (2 * k) k = (k + 1) * Nat.choose (2 * k + 1) (k + 1) := by
            have := Nat.add_one_mul_choose_eq (2 * k) k
            linarith
          rw [← h2] at hc; exact hc.symm
        linarith
      have hc : (((k + 1 : ℕ) : ℝ)) * (Nat.choose (2 * (k + 1)) (k + 1) : ℝ) =
          2 * (2 * (k : ℝ) + 1) * (Nat.choose (2 * k) k : ℝ) := by
        have := congr_arg (Nat.cast (R := ℝ)) hnat
        push_cast at this; simpa [Nat.mul_add] using this
      have hp : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; ring
      rw [hp]
      have hk1 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
      have h2p : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
      field_simp [hk1, h2p]
      push_cast at hc; linarith
    rw [hrec, mul_pow]
    have hstep : (4 * (k : ℝ) + 1) ≤
        (4 * ((k + 1 : ℕ) : ℝ) + 1) * ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) ^ 2 := by
      have hk2 : (0 : ℝ) < (2 * (k : ℝ) + 2) ^ 2 := by positivity
      rw [div_pow, mul_div_assoc', le_div_iff₀ hk2]
      push_cast; nlinarith
    have hnn : 0 ≤ ((Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)) ^ 2 := sq_nonneg _
    calc (5 / 4 : ℝ) ≤ (4 * (k : ℝ) + 1) * ((Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)) ^ 2 := ih
      _ ≤ (4 * ((k + 1 : ℕ) : ℝ) + 1) * ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) ^ 2 *
            ((Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)) ^ 2 := mul_le_mul_of_nonneg_right hstep hnn
      _ = _ := by ring

/-- **Exact Asymptotic Lower Bound `1 - 2 ρₙ = Ω(2⁻ⁿ/²)` (ALL `n ≥ 4`)**:
    For EVERY `n ≥ 4`, there exists a valid Pauli sign assignment `s : PauliIdx n → ℤ` with
      `(1 / 7) / √(2ⁿ) ≤ 1 - 2 ρₙ(s)`.
    Combined with `frustPairs_ge_spectral_two_inv_sqrt` (`1 - 2 ρₙ(s) < 2 / √(2ⁿ)`), this completely
    determines the exact asymptotic scaling `1 - 2 ρₙ = Θ(2⁻ⁿ/²)`! -/
theorem exists_signAssign_omega_inv_sqrt {n : ℕ} (hn : 4 ≤ n) :
    ∃ s : PauliIdx n → ℤ, IsSignAssign s ∧
      (1 / 7 : ℝ) / Real.sqrt ((2 : ℝ) ^ n) ≤
        1 - 2 * (frustPairs (nzPts n) s : ℝ) /
          (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) := by
  let d : ℝ := (2 : ℝ) ^ n
  let B : ℝ := (Nat.choose (2 ^ n) (2 ^ (n - 1)) : ℝ) / (2 : ℝ) ^ (2 ^ n)
  let L1 : (F2 n → ZMod 4) → ℝ := fun f =>
    ∑ p ∈ nzPts n, |(innerProd (z4PhaseState f) (pauliApply p (z4PhaseState f))).re|
  -- Compute exact total `∑_f L1 f ≥ 4^(2^n) * d * (d - 1) * B`!
  have hsum_L1 : (4 : ℝ) ^ (2 ^ n) * (d * (d - 1) * B) ≤ ∑ f : F2 n → ZMod 4, L1 f := by
    simp only [L1]
    rw [Finset.sum_comm]
    let NZ_a := (nzPts n).filter fun p : PauliIdx n => p.1 ≠ 0
    have hsub : ∑ p ∈ NZ_a, ∑ f : F2 n → ZMod 4,
        |(innerProd (z4PhaseState f) (pauliApply p (z4PhaseState f))).re| ≤
        ∑ p ∈ nzPts n, ∑ f : F2 n → ZMod 4,
          |(innerProd (z4PhaseState f) (pauliApply p (z4PhaseState f))).re| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
        Finset.sum_nonneg fun _ _ => abs_nonneg _
    have heach : ∀ p ∈ NZ_a,
        ∑ f : F2 n → ZMod 4, |(innerProd (z4PhaseState f) (pauliApply p (z4PhaseState f))).re| =
        (4 : ℝ) ^ (2 ^ n) * B := fun p hp => by
      have ha : p.1 ≠ 0 := (Finset.mem_filter.mp hp).2
      rcases p with ⟨a, b⟩
      exact avg_pauliExpect_z4Phase_eq_centralBinom (by omega) ha b
    have hcard_NZa : (NZ_a.card : ℝ) = d * (d - 1) := by
      have hflt : NZ_a = (Finset.univ.erase (0 : F2 n)) ×ˢ (Finset.univ : Finset (F2 n)) := by
        ext ⟨a, b⟩; simp only [NZ_a, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
          Finset.mem_product, and_true]
        exact ⟨fun ⟨_, ha⟩ => ha, fun ha => ⟨fun h => ha (congr_arg Prod.fst h), ha⟩⟩
      rw [hflt, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      rw [Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
    rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul, hcard_NZa] at hsub
    linarith
  -- Finite pigeonhole: `∃ f` with `d * (d - 1) * B ≤ L1 f`!
  have hcard_F : ((Finset.univ : Finset (F2 n → ZMod 4)).card : ℝ) = (4 : ℝ) ^ (2 ^ n) := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, card_F2]; push_cast; rfl
  have hex_f : ∃ f : F2 n → ZMod 4, d * (d - 1) * B ≤ L1 f := by
    by_contra hall; push Not at hall
    have hlt : ∑ f ∈ (Finset.univ : Finset (F2 n → ZMod 4)), L1 f <
        ∑ _f ∈ (Finset.univ : Finset (F2 n → ZMod 4)), d * (d - 1) * B :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun f _ => hall f
    rw [Finset.sum_const, nsmul_eq_mul, hcard_F] at hlt
    linarith
  obtain ⟨f, hf⟩ := hex_f
  -- Let `ψ = z4PhaseState f` and extract its sign assignment `s`!
  let ψ := z4PhaseState f
  have hunit : IsUnitState ψ := z4PhaseState_unit f
  let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  have hs : IsSignAssign s :=
    ⟨by simp [s], fun p hp => by simp only [s, hp, ↓reduceIte]; split_ifs <;> simp⟩
  refine ⟨s, hs, ?_⟩
  have hd_ge16 : (16 : ℝ) ≤ d := by
    have : (16 : ℕ) ≤ 2 ^ n := calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hd_pos : 0 < d := by linarith only [hd_ge16]
  have hT2_pos : 0 < d * (d ^ 2 - 1) := by nlinarith only [hd_ge16]
  -- Show `(731 / 1000) * √T2 ≤ L1 f` using `centralBinom_sq_ge`!
  have hB_sq : (5 / 4 : ℝ) ≤ (2 * d + 1) * B ^ 2 := by
    have hm1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have hcb := centralBinom_sq_ge hm1
    have h2n : 2 * 2 ^ (n - 1) = 2 ^ n := by
      conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    have h4m : 4 * ((2 ^ (n - 1) : ℕ) : ℝ) + 1 = 2 * d + 1 := by
      have hcast : ((2 * 2 ^ (n - 1) : ℕ) : ℝ) = (2 : ℝ) ^ n := by exact_mod_cast h2n
      push_cast at hcast ⊢; dsimp only [d]; linarith only [hcast]
    rw [h4m, h2n] at hcb; exact hcb
  have hL1_lb : (731 / 1000 : ℝ) * Real.sqrt (d * (d ^ 2 - 1)) ≤ L1 f := by
    have hB_nn : 0 ≤ B := by positivity
    have hL1_nn : 0 ≤ L1 f := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsq : ((731 / 1000 : ℝ) * Real.sqrt (d * (d ^ 2 - 1))) ^ 2 ≤ (L1 f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)]
      have h1 : (d * (d - 1) * B) ^ 2 ≤ (L1 f) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by nlinarith only [hd_ge16]) hB_nn) hf 2
      have h2 : (731 / 1000 : ℝ) ^ 2 * (d * (d ^ 2 - 1)) * (2 * d + 1) ≤
          (d * (d - 1)) ^ 2 * (5 / 4) := by
        have hcore : (731 / 1000 : ℝ) ^ 2 * (d + 1) * (2 * d + 1) ≤ (5 / 4 : ℝ) * d * (d - 1) := by
          nlinarith only [hd_ge16]
        have hdd : 0 ≤ d * (d - 1) := by nlinarith only [hd_ge16]
        have hl : (731 / 1000 : ℝ) ^ 2 * (d * (d ^ 2 - 1)) * (2 * d + 1) =
            (d * (d - 1)) * ((731 / 1000 : ℝ) ^ 2 * (d + 1) * (2 * d + 1)) := by ring
        have hr : (d * (d - 1)) ^ 2 * (5 / 4 : ℝ) = (d * (d - 1)) * ((5 / 4 : ℝ) * d * (d - 1)) := by ring
        rw [hl, hr]; exact mul_le_mul_of_nonneg_left hcore hdd
      have h3 : (d * (d - 1)) ^ 2 * (5 / 4 : ℝ) ≤ (d * (d - 1) * B) ^ 2 * (2 * d + 1) := by
        have hdd2 : 0 ≤ (d * (d - 1)) ^ 2 := sq_nonneg _
        calc (d * (d - 1)) ^ 2 * (5 / 4 : ℝ)
            ≤ (d * (d - 1)) ^ 2 * ((2 * d + 1) * B ^ 2) := mul_le_mul_of_nonneg_left hB_sq hdd2
          _ = (d * (d - 1) * B) ^ 2 * (2 * d + 1) := by ring
      have h2d1 : 0 < 2 * d + 1 := by linarith only [hd_ge16]
      have h1m := mul_le_mul_of_nonneg_right h1 (le_of_lt h2d1)
      nlinarith only [h2, h3, h1m, h2d1]
    nlinarith only [hsq, hL1_nn, mul_nonneg (by norm_num : (0 : ℝ) ≤ 731 / 1000) (Real.sqrt_nonneg (d * (d ^ 2 - 1)))]
  -- Apply `signCubeSum_ge_of_L1`!
  have hdom : d * (d ^ 2 - 1) ≤ 2 * (L1 f) ^ 2 := by
    have hsq : ((731 / 1000 : ℝ) * Real.sqrt (d * (d ^ 2 - 1))) ^ 2 ≤ (L1 f) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL1_lb 2
    rw [mul_pow, Real.sq_sqrt (le_of_lt hT2_pos)] at hsq
    nlinarith only [hsq, hT2_pos]
  have hcube := signCubeSum_ge_of_L1 hunit hdom
  dsimp only at hcube
  set sT := Real.sqrt (d * (d ^ 2 - 1))
  have hsT_pos : 0 < sT := Real.sqrt_pos.mpr hT2_pos
  have hsT_sq : sT ^ 2 = d * (d ^ 2 - 1) := Real.sq_sqrt (le_of_lt hT2_pos)
  have hL1_3 : ((731 / 1000 : ℝ) * sT) ^ 3 ≤ (L1 f) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hL1_lb 3
  have hrest_le : Real.sqrt (d * (d ^ 2 - 1) - (L1 f) ^ 2) ≤ (6824 / 10000 : ℝ) * sT := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hsT_sq]
    have hsq : ((731 / 1000 : ℝ) * sT) ^ 2 ≤ (L1 f) ^ 2 := pow_le_pow_left₀ (by positivity) hL1_lb 2
    rw [mul_pow, hsT_sq] at hsq
    nlinarith only [hsq, hT2_pos]
  have hrest_3 : (Real.sqrt (d * (d ^ 2 - 1) - (L1 f) ^ 2)) ^ 3 ≤ ((6824 / 10000 : ℝ) * sT) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hrest_le 3
  have h14 : (1 / 14 : ℝ) * sT ^ 3 ≤ 2 * d * signCubeSum n σ := by
    have hnum : (1 / 14 : ℝ) ≤ (731 / 1000 : ℝ) ^ 3 - (6824 / 10000 : ℝ) ^ 3 := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hnum (pow_nonneg (le_of_lt hsT_pos) 3)
    have heq : ((731 / 1000 : ℝ) * sT) ^ 3 - ((6824 / 10000 : ℝ) * sT) ^ 3 =
        ((731 / 1000 : ℝ) ^ 3 - (6824 / 10000 : ℝ) ^ 3) * sT ^ 3 := by ring
    linarith only [hcube, hL1_3, hrest_3, hmul, heq]
  -- Convert `2 * d * signCubeSum n σ` to `1 - 2 * frustPairs / L`!
  let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
  have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real (by omega)
  have hL_pos : 0 < L := by
    rw [hL_eq]; exact mul_pos (mul_pos (by nlinarith only [hd_ge16]) (by linarith only [hd_ge16])) (by linarith only [hd_ge16])
  have h0 : σ 0 = 0 := by simp [σ]
  have hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp
  have hbr := (signCubeSum_eq_frustPairs_all (by omega) h0 hpm).2
  have hseq : (fun p : PauliIdx n => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = s := by
    ext p; by_cases hp : p = 0
    · subst hp; simp [s]
    · simp only [s, σ, hp, ↓reduceIte]
      by_cases hcp : 0 ≤ c p
      · simp [hcp]
      · simp only [hcp, ↓reduceIte]; norm_num
  rw [hseq] at hbr
  have hrho_eq : 1 - 2 * (frustPairs (nzPts n) s : ℝ) / L = 2 * signCubeSum n σ / L := by
    field_simp [ne_of_gt hL_pos]; linarith only [hbr]
  rw [hrho_eq, div_le_div_iff₀ (Real.sqrt_pos.mpr hd_pos) hL_pos]
  -- Show `(1/7) * L ≤ 2 * signCubeSum n σ * √d`, i.e., `(1/7) * √d * L ≤ 2 * d * signCubeSum n σ`!
  have hL_vs_sT : 2 * Real.sqrt d * L ≤ sT ^ 3 := by
    have hsT3 : sT ^ 3 = Real.sqrt d * (d * (d ^ 2 - 1) * Real.sqrt (d ^ 2 - 1)) := by
      have hm : sT = Real.sqrt d * Real.sqrt (d ^ 2 - 1) := Real.sqrt_mul (le_of_lt hd_pos) _
      calc sT ^ 3 = sT ^ 2 * sT := by ring
        _ = (d * (d ^ 2 - 1)) * (Real.sqrt d * Real.sqrt (d ^ 2 - 1)) := by rw [hsT_sq, hm]
        _ = _ := by ring
    rw [hsT3, hL_eq]
    have hcmp : 2 * ((d / 2 - 1) * (d + 2)) ≤ d * Real.sqrt (d ^ 2 - 1) := by
      have hsq : (2 * ((d / 2 - 1) * (d + 2))) ^ 2 ≤ (d * Real.sqrt (d ^ 2 - 1)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by nlinarith only [hd_ge16])]; nlinarith only [hd_ge16]
      have hr_nn : 0 ≤ d * Real.sqrt (d ^ 2 - 1) := mul_nonneg (le_of_lt hd_pos) (Real.sqrt_nonneg _)
      nlinarith only [hsq, hr_nn]
    have hnn : 0 ≤ Real.sqrt d * (d ^ 2 - 1) := mul_nonneg (Real.sqrt_nonneg d) (by nlinarith only [hd_ge16])
    have hm := mul_le_mul_of_nonneg_left hcmp hnn
    linarith only [hm]
  have hfin : (1 / 7 : ℝ) * Real.sqrt d * L ≤ 2 * d * signCubeSum n σ := by linarith only [h14, hL_vs_sT]
  have hdivd : (1 / 7 : ℝ) * L ≤ 2 * signCubeSum n σ * Real.sqrt d := by
    have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (le_of_lt hd_pos)
    have hsd_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
    have hfin' : (1 / 7 : ℝ) * Real.sqrt d * L ≤ 2 * (Real.sqrt d * Real.sqrt d) * signCubeSum n σ := by
      rwa [hsd]
    nlinarith only [hfin', hsd_pos]
  linarith only [hdivd]

/-! ### Part 4: Exact All-`n` Spike Frustration Formula & Asymptotic Suboptimality (`∀ n ≥ 2`) -/

/-- General-`n` spike sign assignment (`+1` on pure-`X`/`Z` axes, `-1` elsewhere). -/
def spikeSign (n : ℕ) (p : PauliIdx n) : ℤ :=
  if p = 0 then 0 else if p.1 = 0 ∨ p.2 = 0 then 1 else -1

lemma spikeSign_isSignAssign (n : ℕ) : IsSignAssign (spikeSign n) := by
  refine ⟨by simp [spikeSign], fun p hp => ?_⟩
  simp only [spikeSign, hp, ↓reduceIte]; split_ifs <;> simp

private lemma zmod2_mul_self' (x : ZMod 2) : x * x = x := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_add_self' (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma exists_coord_one {n : ℕ} {u : F2 n} (hu : u ≠ 0) : ∃ i : Fin n, u i = 1 := by
  by_contra hall; push Not at hall
  exact hu (funext fun i => (zmod2_cases (u i)).resolve_right (hall i))

private lemma card_dot_eq {n : ℕ} (hn : 1 ≤ n) {u : F2 n} (hu : u ≠ 0) (c : ZMod 2) :
    (Finset.univ.filter fun v : F2 n => dot u v = c).card = 2 ^ (n - 1) := by
  obtain ⟨i, hi⟩ := exists_coord_one hu
  have hdei : dot u (eVec i) = 1 := (dot_eVec_right u i).trans hi
  have heq : (Finset.univ.filter fun v : F2 n => dot u v = 0).card =
      (Finset.univ.filter fun v : F2 n => dot u v = 1).card := by
    refine Finset.card_bij (fun v _ => v + eVec i) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [dot_add_right, hv, hdei, zero_add]
    · intro v1 _ v2 _ h; have := congr_arg (· + eVec i) h; simpa [f2_add_cancel_right] using this
    · intro w hw
      refine ⟨w + eVec i, ?_, f2_add_cancel_right w (eVec i)⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [dot_add_right, hw, hdei]; decide
  have hpart : (Finset.univ.filter fun v : F2 n => dot u v = 0).card +
      (Finset.univ.filter fun v : F2 n => dot u v = 1).card = 2 ^ n := by
    rw [← Finset.card_union_of_disjoint, ← card_F2 n, ← Finset.card_univ]
    · refine congr_arg Finset.card (Finset.ext fun v => ?_)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_cases (dot u v)
    · rw [Finset.disjoint_left]; intro v h0 h1
      simp only [Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; exact absurd h1.2 (by decide)
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  rcases zmod2_cases c with rfl | rfl <;> omega

private lemma card_dot2_eq {n : ℕ} (hn : 2 ≤ n) {u v : F2 n} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) (c1 c2 : ZMod 2) :
    (Finset.univ.filter fun w : F2 n => dot u w = c1 ∧ dot v w = c2).card = 2 ^ (n - 2) := by
  have hex : ∃ (e1 e2 : F2 n), dot u e1 = 1 ∧ dot v e1 = 0 ∧ dot u e2 = 0 ∧ dot v e2 = 1 := by
    have hdiff : ∃ i : Fin n, u i ≠ v i := by
      by_contra h; push Not at h; exact huv (funext h)
    obtain ⟨i, hi⟩ := hdiff
    rcases zmod2_cases (u i) with hui | hui <;> rcases zmod2_cases (v i) with hvi | hvi
    · exact absurd (hui.trans hvi.symm) hi
    · obtain ⟨j, huj⟩ := exists_coord_one hu
      rcases zmod2_cases (v j) with hvj | hvj
      · exact ⟨eVec j, eVec i, by rw [dot_eVec_right, huj], by rw [dot_eVec_right, hvj],
          by rw [dot_eVec_right, hui], by rw [dot_eVec_right, hvi]⟩
      · refine ⟨eVec j + eVec i, eVec i, ?_, ?_, by rw [dot_eVec_right, hui], by rw [dot_eVec_right, hvi]⟩
        · rw [dot_add_right, dot_eVec_right, dot_eVec_right, huj, hui, add_zero]
        · rw [dot_add_right, dot_eVec_right, dot_eVec_right, hvj, hvi]; decide
    · obtain ⟨j, hvj⟩ := exists_coord_one hv
      rcases zmod2_cases (u j) with huj | huj
      · exact ⟨eVec i, eVec j, by rw [dot_eVec_right, hui], by rw [dot_eVec_right, hvi],
          by rw [dot_eVec_right, huj], by rw [dot_eVec_right, hvj]⟩
      · refine ⟨eVec i, eVec j + eVec i, by rw [dot_eVec_right, hui], by rw [dot_eVec_right, hvi], ?_, ?_⟩
        · rw [dot_add_right, dot_eVec_right, dot_eVec_right, huj, hui]; decide
        · rw [dot_add_right, dot_eVec_right, dot_eVec_right, hvj, hvi, add_zero]
    · exact absurd (hui.trans hvi.symm) hi
  obtain ⟨e1, e2, hu1, hv1, hu2, hv2⟩ := hex
  let F : ZMod 2 → ZMod 2 → Finset (F2 n) := fun a b =>
    Finset.univ.filter fun w : F2 n => dot u w = a ∧ dot v w = b
  have hcard_eq : ∀ a b : ZMod 2, (F a b).card = (F 0 0).card := by
    intro a b
    let shift : F2 n := (if a = 1 then e1 else 0) + (if b = 1 then e2 else 0)
    have hsu : dot u shift = a := by
      simp only [shift, dot_add_right]
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        simp [dot_zero_right, hu1, hu2]
    have hsv : dot v shift = b := by
      simp only [shift, dot_add_right]
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        simp [dot_zero_right, hv1, hv2]
    symm
    refine Finset.card_bij (fun w _ => w + shift) ?_ ?_ ?_
    · intro w hw
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [dot_add_right u, dot_add_right v, hw.1, hw.2, hsu, hsv, zero_add, zero_add]
      exact ⟨rfl, rfl⟩
    · intro w1 _ w2 _ h; have := congr_arg (· + shift) h; simpa [f2_add_cancel_right] using this
    · intro w hw
      refine ⟨w + shift, ?_, f2_add_cancel_right w shift⟩
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [dot_add_right u, dot_add_right v, hw.1, hw.2, hsu, hsv, zmod2_add_self', zmod2_add_self']
      exact ⟨rfl, rfl⟩
  have hsum4 : (F 0 0).card + (F 0 1).card + (F 1 0).card + (F 1 1).card = 2 ^ n := by
    have hdisj : ∀ a1 b1 a2 b2 : ZMod 2, (a1 ≠ a2 ∨ b1 ≠ b2) → Disjoint (F a1 b1) (F a2 b2) := by
      intro a1 b1 a2 b2 hne
      rw [Finset.disjoint_left]; intro w h1 h2
      simp only [F, Finset.mem_filter] at h1 h2
      rcases hne with ha | hb
      · exact ha (h1.2.1.symm.trans h2.2.1)
      · exact hb (h1.2.2.symm.trans h2.2.2)
    have hu1 : Disjoint (F 0 0) (F 0 1) := hdisj 0 0 0 1 (Or.inr (by decide))
    have hu2 : Disjoint (F 1 0) (F 1 1) := hdisj 1 0 1 1 (Or.inr (by decide))
    have hu3 : Disjoint (F 0 0 ∪ F 0 1) (F 1 0 ∪ F 1 1) := by
      simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hdisj 0 0 1 0 (Or.inl (by decide)), hdisj 0 1 1 0 (Or.inl (by decide))⟩,
             ⟨hdisj 0 0 1 1 (Or.inl (by decide)), hdisj 0 1 1 1 (Or.inl (by decide))⟩⟩
    have hall : (F 0 0 ∪ F 0 1) ∪ (F 1 0 ∪ F 1 1) = Finset.univ := by
      ext w; simp only [F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases zmod2_cases (dot u w) with h1 | h1 <;> rcases zmod2_cases (dot v w) with h2 | h2 <;> simp [h1, h2]
    have hc := congr_arg Finset.card hall
    rw [Finset.card_union_of_disjoint hu3, Finset.card_union_of_disjoint hu1,
        Finset.card_union_of_disjoint hu2, Finset.card_univ, card_F2] at hc
    omega
  have h2n : 2 ^ n = 4 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have h01 := hcard_eq 0 1
  have h10 := hcard_eq 1 0
  have h11 := hcard_eq 1 1
  have hcc := hcard_eq c1 c2
  change (F c1 c2).card = 2 ^ (n - 2)
  omega

private lemma card_nz_dot_zero {n : ℕ} (hn : 1 ≤ n) {u : F2 n} (hu : u ≠ 0) :
    (Finset.univ.filter fun v : F2 n => v ≠ 0 ∧ dot u v = 0).card = 2 ^ (n - 1) - 1 := by
  have h0 : (0 : F2 n) ∈ Finset.univ.filter fun v : F2 n => dot u v = 0 := by simp [dot_zero_right]
  have heq : (Finset.univ.filter fun v : F2 n => v ≠ 0 ∧ dot u v = 0) =
      (Finset.univ.filter fun v : F2 n => dot u v = 0).erase 0 := by ext v; simp [Finset.mem_erase]
  rw [heq, Finset.card_erase_of_mem h0, card_dot_eq hn hu 0]

private lemma card_nz_dot2_zero {n : ℕ} (hn : 2 ≤ n) {u v : F2 n} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) :
    (Finset.univ.filter fun w : F2 n => w ≠ 0 ∧ dot u w = 0 ∧ dot v w = 0).card = 2 ^ (n - 2) - 1 := by
  have h0 : (0 : F2 n) ∈ Finset.univ.filter fun w : F2 n => dot u w = 0 ∧ dot v w = 0 := by
    simp [dot_zero_right]
  have heq : (Finset.univ.filter fun w : F2 n => w ≠ 0 ∧ dot u w = 0 ∧ dot v w = 0) =
      (Finset.univ.filter fun w : F2 n => dot u w = 0 ∧ dot v w = 0).erase 0 := by
    ext w; simp [Finset.mem_erase]
  rw [heq, Finset.card_erase_of_mem h0, card_dot2_eq hn hu hv huv 0 0]

/-- **Exact All-`n` Spike Frustration Formula (`n ≥ 2`)**:
      `frustPairs (nzPts n) (spikeSign n) =`
      `  3 * (2^n - 1) * (2 * (2^(n-1) - 1)) + (2^n - 1) * (2^n - 2) * ((2^(n-2) - 1) * (2^n - 2))`.
    Reproduces exact `CD(W(3,2)) = 3`, `CD(W(5,2)) = 63`, `CD(W(7,2)) = 1575`, and `33015` at `n = 5`! -/
theorem frustPairs_spikeSign_all {n : ℕ} (hn : 2 ≤ n) :
    frustPairs (nzPts n) (spikeSign n) =
      3 * (2 ^ n - 1) * (2 * (2 ^ (n - 1) - 1)) +
        (2 ^ n - 1) * (2 ^ n - 2) * ((2 ^ (n - 2) - 1) * (2 ^ n - 2)) := by
  let P : PauliIdx n → PauliIdx n → Prop := fun p q =>
    p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ symp p q = 0 ∧
    gammaSgn p q * spikeSign n p * spikeSign n q * spikeSign n (p + q) = -1
  let innerCount : F2 n → F2 n → ℕ := fun a1 a2 =>
    ∑ b1 : F2 n, ∑ b2 : F2 n, if P (a1, b1) (a2, b2) then 1 else 0
  have h1 : frustPairs (nzPts n) (spikeSign n) = ∑ a1 : F2 n, ∑ a2 : F2 n, innerCount a1 a2 := by
    unfold frustPairs
    rw [Finset.card_filter, Finset.sum_product]
    have hnz : ∀ p : PauliIdx n,
        (∑ q ∈ nzPts n, if p ≠ q ∧ symp p q = 0 ∧
            gammaSgn p q * spikeSign n p * spikeSign n q * spikeSign n (p + q) = -1 then 1 else 0) =
        ∑ q : PauliIdx n, if P p q then 1 else 0 := by
      intro p
      by_cases hp : p = 0
      · subst hp
        simp only [P, ne_eq, not_true_eq_false, false_and, ↓reduceIte, Finset.sum_const_zero]
        exact Finset.sum_eq_zero fun q _ => by simp [(spikeSign_isSignAssign n).1]
      · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : PauliIdx n))]
        simp only [P, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, zero_add]
        exact Finset.sum_congr rfl fun q hq => by simp [hp, (Finset.mem_erase.mp hq).1]
    have h0zero : (∑ q : PauliIdx n, if P 0 q then 1 else 0) = 0 := by simp [P]
    have hleft : (∑ p ∈ nzPts n, ∑ q ∈ nzPts n,
          if p ≠ q ∧ symp p q = 0 ∧
            gammaSgn p q * spikeSign n p * spikeSign n q * spikeSign n (p + q) = -1 then 1 else 0) =
        ∑ p : PauliIdx n, ∑ q : PauliIdx n, if P p q then 1 else 0 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : PauliIdx n)), h0zero, zero_add]
      exact Finset.sum_congr rfl fun p _ => hnz p
    rw [hleft, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a1 _ => Finset.sum_comm
  have hsymp_iff : ∀ a1 b1 a2 b2 : F2 n, symp (a1, b1) (a2, b2) = 0 ↔ dot a1 b2 = dot a2 b1 := fun a1 b1 a2 b2 => by
    simp only [symp, dot_comm b1 a2]
    rcases zmod2_cases (dot a1 b2) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2 <;>
      simp [h1, h2, zmod2_add_self']
  have hgam_eq : ∀ a1 b1 a2 b2 : F2 n,
      gammaSgn (a1, b1) (a2, b2) = if dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 then 1 else -1 := fun a1 b1 a2 b2 => by
    simp only [gammaSgn, gammaBit, quadForm0]
    by_cases h : dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 <;> simp [h]
  -- Case 1: `(0, 0) -> 0`
  have hcase00 : innerCount 0 0 = 0 := by
    refine Finset.sum_eq_zero fun b1 _ => Finset.sum_eq_zero fun b2 _ => ?_
    rw [ite_eq_right_iff]; rintro ⟨hp, hq, hpq, _, hfr⟩
    have hpq0 : ((0 : F2 n), b1) + (0, b2) ≠ 0 := by
      intro h; apply hpq; ext k
      · rfl
      · have hb : b1 + b2 = 0 := congr_arg Prod.snd h
        have h' := congr_arg (b1 + ·) hb
        rw [f2_add_cancel_left, add_zero] at h'
        exact congr_fun h'.symm k
    have hsp : spikeSign n (0, b1) = 1 := by simp [spikeSign, hp]
    have hsq : spikeSign n (0, b2) = 1 := by simp [spikeSign, hq]
    have hspq : spikeSign n ((0, b1) + (0, b2)) = 1 := by
      simp only [spikeSign, hpq0, ↓reduceIte]
      change (if (0 : F2 n) + 0 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = 1; simp
    have hg : gammaSgn (0, b1) (0, b2) = 1 := by simp [hgam_eq, dot_zero_left]
    rw [hg, hsp, hsq, hspq] at hfr; norm_num at hfr
  -- Case 2: `(0, a2) -> 2 * (2^(n-1) - 1)`
  have hcase0n : ∀ {a2 : F2 n}, a2 ≠ 0 → innerCount 0 a2 = 2 * (2 ^ (n - 1) - 1) := by
    intro a2 ha2
    have hiff : ∀ b1 b2 : F2 n, P (0, b1) (a2, b2) ↔ (b1 ≠ 0 ∧ dot a2 b1 = 0) ∧ (b2 = 0 ∨ b2 = b1) := by
      intro b1 b2
      have hq0 : (a2, b2) ≠ 0 := fun h => ha2 (congr_arg Prod.fst h)
      have hpq : (0, b1) ≠ (a2, b2) := fun h => ha2 (congr_arg Prod.fst h).symm
      have hpq0 : ((0 : F2 n), b1) + (a2, b2) ≠ 0 := fun h => ha2 (by simpa using congr_arg Prod.fst h)
      have hg : gammaSgn (0, b1) (a2, b2) = 1 := by simp [hgam_eq, dot_zero_left]
      have hne_a : (((0 : F2 n), b1) + (a2, b2)).1 ≠ 0 := by simpa using ha2
      have hsum_b : b1 + b2 = 0 ↔ b2 = b1 :=
        ⟨fun h => by have := congr_arg (b1 + ·) h; simpa [f2_add_cancel_left] using this,
         fun h => by rw [h, f2_add_self]⟩
      by_cases hb1 : b1 = 0
      · subst hb1; simp [P]
      · have hp0 : ((0 : F2 n), b1) ≠ 0 := fun h => hb1 (congr_arg Prod.snd h)
        have hsp : spikeSign n (0, b1) = 1 := by simp [spikeSign, hp0]
        have hsq : spikeSign n (a2, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign, hq0, ha2]
        have hspq : spikeSign n ((0, b1) + (a2, b2)) = if b2 = b1 then 1 else -1 := by
          simp only [spikeSign, hpq0, ↓reduceIte, hne_a, false_or]
          change (if b1 + b2 = 0 then (1 : ℤ) else -1) = _; simp only [hsum_b]
        simp only [P, hp0, hq0, hpq, hsymp_iff, dot_zero_left, hg, hsp, hsq, hspq, hb1,
          ne_eq, not_false_eq_true, true_and]
        by_cases hdb : dot a2 b1 = 0
        · simp only [hdb, true_and]
          by_cases hb20 : b2 = 0
          · subst hb20; simp [Ne.symm hb1]
          · by_cases hb21 : b2 = b1
            · subst hb21; simp [hb20]
            · simp [hb20, hb21]
        · have hdb' : (0 : ZMod 2) ≠ dot a2 b1 := Ne.symm hdb
          simp [hdb, hdb']
    have hinner_b1 : ∀ b1 : F2 n,
        (∑ b2 : F2 n, if P (0, b1) (a2, b2) then 1 else 0) = if b1 ≠ 0 ∧ dot a2 b1 = 0 then 2 else 0 := by
      intro b1; simp_rw [hiff b1]
      by_cases h : b1 ≠ 0 ∧ dot a2 b1 = 0
      · simp only [h.1, h.2, ne_eq, not_false_eq_true, and_self, ↓reduceIte, true_and]
        rw [← Finset.card_filter]
        have hset : (Finset.univ.filter fun b2 : F2 n => b2 = 0 ∨ b2 = b1) = {0, b1} := by ext x; simp
        rw [hset, Finset.card_pair h.1.symm]
      · simp only [h, ↓reduceIte]; exact Finset.sum_eq_zero fun b2 _ => by simp
    dsimp only [innerCount]
    simp_rw [hinner_b1, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
        card_nz_dot_zero (by omega) ha2]
    ring
  -- Case 3: `(a1, 0) -> 2 * (2^(n-1) - 1)`
  have hcasen0 : ∀ {a1 : F2 n}, a1 ≠ 0 → innerCount a1 0 = 2 * (2 ^ (n - 1) - 1) := by
    intro a1 ha1
    have hsym : ∀ b1 b2 : F2 n, P (a1, b1) (0, b2) ↔ P (0, b2) (a1, b1) := by
      intro b1 b2
      have hg1 : symp (a1, b1) (0, b2) = 0 → gammaSgn (a1, b1) (0, b2) = 1 := fun hs => by
        have hd : dot a1 b2 = 0 := by simpa [hsymp_iff, dot_zero_left] using hs
        simp [hgam_eq, dot_zero_left, hd]
      have hg2 : gammaSgn (0, b2) (a1, b1) = 1 := by simp [hgam_eq, dot_zero_left]
      simp only [P, ne_comm (a := (a1, b1)), add_comm (a := (a1, b1))]
      have hs : symp (a1, b1) (0, b2) = 0 ↔ symp (0, b2) (a1, b1) = 0 := by
        simp [hsymp_iff, dot_zero_left, eq_comm]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩; refine ⟨h2, h1, h3, hs.mp h4, ?_⟩
        rw [hg1 h4] at h5; rw [hg2]; linarith
      · rintro ⟨h1, h2, h3, h4, h5⟩; have h4' := hs.mpr h4; refine ⟨h2, h1, h3, h4', ?_⟩
        rw [hg2] at h5; rw [hg1 h4']; linarith
    calc innerCount a1 0
        = ∑ b2 : F2 n, ∑ b1 : F2 n, if P (a1, b1) (0, b2) then 1 else 0 := Finset.sum_comm
      _ = innerCount 0 a1 := by dsimp only [innerCount]; simp_rw [hsym]
      _ = 2 * (2 ^ (n - 1) - 1) := hcase0n ha1
  -- Case 4: `(a1, a1) -> 2 * (2^(n-1) - 1)`
  have hcasenn_eq : ∀ {a1 : F2 n}, a1 ≠ 0 → innerCount a1 a1 = 2 * (2 ^ (n - 1) - 1) := by
    intro a1 ha1
    have hiff : ∀ b1 b2 : F2 n, P (a1, b1) (a1, b2) ↔
        (b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0) ∨ (b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0) := by
      intro b1 b2
      have hp0 : (a1, b1) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hq0 : (a1, b2) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hpq_iff : (a1, b1) ≠ (a1, b2) ↔ b1 ≠ b2 := ⟨fun h hb => h (by rw [hb]), fun h hp => h (congr_arg Prod.snd hp)⟩
      have hsp : spikeSign n (a1, b1) = if b1 = 0 then 1 else -1 := by simp [spikeSign, hp0, ha1]
      have hsq : spikeSign n (a1, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign, hq0, ha1]
      by_cases hbb : b1 = b2
      · subst hbb
        simp only [P, ne_eq, not_true_eq_false, false_and, and_false, false_iff, not_or, not_and]
        exact ⟨fun h hne _ => hne h, fun h hne _ => hne h⟩
      · have hpq0 : (a1, b1) + (a1, b2) ≠ 0 := fun h => hbb (by
          have hb : b1 + b2 = 0 := congr_arg Prod.snd h
          have := congr_arg (b1 + ·) hb; simpa [f2_add_cancel_left] using this.symm)
        have hspq : spikeSign n ((a1, b1) + (a1, b2)) = 1 := by
          simp only [spikeSign, hpq0, ↓reduceIte]
          change (if a1 + a1 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = 1; simp [f2_add_self]
        simp only [P, hp0, hq0, hpq_iff, hbb, hsymp_iff, hsp, hsq, hspq, ne_eq, not_false_eq_true, true_and]
        by_cases hcomm : dot a1 b2 = dot a1 b1
        · have hg : gammaSgn (a1, b1) (a1, b2) = 1 := by
            rw [hgam_eq, hcomm, zmod2_mul_self', zmod2_add_self']; simp
          simp only [hcomm, hg, true_and]
          by_cases hb1 : b1 = 0
          · subst hb1; simp [Ne.symm hbb, dot_zero_right] at hcomm ⊢
          · by_cases hb2 : b2 = 0
            · subst hb2; simp [hb1, dot_zero_right] at hcomm ⊢; exact hcomm.symm
            · simp [hb1, hb2]
        · simp only [hcomm, false_and, false_iff, not_or, not_and]
          exact ⟨fun hb1 _ hb20 => hcomm (by rw [hb1, dot_zero_right, hb20]),
                 fun hb2 _ hb10 => hcomm (by rw [hb2, dot_zero_right, hb10])⟩
    dsimp only [innerCount]; simp_rw [hiff]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 n))]
    have h0 : (∑ b2 : F2 n, if (0 : F2 n) = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ (0 : F2 n) ≠ 0 ∧ dot a1 0 = 0 then 1 else 0) =
        2 ^ (n - 1) - 1 := by
      simp only [true_and, ne_eq, not_true_eq_false, false_and, and_false, or_false]
      rw [← Finset.card_filter, card_nz_dot_zero (by omega) ha1]
    have hrest : ∑ b1 ∈ Finset.univ.erase (0 : F2 n),
        (∑ b2 : F2 n, if b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0 then 1 else 0) =
        2 ^ (n - 1) - 1 := by
      have heach : ∀ b1 ∈ Finset.univ.erase (0 : F2 n),
          (∑ b2 : F2 n, if b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0 then 1 else 0) =
          if dot a1 b1 = 0 then 1 else 0 := by
        intro b1 hb1
        have hb10 : b1 ≠ 0 := (Finset.mem_erase.mp hb1).1
        simp only [hb10, false_and, false_or, ne_eq, not_false_eq_true, true_and]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 n))]
        have hzero : ∑ b2 ∈ Finset.univ.erase (0 : F2 n), (if b2 = 0 ∧ dot a1 b1 = 0 then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun b2 hb2 => by simp [(Finset.mem_erase.mp hb2).1]
        rw [hzero, add_zero]; simp
      rw [Finset.sum_congr rfl heach, ← Finset.card_filter]
      have hfilt : ((Finset.univ.erase (0 : F2 n)).filter fun b1 => dot a1 b1 = 0) =
          Finset.univ.filter fun b1 => b1 ≠ 0 ∧ dot a1 b1 = 0 := by ext b1; simp [Finset.mem_erase]
      rw [hfilt, card_nz_dot_zero (by omega) ha1]
    rw [h0, hrest]; omega
  -- Case 5: `(a1, a2)` (`a1 ≠ 0, a2 ≠ 0, a1 ≠ a2`) -> `(2^(n-2) - 1) * (2^n - 2)`
  have hcasenn_ne : ∀ {a1 a2 : F2 n}, a1 ≠ 0 → a2 ≠ 0 → a1 ≠ a2 →
      innerCount a1 a2 = (2 ^ (n - 2) - 1) * (2 ^ n - 2) := by
    intro a1 a2 ha1 ha2 ha12
    have ha12_sum : a1 + a2 ≠ 0 := fun h => ha12 (by
      have := congr_arg (a1 + ·) h; simpa [f2_add_cancel_left] using this.symm)
    have hiff : ∀ b1 b2 : F2 n, P (a1, b1) (a2, b2) ↔
        b1 ≠ 0 ∧ b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = dot a2 b1 ∧ dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 := by
      intro b1 b2
      have hp0 : (a1, b1) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hq0 : (a2, b2) ≠ 0 := fun h => ha2 (congr_arg Prod.fst h)
      have hpq : (a1, b1) ≠ (a2, b2) := fun h => ha12 (congr_arg Prod.fst h)
      have hpq0 : (a1, b1) + (a2, b2) ≠ 0 := fun h => ha12_sum (congr_arg Prod.fst h)
      have hsp : spikeSign n (a1, b1) = if b1 = 0 then 1 else -1 := by simp [spikeSign, hp0, ha1]
      have hsq : spikeSign n (a2, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign, hq0, ha2]
      have hsum_b : b1 + b2 = 0 ↔ b1 = b2 :=
        ⟨fun h => by have := congr_arg (b1 + ·) h; simpa [f2_add_cancel_left] using this.symm,
         fun h => by rw [h, f2_add_self]⟩
      have hspq : spikeSign n ((a1, b1) + (a2, b2)) = if b1 = b2 then 1 else -1 := by
        simp only [spikeSign, hpq0, ↓reduceIte]
        change (if a1 + a2 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = _
        simp only [ha12_sum, false_or, hsum_b]
      simp only [P, hp0, hq0, hpq, hsymp_iff, hgam_eq, hsp, hsq, hspq, ne_eq, not_false_eq_true, true_and]
      by_cases hb1 : b1 = 0
      · subst hb1
        simp only [↓reduceIte, not_true_eq_false, false_and, iff_false, not_and]
        intro hcomm
        have hd0 : dot a1 b2 = 0 := by simpa [dot_zero_right] using hcomm
        simp only [dot_zero_right, zero_mul, zero_add, hd0, ↓reduceIte]
        by_cases hb20 : b2 = 0
        · subst hb20; simp
        · simp [hb20, Ne.symm hb20]
      · by_cases hb2 : b2 = 0
        · subst hb2
          simp only [hb1, ↓reduceIte, not_true_eq_false, false_and, and_false, iff_false, not_and]
          intro _; simp only [dot_zero_right, mul_zero, add_zero, ↓reduceIte]; norm_num
        · by_cases hbb : b1 = b2
          · subst hbb
            simp only [hb1, ↓reduceIte, not_true_eq_false, false_and, and_false, iff_false, not_and]
            intro hcomm; rw [← hcomm, zmod2_mul_self', zmod2_add_self']; norm_num
          · simp only [hb1, hb2, hbb, ↓reduceIte, not_false_eq_true, true_and]
            by_cases hcomm : dot a1 b2 = dot a2 b1
            · simp only [hcomm, true_and]
              by_cases hg : dot a1 b1 * dot a2 b2 + dot a1 b2 = 0
              · simp
              · simp
            · simp [hcomm]
    have hinner_b1 : ∀ b1 : F2 n,
        (∑ b2 : F2 n, if P (a1, b1) (a2, b2) then 1 else 0) =
        if b1 = 0 then 0
        else if dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 2 ^ (n - 1) - 2
        else if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 2 ^ (n - 2) - 1
        else if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 2 ^ (n - 2) - 1
        else 0 := by
      intro b1; simp_rw [hiff b1]
      by_cases hb1 : b1 = 0
      · subst hb1; simp
      · simp only [hb1, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
        rcases zmod2_cases (dot a1 b1) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2
        · simp only [h1, h2, ↓reduceIte, zero_mul, zero_add, and_self]
          have hset : (Finset.univ.filter fun b2 : F2 n => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 0) =
              ((Finset.univ.filter fun b2 : F2 n => dot a1 b2 = 0).erase 0).erase b1 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            exact ⟨fun ⟨a, b, c⟩ => ⟨b.symm, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a.symm, c⟩⟩
          have h0m : (0 : F2 n) ∈ Finset.univ.filter fun b2 : F2 n => dot a1 b2 = 0 := by simp [dot_zero_right]
          have hb1m : b1 ∈ (Finset.univ.filter fun b2 : F2 n => dot a1 b2 = 0).erase 0 := by
            simp [Finset.mem_erase, hb1, h1]
          rw [← Finset.card_filter, hset, Finset.card_erase_of_mem hb1m,
              Finset.card_erase_of_mem h0m, card_dot_eq (by omega) ha1 0]; omega
        · simp only [h1, h2, zero_mul, zero_add]
          have hno : ∀ b2 : F2 n, ¬(b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 1 ∧ dot a1 b2 = 0) := fun b2 ⟨_, _, ha, hb⟩ =>
            absurd (ha.symm.trans hb) (by decide)
          simp only [hno, ↓reduceIte, Finset.sum_const_zero]
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          simp [h01]
        · have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [h1, h2, h10, false_and, true_and, ↓reduceIte, one_mul]
          have hset : (Finset.univ.filter fun b2 : F2 n => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 0 ∧ dot a2 b2 + dot a1 b2 = 0) =
              Finset.univ.filter fun b2 : F2 n => b2 ≠ 0 ∧ dot a1 b2 = 0 ∧ dot a2 b2 = 0 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨h1', _, h3', h4'⟩; rw [h3', add_zero] at h4'; exact ⟨h1', h3', h4'⟩
            · rintro ⟨h1', h3', h4'⟩
              exact ⟨h1', fun heq => h10 (by rw [← h1, heq, h3']), h3', by rw [h3', h4', add_zero]⟩
          rw [← Finset.card_filter, hset, card_nz_dot2_zero hn ha1 ha2 ha12]
        · have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [h1, h2, h10, and_false, true_and, ↓reduceIte, one_mul]
          have hset : (Finset.univ.filter fun b2 : F2 n => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 1 ∧ dot a2 b2 + dot a1 b2 = 0) =
              (Finset.univ.filter fun b2 : F2 n => dot a1 b2 = 1 ∧ dot a2 b2 = 1).erase b1 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨_, hne, hd1, hd2⟩
              refine ⟨hne.symm, hd1, ?_⟩; rw [hd1] at hd2
              rcases zmod2_cases (dot a2 b2) with hc | hc
              · rw [hc] at hd2; exact absurd hd2 (by decide)
              · exact hc
            · rintro ⟨hne, hd1, hd2⟩
              refine ⟨fun h0 => h10 (by rw [← hd1, h0, dot_zero_right]), hne.symm, hd1, ?_⟩
              rw [hd1, hd2]; decide
          have hb1m : b1 ∈ Finset.univ.filter fun b2 : F2 n => dot a1 b2 = 1 ∧ dot a2 b2 = 1 := by simp [h1, h2]
          rw [← Finset.card_filter, hset, Finset.card_erase_of_mem hb1m, card_dot2_eq hn ha1 ha2 ha12 1 1]
    dsimp only [innerCount]; simp_rw [hinner_b1]
    have hsplit : ∀ b1 : F2 n,
        (if b1 = 0 then 0
          else if dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 2 ^ (n - 1) - 2
          else if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 2 ^ (n - 2) - 1
          else if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 2 ^ (n - 2) - 1
          else 0) =
        (if b1 ≠ 0 ∧ dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 2 ^ (n - 1) - 2 else 0) +
        (if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 2 ^ (n - 2) - 1 else 0) +
        (if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 2 ^ (n - 2) - 1 else 0) := by
      intro b1; by_cases hb1 : b1 = 0
      · subst hb1; simp [dot_zero_right]
      · rcases zmod2_cases (dot a1 b1) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2 <;>
          simp [hb1, h1, h2]
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [card_nz_dot2_zero hn ha1 ha2 ha12, card_dot2_eq hn ha1 ha2 ha12 1 0, card_dot2_eq hn ha1 ha2 ha12 1 1]
    have h2n1 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      ring
    have h2n : 2 ^ n = 4 * 2 ^ (n - 2) := by
      conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
      ring
    have hge1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
    have hge2 : 2 ≤ 2 ^ (n - 1) := by omega
    have hge2' : 2 ≤ 2 ^ n := by omega
    zify [hge1, hge2, hge2']
    have h2n1Z : (2 : ℤ) ^ (n - 1) = 2 * (2 : ℤ) ^ (n - 2) := by exact_mod_cast h2n1
    have h2nZ : (2 : ℤ) ^ n = 4 * (2 : ℤ) ^ (n - 2) := by exact_mod_cast h2n
    rw [h2n1Z, h2nZ]; ring
  -- Assemble over `a1, a2 : F2 n`!
  rw [h1, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 n))]
  have hcard1 : (Finset.univ.erase (0 : F2 n)).card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_F2]
  have hrow0 : ∑ a2 : F2 n, innerCount 0 a2 = (2 ^ n - 1) * (2 * (2 ^ (n - 1) - 1)) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 n)), hcase00, zero_add]
    rw [Finset.sum_congr rfl fun a2 ha2 => hcase0n (Finset.mem_erase.mp ha2).1,
        Finset.sum_const, smul_eq_mul, hcard1]
  have hrown : ∀ a1 ∈ Finset.univ.erase (0 : F2 n),
      ∑ a2 : F2 n, innerCount a1 a2 =
        2 * (2 * (2 ^ (n - 1) - 1)) + (2 ^ n - 2) * ((2 ^ (n - 2) - 1) * (2 ^ n - 2)) := by
    intro a1 ha1
    have ha10 : a1 ≠ 0 := (Finset.mem_erase.mp ha1).1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 n)), hcasen0 ha10]
    rw [← Finset.add_sum_erase (Finset.univ.erase 0) _ (Finset.mem_erase.mpr ⟨ha10, Finset.mem_univ _⟩),
        hcasenn_eq ha10]
    have hcard2 : ((Finset.univ.erase (0 : F2 n)).erase a1).card = 2 ^ n - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha10, Finset.mem_univ _⟩), hcard1]; omega
    rw [Finset.sum_congr rfl fun a2 ha2 =>
          hcasenn_ne ha10 (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha2)).1
            (Finset.mem_erase.mp ha2).1.symm,
        Finset.sum_const, smul_eq_mul, hcard2]
    ring
  rw [hrow0, Finset.sum_congr rfl hrown, Finset.sum_const, smul_eq_mul, hcard1]
  ring

/-- **Exact `O(2⁻ⁿ)` Frustration Gap of `spikeSign n` (ALL `n ≥ 2`)**:
      `1 - 2 * ρₙ(spikeSign n) = 9 * (2^n - 2) / ((2^n + 1) * (2^n + 2))`. -/
theorem spikeSign_frust_gap_eq {n : ℕ} (hn : 2 ≤ n) :
    1 - 2 * (frustPairs (nzPts n) (spikeSign n) : ℝ) /
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) =
      9 * ((2 : ℝ) ^ n - 2) / (((2 : ℝ) ^ n + 1) * ((2 : ℝ) ^ n + 2)) := by
  let d : ℝ := (2 : ℝ) ^ n
  let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
  have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real hn
  have hd_ge4 : (4 : ℝ) ≤ d := by
    have : (4 : ℕ) ≤ 2 ^ n := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hL_ne : L ≠ 0 := ne_of_gt (by
    rw [hL_eq]; exact mul_pos (mul_pos (by nlinarith only [hd_ge4]) (by linarith only [hd_ge4])) (by linarith only [hd_ge4]))
  have hsp : (frustPairs (nzPts n) (spikeSign n) : ℝ) =
      3 * (d - 1) * (d - 2) + (d - 1) * (d - 2) * ((d / 4 - 1) * (d - 2)) := by
    rw [frustPairs_spikeSign_all hn]
    have hge1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hge2 : 2 ≤ 2 ^ n := calc 2 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hge1' : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have hge1'' : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
    have h2n1 : (2 : ℝ) ^ (n - 1) = d / 2 := by
      have : d = 2 * (2 : ℝ) ^ (n - 1) := by
        simp only [d]; conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        ring
      linarith
    have h2n2 : (2 : ℝ) ^ (n - 2) = d / 4 := by
      have : d = 4 * (2 : ℝ) ^ (n - 2) := by
        simp only [d]; conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
        ring
      linarith
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_sub hge1, Nat.cast_sub hge1', Nat.cast_sub hge2, Nat.cast_sub hge1'']
    push_cast; rw [h2n1, h2n2]; ring
  change 1 - 2 * (frustPairs (nzPts n) (spikeSign n) : ℝ) / L = 9 * (d - 2) / ((d + 1) * (d + 2))
  rw [hsp]
  have hd12 : (d + 1) * (d + 2) ≠ 0 := by nlinarith only [hd_ge4]
  field_simp [hL_ne, hd12]
  rw [hL_eq]; ring

/-- **Asymptotic Suboptimality of `spikeSign n` (ALL `n ≥ 12`)**:
    Because `1 - 2 ρₙ(spikeSign n) = Θ(2⁻ⁿ)` while `max_s (1 - 2 ρₙ(s)) = Ω(2⁻ⁿ/²)`,
    for EVERY `n ≥ 12` there exists a valid sign assignment strictly beating `spikeSign n`! -/
theorem spikeSign_strictly_suboptimal_asymptotic {n : ℕ} (hn : 12 ≤ n) :
    ∃ s : PauliIdx n → ℤ, IsSignAssign s ∧
      frustPairs (nzPts n) s < frustPairs (nzPts n) (spikeSign n) := by
  obtain ⟨s, hs, hlb⟩ := exists_signAssign_omega_inv_sqrt (n := n) (by omega)
  refine ⟨s, hs, ?_⟩
  let d : ℝ := (2 : ℝ) ^ n
  let L : ℝ := (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ)
  have hd_ge : (4096 : ℝ) ≤ d := by
    have : (4096 : ℕ) ≤ 2 ^ n := calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    dsimp only [d]; exact_mod_cast this
  have hL_pos : 0 < L := by
    have hL_eq : L = (d ^ 2 - 1) * (d / 2 - 1) * (d + 2) := totalCommPairs_real (n := n) (by omega)
    rw [hL_eq]; exact mul_pos (mul_pos (by nlinarith only [hd_ge]) (by linarith only [hd_ge])) (by linarith only [hd_ge])
  have hsp := spikeSign_frust_gap_eq (n := n) (by omega)
  have hsqrt_gt : (63 : ℝ) < Real.sqrt d := by
    rw [Real.lt_sqrt (by norm_num)]; linarith only [hd_ge]
  have hstrict : 9 * (d - 2) / ((d + 1) * (d + 2)) < (1 / 7 : ℝ) / Real.sqrt d := by
    have hden1 : 0 < (d + 1) * (d + 2) := by nlinarith only [hd_ge]
    have hden2 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith only [hd_ge])
    rw [div_lt_div_iff₀ hden1 hden2]
    have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith only [hd_ge])
    have h63 : 63 * (d - 2) * Real.sqrt d < (d - 2) * d := by
      have h1 : 63 * Real.sqrt d < d := by
        calc 63 * Real.sqrt d < Real.sqrt d * Real.sqrt d := by nlinarith only [hsqrt_gt, hden2]
          _ = d := hsq
      have h2 : 0 < d - 2 := by linarith only [hd_ge]
      nlinarith only [h1, h2]
    nlinarith only [h63, hd_ge]
  have hltR : (frustPairs (nzPts n) s : ℝ) < (frustPairs (nzPts n) (spikeSign n) : ℝ) := by
    have hcmp : 1 - 2 * (frustPairs (nzPts n) (spikeSign n) : ℝ) / L <
        1 - 2 * (frustPairs (nzPts n) s : ℝ) / L := lt_of_lt_of_le (hsp.symm ▸ hstrict) hlb
    have h2 : 2 * (frustPairs (nzPts n) s : ℝ) / L < 2 * (frustPairs (nzPts n) (spikeSign n) : ℝ) / L := by
      linarith only [hcmp]
    rw [mul_div_assoc, mul_div_assoc] at h2
    have : (frustPairs (nzPts n) s : ℝ) / L < (frustPairs (nzPts n) (spikeSign n) : ℝ) / L := by
      linarith only [h2]
    exact (div_lt_div_iff_of_pos_right hL_pos).mp this
  exact_mod_cast hltR

end AsymptoticContextuality

-- Re-export main theorems at `MultiQubitMUB` root namespace for clean Audit access.
export AsymptoticContextuality (
  signCubeSum_le_spectral
  frustPairs_ge_spectral
  frustPairs_ge_spectral_two_inv_sqrt
  ellipticSignCubeSum
  ellipticSignCubeSum_le_spectral
  elliptic_frustPairs_ge_spectral
  matTr_cube_ge_of_rayleigh
  signCubeSum_ge_of_L1
  pauliMoment4_ge_of_contextuality_const
  z4Pow
  z4PhaseState
  z4PhaseState_unit
  avg_pauliExpect_z4Phase_eq_centralBinom
  centralBinom_sq_ge
  exists_signAssign_omega_inv_sqrt
  spikeSign
  spikeSign_isSignAssign
  frustPairs_spikeSign_all
  spikeSign_frust_gap_eq
  spikeSign_strictly_suboptimal_asymptotic
)

end MultiQubitMUB
