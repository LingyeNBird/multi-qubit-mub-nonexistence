import MultiQubitMUB.AsymptoticPauliSlicing

/-!
# Stage 17–18 Final Milestone — All-`k` Subgroup Mass Concentration (Theorem 17.5),
  Complete All-`m` Real Pauli-SIC Classification (Theorem 17.6),
  Exact Self-Dual Twisted Autocorrelation Identities (Identities I & II),
  and Indefinite `(1, 1)`-Spread `βₘ*` Reduction (Theorem 18.1)

Formalizes four unconditional general-`m` pure-theory theorem groups (zero `sorry`,
zero `native_decide`, zero `set_option`, standard three Lean axioms
`[propext, Classical.choice, Quot.sound]` only, zero edits to upstream modules):

1. **Theorem 17.5 — All-`k` Additive-Subgroup Mass Concentration, `𝒥ₘ` Lower Bounds & Unified Quadric–Subspace Coset Identity (ALL `m`)**:
   - `sum_pauliSq_subspace`: exact mass split across `H^⊥` and `(H^⊥)^c` for any additive subgroup `H ⊆ PauliIdx m`.
   - `twoStateJ_ge_of_subspace` & `twoStateJ_ge_two_add_subspace_gap`:
       `2 + S_H² / (2 (|H| - 1)) - (1 + S_H) / 2ᵐ ≤ 𝒥ₘ(φ₁, φ₂)`.
   - `twoStateJ_ge_of_k_stabilizers`: whenever either slice is stabilized by `H`,
       `2 + (|H| - 1) / 8 - |H| / 2ᵐ ≤ 𝒥ₘ(φ₁, φ₂)`.
   - `sum_pauliSq_quadric_coset`: unified quadric–subspace coset identity
       `∑_{r ∈ H^⊥, Q_{p₀}(r) = 0} c_r(φ)² = (2ᵐ / (2 |H|)) ∑_{q ∈ H} (c_q(φ)² + w_{p₀ + q}(φ))`.

2. **Theorem 17.6 — Complete Elementary Classification of Multi-Qubit Real Pauli-SICs (ALL `m ≥ 2, m ≠ 4`)**:
   - `pauliExpect_eq_zero_of_real_antisym`: real states have `c_p(φ) = 0` on every antisymmetric Pauli (`Q₀(p) ≠ 0`).
   - `no_real_pauli_sic_all`: for EVERY `m ≥ 2` with `m ≠ 4` and EVERY real unit state `φ : QState m`,
       `3 * 2ᵐ / (2ᵐ + 2) < pauliMoment4 m φ`
     (proved in 3 steps via `Tr(S_real³) ∈ ℤ` vs `√(2^{m-1} + 1) ∉ ℚ`, dual to complex Pauli-SIC `n ∈ {1, 3}`).

3. **Identities I & II — Exact Self-Dual Twisted Autocorrelation Equations (ALL `m`, ALL State Pairs)**:
   - `sum_innerProd_pauliApply_mul`: universal Pauli completeness / `SWAP` contraction
       `∑_p ⟨u₁ | P_p | v₁⟩ ⟨u₂ | P_p | v₂⟩ = 2ᵐ ⟨u₁ | v₂⟩ ⟨u₂ | v₁⟩`.
   - `crossPauli_selfDual_deriv` (Identity I):
       `∑_p (-1)^{ω(p,s)} γ(p,h) ⟨φ₁|P_p|φ₂⟩ ⟨φ₁|P_{p+h}|φ₂⟩ = 2ᵐ γ(s,h) ⟨φ₁|P_s|φ₂⟩ ⟨φ₁|P_{s+h}|φ₂⟩`.
   - `crossPauli_autocorr_outer` (Identity II):
       `∑_p (-1)^{ω(p,s)} γ(p,h) ⟨φ₁|P_p|φ₂⟩* ⟨φ₁|P_{p+h}|φ₂⟩ = 2ᵐ γ(s,h) ⟨φ₁|P_s|φ₁⟩ ⟨φ₂|P_{s+h}|φ₂⟩`.

4. **Theorem 18.1 — Unconditional Indefinite `(1, 1)`-Spread `βₘ*` Reduction (ALL `m ≥ 1`)**:
   - `sum_pauliDiff_sq` & `sum_pauliDiff_pow4_le`: exact `ℓ₂` norm `2 D (1 - |⟨φ₁|φ₂⟩|²)` and `ℓ₄` bound.
   - `twoState_indefiniteSpread_ge`: for every unit pair `(φ₁, φ₂)`, choosing `τ_r = sgn(c_r⁺ - c_r⁻)` yields
       `(⟨φ₁|S(τ)|φ₁⟩ - ⟨φ₂|S(τ)|φ₂⟩)² / (2 D (D² - 1)) ≥ (D² / (D² - 1)) * 4 (1 - |⟨φ₁|φ₂⟩|²)³ / ((F₁ + F₂ - 2) + 6 C + 4 (√(F₁ - 1) + √(F₂ - 1)) √C)`.
   - `twoState_indefiniteSpread_le_of_bulkFloor`: any universal bulk-eigenvalue floor `c₀ T₂ ≤ ∑_{j ≠ max, min} λ_j(S(τ))²`
     forces `(⟨e₁|S(τ)|e₁⟩ - ⟨e₂|S(τ)|e₂⟩)² ≤ 2 (1 - c₀) T₂` for all unit `e₁, e₂`.
-/

namespace MultiQubitMUB

open scoped Classical
open FourQubitCD
open GeneralContextualityLift
open AsymptoticContextuality
open AsymptoticBarriers
open AsymptoticChar2Theory
open AsymptoticPauliSlicing

namespace AsymptoticSubspaceAndRealSIC

/-! ### Part 1: Theorem 17.5 — All-`k` Subgroup Mass Concentration & Unified Quadric–Coset Identity -/

/-- Character-orthogonality indicator for any additive subgroup `H ⊆ PauliIdx m`:
    `∑_{q ∈ H} (-1)^{ω(q, r)} = |H|` if `r ∈ H^⊥`, and `0` otherwise. -/
lemma sum_sympSign_subgroup {m : ℕ} (H : Finset (PauliIdx m))
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) (r : PauliIdx m) :
    ∑ q ∈ H, (sympSign q r : ℝ) =
      if (∀ q ∈ H, symp q r = 0) then (H.card : ℝ) else 0 := by
  split_ifs with horth
  · have ht : ∀ q ∈ H, (sympSign q r : ℝ) = 1 := fun q hq => by simp [sympSign, horth q hq]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul, mul_one]
  · push Not at horth
    obtain ⟨q₀, hq₀H, hq₀_ne⟩ := horth
    have hsgn : (sympSign q₀ r : ℝ) = -1 := by simp [sympSign, hq₀_ne]
    have hbij : ∑ q ∈ H, (sympSign (q₀ + q) r : ℝ) = ∑ q ∈ H, (sympSign q r : ℝ) := by
      refine Finset.sum_bij (fun q _ => q₀ + q) (fun q hq => hadd q₀ hq₀H q hq) ?_ ?_ (fun _ _ => rfl)
      · intro a _ b _ hab
        have := congr_arg (q₀ + ·) hab
        simpa [pauliIdx_add_cancel_left] using this
      · intro b hb
        refine ⟨q₀ + b, hadd q₀ hq₀H b hb, ?_⟩
        rw [pauliIdx_add_cancel_left]
    have hneg : ∑ q ∈ H, (sympSign (q₀ + q) r : ℝ) = -(∑ q ∈ H, (sympSign q r : ℝ)) := by
      have ht : ∀ q ∈ H, (sympSign (q₀ + q) r : ℝ) = -(sympSign q r : ℝ) := fun q _ => by
        rw [sympSign_comm (q₀ + q) r, sympSign_add_right, sympSign_comm r q₀, sympSign_comm r q,
            Int.cast_mul, hsgn]
        ring
      rw [Finset.sum_congr rfl ht, Finset.sum_neg_distrib]
    linarith

/-- Exact cardinality of `H^⊥` and its complement inside `nzPts m` for any additive subgroup `H`. -/
lemma card_nz_filter_subspace {m : ℕ} (H : Finset (PauliIdx m))
    (h0 : (0 : PauliIdx m) ∈ H) (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) :
    (((nzPts m).filter (fun r => ∀ q ∈ H, symp q r = 0)).card : ℝ) =
      ((2 : ℝ) ^ m) ^ 2 / (H.card : ℝ) - 1 ∧
    (((nzPts m).filter (fun r => ¬∀ q ∈ H, symp q r = 0)).card : ℝ) =
      ((2 : ℝ) ^ m) ^ 2 * (1 - 1 / (H.card : ℝ)) := by
  have hcard_pos : (0 : ℝ) < (H.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨0, h0⟩)
  have hcard_ne : (H.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  let S0 := (nzPts m).filter (fun r => ∀ q ∈ H, symp q r = 0)
  let S1 := (nzPts m).filter (fun r => ¬∀ q ∈ H, symp q r = 0)
  let Full0 := Finset.univ.filter (fun r : PauliIdx m => ∀ q ∈ H, symp q r = 0)
  have hsum_full : (H.card : ℝ) * (Full0.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 := by
    have hL : ∑ r : PauliIdx m, ∑ q ∈ H, (sympSign q r : ℝ) = (H.card : ℝ) * (Full0.card : ℝ) := by
      simp_rw [sum_sympSign_subgroup H hadd, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm]
    have hR : ∑ r : PauliIdx m, ∑ q ∈ H, (sympSign q r : ℝ) = ((2 : ℝ) ^ m) ^ 2 := by
      rw [Finset.sum_comm]
      have hterm : ∀ q ∈ H, ∑ r : PauliIdx m, (sympSign q r : ℝ) =
          if q = 0 then ((2 : ℝ) ^ m) ^ 2 else 0 := fun q _ => by
        have hcast : ∑ r : PauliIdx m, (sympSign q r : ℝ) =
            ((∑ r : PauliIdx m, sympSign q r : ℤ) : ℝ) := by rw [Int.cast_sum]
        rw [hcast, sum_sympSign_univ q]
        split_ifs
        · push_cast
          have h4 : (4 : ℝ) = 2 * 2 := by norm_num
          rw [h4, mul_pow, sq]
        · simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' H (0 : PauliIdx m)]
      simp [h0]
    linarith
  have hfull_eq : (Full0.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 / (H.card : ℝ) :=
    (eq_div_iff hcard_ne).mpr (by linarith)
  have h0_mem : (0 : PauliIdx m) ∈ Full0 := by
    simp [Full0, symp_zero_right]
  have hS0_eq : S0 = Full0.erase 0 := by
    ext r; simp [S0, Full0, nzPts, and_comm]
  have hS0_card : (S0.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 / (H.card : ℝ) - 1 := by
    rw [hS0_eq, Finset.card_erase_of_mem h0_mem]
    have hpos : 1 ≤ Full0.card := Finset.one_le_card.mpr ⟨0, h0_mem⟩
    rw [Nat.cast_sub hpos, Nat.cast_one, hfull_eq]
  have hadd_card : (S0.card : ℝ) + (S1.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 - 1 := by
    have h1 := Finset.sum_filter_add_sum_filter_not (nzPts m)
      (fun r => ∀ q ∈ H, symp q r = 0) (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [h1]; exact card_PauliIdx_erase_zero m
  have hS1_card : (S1.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 * (1 - 1 / (H.card : ℝ)) := by
    have : (S1.card : ℝ) = ((2 : ℝ) ^ m) ^ 2 - ((2 : ℝ) ^ m) ^ 2 / (H.card : ℝ) := by linarith
    rw [this]; ring
  exact ⟨hS0_card, hS1_card⟩

/-- **Theorem 17.5(a) — Exact All-`k` Additive-Subgroup Mass Concentration Identity (ALL `m`, ALL `H`)**:
    For every unit state `φ : QState m` and additive subgroup `H ⊆ PauliIdx m` (`0 ∈ H`),
      `∑_{r ∈ H^⊥ \ {0}} c_r(φ)² = (2ᵐ / |H|) (1 + ∑_{q ∈ H \ {0}} c_q(φ)²) - 1`. -/
theorem sum_pauliSq_subspace {m : ℕ} {φ : QState m} (hunit : IsUnitState φ)
    (H : Finset (PauliIdx m)) (h0 : (0 : PauliIdx m) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) :
    let D : ℝ := (2 : ℝ) ^ m
    let cH : ℝ := ∑ q ∈ H.erase 0, (innerProd φ (pauliApply q φ)).re ^ 2
    ∑ r ∈ (nzPts m).filter (fun r => ∀ q ∈ H, symp q r = 0),
        (innerProd φ (pauliApply r φ)).re ^ 2 = (D / (H.card : ℝ)) * (1 + cH) - 1 ∧
    ∑ r ∈ (nzPts m).filter (fun r => ¬∀ q ∈ H, symp q r = 0),
        (innerProd φ (pauliApply r φ)).re ^ 2 = D - (D / (H.card : ℝ)) * (1 + cH) := by
  intro D cH
  have hcard_pos : (0 : ℝ) < (H.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨0, h0⟩)
  have hcard_ne : (H.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  let S0 := (nzPts m).filter (fun r => ∀ q ∈ H, symp q r = 0)
  let S1 := (nzPts m).filter (fun r => ¬∀ q ∈ H, symp q r = 0)
  let Full0 := Finset.univ.filter (fun r : PauliIdx m => ∀ q ∈ H, symp q r = 0)
  have hre_ns : ∀ r : PauliIdx m, Complex.normSq (innerProd φ (pauliApply r φ)) =
      (innerProd φ (pauliApply r φ)).re ^ 2 := fun r => by
    have hre := innerProd_pauliApply_self_real r φ
    conv_lhs => rw [← hre]
    rw [Complex.normSq_ofReal, ← sq]
  -- Evaluate `∑ r, (∑ q ∈ H, sympSign q r) * c_r²` in two ways!
  have hL : ∑ r : PauliIdx m, (∑ q ∈ H, (sympSign q r : ℝ)) *
        (innerProd φ (pauliApply r φ)).re ^ 2 =
      (H.card : ℝ) * ∑ r ∈ Full0, (innerProd φ (pauliApply r φ)).re ^ 2 := by
    simp_rw [sum_sympSign_subgroup H hadd, ite_mul, zero_mul, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
    rfl
  have hR : ∑ r : PauliIdx m, (∑ q ∈ H, (sympSign q r : ℝ)) *
        (innerProd φ (pauliApply r φ)).re ^ 2 =
      D * ∑ q ∈ H, (innerProd φ (pauliApply q φ)).re ^ 2 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsd := pauli_symp_self_dual φ q
    simp_rw [hre_ns, sympSign_comm _ q] at hsd
    exact hsd
  have hsum_full : ∑ r ∈ Full0, (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D / (H.card : ℝ)) * (1 + cH) := by
    have hq_split : ∑ q ∈ H, (innerProd φ (pauliApply q φ)).re ^ 2 = 1 + cH := by
      rw [← Finset.add_sum_erase _ _ h0, pauliExpect_zero_re hunit, one_pow]
    rw [hq_split] at hR
    have heq : (H.card : ℝ) * ∑ r ∈ Full0, (innerProd φ (pauliApply r φ)).re ^ 2 =
        D * (1 + cH) := by linarith
    have hdiv : ∑ r ∈ Full0, (innerProd φ (pauliApply r φ)).re ^ 2 =
        (D * (1 + cH)) / (H.card : ℝ) := (eq_div_iff hcard_ne).mpr (by linarith)
    rw [hdiv]; ring
  have h0_mem : (0 : PauliIdx m) ∈ Full0 := by simp [Full0, symp_zero_right]
  have hS0_eq : S0 = Full0.erase 0 := by ext r; simp [S0, Full0, nzPts, and_comm]
  have hS0 : ∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D / (H.card : ℝ)) * (1 + cH) - 1 := by
    have hsplit := Finset.add_sum_erase Full0
      (fun r => (innerProd φ (pauliApply r φ)).re ^ 2) h0_mem
    rw [pauliExpect_zero_re hunit, one_pow, ← hS0_eq] at hsplit
    linarith
  have hadd_sum : ∑ r ∈ S0, (innerProd φ (pauliApply r φ)).re ^ 2 +
      ∑ r ∈ S1, (innerProd φ (pauliApply r φ)).re ^ 2 = D - 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_nz_pauliExpect_sq hunit]
  exact ⟨hS0, by linarith⟩

/-- **Theorem 17.5(b) — Exact General-Subgroup Partition Lower Bound on `𝒥ₘ` (ALL `m`, ALL `1 < |H| < 4ᵐ`)**. -/
theorem twoStateJ_ge_of_subspace {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (H : Finset (PauliIdx m)) (h0 : (0 : PauliIdx m) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H)
    (hK_gt : 1 < H.card) (hK_lt : H.card < (2 ^ m) ^ 2) :
    let D : ℝ := (2 : ℝ) ^ m
    let K : ℝ := (H.card : ℝ)
    let SH : ℝ := (∑ q ∈ H.erase 0,
      ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2)) / 2
    3 / 2 + (((2 * D / K) * (1 + SH) - 2) ^ 2 / (D ^ 2 / K - 1) +
             (2 * D - (2 * D / K) * (1 + SH)) ^ 2 / (D ^ 2 * (1 - 1 / K))) / 8 ≤
      twoStateJ φ₁ φ₂ := by
  intro D K SH
  have hK_gt1 : (1 : ℝ) < K := by dsimp only [K]; exact_mod_cast hK_gt
  have hK_pos : 0 < K := by linarith
  have hK_ltD2 : K < D ^ 2 := by
    have hnat : (H.card : ℝ) < (((2 ^ m) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hK_lt
    simpa [D, K] using hnat
  have hN0_pos : 0 < D ^ 2 / K - 1 := by
    rw [sub_pos, lt_div_iff₀ hK_pos]; linarith
  have hN1_pos : 0 < D ^ 2 * (1 - 1 / K) := by
    have h1K : 0 < 1 - 1 / K := by
      rw [sub_pos, div_lt_one hK_pos]; exact hK_gt1
    have hD2_pos : 0 < D ^ 2 := by positivity
    exact mul_pos hD2_pos h1K
  obtain ⟨hc0, hc1⟩ := card_nz_filter_subspace H h0 hadd
  obtain ⟨hp0, hp1⟩ := sum_pauliSq_subspace h1 H h0 hadd
  obtain ⟨hq0, hq1⟩ := sum_pauliSq_subspace h2 H h0 hadd
  dsimp only [D, K, SH]
  refine twoStateJ_ge_of_partition h1 h2 (fun r => ∀ q ∈ H, symp q r = 0)
    hN0_pos hN1_pos hc0 hc1 ?_ ?_
  · rw [Finset.sum_add_distrib, hp0, hq0, Finset.sum_add_distrib]; ring
  · rw [Finset.sum_add_distrib, hp1, hq1, Finset.sum_add_distrib]; ring

/-- **Theorem 17.5(c) — Clean Closed-Form Subgroup Excess Lower Bound on `𝒥ₘ` (ALL `m`, ALL `1 < |H| < 4ᵐ`)**:
      `2 + S_H² / (2 (|H| - 1)) - (1 + S_H) / 2ᵐ ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_two_add_subspace_gap {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (H : Finset (PauliIdx m)) (h0 : (0 : PauliIdx m) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H)
    (hK_gt : 1 < H.card) (hK_lt : H.card < (2 ^ m) ^ 2) :
    let D : ℝ := (2 : ℝ) ^ m
    let K : ℝ := (H.card : ℝ)
    let SH : ℝ := (∑ q ∈ H.erase 0,
      ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2)) / 2
    2 + SH ^ 2 / (2 * (K - 1)) - (1 + SH) / D ≤ twoStateJ φ₁ φ₂ := by
  intro D K SH
  have hbase := twoStateJ_ge_of_subspace h1 h2 H h0 hadd hK_gt hK_lt
  dsimp only at hbase
  have hD_pos : 0 < D := by positivity
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hK_gt1 : (1 : ℝ) < K := by dsimp only [K]; exact_mod_cast hK_gt
  have hK_pos : 0 < K := by linarith
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hKm1_pos : 0 < K - 1 := by linarith
  have hKm1_ne : K - 1 ≠ 0 := ne_of_gt hKm1_pos
  have hK_ltD2 : K < D ^ 2 := by
    have hnat : (H.card : ℝ) < (((2 ^ m) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hK_lt
    simpa [D, K] using hnat
  have hN0_pos : 0 < D ^ 2 / K - 1 := by rw [sub_pos, lt_div_iff₀ hK_pos]; linarith
  -- Drop `-1` in `D²/K - 1 < D²/K` (strictly lowering the first term):
  have hdrop : ((2 * D / K) * (1 + SH) - 2) ^ 2 / (D ^ 2 / K) ≤
      ((2 * D / K) * (1 + SH) - 2) ^ 2 / (D ^ 2 / K - 1) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hN0_pos (by linarith)
  have hident : 3 / 2 + (((2 * D / K) * (1 + SH) - 2) ^ 2 / (D ^ 2 / K) +
      (2 * D - (2 * D / K) * (1 + SH)) ^ 2 / (D ^ 2 * (1 - 1 / K))) / 8 =
      2 + SH ^ 2 / (2 * (K - 1)) - (1 + SH) / D + K / (2 * D ^ 2) := by
    have h1K_ne : 1 - 1 / K ≠ 0 := by
      have : 0 < 1 - 1 / K := by rw [sub_pos, div_lt_one hK_pos]; exact hK_gt1
      exact ne_of_gt this
    field_simp [hD_ne, hK_ne, hKm1_ne, h1K_ne]; ring
  have hrem_nn : 0 ≤ K / (2 * D ^ 2) := by positivity
  dsimp only [D, K, SH] at hdrop hident hrem_nn ⊢
  linarith

/-- **Corollary of Theorem 17.5 — `k`-Stabilizer Subgroup Bound on `𝒥ₘ` (ALL `m`, ALL `1 < |H| < 4ᵐ`)**:
    Whenever EITHER `φ₁` or `φ₂` is stabilized by every element of `H` (`∀ q ∈ H, c_q² = 1`),
      `2 + (|H| - 1) / 8 - |H| / 2ᵐ ≤ 𝒥ₘ(φ₁, φ₂)`. -/
theorem twoStateJ_ge_of_k_stabilizers {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂)
    (H : Finset (PauliIdx m)) (h0 : (0 : PauliIdx m) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H)
    (hK_gt : 1 < H.card) (hK_lt : H.card < (2 ^ m) ^ 2)
    (hstab : (∀ q ∈ H, (innerProd φ₁ (pauliApply q φ₁)).re ^ 2 = 1) ∨
             (∀ q ∈ H, (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 = 1)) :
    let D : ℝ := (2 : ℝ) ^ m
    let K : ℝ := (H.card : ℝ)
    2 + (K - 1) / 8 - K / D ≤ twoStateJ φ₁ φ₂ := by
  intro D K
  have hbase := twoStateJ_ge_two_add_subspace_gap h1 h2 H h0 hadd hK_gt hK_lt
  dsimp only at hbase
  let SH : ℝ := (∑ q ∈ H.erase 0,
    ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2)) / 2
  have hD_pos : 0 < D := by positivity
  have hK_gt1 : (1 : ℝ) < K := by dsimp only [K]; exact_mod_cast hK_gt
  have hKm1_pos : 0 < K - 1 := by linarith
  have hcard_er : ((H.erase 0).card : ℝ) = K - 1 := by
    rw [Finset.card_erase_of_mem h0]
    have h1le : 1 ≤ H.card := Finset.one_le_card.mpr ⟨0, h0⟩
    rw [Nat.cast_sub h1le, Nat.cast_one]
  -- Lower bound `SH ≥ (K - 1) / 2` from the stabilized slice!
  have hSH_ge : (K - 1) / 2 ≤ SH := by
    dsimp only [SH]
    have hsum_ge : K - 1 ≤ ∑ q ∈ H.erase 0,
        ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2) := by
      have hterm : ∀ q ∈ H.erase 0, (1 : ℝ) ≤
          (innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 := fun q hq => by
        have hqH : q ∈ H := (Finset.mem_erase.mp hq).2
        have hnn1 : 0 ≤ (innerProd φ₁ (pauliApply q φ₁)).re ^ 2 := sq_nonneg _
        have hnn2 : 0 ≤ (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 := sq_nonneg _
        rcases hstab with h | h
        · linarith [h q hqH]
        · linarith [h q hqH]
      have hle := Finset.sum_le_sum hterm
      simpa [Finset.sum_const, nsmul_eq_mul, mul_one, hcard_er] using hle
    linarith
  -- Upper bound `SH ≤ K - 1` since `c_q(φ)² ≤ 1` for every unit state `φ`!
  have hcq_le1 : ∀ (φ : QState m) (_hu : IsUnitState φ) (q : PauliIdx m),
      (innerProd φ (pauliApply q φ)).re ^ 2 ≤ 1 := fun φ hu q => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (F2 m))
      (fun x => ‖φ x‖) (fun x => ‖pauliApply q φ x‖)
    have hre_le : |(innerProd φ (pauliApply q φ)).re| ≤
        ∑ x : F2 m, ‖φ x‖ * ‖pauliApply q φ x‖ := by
      calc |(innerProd φ (pauliApply q φ)).re|
          ≤ ‖innerProd φ (pauliApply q φ)‖ := Complex.abs_re_le_norm _
        _ ≤ ∑ x : F2 m, ‖star (φ x) * pauliApply q φ x‖ := norm_sum_le _ _
        _ = ∑ x : F2 m, ‖φ x‖ * ‖pauliApply q φ x‖ := by
            refine Finset.sum_congr rfl fun x _ => by rw [norm_mul, norm_star]
    have hφn : ∑ x : F2 m, ‖φ x‖ ^ 2 = 1 := by
      have h := innerProd_self_re φ
      rw [hu, Complex.one_re] at h
      simpa [Complex.normSq_eq_norm_sq] using h.symm
    have hPφn : ∑ x : F2 m, ‖pauliApply q φ x‖ ^ 2 = 1 := by
      have h := innerProd_self_re (pauliApply q φ)
      rw [innerProd_pauliApply_both, hu, Complex.one_re] at h
      simpa [Complex.normSq_eq_norm_sq] using h.symm
    calc (innerProd φ (pauliApply q φ)).re ^ 2
        = |(innerProd φ (pauliApply q φ)).re| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ x : F2 m, ‖φ x‖ * ‖pauliApply q φ x‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hre_le 2
      _ ≤ (∑ x : F2 m, ‖φ x‖ ^ 2) * (∑ x : F2 m, ‖pauliApply q φ x‖ ^ 2) := hcs
      _ = 1 := by rw [hφn, hPφn, mul_one]
  have hSH_le : SH ≤ K - 1 := by
    dsimp only [SH]
    have hsum_le : ∑ q ∈ H.erase 0,
        ((innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2) ≤
        2 * (K - 1) := by
      have hterm : ∀ q ∈ H.erase 0,
          (innerProd φ₁ (pauliApply q φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply q φ₂)).re ^ 2 ≤ 2 :=
        fun q _ => by linarith [hcq_le1 φ₁ h1 q, hcq_le1 φ₂ h2 q]
      have hle := Finset.sum_le_sum hterm
      simpa [Finset.sum_const, nsmul_eq_mul, hcard_er, mul_comm] using hle
    linarith
  have h1 : (K - 1) / 8 ≤ SH ^ 2 / (2 * (K - 1)) := by
    have hsq : ((K - 1) / 2) ^ 2 ≤ SH ^ 2 := pow_le_pow_left₀ (by linarith) hSH_ge 2
    have hdiv := div_le_div_of_nonneg_right hsq (show (0 : ℝ) ≤ 2 * (K - 1) by linarith)
    have heq : ((K - 1) / 2) ^ 2 / (2 * (K - 1)) = (K - 1) / 8 := by
      field_simp [ne_of_gt hKm1_pos]; ring
    linarith
  have h2' : (1 + SH) / D ≤ K / D := div_le_div_of_nonneg_right (by linarith) (le_of_lt hD_pos)
  dsimp only [D, K, SH] at h1 h2' ⊢
  linarith

/-- **Theorem 17.5(d) — Unified Quadric–Subspace Coset Identity (ALL `m`, ALL `φ`, ALL `H`, ALL `p₀`)**:
      `∑_{r ∈ H^⊥, Q_{p₀}(r) = 0} c_r(φ)² = (2ᵐ / (2 |H|)) ∑_{q ∈ H} (c_q(φ)² + w_{p₀ + q}(φ))`. -/
theorem sum_pauliSq_quadric_coset {m : ℕ} (φ : QState m)
    (H : Finset (PauliIdx m)) (h0 : (0 : PauliIdx m) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) (p₀ : PauliIdx m) :
    ∑ r ∈ Finset.univ.filter (fun r : PauliIdx m => (∀ q ∈ H, symp q r = 0) ∧ quadForm p₀ r = 0),
        (innerProd φ (pauliApply r φ)).re ^ 2 =
      ((2 : ℝ) ^ m / (2 * (H.card : ℝ))) *
        ∑ q ∈ H, ((innerProd φ (pauliApply q φ)).re ^ 2 + symPauliNormSq φ (p₀ + q)) := by
  let D : ℝ := (2 : ℝ) ^ m
  have hD_ne : D ≠ 0 := by positivity
  have hcard_pos : (0 : ℝ) < (H.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨0, h0⟩)
  have h2K_ne : (2 * (H.card : ℝ)) ≠ 0 := by positivity
  have hre_ns : ∀ r : PauliIdx m, Complex.normSq (innerProd φ (pauliApply r φ)) =
      (innerProd φ (pauliApply r φ)).re ^ 2 := fun r => by
    have hre := innerProd_pauliApply_self_real r φ
    conv_lhs => rw [← hre]
    rw [Complex.normSq_ofReal, ← sq]
  -- Pointwise indicator identity:
  -- `∑_{q ∈ H} (sympSign q r + (-1)^{Q_{p₀+q}(r)}) = if (r ∈ H^⊥ ∧ Q_{p₀}(r) = 0) then 2|H| else 0`!
  have hind : ∀ r : PauliIdx m,
      ∑ q ∈ H, ((sympSign q r : ℝ) + (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1)) =
        if ((∀ q ∈ H, symp q r = 0) ∧ quadForm p₀ r = 0) then 2 * (H.card : ℝ) else 0 := fun r => by
    have hmul_char : ∀ q : PauliIdx m,
        (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1) =
          (sympSign q r : ℝ) * (if quadForm p₀ r = 0 then (1 : ℝ) else -1) := fun q => by
      have hq : quadForm (p₀ + q) r = quadForm p₀ r + symp q r := by
        simp only [quadForm, symp_add_left]; ring
      rw [hq]
      rcases zmod2_cases (quadForm p₀ r) with h1 | h1 <;>
        rcases zmod2_cases (symp q r) with h2 | h2 <;>
        simp [sympSign, h1, h2, show (1 : ZMod 2) + 1 = 0 by decide,
              show (1 : ZMod 2) ≠ 0 by decide]
    have hfact : ∑ q ∈ H, ((sympSign q r : ℝ) + (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1)) =
        (∑ q ∈ H, (sympSign q r : ℝ)) * (1 + (if quadForm p₀ r = 0 then (1 : ℝ) else -1)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by rw [hmul_char q]; ring
    rw [hfact, sum_sympSign_subgroup H hadd r]
    split_ifs <;> first | (exfalso; tauto) | ring
  have hL : ∑ r : PauliIdx m,
        (∑ q ∈ H, ((sympSign q r : ℝ) + (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1))) *
          (innerProd φ (pauliApply r φ)).re ^ 2 =
      (2 * (H.card : ℝ)) *
        ∑ r ∈ Finset.univ.filter (fun r : PauliIdx m => (∀ q ∈ H, symp q r = 0) ∧ quadForm p₀ r = 0),
          (innerProd φ (pauliApply r φ)).re ^ 2 := by
    simp_rw [hind, ite_mul, zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      ← Finset.mul_sum]
  have hR : ∑ r : PauliIdx m,
        (∑ q ∈ H, ((sympSign q r : ℝ) + (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1))) *
          (innerProd φ (pauliApply r φ)).re ^ 2 =
      D * ∑ q ∈ H, ((innerProd φ (pauliApply q φ)).re ^ 2 + symPauliNormSq φ (p₀ + q)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ r : PauliIdx m, (sympSign q r : ℝ) * (innerProd φ (pauliApply r φ)).re ^ 2 =
        D * (innerProd φ (pauliApply q φ)).re ^ 2 := by
      have hsd := pauli_symp_self_dual φ q
      simp_rw [hre_ns, sympSign_comm _ q] at hsd
      exact hsd
    have h2 : ∑ r : PauliIdx m, (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1) *
          (innerProd φ (pauliApply r φ)).re ^ 2 = D * symPauliNormSq φ (p₀ + q) := by
      have hw := symPauliNormSq_eq_sympWHT φ (p₀ + q)
      have hmul : D * symPauliNormSq φ (p₀ + q) =
          ∑ r : PauliIdx m, (if quadForm (p₀ + q) r = 0 then (1 : ℝ) else -1) *
            (innerProd φ (pauliApply r φ)).re ^ 2 := by
        rw [hw]; dsimp only [D]; field_simp [hD_ne]
      exact hmul.symm
    rw [h1, h2]; ring
  have heq : (2 * (H.card : ℝ)) *
      ∑ r ∈ Finset.univ.filter (fun r : PauliIdx m => (∀ q ∈ H, symp q r = 0) ∧ quadForm p₀ r = 0),
        (innerProd φ (pauliApply r φ)).re ^ 2 =
      D * ∑ q ∈ H, ((innerProd φ (pauliApply q φ)).re ^ 2 + symPauliNormSq φ (p₀ + q)) := by
    linarith
  have hdiv : ∑ r ∈ Finset.univ.filter (fun r : PauliIdx m => (∀ q ∈ H, symp q r = 0) ∧ quadForm p₀ r = 0),
      (innerProd φ (pauliApply r φ)).re ^ 2 =
      (D * ∑ q ∈ H, ((innerProd φ (pauliApply q φ)).re ^ 2 + symPauliNormSq φ (p₀ + q))) /
        (2 * (H.card : ℝ)) :=
    (eq_div_iff h2K_ne).mpr (by linarith)
  rw [hdiv]; dsimp only [D]; ring

/-! ### Part 2: Theorem 17.6 — Complete Elementary Classification of Multi-Qubit Real Pauli-SICs -/

/-- Every real state has zero Pauli expectation on every antisymmetric Pauli (`Q₀(p) ≠ 0`). -/
theorem pauliExpect_eq_zero_of_real_antisym {m : ℕ} {φ : QState m}
    (hreal : ∀ x : F2 m, (φ x).im = 0) {p : PauliIdx m} (hp : quadForm0 p ≠ 0) :
    (innerProd φ (pauliApply p φ)).re = 0 := by
  have hstar : (fun x : F2 m => star (φ x)) = φ := by
    funext x
    apply Complex.ext
    · simp
    · simp [hreal x]
  have h0 := symPauliExpect_eq_zero_of_antisym φ hp
  rw [symPauliExpect, hstar] at h0
  rw [h0, Complex.zero_re]

/-- **Theorem 17.6 — Complete All-`m` Classification of Multi-Qubit Real Pauli-SICs (`m ≥ 2, m ≠ 4`)**:
    For EVERY `m ∈ {2, 3} ∪ {5, 6, 7, …}` and EVERY real unit state `φ : QState m`,
      `3 * 2ᵐ / (2ᵐ + 2) < pauliMoment4 m φ`.
    (Tight ONLY at `m = 1` with `|H⟩` attaining `3/2`, and `m = 4` with the 135-point real Pauli-SIC
    attaining `8/3`, since `2^{m-1} + 1 = k² ⇔ m = 4` by `pow_two_add_one_ne_sq`!) -/
theorem no_real_pauli_sic_all {m : ℕ} (hm : 2 ≤ m) (hm4 : m ≠ 4)
    {φ : QState m} (hunit : IsUnitState φ) (hreal : ∀ x : F2 m, (φ x).im = 0) :
    3 * (2 : ℝ) ^ m / ((2 : ℝ) ^ m + 2) < pauliMoment4 m φ := by
  refine lt_of_le_of_ne (pauliMoment4_real_state_ge (by omega) hunit hreal) fun heq => ?_
  let D : ℝ := (2 : ℝ) ^ m
  let c : PauliIdx m → ℝ := fun p => (innerProd φ (pauliApply p φ)).re
  have hD_ge4 : (4 : ℝ) ≤ D := by
    have : (4 : ℕ) ≤ 2 ^ m := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    dsimp only [D]; exact_mod_cast this
  have hD_pos : 0 < D := by linarith
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hD2_pos : 0 < D + 2 := by linarith
  have hD2_ne : D + 2 ≠ 0 := ne_of_gt hD2_pos
  let symNz : Finset (PauliIdx m) := (nzPts m).filter (fun p => quadForm0 p = 0)
  -- Step 1: Cardinality of `symNz` is `(D - 1)(D + 2) / 2`.
  have hcard_symNz : (symNz.card : ℝ) = (D - 1) * (D + 2) / 2 := by
    have hq := (card_nz_filter_quadForm (m := m) (p := 0) (by simp [quadForm0, dot_zero_left])).1
    have hset : symNz = (nzPts m).filter (fun r => quadForm (0 : PauliIdx m) r = 0) := by
      ext r; simp [symNz, quadForm, symp_zero_left]
    rw [hset]
    exact hq
  -- Step 2: All non-zero Pauli mass lies on `symNz`, and `pauliMoment4 m φ = 3D/(D+2)` forces
  -- `c p ^ 2 = 2 / (D + 2)` for every `p ∈ symNz`.
  have hsum2_symNz : ∑ p ∈ symNz, (c p) ^ 2 = D - 1 := by
    have htot := sum_nz_pauliExpect_sq hunit
    rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun p => quadForm0 p = 0)] at htot
    have hanti : ∑ p ∈ (nzPts m).filter (fun p => ¬quadForm0 p = 0), (c p) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hne : quadForm0 p ≠ 0 := (Finset.mem_filter.mp hp).2
      simp [c, pauliExpect_eq_zero_of_real_antisym hreal hne]
    change ∑ p ∈ symNz, (c p) ^ 2 +
      ∑ p ∈ (nzPts m).filter (fun p => ¬quadForm0 p = 0), (c p) ^ 2 = D - 1 at htot
    linarith
  have hsum4_symNz : ∑ p ∈ symNz, (c p) ^ 4 = 2 * (D - 1) / (D + 2) := by
    have hF := pauliMoment4_eq_sum_re_pow4 φ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)), pauliExpect_zero_re hunit,
        one_pow] at hF
    change pauliMoment4 m φ = 1 + ∑ p ∈ nzPts m, (c p) ^ 4 at hF
    rw [← Finset.sum_filter_add_sum_filter_not (nzPts m) (fun p => quadForm0 p = 0)] at hF
    have hanti : ∑ p ∈ (nzPts m).filter (fun p => ¬quadForm0 p = 0), (c p) ^ 4 = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hne : quadForm0 p ≠ 0 := (Finset.mem_filter.mp hp).2
      simp [c, pauliExpect_eq_zero_of_real_antisym hreal hne]
    rw [hanti, add_zero] at hF
    have hsub : 3 * D / (D + 2) - 1 = 2 * (D - 1) / (D + 2) := by
      field_simp [hD2_ne]; ring
    change 3 * D / (D + 2) = pauliMoment4 m φ at heq
    linarith
  have hvar0 : ∑ p ∈ symNz, ((c p) ^ 2 - 2 / (D + 2)) ^ 2 = 0 := by
    have hexp : ∑ p ∈ symNz, ((c p) ^ 2 - 2 / (D + 2)) ^ 2 =
        ∑ p ∈ symNz, (c p) ^ 4 - 2 * (2 / (D + 2)) * ∑ p ∈ symNz, (c p) ^ 2 +
        (symNz.card : ℝ) * (2 / (D + 2)) ^ 2 := by
      have ht : ∀ p ∈ symNz, ((c p) ^ 2 - 2 / (D + 2)) ^ 2 =
          (c p) ^ 4 - 2 * (2 / (D + 2)) * (c p) ^ 2 + (2 / (D + 2)) ^ 2 := fun _ _ => by ring
      rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hexp, hsum4_symNz, hsum2_symNz, hcard_symNz]
    field_simp [hD2_ne]; ring
  have hflat : ∀ p ∈ symNz, (c p) ^ 2 = 2 / (D + 2) := fun p hp => by
    have hsq0 : ((c p) ^ 2 - 2 / (D + 2)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hvar0 p hp
    linarith [sq_eq_zero_iff.mp hsq0]
  -- Step 3: Build `S_real = pauliExpand σ` (`σ p ∈ {-1, 0, 1}`) and relate `S_real = r • (D • P - I)`.
  let r : ℝ := Real.sqrt ((D + 2) / 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr2 : r ^ 2 = (D + 2) / 2 := Real.sq_sqrt (by linarith)
  let σ : PauliIdx m → ℝ := fun p => if p ∈ symNz then (if 0 ≤ c p then 1 else -1) else 0
  let Sreal : QMat m := pauliExpand σ
  let P : QMat m := stateProj φ
  let Imat : QMat m := fun x y => if x = y then (1 : ℂ) else 0
  let A : QMat m := fun x y => (D : ℂ) * P x y - Imat x y
  have hS_eq : Sreal = matSmul (r : ℂ) A := by
    -- Show `pauliExpand (fun p => r * c p) = matSmul r (pauliExpand c)` and compare at `p = 0` vs `p ≠ 0`!
    have hImat : Imat = pauliMat (0 : PauliIdx m) := by
      ext x y
      simp only [Imat, pauliMat, Prod.fst_zero, Prod.snd_zero, add_zero, pauliPh, dot_zero_left,
        ↓reduceIte, chi_zero_left, Int.cast_one, mul_one, eq_comm]
    have hcoeff : ∀ p : PauliIdx m, σ p = r * (c p - if p = 0 then 1 else 0) := fun p => by
      by_cases hp0 : p = 0
      · subst hp0
        have hnot : (0 : PauliIdx m) ∉ symNz := by simp [symNz, nzPts]
        simp [σ, hnot, c, pauliExpect_zero_re hunit]
      · by_cases hq0 : quadForm0 p = 0
        · have hp_mem : p ∈ symNz := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hp0, Finset.mem_univ p⟩, hq0⟩
          have hcp2 : (c p) ^ 2 = (1 / r) ^ 2 := by
            rw [hflat p hp_mem, div_pow, one_pow, hr2]; field_simp [hD2_ne]
          have habs : |c p| = 1 / r := by
            have h1r_pos : 0 < 1 / r := div_pos one_pos hr_pos
            nlinarith [sq_abs (c p), abs_nonneg (c p)]
          simp only [σ, hp_mem, hp0, ↓reduceIte, sub_zero]
          by_cases hnn : 0 ≤ c p
          · simp only [hnn, ↓reduceIte]
            rw [← abs_of_nonneg hnn, habs]; field_simp [hr_ne]
          · push Not at hnn
            simp only [not_le.mpr hnn, ↓reduceIte]
            have hneg : c p = -|c p| := by rw [abs_of_neg hnn]; ring
            rw [hneg, habs]; field_simp [hr_ne]
        · have hnot : p ∉ symNz := fun hm => hq0 (Finset.mem_filter.mp hm).2
          simp [σ, hnot, hp0, c, pauliExpect_eq_zero_of_real_antisym hreal hq0]
    have hPexp : pauliExpand c = matSmul (D : ℂ) P := by
      have h := (stateProj_eq_pauliExpand φ).symm
      simpa [D, c, P] using h
    ext x y
    simp only [Sreal, matSmul, A, pauliExpand]
    rw [hImat]
    have hsum_eq : ∑ p : PauliIdx m, (σ p : ℂ) * pauliMat p x y =
        (r : ℂ) * (∑ p : PauliIdx m, (c p : ℂ) * pauliMat p x y - pauliMat (0 : PauliIdx m) x y) := by
      have h0sum : pauliMat (0 : PauliIdx m) x y =
          ∑ p : PauliIdx m, (if p = 0 then (1 : ℂ) else 0) * pauliMat p x y := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [h0sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hcoeff p]
      by_cases hp : p = 0 <;> simp [hp] <;> ring
    have hPxy : ∑ p : PauliIdx m, (c p : ℂ) * pauliMat p x y = (D : ℂ) * P x y := by
      have := congr_fun (congr_fun hPexp x) y
      simpa [pauliExpand, matSmul] using this
    rw [hsum_eq, hPxy]
  -- Step 4: Evaluate `Tr(Sreal³)` via `r³ * Tr(A³) = r³ * D(D - 1)(D - 2)`.
  have hP_tr : matTr P = 1 := by
    have : matTr P = innerProd φ φ := by
      simp only [matTr, P, stateProj, innerProd]
      refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [this, hunit]
  have hI_tr : matTr Imat = (D : ℂ) := by
    simp only [matTr, Imat, ↓reduceIte, Finset.sum_const, Finset.card_univ, card_F2, nsmul_eq_mul,
      mul_one, D]
    push_cast; rfl
  have hmul_I_left : ∀ X : QMat m, matMul Imat X = X := fun X => by
    ext x y; simp [matMul, Imat]
  have hmul_I_right : ∀ X : QMat m, matMul X Imat = X := fun X => by
    ext x y; simp [matMul, Imat]
  have hA2 : matMul A A = fun x y => ((D : ℂ) ^ 2 - 2 * (D : ℂ)) * P x y + Imat x y := by
    ext x y
    have hPP := congr_fun (congr_fun (stateProj_idem hunit) x) y
    have hPI := congr_fun (congr_fun (hmul_I_right P) x) y
    have hIP := congr_fun (congr_fun (hmul_I_left P) x) y
    have hII := congr_fun (congr_fun (hmul_I_left Imat) x) y
    simp only [matMul, A] at hPP hPI hIP hII ⊢
    calc ∑ z : F2 m, ((D : ℂ) * P x z - Imat x z) * ((D : ℂ) * P z y - Imat z y)
        = (D : ℂ) ^ 2 * ∑ z, P x z * P z y - (D : ℂ) * ∑ z, P x z * Imat z y -
          (D : ℂ) * ∑ z, Imat x z * P z y + ∑ z, Imat x z * Imat z y := by
          simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun z _ => by ring
      _ = ((D : ℂ) ^ 2 - 2 * (D : ℂ)) * P x y + Imat x y := by
          rw [hPP, hPI, hIP, hII]; ring
  have hA3 : matMul A (matMul A A) =
      fun x y => ((D : ℂ) ^ 3 - 3 * (D : ℂ) ^ 2 + 3 * (D : ℂ)) * P x y - Imat x y := by
    ext x y
    have hPP := congr_fun (congr_fun (stateProj_idem hunit) x) y
    have hPI := congr_fun (congr_fun (hmul_I_right P) x) y
    have hIP := congr_fun (congr_fun (hmul_I_left P) x) y
    have hII := congr_fun (congr_fun (hmul_I_left Imat) x) y
    rw [hA2]
    simp only [matMul, A] at hPP hPI hIP hII ⊢
    calc ∑ z : F2 m, ((D : ℂ) * P x z - Imat x z) *
            (((D : ℂ) ^ 2 - 2 * (D : ℂ)) * P z y + Imat z y)
        = (D : ℂ) * ((D : ℂ) ^ 2 - 2 * (D : ℂ)) * ∑ z, P x z * P z y +
          (D : ℂ) * ∑ z, P x z * Imat z y -
          ((D : ℂ) ^ 2 - 2 * (D : ℂ)) * ∑ z, Imat x z * P z y -
          ∑ z, Imat x z * Imat z y := by
          simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun z _ => by ring
      _ = ((D : ℂ) ^ 3 - 3 * (D : ℂ) ^ 2 + 3 * (D : ℂ)) * P x y - Imat x y := by
          rw [hPP, hPI, hIP, hII]; ring
  have htr3_way1 : (matTr (matMul Sreal (matMul Sreal Sreal))).re =
      D * (D - 1) * (D - 2) * ((D + 2) / 2) * r := by
    have hscale : matTr (matMul Sreal (matMul Sreal Sreal)) =
        (r : ℂ) ^ 3 * matTr (matMul A (matMul A A)) := by
      rw [hS_eq]
      simp only [matTr, matMul, matSmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
        Finset.sum_congr rfl fun w _ => by ring
    have htrA3 : matTr (matMul A (matMul A A)) =
        ((D * (D - 1) * (D - 2) : ℝ) : ℂ) := by
      rw [hA3]
      have hsplit : matTr (fun x y => ((D : ℂ) ^ 3 - 3 * (D : ℂ) ^ 2 + 3 * (D : ℂ)) * P x y - Imat x y) =
          ((D : ℂ) ^ 3 - 3 * (D : ℂ) ^ 2 + 3 * (D : ℂ)) * matTr P - matTr Imat := by
        simp only [matTr, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsplit, hP_tr, hI_tr]; push_cast; ring
    rw [hscale, htrA3, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc r ^ 3 * (D * (D - 1) * (D - 2))
        = D * (D - 1) * (D - 2) * r ^ 2 * r := by ring
      _ = D * (D - 1) * (D - 2) * ((D + 2) / 2) * r := by rw [hr2]
  -- Step 5: Evaluate `Tr(Sreal³)` via Pauli expansion — exact integer!
  have htr3_int : ∃ N : ℤ, (matTr (matMul Sreal (matMul Sreal Sreal))).re = (N : ℝ) := by
    let σZ : PauliIdx m → ℤ := fun p => if p ∈ symNz then (if 0 ≤ c p then 1 else -1) else 0
    have hσZ : ∀ p : PauliIdx m, σ p = (σZ p : ℝ) := fun p => by
      simp only [σ, σZ]; split_ifs <;> simp
    let phZ : PauliIdx m → PauliIdx m → ℤ := fun q p =>
      if pauliPhase q p = 1 then 1 else if pauliPhase q p = -1 then -1 else 0
    have hphZ : ∀ q p : PauliIdx m, (pauliPhase q p).re = (phZ q p : ℝ) := fun q p => by
      rcases zmod2_cases (symp q p) with hs | hs
      · rcases (pauliPhase_re_cases q p).1 hs with h1 | h1
        · simp [phZ, h1]
        · have hne : (-1 : ℂ) ≠ 1 := by norm_num
          simp [phZ, h1, hne]
      · have h0 := (pauliPhase_re_cases q p).2 hs
        have hne1 : pauliPhase q p ≠ 1 := fun h => by rw [h, Complex.one_re] at h0; norm_num at h0
        have hnem1 : pauliPhase q p ≠ -1 := fun h => by rw [h, Complex.neg_re, Complex.one_re] at h0; norm_num at h0
        simp [phZ, h0, hne1, hnem1]
    refine ⟨(2 : ℤ) ^ m * ∑ q : PauliIdx m, σZ q * ∑ p : PauliIdx m, phZ q p * σZ p * σZ (q + p), ?_⟩
    dsimp only [Sreal]
    rw [matMul_pauliExpand_self, matTr_pauliExpand_mul]
    have h2c : (2 : ℂ) ^ m = (D : ℂ) := by simp [D]
    rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    push_cast
    refine congr_arg (D * ·) (Finset.sum_congr rfl fun q _ => ?_)
    rw [hσZ q]
    refine congr_arg ((σZ q : ℝ) * ·) (Finset.sum_congr rfl fun p _ => ?_)
    rw [hphZ q p, hσZ p, hσZ (q + p)]
  -- Step 6: Contradict irrationality of `√(2^{m-1} + 1)` (`sqrt_pow_two_add_one_ne_rat`)!
  obtain ⟨N, hN⟩ := htr3_int
  have hD_half : (D + 2) / 2 = (2 : ℝ) ^ (m - 1) + 1 := by
    have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    dsimp only [D]; rw [hpow]; ring
  let q_fac : ℚ := (2 : ℚ) ^ m * ((2 : ℚ) ^ m - 1) * ((2 : ℚ) ^ m - 2) * (((2 : ℚ) ^ m + 2) / 2)
  have hfac_cast : D * (D - 1) * (D - 2) * ((D + 2) / 2) = (q_fac : ℝ) := by
    simp [q_fac, D]
  have hfac_ne : (q_fac : ℝ) ≠ 0 := by
    rw [← hfac_cast]
    have h1 : 0 < D - 1 := by linarith
    have h2 : 0 < D - 2 := by linarith
    have h3 : 0 < (D + 2) / 2 := by linarith
    exact ne_of_gt (mul_pos (mul_pos (mul_pos hD_pos h1) h2) h3)
  have hsqrt : Real.sqrt ((2 : ℝ) ^ (m - 1) + 1) = (((N : ℚ) / q_fac : ℚ) : ℝ) := by
    rw [← hD_half]
    change r = (((N : ℚ) / q_fac : ℚ) : ℝ)
    rw [Rat.cast_div, Rat.cast_intCast]
    exact (eq_div_iff hfac_ne).mpr (by rw [← hfac_cast]; linarith)
  exact sqrt_pow_two_add_one_ne_rat (by omega : m - 1 ≠ 3) ((N : ℚ) / q_fac) hsqrt

/-! ### Part 3: Stage 17 Identities I & II — Exact Self-Dual Twisted Autocorrelation Equations -/

/-- **Universal Pauli Completeness / `SWAP` Contraction (ALL `m`, ALL Four States)**:
      `∑_{p : PauliIdx m} ⟨u₁ | P_p | v₁⟩ ⟨u₂ | P_p | v₂⟩ = 2ᵐ ⟨u₁ | v₂⟩ ⟨u₂ | v₁⟩`. -/
theorem sum_innerProd_pauliApply_mul {m : ℕ} (u₁ v₁ u₂ v₂ : QState m) :
    ∑ p : PauliIdx m, innerProd u₁ (pauliApply p v₁) * innerProd u₂ (pauliApply p v₂) =
      (2 : ℂ) ^ m * (innerProd u₁ v₂ * innerProd u₂ v₁) := by
  -- Expand both inner products and sum over `b = p.2 : F2 m` first!
  calc ∑ p : PauliIdx m, innerProd u₁ (pauliApply p v₁) * innerProd u₂ (pauliApply p v₂)
      = ∑ a : F2 m, ∑ b : F2 m,
          ∑ x : F2 m, ∑ y : F2 m,
            star (u₁ x) * v₁ (x + a) * star (u₂ y) * v₂ (y + a) *
              ((chi b (a + x + y) : ℤ) : ℂ) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [innerProd, innerProd, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [pauliApply]
        have hph2 : pauliPh (a, b) * pauliPh (a, b) = (chi b a : ℂ) := by
          simpa [sq] using pauliPh_sq (a, b)
        have hchi3 : ((chi b (a + x + y) : ℤ) : ℂ) =
            (chi b a : ℂ) * (chi b x : ℂ) * (chi b y : ℂ) := by
          rw [chi_add_right, chi_add_right]; push_cast; ring
        rw [hchi3]
        calc star (u₁ x) * (pauliPh (a, b) * (chi b x : ℂ) * v₁ (x + a)) *
              (star (u₂ y) * (pauliPh (a, b) * (chi b y : ℂ) * v₂ (y + a)))
            = star (u₁ x) * v₁ (x + a) * star (u₂ y) * v₂ (y + a) *
                ((pauliPh (a, b) * pauliPh (a, b)) * (chi b x : ℂ) * (chi b y : ℂ)) := by ring
          _ = _ := by rw [hph2]
    _ = ∑ a : F2 m, ∑ x : F2 m, ∑ y : F2 m,
          star (u₁ x) * v₁ (x + a) * star (u₂ y) * v₂ (y + a) *
            (∑ b : F2 m, ((chi b (a + x + y) : ℤ) : ℂ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
    _ = ∑ a : F2 m, ∑ x : F2 m,
          star (u₁ x) * v₁ (x + a) * star (u₂ (x + a)) * v₂ x * (2 : ℂ) ^ m := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
        have hsum_b : ∀ y : F2 m, ∑ b : F2 m, ((chi b (a + x + y) : ℤ) : ℂ) =
            if y = x + a then (2 : ℂ) ^ m else 0 := fun y => by
          rw [← Int.cast_sum, sum_chi]
          have hself : ∀ u : F2 m, u + u = 0 := fun u => by
            ext i; simp only [Pi.add_apply, Pi.zero_apply]
            rcases zmod2_cases (u i) with h | h
            · simp [h]
            · simp [h]; decide
          have hiff : a + x + y = 0 ↔ y = x + a := by
            constructor
            · intro h
              have h1 := congr_arg ((a + x) + ·) h
              rw [← add_assoc, hself (a + x), zero_add, add_zero, add_comm] at h1
              exact h1
            · intro h; subst h
              rw [add_comm x a, hself (a + x)]
          simp only [hiff]
          by_cases hy : y = x + a <;> simp [hy]
        simp only [hsum_b, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hxaa : x + a + a = x := f2_add_cancel_right x a
        rw [hxaa]
    _ = (2 : ℂ) ^ m * (innerProd u₁ v₂ * innerProd u₂ v₁) := by
        rw [Finset.sum_comm, innerProd, innerProd, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun a => ?_
        change star (u₁ x) * v₁ (x + a) * star (u₂ (x + a)) * v₂ x * (2 : ℂ) ^ m =
          (2 : ℂ) ^ m * (star (u₁ x) * v₂ x * (star (u₂ (x + a)) * v₁ (x + a)))
        ring

/-- **Stage 17 Identity I — Self-Dual Twisted Multiplicative-Derivative Equation (ALL `m`, ALL `φ₁, φ₂, s, h`)**:
      `∑_p (-1)^{ω(p, s)} γ(p, h) ⟨φ₁|P_p|φ₂⟩ ⟨φ₁|P_{p+h}|φ₂⟩ = 2ᵐ γ(s, h) ⟨φ₁|P_s|φ₂⟩ ⟨φ₁|P_{s+h}|φ₂⟩`. -/
theorem crossPauli_selfDual_deriv {m : ℕ} (φ₁ φ₂ : QState m) (s h : PauliIdx m) :
    ∑ p : PauliIdx m,
        (sympSign p s : ℂ) * pauliPhase p h *
          innerProd φ₁ (pauliApply p φ₂) * innerProd φ₁ (pauliApply (p + h) φ₂) =
      (2 : ℂ) ^ m * pauliPhase s h *
        innerProd φ₁ (pauliApply s φ₂) * innerProd φ₁ (pauliApply (s + h) φ₂) := by
  have hswap := sum_innerProd_pauliApply_mul (pauliApply s φ₁) (pauliApply s φ₂) φ₁ (pauliApply h φ₂)
  have hL : ∑ p : PauliIdx m,
      innerProd (pauliApply s φ₁) (pauliApply p (pauliApply s φ₂)) *
        innerProd φ₁ (pauliApply p (pauliApply h φ₂)) =
      ∑ p : PauliIdx m,
        (sympSign p s : ℂ) * pauliPhase p h *
          innerProd φ₁ (pauliApply p φ₂) * innerProd φ₁ (pauliApply (p + h) φ₂) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : innerProd (pauliApply s φ₁) (pauliApply p (pauliApply s φ₂)) =
        (sympSign p s : ℂ) * innerProd φ₁ (pauliApply p φ₂) := by
      rw [pauliApply_comm p s φ₂, innerProd_smul_right, innerProd_pauliApply_both]
    have h2 : innerProd φ₁ (pauliApply p (pauliApply h φ₂)) =
        pauliPhase p h * innerProd φ₁ (pauliApply (p + h) φ₂) := by
      rw [pauliApply_comp p h φ₂, innerProd_smul_right]
    rw [h1, h2]; ring
  have hR : (2 : ℂ) ^ m * (innerProd (pauliApply s φ₁) (pauliApply h φ₂) *
      innerProd φ₁ (pauliApply s φ₂)) =
      (2 : ℂ) ^ m * pauliPhase s h *
        innerProd φ₁ (pauliApply s φ₂) * innerProd φ₁ (pauliApply (s + h) φ₂) := by
    rw [← innerProd_pauliApply_right s φ₁ (pauliApply h φ₂), pauliApply_comp s h φ₂,
        innerProd_smul_right]
    ring
  rw [hL, hR] at hswap
  exact hswap

/-- **Stage 17 Identity II — Twisted Autocorrelation Outer-Product Identity (ALL `m`, ALL `φ₁, φ₂, s, h`)**:
      `∑_p (-1)^{ω(p, s)} γ(p, h) ⟨φ₁|P_p|φ₂⟩* ⟨φ₁|P_{p+h}|φ₂⟩ = 2ᵐ γ(s, h) ⟨φ₁|P_s|φ₁⟩ ⟨φ₂|P_{s+h}|φ₂⟩`. -/
theorem crossPauli_autocorr_outer {m : ℕ} (φ₁ φ₂ : QState m) (s h : PauliIdx m) :
    ∑ p : PauliIdx m,
        (sympSign p s : ℂ) * pauliPhase p h *
          star (innerProd φ₁ (pauliApply p φ₂)) * innerProd φ₁ (pauliApply (p + h) φ₂) =
      (2 : ℂ) ^ m * pauliPhase s h *
        innerProd φ₁ (pauliApply s φ₁) * innerProd φ₂ (pauliApply (s + h) φ₂) := by
  have hswap := sum_innerProd_pauliApply_mul (pauliApply s φ₂) (pauliApply s φ₁) φ₁ (pauliApply h φ₂)
  have hL : ∑ p : PauliIdx m,
      innerProd (pauliApply s φ₂) (pauliApply p (pauliApply s φ₁)) *
        innerProd φ₁ (pauliApply p (pauliApply h φ₂)) =
      ∑ p : PauliIdx m,
        (sympSign p s : ℂ) * pauliPhase p h *
          star (innerProd φ₁ (pauliApply p φ₂)) * innerProd φ₁ (pauliApply (p + h) φ₂) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : innerProd (pauliApply s φ₂) (pauliApply p (pauliApply s φ₁)) =
        (sympSign p s : ℂ) * star (innerProd φ₁ (pauliApply p φ₂)) := by
      rw [pauliApply_comm p s φ₁, innerProd_smul_right, innerProd_pauliApply_both,
          innerProd_pauliApply_right, innerProd_conj_symm]
    have h2 : innerProd φ₁ (pauliApply p (pauliApply h φ₂)) =
        pauliPhase p h * innerProd φ₁ (pauliApply (p + h) φ₂) := by
      rw [pauliApply_comp p h φ₂, innerProd_smul_right]
    rw [h1, h2]; ring
  have hR : (2 : ℂ) ^ m * (innerProd (pauliApply s φ₂) (pauliApply h φ₂) *
      innerProd φ₁ (pauliApply s φ₁)) =
      (2 : ℂ) ^ m * pauliPhase s h *
        innerProd φ₁ (pauliApply s φ₁) * innerProd φ₂ (pauliApply (s + h) φ₂) := by
    rw [← innerProd_pauliApply_right s φ₂ (pauliApply h φ₂), pauliApply_comp s h φ₂,
        innerProd_smul_right]
    ring
  rw [hL, hR] at hswap
  exact hswap

/-! ### Part 4: Theorem 18.1 — Unconditional Indefinite `(1, 1)`-Spread `βₘ*` Reduction -/

/-- Exact `ℓ₂` squared norm of the Pauli difference `c_r(φ₁) - c_r(φ₂)` on `nzPts m`:
      `∑_{r ≠ 0} (c_r(φ₁) - c_r(φ₂))² = 2 D (1 - |⟨φ₁ | φ₂⟩|²)`. -/
theorem sum_pauliDiff_sq {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) :
    ∑ r ∈ nzPts m,
        ((innerProd φ₁ (pauliApply r φ₁)).re - (innerProd φ₂ (pauliApply r φ₂)).re) ^ 2 =
      2 * (2 : ℝ) ^ m * (1 - Complex.normSq (innerProd φ₁ φ₂)) := by
  let D : ℝ := (2 : ℝ) ^ m
  have hD_ne : D ≠ 0 := by positivity
  -- From `crossOverlap_normSq_eq_sympWHT φ₁ φ₂ 0`: `|⟨φ₁|φ₂⟩|² = (1/D) ∑_s c_s(φ₁) c_s(φ₂)`.
  have hcov := crossOverlap_normSq_eq_sympWHT φ₁ φ₂ 0
  rw [pauliApply_zero] at hcov
  have hsum_prod_all : ∑ s : PauliIdx m,
      (innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re =
      D * Complex.normSq (innerProd φ₁ φ₂) := by
    have hs1 : ∀ s : PauliIdx m, (sympSign (0 : PauliIdx m) s : ℝ) = 1 := fun s => by
      simp [sympSign, symp_zero_left]
    simp_rw [hs1, one_mul] at hcov
    have hmul : D * Complex.normSq (innerProd φ₁ φ₂) =
        ∑ s : PauliIdx m, (innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re := by
      rw [hcov]; dsimp only [D]; field_simp [hD_ne]
    exact hmul.symm
  have hsum_prod_nz : ∑ s ∈ nzPts m,
      (innerProd φ₁ (pauliApply s φ₁)).re * (innerProd φ₂ (pauliApply s φ₂)).re =
      D * Complex.normSq (innerProd φ₁ φ₂) - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
        pauliExpect_zero_re h1, pauliExpect_zero_re h2, mul_one] at hsum_prod_all
    change 1 + ∑ s ∈ nzPts m, _ = _ at hsum_prod_all
    linarith
  have hexp : ∑ r ∈ nzPts m,
      ((innerProd φ₁ (pauliApply r φ₁)).re - (innerProd φ₂ (pauliApply r φ₂)).re) ^ 2 =
      ∑ r ∈ nzPts m, (innerProd φ₁ (pauliApply r φ₁)).re ^ 2 +
      ∑ r ∈ nzPts m, (innerProd φ₂ (pauliApply r φ₂)).re ^ 2 -
      2 * ∑ r ∈ nzPts m, (innerProd φ₁ (pauliApply r φ₁)).re * (innerProd φ₂ (pauliApply r φ₂)).re := by
    have ht : ∀ r ∈ nzPts m,
        ((innerProd φ₁ (pauliApply r φ₁)).re - (innerProd φ₂ (pauliApply r φ₂)).re) ^ 2 =
        (innerProd φ₁ (pauliApply r φ₁)).re ^ 2 + (innerProd φ₂ (pauliApply r φ₂)).re ^ 2 -
        2 * ((innerProd φ₁ (pauliApply r φ₁)).re * (innerProd φ₂ (pauliApply r φ₂)).re) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp, sum_nz_pauliExpect_sq h1, sum_nz_pauliExpect_sq h2, hsum_prod_nz]
  dsimp only [D]; ring

/-- Quartic `ℓ₄` upper bound on the Pauli difference `c_r(φ₁) - c_r(φ₂)` on `nzPts m`:
      `∑_{r ≠ 0} (c_r⁺ - c_r⁻)⁴ ≤ (F₁ + F₂ - 2) + 6 C + 4 (√(F₁ - 1) + √(F₂ - 1)) √C`. -/
theorem sum_pauliDiff_pow4_le {m : ℕ} {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) :
    let F1 := pauliMoment4 m φ₁
    let F2 := pauliMoment4 m φ₂
    let C := pauliSupportOverlap φ₁ φ₂
    ∑ r ∈ nzPts m,
        ((innerProd φ₁ (pauliApply r φ₁)).re - (innerProd φ₂ (pauliApply r φ₂)).re) ^ 4 ≤
      (F1 + F2 - 2) + 6 * C + 4 * (Real.sqrt (F1 - 1) + Real.sqrt (F2 - 1)) * Real.sqrt C := by
  intro F1 F2 C
  let x : PauliIdx m → ℝ := fun r => (innerProd φ₁ (pauliApply r φ₁)).re
  let y : PauliIdx m → ℝ := fun r => (innerProd φ₂ (pauliApply r φ₂)).re
  have hF1 : ∑ r ∈ nzPts m, (x r) ^ 4 = F1 - 1 := by
    have h := pauliMoment4_eq_sum_re_pow4 φ₁
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)), pauliExpect_zero_re h1,
        one_pow] at h
    change F1 = 1 + ∑ r ∈ nzPts m, (x r) ^ 4 at h
    linarith
  have hF2 : ∑ r ∈ nzPts m, (y r) ^ 4 = F2 - 1 := by
    have h := pauliMoment4_eq_sum_re_pow4 φ₂
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)), pauliExpect_zero_re h2,
        one_pow] at h
    change F2 = 1 + ∑ r ∈ nzPts m, (y r) ^ 4 at h
    linarith
  have hF1_nn : 0 ≤ F1 - 1 := by rw [← hF1]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hF2_nn : 0 ≤ F2 - 1 := by rw [← hF2]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun _ _ => by positivity
  have hodd1 : -(∑ r ∈ nzPts m, (x r) ^ 3 * y r) ≤ Real.sqrt (F1 - 1) * Real.sqrt C := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nzPts m) (fun r => (x r) ^ 2) (fun r => x r * y r)
    have hsq1 : ∑ r ∈ nzPts m, ((x r) ^ 2) ^ 2 = F1 - 1 := by
      rw [← hF1]; refine Finset.sum_congr rfl fun _ _ => by ring
    have hsq2 : ∑ r ∈ nzPts m, (x r * y r) ^ 2 = C := by
      dsimp only [C, pauliSupportOverlap]
      refine Finset.sum_congr rfl fun _ _ => by dsimp only [x, y]; ring
    have hprod : ∑ r ∈ nzPts m, (x r) ^ 2 * (x r * y r) = ∑ r ∈ nzPts m, (x r) ^ 3 * y r :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [hsq1, hsq2, hprod] at hcs
    have hrhs_sq : (Real.sqrt (F1 - 1) * Real.sqrt C) ^ 2 = (F1 - 1) * C := by
      rw [mul_pow, Real.sq_sqrt hF1_nn, Real.sq_sqrt hC_nn]
    have hnn : 0 ≤ Real.sqrt (F1 - 1) * Real.sqrt C := by positivity
    nlinarith [sq_nonneg (-(∑ r ∈ nzPts m, (x r) ^ 3 * y r) - Real.sqrt (F1 - 1) * Real.sqrt C)]
  have hodd2 : -(∑ r ∈ nzPts m, x r * (y r) ^ 3) ≤ Real.sqrt (F2 - 1) * Real.sqrt C := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nzPts m) (fun r => (y r) ^ 2) (fun r => x r * y r)
    have hsq1 : ∑ r ∈ nzPts m, ((y r) ^ 2) ^ 2 = F2 - 1 := by
      rw [← hF2]; refine Finset.sum_congr rfl fun _ _ => by ring
    have hsq2 : ∑ r ∈ nzPts m, (x r * y r) ^ 2 = C := by
      dsimp only [C, pauliSupportOverlap]
      refine Finset.sum_congr rfl fun _ _ => by dsimp only [x, y]; ring
    have hprod : ∑ r ∈ nzPts m, (y r) ^ 2 * (x r * y r) = ∑ r ∈ nzPts m, x r * (y r) ^ 3 :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [hsq1, hsq2, hprod] at hcs
    have hrhs_sq : (Real.sqrt (F2 - 1) * Real.sqrt C) ^ 2 = (F2 - 1) * C := by
      rw [mul_pow, Real.sq_sqrt hF2_nn, Real.sq_sqrt hC_nn]
    have hnn : 0 ≤ Real.sqrt (F2 - 1) * Real.sqrt C := by positivity
    nlinarith [sq_nonneg (-(∑ r ∈ nzPts m, x r * (y r) ^ 3) - Real.sqrt (F2 - 1) * Real.sqrt C)]
  have hexp : ∑ r ∈ nzPts m, (x r - y r) ^ 4 =
      (∑ r ∈ nzPts m, (x r) ^ 4) + (∑ r ∈ nzPts m, (y r) ^ 4) +
      6 * C - 4 * (∑ r ∈ nzPts m, (x r) ^ 3 * y r) - 4 * (∑ r ∈ nzPts m, x r * (y r) ^ 3) := by
    have ht : ∀ r ∈ nzPts m, (x r - y r) ^ 4 =
        (x r) ^ 4 + (y r) ^ 4 + 6 * ((x r) ^ 2 * (y r) ^ 2) -
        4 * ((x r) ^ 3 * y r) - 4 * (x r * (y r) ^ 3) := fun _ _ => by ring
    rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
    rfl
  change ∑ r ∈ nzPts m, (x r - y r) ^ 4 ≤ _
  rw [hexp, hF1, hF2]
  linarith

/-- Elementary Cauchy–Schwarz Hölder inequality (`(∑ u²)³ ≤ (∑ u)² (∑ u⁴)` for `u ≥ 0`, zero `rpow`). -/
lemma sum_sq_cube_le_sum_sq_mul_sum_pow4 {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, (u i) ^ 2) ^ 3 ≤ (∑ i ∈ s, u i) ^ 2 * ∑ i ∈ s, (u i) ^ 4 := by
  by_cases h2 : ∑ i ∈ s, (u i) ^ 2 = 0
  · rw [h2, zero_pow (by norm_num)]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)
  · have h2_pos : 0 < ∑ i ∈ s, (u i) ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm h2)
    -- Step 1: `(∑ u²)² ≤ (∑ u) (∑ u³)` via CS on `√u` and `u √u`.
    have hcs1 : (∑ i ∈ s, (u i) ^ 2) ^ 2 ≤ (∑ i ∈ s, u i) * ∑ i ∈ s, (u i) ^ 3 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (u i))
        (fun i => u i * Real.sqrt (u i))
      have hL : ∑ i ∈ s, Real.sqrt (u i) * (u i * Real.sqrt (u i)) = ∑ i ∈ s, (u i) ^ 2 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        calc Real.sqrt (u i) * (u i * Real.sqrt (u i))
            = u i * (Real.sqrt (u i) * Real.sqrt (u i)) := by ring
          _ = u i * u i := by rw [Real.mul_self_sqrt (hu i hi)]
          _ = (u i) ^ 2 := by ring
      have hR1 : ∑ i ∈ s, (Real.sqrt (u i)) ^ 2 = ∑ i ∈ s, u i :=
        Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hu i hi)
      have hR2 : ∑ i ∈ s, (u i * Real.sqrt (u i)) ^ 2 = ∑ i ∈ s, (u i) ^ 3 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mul_pow, Real.sq_sqrt (hu i hi)]; ring
      rwa [hL, hR1, hR2] at h
    -- Step 2: `(∑ u³)² ≤ (∑ u²) (∑ u⁴)` via CS on `u` and `u²`.
    have hcs2 : (∑ i ∈ s, (u i) ^ 3) ^ 2 ≤ (∑ i ∈ s, (u i) ^ 2) * ∑ i ∈ s, (u i) ^ 4 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq s u (fun i => (u i) ^ 2)
      have hL : ∑ i ∈ s, u i * (u i) ^ 2 = ∑ i ∈ s, (u i) ^ 3 :=
        Finset.sum_congr rfl fun _ _ => by ring
      have hR2 : ∑ i ∈ s, ((u i) ^ 2) ^ 2 = ∑ i ∈ s, (u i) ^ 4 :=
        Finset.sum_congr rfl fun _ _ => by ring
      rwa [hL, hR2] at h
    have hsum1_nn : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg hu
    have hsum3_nn : 0 ≤ ∑ i ∈ s, (u i) ^ 3 := Finset.sum_nonneg fun i hi => pow_nonneg (hu i hi) 3
    have hpow4 : (∑ i ∈ s, (u i) ^ 2) ^ 4 ≤
        (∑ i ∈ s, u i) ^ 2 * ((∑ i ∈ s, (u i) ^ 2) * ∑ i ∈ s, (u i) ^ 4) := by
      calc (∑ i ∈ s, (u i) ^ 2) ^ 4
          = ((∑ i ∈ s, (u i) ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((∑ i ∈ s, u i) * ∑ i ∈ s, (u i) ^ 3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hcs1 2
        _ = (∑ i ∈ s, u i) ^ 2 * (∑ i ∈ s, (u i) ^ 3) ^ 2 := by ring
        _ ≤ (∑ i ∈ s, u i) ^ 2 * ((∑ i ∈ s, (u i) ^ 2) * ∑ i ∈ s, (u i) ^ 4) :=
            mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
    nlinarith

/-- **Theorem 18.1(a) — Unconditional Indefinite `(1, 1)`-Spread `βₘ*` Reduction (ALL `m ≥ 1`)**:
    For EVERY unit pair `(φ₁, φ₂)` on `m ≥ 1` qubits, choosing `τ_r = sgn(c_r(φ₁) - c_r(φ₂))`
    gives a Boolean Pauli sign operator `S(τ) = pauliExpand τ` whose `(1, 1)` Rayleigh spread
    obeys the exact lower bound
      `((⟨φ₁|S(τ)|φ₁⟩ - ⟨φ₂|S(τ)|φ₂⟩).re)² / (2 D (D² - 1))`
      `  ≥ (D² / (D² - 1)) * 4 (1 - |⟨φ₁|φ₂⟩|²)³ / ((F₁ + F₂ - 2) + 6 C + 4 (√(F₁ - 1) + √(F₂ - 1)) √C)`.
    Whenever `𝒥ₘ → 2`, we have `C → 0`, `F₁ + F₂ → 6`, `|⟨φ₁|φ₂⟩|² → 0`, so the RHS approaches `1`. -/
theorem twoState_indefiniteSpread_ge {m : ℕ} (hm : 1 ≤ m) {φ₁ φ₂ : QState m}
    (h1 : IsUnitState φ₁) (h2 : IsUnitState φ₂) :
    let D : ℝ := (2 : ℝ) ^ m
    let T2 : ℝ := D * (D ^ 2 - 1)
    let F1 := pauliMoment4 m φ₁
    let F2 := pauliMoment4 m φ₂
    let C := pauliSupportOverlap φ₁ φ₂
    let g2 := Complex.normSq (innerProd φ₁ φ₂)
    ∃ τ : PauliIdx m → ℝ, τ 0 = 0 ∧ (∀ r : PauliIdx m, r ≠ 0 → τ r = 1 ∨ τ r = -1) ∧
      (((innerProd φ₁ (matApply (pauliExpand τ) φ₁)).re -
        (innerProd φ₂ (matApply (pauliExpand τ) φ₂)).re) ^ 2 / (2 * T2)) *
        ((F1 + F2 - 2) + 6 * C + 4 * (Real.sqrt (F1 - 1) + Real.sqrt (F2 - 1)) * Real.sqrt C) ≥
        (D ^ 2 / (D ^ 2 - 1)) * (4 * (1 - g2) ^ 3) := by
  intro D T2 F1 F2 C g2
  let d : PauliIdx m → ℝ := fun r =>
    (innerProd φ₁ (pauliApply r φ₁)).re - (innerProd φ₂ (pauliApply r φ₂)).re
  let τ : PauliIdx m → ℝ := fun r => if r = 0 then 0 else if 0 ≤ d r then 1 else -1
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτpm : ∀ r : PauliIdx m, r ≠ 0 → τ r = 1 ∨ τ r = -1 := fun r hr => by
    simp only [τ, hr, ↓reduceIte]; split_ifs <;> simp
  refine ⟨τ, hτ0, hτpm, ?_⟩
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have : (2 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  have hD_pos : 0 < D := by linarith
  have hD2m1_pos : 0 < D ^ 2 - 1 := by nlinarith
  have hT2_pos : 0 < T2 := by dsimp only [T2]; exact mul_pos hD_pos hD2m1_pos
  -- Compute Rayleigh difference `⟨φ₁|S(τ)|φ₁⟩ - ⟨φ₂|S(τ)|φ₂⟩ = ∑_{r ≠ 0} |d r|`.
  have hray_of : ∀ φ : QState m,
      (innerProd φ (matApply (pauliExpand τ) φ)).re =
        ∑ r ∈ nzPts m, τ r * (innerProd φ (pauliApply r φ)).re := fun φ => by
    have hlin : innerProd φ (matApply (pauliExpand τ) φ) =
        ∑ r : PauliIdx m, (τ r : ℂ) * innerProd φ (pauliApply r φ) := by
      have hap : matApply (pauliExpand τ) φ = ∑ r : PauliIdx m, (τ r : ℂ) • pauliApply r φ := by
        ext x
        simp only [matApply, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]; congr 1
        exact congr_fun (pauliMat_apply r φ) x
      rw [hap, innerProd_sum_right]
      refine Finset.sum_congr rfl fun r _ => innerProd_smul_right _ _ _
    rw [hlin, Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)),
        hτ0, Complex.ofReal_zero, zero_mul, Complex.zero_re, zero_add]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hre := innerProd_pauliApply_self_real r φ
    conv_lhs => rw [← hre]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hspread : (innerProd φ₁ (matApply (pauliExpand τ) φ₁)).re -
      (innerProd φ₂ (matApply (pauliExpand τ) φ₂)).re = ∑ r ∈ nzPts m, |d r| := by
    rw [hray_of φ₁, hray_of φ₂, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hfac : τ r * (innerProd φ₁ (pauliApply r φ₁)).re -
        τ r * (innerProd φ₂ (pauliApply r φ₂)).re = τ r * d r := by dsimp only [d]; ring
    rw [hfac]
    simp only [τ, hr0, ↓reduceIte]
    split_ifs with hnn
    · rw [one_mul, abs_of_nonneg hnn]
    · push Not at hnn; rw [abs_of_neg hnn]; ring
  -- Apply Hölder (`sum_sq_cube_le_sum_sq_mul_sum_pow4`) to `u r := |d r|`.
  have hhold := sum_sq_cube_le_sum_sq_mul_sum_pow4 (nzPts m) (fun r => |d r|) (fun _ _ => abs_nonneg _)
  have hsq_eq : ∑ r ∈ nzPts m, |d r| ^ 2 = 2 * D * (1 - g2) := by
    have : ∑ r ∈ nzPts m, |d r| ^ 2 = ∑ r ∈ nzPts m, (d r) ^ 2 :=
      Finset.sum_congr rfl fun _ _ => sq_abs _
    rw [this]; exact sum_pauliDiff_sq h1 h2
  have hpow4_eq : ∑ r ∈ nzPts m, |d r| ^ 4 = ∑ r ∈ nzPts m, (d r) ^ 4 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    calc |d r| ^ 4 = (|d r| ^ 2) ^ 2 := by ring
      _ = ((d r) ^ 2) ^ 2 := by rw [sq_abs]
      _ = (d r) ^ 4 := by ring
  have hpow4_le := sum_pauliDiff_pow4_le h1 h2
  dsimp only at hpow4_le
  rw [hsq_eq, hpow4_eq, ← hspread] at hhold
  have hstep : (2 * D * (1 - g2)) ^ 3 ≤
      ((innerProd φ₁ (matApply (pauliExpand τ) φ₁)).re -
       (innerProd φ₂ (matApply (pauliExpand τ) φ₂)).re) ^ 2 *
      ((F1 + F2 - 2) + 6 * C + 4 * (Real.sqrt (F1 - 1) + Real.sqrt (F2 - 1)) * Real.sqrt C) := by
    exact le_trans hhold (mul_le_mul_of_nonneg_left hpow4_le (sq_nonneg _))
  have hdiv := div_le_div_of_nonneg_right hstep (show (0 : ℝ) ≤ 2 * T2 by linarith)
  have hL : (2 * D * (1 - g2)) ^ 3 / (2 * T2) = (D ^ 2 / (D ^ 2 - 1)) * (4 * (1 - g2) ^ 3) := by
    dsimp only [T2]; field_simp [ne_of_gt hD_pos, ne_of_gt hD2m1_pos]; ring
  rw [hL, mul_div_right_comm] at hdiv
  exact hdiv

/-- **Theorem 18.1(b) — Spectral Equivalence with the Bulk-Eigenvalue Floor (ALL `m ≥ 1`)**:
    For any Boolean Pauli sign operator `S = pauliExpand τ` (`τ 0 = 0`, `∀ r ≠ 0, τ r = ±1`),
    if its middle `2ᵐ - 2` eigenvalues (excluding the largest and smallest) carry at least
    fraction `c₀` of its Frobenius norm squared `T₂ = D(D² - 1)`, then EVERY pair of unit states
    `(e₁, e₂)` obeys `((⟨e₁|S|e₁⟩ - ⟨e₂|S|e₂⟩).re)² ≤ 2 (1 - c₀) T₂`. -/
theorem twoState_indefiniteSpread_le_of_bulkFloor {m : ℕ} (hm : 1 ≤ m)
    {τ : PauliIdx m → ℝ} (h0 : τ 0 = 0)
    (hpm : ∀ r : PauliIdx m, r ≠ 0 → τ r = 1 ∨ τ r = -1)
    {c₀ : ℝ}
    (hbulk : ∀ (hM : (Matrix.of (pauliExpand τ)).IsHermitian) (i_max i_min : F2 m),
      i_max ≠ i_min →
      c₀ * ((2 : ℝ) ^ m * (((2 : ℝ) ^ m) ^ 2 - 1)) ≤
        ∑ j ∈ (Finset.univ.erase i_max).erase i_min, (hM.eigenvalues j) ^ 2)
    {e₁ e₂ : QState m} (h1 : IsUnitState e₁) (h2 : IsUnitState e₂) :
    let D : ℝ := (2 : ℝ) ^ m
    let T2 : ℝ := D * (D ^ 2 - 1)
    ((innerProd e₁ (matApply (pauliExpand τ) e₁)).re -
     (innerProd e₂ (matApply (pauliExpand τ) e₂)).re) ^ 2 ≤ 2 * (1 - c₀) * T2 := by
  intro D T2
  let S : QMat m := pauliExpand τ
  have hD_ge2 : (2 : ℝ) ≤ D := by
    have : (2 : ℕ) ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    dsimp only [D]; exact_mod_cast this
  have hS_frob : frobSq S = T2 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx m)), h0]
    have ht : ∀ p ∈ nzPts m, (τ p) ^ 2 = 1 := fun p hp => by
      rcases hpm p (Finset.mem_erase.mp hp).1 with h | h <;> rw [h] <;> norm_num
    change (2 : ℝ) ^ m * (0 ^ 2 + ∑ p ∈ nzPts m, (τ p) ^ 2) = T2
    rw [zero_pow (by norm_num), zero_add, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul,
        mul_one, nzPts, card_PauliIdx_erase_zero m]
  let M : Matrix (F2 m) (F2 m) ℂ := Matrix.of S
  have hM : M.IsHermitian := by
    ext x y; simp only [Matrix.conjTranspose_apply, M, Matrix.of_apply, S]
    rw [pauliExpand_herm τ x y, star_star]
  let ev : F2 m → ℝ := hM.eigenvalues
  let U := hM.eigenvectorUnitary
  let Dmat : Matrix (F2 m) (F2 m) ℂ := Matrix.diagonal (RCLike.ofReal ∘ ev)
  have hspec : M = Unitary.conjStarAlgAut ℂ (Matrix (F2 m) (F2 m) ℂ) U Dmat := hM.spectral_theorem
  have htr_conj : ∀ X : Matrix (F2 m) (F2 m) ℂ,
      (Unitary.conjStarAlgAut ℂ (Matrix (F2 m) (F2 m) ℂ) U X).trace = X.trace := fun X => by
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    have hU : (star (U : Matrix (F2 m) (F2 m) ℂ)) * (U : Matrix (F2 m) (F2 m) ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hU, Matrix.one_mul]
  have hfrob_eq : T2 = ∑ j : F2 m, (ev j) ^ 2 := by
    rw [← hS_frob]
    have hmul : ∀ X Y : QMat m, Matrix.of (matMul X Y) = Matrix.of X * Matrix.of Y := fun X Y => by
      ext x y; simp [matMul, Matrix.mul_apply]
    have htr : ∀ X : QMat m, matTr X = (Matrix.of X).trace := fun X => by
      simp [matTr, Matrix.trace, Matrix.diag]
    have h1' : (frobSq S : ℂ) = (M * M).trace := by
      rw [← matTr_mul_self_herm (pauliExpand_herm τ), htr, hmul]
    have h2' : M * M = Unitary.conjStarAlgAut ℂ (Matrix (F2 m) (F2 m) ℂ) U (Dmat * Dmat) := by
      conv_lhs => rw [hspec]
      rw [map_mul]
    have h3' : (Dmat * Dmat).trace = ∑ j : F2 m, (((ev j) ^ 2 : ℝ) : ℂ) := by
      simp only [Dmat, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, sq]
    rw [h2', htr_conj, h3', ← Complex.ofReal_sum] at h1'
    exact Complex.ofReal_injective h1'
  -- Pick `i_max` maximizing `ev` and `i_min` minimizing `ev` on `Finset.univ : Finset (F2 m)`.
  have huniv_ne : (Finset.univ : Finset (F2 m)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ ev huniv_ne
  obtain ⟨i_min, _, hi_min⟩ := Finset.exists_min_image Finset.univ ev huniv_ne
  -- Rayleigh quotient of any unit vector `e` lies in `[ev i_min, ev i_max]`!
  have hray_bounds : ∀ (e : QState m), IsUnitState e →
      ev i_min ≤ (innerProd e (matApply S e)).re ∧ (innerProd e (matApply S e)).re ≤ ev i_max := fun e he => by
    let Umat : Matrix (F2 m) (F2 m) ℂ := (U : Matrix (F2 m) (F2 m) ℂ)
    let w : F2 m → ℂ := Matrix.mulVec Umat.conjTranspose e
    have hUUstar : Umat * Umat.conjTranspose = 1 := Unitary.coe_mul_star_self U
    have hnorm_w : ∑ j : F2 m, Complex.normSq (w j) = 1 := by
      have h1' : dotProduct (star w) w = dotProduct (star e) e := by
        simp only [w, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          Matrix.conjTranspose_conjTranspose, hUUstar, Matrix.vecMul_one]
      have hL : (dotProduct (star w) w).re = ∑ j : F2 m, Complex.normSq (w j) := by
        simp only [dotProduct, Pi.star_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      have hR : dotProduct (star e) e = 1 := by
        simpa [dotProduct, innerProd, Pi.star_apply, IsUnitState] using he
      rw [← hL, h1', hR, Complex.one_re]
    have hray_w : (innerProd e (matApply S e)).re = ∑ j : F2 m, ev j * Complex.normSq (w j) := by
      have hC : innerProd e (matApply S e) = ∑ j : F2 m, ((ev j : ℝ) : ℂ) * (star (w j) * w j) := by
        have hM_mul : matApply S e = Matrix.mulVec M e := by
          ext x; simp [matApply, Matrix.mulVec, dotProduct, M]
        have hspec_mat : M = Umat * Dmat * Umat.conjTranspose := by
          simpa [Umat, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hspec
        have hdot : innerProd e (matApply S e) = dotProduct (star e) (Matrix.mulVec M e) := by
          rw [hM_mul]; rfl
        rw [hdot, hspec_mat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            Matrix.dotProduct_mulVec]
        have hstar_w : Matrix.vecMul (star e) Umat = star w := by
          simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
        rw [hstar_w]
        simp only [dotProduct, Dmat, Matrix.mulVec_diagonal, Function.comp_apply,
          RCLike.ofReal_eq_complex_ofReal]
        refine Finset.sum_congr rfl fun j _ => by
          dsimp only [w]; simp only [Pi.star_apply]; ring
      rw [hC, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (star (w j)) (w j), Complex.star_def, Complex.mul_conj,
          ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hray_w]
    constructor
    · calc ev i_min = ∑ j : F2 m, ev i_min * Complex.normSq (w j) := by
            rw [← Finset.mul_sum, hnorm_w, mul_one]
        _ ≤ ∑ j : F2 m, ev j * Complex.normSq (w j) :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hi_min j (Finset.mem_univ j)) (Complex.normSq_nonneg _)
    · calc ∑ j : F2 m, ev j * Complex.normSq (w j)
          ≤ ∑ j : F2 m, ev i_max * Complex.normSq (w j) :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hi_max j (Finset.mem_univ j)) (Complex.normSq_nonneg _)
        _ = ev i_max := by rw [← Finset.mul_sum, hnorm_w, mul_one]
  obtain ⟨h1_lo, h1_hi⟩ := hray_bounds e₁ h1
  obtain ⟨h2_lo, h2_hi⟩ := hray_bounds e₂ h2
  -- Note `ev i_max ≠ ev i_min` because `Tr(S) = 0` and `frobSq S = T2 > 0`!
  have hne_idx : i_max ≠ i_min := by
    intro heq_idx
    have hconst : ∀ j : F2 m, ev j = ev i_max := fun j =>
      le_antisymm (hi_max j (Finset.mem_univ j)) (heq_idx ▸ hi_min j (Finset.mem_univ j))
    -- Trace of `S = pauliExpand τ` is `D * τ 0 = 0`, forcing `ev i_max = 0`, contradicting `T2 > 0`!
    have htr0 : ∑ j : F2 m, ev j = 0 := by
      have htrS : matTr S = 0 := by
        have h1' : matTr (matMul S (pauliExpand (fun p => if p = 0 then (1 : ℝ) else 0))) =
            (2 : ℂ) ^ m * ∑ p : PauliIdx m, ((τ p * (if p = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) :=
          matTr_pauliExpand_mul τ _
        have hI : pauliExpand (fun p : PauliIdx m => if p = 0 then (1 : ℝ) else 0) =
            fun x y => if x = y then (1 : ℂ) else 0 := by
          ext x y
          simp only [pauliExpand, apply_ite (Complex.ofReal : ℝ → ℂ), Complex.ofReal_one,
            Complex.ofReal_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte, pauliMat, Prod.fst_zero, Prod.snd_zero, add_zero, pauliPh, dot_zero_left,
            chi_zero_left, Int.cast_one, eq_comm]
        have hSI : matMul S (pauliExpand (fun p : PauliIdx m => if p = 0 then (1 : ℝ) else 0)) = S := by
          rw [hI]; ext x y; simp [matMul]
        rw [hSI] at h1'
        have hsum0 : ∑ p : PauliIdx m, ((τ p * (if p = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) = 0 :=
          Finset.sum_eq_zero fun p _ => by by_cases hp : p = 0 <;> simp [hp, h0]
        rw [h1', hsum0, mul_zero]
      have htrM : (M.trace) = ∑ j : F2 m, ((ev j : ℝ) : ℂ) := by
        conv_lhs => rw [hspec]
        rw [htr_conj]
        simp [Dmat, Matrix.trace_diagonal]
      have hMeq : M.trace = matTr S := by simp [matTr, M, Matrix.trace, Matrix.diag]
      rw [hMeq, htrS, ← Complex.ofReal_sum] at htrM
      exact (Complex.ofReal_injective htrM.symm)
    have hD_ev0 : D * ev i_max = 0 := by
      have hcard : ((Finset.univ : Finset (F2 m)).card : ℝ) = D := by
        rw [Finset.card_univ, card_F2]; simp [D]
      have : ∑ j : F2 m, ev j = D * ev i_max := by
        rw [Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const, nsmul_eq_mul, hcard]
      linarith
    have hev0 : ev i_max = 0 := by
      rcases mul_eq_zero.mp hD_ev0 with h | h
      · linarith
      · exact h
    have hT2_0 : T2 = 0 := by
      rw [hfrob_eq]
      refine Finset.sum_eq_zero fun j _ => by rw [hconst j, hev0]; norm_num
    have hT2_pos : 0 < T2 := by dsimp only [T2]; nlinarith
    linarith
  have hbulk_ge := hbulk hM i_max i_min hne_idx
  have hsplit : ∑ j : F2 m, (ev j) ^ 2 =
      (ev i_max) ^ 2 + (ev i_min) ^ 2 + ∑ j ∈ (Finset.univ.erase i_max).erase i_min, (ev j) ^ 2 := by
    have hmem_min : i_min ∈ (Finset.univ : Finset (F2 m)).erase i_max :=
      Finset.mem_erase.mpr ⟨hne_idx.symm, Finset.mem_univ i_min⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i_max),
        ← Finset.add_sum_erase _ _ hmem_min]
    ring
  have h2sum : (ev i_max) ^ 2 + (ev i_min) ^ 2 ≤ (1 - c₀) * T2 := by
    dsimp only [T2, D] at hbulk_ge hfrob_eq ⊢
    linarith
  have hdiff_abs : |(innerProd e₁ (matApply S e₁)).re - (innerProd e₂ (matApply S e₂)).re| ≤
      ev i_max - ev i_min := by
    rw [abs_le]; constructor <;> linarith
  have hdiff_sq : ((innerProd e₁ (matApply S e₁)).re - (innerProd e₂ (matApply S e₂)).re) ^ 2 ≤
      (ev i_max - ev i_min) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hdiff_abs 2
  have hcs2 : (ev i_max - ev i_min) ^ 2 ≤ 2 * ((ev i_max) ^ 2 + (ev i_min) ^ 2) := by
    nlinarith [sq_nonneg (ev i_max + ev i_min)]
  linarith

end AsymptoticSubspaceAndRealSIC

-- Re-export all Stage 17–18 final milestone theorems at `MultiQubitMUB` root namespace.
export AsymptoticSubspaceAndRealSIC (
  sum_pauliSq_subspace
  twoStateJ_ge_of_subspace
  twoStateJ_ge_two_add_subspace_gap
  twoStateJ_ge_of_k_stabilizers
  sum_pauliSq_quadric_coset
  pauliExpect_eq_zero_of_real_antisym
  no_real_pauli_sic_all
  sum_innerProd_pauliApply_mul
  crossPauli_selfDual_deriv
  crossPauli_autocorr_outer
  sum_pauliDiff_sq
  sum_pauliDiff_pow4_le
  twoState_indefiniteSpread_ge
  twoState_indefiniteSpread_le_of_bulkFloor
)

end MultiQubitMUB
