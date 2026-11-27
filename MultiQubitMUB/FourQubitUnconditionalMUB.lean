import MultiQubitMUB.FourQubitContextualityMUB
import MultiQubitMUB.FourQubitCDCerts
import MultiQubitMUB.FourQubitQminus52
import MultiQubitMUB.FourQubitW52DPLLSoundness
import MultiQubitMUB.FourQubitW52Orbit0Soundness
import MultiQubitMUB.FourQubitW52Orbit2a
import MultiQubitMUB.FourQubitW52Orbit2b
import MultiQubitMUB.FourQubitW52Orbit1a
import MultiQubitMUB.FourQubitW52Orbit1b
import MultiQubitMUB.FourQubitW52Orbit1c

/-!
# Unconditional 4-Qubit Contextuality Degree (`CD(W(7,2)) ≥ 1575`) and Strict MUB Separation (`F₄(|ψ⟩) > 31/16`)

Assembles the complete, 100% unconditional, machine-checked Lean 4 proof of:
1. `signCubeSum_four_le_6615` (`CD(W(7,2)) ≥ 1575`, equivalently `CD(Q⁻(7,2)) ≥ 315`),
2. `pauliMoment4_four_ge_193_100` (`∀ |ψ⟩, 193 / 100 ≤ pauliMoment4 4 ψ`),
3. `pauliMoment4_four_gt_mub` (`∀ |ψ⟩, 31 / 16 < pauliMoment4 4 ψ`),

with **zero `sorry`**, **zero `native_decide`**, and **standard three axioms only**
(`[propext, Classical.choice, Quot.sound]`).

## Complete Proof Chain
- **Part 0** (`FourQubitContextualityCore.signCubeSum_le_6615_of_minSlice`):
  Double-counting `W(7,2) → Q⁻(7,2) → 136 Q(6,2) slices → 28 Q⁻(5,2)` quadrics reduces `CD(Q⁻(7,2)) ≥ 315`
  to ruling out a 4-qubit sign assignment `s4` with `f_Q < 315`, min-slice at `c0_88` (`f_A ≤ 92`),
  and min-`Q⁻(5,2)` at `c0_09` (`f₂₇ ≤ 13`).
- **Part 1** (`FourQubitQminus52.qminus52_le13_classified`):
  Classifies all `Q⁻(5,2)` assignments with `f₂₇ ≤ 13` via `O⁻(6,2)` + gauge into exactly 3 canonical
  orbits `rep27[0..2]` (`f₂₇ = 9, 12, 13`).
- **Part 2c** (`FourQubitW52Orbit0Soundness.orbit0_hits_sp42`):
  Zero-search spectral projector (`R₃₆² = 36 R₃₆`) + `4 × K_{3,3,3}` 3-coloring + `C₄`-free 3-regular
  bipartite bounds + `k ≤ 5` stabilizer coverage maps EVERY `f_A ≤ 92` extension of Orbit 0 into `sp42Certs`.
- **Parts 2a & 2b** (`FourQubitW52DPLLSoundness.orbit_dpll_hits_sp42`):
  36-bit + 144-bit SIMD DPLL + stabilizer orbit coverage (`orb2_trees_a/b`, `orb1_trees_a/b/c`) rules out
  Orbit 2 completely (0 `O` leaves) and maps every surviving extension of Orbit 1 into `sp42Certs`.
- **Part 3** (`FourQubitCDCerts.sp42Certs_valid` + `FourQubitCDCertEngine.cd315_of_hits_cert`):
  All 42 exact integer `56 × 56` SOS + Cholesky + diagonal-dominance certificates verify `CD(Q⁻(7,2)) ≥ 315`.
- **Part 4** (`FourQubitContextualityMUB.pauliMoment4_four_gt_mub_of_contextuality_1575`):
  Combines `signCubeSum_four_le_6615` with the 174-leaf adaptive spectral + symplectic Turán certificate
  to prove `(31 / 16 : ℝ) < pauliMoment4 4 ψ` unconditionally for EVERY 4-qubit pure quantum state!
-/

namespace MultiQubitMUB

open FourQubitCD

set_option maxRecDepth 20000 in
private lemma orb1_allPats_covered :
    (orb1_allPats.all fun p => ((orb1_trees_a ++ orb1_trees_b ++ orb1_trees_c).map Prod.fst).contains p) = true := by
  rfl

set_option maxRecDepth 20000 in
private lemma orb2_allPats_covered :
    (orb2_allPats.all fun p => ((orb2_trees_a ++ orb2_trees_b).map Prod.fst).contains p) = true := by
  rfl

/-- **Unconditional 4-Qubit Symplectic Contextuality Bound (`CD(W(7,2)) ≥ 1575`)**:
    For every 4-qubit Pauli sign assignment `σ : PauliIdx 4 → ℝ` with `σ 0 = 0` and
    `σ p ∈ {±1}` for `p ≠ 0`, the signed commuting-triple sum satisfies `signCubeSum 4 σ ≤ 6615`. -/
theorem signCubeSum_four_le_6615 :
    ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615 := by
  refine signCubeSum_le_6615_of_minSlice ?_
  intro s4 hs4 hQlt hmin4 hfA hmin3 hf27
  let s3 := restrictA s4
  have hs3 : IsSignAssign s3 := restrictA_isSignAssign hs4
  -- Part 1: Classify `s3` on `Qminus c0_09` (`f₂₇ ≤ 13`) into `r ∈ {0, 1, 2}`!
  obtain ⟨r, us1, g1, hus1_Q, hmatch1⟩ := qminus52_le13_classified hs3 hf27
  let s3' := applyGauge g1 (applyTransvWord us1 s3)
  have hs3' : IsSignAssign s3' := applyGauge_isSignAssign g1 (applyTransvWord_isSignAssign us1 hs3)
  have hfeq1 : w5FrustEq s3' (applyTransvWord us1 s3) := w5FrustEq_applyGauge g1 _
  have hfA' : frustPairs (nzPts 3) s3' ≤ 92 * 6 := by
    rw [frustPairs_of_w5FrustEq (by simp [nzPts]) hfeq1, frustPairs_nzPts_applyTransvWord]
    exact hfA
  have hmin3' : isMinQminus09 s3' :=
    isMinQminus09_of_w5FrustEq (w5FrustEq_symm hfeq1)
      (isMinQminus09_applyTransvWord_Ominus hus1_Q hmin3)
  -- Part 2: Every orbit `r ∈ {0, 1, 2}` hits one of the 42 certified `Sp(6,2)` orbits!
  have hhit : ∃ (spId : Fin 42) (us2 : List (PauliIdx 3)),
      w5FrustEq (applyTransvWord us2 s3') (listToSign3 (sp42Certs spId).s64) := by
    fin_cases r
    · exact orbit0_hits_sp42 hs3' hmatch1 hfA'
    · have ho1 : orb1_O12 = [0, 3, 4, 5, 10, 11, 28, 31, 32, 33, 34, 35] := rfl
      have htrees1 : checkPatList (if (⟨1, by decide⟩ : Fin 3).val = 1 then orb1_tables else orb2_tables)
          orb1_O12 (orb1_trees_a ++ orb1_trees_b ++ orb1_trees_c) = true := by
        simp only [↓reduceIte]
        rw [checkPatList_append, checkPatList_append, ho1, orb1_trees_a_valid, orb1_trees_b_valid, orb1_trees_c_valid]
        rfl
      exact orbit_dpll_hits_sp42 ⟨1, by decide⟩ (Or.inl rfl) orb1_O12 orb1_stab orb1_allPats
        (orb1_trees_a ++ orb1_trees_b ++ orb1_trees_c)
        orb1_stab_covers htrees1 orb1_allPats_covered
        hs3' hmatch1 hfA' hmin3'
    · have ho2 : orb2_O12 = [1, 3, 6, 7, 10, 11, 20, 24, 25, 28, 32, 33] := rfl
      have htrees2 : checkPatList (if (⟨2, by decide⟩ : Fin 3).val = 1 then orb1_tables else orb2_tables)
          orb2_O12 (orb2_trees_a ++ orb2_trees_b) = true := by
        simp only [show ¬((2 : Nat) = 1) by decide, ↓reduceIte]
        rw [checkPatList_append, ho2, orb2_trees_a_valid, orb2_trees_b_valid]
        rfl
      exact orbit_dpll_hits_sp42 ⟨2, by decide⟩ (Or.inr rfl) orb2_O12 orb2_stab orb2_allPats
        (orb2_trees_a ++ orb2_trees_b)
        orb2_stab_covers htrees2 orb2_allPats_covered
        hs3' hmatch1 hfA' hmin3'
  -- Part 3: Collapse `w5FrustEq` and apply `cd315_of_hits_cert` to contradict `f_Q < 315`!
  obtain ⟨spId, us2, hfeq2⟩ := hhit
  have hfeqTot : w5FrustEq (applyTransvWord (us1 ++ us2) (restrictA s4))
      (listToSign3 (sp42Certs spId).s64) := by
    rw [applyTransvWord_append]
    exact w5FrustEq_trans (w5FrustEq_applyTransvWord us2 (w5FrustEq_symm hfeq1)) hfeq2
  have h315 := cd315_of_hits_cert (sp42Certs spId) (sp42Certs_valid spId) hs4 hmin4 (us1 ++ us2) hfeqTot
  omega

/-- **Unconditional 4-Qubit Contextuality-Bridge Lower Bound**:
    For every 4-qubit pure quantum state `|ψ⟩`, `193 / 100 ≤ pauliMoment4 4 ψ`. -/
theorem pauliMoment4_four_ge_193_100 {ψ : QState 4} (hunit : IsUnitState ψ) :
    (193 / 100 : ℝ) ≤ pauliMoment4 4 ψ :=
  pauliMoment4_four_of_contextuality_1575 signCubeSum_four_le_6615 hunit

/-- **Main Unconditional 4-Qubit Strict MUB Separation Theorem**:
    For EVERY 4-qubit pure quantum state `|ψ⟩`, its Pauli fourth moment strictly exceeds
    the 4-qubit Pauli-covariant MUB threshold `31 / 16 = 1.9375`:
      `F₄(|ψ⟩) = ∑_{p ∈ 𝔽₂⁸} |⟨ψ|P_p|ψ⟩|⁴ > 31 / 16`.
    Proved unconditionally with zero `sorry`, zero `native_decide`, and standard three axioms only. -/
theorem pauliMoment4_four_gt_mub {ψ : QState 4} (hunit : IsUnitState ψ) :
    (31 / 16 : ℝ) < pauliMoment4 4 ψ := by
  have h := @pauliMoment4_four_gt_mub_of_contextuality_1575 signCubeSum_four_le_6615 ψ
  revert h
  generalize pauliMoment4 4 ψ = F
  intro h
  exact h hunit

end MultiQubitMUB
