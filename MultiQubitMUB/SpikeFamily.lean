import MultiQubitMUB.PauliGroup

/-!
# The `GL(n, 𝔽₂) ⋊ ⟨H^⊗n⟩`-Invariant Spike+Uniform Family

For every `n ≥ 1` (`d = 2ⁿ`) and real parameter `s` satisfying `0 < 1 - ((d - 1) / d) * s`
and `0 ≤ -1 + 4 * s - (4 * (d - 1) / d) * s²`, we define the explicit pure state
`|ψ_n(s)⟩ = α |0⟩ + β ∑_{x ≠ 0} |x⟩` and prove the exact closed-form Pauli 4th moment:
  `pauliMoment4 n (spikeState n s) = 1 + (d - 1) * (2 * (1 - s)⁴ + (d/2 - 1) * (1 - 2s)⁴ + (d/2) * (-1 + 4s - 4(d-1)/d * s²)²)`.

Remarkably, this single 1-parameter family unifies the known optimal magic states across `n = 1, 2, 3, 4`:
- `n = 1`, `s = 1 - 1/√3`: exact 1-qubit SIC / `|T⟩` state (`F₁ = 4/3`).
- `n = 2`, `s = 1/2`: exact 2-qubit MUB fiducial (`F₂ = 7/4`, Clifford-equivalent to `(1, 1, 1, i)/2`).
- `n = 3`, `s = 2/3`: exact 3-qubit **Hoggar SIC** (`F₃ = 16/9`, all 63 non-identity Paulis have `|⟨P⟩| = 1/3`).
- `n = 4`, cubic root of `453 s³ - 708 s² + 368 s - 64 = 0`: candidate global 4-qubit magic extremizer
  (`F₄ ≈ 2.1505201547`, certified `F₄ < 2.150521`).
-/

namespace MultiQubitMUB

open scoped Classical

/-- Pauli 4th moment `F_n(ψ) = ∑_{p ∈ 𝔽₂²ⁿ} |⟨ψ | P_p | ψ⟩|⁴` of an `n`-qubit state `ψ`. -/
noncomputable def pauliMoment4 (n : ℕ) (ψ : QState n) : ℝ :=
  ∑ p : PauliIdx n, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2

/-- Closed-form Pauli 4th moment polynomial of the `GL(n, 𝔽₂) ⋊ ⟨H^⊗n⟩`-invariant spike+uniform family. -/
noncomputable def spikeMomentPoly (n : ℕ) (s : ℝ) : ℝ :=
  let d : ℝ := (2 : ℝ) ^ n
  1 + (d - 1) * (2 * (1 - s) ^ 4 + (d / 2 - 1) * (1 - 2 * s) ^ 4 +
    (d / 2) * (-1 + 4 * s - (4 * (d - 1) / d) * s ^ 2) ^ 2)

/-- The explicit `GL(n, 𝔽₂) ⋊ ⟨H^⊗n⟩`-invariant state `|ψ_n(s)⟩ = α |0⟩ + β ∑_{x ≠ 0} |x⟩`. -/
noncomputable def spikeState (n : ℕ) (s : ℝ) : QState n :=
  let d : ℝ := (2 : ℝ) ^ n
  let p : ℝ := 1 - ((d - 1) / d) * s
  let α : ℝ := Real.sqrt p
  let u : ℝ := 2 * p - 1
  let v : ℝ := Real.sqrt (-1 + 4 * s - (4 * (d - 1) / d) * s ^ 2)
  let β : ℂ := ((u / (2 * α) : ℝ) : ℂ) + ((v / (2 * α) : ℝ) : ℂ) * Complex.I
  fun x => if x = 0 then (α : ℂ) else β

/-- Feasibility condition for `spikeState n s` to be a valid unit vector. -/
def SpikeFeasible (n : ℕ) (s : ℝ) : Prop :=
  0 < 1 - (((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n) * s ∧
  0 ≤ -1 + 4 * s - (4 * ((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n) * s ^ 2

lemma spikeState_unit {n : ℕ} {s : ℝ} (hf : SpikeFeasible n s) :
    IsUnitState (spikeState n s) := by
  set d : ℝ := (2 : ℝ) ^ n
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  set p : ℝ := 1 - ((d - 1) / d) * s
  have hp_pos : 0 < p := hf.1
  set α : ℝ := Real.sqrt p
  have hα_pos : 0 < α := Real.sqrt_pos.mpr hp_pos
  have hα_sq : α ^ 2 = p := Real.sq_sqrt (le_of_lt hp_pos)
  set u : ℝ := 2 * p - 1
  set v2 : ℝ := -1 + 4 * s - (4 * (d - 1) / d) * s ^ 2
  have hv2_nn : 0 ≤ v2 := hf.2
  set v : ℝ := Real.sqrt v2
  have hv_sq : v ^ 2 = v2 := Real.sq_sqrt hv2_nn
  set β : ℂ := ((u / (2 * α) : ℝ) : ℂ) + ((v / (2 * α) : ℝ) : ℂ) * Complex.I
  have hβ_ns : Complex.normSq β = s / d := by
    have h1 : Complex.normSq β = (u / (2 * α)) ^ 2 + (v / (2 * α)) ^ 2 := by
      simp only [β, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [h1]
    have hnum : u ^ 2 + v2 = 4 * p * (s / d) := by
      dsimp only [u, v2, p]; field_simp [hd_ne]; ring
    have h2 : (u / (2 * α)) ^ 2 + (v / (2 * α)) ^ 2 = (u ^ 2 + v ^ 2) / (4 * α ^ 2) := by ring
    rw [h2, hv_sq, hα_sq, hnum]
    field_simp [ne_of_gt hp_pos]
  rw [IsUnitState, innerProd_self_eq_sum_normSq]
  have hsum : ∑ x : F2 n, Complex.normSq (spikeState n s x) = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    have h0 : Complex.normSq (spikeState n s 0) = p := by
      have hψ0 : spikeState n s 0 = (α : ℂ) := by simp [spikeState, α, p, d]
      rw [hψ0, Complex.normSq_ofReal, ← sq, hα_sq]
    have hrest : ∑ x ∈ Finset.univ.erase (0 : F2 n), Complex.normSq (spikeState n s x) =
        (d - 1) * (s / d) := by
      have hterm : ∀ x ∈ Finset.univ.erase (0 : F2 n), Complex.normSq (spikeState n s x) = s / d := by
        intro x hx
        have hne : x ≠ 0 := (Finset.mem_erase.mp hx).1
        change Complex.normSq (if x = 0 then (α : ℂ) else β) = s / d
        simp [hne, hβ_ns]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ.erase (0 : F2 n)).card : ℝ) = d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        simp [d, ZMod.card, Nat.cast_sub h1]
      rw [hcard]
    rw [h0, hrest]
    simp only [p]; field_simp [hd_ne]; ring
  rw [hsum, Complex.ofReal_one]

/-- Exact closed-form Pauli 4th moment for the `GL(n, 𝔽₂) ⋊ ⟨H^⊗n⟩`-invariant spike+uniform family (`n ≥ 1`). -/
theorem pauliMoment4_spikeState {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hf : SpikeFeasible n s) :
    pauliMoment4 n (spikeState n s) = spikeMomentPoly n s := by
  set d : ℝ := (2 : ℝ) ^ n
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  set p : ℝ := 1 - ((d - 1) / d) * s
  have hp_pos : 0 < p := hf.1
  set α : ℝ := Real.sqrt p
  have hα_pos : 0 < α := Real.sqrt_pos.mpr hp_pos
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hα_sq : α ^ 2 = p := Real.sq_sqrt (le_of_lt hp_pos)
  set u : ℝ := 2 * p - 1
  set v2 : ℝ := -1 + 4 * s - (4 * (d - 1) / d) * s ^ 2
  have hv2_nn : 0 ≤ v2 := hf.2
  set v : ℝ := Real.sqrt v2
  have hv_sq : v ^ 2 = v2 := Real.sq_sqrt hv2_nn
  set β : ℂ := ((u / (2 * α) : ℝ) : ℂ) + ((v / (2 * α) : ℝ) : ℂ) * Complex.I
  set ψ : QState n := spikeState n s
  have hq : star β * β = ((s / d : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
    congr 1
    have h1 : Complex.normSq β = (u / (2 * α)) ^ 2 + (v / (2 * α)) ^ 2 := by
      simp only [β, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [h1]
    have hnum : u ^ 2 + v2 = 4 * p * (s / d) := by
      dsimp only [u, v2, p]; field_simp [hd_ne]; ring
    have h2 : (u / (2 * α)) ^ 2 + (v / (2 * α)) ^ 2 = (u ^ 2 + v ^ 2) / (4 * α ^ 2) := by ring
    rw [h2, hv_sq, hα_sq, hnum]
    field_simp [ne_of_gt hp_pos]
  have hαβ : star (α : ℂ) * β = ((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.star_def, Complex.conj_ofReal]
    apply Complex.ext
    · simp only [β, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero]
      field_simp [hα_ne]
    · simp only [β, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
      field_simp [hα_ne]
  have hβα : star β * (α : ℂ) = ((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I := by
    rw [Complex.star_def]
    apply Complex.ext
    · simp only [β, Complex.mul_re, Complex.sub_re, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, neg_zero]
      field_simp [hα_ne]
    · simp only [β, Complex.mul_im, Complex.sub_im, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, zero_add, mul_neg]
      field_simp [hα_ne]; ring
  -- Evaluate `Complex.normSq (innerProd ψ (pauliApply (a, b) ψ))` in all 5 cases!
  have hψ0_eq : ψ 0 = (α : ℂ) := by simp [ψ, spikeState, α, p, d]
  have hval : ∀ a b : F2 n,
      Complex.normSq (innerProd ψ (pauliApply (a, b) ψ)) =
        if a = 0 then (if b = 0 then 1 else (1 - s) ^ 2)
        else if b = 0 then (1 - s) ^ 2
        else if dot a b = 0 then (1 - 2 * s) ^ 2
        else v2 := by
    intro a b
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb
        simp only [↓reduceIte]
        have h00 : (0 : PauliIdx n) = (0, 0) := rfl
        rw [← h00, pauliApply_zero, spikeState_unit hf, Complex.normSq_one]
      · simp only [↓reduceIte, hb]
        have hsum : innerProd ψ (pauliApply (0, b) ψ) = ((1 - s : ℝ) : ℂ) := by
          simp only [innerProd, pauliApply, add_zero, pauliPh, dot_zero_left, ↓reduceIte, one_mul]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
          have h0 : star (ψ 0) * ((chi b 0 : ℂ) * ψ 0) = (p : ℂ) := by
            rw [hψ0_eq, chi_zero_right, Int.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal,
              ← Complex.ofReal_mul, ← sq, hα_sq]
          have hrest : ∑ x ∈ Finset.univ.erase (0 : F2 n),
              star (ψ x) * ((chi b x : ℂ) * ψ x) = -((s / d : ℝ) : ℂ) := by
            have ht : ∀ x ∈ Finset.univ.erase (0 : F2 n),
                star (ψ x) * ((chi b x : ℂ) * ψ x) = ((s / d : ℝ) : ℂ) * (chi x b : ℂ) := by
              intro x hx
              have hne : x ≠ 0 := (Finset.mem_erase.mp hx).1
              have hψx : ψ x = β := by change (if x = 0 then (α : ℂ) else β) = β; simp [hne]
              rw [hψx, chi_comm b x]
              calc star β * ((chi x b : ℂ) * β) = (star β * β) * (chi x b : ℂ) := by ring
                _ = ((s / d : ℝ) : ℂ) * (chi x b : ℂ) := by rw [hq]
            rw [Finset.sum_congr rfl ht, ← Finset.mul_sum, ← Int.cast_sum]
            have hchi_er : ∑ x ∈ Finset.univ.erase (0 : F2 n), chi x b = -1 := by
              have hall := sum_chi b
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), chi_zero_left] at hall
              simp only [hb, ↓reduceIte] at hall
              linarith
            rw [hchi_er]; push_cast; ring
          rw [h0, hrest, ← sub_eq_add_neg, ← Complex.ofReal_sub]
          congr 1; dsimp only [p]; field_simp [hd_ne]; ring
        rw [hsum, Complex.normSq_ofReal, sq]
    · simp only [ha, ↓reduceIte]
      -- Split `∑ x` into `x = 0`, `x = a`, and `x ∈ (univ.erase 0).erase a`!
      have ha_in : a ∈ Finset.univ.erase (0 : F2 n) :=
        Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
      have hexp : innerProd ψ (pauliApply (a, b) ψ) =
          pauliPh (a, b) * (star (α : ℂ) * β + (chi b a : ℂ) * (star β * (α : ℂ)) +
            ((s / d : ℝ) : ℂ) * (((if b = 0 then (2 : ℤ) ^ n else 0) - 1 - chi b a : ℤ) : ℂ)) := by
        simp only [innerProd, pauliApply]
        have hfac : (∑ x : F2 n, star (ψ x) * (pauliPh (a, b) * (chi b x : ℂ) * ψ (x + a))) =
            pauliPh (a, b) * ∑ x : F2 n, (chi b x : ℂ) * star (ψ x) * ψ (x + a) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [hfac]; congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
            ← Finset.add_sum_erase _ _ ha_in]
        have h0 : (chi b 0 : ℂ) * star (ψ 0) * ψ (0 + a) = star (α : ℂ) * β := by
          have hψ0 : ψ 0 = (α : ℂ) := by change (if (0 : F2 n) = 0 then (α : ℂ) else β) = (α : ℂ); simp
          have hψa : ψ a = β := by change (if a = 0 then (α : ℂ) else β) = β; simp [ha]
          rw [chi_zero_right, zero_add, hψ0, hψa]; simp
        have hta : (chi b a : ℂ) * star (ψ a) * ψ (a + a) = (chi b a : ℂ) * (star β * (α : ℂ)) := by
          have hψ0 : ψ 0 = (α : ℂ) := by change (if (0 : F2 n) = 0 then (α : ℂ) else β) = (α : ℂ); simp
          have hψa : ψ a = β := by change (if a = 0 then (α : ℂ) else β) = β; simp [ha]
          rw [f2_add_self, hψ0, hψa]; ring
        have hrest : ∑ x ∈ (Finset.univ.erase (0 : F2 n)).erase a,
            (chi b x : ℂ) * star (ψ x) * ψ (x + a) =
            ((s / d : ℝ) : ℂ) * (((if b = 0 then (2 : ℤ) ^ n else 0) - 1 - chi b a : ℤ) : ℂ) := by
          have ht : ∀ x ∈ (Finset.univ.erase (0 : F2 n)).erase a,
              (chi b x : ℂ) * star (ψ x) * ψ (x + a) = ((s / d : ℝ) : ℂ) * (chi x b : ℂ) := by
            intro x hx
            have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
            have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hxa0 : x + a ≠ 0 := fun hc => hxa (by
              have := congr_arg (· + a) hc; simpa [f2_add_cancel_right] using this)
            have hψx : ψ x = β := by change (if x = 0 then (α : ℂ) else β) = β; simp [hx0]
            have hψxa : ψ (x + a) = β := by change (if x + a = 0 then (α : ℂ) else β) = β; simp [hxa0]
            rw [hψx, hψxa, chi_comm b x]
            calc (chi x b : ℂ) * star β * β = (star β * β) * (chi x b : ℂ) := by ring
              _ = ((s / d : ℝ) : ℂ) * (chi x b : ℂ) := by rw [hq]
          rw [Finset.sum_congr rfl ht, ← Finset.mul_sum, ← Int.cast_sum]
          congr 2
          have hall := sum_chi b
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)),
              ← Finset.add_sum_erase _ _ ha_in, chi_zero_left, chi_comm a b] at hall
          linarith
        rw [h0, hta, hrest]; ring
      rw [hexp, hαβ, hβα]
      by_cases hb : b = 0
      · subst hb
        simp only [↓reduceIte, pauliPh, dot_zero_right, one_mul, chi_zero_left, Int.cast_one]
        have hEq : (((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I +
            (((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I) +
            ((s / d : ℝ) : ℂ) * (((2 : ℤ) ^ n - 1 - 1 : ℤ) : ℂ)) = ((1 - s : ℝ) : ℂ) := by
          have hdC : (((2 : ℤ) ^ n - 1 - 1 : ℤ) : ℂ) = (((d - 2 : ℝ) : ℝ) : ℂ) := by
            dsimp only [d]; push_cast; ring
          rw [hdC]
          have hreal : u / 2 + u / 2 + (s / d) * (d - 2) = 1 - s := by
            dsimp only [u, p]; field_simp [hd_ne]; ring
          calc ((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I +
                (((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I) +
                ((s / d : ℝ) : ℂ) * ((d - 2 : ℝ) : ℂ)
              = (((u / 2 + u / 2 + (s / d) * (d - 2) : ℝ) : ℂ)) := by push_cast; ring
            _ = ((1 - s : ℝ) : ℂ) := by rw [hreal]
        rw [hEq, Complex.normSq_ofReal, sq]
      · simp only [hb, ↓reduceIte]
        rcases zmod2_cases (dot a b) with hdab | hdab
        · simp only [hdab, ↓reduceIte, pauliPh, one_mul, chi, dot_comm b a, Int.cast_one]
          have hEq : (((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I +
              (((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I) +
              ((s / d : ℝ) : ℂ) * (((0 - 1 - 1 : ℤ) : ℤ) : ℂ)) = ((1 - 2 * s : ℝ) : ℂ) := by
            have hreal : u / 2 + u / 2 + (s / d) * (-2) = 1 - 2 * s := by
              dsimp only [u, p]; field_simp [hd_ne]; ring
            calc ((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I +
                  (((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I) +
                  ((s / d : ℝ) : ℂ) * (((0 - 1 - 1 : ℤ) : ℤ) : ℂ)
                = (((u / 2 + u / 2 + (s / d) * (-2) : ℝ) : ℂ)) := by push_cast; ring
              _ = ((1 - 2 * s : ℝ) : ℂ) := by rw [hreal]
          rw [hEq, Complex.normSq_ofReal, sq]
        · have hne0 : dot a b ≠ 0 := by rw [hdab]; exact one_ne_zero
          simp only [hne0, ↓reduceIte, pauliPh, chi, dot_comm b a, Int.cast_neg, Int.cast_one]
          have hEq : Complex.I * (((u / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I +
              (-1 : ℂ) * (((u / 2 : ℝ) : ℂ) - ((v / 2 : ℝ) : ℂ) * Complex.I) +
              ((s / d : ℝ) : ℂ) * (((0 - 1 - -1 : ℤ) : ℤ) : ℂ)) = ((-v : ℝ) : ℂ) := by
            apply Complex.ext <;> simp
          rw [hEq, Complex.normSq_ofReal, neg_mul_neg, ← sq, hv_sq]
  -- Sum the 4th powers over `(a, b) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`!
  unfold pauliMoment4 spikeMomentPoly
  rw [Fintype.sum_prod_type]
  simp_rw [hval]
  -- Peel off `a = 0`!
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
  have ha0 : (∑ b : F2 n, (if (0 : F2 n) = 0 then (if b = 0 then (1 : ℝ) else (1 - s) ^ 2)
      else if b = 0 then (1 - s) ^ 2 else if dot 0 b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2) =
      1 + (d - 1) * (1 - s) ^ 4 := by
    simp only [↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    simp only [↓reduceIte, one_pow]
    congr 1
    have ht : ∀ b ∈ Finset.univ.erase (0 : F2 n),
        (if b = 0 then (1 : ℝ) else (1 - s) ^ 2) ^ 2 = (1 - s) ^ 4 := fun b hb => by
      have hne : b ≠ 0 := (Finset.mem_erase.mp hb).1
      simp [hne]; ring
    rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase (0 : F2 n)).card : ℝ) = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      simp [d, ZMod.card, Nat.cast_sub h1]
    rw [hcard]
  have hanz : ∀ a ∈ Finset.univ.erase (0 : F2 n),
      (∑ b : F2 n, (if a = 0 then (if b = 0 then (1 : ℝ) else (1 - s) ^ 2)
        else if b = 0 then (1 - s) ^ 2 else if dot a b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2) =
      (1 - s) ^ 4 + (d / 2 - 1) * (1 - 2 * s) ^ 4 + (d / 2) * v2 ^ 2 := by
    intro a ha
    have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
    simp only [hane, ↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n))]
    simp only [↓reduceIte]
    have hcard_dot0 : (Finset.univ.filter (fun b : F2 n => dot a b = 0)).card = 2 ^ (n - 1) := by
      -- `a^⊥` is the kernel of the surjective linear functional `b ↦ dot a b`!
      let L : F2 n →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun b => dot a b
          map_add' := fun b₁ b₂ => dot_add_right a b₁ b₂
          map_smul' := fun c b => by rcases zmod2_cases c with rfl | rfl <;> simp [dot_zero_right] }
      have hsurj : Function.Surjective L := by
        have hex : ∃ i : Fin n, a i ≠ 0 := by
          by_contra hall; push Not at hall; exact hane (funext hall)
        obtain ⟨i, hi⟩ := hex
        have hai : a i = 1 := (zmod2_cases (a i)).resolve_left hi
        intro y
        rcases zmod2_cases y with rfl | rfl
        · exact ⟨0, by simp [L, dot_zero_right]⟩
        · exact ⟨eVec i, by simp [L, dot_eVec_right, hai]⟩
      have hrn := LinearMap.finrank_range_add_finrank_ker L
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrn
      have hker_card : Fintype.card (LinearMap.ker L) = 2 ^ (n - 1) := by
        rw [card_submodule_f2]; congr 1; omega
      have hce : (Finset.univ.filter (fun b : F2 n => dot a b = 0)).card = Fintype.card (LinearMap.ker L) := by
        rw [← Fintype.card_coe]
        exact Fintype.card_congr (Equiv.subtypeEquivRight fun b => by simp [L])
      rw [hce, hker_card]
    have hpow_half : ((2 ^ (n - 1) : ℕ) : ℝ) = d / 2 := by
      have : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
        conv_lhs => rw [show n = 1 + (n - 1) by omega, pow_add]; norm_num
      simp only [d]; push_cast; linarith
    -- Split `univ.erase 0` into `dot a b = 0` and `dot a b ≠ 0`!
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (0 : F2 n)) (fun b : F2 n => dot a b = 0)]
    have hsum0 : ∑ b ∈ (Finset.univ.erase (0 : F2 n)).filter (fun b => dot a b = 0),
        (if b = 0 then (1 - s) ^ 2 else if dot a b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2 =
        (d / 2 - 1) * (1 - 2 * s) ^ 4 := by
      have ht : ∀ b ∈ (Finset.univ.erase (0 : F2 n)).filter (fun b => dot a b = 0),
          (if b = 0 then (1 - s) ^ 2 else if dot a b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2 =
          (1 - 2 * s) ^ 4 := fun b hb => by
        have ⟨hmem, hd0⟩ := Finset.mem_filter.mp hb
        have hbne : b ≠ 0 := (Finset.mem_erase.mp hmem).1
        simp [hbne, hd0]; ring
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
      have hfeq : (Finset.univ.erase (0 : F2 n)).filter (fun b => dot a b = 0) =
          (Finset.univ.filter (fun b : F2 n => dot a b = 0)).erase 0 := by
        ext b; simp [and_comm]
      have h0in : (0 : F2 n) ∈ Finset.univ.filter (fun b : F2 n => dot a b = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ 0, dot_zero_right a⟩
      have h1le : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [hfeq, Finset.card_erase_of_mem h0in, hcard_dot0, Nat.cast_sub h1le, Nat.cast_one, hpow_half]
    have hsum1 : ∑ b ∈ (Finset.univ.erase (0 : F2 n)).filter (fun b => ¬ dot a b = 0),
        (if b = 0 then (1 - s) ^ 2 else if dot a b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2 =
        (d / 2) * v2 ^ 2 := by
      have ht : ∀ b ∈ (Finset.univ.erase (0 : F2 n)).filter (fun b => ¬ dot a b = 0),
          (if b = 0 then (1 - s) ^ 2 else if dot a b = 0 then (1 - 2 * s) ^ 2 else v2) ^ 2 =
          v2 ^ 2 := fun b hb => by
        have ⟨hmem, hd1⟩ := Finset.mem_filter.mp hb
        have hbne : b ≠ 0 := (Finset.mem_erase.mp hmem).1
        simp [hbne, hd1]
      rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]
      have hfeq : (Finset.univ.erase (0 : F2 n)).filter (fun b => ¬ dot a b = 0) =
          Finset.univ.filter (fun b : F2 n => ¬ dot a b = 0) := by
        ext b; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨fun hb0 => h (by rw [hb0, dot_zero_right]), h⟩
      have hcard1 : (Finset.univ.filter (fun b : F2 n => ¬ dot a b = 0)).card = 2 ^ (n - 1) := by
        have htot := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (F2 n))
          (fun b : F2 n => dot a b = 0) (fun _ => (1 : ℕ))
        simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_pi,
          ZMod.card, Finset.prod_const, Fintype.card_fin] at htot
        rw [hcard_dot0] at htot
        have h2n : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_two]
        omega
      rw [hfeq, hcard1, hpow_half]
    rw [hsum0, hsum1]; ring
  rw [ha0, Finset.sum_congr rfl hanz, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.erase (0 : F2 n)).card : ℝ) = d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    simp [d, ZMod.card, Nat.cast_sub h1]
  rw [hcard]; ring

/-- **3-Qubit Hoggar SIC**: `spikeState 3 (2/3)` is a unit state attaining `F₃ = 16/9`! -/
theorem hoggar_sic_three :
    IsUnitState (spikeState 3 (2 / 3)) ∧ pauliMoment4 3 (spikeState 3 (2 / 3)) = 16 / 9 := by
  have hf : SpikeFeasible 3 (2 / 3) := by unfold SpikeFeasible; norm_num
  refine ⟨spikeState_unit hf, ?_⟩
  rw [pauliMoment4_spikeState (by norm_num) hf]
  unfold spikeMomentPoly; norm_num

/-- **4-Qubit Candidate Global Extremizer Upper Bound**:
    `spikeState 4 (622543 / 1000000)` is a valid 4-qubit unit state with `F₄ < 2.150521`! -/
theorem four_qubit_spike_bound :
    IsUnitState (spikeState 4 (622543 / 1000000)) ∧
    pauliMoment4 4 (spikeState 4 (622543 / 1000000)) < 2150521 / 1000000 := by
  have hf : SpikeFeasible 4 (622543 / 1000000) := by unfold SpikeFeasible; norm_num
  refine ⟨spikeState_unit hf, ?_⟩
  rw [pauliMoment4_spikeState (by norm_num) hf]
  unfold spikeMomentPoly; norm_num

end MultiQubitMUB
