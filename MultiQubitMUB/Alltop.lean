module

public import MultiQubitMUB.GaussianInt
public import MultiQubitMUB.Basic
public import MultiQubitMUB.SubspaceInduction
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Theorem 1: Non-Existence of Alltop Functions on `𝔽₂ⁿ` for All `n ≥ 3`

An **Alltop function** on `𝔽₂ⁿ` is a unimodular function `φ : 𝔽₂ⁿ → ℂ` (`|φ(x)| = 1`) whose
every nontrivial multiplicative derivative `g_a(x) = conj(φ(x)) * φ(x + a)` (`a ≠ 0`) has a flat
Walsh–Hadamard spectrum (`|∑_x (-1)^(b·x) g_a(x)| = 2^(n/2)` for all `b ∈ 𝔽₂ⁿ`).

We prove:
1. **Odd `n = 2k + 1 ≥ 3`**: Quantization forces `g_a(x) ∈ {(±1 ± i)/√2}`, contradicting the
   triangle identity `g_a(0) * g_{a+b}(a) = g_b(0)`.
2. **Even `n = 2k ≥ 4`**: Quantization forces `φ(x) ∈ {±1, ±i}` (up to global phase), and the
   2-adic subspace induction theorem (`SubspaceInduction.lean`) forces `4 ∣ |φ(x) - φ(y)|²` for
   all `x, y`, forcing `g_a` to be purely real — contradicting `|t̂_a(b)| = 2^k > 0`.
3. **Combined Theorem (`no_alltop_f2`)**: For ALL `n ≥ 3`, no Alltop function exists on `𝔽₂ⁿ`.
4. **Sharpness (`exists_alltop_two`)**: For `n = 2`, `φ₂ = (1, 1, 1, i)` IS an Alltop function.
5. **Strict Gowers `U³` / Phase-State Pauli Moment Bound (`phasePauliMoment4_gt_mub`)**:
   For all `n ≥ 3` and every phase function `φ : 𝔽₂ⁿ → U(1)`,
   `∑_{a,b} |2^(-n) ∑_x (-1)^(b·x) conj(φ x) φ(x+a)|^4 > 2 - 2^(-n)`.
-/

@[expose] public section

namespace MultiQubitMUB

open scoped Classical

/-- Unimodular Alltop function on `𝔽₂ⁿ`: `|φ(x)| = 1` and `|WHT(g_a)(b)|² = 2^n` for all `a ≠ 0, b`. -/
def IsAlltop (n : ℕ) (φ : F2 n → ℂ) : Prop :=
  (∀ x : F2 n, Complex.normSq (φ x) = 1) ∧
  (∀ a : F2 n, a ≠ 0 → ∀ b : F2 n,
    Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) = (2 : ℝ) ^ n)

/-- Multiplicative derivative `g_a(x) = conj(φ x) * φ(x + a)`. -/
def multDeriv {n : ℕ} (φ : F2 n → ℂ) (a x : F2 n) : ℂ :=
  star (φ x) * φ (x + a)

lemma multDeriv_shift {n : ℕ} (φ : F2 n → ℂ) (a x : F2 n) :
    multDeriv φ a (x + a) = star (multDeriv φ a x) := by
  simp only [multDeriv, f2_add_cancel_right, star_mul, star_star, mul_comm]

lemma multDeriv_normSq {n : ℕ} {φ : F2 n → ℂ} (hunit : ∀ x, Complex.normSq (φ x) = 1) (a x : F2 n) :
    Complex.normSq (multDeriv φ a x) = 1 := by
  simp [multDeriv, map_mul, Complex.normSq_conj, hunit]

lemma isAlltop_smul {n : ℕ} {φ : F2 n → ℂ} (h : IsAlltop n φ) {c : ℂ} (hc : Complex.normSq c = 1) :
    IsAlltop n (fun x => c * φ x) := by
  refine ⟨fun x => by simp [map_mul, hc, h.1 x], fun a ha b => ?_⟩
  have hcc : star c * c = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, hc]; simp
  have hsum : (∑ x : F2 n, (chi b x : ℂ) * star (c * φ x) * (c * φ (x + a))) =
      ∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul]
    calc (chi b x : ℂ) * (star (φ x) * star c) * (c * φ (x + a))
        = (chi b x : ℂ) * star (φ x) * (star c * c) * φ (x + a) := by ring
      _ = (chi b x : ℂ) * star (φ x) * φ (x + a) := by rw [hcc, mul_one]
  rw [hsum]
  exact h.2 a ha b

/-- Real/imaginary parity of the WHT of `g_a`:
    - When `dot a b = 0`: `Im(ĝ_a(b)) = 0` and `(Re(ĝ_a(b)))² = 2^n`.
    - When `dot a b = 1`: `Re(ĝ_a(b)) = 0` and `(Im(ĝ_a(b)))² = 2^n`. -/
lemma alltop_wht_re_im {n : ℕ} {φ : F2 n → ℂ} (h : IsAlltop n φ) {a : F2 n} (ha : a ≠ 0) (b : F2 n) :
    (dot a b = 0 →
      (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) = 0 ∧
      (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) ^ 2 = (2 : ℝ) ^ n) ∧
    (dot a b = 1 →
      (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) = 0 ∧
      (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) ^ 2 = (2 : ℝ) ^ n) := by
  have hre : (∑ x : F2 n, (chi b x : ℂ) * multDeriv φ a x).re =
      ∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re := by
    simp [Complex.re_sum]
  have him : (∑ x : F2 n, (chi b x : ℂ) * multDeriv φ a x).im =
      ∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im := by
    simp [Complex.im_sum]
  have hns := h.2 a ha b
  have hns' : (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) ^ 2 +
      (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) ^ 2 = (2 : ℝ) ^ n := by
    have hmul : ∀ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a) =
        (chi b x : ℂ) * multDeriv φ a x := fun x => by simp [multDeriv, mul_assoc]
    simp_rw [hmul] at hns
    rw [Complex.normSq_apply, hre, him] at hns
    linarith
  constructor
  · intro hd
    have hshift : (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) =
        ∑ x : F2 n, (chi b (x + a) : ℝ) * (multDeriv φ a (x + a)).im :=
      (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)).symm
    have hneg : (∑ x : F2 n, (chi b (x + a) : ℝ) * (multDeriv φ a (x + a)).im) =
        -(∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_add_right, multDeriv_shift]
      have hba : chi b a = 1 := by simp [chi, dot_comm, hd]
      simp [hba]
    have him0 : (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).im) = 0 := by linarith
    refine ⟨him0, ?_⟩
    rw [him0] at hns'; linarith
  · intro hd
    have hshift : (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) =
        ∑ x : F2 n, (chi b (x + a) : ℝ) * (multDeriv φ a (x + a)).re :=
      (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)).symm
    have hneg : (∑ x : F2 n, (chi b (x + a) : ℝ) * (multDeriv φ a (x + a)).re) =
        -(∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_add_right, multDeriv_shift]
      have hba : chi b a = -1 := by
        have hne : dot b a ≠ 0 := by rw [dot_comm, hd]; exact one_ne_zero
        simp [chi, hne]
      simp [hba]
    have hre0 : (∑ x : F2 n, (chi b x : ℝ) * (multDeriv φ a x).re) = 0 := by linarith
    refine ⟨hre0, ?_⟩
    rw [hre0] at hns'; linarith

/-- Quantization Lemma for any Alltop function on `𝔽₂ⁿ` (`n ≥ 2`):
    for every `a ≠ 0` and `x`, there exist integers `m, l` such that
    `2^n * Re(g_a(x)) = 2 * m * √(2^n)`, `2^n * Im(g_a(x)) = 2 * l * √(2^n)`, and `m² + l² = 2^(n-2)`. -/
lemma alltop_quantization {n : ℕ} (hn : 2 ≤ n) {φ : F2 n → ℂ} (h : IsAlltop n φ)
    {a : F2 n} (ha : a ≠ 0) (x : F2 n) :
    ∃ m l : ℤ,
      (2 : ℝ) ^ n * (multDeriv φ a x).re = 2 * (m : ℝ) * Real.sqrt ((2 : ℝ) ^ n) ∧
      (2 : ℝ) ^ n * (multDeriv φ a x).im = 2 * (l : ℝ) * Real.sqrt ((2 : ℝ) ^ n) ∧
      m ^ 2 + l ^ 2 = (2 : ℤ) ^ (n - 2) := by
  let sq2 := Real.sqrt ((2 : ℝ) ^ n)
  have hsq2_pos : 0 < sq2 := Real.sqrt_pos.mpr (by positivity)
  have hsq2_sq : sq2 ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  -- Sign functions on `a^⊥` and its complement
  let sr : F2 n → ℤ := fun b =>
    if 0 ≤ ∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re then 1 else -1
  let st : F2 n → ℤ := fun b =>
    if 0 ≤ ∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im then 1 else -1
  have hhat_r : ∀ b : F2 n,
      (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re) =
        if dot a b = 0 then (sr b : ℝ) * sq2 else 0 := by
    intro b
    rcases zmod2_cases (dot a b) with hd | hd
    · simp only [hd, ↓reduceIte]
      have hsq := ((alltop_wht_re_im h ha b).1 hd).2
      have hpm : (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re) = sq2 ∨
          (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re) = -sq2 := by
        have : ((∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re) - sq2) *
            ((∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).re) + sq2) = 0 := by
          linarith
        rcases mul_eq_zero.mp this with h1 | h2
        · left; linarith
        · right; linarith
      rcases hpm with h1 | h1
      · simp [sr, h1, le_of_lt hsq2_pos]
      · simp [sr, h1, show ¬ (0 ≤ -sq2) by linarith]
    · simp only [hd, one_ne_zero, ↓reduceIte]
      exact ((alltop_wht_re_im h ha b).2 hd).1
  have hhat_t : ∀ b : F2 n,
      (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im) =
        if dot a b = 1 then (st b : ℝ) * sq2 else 0 := by
    intro b
    rcases zmod2_cases (dot a b) with hd | hd
    · simp only [hd, zero_ne_one, ↓reduceIte]
      exact ((alltop_wht_re_im h ha b).1 hd).1
    · simp only [hd, ↓reduceIte]
      have hsq := ((alltop_wht_re_im h ha b).2 hd).2
      have hpm : (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im) = sq2 ∨
          (∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im) = -sq2 := by
        have : ((∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im) - sq2) *
            ((∑ y : F2 n, (chi b y : ℝ) * (multDeriv φ a y).im) + sq2) = 0 := by
          linarith
        rcases mul_eq_zero.mp this with h1 | h2
        · left; linarith
        · right; linarith
      rcases hpm with h1 | h1
      · simp [st, h1, le_of_lt hsq2_pos]
      · simp [st, h1, show ¬ (0 ≤ -sq2) by linarith]
  -- Inverse WHT gives `2^n * r a x = Sr * sq2` and `2^n * t a x = St * sq2`
  let S0 := Finset.univ.filter (fun b : F2 n => dot a b = 0)
  let S1 := Finset.univ.filter (fun b : F2 n => dot a b = 1)
  let Sr : ℤ := ∑ b ∈ S0, chi b x * sr b
  let St : ℤ := ∑ b ∈ S1, chi b x * st b
  have hr_inv : (2 : ℝ) ^ n * (multDeriv φ a x).re = (Sr : ℝ) * sq2 := by
    have hw := wht_inversion (R := ℝ) (fun y => (multDeriv φ a y).re) x
    rw [← hw]
    simp_rw [hhat_r]
    have : (∑ b : F2 n, (chi b x : ℝ) * (if dot a b = 0 then (sr b : ℝ) * sq2 else 0)) =
        (∑ b ∈ S0, ((chi b x * sr b : ℤ) : ℝ)) * sq2 := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [mul_assoc]
    rw [this, ← Int.cast_sum]
  have ht_inv : (2 : ℝ) ^ n * (multDeriv φ a x).im = (St : ℝ) * sq2 := by
    have hw := wht_inversion (R := ℝ) (fun y => (multDeriv φ a y).im) x
    rw [← hw]
    simp_rw [hhat_t]
    have : (∑ b : F2 n, (chi b x : ℝ) * (if dot a b = 1 then (st b : ℝ) * sq2 else 0)) =
        (∑ b ∈ S1, ((chi b x * st b : ℤ) : ℝ)) * sq2 := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [mul_assoc]
    rw [this, ← Int.cast_sum]
  -- Both `S0.card` and `S1.card` are EVEN (since `n ≥ 2` and `a ≠ 0`!)
  have hS1_even : Even S1.card := by
    have htop : 2 ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2 n)) := by
      rw [finrank_top, Module.finrank_fin_fun]; exact hn
    have hev := even_card_dot_one (⊤ : Submodule (ZMod 2) (F2 n)) a htop
    have heq : S1 = Finset.univ.filter (fun b : F2 n => b ∈ (⊤ : Submodule (ZMod 2) (F2 n)) ∧ dot b a = 1) := by
      ext b; simp [S1, dot_comm]
    rw [heq]; exact hev
  have hS0_even : Even S0.card := by
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_filter]; intro b _ h0 h1; rw [h0] at h1; exact zero_ne_one h1
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext b; simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_cases (dot a b)
    have hsum : S0.card + S1.card = 2 ^ n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_pi]
      simp [ZMod.card]
    have hev2n : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    rw [even_iff_two_dvd] at hS1_even hev2n ⊢
    obtain ⟨p, hp⟩ := hev2n
    obtain ⟨q, hq⟩ := hS1_even
    exact ⟨p - q, by omega⟩
  have hSr_even : (2 : ℤ) ∣ Sr := by
    apply Int.dvd_of_emod_eq_zero
    rw [sum_signs_parity S0 (fun b => chi b x * sr b)]
    · obtain ⟨k, hk⟩ := hS0_even; omega
    · intro b _
      rcases chi_eq_one_or_neg_one b x with h1 | h1 <;>
        (simp only [sr]; split_ifs <;> simp [h1])
  have hSt_even : (2 : ℤ) ∣ St := by
    apply Int.dvd_of_emod_eq_zero
    rw [sum_signs_parity S1 (fun b => chi b x * st b)]
    · obtain ⟨k, hk⟩ := hS1_even; omega
    · intro b _
      rcases chi_eq_one_or_neg_one b x with h1 | h1 <;>
        (simp only [st]; split_ifs <;> simp [h1])
  obtain ⟨m, hm⟩ := hSr_even
  obtain ⟨l, hl⟩ := hSt_even
  refine ⟨m, l, ?_, ?_, ?_⟩
  · rw [hr_inv, hm]; push_cast; ring
  · rw [ht_inv, hl]; push_cast; ring
  · -- From `r² + t² = 1`, derive `m² + l² = 2^(n - 2)`!
    have hnorm := multDeriv_normSq h.1 a x
    rw [Complex.normSq_apply] at hnorm
    have hreal : ((2 : ℝ) ^ n * (multDeriv φ a x).re) ^ 2 +
        ((2 : ℝ) ^ n * (multDeriv φ a x).im) ^ 2 = ((2 : ℝ) ^ n) ^ 2 := by
      nlinarith
    rw [hr_inv, ht_inv, hm, hl] at hreal
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hcast : ((4 * (m ^ 2 + l ^ 2) : ℤ) : ℝ) * (2 : ℝ) ^ n = ((2 : ℝ) ^ n) * (2 : ℝ) ^ n := by
      have : (2 * (m : ℝ) * sq2) ^ 2 + (2 * (l : ℝ) * sq2) ^ 2 =
          (4 * ((m : ℝ) ^ 2 + (l : ℝ) ^ 2)) * sq2 ^ 2 := by ring
      rw [hsq2_sq] at this
      push_cast at hreal ⊢
      linarith
    have hreal2 : ((4 * (m ^ 2 + l ^ 2) : ℤ) : ℝ) = ((2 : ℤ) ^ n : ℝ) := by
      have := mul_right_cancel₀ (ne_of_gt h2n_pos) hcast
      simpa using this
    have hint : 4 * (m ^ 2 + l ^ 2) = (2 : ℤ) ^ n := by exact_mod_cast hreal2
    have hpow : (2 : ℤ) ^ n = 4 * (2 : ℤ) ^ (n - 2) := by
      have : n = 2 + (n - 2) := by omega
      conv_lhs => rw [this, pow_add]
      norm_num
    linarith

/-- **Part A (Odd `n = 2k + 1 ≥ 3`)**: No Alltop function exists on `𝔽₂^(2k+1)` (`k ≥ 1`). -/
theorem no_alltop_odd (k : ℕ) (hk : 1 ≤ k) (φ : F2 (2 * k + 1) → ℂ) :
    ¬ IsAlltop (2 * k + 1) φ := by
  intro h
  have hn : 2 ≤ 2 * k + 1 := by omega
  -- Every `g_a(x)` has `Re(g_a(x))² = Im(g_a(x))² = 1/2`!
  have hhalf : ∀ a : F2 (2 * k + 1), a ≠ 0 → ∀ x : F2 (2 * k + 1),
      (multDeriv φ a x).re ^ 2 = (1 / 2 : ℝ) ∧ (multDeriv φ a x).im ^ 2 = (1 / 2 : ℝ) := by
    intro a ha x
    obtain ⟨m, l, hre, him, hsq⟩ := alltop_quantization hn h ha x
    rw [show 2 * k + 1 - 2 = 2 * (k - 1) + 1 by omega] at hsq
    obtain ⟨hm, hl⟩ := sq_add_sq_eq_pow_two_odd (k - 1) hsq
    have hm2 : (m : ℝ) ^ 2 = (2 : ℝ) ^ (2 * (k - 1)) := by
      rcases hm with rfl | rfl
      · push_cast; rw [← pow_mul, mul_comm]
      · push_cast; rw [neg_sq, ← pow_mul, mul_comm]
    have hl2 : (l : ℝ) ^ 2 = (2 : ℝ) ^ (2 * (k - 1)) := by
      rcases hl with rfl | rfl
      · push_cast; rw [← pow_mul, mul_comm]
      · push_cast; rw [neg_sq, ← pow_mul, mul_comm]
    have hsq2 : (Real.sqrt ((2 : ℝ) ^ (2 * k + 1))) ^ 2 = (2 : ℝ) ^ (2 * k + 1) :=
      Real.sq_sqrt (by positivity)
    have hpow : (2 : ℝ) ^ (2 * k + 1) = 8 * (2 : ℝ) ^ (2 * (k - 1)) := by
      have : 2 * k + 1 = 3 + 2 * (k - 1) := by omega
      rw [this, pow_add]; norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 1) := by positivity
    constructor
    · have h1 := congr_arg (· ^ 2) hre
      have h2 : (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).re ^ 2) =
          (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (1 / 2)) := by
        calc (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).re ^ 2)
            = ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).re) ^ 2 := by ring
          _ = (2 * (m : ℝ) * Real.sqrt ((2 : ℝ) ^ (2 * k + 1))) ^ 2 := h1
          _ = 4 * (m : ℝ) ^ 2 * (Real.sqrt ((2 : ℝ) ^ (2 * k + 1))) ^ 2 := by ring
          _ = 4 * (2 : ℝ) ^ (2 * (k - 1)) * (2 : ℝ) ^ (2 * k + 1) := by rw [hm2, hsq2]
          _ = (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (1 / 2)) := by rw [hpow]; ring
      have h3 := mul_left_cancel₀ (ne_of_gt hpos) h2
      exact mul_left_cancel₀ (ne_of_gt hpos) h3
    · have h1 := congr_arg (· ^ 2) him
      have h2 : (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).im ^ 2) =
          (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (1 / 2)) := by
        calc (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).im ^ 2)
            = ((2 : ℝ) ^ (2 * k + 1) * (multDeriv φ a x).im) ^ 2 := by ring
          _ = (2 * (l : ℝ) * Real.sqrt ((2 : ℝ) ^ (2 * k + 1))) ^ 2 := h1
          _ = 4 * (l : ℝ) ^ 2 * (Real.sqrt ((2 : ℝ) ^ (2 * k + 1))) ^ 2 := by ring
          _ = 4 * (2 : ℝ) ^ (2 * (k - 1)) * (2 : ℝ) ^ (2 * k + 1) := by rw [hl2, hsq2]
          _ = (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) * (1 / 2)) := by rw [hpow]; ring
      have h3 := mul_left_cancel₀ (ne_of_gt hpos) h2
      exact mul_left_cancel₀ (ne_of_gt hpos) h3
  -- Triangle contradiction with `a = eVec 0`, `b = eVec 1`!
  let i0 : Fin (2 * k + 1) := ⟨0, by omega⟩
  let i1 : Fin (2 * k + 1) := ⟨1, by omega⟩
  let a : F2 (2 * k + 1) := eVec i0
  let b : F2 (2 * k + 1) := eVec i1
  have ha0 : a ≠ 0 := fun hc => by
    have := congr_fun hc i0; simp [a, eVec] at this
  have hb0 : b ≠ 0 := fun hc => by
    have := congr_fun hc i1; simp [b, eVec] at this
  have hab0 : a + b ≠ 0 := fun hc => by
    have := congr_fun hc i0
    have hne : i0 ≠ i1 := by simp [i0, i1]
    simp [a, b, eVec, hne] at this
  -- Triangle identity: `g_a(0) * g_{a+b}(a) = g_b(0)`
  have htri : multDeriv φ a 0 * multDeriv φ (a + b) a = multDeriv φ b 0 := by
    simp only [multDeriv, zero_add, f2_add_cancel_left]
    have h1 : φ a * star (φ a) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, h.1 a]; simp
    calc star (φ 0) * φ a * (star (φ a) * φ b)
        = star (φ 0) * (φ a * star (φ a)) * φ b := by ring
      _ = star (φ 0) * φ b := by rw [h1, mul_one]
  obtain ⟨hr1, hi1⟩ := hhalf a ha0 0
  obtain ⟨hr2, hi2⟩ := hhalf (a + b) hab0 a
  obtain ⟨hr3, hi3⟩ := hhalf b hb0 0
  have hprod_re : (multDeriv φ b 0).re =
      (multDeriv φ a 0).re * (multDeriv φ (a + b) a).re -
      (multDeriv φ a 0).im * (multDeriv φ (a + b) a).im := by
    rw [← htri]; simp [Complex.mul_re]
  have hprod_im : (multDeriv φ b 0).im =
      (multDeriv φ a 0).re * (multDeriv φ (a + b) a).im +
      (multDeriv φ a 0).im * (multDeriv φ (a + b) a).re := by
    rw [← htri]; simp [Complex.mul_im]
  have hzero : (multDeriv φ b 0).re * (multDeriv φ b 0).im = 0 := by
    calc (multDeriv φ b 0).re * (multDeriv φ b 0).im
        = (multDeriv φ a 0).re * (multDeriv φ a 0).im *
            ((multDeriv φ (a + b) a).re ^ 2 - (multDeriv φ (a + b) a).im ^ 2) +
          (multDeriv φ (a + b) a).re * (multDeriv φ (a + b) a).im *
            ((multDeriv φ a 0).re ^ 2 - (multDeriv φ a 0).im ^ 2) := by
          rw [hprod_re, hprod_im]; ring
      _ = 0 := by rw [hr1, hi1, hr2, hi2]; ring
  have hpos : (multDeriv φ b 0).re ^ 2 * (multDeriv φ b 0).im ^ 2 = (1 / 4 : ℝ) := by
    rw [hr3, hi3]; norm_num
  nlinarith

/-- **Part B (Even `n = 2k ≥ 4`)**: No Alltop function exists on `𝔽₂^(2k)` (`k ≥ 2`). -/
theorem no_alltop_even (k : ℕ) (hk : 2 ≤ k) (φ : F2 (2 * k) → ℂ) :
    ¬ IsAlltop (2 * k) φ := by
  intro hφ
  have hn : 2 ≤ 2 * k := by omega
  -- Normalize `φ` so `φ₀ 0 = 1`
  let φ₀ : F2 (2 * k) → ℂ := fun x => star (φ 0) * φ x
  have hφ₀ : IsAlltop (2 * k) φ₀ :=
    isAlltop_smul hφ (by rw [Complex.star_def, Complex.normSq_conj]; exact hφ.1 0)
  have hφ₀_zero : φ₀ 0 = 1 := by
    simp only [φ₀]; rw [mul_comm, Complex.star_def, Complex.mul_conj, hφ.1 0]; simp
  -- Step 1: Every `multDeriv φ₀ a x` (`a ≠ 0`) lies in `{1, -1, I, -I}`!
  have hquant : ∀ a : F2 (2 * k), a ≠ 0 → ∀ x : F2 (2 * k),
      multDeriv φ₀ a x = 1 ∨ multDeriv φ₀ a x = -1 ∨
      multDeriv φ₀ a x = Complex.I ∨ multDeriv φ₀ a x = -Complex.I := by
    intro a ha x
    obtain ⟨m, l, hre, him, hsq⟩ := alltop_quantization hn hφ₀ ha x
    rw [show 2 * k - 2 = 2 * (k - 1) by omega] at hsq
    have hsq2 : Real.sqrt ((2 : ℝ) ^ (2 * k)) = (2 : ℝ) ^ k := by
      rw [show (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 by rw [← pow_mul, mul_comm]]
      exact Real.sqrt_sq (by positivity)
    rw [hsq2] at hre him
    have hpow2 : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
      rw [← pow_add, ← two_mul]
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2_km1 : 2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
      rw [← pow_succ', show k - 1 + 1 = k by omega]
    rcases sq_add_sq_eq_pow_two_even (k - 1) hsq with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; apply Complex.ext
      · push_cast at hre; rw [hpow2] at hre
        have : (2 : ℝ) ^ k * (multDeriv φ₀ a x).re = (2 : ℝ) ^ k * 1 := by nlinarith
        exact mul_left_cancel₀ (ne_of_gt h2k_pos) this
      · simpa using him
    · right; left; apply Complex.ext
      · push_cast at hre; rw [hpow2] at hre
        have : (2 : ℝ) ^ k * (multDeriv φ₀ a x).re = (2 : ℝ) ^ k * (-1) := by nlinarith
        exact mul_left_cancel₀ (ne_of_gt h2k_pos) this
      · simpa using him
    · right; right; left; apply Complex.ext
      · simpa using hre
      · push_cast at him; rw [hpow2] at him
        have : (2 : ℝ) ^ k * (multDeriv φ₀ a x).im = (2 : ℝ) ^ k * 1 := by nlinarith
        exact mul_left_cancel₀ (ne_of_gt h2k_pos) this
    · right; right; right; apply Complex.ext
      · simpa using hre
      · push_cast at him; rw [hpow2] at him
        have : (2 : ℝ) ^ k * (multDeriv φ₀ a x).im = (2 : ℝ) ^ k * (-1) := by nlinarith
        exact mul_left_cancel₀ (ne_of_gt h2k_pos) this
  -- Lift `φ₀` to `ψ : F2 (2*k) → GI` taking values in `{1, -1, giI, -giI}`!
  have hφ₀_vals : ∀ x : F2 (2 * k),
      ∃ g : GI, (g = 1 ∨ g = -1 ∨ g = giI ∨ g = -giI) ∧ giToComplex g = φ₀ x := by
    intro x
    by_cases hx : x = 0
    · subst hx; exact ⟨1, Or.inl rfl, by simp [hφ₀_zero]⟩
    · have hgx : multDeriv φ₀ x 0 = φ₀ x := by simp [multDeriv, hφ₀_zero]
      rcases hquant x hx 0 with h1 | h1 | h1 | h1 <;> rw [hgx] at h1
      · exact ⟨1, Or.inl rfl, by simp [h1]⟩
      · exact ⟨-1, Or.inr (Or.inl rfl), by simp [h1]⟩
      · exact ⟨giI, Or.inr (Or.inr (Or.inl rfl)), by simp [h1]⟩
      · exact ⟨-giI, Or.inr (Or.inr (Or.inr rfl)), by simp [h1]⟩
  choose ψ hψ_vals hψ_eq using hφ₀_vals
  -- Step 2: Sign functions `σ_r, σ_t : F2 (2*k) → F2 (2*k) → ℤ` for the WHT of `g_a` in `GI`!
  let gHat : F2 (2 * k) → F2 (2 * k) → GI :=
    fun a b => ∑ x : F2 (2 * k), (chi b x : GI) * star (ψ x) * ψ (x + a)
  have hgHat_cast : ∀ a b, giToComplex (gHat a b) =
      ∑ x : F2 (2 * k), (chi b x : ℂ) * multDeriv φ₀ a x := by
    intro a b
    simp only [gHat, map_sum, map_mul, map_intCast, giToComplex_star, hψ_eq, multDeriv, mul_assoc]
  have hgHat_zero : ∀ b, gHat 0 b = if b = 0 then (2 : GI) ^ (2 * k) else 0 := by
    intro b
    have hnorm1 : ∀ x, star (ψ x) * ψ x = 1 := fun x => by
      rcases hψ_vals x with h | h | h | h <;> rw [h] <;> ext <;> simp [giI]
    simp only [gHat, add_zero]
    have : (∑ x : F2 (2 * k), (chi b x : GI) * star (ψ x) * ψ x) =
        ((∑ x : F2 (2 * k), chi x b : ℤ) : GI) := by
      rw [Int.cast_sum]
      refine Finset.sum_congr rfl fun x _ => by rw [mul_assoc, hnorm1, mul_one, chi_comm]
    rw [this, sum_chi]
    split_ifs <;> simp
  have hgHat_nz : ∀ a : F2 (2 * k), a ≠ 0 → ∀ b : F2 (2 * k),
      (dot a b = 0 → ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ gHat a b = (s : GI) * (2 : GI) ^ k) ∧
      (dot a b = 1 → ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ gHat a b = (s : GI) * (2 : GI) ^ k * giI) := by
    intro a ha b
    have hcast := hgHat_cast a b
    have hre_c : (giToComplex (gHat a b)).re = ((gHat a b).re : ℝ) := by simp [giToComplex]
    have him_c : (giToComplex (gHat a b)).im = ((gHat a b).im : ℝ) := by simp [giToComplex]
    have hsum_re : (∑ x : F2 (2 * k), (chi b x : ℂ) * multDeriv φ₀ a x).re =
        ∑ x : F2 (2 * k), (chi b x : ℝ) * (multDeriv φ₀ a x).re := by simp [Complex.re_sum]
    have hsum_im : (∑ x : F2 (2 * k), (chi b x : ℂ) * multDeriv φ₀ a x).im =
        ∑ x : F2 (2 * k), (chi b x : ℝ) * (multDeriv φ₀ a x).im := by simp [Complex.im_sum]
    constructor
    · intro hd
      obtain ⟨him0, hre2⟩ := (alltop_wht_re_im hφ₀ ha b).1 hd
      have him_g : (gHat a b).im = 0 := by
        have : ((gHat a b).im : ℝ) = 0 := by rw [← him_c, hcast, hsum_im, him0]
        exact_mod_cast this
      have hre_g2 : (gHat a b).re ^ 2 = ((2 : ℤ) ^ k) ^ 2 := by
        have : ((gHat a b).re : ℝ) ^ 2 = ((2 : ℝ) ^ k) ^ 2 := by
          rw [← hre_c, hcast, hsum_re, hre2, ← pow_mul, mul_comm]
        exact_mod_cast this
      have hpm : (gHat a b).re = (2 : ℤ) ^ k ∨ (gHat a b).re = -((2 : ℤ) ^ k) :=
        sq_eq_sq_iff_eq_or_eq_neg.mp hre_g2
      rcases hpm with hr | hr
      · refine ⟨1, Or.inl rfl, ?_⟩
        ext <;> simp [gi_two_pow_eq_mk, hr, him_g]
      · refine ⟨-1, Or.inr rfl, ?_⟩
        ext <;> simp [gi_two_pow_eq_mk, hr, him_g]
    · intro hd
      obtain ⟨hre0, him2⟩ := (alltop_wht_re_im hφ₀ ha b).2 hd
      have hre_g : (gHat a b).re = 0 := by
        have : ((gHat a b).re : ℝ) = 0 := by rw [← hre_c, hcast, hsum_re, hre0]
        exact_mod_cast this
      have him_g2 : (gHat a b).im ^ 2 = ((2 : ℤ) ^ k) ^ 2 := by
        have : ((gHat a b).im : ℝ) ^ 2 = ((2 : ℝ) ^ k) ^ 2 := by
          rw [← him_c, hcast, hsum_im, him2, ← pow_mul, mul_comm]
        exact_mod_cast this
      have hpm : (gHat a b).im = (2 : ℤ) ^ k ∨ (gHat a b).im = -((2 : ℤ) ^ k) :=
        sq_eq_sq_iff_eq_or_eq_neg.mp him_g2
      rcases hpm with hi | hi
      · refine ⟨1, Or.inl rfl, ?_⟩
        ext <;> simp [gi_two_pow_eq_mk, giI, hre_g, hi]
      · refine ⟨-1, Or.inr rfl, ?_⟩
        ext <;> simp [gi_two_pow_eq_mk, giI, hre_g, hi]
  -- Pick sign functions `σr`, `σt` globally!
  have hsr_ex : ∀ a b : F2 (2 * k), ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (a ≠ 0 → dot a b = 0 → gHat a b = (s : GI) * (2 : GI) ^ k) := fun a b => by
    by_cases ha : a ≠ 0
    · by_cases hd : dot a b = 0
      · obtain ⟨s, hs, hEq⟩ := (hgHat_nz a ha b).1 hd
        exact ⟨s, hs, fun _ _ => hEq⟩
      · exact ⟨1, Or.inl rfl, fun _ hc => absurd hc hd⟩
    · exact ⟨1, Or.inl rfl, fun hc _ => absurd hc ha⟩
  have hst_ex : ∀ a b : F2 (2 * k), ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (a ≠ 0 → dot a b = 1 → gHat a b = (s : GI) * (2 : GI) ^ k * giI) := fun a b => by
    by_cases ha : a ≠ 0
    · by_cases hd : dot a b = 1
      · obtain ⟨s, hs, hEq⟩ := (hgHat_nz a ha b).2 hd
        exact ⟨s, hs, fun _ _ => hEq⟩
      · exact ⟨1, Or.inl rfl, fun _ hc => absurd hc hd⟩
    · exact ⟨1, Or.inl rfl, fun hc _ => absurd hc ha⟩
  choose σr hσr_pm hσr_eq using hsr_ex
  choose σt hσt_pm hσt_eq using hst_ex
  -- Step 3: Walsh transform `z u = ∑ x, χ(u, x) ψ(x)` and convolution identity!
  let z : F2 (2 * k) → GI := fun u => ∑ x : F2 (2 * k), (chi u x : GI) * ψ x
  have hconv : ∀ u b : F2 (2 * k),
      star (z (u + b)) * z u = ∑ a : F2 (2 * k), (chi u a : GI) * gHat a b := by
    intro u b
    calc star (z (u + b)) * z u
        = (∑ x : F2 (2 * k), (chi (u + b) x : GI) * star (ψ x)) *
          (∑ y : F2 (2 * k), (chi u y : GI) * ψ y) := by
          simp only [z, star_sum, star_mul]
          congr 1; refine Finset.sum_congr rfl fun x _ => ?_
          have hc : star (chi (u + b) x : GI) = (chi (u + b) x : GI) := by
            ext <;> simp
          rw [hc, mul_comm]
      _ = ∑ x : F2 (2 * k), ∑ y : F2 (2 * k),
            (chi u (x + y) : GI) * (chi b x : GI) * star (ψ x) * ψ y := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [chi_add_left, chi_add_right]
          push_cast; ring
      _ = ∑ x : F2 (2 * k), ∑ a : F2 (2 * k),
            (chi u a : GI) * ((chi b x : GI) * star (ψ x) * ψ (x + a)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => ?_
          change (chi u (x + y) : GI) * (chi b x : GI) * star (ψ x) * ψ y =
            (chi u (x + y) : GI) * ((chi b x : GI) * star (ψ x) * ψ (x + (x + y)))
          rw [f2_add_cancel_left]
          ring
      _ = ∑ a : F2 (2 * k), (chi u a : GI) * gHat a b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum]
  -- Extract `w : F2 (2*k) → GI` with `z u = giPi ^ k * w u`!
  have hz_div : ∀ u : F2 (2 * k), giPi ^ k ∣ z u := by
    intro u
    apply pow_giPi_dvd_of_pow_two_dvd_norm k
    have hc0 := hconv u 0
    rw [add_zero, gi_mul_star] at hc0
    have hsum0 : (∑ a : F2 (2 * k), (chi u a : GI) * gHat a 0) =
        (2 : GI) ^ k * ((2 : GI) ^ k + ∑ a ∈ Finset.univ.erase (0 : F2 (2 * k)),
          (chi u a * σr a 0 : GI)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 (2 * k))),
        chi_zero_right, Int.cast_one, one_mul, hgHat_zero 0]
      simp only [↓reduceIte]
      rw [mul_add, Finset.mul_sum, ← pow_add, ← two_mul]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
      rw [hσr_eq a 0 hne (dot_zero_right a)]
      ring
    rw [hsum0] at hc0
    have hre := congr_arg Zsqrtd.re hc0
    have h2k_re : ((2 : GI) ^ k).re = (2 : ℤ) ^ k := by rw [gi_two_pow_eq_mk]
    have h2k_im : ((2 : GI) ^ k).im = 0 := by rw [gi_two_pow_eq_mk]
    refine ⟨((2 : GI) ^ k + ∑ a ∈ Finset.univ.erase (0 : F2 (2 * k)),
        (chi u a * σr a 0 : GI)).re, ?_⟩
    simpa [h2k_re, h2k_im] using hre
  choose w hw_eq using hz_div
  -- Convolution for `w`!
  have hpi_mul : star (giPi ^ k) * giPi ^ k = (2 : GI) ^ k := by
    rw [gi_mul_star, gi_norm_pow_pi, gi_two_pow_eq_mk]
    ext
    · exact Zsqrtd.re_intCast _
    · exact Zsqrtd.im_intCast _
  have h2k_ne : (2 : GI) ^ k ≠ 0 := by
    intro hc
    have := congr_arg Zsqrtd.re hc
    rw [gi_two_pow_eq_mk] at this
    exact pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0) this
  have hw_conv_zero : ∀ u : F2 (2 * k),
      star (w u) * w u = (2 : GI) ^ k +
        ∑ a ∈ Finset.univ.erase (0 : F2 (2 * k)), ((chi u a * σr a 0 : ℤ) : GI) := by
    intro u
    apply mul_left_cancel₀ h2k_ne
    have hc0 := hconv u 0
    rw [add_zero, hw_eq u, star_mul] at hc0
    have hlhs : (2 : GI) ^ k * (star (w u) * w u) = star (w u) * star (giPi ^ k) * (giPi ^ k * w u) := by
      calc (2 : GI) ^ k * (star (w u) * w u)
          = (star (giPi ^ k) * giPi ^ k) * (star (w u) * w u) := by rw [hpi_mul]
        _ = star (w u) * star (giPi ^ k) * (giPi ^ k * w u) := by ring
    rw [hlhs, hc0, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 (2 * k))),
      chi_zero_right, Int.cast_one, one_mul, hgHat_zero 0]
    simp only [↓reduceIte]
    rw [mul_add, Finset.mul_sum, ← pow_add, ← two_mul]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hσr_eq a 0 (Finset.mem_erase.mp ha).1 (dot_zero_right a)]
    push_cast; ring
  have hw_conv_nz : ∀ u b : F2 (2 * k), b ≠ 0 →
      star (w (u + b)) * w u =
        ((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a b = 0),
            chi u a * σr a b : ℤ) : GI) +
        ((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => dot a b = 1),
            chi u a * σt a b : ℤ) : GI) * giI := by
    intro u b hb
    apply mul_left_cancel₀ h2k_ne
    have hcb := hconv u b
    rw [hw_eq (u + b), hw_eq u, star_mul] at hcb
    have hlhs : (2 : GI) ^ k * (star (w (u + b)) * w u) =
        star (w (u + b)) * star (giPi ^ k) * (giPi ^ k * w u) := by
      calc (2 : GI) ^ k * (star (w (u + b)) * w u)
          = (star (giPi ^ k) * giPi ^ k) * (star (w (u + b)) * w u) := by rw [hpi_mul]
        _ = star (w (u + b)) * star (giPi ^ k) * (giPi ^ k * w u) := by ring
    rw [hlhs, hcb]
    -- Partition `a : F2 (2*k)` into `{a = 0}`, `{a ≠ 0 ∧ dot a b = 0}`, `{dot a b = 1}`
    have hpart : (∑ a : F2 (2 * k), (chi u a : GI) * gHat a b) =
        (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a b = 0),
          (2 : GI) ^ k * ((chi u a * σr a b : ℤ) : GI)) +
        (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => dot a b = 1),
          (2 : GI) ^ k * ((chi u a * σt a b : ℤ) : GI) * giI) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : F2 (2 * k) => dot a b = 1)]
      rw [add_comm]
      congr 1
      · -- `¬ dot a b = 1` means `dot a b = 0`; drop `a = 0` since `gHat 0 b = 0`!
        rw [← Finset.add_sum_erase _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, by simp [dot_zero_left]⟩)]
        simp only [hgHat_zero b, hb, ↓reduceIte, mul_zero, zero_add]
        have hfilt : (Finset.univ.filter (fun a : F2 (2 * k) => ¬ dot a b = 1)).erase 0 =
            Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a b = 0) := by
          ext a; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hne, hnd⟩
            rcases zmod2_cases (dot a b) with h | h
            · exact ⟨hne, h⟩
            · exact absurd h hnd
          · rintro ⟨hne, hd⟩; exact ⟨hne, by rw [hd]; exact zero_ne_one⟩
        rw [hfilt]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ⟨hne, hd⟩ := (Finset.mem_filter.mp ha).2
        rw [hσr_eq a b hne hd]; push_cast; ring
      · refine Finset.sum_congr rfl fun a ha => ?_
        have hd : dot a b = 1 := (Finset.mem_filter.mp ha).2
        have hne : a ≠ 0 := fun hc => by rw [hc, dot_zero_left] at hd; exact zero_ne_one hd
        rw [hσt_eq a b hne hd]; push_cast; ring
    rw [hpart, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Int.cast_sum, ← Int.cast_sum]
    ring
  -- Step 4: Parity alignment! Every `w u` has odd norm, and for `b ≠ 0`, `Re(w_{u+b}^* w_u)` is odd, `Im` is even!
  have hw_odd_norm : ∀ u : F2 (2 * k), Odd (w u).norm := by
    intro u
    have h0 := congr_arg Zsqrtd.re (hw_conv_zero u)
    rw [gi_mul_star] at h0
    have hre_norm : ((w u).norm : GI).re = (w u).norm := by simp
    have h2k_re : ((2 : GI) ^ k).re = (2 : ℤ) ^ k := by rw [gi_two_pow_eq_mk]
    rw [hre_norm, Zsqrtd.re_add, h2k_re] at h0
    have hsum_re : (∑ a ∈ Finset.univ.erase (0 : F2 (2 * k)), ((chi u a * σr a 0 : ℤ) : GI)).re =
        ∑ a ∈ Finset.univ.erase (0 : F2 (2 * k)), chi u a * σr a 0 := by
      rw [← Int.cast_sum, Zsqrtd.re_intCast]
    rw [hsum_re] at h0
    have hpar := sum_signs_parity (Finset.univ.erase (0 : F2 (2 * k))) (fun a => chi u a * σr a 0)
      (fun a _ => by
        rcases chi_eq_one_or_neg_one u a with h1 | h1 <;> rcases hσr_pm a 0 with h2 | h2 <;>
          simp [h1, h2])
    have hcard : (Finset.univ.erase (0 : F2 (2 * k))).card = 2 ^ (2 * k) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
      simp [ZMod.card]
    have h2k_even : (2 : ℤ) ^ k % 2 = 0 := Int.emod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    have h22k_even : (2 : ℕ) ∣ 2 ^ (2 * k) := dvd_pow_self 2 (by omega)
    have h22k_pos : 1 ≤ 2 ^ (2 * k) := Nat.one_le_pow _ _ (by norm_num)
    have hcard_odd : ((Finset.univ.erase (0 : F2 (2 * k))).card : ℤ) % 2 = 1 := by
      rw [hcard]; obtain ⟨q, hq⟩ := h22k_even; omega
    have hmod1 : (w u).norm % 2 = 1 := by omega
    exact Int.odd_iff.mpr hmod1
  have hw_same_par : ∀ u v : F2 (2 * k), (w u).re % 2 = (w v).re % 2 := by
    intro u v
    by_cases huv : u = v
    · rw [huv]
    · have hb : u + v ≠ 0 := fun hc => huv (by
        have := congr_arg (u + ·) hc
        simpa [f2_add_cancel_left] using this.symm)
      have hcb := hw_conv_nz u (u + v) hb
      rw [f2_add_cancel_left] at hcb
      have hre := congr_arg Zsqrtd.re hcb
      have htop : 2 ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (F2 (2 * k))) := by
        rw [finrank_top, Module.finrank_fin_fun]; omega
      have hodd_card := odd_card_nonzero_dot_zero (⊤ : Submodule (ZMod 2) (F2 (2 * k))) (u + v) htop
      have hfilt_eq : Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a (u + v) = 0) =
          Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ (⊤ : Submodule (ZMod 2) (F2 (2 * k))) ∧ dot a (u + v) = 0) := by
        ext a; simp
      have hpar := sum_signs_parity
        (Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a (u + v) = 0))
        (fun a => chi u a * σr a (u + v))
        (fun a _ => by
          rcases chi_eq_one_or_neg_one u a with h1 | h1 <;> rcases hσr_pm a (u + v) with h2 | h2 <;>
            simp [h1, h2])
      rw [hfilt_eq] at hpar
      have hre_odd : (star (w v) * w u).re % 2 = 1 := by
        have h1 : (star (w v) * w u).re =
            ∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a (u + v) = 0),
              chi u a * σr a (u + v) := by
          have hz : (((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => dot a (u + v) = 1),
              chi u a * σt a (u + v) : ℤ) : GI) * giI).re = 0 := by
            rw [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; simp [giI]
          rw [Zsqrtd.re_add, Zsqrtd.re_intCast, hz, add_zero] at hre
          exact hre
        rw [h1, hfilt_eq, hpar]
        obtain ⟨q, hq⟩ := hodd_card
        omega
      -- Use `(star (w v) * w u).re = (w v).re * (w u).re + (w v).im * (w u).im` and odd norms!
      have hnv := hw_odd_norm v
      have hnu := hw_odd_norm u
      rw [gi_norm_eq] at hnv hnu
      rw [Int.odd_iff] at hnv hnu
      have hre_exp : (star (w v) * w u).re = (w v).re * (w u).re + (w v).im * (w u).im := by
        simp
      rw [hre_exp] at hre_odd
      have hvr : (w v).re % 2 = 0 ∨ (w v).re % 2 = 1 := by omega
      have hvi : (w v).im % 2 = 0 ∨ (w v).im % 2 = 1 := by omega
      have hur : (w u).re % 2 = 0 ∨ (w u).re % 2 = 1 := by omega
      have hui : (w u).im % 2 = 0 ∨ (w u).im % 2 = 1 := by omega
      -- Eliminate impossible parity combos cleanly via mod-2 arithmetic
      have sq_mod : ∀ a : ℤ, (a ^ 2) % 2 = a % 2 := fun a => by
        rw [sq, Int.mul_emod]
        rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with h | h <;> simp [h]
      have mul_mod : ∀ a b : ℤ, (a * b) % 2 = (a % 2) * (b % 2) := fun a b => by
        rw [Int.mul_emod]
        rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with ha | ha <;>
        rcases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with hb | hb <;>
        simp [ha, hb]
      have hv_par : ((w v).re % 2 + (w v).im % 2) % 2 = 1 := by
        have := sq_mod (w v).re; have := sq_mod (w v).im; omega
      have hu_par : ((w u).re % 2 + (w u).im % 2) % 2 = 1 := by
        have := sq_mod (w u).re; have := sq_mod (w u).im; omega
      have hprod_par : (((w v).re % 2) * ((w u).re % 2) + ((w v).im % 2) * ((w u).im % 2)) % 2 = 1 := by
        have := mul_mod (w v).re (w u).re; have := mul_mod (w v).im (w u).im; omega
      rcases hvr with h1 | h1 <;> rcases hvi with h2 | h2 <;>
        rcases hur with h3 | h3 <;> rcases hui with h4 | h4 <;>
        simp [h1, h2, h3, h4] at hv_par hu_par hprod_par ⊢
  -- Rotate by `u_rot ∈ {1, -giI}` so ALL `w' u` have `re % 2 = 1` and `im % 2 = 0`!
  let urot : GI := if (w 0).re % 2 = 1 then 1 else -giI
  have hurot_star : star urot * urot = 1 := by
    simp only [urot]; split_ifs <;> ext <;> simp [giI]
  let ψ' : F2 (2 * k) → GI := fun x => urot * ψ x
  let w' : F2 (2 * k) → GI := fun u => urot * w u
  have hψ'_vals : ∀ x, ψ' x = 1 ∨ ψ' x = -1 ∨ ψ' x = giI ∨ ψ' x = -giI := fun x => by
    simp only [ψ', urot]
    split_ifs
    · simpa using hψ_vals x
    · rcases hψ_vals x with h | h | h | h <;> rw [h]
      · right; right; right; simp
      · right; right; left; simp
      · left; ext <;> simp [giI]
      · right; left; ext <;> simp [giI]
  have hw'_par : ∀ u : F2 (2 * k), (w' u).re % 2 = 1 ∧ (w' u).im % 2 = 0 := by
    intro u
    have hnu := hw_odd_norm u
    rw [gi_norm_eq, Int.odd_iff] at hnu
    have hsq : ∀ a : ℤ, (a ^ 2) % 2 = a % 2 := fun a => by
      rw [sq, Int.mul_emod]
      rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with h | h <;> simp [h]
    have hsum_p : ((w u).re % 2 + (w u).im % 2) % 2 = 1 := by
      have := hsq (w u).re; have := hsq (w u).im; omega
    have hsame := hw_same_par u 0
    simp only [w', urot]
    split_ifs with h0
    · simp only [one_mul]; omega
    · have hre0 : (w 0).re % 2 = 0 := by omega
      have hreu : (w u).re % 2 = 0 := by omega
      have himu : (w u).im % 2 = 1 := by omega
      have h1 : (-giI * w u).re = (w u).im := by simp [giI]
      have h2 : (-giI * w u).im = -(w u).re := by simp [giI]
      rw [h1, h2]; omega
  -- Define `η u` so `w' u = 1 + 2 * η u`!
  let η : F2 (2 * k) → GI := fun u => ⟨((w' u).re - 1) / 2, (w' u).im / 2⟩
  have hw'_eta : ∀ u, w' u = 1 + 2 * η u := fun u => by
    have ⟨hr, hi⟩ := hw'_par u
    ext
    · simp [η]; omega
    · simp [η]; omega
  -- Step 5: Verify `CorrCongr η r` for all `1 ≤ r ≤ 2*k - 2`!
  have hCorr : ∀ r : ℕ, 1 ≤ r → r ≤ 2 * k - 2 → CorrCongr η r := by
    intro r hr1 hrle U hU v₀ b
    -- First show `((2 : GI) ^ (r + 1)) ∣ (∑ u : U, star (w' (v₀ + u.1)) * w' (v₀ + u.1 + b)) - (2 : GI) ^ r`!
    -- Since `star (w' x) * w' y = star (w x) * w y` (as `star urot * urot = 1`), take conjugates!
    have hw'_prod : ∀ x y : F2 (2 * k), star (w' x) * w' y = star (w x) * w y := fun x y => by
      simp only [w', star_mul]
      calc star (w x) * star urot * (urot * w y)
          = star (w x) * (star urot * urot) * w y := by ring
        _ = star (w x) * w y := by rw [hurot_star, mul_one]
    have hcardU : (Fintype.card U : ℤ) = (2 : ℤ) ^ r := by
      rw [card_submodule_f2, hU]; norm_cast
    have horth_dim : 2 ≤ Module.finrank (ZMod 2) (orth U) := by
      have := finrank_orth_ge U; omega
    have hw_sub : ((2 : GI) ^ (r + 1)) ∣
        (∑ u : U, star (w' (v₀ + u.1)) * w' (v₀ + u.1 + b)) - (2 : GI) ^ r := by
      -- Work on the conjugate `∑ u : U, star (w (v₀ + u.1 + b)) * w (v₀ + u.1)`!
      have hconj_dvd : ∀ z : GI, ((2 : GI) ^ (r + 1)) ∣ star z → ((2 : GI) ^ (r + 1)) ∣ z := by
        intro z hz; rw [pow_two_dvd_gi_iff] at hz ⊢
        exact ⟨hz.1, by simpa using dvd_neg.mp hz.2⟩
      apply hconj_dvd
      have hstar_sum : star ((∑ u : U, star (w' (v₀ + u.1)) * w' (v₀ + u.1 + b)) - (2 : GI) ^ r) =
          (∑ u : U, star (w (v₀ + u.1 + b)) * w (v₀ + u.1)) - (2 : GI) ^ r := by
        rw [star_sub, star_sum]
        have h2r : star ((2 : GI) ^ r) = (2 : GI) ^ r := by rw [gi_two_pow_eq_mk]; ext <;> simp
        rw [h2r]
        congr 1; refine Finset.sum_congr rfl fun u _ => ?_
        rw [hw'_prod, star_mul, star_star]
      rw [hstar_sum, pow_two_dvd_gi_iff]
      by_cases hb : b = 0
      · subst hb
        simp only [add_zero]
        have hsum0 : (∑ u : U, star (w (v₀ + u.1)) * w (v₀ + u.1)) =
            (2 : GI) ^ (r + k) +
            (2 : GI) ^ r * ((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U),
              chi v₀ a * σr a 0 : ℤ) : GI) := by
          simp_rw [hw_conv_zero, Finset.sum_add_distrib]
          congr 1
          · simp [Finset.sum_const, nsmul_eq_mul, card_submodule_f2, hU, pow_add]
          · rw [Finset.sum_comm, Int.cast_sum, Finset.mul_sum]
            have hinner : ∀ a ∈ Finset.univ.erase (0 : F2 (2 * k)),
                (∑ u : U, ((chi (v₀ + u.1) a * σr a 0 : ℤ) : GI)) =
                  if a ∈ orth U then (2 : GI) ^ r * ((chi v₀ a * σr a 0 : ℤ) : GI) else 0 := by
              intro a _
              rw [← Int.cast_sum, ← Finset.sum_mul, sum_chi_affine, hcardU]
              split_ifs
              · push_cast; rw [gi_two_pow_eq_mk]; ext
                · simp; ring
                · simp
              · simp
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
            have hfeq : (Finset.univ.erase (0 : F2 (2 * k))).filter (fun a => a ∈ orth U) =
                Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U) := by
              ext a; simp
            rw [hfeq]
        rw [hsum0]
        -- Real part: `2^(r+k) + 2^r * (ODD) - 2^r` divisible by `2^(r+1)`; Imag part = 0!
        have hodd := odd_card_nonzero_dot_zero (orth U) 0 horth_dim
        have hfeq0 : Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U) =
            Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a 0 = 0) := by
          ext a; simp [dot_zero_right]
        rw [← hfeq0] at hodd
        have hpar := sum_signs_parity
          (Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U))
          (fun a => chi v₀ a * σr a 0)
          (fun a _ => by
            rcases chi_eq_one_or_neg_one v₀ a with h1 | h1 <;> rcases hσr_pm a 0 with h2 | h2 <;>
              simp [h1, h2])
        obtain ⟨q, hq⟩ := hodd
        have hodd_sum : (2 : ℤ) ∣ (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U),
            chi v₀ a * σr a 0) - 1 := by
          apply Int.dvd_of_emod_eq_zero; omega
        obtain ⟨t, ht⟩ := hodd_sum
        have h2re : ∀ m : ℕ, ((2 : GI) ^ m).re = (2 : ℤ) ^ m := fun m => by rw [gi_two_pow_eq_mk]
        have h2im : ∀ m : ℕ, ((2 : GI) ^ m).im = 0 := fun m => by rw [gi_two_pow_eq_mk]
        have hre_mi : ∀ (m : ℕ) (x : ℤ), ((2 : GI) ^ m * (x : GI)).re = (2 : ℤ) ^ m * x := fun m x => by
          rw [Zsqrtd.re_mul, h2re, h2im, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring
        have him_mi : ∀ (m : ℕ) (x : ℤ), ((2 : GI) ^ m * (x : GI)).im = 0 := fun m x => by
          rw [Zsqrtd.im_mul, h2re, h2im, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring
        constructor
        · simp only [Zsqrtd.re_sub, Zsqrtd.re_add, hre_mi, h2re]
          refine ⟨(2 : ℤ) ^ (k - 1) + t, ?_⟩
          have hpow1 : (2 : ℤ) ^ (r + k) = (2 : ℤ) ^ (r + 1) * (2 : ℤ) ^ (k - 1) := by
            rw [← pow_add, show r + 1 + (k - 1) = r + k by omega]
          have hpow2 : (2 : ℤ) ^ (r + 1) = (2 : ℤ) ^ r * 2 := by rw [pow_succ]
          have hsum_eq : (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U),
              chi v₀ a * σr a 0) = 2 * t + 1 := by linarith
          rw [hsum_eq, hpow1, hpow2]; ring
        · simp only [Zsqrtd.im_sub, Zsqrtd.im_add, him_mi, h2im, add_zero, sub_zero]
          exact dvd_zero _
      · -- `b ≠ 0`!
        have hsum_b : (∑ u : U, star (w (v₀ + u.1 + b)) * w (v₀ + u.1)) =
            (2 : GI) ^ r * ((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a b = 0),
              chi v₀ a * σr a b : ℤ) : GI) +
            (2 : GI) ^ r * ((∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ∈ orth U ∧ dot a b = 1),
              chi v₀ a * σt a b : ℤ) : GI) * giI := by
          simp_rw [hw_conv_nz _ b hb, Finset.sum_add_distrib]
          congr 1
          · simp_rw [Int.cast_sum]
            rw [Finset.sum_comm, Finset.mul_sum]
            have hinner : ∀ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a b = 0),
                (∑ u : U, ((chi (v₀ + u.1) a * σr a b : ℤ) : GI)) =
                  if a ∈ orth U then (2 : GI) ^ r * ((chi v₀ a * σr a b : ℤ) : GI) else 0 := by
              intro a _
              rw [← Int.cast_sum, ← Finset.sum_mul, sum_chi_affine, hcardU]
              split_ifs
              · push_cast; rw [gi_two_pow_eq_mk]; ext
                · simp; ring
                · simp
              · simp
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
            have hfeq : (Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ dot a b = 0)).filter
                (fun a => a ∈ orth U) =
                Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a b = 0) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
            rw [hfeq]
          · rw [← Finset.sum_mul]
            congr 1
            simp_rw [Int.cast_sum]
            rw [Finset.sum_comm, Finset.mul_sum]
            have hinner : ∀ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => dot a b = 1),
                (∑ u : U, ((chi (v₀ + u.1) a * σt a b : ℤ) : GI)) =
                  if a ∈ orth U then (2 : GI) ^ r * ((chi v₀ a * σt a b : ℤ) : GI) else 0 := by
              intro a _
              rw [← Int.cast_sum, ← Finset.sum_mul, sum_chi_affine, hcardU]
              split_ifs
              · push_cast; rw [gi_two_pow_eq_mk]; ext
                · simp; ring
                · simp
              · simp
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
            have hfeq : (Finset.univ.filter (fun a : F2 (2 * k) => dot a b = 1)).filter
                (fun a => a ∈ orth U) =
                Finset.univ.filter (fun a : F2 (2 * k) => a ∈ orth U ∧ dot a b = 1) := by
              ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
            rw [hfeq]
        rw [hsum_b]
        have hodd := odd_card_nonzero_dot_zero (orth U) b horth_dim
        have heven := even_card_dot_one (orth U) b horth_dim
        have hpar_r := sum_signs_parity
          (Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a b = 0))
          (fun a => chi v₀ a * σr a b)
          (fun a _ => by
            rcases chi_eq_one_or_neg_one v₀ a with h1 | h1 <;> rcases hσr_pm a b with h2 | h2 <;>
              simp [h1, h2])
        have hpar_t := sum_signs_parity
          (Finset.univ.filter (fun a : F2 (2 * k) => a ∈ orth U ∧ dot a b = 1))
          (fun a => chi v₀ a * σt a b)
          (fun a _ => by
            rcases chi_eq_one_or_neg_one v₀ a with h1 | h1 <;> rcases hσt_pm a b with h2 | h2 <;>
              simp [h1, h2])
        obtain ⟨q1, hq1⟩ := hodd
        obtain ⟨q2, hq2⟩ := heven
        have hr_even : (2 : ℤ) ∣ (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a b = 0),
            chi v₀ a * σr a b) - 1 := Int.dvd_of_emod_eq_zero (by omega)
        have ht_even : (2 : ℤ) ∣ ∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ∈ orth U ∧ dot a b = 1),
            chi v₀ a * σt a b := Int.dvd_of_emod_eq_zero (by omega)
        obtain ⟨t1, ht1⟩ := hr_even
        obtain ⟨t2, ht2⟩ := ht_even
        have h2re : ∀ m : ℕ, ((2 : GI) ^ m).re = (2 : ℤ) ^ m := fun m => by rw [gi_two_pow_eq_mk]
        have h2im : ∀ m : ℕ, ((2 : GI) ^ m).im = 0 := fun m => by rw [gi_two_pow_eq_mk]
        have hre_mi : ∀ (m : ℕ) (x : ℤ), ((2 : GI) ^ m * (x : GI)).re = (2 : ℤ) ^ m * x := fun m x => by
          rw [Zsqrtd.re_mul, h2re, h2im, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring
        have him_mi : ∀ (m : ℕ) (x : ℤ), ((2 : GI) ^ m * (x : GI)).im = 0 := fun m x => by
          rw [Zsqrtd.im_mul, h2re, h2im, Zsqrtd.re_intCast, Zsqrtd.im_intCast]; ring
        have hre_miI : ∀ (m : ℕ) (x : ℤ), (((2 : GI) ^ m * (x : GI)) * giI).re = 0 := fun m x => by
          rw [Zsqrtd.re_mul, hre_mi, him_mi]; simp [giI]
        have him_miI : ∀ (m : ℕ) (x : ℤ), (((2 : GI) ^ m * (x : GI)) * giI).im = (2 : ℤ) ^ m * x := fun m x => by
          rw [Zsqrtd.im_mul, hre_mi, him_mi]; simp [giI]
        constructor
        · simp only [Zsqrtd.re_sub, Zsqrtd.re_add, hre_mi, hre_miI, h2re, add_zero]
          refine ⟨t1, ?_⟩
          have hsum_eq : (∑ a ∈ Finset.univ.filter (fun a : F2 (2 * k) => a ≠ 0 ∧ a ∈ orth U ∧ dot a b = 0),
              chi v₀ a * σr a b) = 2 * t1 + 1 := by linarith
          rw [hsum_eq, pow_succ]; ring
        · simp only [Zsqrtd.im_sub, Zsqrtd.im_add, him_mi, him_miI, h2im, zero_add, sub_zero]
          refine ⟨t2, ?_⟩
          rw [ht2, pow_succ]; ring
    -- Substitute `w' u = 1 + 2 * η u` and cancel one factor of `2`!
    have hexpand : (∑ u : U, star (w' (v₀ + u.1)) * w' (v₀ + u.1 + b)) - (2 : GI) ^ r =
        2 * ∑ u : U, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b) +
          2 * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)) := by
      have hterm : ∀ u : U, star (w' (v₀ + u.1)) * w' (v₀ + u.1 + b) =
          1 + 2 * (star (η (v₀ + u.1)) + η (v₀ + u.1 + b) +
            2 * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)) := fun u => by
        rw [hw'_eta, hw'_eta, star_add, star_one, star_mul]
        have h2s : star (2 : GI) = 2 := by ext <;> simp
        rw [h2s]; ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Finset.mul_sum]
      have hcard_gi : (Fintype.card U : GI) = (2 : GI) ^ r := by
        rw [card_submodule_f2, hU]; norm_cast
      rw [hcard_gi]; ring
    rw [hexpand, pow_succ'] at hw_sub
    exact (mul_dvd_mul_iff_left (by intro hc; have := congr_arg Zsqrtd.re hc; simp at this)).mp hw_sub
  -- Step 6: Apply the 2-adic Subspace Induction Theorem (`M = 2*k - 2` gives `SubspaceVal η (2*k - 1)`)!
  have hIH : SubspaceVal η (2 * k - 1) := by
    have := subspaceVal_of_corrCongr (2 * k - 2) hCorr
    rwa [show 2 * k - 2 + 1 = 2 * k - 1 by omega] at this
  -- Step 7: Final kill! `2^(2*k) ∣ (-1)^k * giPi^(3*k) * (ψ' x - ψ' y)` for ALL `x, y`!
  have hinv_w' : ∀ x : F2 (2 * k),
      ∑ u : F2 (2 * k), (chi u x : GI) * (1 + 2 * η u) = (-1 : GI) ^ k * giPi ^ (3 * k) * ψ' x := by
    intro x
    have hpi_ne : giPi ^ k ≠ 0 := by
      intro hc
      have := congr_arg Zsqrtd.norm hc
      rw [gi_norm_pow_pi] at this
      exact pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0) (by simp [Zsqrtd.norm] at this)
    apply mul_left_cancel₀ hpi_ne
    have h1 : giPi ^ k * ∑ u : F2 (2 * k), (chi u x : GI) * (1 + 2 * η u) =
        urot * ∑ u : F2 (2 * k), (chi u x : GI) * z u := by
      simp_rw [← hw'_eta, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [w', hw_eq u]; ring
    rw [h1]
    have hwht := wht_inversion (R := GI) ψ x
    change urot * (∑ u : F2 (2 * k), (chi u x : GI) * ∑ y : F2 (2 * k), (chi u y : GI) * ψ y) = _
    rw [hwht, gi_two_pow_even k]
    simp only [ψ']
    have : giPi ^ k * giPi ^ (3 * k) = giPi ^ (4 * k) := by
      rw [← pow_add, show k + 3 * k = 4 * k by omega]
    calc urot * ((-1 : GI) ^ k * giPi ^ (4 * k) * ψ x)
        = (-1 : GI) ^ k * (giPi ^ k * giPi ^ (3 * k)) * (urot * ψ x) := by rw [this]; ring
      _ = giPi ^ k * ((-1 : GI) ^ k * giPi ^ (3 * k) * (urot * ψ x)) := by ring
  have h4_dvd_diff : ∀ x y : F2 (2 * k), (4 : ℤ) ∣ (ψ' x - ψ' y).norm := by
    intro x y
    have hd := pow_two_dvd_wht_sub_of_subspaceVal hn hIH x y
    rw [hinv_w' x, hinv_w' y] at hd
    have hfac : (-1 : GI) ^ k * giPi ^ (3 * k) * ψ' x - (-1 : GI) ^ k * giPi ^ (3 * k) * ψ' y =
        (-1 : GI) ^ k * giPi ^ (3 * k) * (ψ' x - ψ' y) := by ring
    rw [hfac] at hd
    obtain ⟨q, hq⟩ := hd
    have hnorm := congr_arg Zsqrtd.norm hq
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, Zsqrtd.norm_mul, gi_norm_pow_two, gi_norm_pow_pi] at hnorm
    have hneg1_norm : ((-1 : GI) ^ k).norm = 1 := by
      have hgen : ∀ m : ℕ, ((-1 : GI) ^ m).norm = 1 := fun m => by
        induction m with
        | zero => simp [Zsqrtd.norm]
        | succ m ih =>
          rw [pow_succ, Zsqrtd.norm_mul, ih]
          simp [Zsqrtd.norm]
      exact hgen k
    rw [hneg1_norm, one_mul] at hnorm
    have h2k_dvd : (2 : ℤ) ^ k ∣ (ψ' x - ψ' y).norm := by
      refine ⟨q.norm, ?_⟩
      have hpow : (2 : ℤ) ^ (2 * (2 * k)) = (2 : ℤ) ^ (3 * k) * (2 : ℤ) ^ k := by
        rw [← pow_add, show 3 * k + k = 2 * (2 * k) by omega]
      rw [hpow, mul_assoc] at hnorm
      exact mul_left_cancel₀ (pow_ne_zero (3 * k) (by norm_num : (2 : ℤ) ≠ 0)) hnorm
    exact dvd_trans (pow_dvd_pow (2 : ℤ) hk) h2k_dvd
  -- Therefore `ψ' x = ±ψ' 0` for ALL `x`, so `star (ψ x) * ψ (x + a)` is PURELY REAL!
  have hpm_all : ∀ x : F2 (2 * k), ψ' x = ψ' 0 ∨ ψ' x = -ψ' 0 := by
    intro x
    have h4 := h4_dvd_diff x 0
    rcases hψ'_vals x with hx | hx | hx | hx <;> rcases hψ'_vals 0 with h0 | h0 | h0 | h0 <;>
      rw [hx, h0] at h4 ⊢
    all_goals try (left; rfl)
    all_goals try (right; simp)
    all_goals (exfalso; norm_num [Zsqrtd.norm, giI] at h4)
  -- Contradiction: for `a = eVec 0`, `gHat a a` has `dot a a = 1`, hence `Im(gHat a a) = ±2^k ≠ 0`!
  let a0 : F2 (2 * k) := eVec ⟨0, by omega⟩
  have ha0_ne : a0 ≠ 0 := fun hc => by
    have := congr_fun hc ⟨0, by omega⟩; simp [a0, eVec] at this
  have hdot1 : dot a0 a0 = 1 := by
    rw [show a0 = eVec ⟨0, by omega⟩ from rfl, dot_eVec_left]
    simp [eVec]
  obtain ⟨s, hs_pm, hg_eq⟩ := (hgHat_nz a0 ha0_ne a0).2 hdot1
  have him_zero : (gHat a0 a0).im = 0 := by
    have hterm_im : ∀ x : F2 (2 * k), ((chi a0 x : GI) * star (ψ x) * ψ (x + a0)).im = 0 := by
      intro x
      have hprod : star (ψ x) * ψ (x + a0) = star (ψ' x) * ψ' (x + a0) := by
        simp only [ψ', star_mul]
        calc star (ψ x) * ψ (x + a0)
            = star (ψ x) * (star urot * urot) * ψ (x + a0) := by rw [hurot_star, mul_one]
          _ = star (ψ x) * star urot * (urot * ψ (x + a0)) := by ring
      have hreal : star (ψ' x) * ψ' (x + a0) = 1 ∨ star (ψ' x) * ψ' (x + a0) = -1 := by
        have h0norm : star (ψ' 0) * ψ' 0 = 1 := by
          rcases hψ'_vals 0 with h | h | h | h <;> rw [h] <;> ext <;> simp [giI]
        rcases hpm_all x with h1 | h1 <;> rcases hpm_all (x + a0) with h2 | h2 <;>
          rw [h1, h2]
        · left; exact h0norm
        · right; simp [h0norm]
        · right; simp [h0norm]
        · left; simp [h0norm]
      rw [mul_assoc, hprod]
      rcases hreal with hr | hr <;> rw [hr] <;> simp
    simp only [gHat, gi_sum_im]
    exact Finset.sum_eq_zero fun x _ => hterm_im x
  have him_nz : (gHat a0 a0).im ≠ 0 := by
    rw [hg_eq]
    have h1 : ((s : GI) * (2 : GI) ^ k * giI).im = s * (2 : ℤ) ^ k := by
      rw [gi_two_pow_eq_mk]; simp [giI]
    rw [h1]
    rcases hs_pm with rfl | rfl
    · simp
    · simp
  exact him_nz him_zero

/-- **THEOREM 1 (All `n ≥ 3`)**: No Alltop function exists on `𝔽₂ⁿ` for any `n ≥ 3`. -/
theorem no_alltop_f2 (n : ℕ) (hn : 3 ≤ n) (φ : F2 n → ℂ) : ¬ IsAlltop n φ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h2k : n = 2 * k := by omega
    subst h2k
    exact no_alltop_even k (by omega) φ
  · subst hk
    exact no_alltop_odd k (by omega) φ

/-- **Sharpness (`n = 2` EXISTS!)**: `φ₂(x₀, x₁) = i^(x₀ x₁)` (`(1, 1, 1, i)`) IS an Alltop function on `𝔽₂²`. -/
def alltopTwo : F2 2 → ℂ := fun x =>
  if x 0 = 1 ∧ x 1 = 1 then Complex.I else 1

theorem exists_alltop_two : IsAlltop 2 alltopTwo := by
  refine ⟨fun x => ?_, fun a ha b => ?_⟩
  · simp only [alltopTwo]; split_ifs <;> simp [Complex.normSq_I]
  · -- Expand finite sums explicitly over all 4 vectors of `𝔽₂²`
    have hsum : ∀ f : F2 2 → ℂ, (∑ x : F2 2, f x) =
        f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
      intro f
      let e : Fin 4 ≃ F2 2 :=
        { toFun := fun i => match i with
            | 0 => ![0, 0] | 1 => ![0, 1] | 2 => ![1, 0] | 3 => ![1, 1]
          invFun := fun x =>
            if x 0 = 0 then (if x 1 = 0 then 0 else 1) else (if x 1 = 0 then 2 else 3)
          left_inv := fun i => by fin_cases i <;> decide
          right_inv := fun x => by
            ext j
            have h0 := zmod2_cases (x 0)
            have h1 := zmod2_cases (x 1)
            fin_cases j <;> rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
              simp [h0, h1] }
      rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fin.sum_univ_four]
      simp [e]
    have ha_cases : a = ![0, 1] ∨ a = ![1, 0] ∨ a = ![1, 1] := by
      have h0 := zmod2_cases (a 0)
      have h1 := zmod2_cases (a 1)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exfalso; apply ha; ext j; fin_cases j <;> simp [h0, h1]
      · left; ext j; fin_cases j <;> simp [h0, h1]
      · right; left; ext j; fin_cases j <;> simp [h0, h1]
      · right; right; ext j; fin_cases j <;> simp [h0, h1]
    have hb_cases : b = ![0, 0] ∨ b = ![0, 1] ∨ b = ![1, 0] ∨ b = ![1, 1] := by
      have h0 := zmod2_cases (b 0)
      have h1 := zmod2_cases (b 1)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · left; ext j; fin_cases j <;> simp [h0, h1]
      · right; left; ext j; fin_cases j <;> simp [h0, h1]
      · right; right; left; ext j; fin_cases j <;> simp [h0, h1]
      · right; right; right; ext j; fin_cases j <;> simp [h0, h1]
    rw [hsum]
    rcases ha_cases with rfl | rfl | rfl <;> rcases hb_cases with rfl | rfl | rfl | rfl
    all_goals
      simp only [alltopTwo, chi, dot, Fin.sum_univ_two, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, add_zero, zero_add, mul_zero, mul_one,
        show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide,
        show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte, and_self, and_false, false_and,
        Complex.normSq_apply]
      norm_num

/-- Phase-state Pauli 4th moment `F_n(φ) = ∑_{a,b} |2^(-n) ∑_x (-1)^(b·x) conj(φ x) φ(x+a)|^4`
    (equivalently `2^n ‖φ‖_{U³(𝔽₂ⁿ)}⁸`). -/
noncomputable def phasePauliMoment4 (n : ℕ) (φ : F2 n → ℂ) : ℝ :=
  ∑ a : F2 n, ∑ b : F2 n,
    (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) / ((2 : ℝ) ^ n) ^ 2) ^ 2

/-- Parseval identity for `g_a`: `∑_b |WHT(g_a)(b)|² = 4^n` for any unit-modulus `φ`. -/
lemma sum_normSq_wht_multDeriv {n : ℕ} {φ : F2 n → ℂ} (hunit : ∀ x, Complex.normSq (φ x) = 1) (a : F2 n) :
    ∑ b : F2 n, Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) = ((2 : ℝ) ^ n) ^ 2 := by
  have hC : ((∑ b : F2 n, Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) : ℝ) : ℂ) =
      (((2 : ℝ) ^ n) ^ 2 : ℝ) := by
    push_cast
    have hns : ∀ z : ℂ, (Complex.normSq z : ℂ) = star z * z := fun z => by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]
    simp_rw [hns]
    have hexp : ∀ b : F2 n,
        star (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) *
          (∑ y : F2 n, (chi b y : ℂ) * star (φ y) * φ (y + a)) =
        ∑ x : F2 n, ∑ y : F2 n, (chi b (x + y) : ℂ) * (star (multDeriv φ a x) * multDeriv φ a y) := by
      intro b
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hc : star (chi b x : ℂ) = (chi b x : ℂ) := by simp
      simp only [multDeriv, star_mul, hc, chi_add_right]
      push_cast; ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hinner : ∀ x : F2 n,
        (∑ b : F2 n, ∑ y : F2 n, (chi b (x + y) : ℂ) * (star (multDeriv φ a x) * multDeriv φ a y)) =
        (2 : ℂ) ^ n := by
      intro x
      rw [Finset.sum_comm]
      have hy : ∀ y : F2 n,
          (∑ b : F2 n, (chi b (x + y) : ℂ) * (star (multDeriv φ a x) * multDeriv φ a y)) =
          if y = x then (2 : ℂ) ^ n else 0 := by
        intro y
        rw [← Finset.sum_mul, ← Int.cast_sum, sum_chi]
        have hiff : x + y = 0 ↔ y = x := by
          constructor
          · intro h; have := congr_arg (x + ·) h; simpa [f2_add_cancel_left] using this
          · intro hy; rw [hy, f2_add_self]
        by_cases h : y = x
        · subst h
          simp only [f2_add_self, ↓reduceIte]
          have h1 : star (multDeriv φ a y) * multDeriv φ a y = 1 := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, multDeriv_normSq hunit a y]; simp
          rw [h1, mul_one]; norm_cast
        · simp [h, show x + y ≠ 0 from fun hc => h (hiff.mp hc)]
      simp_rw [hy]
      simp
    simp_rw [hinner]
    simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_pi, ZMod.card, sq]
  exact_mod_cast hC

/-- **Corollary (Strict Gowers `U³` Lower Bound for All `n ≥ 3`)**:
    Every phase function `φ : 𝔽₂ⁿ → U(1)` (`n ≥ 3`) strictly exceeds the MUB floor `2 - 2^(-n)`. -/
theorem phasePauliMoment4_gt_mub (n : ℕ) (hn : 3 ≤ n) (φ : F2 n → ℂ)
    (hunit : ∀ x : F2 n, Complex.normSq (φ x) = 1) :
    2 - 1 / (2 : ℝ) ^ n < phasePauliMoment4 n φ := by
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  -- Split `a = 0` (contributes `1`) and `a ≠ 0` (each contributes `≥ 1 / 2^n` by Cauchy–Schwarz!)
  have ha0 : (∑ b : F2 n,
      (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + 0)) / ((2 : ℝ) ^ n) ^ 2) ^ 2) = 1 := by
    have hterm : ∀ b : F2 n,
        (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + 0)) / ((2 : ℝ) ^ n) ^ 2) ^ 2 =
        if b = 0 then 1 else 0 := by
      intro b
      have h1 : ∀ x : F2 n, star (φ x) * φ (x + 0) = 1 := fun x => by
        rw [add_zero, mul_comm, Complex.star_def, Complex.mul_conj, hunit x]; simp
      have hs : (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + 0)) =
          ((∑ x : F2 n, chi x b : ℤ) : ℂ) := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun x _ => by rw [mul_assoc, h1 x, mul_one, chi_comm]
      rw [hs, sum_chi]
      split_ifs
      · push_cast
        have hns : Complex.normSq ((2 : ℂ) ^ n) = ((2 : ℝ) ^ n) ^ 2 := by
          rw [show (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) by norm_cast, Complex.normSq_ofReal, sq]
        rw [hns, div_self (ne_of_gt (sq_pos_of_pos h2n_pos))]; norm_num
      · simp
    simp_rw [hterm]; simp
  -- For every `a ≠ 0`, Cauchy–Schwarz (sum of squares identity!) gives:
  -- `∑_b (c_b / 4^n)^2 = 1/2^n + ∑_b (c_b - 2^n)^2 / 4^(2n) ≥ 1/2^n`!
  have hcs : ∀ a : F2 n,
      (∑ b : F2 n,
        (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) / ((2 : ℝ) ^ n) ^ 2) ^ 2) =
      1 / (2 : ℝ) ^ n +
      (∑ b : F2 n,
        (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) - (2 : ℝ) ^ n) ^ 2) /
        (((2 : ℝ) ^ n) ^ 2) ^ 2 := by
    intro a
    let c : F2 n → ℝ := fun b => Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a))
    have hsum_c : ∑ b : F2 n, c b = ((2 : ℝ) ^ n) ^ 2 := sum_normSq_wht_multDeriv hunit a
    have hcard : (Fintype.card (F2 n) : ℝ) = (2 : ℝ) ^ n := by
      simp [Fintype.card_pi, ZMod.card]
    have hdiff : ∑ b : F2 n, (c b - (2 : ℝ) ^ n) ^ 2 =
        (∑ b : F2 n, (c b) ^ 2) - ((2 : ℝ) ^ n) ^ 3 := by
      have hexp : ∀ b, (c b - (2 : ℝ) ^ n) ^ 2 = (c b) ^ 2 - 2 * (2 : ℝ) ^ n * c b + ((2 : ℝ) ^ n) ^ 2 :=
        fun b => by ring
      simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsum_c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      ring
    change ∑ b : F2 n, (c b / ((2 : ℝ) ^ n) ^ 2) ^ 2 =
      1 / (2 : ℝ) ^ n + (∑ b : F2 n, (c b - (2 : ℝ) ^ n) ^ 2) / (((2 : ℝ) ^ n) ^ 2) ^ 2
    rw [hdiff]
    have hdiv : ∑ b : F2 n, (c b / ((2 : ℝ) ^ n) ^ 2) ^ 2 =
        (∑ b : F2 n, (c b) ^ 2) / (((2 : ℝ) ^ n) ^ 2) ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun b _ => by rw [div_pow]
    rw [hdiv]
    field_simp [ne_of_gt h2n_pos]
    ring
  -- Sum over `a ∈ univ.erase 0`!
  unfold phasePauliMoment4
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F2 n)), ha0]
  simp_rw [hcs]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hcard_er : ((Finset.univ.erase (0 : F2 n)).card : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_pi]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    simp [ZMod.card, Nat.cast_sub h1]
  rw [hcard_er]
  have hbase : 1 + ((2 : ℝ) ^ n - 1) * (1 / (2 : ℝ) ^ n) = 2 - 1 / (2 : ℝ) ^ n := by
    field_simp [ne_of_gt h2n_pos]; ring
  rw [← add_assoc, hbase]
  -- Excess term is strictly positive because `¬ IsAlltop n φ`!
  have hnot := no_alltop_f2 n hn φ
  have hex : ∃ a : F2 n, a ≠ 0 ∧ ∃ b : F2 n,
      Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) ≠ (2 : ℝ) ^ n := by
    by_contra hc
    push Not at hc
    exact hnot ⟨hunit, hc⟩
  obtain ⟨a₀, ha₀, b₀, hb₀⟩ := hex
  have hterm_pos : 0 <
      (∑ b : F2 n, (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a₀)) - (2 : ℝ) ^ n) ^ 2) /
      (((2 : ℝ) ^ n) ^ 2) ^ 2 := by
    apply div_pos _ (by positivity)
    refine Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨b₀, Finset.mem_univ b₀, sq_pos_of_ne_zero (sub_ne_zero.mpr hb₀)⟩
  have hsum_pos : 0 < ∑ a ∈ Finset.univ.erase (0 : F2 n),
      (∑ b : F2 n, (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) - (2 : ℝ) ^ n) ^ 2) /
      (((2 : ℝ) ^ n) ^ 2) ^ 2 := by
    refine Finset.sum_pos' (fun a _ => div_nonneg (Finset.sum_nonneg fun b _ => sq_nonneg _) (by positivity))
      ⟨a₀, Finset.mem_erase.mpr ⟨ha₀, Finset.mem_univ a₀⟩, hterm_pos⟩
  linarith

end MultiQubitMUB
