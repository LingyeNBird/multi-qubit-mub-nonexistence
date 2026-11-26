module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Elementary Gaussian Integer Arithmetic (Zero-UFD)

Provides elementary descent lemmas in `GaussianInt` (`ℤ[i]`) used in the non-existence
proof of multi-qubit Pauli-covariant MUB fiducial states and Alltop functions on `𝔽₂ⁿ`:
1. Integer sum-of-two-squares descent for powers of 2 (`m^2 + l^2 = 2^r`).
2. Elementary `(1 + i)^k`-divisibility from `2^k ∣ norm z`.
3. Coordinate-wise characterization of `2^r ∣ z` in `GaussianInt`.
4. Exact complex embedding `giToComplex : GaussianInt →+* ℂ` preserving conjugation and norm.
-/

@[expose] public section

namespace MultiQubitMUB

abbrev GI := GaussianInt

/-- The imaginary unit `i = ⟨0, 1⟩` in `ℤ[i]`. -/
def giI : GI := ⟨0, 1⟩

/-- The Gaussian prime `π = 1 + i` of norm 2. -/
def giPi : GI := ⟨1, 1⟩

@[simp] lemma giI_re : giI.re = 0 := rfl
@[simp] lemma giI_im : giI.im = 1 := rfl
@[simp] lemma giPi_re : giPi.re = 1 := rfl
@[simp] lemma giPi_im : giPi.im = 1 := rfl

lemma giI_sq : giI * giI = -1 := by
  ext <;> simp [giI]

lemma giPi_sq : giPi * giPi = (2 : GI) * giI := by
  ext <;> simp [giPi, giI]

lemma giPi_norm : giPi.norm = 2 := by
  simp [Zsqrtd.norm, giPi]

lemma giI_norm : giI.norm = 1 := by
  simp [Zsqrtd.norm, giI]

lemma gi_norm_eq (z : GI) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm]; ring

lemma gi_mul_star (z : GI) : star z * z = (z.norm : GI) := by
  ext
  · simp [Zsqrtd.norm]
  · simp; ring

lemma gi_star_mul (z : GI) : z * star z = (z.norm : GI) := by
  rw [mul_comm, gi_mul_star]

lemma gi_two_eq : (2 : GI) = (-giI) * giPi ^ 2 := by
  ext <;> simp [giI, giPi, sq]

lemma gi_two_pow_even (k : ℕ) : (2 : GI) ^ (2 * k) = (-1 : GI) ^ k * giPi ^ (4 * k) := by
  have h4 : (2 : GI) ^ 2 = (-1 : GI) * giPi ^ 4 := by
    ext <;> simp [giPi, pow_succ]
  calc (2 : GI) ^ (2 * k) = ((2 : GI) ^ 2) ^ k := by rw [pow_mul]
    _ = ((-1 : GI) * giPi ^ 4) ^ k := by rw [h4]
    _ = (-1 : GI) ^ k * (giPi ^ 4) ^ k := by rw [mul_pow]
    _ = (-1 : GI) ^ k * giPi ^ (4 * k) := by rw [← pow_mul]

lemma gi_norm_pow_pi (k : ℕ) : (giPi ^ k).norm = (2 : ℤ) ^ k := by
  induction k with
  | zero => simp [Zsqrtd.norm]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, giPi_norm, pow_succ]

lemma gi_norm_pow_two (r : ℕ) : ((2 : GI) ^ r).norm = (2 : ℤ) ^ (2 * r) := by
  have h2 : (2 : GI).norm = 4 := by simp [Zsqrtd.norm]
  induction r with
  | zero => simp [Zsqrtd.norm]
  | succ r ih =>
    rw [pow_succ, Zsqrtd.norm_mul, ih, h2, show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    ring

lemma gi_two_pow_eq_mk (r : ℕ) : (2 : GI) ^ r = ⟨(2 : ℤ) ^ r, 0⟩ := by
  induction r with
  | zero => ext <;> simp
  | succ r ih =>
    rw [pow_succ, ih]
    ext <;> simp [pow_succ]

/-- Divisibility by `2^r` in `ℤ[i]` is equivalent to divisibility of both integer coordinates. -/
lemma pow_two_dvd_gi_iff (r : ℕ) (z : GI) :
    ((2 : GI) ^ r) ∣ z ↔ (2 : ℤ) ^ r ∣ z.re ∧ (2 : ℤ) ^ r ∣ z.im := by
  rw [gi_two_pow_eq_mk]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨⟨w.re, ?_⟩, ⟨w.im, ?_⟩⟩
    · have := congr_arg Zsqrtd.re hw
      simpa using this
    · have := congr_arg Zsqrtd.im hw
      simpa using this
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a, b⟩, ?_⟩
    ext
    · simp [ha]
    · simp [hb]

/-- If `4 ∣ m^2 + l^2` for integers `m, l`, then both `m` and `l` are even. -/
lemma even_of_four_dvd_sq_add_sq {m l : ℤ} (h : (4 : ℤ) ∣ m ^ 2 + l ^ 2) :
    (2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ l := by
  obtain ⟨k, hk⟩ := h
  have hm_mod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hl_mod : l % 2 = 0 ∨ l % 2 = 1 := by omega
  rcases hm_mod with h1 | h1 <;> rcases hl_mod with h2 | h2
  · exact ⟨Int.dvd_of_emod_eq_zero h1, Int.dvd_of_emod_eq_zero h2⟩
  · exfalso
    have hm : m = 2 * (m / 2) := by omega
    have hl : l = 2 * (l / 2) + 1 := by omega
    rw [hm, hl] at hk
    have : 4 * ((m / 2) ^ 2 + (l / 2) ^ 2 + (l / 2) - k) + 1 = 0 := by linarith
    omega
  · exfalso
    have hm : m = 2 * (m / 2) + 1 := by omega
    have hl : l = 2 * (l / 2) := by omega
    rw [hm, hl] at hk
    have : 4 * ((m / 2) ^ 2 + (m / 2) + (l / 2) ^ 2 - k) + 1 = 0 := by linarith
    omega
  · exfalso
    have hm : m = 2 * (m / 2) + 1 := by omega
    have hl : l = 2 * (l / 2) + 1 := by omega
    rw [hm, hl] at hk
    have : 4 * ((m / 2) ^ 2 + (m / 2) + (l / 2) ^ 2 + (l / 2) - k) + 2 = 0 := by linarith
    omega

/-- Elementary descent: the only integer solutions to `m^2 + l^2 = 2^(2j)` are `(±2^j, 0)` and `(0, ±2^j)`. -/
lemma sq_add_sq_eq_pow_two_even : ∀ (j : ℕ) {m l : ℤ}, m ^ 2 + l ^ 2 = (2 : ℤ) ^ (2 * j) →
    (m = (2 : ℤ) ^ j ∧ l = 0) ∨ (m = -((2 : ℤ) ^ j) ∧ l = 0) ∨
    (m = 0 ∧ l = (2 : ℤ) ^ j) ∨ (m = 0 ∧ l = -((2 : ℤ) ^ j))
  | 0, m, l, h => by
    simp only [mul_zero, pow_zero] at h ⊢
    have hm_bnd : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith [sq_nonneg l]
    have hl_bnd : -1 ≤ l ∧ l ≤ 1 := by constructor <;> nlinarith [sq_nonneg m]
    have hm : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    have hl : l = -1 ∨ l = 0 ∨ l = 1 := by omega
    rcases hm with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> simp at h ⊢
  | j + 1, m, l, h => by
    have h4 : (4 : ℤ) ∣ m ^ 2 + l ^ 2 := by
      rw [h, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      exact ⟨(2 : ℤ) ^ (2 * j), by ring⟩
    obtain ⟨⟨m', rfl⟩, ⟨l', rfl⟩⟩ := even_of_four_dvd_sq_add_sq h4
    have h' : m' ^ 2 + l' ^ 2 = (2 : ℤ) ^ (2 * j) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add] at h
      linarith
    rcases sq_add_sq_eq_pow_two_even j h' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨by ring, by ring⟩
    · right; left; exact ⟨by ring, by ring⟩
    · right; right; left; exact ⟨by ring, by ring⟩
    · right; right; right; exact ⟨by ring, by ring⟩

/-- Elementary descent: the only integer solutions to `m^2 + l^2 = 2^(2j+1)` are `(±2^j, ±2^j)`. -/
lemma sq_add_sq_eq_pow_two_odd : ∀ (j : ℕ) {m l : ℤ}, m ^ 2 + l ^ 2 = (2 : ℤ) ^ (2 * j + 1) →
    (m = (2 : ℤ) ^ j ∨ m = -((2 : ℤ) ^ j)) ∧ (l = (2 : ℤ) ^ j ∨ l = -((2 : ℤ) ^ j))
  | 0, m, l, h => by
    simp only [mul_zero, zero_add, pow_one, pow_zero] at h ⊢
    have hm_bnd : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith [sq_nonneg l]
    have hl_bnd : -1 ≤ l ∧ l ≤ 1 := by constructor <;> nlinarith [sq_nonneg m]
    have hm : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    have hl : l = -1 ∨ l = 0 ∨ l = 1 := by omega
    rcases hm with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> simp at h ⊢
  | j + 1, m, l, h => by
    have h4 : (4 : ℤ) ∣ m ^ 2 + l ^ 2 := by
      rw [h, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add]
      exact ⟨(2 : ℤ) ^ (2 * j + 1), by ring⟩
    obtain ⟨⟨m', rfl⟩, ⟨l', rfl⟩⟩ := even_of_four_dvd_sq_add_sq h4
    have h' : m' ^ 2 + l' ^ 2 = (2 : ℤ) ^ (2 * j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add] at h
      linarith
    obtain ⟨hm', hl'⟩ := sq_add_sq_eq_pow_two_odd j h'
    constructor
    · rcases hm' with rfl | rfl
      · left; ring
      · right; ring
    · rcases hl' with rfl | rfl
      · left; ring
      · right; ring

/-- Elementary `(1+i)`-divisibility: if `2 ∣ z.norm`, then `(1 + i) ∣ z` in `ℤ[i]`. -/
lemma giPi_dvd_of_two_dvd_norm {z : GI} (h : (2 : ℤ) ∣ z.norm) : giPi ∣ z := by
  rw [gi_norm_eq] at h
  obtain ⟨k, hk⟩ := h
  have h1 : z.re % 2 = 0 ∨ z.re % 2 = 1 := by omega
  have h2 : z.im % 2 = 0 ∨ z.im % 2 = 1 := by omega
  have hpar : (z.re + z.im) % 2 = 0 ∧ (z.im - z.re) % 2 = 0 := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · omega
    · exfalso
      have hr : z.re = 2 * (z.re / 2) := by omega
      have hi : z.im = 2 * (z.im / 2) + 1 := by omega
      rw [hr, hi] at hk
      have : 2 * (2 * (z.re / 2) ^ 2 + 2 * (z.im / 2) ^ 2 + 2 * (z.im / 2) - k) + 1 = 0 := by linarith
      omega
    · exfalso
      have hr : z.re = 2 * (z.re / 2) + 1 := by omega
      have hi : z.im = 2 * (z.im / 2) := by omega
      rw [hr, hi] at hk
      have : 2 * (2 * (z.re / 2) ^ 2 + 2 * (z.re / 2) + 2 * (z.im / 2) ^ 2 - k) + 1 = 0 := by linarith
      omega
    · omega
  refine ⟨⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩, ?_⟩
  ext <;> simp [giPi] <;> omega

/-- Elementary `(1+i)^k`-divisibility by induction on `k` (zero UFD!). -/
lemma pow_giPi_dvd_of_pow_two_dvd_norm :
    ∀ (k : ℕ) {z : GI}, (2 : ℤ) ^ k ∣ z.norm → giPi ^ k ∣ z
  | 0, z, _ => by simp
  | k + 1, z, h => by
    have h2 : (2 : ℤ) ∣ z.norm := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h
    obtain ⟨w, rfl⟩ := giPi_dvd_of_two_dvd_norm h2
    rw [Zsqrtd.norm_mul, giPi_norm, pow_succ'] at h
    have hw : (2 : ℤ) ^ k ∣ w.norm := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
    obtain ⟨u, rfl⟩ := pow_giPi_dvd_of_pow_two_dvd_norm k hw
    exact ⟨u, by rw [pow_succ']; ring⟩

/-- Ring homomorphism embedding `ℤ[i]` into `ℂ`. -/
def giToComplex : GI →+* ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * Complex.I
  map_one' := by simp
  map_mul' a b := by
    cases a; cases b
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one]
    ring_nf
    rw [Complex.I_sq]
    ring
  map_zero' := by simp
  map_add' a b := by
    cases a; cases b
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Int.cast_add]
    ring

@[simp] lemma giToComplex_mk (a b : ℤ) :
    giToComplex ⟨a, b⟩ = (a : ℂ) + (b : ℂ) * Complex.I := rfl

@[simp] lemma giToComplex_giI : giToComplex giI = Complex.I := by
  simp [giToComplex, giI]

@[simp] lemma giToComplex_giPi : giToComplex giPi = 1 + Complex.I := by
  simp [giToComplex, giPi]

@[simp] lemma giToComplex_star (z : GI) : giToComplex (star z) = star (giToComplex z) := by
  cases z
  simp [giToComplex, Complex.conj_I]

lemma giToComplex_injective : Function.Injective giToComplex := by
  intro a b h
  cases a with | mk a1 a2 =>
  cases b with | mk b1 b2 =>
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  simp [giToComplex] at hre him
  ext
  · exact_mod_cast hre
  · exact_mod_cast him

lemma giToComplex_normSq (z : GI) : Complex.normSq (giToComplex z) = (z.norm : ℝ) := by
  cases z
  rw [gi_norm_eq]
  simp [giToComplex, Complex.normSq_apply]
  ring

@[simp] lemma gi_star_re (z : GI) : (star z).re = z.re := rfl
@[simp] lemma gi_star_im (z : GI) : (star z).im = -z.im := rfl

lemma gi_sum_re {α : Type*} (s : Finset α) (f : α → GI) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => simp [Finset.sum_cons, ih]

lemma gi_sum_im {α : Type*} (s : Finset α) (f : α → GI) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => simp [Finset.sum_cons, ih]

end MultiQubitMUB
