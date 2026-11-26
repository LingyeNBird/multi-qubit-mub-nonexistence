import MultiQubitMUB.PauliGroup
import MultiQubitMUB.SpikeFamily

/-!
# General Pure-State Quantitative Lower Bounds Above the Welch/SIC Bound

Proves in complete matrix-free generality on `QState n := F2 n → ℂ` (zero `sorry`,
zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only):

1. **Universal Quantitative Stability Theorem (`pauliMoment4_ge_welch_add_universal`)**:
   For EVERY `n ∈ {2} ∪ {4, 5, 6, …}` (`d = 2ⁿ`) and EVERY unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n`,
     `pauliMoment4 n ψ ≥ 2 d / (d + 1) + 16 (d - 1) / (d⁴ (d + 1)³) > 2 d / (d + 1)`.
   - Yields a new elementary proof of Godsil–Roy (2009) (`no_pauli_sic_all`) AND its first
     explicit quantitative stability theorem certifying a strictly positive gap above the
     Welch/SIC bound for all general pure states on every `n ≠ 1, 3`.
2. **Sharp `n = 2` Bound (`pauliMoment4_two_ge`)**:
   Using the `b(2 - b)` odd-integer parity upgrade and `Tr(ρ̃³) ≤ 1`,
     `pauliMoment4 2 ψ ≥ 8 / 5 + 34 / 1000` (`= 1.634`, Welch `= 1.600`).
3. **Kramers / Elliptic-Quadric `Q⁻(2n-1, 2)` Stability Theorem (`pauliMoment4_four_ge_kramers`)**:
   Using the antiunitary Kramers operator `Θ_c = P_c ∘ K` (`Θ_c² = -I`, `⟨ψ | Θ_c ψ⟩ = 0`),
   a 10-line matrix-free proof of the quaternionic Frobenius inequality `frobSq(A²) ≤ (1/2) frobSq(A)²`,
   and averaging the rank-2 state `ρ_c = (|ψ⟩⟨ψ| + |Θ_c ψ⟩⟨Θ_c ψ|) / 2` over all 120 elliptic
   quadrics `Q⁻(7, 2) ⊂ W(7, 2)`, certifies unconditionally:
     `pauliMoment4 4 ψ ≥ 32 / 17 + 33 / 10000` (`> 1.88565`, Welch `= 32/17 ≈ 1.88235`,
     a `57×` boost over naive `W(7, 2)` parity!).
4. **Matrix-Free Contextuality-Degree-to-Magic Bridge (`pauliMoment4_contextuality_bridge`,
   `pauliMoment4_four_of_contextuality_1575`)**:
   Connects `pauliMoment4 n ψ` directly to the Pauli contextuality degree `CD(W(2n-1, 2))`
   (maximum sign-cube sum `S(σ) = ∑_{q≠0} σ_q T_q(σ)`). At `n = 4`, proves:
     `(∀ σ ∈ {±1}^{𝔽₂⁸ \ {0}}, signCubeSum 4 σ ≤ 6615) → ∀ ψ, pauliMoment4 4 ψ ≥ 193 / 100`.
-/

namespace MultiQubitMUB

open scoped Classical

/-! ### Section 1: Matrix-Free Operator Algebra on `F2 n → F2 n → ℂ` -/

abbrev QMat (n : ℕ) := F2 n → F2 n → ℂ

def matMul {n : ℕ} (A B : QMat n) : QMat n :=
  fun x y => ∑ z : F2 n, A x z * B z y

def matAdd {n : ℕ} (A B : QMat n) : QMat n :=
  fun x y => A x y + B x y

def matSub {n : ℕ} (A B : QMat n) : QMat n :=
  fun x y => A x y - B x y

def matSmul {n : ℕ} (c : ℂ) (A : QMat n) : QMat n :=
  fun x y => c * A x y

def matId (n : ℕ) : QMat n :=
  fun x y => if x = y then 1 else 0

def matAdj {n : ℕ} (A : QMat n) : QMat n :=
  fun x y => star (A y x)

def matTr {n : ℕ} (A : QMat n) : ℂ :=
  ∑ x : F2 n, A x x

def frobSq {n : ℕ} (A : QMat n) : ℝ :=
  ∑ x : F2 n, ∑ y : F2 n, Complex.normSq (A x y)

def IsHermMat {n : ℕ} (A : QMat n) : Prop :=
  ∀ x y : F2 n, A y x = star (A x y)

def matApply {n : ℕ} (A : QMat n) (ψ : QState n) : QState n :=
  fun x => ∑ y : F2 n, A x y * ψ y

lemma frobSq_nonneg {n : ℕ} (A : QMat n) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma frobSq_smul {n : ℕ} (c : ℂ) (A : QMat n) :
    frobSq (matSmul c A) = Complex.normSq c * frobSq A := by
  simp only [frobSq, matSmul, map_mul, Finset.mul_sum]

lemma matTr_add {n : ℕ} (A B : QMat n) :
    matTr (matAdd A B) = matTr A + matTr B := by
  simp only [matTr, matAdd, Finset.sum_add_distrib]

lemma matTr_sub {n : ℕ} (A B : QMat n) :
    matTr (matSub A B) = matTr A - matTr B := by
  simp only [matTr, matSub, Finset.sum_sub_distrib]

lemma matTr_smul {n : ℕ} (c : ℂ) (A : QMat n) :
    matTr (matSmul c A) = c * matTr A := by
  simp only [matTr, matSmul, Finset.mul_sum]

lemma matTr_mul_comm {n : ℕ} (A B : QMat n) :
    matTr (matMul A B) = matTr (matMul B A) := by
  simp only [matTr, matMul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _

lemma matMul_assoc {n : ℕ} (A B C : QMat n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  ext x y
  simp only [matMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => mul_assoc _ _ _

lemma matMul_add_left {n : ℕ} (A B C : QMat n) :
    matMul (matAdd A B) C = matAdd (matMul A C) (matMul B C) := by
  ext x y; simp only [matMul, matAdd, add_mul, Finset.sum_add_distrib]

lemma matMul_add_right {n : ℕ} (A B C : QMat n) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  ext x y; simp only [matMul, matAdd, mul_add, Finset.sum_add_distrib]

lemma matMul_sub_left {n : ℕ} (A B C : QMat n) :
    matMul (matSub A B) C = matSub (matMul A C) (matMul B C) := by
  ext x y; simp only [matMul, matSub, sub_mul, Finset.sum_sub_distrib]

lemma matMul_sub_right {n : ℕ} (A B C : QMat n) :
    matMul A (matSub B C) = matSub (matMul A B) (matMul A C) := by
  ext x y; simp only [matMul, matSub, mul_sub, Finset.sum_sub_distrib]

lemma matMul_smul_left {n : ℕ} (c : ℂ) (A B : QMat n) :
    matMul (matSmul c A) B = matSmul c (matMul A B) := by
  ext x y; simp only [matMul, matSmul, Finset.mul_sum, mul_assoc]

lemma matMul_smul_right {n : ℕ} (c : ℂ) (A B : QMat n) :
    matMul A (matSmul c B) = matSmul c (matMul A B) := by
  ext x y; simp only [matMul, matSmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => by ring

lemma matMul_id_left {n : ℕ} (A : QMat n) : matMul (matId n) A = A := by
  ext x y; simp [matMul, matId]

lemma matMul_id_right {n : ℕ} (A : QMat n) : matMul A (matId n) = A := by
  ext x y; simp [matMul, matId]

lemma matTr_mul_adj_self {n : ℕ} (A : QMat n) :
    matTr (matMul A (matAdj A)) = (frobSq A : ℂ) := by
  simp only [matTr, matMul, matAdj, frobSq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [Complex.star_def, Complex.mul_conj]

lemma matTr_mul_self_herm {n : ℕ} {A : QMat n} (hA : IsHermMat A) :
    matTr (matMul A A) = (frobSq A : ℂ) := by
  have hadj : matAdj A = A := by ext x y; simp [matAdj, hA y x]
  simpa [hadj] using matTr_mul_adj_self A

lemma isHermMat_add {n : ℕ} {A B : QMat n} (hA : IsHermMat A) (hB : IsHermMat B) :
    IsHermMat (matAdd A B) := fun x y => by simp [matAdd, hA x y, hB x y]

lemma isHermMat_sub {n : ℕ} {A B : QMat n} (hA : IsHermMat A) (hB : IsHermMat B) :
    IsHermMat (matSub A B) := fun x y => by simp [matSub, hA x y, hB x y]

lemma isHermMat_smul_real {n : ℕ} (r : ℝ) {A : QMat n} (hA : IsHermMat A) :
    IsHermMat (matSmul (r : ℂ) A) := fun x y => by
  simp [matSmul, hA x y]

lemma isHermMat_id (n : ℕ) : IsHermMat (matId n) := fun x y => by
  simp only [matId]; by_cases h : x = y
  · subst h; simp
  · have h' : y ≠ x := Ne.symm h; simp [h, h']

lemma matAdj_mul {n : ℕ} (A B : QMat n) :
    matAdj (matMul A B) = matMul (matAdj B) (matAdj A) := by
  ext x y
  simp only [matAdj, matMul, star_sum, star_mul]

lemma matAdj_sub {n : ℕ} (A B : QMat n) :
    matAdj (matSub A B) = matSub (matAdj A) (matAdj B) := by
  ext x y; simp [matAdj, matSub]

lemma matAdj_of_herm {n : ℕ} {A : QMat n} (hA : IsHermMat A) : matAdj A = A := by
  ext x y; simp [matAdj, hA y x]

/-- Complex Cauchy–Schwarz on finite sums. -/
lemma normSq_sum_mul_le {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, u i * v i) ≤
      (∑ i ∈ s, Complex.normSq (u i)) * (∑ i ∈ s, Complex.normSq (v i)) := by
  have htri : ‖∑ i ∈ s, u i * v i‖ ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
    calc ‖∑ i ∈ s, u i * v i‖
        ≤ ∑ i ∈ s, ‖u i * v i‖ := norm_sum_le s _
      _ = ∑ i ∈ s, ‖u i‖ * ‖v i‖ := Finset.sum_congr rfl fun i _ => norm_mul _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖u i‖) (fun i => ‖v i‖)
  have hsq : ‖∑ i ∈ s, u i * v i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hns : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := fun z => Complex.normSq_eq_norm_sq z
  simpa only [hns] using le_trans hsq hcs

lemma normSq_innerProd_le {n : ℕ} (φ ψ : QState n) :
    Complex.normSq (innerProd φ ψ) ≤
      (innerProd φ φ).re * (innerProd ψ ψ).re := by
  rw [innerProd, innerProd_self_re, innerProd_self_re]
  have h := normSq_sum_mul_le (Finset.univ : Finset (F2 n)) (fun x => star (φ x)) ψ
  simpa [Complex.star_def, Complex.normSq_conj] using h

/-- Bessel's inequality for two orthogonal vectors `u, v : QState n` of equal norm. -/
lemma bessel_two_orth {n : ℕ} (w u v : QState n) (horth : innerProd u v = 0)
    (hnorm : (innerProd v v).re = (innerProd u u).re) :
    Complex.normSq (innerProd w u) + Complex.normSq (innerProd w v) ≤
      (innerProd w w).re * (innerProd u u).re := by
  by_cases hu : (innerProd u u).re = 0
  · have hu0 : innerProd u u = 0 := by
      rw [innerProd_self_eq_sum_normSq, ← innerProd_self_re, hu]; simp
    have hv0 : innerProd v v = 0 := by
      rw [innerProd_self_eq_sum_normSq, ← innerProd_self_re, hnorm, hu]; simp
    have hu_eq : u = 0 := (innerProd_self_eq_zero_iff u).mp hu0
    have hv_eq : v = 0 := (innerProd_self_eq_zero_iff v).mp hv0
    subst hu_eq; subst hv_eq; simp [innerProd]
  · have hu_pos : 0 < (innerProd u u).re :=
      lt_of_le_of_ne (innerProd_self_re_nonneg u) (Ne.symm hu)
    let N : ℝ := (innerProd u u).re
    let α : ℂ := innerProd u w / (N : ℂ)
    let β : ℂ := innerProd v w / (N : ℂ)
    let r : QState n := w - (α • u + β • v)
    have hr_nn : 0 ≤ (innerProd r r).re := innerProd_self_re_nonneg r
    have huu : innerProd u u = (N : ℂ) := by
      rw [innerProd_self_eq_sum_normSq, ← innerProd_self_re]
    have hvv : innerProd v v = (N : ℂ) := by
      rw [innerProd_self_eq_sum_normSq, ← innerProd_self_re, hnorm]
    have hvu : innerProd v u = 0 := by rw [innerProd_conj_symm, horth, star_zero]
    have hN_ne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu_pos)
    have hexp : innerProd r r = innerProd w w -
        ((Complex.normSq (innerProd w u) / N : ℝ) : ℂ) -
        ((Complex.normSq (innerProd w v) / N : ℝ) : ℂ) := by
      have h1 : innerProd r r = innerProd w w - α * innerProd w u - β * innerProd w v -
          star α * innerProd u w - star β * innerProd v w +
          star α * α * innerProd u u + star α * β * innerProd u v +
          star β * α * innerProd v u + star β * β * innerProd v v := by
        simp only [r, innerProd_sub_right, innerProd_add_right, innerProd_smul_right]
        have hsubL : ∀ a b c : QState n, innerProd (a - b) c = innerProd a c - innerProd b c := by
          intro a b c; simp only [innerProd, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]
        have haddL : ∀ a b c : QState n, innerProd (a + b) c = innerProd a c + innerProd b c := by
          intro a b c; simp only [innerProd, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
        rw [hsubL, hsubL, hsubL, haddL, haddL, haddL, innerProd_smul_left, innerProd_smul_left,
            innerProd_smul_left, innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
        ring
      rw [h1, huu, hvv, horth, hvu]
      have hwu : innerProd u w = star (innerProd w u) := innerProd_conj_symm w u
      have hwv : innerProd v w = star (innerProd w v) := innerProd_conj_symm w v
      have hsuw : star (innerProd u w) = innerProd w u := by rw [hwu, star_star]
      have hsvw : star (innerProd v w) = innerProd w v := by rw [hwv, star_star]
      have hα : α * innerProd w u = ((Complex.normSq (innerProd w u) / N : ℝ) : ℂ) := by
        simp only [α, hwu, Complex.ofReal_div]
        rw [div_mul_eq_mul_div, mul_comm, Complex.star_def, Complex.mul_conj]
      have hβ : β * innerProd w v = ((Complex.normSq (innerProd w v) / N : ℝ) : ℂ) := by
        simp only [β, hwv, Complex.ofReal_div]
        rw [div_mul_eq_mul_div, mul_comm, Complex.star_def, Complex.mul_conj]
      have hα2 : star α * α * (N : ℂ) = ((Complex.normSq (innerProd w u) / N : ℝ) : ℂ) := by
        simp only [α]
        rw [star_div₀, hsuw, hwu]
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_div]
        field_simp [hN_ne]; exact Complex.mul_conj (innerProd w u)
      have hβ2 : star β * β * (N : ℂ) = ((Complex.normSq (innerProd w v) / N : ℝ) : ℂ) := by
        simp only [β]
        rw [star_div₀, hsvw, hwv]
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_div]
        field_simp [hN_ne]; exact Complex.mul_conj (innerProd w v)
      have hsα : star α * innerProd u w = ((Complex.normSq (innerProd w u) / N : ℝ) : ℂ) := by
        simp only [α]
        rw [star_div₀, hsuw, hwu]
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_div]
        rw [div_mul_eq_mul_div, Complex.mul_conj]
      have hsβ : star β * innerProd v w = ((Complex.normSq (innerProd w v) / N : ℝ) : ℂ) := by
        simp only [β]
        rw [star_div₀, hsvw, hwv]
        simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_div]
        rw [div_mul_eq_mul_div, Complex.mul_conj]
      rw [hα, hβ, hα2, hβ2, hsα, hsβ]; ring
    have hre := congr_arg Complex.re hexp
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    have hdiv : (Complex.normSq (innerProd w u) + Complex.normSq (innerProd w v)) / N ≤
        (innerProd w w).re := by rw [add_div]; linarith
    exact (div_le_iff₀ hu_pos).mp hdiv

lemma frobSq_matMul_le {n : ℕ} (A B : QMat n) :
    frobSq (matMul A B) ≤ frobSq A * frobSq B := by
  calc frobSq (matMul A B)
      = ∑ x : F2 n, ∑ y : F2 n, Complex.normSq (∑ z : F2 n, A x z * B z y) := rfl
    _ ≤ ∑ x : F2 n, ∑ y : F2 n,
          (∑ z : F2 n, Complex.normSq (A x z)) * (∑ w : F2 n, Complex.normSq (B w y)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          normSq_sum_mul_le Finset.univ (fun z => A x z) (fun z => B z y)
    _ = (∑ x : F2 n, ∑ z : F2 n, Complex.normSq (A x z)) *
        (∑ y : F2 n, ∑ w : F2 n, Complex.normSq (B w y)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum]
    _ = frobSq A * frobSq B := by congr 1; exact Finset.sum_comm

lemma sqrt_frobSq_add_le {n : ℕ} (A B : QMat n) :
    Real.sqrt (frobSq (matAdd A B)) ≤ Real.sqrt (frobSq A) + Real.sqrt (frobSq B) := by
  have h1 : 0 ≤ frobSq A := frobSq_nonneg A
  have h2 : 0 ≤ frobSq B := frobSq_nonneg B
  have hcross : ∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖ ≤
      Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (F2 n × F2 n))
      (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
    have hns : ∀ z : ℂ, ‖z‖ ^ 2 = Complex.normSq z := fun z => (Complex.normSq_eq_norm_sq z).symm
    simp_rw [hns] at hcs
    have hsum1 : ∑ p : F2 n × F2 n, Complex.normSq (A p.1 p.2) = frobSq A := Fintype.sum_prod_type _
    have hsum2 : ∑ p : F2 n × F2 n, Complex.normSq (B p.1 p.2) = frobSq B := Fintype.sum_prod_type _
    have hsum0 : ∑ p : F2 n × F2 n, ‖A p.1 p.2‖ * ‖B p.1 p.2‖ =
        ∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖ := Fintype.sum_prod_type _
    rw [hsum0, hsum1, hsum2] at hcs
    have hnn : 0 ≤ ∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : (∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖) ^ 2 ≤
        (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]; exact hcs
    nlinarith [mul_nonneg (Real.sqrt_nonneg (frobSq A)) (Real.sqrt_nonneg (frobSq B))]
  have hle : frobSq (matAdd A B) ≤ (Real.sqrt (frobSq A) + Real.sqrt (frobSq B)) ^ 2 := by
    have hexp : frobSq (matAdd A B) ≤
        frobSq A + 2 * (∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖) + frobSq B := by
      have hpt : ∀ x y : F2 n, Complex.normSq (A x y + B x y) ≤
          Complex.normSq (A x y) + 2 * (‖A x y‖ * ‖B x y‖) + Complex.normSq (B x y) := by
        intro x y
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        have hsq : ‖A x y + B x y‖ ^ 2 ≤ (‖A x y‖ + ‖B x y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        linarith
      calc frobSq (matAdd A B)
          = ∑ x : F2 n, ∑ y : F2 n, Complex.normSq (A x y + B x y) := rfl
        _ ≤ ∑ x : F2 n, ∑ y : F2 n,
              (Complex.normSq (A x y) + 2 * (‖A x y‖ * ‖B x y‖) + Complex.normSq (B x y)) :=
            Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
        _ = frobSq A + 2 * (∑ x : F2 n, ∑ y : F2 n, ‖A x y‖ * ‖B x y‖) + frobSq B := by
            simp only [frobSq, Finset.sum_add_distrib, Finset.mul_sum]
    have hsq : (Real.sqrt (frobSq A) + Real.sqrt (frobSq B)) ^ 2 =
        frobSq A + 2 * (Real.sqrt (frobSq A) * Real.sqrt (frobSq B)) + frobSq B := by
      rw [add_sq, Real.sq_sqrt h1, Real.sq_sqrt h2]; ring
    linarith
  exact Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), hle⟩

lemma normSq_matTr_mul_le {n : ℕ} (A B : QMat n) :
    Complex.normSq (matTr (matMul A B)) ≤ frobSq A * frobSq B := by
  have h1 : matTr (matMul A B) = ∑ p : F2 n × F2 n, A p.1 p.2 * B p.2 p.1 := by
    simp only [matTr, matMul, Fintype.sum_prod_type]
  rw [h1]
  have hcs := normSq_sum_mul_le (Finset.univ : Finset (F2 n × F2 n))
    (fun p => A p.1 p.2) (fun p => B p.2 p.1)
  have hA : ∑ p : F2 n × F2 n, Complex.normSq (A p.1 p.2) = frobSq A := Fintype.sum_prod_type _
  have hB : ∑ p : F2 n × F2 n, Complex.normSq (B p.2 p.1) = frobSq B := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rwa [hA, hB] at hcs

lemma matTr_cube_re_sq_le {n : ℕ} (A : QMat n) :
    (matTr (matMul A (matMul A A))).re ^ 2 ≤ (frobSq A) ^ 3 := by
  have hre : (matTr (matMul A (matMul A A))).re ^ 2 ≤
      Complex.normSq (matTr (matMul A (matMul A A))) := by
    rw [Complex.normSq_apply]; nlinarith
  have h1 := normSq_matTr_mul_le A (matMul A A)
  have h2 := frobSq_matMul_le A A
  have hnn : 0 ≤ frobSq A := frobSq_nonneg A
  calc (matTr (matMul A (matMul A A))).re ^ 2
      ≤ frobSq A * frobSq (matMul A A) := le_trans hre h1
    _ ≤ frobSq A * (frobSq A * frobSq A) := mul_le_mul_of_nonneg_left h2 hnn
    _ = (frobSq A) ^ 3 := by ring

lemma matTr_cube_re_le {n : ℕ} (A : QMat n) :
    (matTr (matMul A (matMul A A))).re ≤ (Real.sqrt (frobSq A)) ^ 3 := by
  have hsq := matTr_cube_re_sq_le A
  have hnn : 0 ≤ frobSq A := frobSq_nonneg A
  have hr : ((Real.sqrt (frobSq A)) ^ 3) ^ 2 = (frobSq A) ^ 3 := by
    rw [← pow_mul, mul_comm 3 2, pow_mul, Real.sq_sqrt hnn]
  have h3nn : 0 ≤ (Real.sqrt (frobSq A)) ^ 3 := pow_nonneg (Real.sqrt_nonneg _) 3
  nlinarith

/-- **Unified Exact Off-Diagonal Block Cancellation (Any Rank Projector!)**:
    For ANY Hermitian projector `P` (`P² = P`) and ANY Hermitian `Δ`,
      `frobSq (Δ - P Δ - Δ P) + 2 * frobSq (P Δ - P Δ P) = frobSq Δ`,
    hence `frobSq (Δ - P Δ - Δ P) ≤ frobSq Δ`. -/
lemma frobSq_proj_cancel {n : ℕ} {P Δ : QMat n}
    (hPh : IsHermMat P) (hP2 : matMul P P = P) (hΔh : IsHermMat Δ) :
    frobSq (matSub Δ (matAdd (matMul P Δ) (matMul Δ P))) ≤ frobSq Δ := by
  set M := matSub Δ (matAdd (matMul P Δ) (matMul Δ P))
  set X := matSub (matMul P Δ) (matMul P (matMul Δ P))
  have hMh : IsHermMat M := by
    intro x y
    simp only [M, matSub, matAdd, matMul, star_sub, star_add, star_sum, star_mul]
    rw [hΔh x y]
    have h1 : ∑ z, star (Δ z y) * star (P x z) = ∑ z, Δ y z * P z x :=
      Finset.sum_congr rfl fun z _ => by rw [← hPh x z, ← hΔh z y]
    have h2 : ∑ z, star (P z y) * star (Δ x z) = ∑ z, P y z * Δ z x :=
      Finset.sum_congr rfl fun z _ => by rw [← hPh z y, ← hΔh x z]
    rw [h1, h2]; ring
  have hXadj : matAdj X = matSub (matMul Δ P) (matMul P (matMul Δ P)) := by
    simp only [X, matAdj_sub, matAdj_mul, matAdj_of_herm hPh, matAdj_of_herm hΔh, matMul_assoc]
  -- Helper trace equalities from `P² = P` and cyclicity
  have ht1 : matTr (matMul (matMul Δ P) Δ) = matTr (matMul P (matMul Δ Δ)) := by
    rw [matMul_assoc, matTr_mul_comm Δ, matMul_assoc]
  have ht2 : matTr (matMul (matMul Δ Δ) P) = matTr (matMul P (matMul Δ Δ)) :=
    matTr_mul_comm _ _
  have ht3 : matTr (matMul P (matMul (matMul Δ Δ) P)) = matTr (matMul P (matMul Δ Δ)) := by
    rw [matTr_mul_comm P, matMul_assoc, hP2, matTr_mul_comm]
  have ht4 : matTr (matMul (matMul Δ P) (matMul P Δ)) = matTr (matMul P (matMul Δ Δ)) := by
    rw [matMul_assoc Δ P, ← matMul_assoc P P Δ, hP2, ← matMul_assoc, ht1]
  have ht5 : matTr (matMul (matMul Δ P) (matMul Δ P)) = matTr (matMul (matMul P Δ) (matMul P Δ)) := by
    calc matTr (matMul (matMul Δ P) (matMul Δ P))
        = matTr (matMul Δ (matMul P (matMul Δ P))) := by simp only [matMul_assoc]
      _ = matTr (matMul (matMul P (matMul Δ P)) Δ) := matTr_mul_comm _ _
      _ = matTr (matMul (matMul P Δ) (matMul P Δ)) := by simp only [matMul_assoc]
  -- Expand `Tr(X * X†) = Tr(P Δ²) - Tr((P Δ)²)`
  have hXX : matTr (matMul X (matAdj X)) =
      matTr (matMul P (matMul Δ Δ)) - matTr (matMul (matMul P Δ) (matMul P Δ)) := by
    rw [hXadj]
    simp only [X, matMul_sub_left, matMul_sub_right, matTr_sub]
    have hA : matTr (matMul (matMul P Δ) (matMul Δ P)) = matTr (matMul P (matMul Δ Δ)) := by
      rw [matMul_assoc P Δ, ← matMul_assoc Δ Δ P, ht3]
    have hB' : matTr (matMul (matMul P Δ) (matMul P (matMul Δ P))) =
        matTr (matMul (matMul P Δ) (matMul P Δ)) := by
      calc matTr (matMul (matMul P Δ) (matMul P (matMul Δ P)))
          = matTr (matMul (matMul P (matMul Δ (matMul P Δ))) P) := by simp only [matMul_assoc]
        _ = matTr (matMul P (matMul P (matMul Δ (matMul P Δ)))) := matTr_mul_comm _ _
        _ = matTr (matMul (matMul P P) (matMul Δ (matMul P Δ))) := by rw [← matMul_assoc]
        _ = matTr (matMul (matMul P Δ) (matMul P Δ)) := by rw [hP2]; simp only [matMul_assoc]
    have hC : matTr (matMul (matMul P (matMul Δ P)) (matMul Δ P)) =
        matTr (matMul (matMul P Δ) (matMul P Δ)) := by
      calc matTr (matMul (matMul P (matMul Δ P)) (matMul Δ P))
          = matTr (matMul (matMul P (matMul Δ (matMul P Δ))) P) := by simp only [matMul_assoc]
        _ = matTr (matMul P (matMul P (matMul Δ (matMul P Δ)))) := matTr_mul_comm _ _
        _ = matTr (matMul (matMul P P) (matMul Δ (matMul P Δ))) := by rw [← matMul_assoc]
        _ = matTr (matMul (matMul P Δ) (matMul P Δ)) := by rw [hP2]; simp only [matMul_assoc]
    have hD : matTr (matMul (matMul P (matMul Δ P)) (matMul P (matMul Δ P))) =
        matTr (matMul (matMul P Δ) (matMul P Δ)) := by
      calc matTr (matMul (matMul P (matMul Δ P)) (matMul P (matMul Δ P)))
          = matTr (matMul (matMul P (matMul Δ (matMul (matMul P P) Δ))) P) := by
              simp only [matMul_assoc]
        _ = matTr (matMul (matMul P (matMul Δ (matMul P Δ))) P) := by rw [hP2]
        _ = matTr (matMul P (matMul P (matMul Δ (matMul P Δ)))) := matTr_mul_comm _ _
        _ = matTr (matMul (matMul P P) (matMul Δ (matMul P Δ))) := by rw [← matMul_assoc]
        _ = matTr (matMul (matMul P Δ) (matMul P Δ)) := by rw [hP2]; simp only [matMul_assoc]
    rw [hA, hB', hC, hD]; ring
  -- Expand `Tr(M²) = Tr(Δ²) - 2 Tr(P Δ²) + 2 Tr((P Δ)²)`
  have hMM : matTr (matMul M M) =
      matTr (matMul Δ Δ) - 2 * (matTr (matMul P (matMul Δ Δ)) -
        matTr (matMul (matMul P Δ) (matMul P Δ))) := by
    simp only [M, matMul_sub_left, matMul_sub_right, matMul_add_left, matMul_add_right,
      matTr_sub, matTr_add]
    have ha1 : matTr (matMul Δ (matMul P Δ)) = matTr (matMul P (matMul Δ Δ)) := by
      rw [← matMul_assoc, ht1]
    have ha2 : matTr (matMul Δ (matMul Δ P)) = matTr (matMul P (matMul Δ Δ)) := by
      rw [← matMul_assoc, ht2]
    have ha3 : matTr (matMul (matMul P Δ) Δ) = matTr (matMul P (matMul Δ Δ)) := by
      rw [matMul_assoc]
    have ha4 : matTr (matMul (matMul P Δ) (matMul Δ P)) = matTr (matMul P (matMul Δ Δ)) := by
      rw [matMul_assoc P Δ, ← matMul_assoc Δ Δ P, ht3]
    rw [ha1, ha2, ha3, ha4, ht1, ht4, ht5]; ring
  rw [← hXX, matTr_mul_self_herm hMh, matTr_mul_self_herm hΔh, matTr_mul_adj_self X] at hMM
  have hreal : frobSq M = frobSq Δ - 2 * frobSq X := by
    have := congr_arg Complex.re hMM
    simpa using this
  linarith [frobSq_nonneg X]

/-! ### Pauli Matrices, Parseval, and Squaring -/

lemma card_F2 (n : ℕ) : Fintype.card (F2 n) = 2 ^ n := by
  simp [F2, Fintype.card_pi, ZMod.card]

lemma card_PauliIdx (n : ℕ) : Fintype.card (PauliIdx n) = 2 ^ n * 2 ^ n := by
  rw [Fintype.card_prod, card_F2]

lemma card_PauliIdx_erase_zero (n : ℕ) :
    ((Finset.univ.erase (0 : PauliIdx n)).card : ℝ) = ((2 : ℝ) ^ n) ^ 2 - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_PauliIdx]
  have h1 : 1 ≤ 2 ^ n * 2 ^ n := Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n)
  rw [Nat.cast_sub h1]; push_cast; ring

lemma pauliExpect_zero_re {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    (innerProd ψ (pauliApply 0 ψ)).re = 1 := by
  rw [pauliApply_zero, hunit, Complex.one_re]

def pauliMat {n : ℕ} (p : PauliIdx n) : QMat n :=
  fun x y => if y = x + p.1 then pauliPh p * (chi p.2 x : ℂ) else 0

lemma pauliMat_apply {n : ℕ} (p : PauliIdx n) (ψ : QState n) :
    matApply (pauliMat p) ψ = pauliApply p ψ := by
  ext x
  simp only [matApply, pauliMat, pauliApply]
  rw [Finset.sum_eq_single (x + p.1)]
  · simp [mul_assoc]
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pauliMat_herm {n : ℕ} (p : PauliIdx n) : IsHermMat (pauliMat p) := by
  intro x y
  simp only [pauliMat]
  have hiff : x = y + p.1 ↔ y = x + p.1 := by
    constructor <;> intro h <;> rw [h, f2_add_cancel_right]
  by_cases h : y = x + p.1
  · subst h
    simp only [f2_add_cancel_right, ↓reduceIte, star_mul]
    rw [chi_add_right]; push_cast
    have hph := pauliPh_mul_chi p
    have hsc : star (chi p.2 x : ℂ) = (chi p.2 x : ℂ) := by simp
    rw [hsc, ← hph]; ring
  · have h' : x ≠ y + p.1 := fun hc => h (hiff.mp hc)
    simp [h, h']

lemma pauliMat_mul {n : ℕ} (p q : PauliIdx n) :
    matMul (pauliMat p) (pauliMat q) = matSmul (pauliPhase p q) (pauliMat (p + q)) := by
  ext x y
  simp only [matMul, pauliMat, matSmul, Prod.fst_add, Prod.snd_add]
  rw [Finset.sum_eq_single (x + p.1)]
  · simp only [↓reduceIte]
    have hiff : y = x + p.1 + q.1 ↔ y = x + (p.1 + q.1) := by rw [add_assoc]
    by_cases h : y = x + (p.1 + q.1)
    · subst h
      simp only [add_assoc, ↓reduceIte, pauliPhase, chi_add_left, chi_add_right]
      have hstar := pauliPh_mul_star (p + q)
      calc pauliPh p * (chi p.2 x : ℂ) * (pauliPh q * ((chi q.2 x * chi q.2 p.1 : ℤ) : ℂ))
          = pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * 1 *
              ((chi p.2 x : ℂ) * (chi q.2 x : ℂ)) := by push_cast; ring
        _ = pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * (star (pauliPh (p + q)) * pauliPh (p + q)) *
              ((chi p.2 x : ℂ) * (chi q.2 x : ℂ)) := by rw [hstar]
        _ = _ := by push_cast; ring
    · have h' : y ≠ x + p.1 + q.1 := fun hc => h (hiff.mp hc)
      simp [h, h']
  · intro z _ hz; simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pauliPhase_left_add {n : ℕ} (p q : PauliIdx n) :
    pauliPhase p (q + p) = pauliPhase q p := by
  let e0 : QState n := fun z => if z = 0 then 1 else 0
  have h1 := pauliApply_comp q p (pauliApply (q + p) e0)
  have h2 := pauliApply_comp p (q + p) e0
  rw [h2, pauliApply_smul, show p + (q + p) = q by rw [add_comm q p, pauliIdx_add_cancel_left],
      pauliApply_invol] at h1
  rw [pauliApply_invol] at h1
  have h0 := congr_fun h1 0
  simpa [e0] using h0

lemma pauliPhase_add_right {n : ℕ} (q p : PauliIdx n) :
    pauliPhase q (q + p) = (sympSign q p : ℂ) * pauliPhase q p := by
  let e0 : QState n := fun z => if z = 0 then 1 else 0
  have h1 := pauliApply_comp q (q + p) (pauliApply p e0)
  have h2 := pauliApply_comp (q + p) p e0
  rw [h2, pauliApply_smul, pauliIdx_add_cancel_right, pauliApply_invol] at h1
  rw [pauliIdx_add_cancel_left, pauliApply_invol] at h1
  have h0 := congr_fun h1 0
  simp only [Pi.smul_apply, smul_eq_mul, e0, ↓reduceIte, mul_one] at h0
  rw [← h0, pauliPhase_comm (q + p) p, pauliPhase_left_add]
  congr 1
  simp only [sympSign, symp_add_left, symp_self, add_zero]

def pauliExpand {n : ℕ} (a : PauliIdx n → ℝ) : QMat n :=
  fun x y => ∑ p : PauliIdx n, (a p : ℂ) * pauliMat p x y

lemma pauliExpand_herm {n : ℕ} (a : PauliIdx n → ℝ) : IsHermMat (pauliExpand a) := by
  intro x y
  simp only [pauliExpand, star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun p _ => by rw [pauliMat_herm p x y, Complex.star_def, mul_comm]

lemma pauliExpand_add {n : ℕ} (a b : PauliIdx n → ℝ) :
    pauliExpand (fun p => a p + b p) = matAdd (pauliExpand a) (pauliExpand b) := by
  ext x y; simp only [pauliExpand, matAdd, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

lemma pauliExpand_sub {n : ℕ} (a b : PauliIdx n → ℝ) :
    pauliExpand (fun p => a p - b p) = matSub (pauliExpand a) (pauliExpand b) := by
  ext x y; simp only [pauliExpand, matSub, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]

lemma pauliExpand_smul {n : ℕ} (r : ℝ) (a : PauliIdx n → ℝ) :
    pauliExpand (fun p => r * a p) = matSmul (r : ℂ) (pauliExpand a) := by
  ext x y; simp only [pauliExpand, matSmul, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

lemma pauliExpand_single_zero {n : ℕ} (r : ℝ) :
    pauliExpand (fun p : PauliIdx n => if p = 0 then r else 0) = matSmul (r : ℂ) (matId n) := by
  ext x y
  simp only [pauliExpand, matSmul, matId]
  rw [Finset.sum_eq_single (0 : PauliIdx n)]
  · simp only [↓reduceIte, pauliMat, Prod.fst_zero, Prod.snd_zero, add_zero, pauliPh,
      dot_zero_left, chi_zero_left, Int.cast_one, mul_one]
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := Ne.symm h; simp [h, h']
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma matTr_pauliExpand {n : ℕ} (a : PauliIdx n → ℝ) :
    matTr (pauliExpand a) = (2 : ℂ) ^ n * (a 0 : ℂ) := by
  simp only [matTr, pauliExpand]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (0 : PauliIdx n)]
  · simp only [pauliMat, Prod.fst_zero, Prod.snd_zero, add_zero, ↓reduceIte, pauliPh,
      dot_zero_left, chi_zero_left, Int.cast_one, mul_one, Finset.sum_const, Finset.card_univ,
      card_F2, nsmul_eq_mul]
    push_cast; ring
  · intro p _ hp
    rw [← Finset.mul_sum]
    suffices h0 : ∑ x : F2 n, pauliMat p x x = 0 by rw [h0, mul_zero]
    by_cases hp1 : p.1 = 0
    · have hp2 : p.2 ≠ 0 := fun h2 => hp (Prod.ext hp1 h2)
      simp only [pauliMat, hp1, add_zero, ↓reduceIte, ← Finset.mul_sum]
      have hsc : ∑ x : F2 n, (chi p.2 x : ℂ) = ((∑ x : F2 n, chi x p.2 : ℤ) : ℂ) := by
        rw [Int.cast_sum]; refine Finset.sum_congr rfl fun x _ => by rw [chi_comm]
      rw [hsc, sum_chi]; simp [hp2]
    · refine Finset.sum_eq_zero fun x _ => ?_
      have hne : x ≠ x + p.1 := fun hc => hp1 (by
        have := congr_arg (x + ·) hc; simpa [f2_add_cancel_left, f2_add_self] using this.symm)
      simp [pauliMat, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Pauli–Frobenius Parseval Identity**: `frobSq (pauliExpand a) = 2^n * ∑ p, (a p)²`. -/
lemma frobSq_pauliExpand {n : ℕ} (a : PauliIdx n → ℝ) :
    frobSq (pauliExpand a) = (2 : ℝ) ^ n * ∑ p : PauliIdx n, (a p) ^ 2 := by
  have hentry : ∀ x u : F2 n,
      pauliExpand a x (x + u) =
        ∑ b : F2 n, (a (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ) := by
    intro x u
    simp only [pauliExpand, pauliMat, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single u]
    · refine Finset.sum_congr rfl fun b _ => by simp [mul_assoc]
    · intro u' _ hu'
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : x + u ≠ x + u' := fun h => hu' (by
        have := congr_arg (x + ·) h; simpa [f2_add_cancel_left] using this.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hreindex : frobSq (pauliExpand a) =
      ∑ u : F2 n, ∑ x : F2 n, Complex.normSq (pauliExpand a x (x + u)) := by
    have h1 : ∀ x : F2 n, ∑ y : F2 n, Complex.normSq (pauliExpand a x y) =
        ∑ u : F2 n, Complex.normSq (pauliExpand a x (x + u)) := fun x =>
      (Fintype.sum_equiv (Equiv.addLeft x) _ _ fun _ => rfl).symm
    rw [frobSq]; simp_rw [h1]; exact Finset.sum_comm
  rw [hreindex]
  have hinner : ∀ u : F2 n,
      ∑ x : F2 n, Complex.normSq (pauliExpand a x (x + u)) =
        (2 : ℝ) ^ n * ∑ b : F2 n, (a (u, b)) ^ 2 := by
    intro u
    have hC : ((∑ x : F2 n, Complex.normSq (pauliExpand a x (x + u)) : ℝ) : ℂ) =
        (((2 : ℝ) ^ n * ∑ b : F2 n, (a (u, b)) ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, hentry]
      calc ∑ x : F2 n, (Complex.normSq (∑ b : F2 n, (a (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ)) : ℂ)
          = ∑ x : F2 n, (∑ b : F2 n, (a (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ)) *
              star (∑ b : F2 n, (a (u, b) : ℂ) * pauliPh (u, b) * (chi b x : ℂ)) := by
            refine Finset.sum_congr rfl fun x _ => by rw [Complex.star_def, Complex.mul_conj]
        _ = ∑ b : F2 n, ∑ b' : F2 n,
              ((a (u, b) : ℂ) * pauliPh (u, b) * star ((a (u, b') : ℂ) * pauliPh (u, b'))) *
              (∑ x : F2 n, (chi (b + b') x : ℂ)) := by
            simp only [star_sum]
            conv_lhs =>
              arg 2; ext x
              rw [Finset.sum_mul]
              arg 2; ext b
              rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            have hchi_star : star (chi b' x : ℂ) = (chi b' x : ℂ) := by simp
            rw [chi_add_left, star_mul, hchi_star]
            push_cast; ring
        _ = ∑ b : F2 n, ∑ b' : F2 n,
              ((a (u, b) : ℂ) * pauliPh (u, b) * star ((a (u, b') : ℂ) * pauliPh (u, b'))) *
              (if b = b' then (2 : ℂ) ^ n else 0) := by
            refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
            congr 1
            have hsc : ∑ x : F2 n, (chi (b + b') x : ℂ) =
                ((∑ x : F2 n, chi x (b + b') : ℤ) : ℂ) := by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun x _ => by rw [chi_comm]
            rw [hsc, sum_chi]
            have hiff : b + b' = 0 ↔ b = b' := by
              constructor
              · intro h; have := congr_arg (· + b') h; simpa [f2_add_cancel_right] using this
              · intro h; rw [h, f2_add_self]
            by_cases h : b = b'
            · subst h; simp [f2_add_self]
            · have hne : b + b' ≠ 0 := fun hc => h (hiff.mp hc)
              simp [h, hne]
        _ = ∑ b : F2 n, ((a (u, b) : ℂ) * (a (u, b) : ℂ)) * (2 : ℂ) ^ n := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.sum_eq_single b]
            · simp only [↓reduceIte, star_mul, Complex.star_def, Complex.conj_ofReal]
              have hph := pauliPh_mul_star (u, b)
              calc (a (u, b) : ℂ) * pauliPh (u, b) * (star (pauliPh (u, b)) * (a (u, b) : ℂ)) * (2 : ℂ) ^ n
                  = ((a (u, b) : ℂ) * (a (u, b) : ℂ)) * (star (pauliPh (u, b)) * pauliPh (u, b)) * (2 : ℂ) ^ n := by ring
                _ = _ := by rw [hph, mul_one]
            · intro b' _ hb'; simp [hb'.symm]
            · intro h; exact absurd (Finset.mem_univ b) h
        _ = _ := by
            push_cast; rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
    exact Complex.ofReal_injective hC
  simp_rw [hinner, ← Finset.mul_sum, Fintype.sum_prod_type]

lemma matTr_pauliExpand_mul {n : ℕ} (a b : PauliIdx n → ℝ) :
    matTr (matMul (pauliExpand a) (pauliExpand b)) =
      (2 : ℂ) ^ n * ∑ p : PauliIdx n, ((a p * b p : ℝ) : ℂ) := by
  have hpol : ∀ A B : QMat n, IsHermMat A → IsHermMat B →
      matTr (matMul A B) =
        (((frobSq (matAdd A B) - frobSq A - frobSq B) / 2 : ℝ) : ℂ) := by
    intro A B hA hB
    have hAB : IsHermMat (matAdd A B) := isHermMat_add hA hB
    have h1 := matTr_mul_self_herm hAB
    have h2 := matTr_mul_self_herm hA
    have h3 := matTr_mul_self_herm hB
    have hexp : matTr (matMul (matAdd A B) (matAdd A B)) =
        matTr (matMul A A) + 2 * matTr (matMul A B) + matTr (matMul B B) := by
      rw [matMul_add_left, matMul_add_right, matMul_add_right, matTr_add, matTr_add, matTr_add,
          matTr_mul_comm B A]; ring
    rw [h1, h2, h3] at hexp
    push_cast
    linear_combination (1 / 2 : ℂ) * hexp.symm
  rw [hpol _ _ (pauliExpand_herm a) (pauliExpand_herm b), ← pauliExpand_add,
      frobSq_pauliExpand, frobSq_pauliExpand, frobSq_pauliExpand]
  have hsum : (2 : ℝ) ^ n * ∑ p, (a p + b p) ^ 2 - (2 : ℝ) ^ n * ∑ p, (a p) ^ 2 -
      (2 : ℝ) ^ n * ∑ p, (b p) ^ 2 = 2 * ((2 : ℝ) ^ n * ∑ p, a p * b p) := by
    have : ∑ p : PauliIdx n, (a p + b p) ^ 2 =
        ∑ p : PauliIdx n, (a p) ^ 2 + 2 * ∑ p : PauliIdx n, a p * b p + ∑ p : PauliIdx n, (b p) ^ 2 := by
      simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1; congr 1; refine Finset.sum_congr rfl fun p _ => by ring
    rw [this]; ring
  rw [hsum, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast; rfl

lemma matMul_pauliExpand_self {n : ℕ} (a : PauliIdx n → ℝ) :
    matMul (pauliExpand a) (pauliExpand a) =
      pauliExpand (fun q => ∑ p : PauliIdx n, (pauliPhase q p).re * a p * a (q + p)) := by
  ext x y
  have h1 : matMul (pauliExpand a) (pauliExpand a) x y =
      ∑ p : PauliIdx n, ∑ r : PauliIdx n,
        (a p : ℂ) * (a r : ℂ) * pauliPhase p r * pauliMat (p + r) x y := by
    simp only [matMul, pauliExpand]
    calc ∑ z : F2 n, (∑ p, (a p : ℂ) * pauliMat p x z) * (∑ r, (a r : ℂ) * pauliMat r z y)
        = ∑ p : PauliIdx n, ∑ r : PauliIdx n, (a p : ℂ) * (a r : ℂ) *
            matMul (pauliMat p) (pauliMat r) x y := by
          conv_lhs =>
            arg 2; ext z
            rw [Finset.sum_mul]
            arg 2; ext p
            rw [Finset.mul_sum]
          simp only [matMul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun z _ => by ring
      _ = _ := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
          rw [pauliMat_mul, matSmul]; ring
  rw [h1]
  have h2 : (∑ p : PauliIdx n, ∑ r : PauliIdx n,
        (a p : ℂ) * (a r : ℂ) * pauliPhase p r * pauliMat (p + r) x y) =
      ∑ q : PauliIdx n, (∑ p : PauliIdx n, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase p (q + p)) *
        pauliMat q x y := by
    have hre : ∀ p : PauliIdx n,
        ∑ r : PauliIdx n, (a p : ℂ) * (a r : ℂ) * pauliPhase p r * pauliMat (p + r) x y =
        ∑ q : PauliIdx n, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase p (q + p) * pauliMat q x y := by
      intro p
      refine Fintype.sum_equiv (Equiv.addRight p) _ _ fun r => ?_
      change (a p : ℂ) * (a r : ℂ) * pauliPhase p r * pauliMat (p + r) x y =
        (a p : ℂ) * (a ((r + p) + p) : ℂ) * pauliPhase p ((r + p) + p) * pauliMat (r + p) x y
      rw [pauliIdx_add_cancel_right, add_comm p r]
    simp_rw [hre]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => by rw [Finset.sum_mul]
  rw [h2]; simp only [pauliExpand]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  simp_rw [pauliPhase_left_add]
  have hre_sum : ∑ p : PauliIdx n, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase q p =
      ∑ p : PauliIdx n, (((pauliPhase q p).re * a p * a (q + p) : ℝ) : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => symp q p = 0)]
    conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => symp q p = 0)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hs : symp q p = 0 := (Finset.mem_filter.mp hp).2
      rcases (pauliPhase_re_cases q p).1 hs with hph | hph <;> simp [hph]
    · have hrhs0 : ∑ p ∈ Finset.univ.filter (fun p => ¬symp q p = 0),
          (((pauliPhase q p).re * a p * a (q + p) : ℝ) : ℂ) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hs1 : symp q p = 1 := (zmod2_cases (symp q p)).resolve_left (Finset.mem_filter.mp hp).2
        rw [(pauliPhase_re_cases q p).2 hs1]; simp
      rw [hrhs0]
      let S1 := Finset.univ.filter (fun p : PauliIdx n => ¬symp q p = 0)
      have hneg : ∑ p ∈ S1, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase q p =
          -(∑ p ∈ S1, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase q p) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_bij (fun p _ => q + p) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, symp_add_right,
            symp_self, zero_add] at hp ⊢; exact hp
        · intro p₁ _ p₂ _ h; have := congr_arg (q + ·) h; simpa [pauliIdx_add_cancel_left] using this
        · intro p hp
          refine ⟨q + p, ?_, pauliIdx_add_cancel_left q p⟩
          simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, symp_add_right,
            symp_self, zero_add] at hp ⊢; exact hp
        · intro p hp
          have hs1 : symp q p = 1 := (zmod2_cases (symp q p)).resolve_left (Finset.mem_filter.mp hp).2
          rw [pauliIdx_add_cancel_left, pauliPhase_add_right]
          simp only [sympSign, hs1, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte,
            Int.cast_neg, Int.cast_one]
          ring
      have h2z : (2 : ℂ) * ∑ p ∈ S1, (a p : ℂ) * (a (q + p) : ℂ) * pauliPhase q p = 0 := by
        linear_combination hneg
      exact (mul_eq_zero.mp h2z).resolve_left (by norm_num)
  rw [hre_sum, Complex.ofReal_sum]

def stateProj {n : ℕ} (ψ : QState n) : QMat n :=
  fun x y => ψ x * star (ψ y)

lemma stateProj_herm {n : ℕ} (ψ : QState n) : IsHermMat (stateProj ψ) := fun x y => by
  simp [stateProj, mul_comm]

lemma stateProj_idem {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    matMul (stateProj ψ) (stateProj ψ) = stateProj ψ := by
  ext x y; simp only [matMul, stateProj]
  have : ∑ z : F2 n, ψ x * star (ψ z) * (ψ z * star (ψ y)) =
      ψ x * star (ψ y) * innerProd ψ ψ := by
    simp only [innerProd, Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
  rw [this, hunit, mul_one]

lemma stateProj_eq_pauliExpand {n : ℕ} (ψ : QState n) :
    matSmul ((2 : ℂ) ^ n) (stateProj ψ) =
      pauliExpand (fun p => (innerProd ψ (pauliApply p ψ)).re) := by
  ext x y
  let ey : QState n := fun z => if z = y then 1 else 0
  have hcomp := congr_fun (pauli_completeness ψ ey) x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomp
  have hin : innerProd ψ ey = star (ψ y) := by
    simp only [innerProd, ey]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ y) h
  rw [hin] at hcomp
  simp only [matSmul, stateProj, pauliExpand]
  rw [show (2 : ℂ) ^ n * (ψ x * star (ψ y)) = (2 : ℂ) ^ n * star (ψ y) * ψ x by ring, ← hcomp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [innerProd_pauliApply_self_real]
  congr 1; simp only [pauliApply, pauliMat, ey]
  by_cases h : y = x + p.1
  · subst h; simp
  · have h' : x + p.1 ≠ y := Ne.symm h; simp [h, h']

lemma matTr_stateProj_mul {n : ℕ} (ψ : QState n) (A : QMat n) :
    matTr (matMul (stateProj ψ) A) = innerProd ψ (matApply A ψ) := by
  simp only [matTr, matMul, stateProj, innerProd, matApply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma matTr_stateProj_mul_sq {n : ℕ} (ψ : QState n) {A : QMat n} (hA : IsHermMat A) :
    matTr (matMul (stateProj ψ) (matMul A A)) =
      innerProd (matApply A ψ) (matApply A ψ) := by
  symm
  simp only [innerProd, matApply, star_sum, star_mul]
  calc ∑ z : F2 n, (∑ x : F2 n, star (ψ x) * star (A z x)) * (∑ y : F2 n, A z y * ψ y)
      = ∑ z : F2 n, ∑ x : F2 n, ∑ y : F2 n, ψ y * star (ψ x) * (A x z * A z y) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by rw [← hA z x]; ring
    _ = ∑ y : F2 n, ∑ x : F2 n, ψ y * star (ψ x) * ∑ z : F2 n, A x z * A z y := by
        rw [Finset.sum_comm]
        refine Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm) ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]
    _ = matTr (matMul (stateProj ψ) (matMul A A)) := by
        simp only [matTr, matMul, stateProj]

/-! ### Section 2: Parity, Non-Squareness, and Exact `D² → ε` Conversions -/

/-- Exact Welch/SIC excess identity:
    `pauliMoment4 n ψ - 2 d / (d + 1) = ∑_{p ≠ 0} (c_p² - 1 / (d + 1))²`. -/
lemma pauliMoment4_sub_welch {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    pauliMoment4 n ψ - 2 * d / (d + 1) =
      ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), ((c p) ^ 2 - 1 / (d + 1)) ^ 2 := by
  intro d c
  have hd_pos : 0 < d := by positivity
  have hd1_ne : d + 1 ≠ 0 := by linarith
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hsum_sq : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (c p) ^ 2 = d - 1 := by
    have h := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))] at h
    have hns : ∀ p, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
      fun p => innerProd_pauliApply_self_normSq p ψ
    simp_rw [hns, hc0] at h
    linarith
  have hcard : ((Finset.univ.erase (0 : PauliIdx n)).card : ℝ) = d ^ 2 - 1 :=
    card_PauliIdx_erase_zero n
  have hmom : pauliMoment4 n ψ = 1 + ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (c p) ^ 4 := by
    rw [pauliMoment4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have hns : ∀ p, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2 = (c p) ^ 4 := fun p => by
      rw [innerProd_pauliApply_self_normSq]; ring
    simp_rw [hns, hc0]; ring
  have hexp : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), ((c p) ^ 2 - 1 / (d + 1)) ^ 2 =
      (∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (c p) ^ 4) -
      (2 / (d + 1)) * (∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (c p) ^ 2) +
      ((Finset.univ.erase (0 : PauliIdx n)).card : ℝ) * (1 / (d + 1)) ^ 2 := by
    have : ∀ p, ((c p) ^ 2 - 1 / (d + 1)) ^ 2 =
        (c p) ^ 4 - (2 / (d + 1)) * (c p) ^ 2 + (1 / (d + 1)) ^ 2 := fun p => by ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [hmom, hexp, hsum_sq, hcard]
  field_simp [hd1_ne]; ring

/-- Elementary bound `ε ≥ D² / (d + 1)` where `D² = ∑_{p ≠ 0} (|c_p| - r)²`. -/
lemma eps_ge_div_d_add_one {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let r : ℝ := 1 / Real.sqrt (d + 1)
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    (∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (|c p| - r) ^ 2) / (d + 1) ≤
      pauliMoment4 n ψ - 2 * d / (d + 1) := by
  intro d r c
  rw [pauliMoment4_sub_welch hunit, Finset.sum_div]
  refine Finset.sum_le_sum fun p _ => ?_
  have hd_pos : 0 < d := by positivity
  have hr_pos : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d + 1)]
  have hfac : (c p) ^ 2 - 1 / (d + 1) = (|c p| - r) * (|c p| + r) := by
    rw [← hr2]; nlinarith [sq_abs (c p)]
  rw [hfac, mul_pow]
  have hge : r ^ 2 ≤ (|c p| + r) ^ 2 := by
    have : r ≤ |c p| + r := le_add_of_nonneg_left (abs_nonneg _)
    nlinarith
  have h1 : (|c p| - r) ^ 2 * r ^ 2 ≤ (|c p| - r) ^ 2 * (|c p| + r) ^ 2 :=
    mul_le_mul_of_nonneg_left hge (sq_nonneg _)
  rwa [hr2, mul_one_div] at h1

/-- **Concave Subadditivity Bound (`D² ≤ 1 / (d + 1)`)**:
    When `D² = ∑_{p ≠ 0} (|c_p| - r)² ≤ r² = 1 / (d + 1)`,
      `pauliMoment4 n ψ - 2 d / (d + 1) ≥ (2 r √(D²) - D²)²`.
    (Nearly `4×` sharper than `D² / (d + 1)`!) -/
lemma eps_ge_concave_of_le_r2 {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ)
    {D2 : ℝ} (hD2_nn : 0 ≤ D2)
    (hD2_le : D2 ≤ ∑ p ∈ Finset.univ.erase (0 : PauliIdx n),
      (|(innerProd ψ (pauliApply p ψ)).re| - 1 / Real.sqrt ((2 : ℝ) ^ n + 1)) ^ 2)
    (hD2_small : D2 ≤ 1 / ((2 : ℝ) ^ n + 1)) :
    (2 * (1 / Real.sqrt ((2 : ℝ) ^ n + 1)) * Real.sqrt D2 - D2) ^ 2 ≤
      pauliMoment4 n ψ - 2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1) := by
  set d : ℝ := (2 : ℝ) ^ n
  set r : ℝ := 1 / Real.sqrt (d + 1)
  set c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set S := Finset.univ.erase (0 : PauliIdx n)
  have hd_pos : 0 < d := by positivity
  have hr_pos : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d + 1)]
  rw [pauliMoment4_sub_welch hunit]
  -- Let `ε := ∑_{p ∈ S} ((c p)² - r²)²`. If `ε ≥ r⁴`, we're done immediately since `(2r√D2 - D2)² ≤ r⁴`!
  set eps := ∑ p ∈ S, ((c p) ^ 2 - 1 / (d + 1)) ^ 2
  by_cases hbig : r ^ 4 ≤ eps
  · have hbound : (2 * r * Real.sqrt D2 - D2) ^ 2 ≤ r ^ 4 := by
      have hsqD : Real.sqrt D2 ≤ r := by
        rw [Real.sqrt_le_iff]; exact ⟨le_of_lt hr_pos, by rw [hr2]; exact hD2_small⟩
      have hnn1 : 0 ≤ 2 * r * Real.sqrt D2 - D2 := by
        have h1 : D2 = Real.sqrt D2 * Real.sqrt D2 := (Real.mul_self_sqrt hD2_nn).symm
        nlinarith [Real.sqrt_nonneg D2]
      have hle1 : 2 * r * Real.sqrt D2 - D2 ≤ r ^ 2 := by
        have h1 : D2 = Real.sqrt D2 * Real.sqrt D2 := (Real.mul_self_sqrt hD2_nn).symm
        nlinarith [sq_nonneg (r - Real.sqrt D2)]
      nlinarith
    exact le_trans hbound hbig
  · push Not at hbig
    set T := ∑ p ∈ S, (|c p| - r) ^ 2
    have hT_le : T ≤ r ^ 2 := by
      have h1 := eps_ge_div_d_add_one hunit
      dsimp only at h1
      rw [pauliMoment4_sub_welch hunit] at h1
      have h2 : T * r ^ 2 ≤ eps := by
        have : T / (d + 1) = T * r ^ 2 := by rw [hr2]; ring
        linarith
      nlinarith
    have hT_nn : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hstep1 : (2 * r * Real.sqrt T - T) ^ 2 ≤ eps := by
      have hfac_eq : (2 * r * Real.sqrt T - T) ^ 2 = T * (2 * r - Real.sqrt T) ^ 2 := by
        calc (2 * r * Real.sqrt T - T) ^ 2
            = 4 * r ^ 2 * Real.sqrt T ^ 2 - 4 * r * Real.sqrt T * T + T ^ 2 := by ring
          _ = 4 * r ^ 2 * T - 4 * r * Real.sqrt T * T + T * Real.sqrt T ^ 2 := by
              rw [Real.sq_sqrt hT_nn]; ring
          _ = T * (2 * r - Real.sqrt T) ^ 2 := by ring
      rw [hfac_eq, Finset.sum_mul]
      refine Finset.sum_le_sum fun p hp => ?_
      have hu_le : |(|c p| - r)| ≤ Real.sqrt T := by
        have h1 : (|c p| - r) ^ 2 ≤ T :=
          Finset.single_le_sum (f := fun q => (|c q| - r) ^ 2) (fun q _ => sq_nonneg _) hp
        have h2 : |(|c p| - r)| = Real.sqrt ((|c p| - r) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        rw [h2]; exact Real.sqrt_le_sqrt h1
      have h2r : 0 ≤ 2 * r - Real.sqrt T := by
        have : Real.sqrt T ≤ r := by rw [Real.sqrt_le_iff]; exact ⟨le_of_lt hr_pos, hT_le⟩
        linarith
      have hlow : 2 * r - Real.sqrt T ≤ |c p| + r := by
        have h1 : -(|c p| - r) ≤ |(|c p| - r)| := neg_le_abs _
        linarith
      have hsq_low : (2 * r - Real.sqrt T) ^ 2 ≤ (|c p| + r) ^ 2 := by nlinarith
      have hfac : ((c p) ^ 2 - 1 / (d + 1)) ^ 2 = (|c p| - r) ^ 2 * (|c p| + r) ^ 2 := by
        rw [← hr2]; nlinarith [sq_abs (c p)]
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hsq_low (sq_nonneg _)
    have hmono : (2 * r * Real.sqrt D2 - D2) ^ 2 ≤ (2 * r * Real.sqrt T - T) ^ 2 := by
      have hsD_le_sT : Real.sqrt D2 ≤ Real.sqrt T := Real.sqrt_le_sqrt hD2_le
      have hsT_le_r : Real.sqrt T ≤ r := by rw [Real.sqrt_le_iff]; exact ⟨le_of_lt hr_pos, hT_le⟩
      have hdiff : (2 * r * Real.sqrt T - T) - (2 * r * Real.sqrt D2 - D2) =
          (Real.sqrt T - Real.sqrt D2) * (2 * r - (Real.sqrt T + Real.sqrt D2)) := by
        linear_combination Real.sq_sqrt hT_nn - Real.sq_sqrt hD2_nn
      have hnn_D : 0 ≤ 2 * r * Real.sqrt D2 - D2 := by
        have : Real.sqrt D2 ≤ r := le_trans hsD_le_sT hsT_le_r
        have hD_eq : D2 = Real.sqrt D2 * Real.sqrt D2 := (Real.mul_self_sqrt hD2_nn).symm
        nlinarith [Real.sqrt_nonneg D2]
      have hle : 2 * r * Real.sqrt D2 - D2 ≤ 2 * r * Real.sqrt T - T := by
        nlinarith [Real.sqrt_nonneg D2]
      nlinarith
    exact le_trans hmono hstep1

/-- **1-Line Hölder Conversion (`L1 → pauliMoment4`)**:
    For any unit state `ψ` and any `D2 ≤ ∑_{p ≠ 0} (|c_p| - r)²` with `D2 < 2(d - 1)`,
      `pauliMoment4 n ψ ≥ 1 + (d - 1)³ / ((d - 1) √(d + 1) - (√(d + 1) / 2) D2)²`. -/
lemma pauliMoment4_ge_holder_of_D2 {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ)
    {D2 : ℝ} (hD2_le : D2 ≤ ∑ p ∈ Finset.univ.erase (0 : PauliIdx n),
      (|(innerProd ψ (pauliApply p ψ)).re| - 1 / Real.sqrt ((2 : ℝ) ^ n + 1)) ^ 2)
    (hD2_lt : D2 < 2 * ((2 : ℝ) ^ n - 1)) :
    let d : ℝ := (2 : ℝ) ^ n
    let L : ℝ := (d - 1) * Real.sqrt (d + 1) - (Real.sqrt (d + 1) / 2) * D2
    1 + (d - 1) ^ 3 / L ^ 2 ≤ pauliMoment4 n ψ := by
  intro d L
  set c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set S := Finset.univ.erase (0 : PauliIdx n)
  set r : ℝ := 1 / Real.sqrt (d + 1)
  have hd_pos : 0 < d := by positivity
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr (by linarith)
  have hr_pos : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / (d + 1) := by
    simp only [r, div_pow, one_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d + 1)]
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hsum2 : ∑ p ∈ S, (c p) ^ 2 = d - 1 := by
    have h := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))] at h
    have hns : ∀ p, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (c p) ^ 2 :=
      fun p => innerProd_pauliApply_self_normSq p ψ
    simp_rw [hns, hc0] at h; linarith
  have hcard : (S.card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  -- Exact identity: `∑_{p ∈ S} (|c p| - r)² = 2(d - 1) - 2 r ∑_{p ∈ S} |c p|`!
  have hL1_eq : ∑ p ∈ S, (|c p| - r) ^ 2 = 2 * (d - 1) - 2 * r * ∑ p ∈ S, |c p| := by
    have hexp : ∑ p ∈ S, (|c p| - r) ^ 2 =
        (∑ p ∈ S, (c p) ^ 2) - 2 * r * (∑ p ∈ S, |c p|) + (S.card : ℝ) * r ^ 2 := by
      have : ∀ p, (|c p| - r) ^ 2 = (c p) ^ 2 - 2 * r * |c p| + r ^ 2 := fun p => by
        nlinarith [sq_abs (c p)]
      simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
    rw [hexp, hsum2, hcard, hr2]
    have hd1_ne : d + 1 ≠ 0 := by linarith
    field_simp [hd1_ne]; ring
  set L1 := ∑ p ∈ S, |c p|
  have hL1_nn : 0 ≤ L1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hL1_le : L1 ≤ L := by
    have h1 : 2 * r * L1 ≤ 2 * (d - 1) - D2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (show 0 < Real.sqrt (d + 1) / 2 by positivity))
    have hmul : Real.sqrt (d + 1) / 2 * (2 * r * L1) = L1 := by
      simp only [r]; field_simp [ne_of_gt hs_pos]
    rw [hmul] at h2
    have hrhs : Real.sqrt (d + 1) / 2 * (2 * (d - 1) - D2) = L := by simp only [L]; ring
    linarith
  have hL_pos : 0 < L := by
    have : L = (Real.sqrt (d + 1) / 2) * (2 * (d - 1) - D2) := by simp only [L]; ring
    rw [this]; exact mul_pos (by positivity) (by linarith)
  -- Cauchy–Schwarz twice proves Hölder `(∑ c_p²)³ ≤ (∑ |c_p|)² (∑ c_p⁴)` in 5 lines!
  -- Wait: `∑ c_p² = ∑ √|c_p| * |c_p|^(3/2)` ->
  --   `(∑ c_p²)² ≤ (∑ |c_p|) * (∑ |c_p|³)` AND `(∑ |c_p|³)² ≤ (∑ c_p²) * (∑ c_p⁴)`!
  --   Combine: `(∑ c_p²)⁴ ≤ (∑ |c_p|)² * (∑ c_p²) * (∑ c_p⁴)` -> cancel `∑ c_p²`!
  set S3 := ∑ p ∈ S, |c p| ^ 3
  set S4 := ∑ p ∈ S, (c p) ^ 4
  have hcs1 : (∑ p ∈ S, (c p) ^ 2) ^ 2 ≤ L1 * S3 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => Real.sqrt |c p|)
      (fun p => Real.sqrt |c p| * |c p|)
    have hlhs : ∑ p ∈ S, Real.sqrt |c p| * (Real.sqrt |c p| * |c p|) = ∑ p ∈ S, (c p) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have : Real.sqrt |c p| * (Real.sqrt |c p| * |c p|) = (Real.sqrt |c p| * Real.sqrt |c p|) * |c p| := by ring
      rw [this, Real.mul_self_sqrt (abs_nonneg _), ← sq, sq_abs]
    have hr1 : ∑ p ∈ S, (Real.sqrt |c p|) ^ 2 = L1 :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (abs_nonneg _)
    have hr2' : ∑ p ∈ S, (Real.sqrt |c p| * |c p|) ^ 2 = S3 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]; ring
    rwa [hlhs, hr1, hr2'] at h
  have hcs2 : S3 ^ 2 ≤ (∑ p ∈ S, (c p) ^ 2) * S4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => |c p|) (fun p => (c p) ^ 2)
    have hlhs : ∑ p ∈ S, |c p| * (c p) ^ 2 = S3 :=
      Finset.sum_congr rfl fun p _ => by rw [← sq_abs (c p)]; ring
    have hr1 : ∑ p ∈ S, |c p| ^ 2 = ∑ p ∈ S, (c p) ^ 2 :=
      Finset.sum_congr rfl fun p _ => sq_abs _
    have hr2' : ∑ p ∈ S, ((c p) ^ 2) ^ 2 = S4 :=
      Finset.sum_congr rfl fun p _ => by ring
    rwa [hlhs, hr1, hr2'] at h
  have hS4_nn : 0 ≤ S4 := Finset.sum_nonneg fun _ _ => by positivity
  have hS3_nn : 0 ≤ S3 := Finset.sum_nonneg fun _ _ => by positivity
  have hholder : (d - 1) ^ 3 ≤ L ^ 2 * S4 := by
    rw [hsum2] at hcs1 hcs2
    by_cases hd1 : d - 1 = 0
    · rw [hd1, zero_pow (by norm_num)]; positivity
    · have hd1_pos : 0 < d - 1 := by
        have h1 : (1 : ℝ) ≤ d := by
          have : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          exact this
        exact lt_of_le_of_ne (by linarith) (Ne.symm hd1)
      have h4 : (d - 1) ^ 4 ≤ L1 ^ 2 * ((d - 1) * S4) := by
        have hsq1 : ((d - 1) ^ 2) ^ 2 ≤ (L1 * S3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcs1 2
        calc (d - 1) ^ 4 = ((d - 1) ^ 2) ^ 2 := by ring
          _ ≤ L1 ^ 2 * S3 ^ 2 := by rw [mul_pow] at hsq1; exact hsq1
          _ ≤ L1 ^ 2 * ((d - 1) * S4) := mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
      have h3 : (d - 1) ^ 3 ≤ L1 ^ 2 * S4 := by nlinarith
      have hLL : L1 ^ 2 ≤ L ^ 2 := by nlinarith
      calc (d - 1) ^ 3 ≤ L1 ^ 2 * S4 := h3
        _ ≤ L ^ 2 * S4 := mul_le_mul_of_nonneg_right hLL hS4_nn
  have hmom : pauliMoment4 n ψ = 1 + S4 := by
    rw [pauliMoment4, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have hns : ∀ p, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2 = (c p) ^ 4 := fun p => by
      rw [innerProd_pauliApply_self_normSq]; ring
    simp_rw [hns, hc0]; ring
  rw [hmom]
  have hdiv : (d - 1) ^ 3 / L ^ 2 ≤ S4 := (div_le_iff₀ (sq_pos_of_pos hL_pos)).mpr (by linarith)
  linarith

/-! ### Section 3: Parity & Non-Squareness in `W(2n-1, 2)` and Theorem 5 (Universal All `n ≠ 1, 3`) -/

/-- `2^n + 1` is a perfect square only at `n = 3` (for `n ≥ 1`). -/
lemma two_pow_add_one_ne_sq {n : ℕ} (hn : n = 2 ∨ 4 ≤ n) (k : ℤ) :
    (2 : ℤ) ^ n + 1 ≠ k ^ 2 := by
  intro hk
  have hk_nat : 2 ^ n + 1 = k.natAbs ^ 2 := by zify; simpa [sq_abs] using hk
  set m := k.natAbs
  have hm_ge1 : 1 ≤ m := by
    by_contra h; push Not at h
    have hm0 : m = 0 := by omega
    rw [hm0] at hk_nat; norm_num at hk_nat
  have hprod : (m - 1) * (m + 1) = 2 ^ n := by
    zify [hm_ge1]; linarith [show (2 : ℤ) ^ n + 1 = (m : ℤ) ^ 2 by exact_mod_cast hk_nat]
  have hdvd1 : m - 1 ∣ 2 ^ n := ⟨m + 1, hprod.symm⟩
  have hdvd2 : m + 1 ∣ 2 ^ n := ⟨m - 1, by rw [mul_comm]; exact hprod.symm⟩
  rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd1 hdvd2
  obtain ⟨a, _, ha⟩ := hdvd1
  obtain ⟨b, _, hb⟩ := hdvd2
  have hdiff : 2 ^ b - 2 ^ a = 2 := by omega
  have hab : a + b = n := by
    have : 2 ^ (a + b) = 2 ^ n := by rw [pow_add, ← ha, ← hb, hprod]
    exact Nat.pow_right_injective (by norm_num : 1 < 2) this
  rcases a with _ | _ | a'
  · simp at ha
    have hb3 : 2 ^ b = 3 := by omega
    rcases b with _ | b'
    · norm_num at hb3
    · have : 2 ∣ 2 ^ (b' + 1) := ⟨2 ^ b', by rw [pow_succ]; ring⟩
      omega
  · simp at ha
    have hb4 : 2 ^ b = 4 := by omega
    have hb2 : b = 2 := by
      have : 2 ^ b = 2 ^ 2 := by omega
      exact Nat.pow_right_injective (by norm_num : 1 < 2) this
    omega
  · have h4a : 4 ∣ 2 ^ (a' + 2) := ⟨2 ^ a', by rw [pow_add]; ring⟩
    have hb_gt : a' + 2 ≤ b := by
      by_contra h; push Not at h
      have hlt : 2 ^ b < 2 ^ (a' + 2) := Nat.pow_lt_pow_right (by norm_num) h
      have hz : 2 ^ b - 2 ^ (a' + 2) = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      rw [hz] at hdiff; norm_num at hdiff
    have h4b : 4 ∣ 2 ^ b := dvd_trans h4a (Nat.pow_dvd_pow 2 hb_gt)
    have h4diff : 4 ∣ 2 ^ b - 2 ^ (a' + 2) := Nat.dvd_sub h4b h4a
    rw [hdiff] at h4diff; omega

/-- For `n ∈ {2} ∪ {4, 5, …}` and any odd integer `m = 2k + 1`,
    `|(2^(n-1) - 1)² (2^n + 1) - m²| ≥ 4`. -/
lemma odd_sq_dist_ge_four {n : ℕ} (hn : n = 2 ∨ 4 ≤ n) (k : ℤ) :
    4 ≤ |(((2 : ℤ) ^ (n - 1) - 1) ^ 2 * ((2 : ℤ) ^ n + 1) - (2 * k + 1) ^ 2)| := by
  set a : ℤ := (2 : ℤ) ^ (n - 1) - 1
  set N : ℤ := a ^ 2 * ((2 : ℤ) ^ n + 1)
  set m : ℤ := 2 * k + 1
  have hne : N ≠ m ^ 2 := by
    intro heq
    have ha_pos : 0 < a := by
      rcases hn with rfl | hn4
      · norm_num [a]
      · have : (2 : ℤ) ^ 3 ≤ (2 : ℤ) ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
    have ha_dvd : a ∣ m := by
      have h1 : a ^ 2 ∣ m ^ 2 := ⟨(2 : ℤ) ^ n + 1, by linarith⟩
      exact (Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h1
    obtain ⟨q, hq⟩ := ha_dvd
    have hq2 : (2 : ℤ) ^ n + 1 = q ^ 2 := by
      have : a ^ 2 * ((2 : ℤ) ^ n + 1) = a ^ 2 * q ^ 2 := by rw [hq] at heq; linarith
      exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt ha_pos)) this
    exact two_pow_add_one_ne_sq hn q hq2
  have hmod : (N - m ^ 2) % 4 = 0 := by
    have hm_mod : m ^ 2 % 4 = 1 := by
      have : m ^ 2 = 4 * (k * k + k) + 1 := by ring
      omega
    have hN_mod : N % 4 = 1 := by
      have h4d : 4 ∣ (2 : ℤ) ^ n := by
        have h2le : 2 ≤ n := by omega
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h2le
        exact ⟨(2 : ℤ) ^ r, by rw [pow_add]; ring⟩
      obtain ⟨t, ht⟩ := h4d
      have ha_odd : a % 2 = 1 := by
        have h2d : 2 ∣ (2 : ℤ) ^ (n - 1) := by
          have h1le : 1 ≤ n - 1 := by omega
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le h1le
          rw [hr]; exact ⟨(2 : ℤ) ^ r, by rw [pow_add]; ring⟩
        obtain ⟨u, hu⟩ := h2d
        have : a = 2 * u - 1 := by omega
        omega
      have ha2_mod : a ^ 2 % 4 = 1 := by
        obtain ⟨v, hv⟩ : ∃ v : ℤ, a = 2 * v + 1 := ⟨a / 2, by omega⟩
        have : a ^ 2 = 4 * (v * v + v) + 1 := by rw [hv]; ring
        omega
      obtain ⟨w, hw⟩ : ∃ w : ℤ, a ^ 2 = 4 * w + 1 := ⟨a ^ 2 / 4, by omega⟩
      have : N = 4 * (a ^ 2 * t + w) + 1 := by
        calc N = a ^ 2 * (4 * t + 1) := by simp only [N, ht]
          _ = 4 * (a ^ 2 * t) + a ^ 2 := by ring
          _ = 4 * (a ^ 2 * t + w) + 1 := by rw [hw]; ring
      omega
    omega
  rcases le_total 0 (N - m ^ 2) with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_nonpos h]; omega

/-- Number of commuting non-trivial partners of `q ≠ 0` is `2^(2n-1) - 2`. -/
lemma card_commPartners {n : ℕ} (hn : 2 ≤ n) {q : PauliIdx n} (hq : q ≠ 0) :
    ((Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ symp q p = 0).card) =
      2 * (4 ^ (n - 1) - 1) := by
  -- Use `sum_sympSign_submodule` on `H = span {q}`! Wait: direct character sum `∑ p, sympSign q p = 0`!
  have hsum : ∑ p : PauliIdx n, sympSign q p = 0 := by
    -- Pick `v` with `symp q v = 1`!
    have hex : ∃ v : PauliIdx n, symp q v = 1 := by
      by_cases h1 : q.1 ≠ 0
      · have hexi : ∃ i : Fin n, q.1 i ≠ 0 := by
          by_contra h; push Not at h; exact h1 (funext h)
        obtain ⟨i, hi⟩ := hexi
        refine ⟨(0, eVec i), ?_⟩
        simp only [symp, dot_zero_right, add_zero, dot_eVec_right]
        exact (zmod2_cases (q.1 i)).resolve_left hi
      · push Not at h1
        have h2 : q.2 ≠ 0 := fun hc => hq (Prod.ext h1 hc)
        have hexi : ∃ i : Fin n, q.2 i ≠ 0 := by
          by_contra h; push Not at h; exact h2 (funext h)
        obtain ⟨i, hi⟩ := hexi
        refine ⟨(eVec i, 0), ?_⟩
        simp only [symp, dot_zero_right, zero_add, dot_eVec_right]
        exact (zmod2_cases (q.2 i)).resolve_left hi
    obtain ⟨v, hv⟩ := hex
    have hshift : ∑ p : PauliIdx n, sympSign q p = ∑ p : PauliIdx n, sympSign q (p + v) :=
      (Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl).symm
    have hneg : ∑ p : PauliIdx n, sympSign q (p + v) = -(∑ p : PauliIdx n, sympSign q p) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => by rw [sympSign_add_right]; simp [sympSign, hv]
    linarith
  let A := Finset.univ.filter fun p : PauliIdx n => symp q p = 0
  let B := Finset.univ.filter fun p : PauliIdx n => ¬symp q p = 0
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : PauliIdx n => symp q p = 0)
    (fun p => sympSign q p)
  have hA : ∑ p ∈ A, sympSign q p = (A.card : ℤ) := by
    have : ∀ p ∈ A, sympSign q p = 1 := fun p hp => by simp [sympSign, (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB : ∑ p ∈ B, sympSign q p = -(B.card : ℤ) := by
    have : ∀ p ∈ B, sympSign q p = -1 := fun p hp => by simp [sympSign, (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hAB : A.card + B.card = 4 ^ n := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (PauliIdx n)))
      (p := fun p => symp q p = 0)
    have h2 : (Finset.univ : Finset (PauliIdx n)).card = 4 ^ n := by
      rw [Finset.card_univ, card_PauliIdx]
      calc 2 ^ n * 2 ^ n = (2 * 2) ^ n := (mul_pow 2 2 n).symm
        _ = 4 ^ n := by norm_num
    exact h1.trans h2
  have hA_card : A.card = 2 * 4 ^ (n - 1) := by
    have h4 : 4 ^ n = 4 * 4 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    have heq : (A.card : ℤ) = (B.card : ℤ) := by linarith
    omega
  -- Peel `0` and `q` from `A`!
  have h0A : (0 : PauliIdx n) ∈ A := by simp [A, symp_zero_right]
  have hqA : q ∈ A := by simp [A, symp_self]
  have hset : (Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ symp q p = 0) =
      (A.erase 0).erase q := by
    ext p; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]; tauto
  rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hq, hqA⟩),
      Finset.card_erase_of_mem h0A, hA_card]
  have hpos : 1 ≤ 4 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- Half-sum parity lemma: if `S` is a finite set with a fixed-point-free involution `ι`
    preserving `f : α → ℤ` with `f a ∈ {-1, 1}`, and `S.card = 2 * m`, then
    `∑ a ∈ S, f a = 2 * T` for an integer `T` with `T % 2 = (m : ℤ) % 2`! -/
lemma sum_invol_parity {α : Type*} [Fintype α] (S : Finset α) (ι : α → α) (f : α → ℤ)
    (hmem : ∀ a ∈ S, ι a ∈ S) (hinvol : ∀ a ∈ S, ι (ι a) = a) (hne : ∀ a ∈ S, ι a ≠ a)
    (hf_inv : ∀ a ∈ S, f (ι a) = f a) (hf_pm : ∀ a ∈ S, f a = 1 ∨ f a = -1)
    (m : ℕ) (hcard : S.card = 2 * m) :
    ∃ T : ℤ, ∑ a ∈ S, f a = 2 * T ∧ T % 2 = (m : ℤ) % 2 := by
  let e := Fintype.equivFin α
  let S_lt := S.filter fun a => (e a : ℕ) < (e (ι a) : ℕ)
  let S_gt := S.filter fun a => ¬((e a : ℕ) < (e (ι a) : ℕ))
  have hbij : ∑ a ∈ S_gt, f a = ∑ a ∈ S_lt, f a := by
    refine Finset.sum_bij (fun a _ => ι a) ?_ ?_ ?_ ?_
    · intro a ha
      have haS : a ∈ S := (Finset.mem_filter.mp ha).1
      have hngt : ¬((e a : ℕ) < (e (ι a) : ℕ)) := (Finset.mem_filter.mp ha).2
      have hne_idx : (e (ι a) : ℕ) ≠ (e a : ℕ) := fun hc => hne a haS (e.injective (Fin.ext hc))
      refine Finset.mem_filter.mpr ⟨hmem a haS, ?_⟩
      rw [hinvol a haS]; omega
    · intro a ha b hb h; have := congr_arg ι h
      rw [hinvol a (Finset.mem_filter.mp ha).1, hinvol b (Finset.mem_filter.mp hb).1] at this
      exact this
    · intro b hb
      have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
      have hlt : (e b : ℕ) < (e (ι b) : ℕ) := (Finset.mem_filter.mp hb).2
      refine ⟨ι b, Finset.mem_filter.mpr ⟨hmem b hbS, ?_⟩, hinvol b hbS⟩
      rw [hinvol b hbS]; omega
    · intro a ha; exact (hf_inv a (Finset.mem_filter.mp ha).1).symm
  have hcard_eq : S_gt.card = S_lt.card := by
    have h1 := Finset.sum_bij (s := S_gt) (t := S_lt) (f := fun _ => (1 : ℕ)) (g := fun _ => (1 : ℕ))
      (fun a _ => ι a) ?_ ?_ ?_ (fun _ _ => rfl)
    · simpa using h1
    · intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      have hngt := (Finset.mem_filter.mp ha).2
      have hne_idx : (e (ι a) : ℕ) ≠ (e a : ℕ) := fun hc => hne a haS (e.injective (Fin.ext hc))
      refine Finset.mem_filter.mpr ⟨hmem a haS, ?_⟩; rw [hinvol a haS]; omega
    · intro a ha b hb h; have := congr_arg ι h
      rw [hinvol a (Finset.mem_filter.mp ha).1, hinvol b (Finset.mem_filter.mp hb).1] at this; exact this
    · intro b hb
      have hbS := (Finset.mem_filter.mp hb).1
      have hlt := (Finset.mem_filter.mp hb).2
      refine ⟨ι b, Finset.mem_filter.mpr ⟨hmem b hbS, ?_⟩, hinvol b hbS⟩
      rw [hinvol b hbS]; omega
  have hcard_tot : S_lt.card + S_gt.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (p := fun a => (e a : ℕ) < (e (ι a) : ℕ))
  have hSlt_card : S_lt.card = m := by omega
  refine ⟨∑ a ∈ S_lt, f a, ?_, ?_⟩
  · have hsp := Finset.sum_filter_add_sum_filter_not S (fun a => (e a : ℕ) < (e (ι a) : ℕ)) f
    linarith
  · -- Each `f a ∈ {-1, 1}` satisfies `f a ≡ 1 (mod 2)`, so `∑_{a ∈ S_lt} f a ≡ S_lt.card = m (mod 2)`!
    have hmod2 : ∀ s : Finset α, (∀ a ∈ s, f a = 1 ∨ f a = -1) →
        (∑ a ∈ s, f a) % 2 = (s.card : ℤ) % 2 := by
      intro s hs
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a t hat ih =>
        rw [Finset.sum_cons, Finset.card_cons]
        have ha := hs a (Finset.mem_cons_self a t)
        have iht := ih (fun x hx => hs x (Finset.mem_cons_of_mem hx))
        push_cast
        rcases ha with h1 | h1 <;> omega
    rw [hmod2 S_lt (fun a ha => hf_pm a (Finset.mem_filter.mp ha).1), hSlt_card]

/-- Sign-cube sum `S(σ) = ∑_{q ≠ 0} σ_q * (1/2 * ∑_{p ∈ C_q} γ(q, p) σ_p σ_{q+p})`. -/
noncomputable def signCubeSum (n : ℕ) (σ : PauliIdx n → ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.erase (0 : PauliIdx n),
    σ q * ((1 / 2 : ℝ) * ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).erase q,
      (pauliPhase q p).re * σ p * σ (q + p))

/-- **Core Full-Space Stability Package (`n ≥ 2`)**:
    For every unit state `ψ : QState n` (`d = 2^n`, `r = 1/√(d+1)`, `μ = (d/2 - 1)√(d+1)`),
    setting `σ p = if 0 ≤ c p then 1 else -1` (for `p ≠ 0`, `σ 0 = 0`) and
    `D2 = ∑_{p ≠ 0} (|c p| - r)²`, there exist odd integers `T q ∈ 2ℤ + 1` (`q ≠ 0`) such that:
    1. `((d+1)² / (4 d)) * (d √(d D2) + d D2)² ≥ ∑_{q ≠ 0} ((σ q * T q) - μ)²`  (`L²` block-cancelled bound),
    2. `∑_{q ≠ 0} (σ q * T q) = signCubeSum n σ ≤ (d² - 1) * μ`  (from `Tr(ρ̃³) ≤ 1`),
    3. `∑_{q ≠ 0} (μ - σ q * T q) ≤ ((d+1)^(3/2) / (2 d)) * ((3/2) d (d D2) + (d D2)^(3/2) - (3/(4 d)) (d D2)²)`. -/
lemma full_space_stability_package {n : ℕ} (hn : 2 ≤ n) {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let r : ℝ := 1 / Real.sqrt (d + 1)
    let μ : ℝ := (d / 2 - 1) * Real.sqrt (d + 1)
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
    let D2 : ℝ := ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (|c p| - r) ^ 2
    let y : ℝ := Real.sqrt (d * D2)
    ∃ T : PauliIdx n → ℤ,
      (∀ q ∈ Finset.univ.erase (0 : PauliIdx n), T q % 2 = 1) ∧
      (∑ q ∈ Finset.univ.erase (0 : PauliIdx n), (σ q * (T q : ℝ) - μ) ^ 2 ≤
        ((d + 1) ^ 2 / (4 * d)) * (d * y + y ^ 2) ^ 2) ∧
      (∑ q ∈ Finset.univ.erase (0 : PauliIdx n), σ q * (T q : ℝ) = signCubeSum n σ) ∧
      (∑ q ∈ Finset.univ.erase (0 : PauliIdx n), σ q * (T q : ℝ) ≤ (d ^ 2 - 1) * μ) ∧
      ((d ^ 2 - 1) * μ - signCubeSum n σ ≤
        ((d + 1) * Real.sqrt (d + 1) / (2 * d)) *
          ((3 / 2 : ℝ) * d * y ^ 2 + y ^ 3 - (3 / (4 * d)) * y ^ 4)) := by
  intro d r μ c σ D2 y
  set U := Finset.univ.erase (0 : PauliIdx n)
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr (by linarith)
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hr2 : r ^ 2 = 1 / (d + 1) := by simp only [r, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
  have hc0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hσ_pm : ∀ q ∈ U, σ q = 1 ∨ σ q = -1 := fun q hq => by
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
    simp only [σ, hq0, ↓reduceIte]; split_ifs <;> simp
  have hσ_sq : ∀ q ∈ U, (σ q) ^ 2 = 1 := fun q hq => by
    rcases hσ_pm q hq with h | h <;> rw [h] <;> norm_num
  have hcardU : (U.card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  -- Define integer sign `σI q ∈ {-1, 1}` for `q ∈ U`
  let σI : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  have hσI_cast : ∀ p, (σI p : ℝ) = σ p := fun p => by
    simp only [σI, σ]; split_ifs <;> norm_num
  -- For each `q ∈ U`, extract odd integer `T q` via `sum_invol_parity`!
  have hexT : ∀ q : PauliIdx n, ∃ Tq : ℤ,
      (q ∈ U → Tq % 2 = 1 ∧
        (∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p)) = 2 * (Tq : ℝ)) := by
    intro q
    by_cases hq : q ∈ U
    · have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      let Cq := Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ symp q p = 0
      let γI : PauliIdx n → ℤ := fun p => if pauliPhase q p = 1 then 1 else -1
      have hγI_eq : ∀ p ∈ Cq, (γI p : ℝ) = (pauliPhase q p).re := fun p hp => by
        have hs : symp q p = 0 := (Finset.mem_filter.mp hp).2.2.2
        rcases (pauliPhase_re_cases q p).1 hs with h1 | h1
        · simp [γI, h1]
        · rw [show γI p = -1 by simp only [γI, h1]; norm_num, h1]; norm_num
      have hγI_inv : ∀ p ∈ Cq, γI (q + p) = γI p := fun p hp => by
        have hs : symp q p = 0 := (Finset.mem_filter.mp hp).2.2.2
        have hph := pauliPhase_add_right q p
        simp only [sympSign, hs, ↓reduceIte, Int.cast_one, one_mul] at hph
        simp only [γI, hph]
      have hsum_eq : ∑ p ∈ U.erase q, (pauliPhase q p).re * σ p * σ (q + p) =
          ((∑ p ∈ Cq, γI p * σI p * σI (q + p) : ℤ) : ℝ) := by
        have hsub : Cq = (U.erase q).filter (fun p => symp q p = 0) := by
          ext p; simp only [Cq, U, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]; tauto
        rw [← Finset.sum_filter_add_sum_filter_not (U.erase q) (fun p => symp q p = 0)]
        have hzero : ∑ p ∈ (U.erase q).filter (fun p => ¬symp q p = 0),
            (pauliPhase q p).re * σ p * σ (q + p) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hs1 : symp q p = 1 := (zmod2_cases (symp q p)).resolve_left (Finset.mem_filter.mp hp).2
          rw [(pauliPhase_re_cases q p).2 hs1]; simp
        rw [hzero, add_zero, ← hsub, Int.cast_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        push_cast; rw [hγI_eq p hp, hσI_cast p, hσI_cast (q + p)]
      have hpar := sum_invol_parity Cq (fun p => q + p) (fun p => γI p * σI p * σI (q + p))
        (fun p hp => by
          obtain ⟨hp0, hpq, hsp⟩ := (Finset.mem_filter.mp hp).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
          · intro hc; have := congr_arg (q + ·) hc; rw [pauliIdx_add_cancel_left, add_zero] at this
            exact hpq this
          · intro hc; have := congr_arg (q + ·) hc; rw [pauliIdx_add_cancel_left, pauliIdx_add_self] at this
            exact hp0 this
          · rw [symp_add_right, symp_self, zero_add]; exact hsp)
        (fun p _ => pauliIdx_add_cancel_left q p)
        (fun p _ hc => by
          have := congr_arg (· + p) hc; rw [pauliIdx_add_cancel_right, pauliIdx_add_self] at this
          exact hq0 this)
        (fun p hp => by rw [pauliIdx_add_cancel_left, hγI_inv p hp]; ring)
        (fun p hp => by
          obtain ⟨hp0, hpq, _⟩ := (Finset.mem_filter.mp hp).2
          have hqp0 : q + p ≠ 0 := fun hc => hpq (by
            have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
          have h1 : γI p = 1 ∨ γI p = -1 := by simp only [γI]; split_ifs <;> simp
          have h2 : σI p = 1 ∨ σI p = -1 := by simp only [σI, hp0, ↓reduceIte]; split_ifs <;> simp
          have h3 : σI (q + p) = 1 ∨ σI (q + p) = -1 := by
            simp only [σI, hqp0, ↓reduceIte]; split_ifs <;> simp
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
            simp [h1, h2, h3])
        (4 ^ (n - 1) - 1) (card_commPartners hn hq0)
      obtain ⟨Tq, hTq_eq, hTq_mod⟩ := hpar
      refine ⟨Tq, fun _ => ⟨?_, ?_⟩⟩
      · have hodd : ((4 ^ (n - 1) - 1 : ℕ) : ℤ) % 2 = 1 := by
          have h1 : 1 ≤ n - 1 := by omega
          have h2dvd : 2 ∣ 4 ^ (n - 1) := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
            rw [hk, pow_add]; exact ⟨2 * 4 ^ k, by ring⟩
          have hge1 : 1 ≤ 4 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
          obtain ⟨m, hm⟩ := h2dvd
          omega
        omega
      · rw [hsum_eq, hTq_eq]; push_cast; ring
    · exact ⟨0, fun h => absurd h hq⟩
  choose T hT using hexT
  -- Build operators ONCE before splitting goals: `ρ = stateProj ψ`, `δ p = if p = 0 then 0 else c p - r * σ p`, `Δ = pauliExpand δ`, `rt = ρ - (1/d) Δ`!
  let δ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else c p - r * σ p
  have hδ0 : δ 0 = 0 := by simp [δ]
  have hδ_sq_eq : ∀ q ∈ U, (δ q) ^ 2 = (|c q| - r) ^ 2 := fun q hq => by
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
    simp only [δ, σ, hq0, ↓reduceIte]
    by_cases hcp : 0 ≤ c q
    · simp [hcp, abs_of_nonneg hcp]
    · push Not at hcp; simp [not_le.mpr hcp, abs_of_neg hcp]; ring
  have hD2_eq : ∑ p : PauliIdx n, (δ p) ^ 2 = D2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)), hδ0, zero_pow (by norm_num),
        zero_add]
    exact Finset.sum_congr rfl hδ_sq_eq
  have hD2_nn : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let Δ := pauliExpand δ
  have hΔ_herm : IsHermMat Δ := pauliExpand_herm δ
  have hΔ_frob : frobSq Δ = d * D2 := by rw [frobSq_pauliExpand, hD2_eq]
  have hy_eq : Real.sqrt (frobSq Δ) = y := by rw [hΔ_frob]
  have hy_sq : y ^ 2 = d * D2 := Real.sq_sqrt (by positivity)
  -- `rt = pauliExpand a_rt` where `a_rt 0 = 1/d`, `a_rt p = (r / d) * σ p`!
  let a_rt : PauliIdx n → ℝ := fun p => if p = 0 then 1 / d else (r / d) * σ p
  let ρ := stateProj ψ
  let rt := pauliExpand a_rt
  have hrt_herm : IsHermMat rt := pauliExpand_herm a_rt
  have hrt_eq : rt = matSub ρ (matSmul ((1 / d : ℝ) : ℂ) Δ) := by
    have hρ_exp : ρ = matSmul ((1 / d : ℝ) : ℂ) (pauliExpand c) := by
      have h := stateProj_eq_pauliExpand ψ
      ext x y
      have hxy := congr_fun (congr_fun h x) y
      simp only [ρ, matSmul] at hxy ⊢
      have hdC : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      have hd_cast : ((1 / d : ℝ) : ℂ) = 1 / (2 : ℂ) ^ n := by simp [d]
      rw [hd_cast, ← hxy]; field_simp [hdC]
    rw [hρ_exp, ← pauliExpand_smul, ← pauliExpand_smul, ← pauliExpand_sub]
    dsimp only [rt]; congr 1; ext p
    by_cases hp : p = 0
    · subst hp; simp [a_rt, hc0, hδ0]
    · simp [a_rt, δ, hp]; ring
  -- Compute `frobSq rt = 1`!
  have hrt_frob : frobSq rt = 1 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0 : (a_rt 0) ^ 2 = 1 / d ^ 2 := by simp [a_rt]
    have hrest : ∑ p ∈ U, (a_rt p) ^ 2 = (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
      have hterm : ∀ p ∈ U, (a_rt p) ^ 2 = 1 / (d ^ 2 * (d + 1)) := fun p hp => by
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
        simp only [a_rt, hp0, ↓reduceIte, mul_pow, div_pow, hσ_sq p hp, mul_one, hr2]
        field_simp [hd_ne, hd1_ne]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcardU]
    rw [h0, hrest]; field_simp [hd_ne, hd1_ne]; ring
  -- Compute `rt² = pauliExpand a_rt2` explicitly!
  have hrt2 : matMul rt rt = pauliExpand (fun q =>
      if q = 0 then 1 / d
      else (2 / d ^ 2) * (r * σ q + r ^ 2 * (T q : ℝ))) := by
    rw [matMul_pauliExpand_self]
    congr 1; ext q
    by_cases hq : q = 0
    · subst hq
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
      have ht0 : (pauliPhase (0 : PauliIdx n) 0).re * a_rt 0 * a_rt (0 + 0) = 1 / d ^ 2 := by
        simp [a_rt, pauliPhase_zero_left]; ring
      have hrest : ∑ p ∈ U, (pauliPhase 0 p).re * a_rt p * a_rt (0 + p) =
          (d ^ 2 - 1) * (1 / (d ^ 2 * (d + 1))) := by
        have hterm : ∀ p ∈ U, (pauliPhase 0 p).re * a_rt p * a_rt (0 + p) =
            1 / (d ^ 2 * (d + 1)) := fun p hp => by
          have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
          rw [pauliPhase_zero_left, Complex.one_re, zero_add, one_mul]
          simp only [a_rt, hp0, ↓reduceIte]
          have : (r / d * σ p) * (r / d * σ p) = (r ^ 2 / d ^ 2) * (σ p) ^ 2 := by ring
          rw [this, hσ_sq p hp, hr2]; field_simp [hd_ne, hd1_ne]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcardU]
      simp only [↓reduceIte]; rw [ht0, hrest]; field_simp [hd_ne, hd1_ne]; ring
    · have hqU : q ∈ U := Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
      simp only [hq, ↓reduceIte]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)),
          ← Finset.add_sum_erase _ _ hqU]
      have ht0 : (pauliPhase q 0).re * a_rt 0 * a_rt (q + 0) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_zero_right, Complex.one_re, add_zero]
        simp only [a_rt, ↓reduceIte, hq]; ring
      have htq : (pauliPhase q q).re * a_rt q * a_rt (q + q) = (r / d ^ 2) * σ q := by
        rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self]
        simp only [a_rt, ↓reduceIte, hq]; ring
      have hrest : ∑ p ∈ U.erase q, (pauliPhase q p).re * a_rt p * a_rt (q + p) =
          (r ^ 2 / d ^ 2) * (2 * (T q : ℝ)) := by
        rw [← (hT q hqU).2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have hqp0 : q + p ≠ 0 := fun hc => hpq (by
          have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
        simp only [a_rt, hp0, hqp0, ↓reduceIte]; ring
      rw [ht0, htq, hrest]; ring
  -- Compute `Tr(rt³)` in terms of `∑_{q ∈ U} σ q * T q`!
  have hrt3_tr : (matTr (matMul rt (matMul rt rt))).re =
      (d + 3 * d * (d - 1) + (2 * d / ((d + 1) * Real.sqrt (d + 1))) *
        ∑ q ∈ U, σ q * (T q : ℝ)) / d ^ 3 := by
    rw [hrt2, matTr_pauliExpand_mul]
    have hre : ((2 : ℂ) ^ n * ∑ p : PauliIdx n,
        ((a_rt p * (if p = 0 then 1 / d else 2 / d ^ 2 * (r * σ p + r ^ 2 * (T p : ℝ))) : ℝ) : ℂ)).re =
        d * ∑ p : PauliIdx n,
          a_rt p * (if p = 0 then 1 / d else 2 / d ^ 2 * (r * σ p + r ^ 2 * (T p : ℝ))) := by
      have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
      rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    simp only [↓reduceIte]
    have hrest : ∑ p ∈ U, a_rt p * (if p = 0 then 1 / d else 2 / d ^ 2 * (r * σ p + r ^ 2 * (T p : ℝ))) =
        (d ^ 2 - 1) * (2 * r ^ 2 / d ^ 3) + (2 * r ^ 3 / d ^ 3) * ∑ p ∈ U, σ p * (T p : ℝ) := by
      have hterm : ∀ p ∈ U, a_rt p * (if p = 0 then 1 / d else 2 / d ^ 2 * (r * σ p + r ^ 2 * (T p : ℝ))) =
          2 * r ^ 2 / d ^ 3 + (2 * r ^ 3 / d ^ 3) * (σ p * (T p : ℝ)) := fun p hp => by
        have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
        simp only [a_rt, hp0, ↓reduceIte]
        have : (r / d * σ p) * (2 / d ^ 2 * (r * σ p + r ^ 2 * (T p : ℝ))) =
            (2 * r ^ 2 / d ^ 3) * (σ p) ^ 2 + (2 * r ^ 3 / d ^ 3) * (σ p * (T p : ℝ)) := by ring
        rw [this, hσ_sq p hp, mul_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          hcardU, ← Finset.mul_sum]
    have h0' : a_rt 0 * (1 / d) = 1 / d ^ 2 := by simp [a_rt]; ring
    rw [h0', hrest]
    have hr3 : r ^ 3 = 1 / ((d + 1) * Real.sqrt (d + 1)) := by
      calc r ^ 3 = r ^ 2 * r := by ring
        _ = (1 / (d + 1)) * (1 / Real.sqrt (d + 1)) := by rw [hr2]
        _ = 1 / ((d + 1) * Real.sqrt (d + 1)) := by rw [one_div_mul_one_div]
    rw [hr2, hr3]; field_simp [hd_ne, hd1_ne, hs_ne]; ring
  -- Exact identity: `∑_{q ∈ U} σ q * T q = signCubeSum n σ`!
  have hsum_signCube : ∑ q ∈ U, σ q * (T q : ℝ) = signCubeSum n σ := by
    simp only [signCubeSum]
    refine Finset.sum_congr rfl fun q hq => by rw [(hT q hq).2]; ring
  refine ⟨T, fun q hq => (hT q hq).1, ?_, ?_, ?_, ?_⟩
  · -- Goal 1: `L²` bound `∑ (σ q * T q - μ)² ≤ ((d+1)² / (4 d)) * (d y + y²)²`!
    let E := matSmul ((d ^ 2 : ℝ) : ℂ) (matSub (matMul rt rt) rt)
    have hE_exp : E = pauliExpand (fun q =>
        if q = 0 then 0 else (2 / (d + 1)) * ((T q : ℝ) - μ * σ q)) := by
      simp only [E]
      rw [hrt2, ← pauliExpand_sub, ← pauliExpand_smul]
      congr 1; ext q
      by_cases hq : q = 0
      · subst hq; simp [a_rt]
      · simp only [hq, ↓reduceIte, a_rt, μ]
        have hr_eq : d ^ 2 * (2 / d ^ 2 * (r * σ q + r ^ 2 * (T q : ℝ)) - r / d * σ q) =
            2 * r ^ 2 * (T q : ℝ) - (d - 2) * r * σ q := by field_simp [hd_ne]; ring
        rw [hr_eq, hr2]
        have hr_alt : r = Real.sqrt (d + 1) / (d + 1) := by
          simp only [r]; field_simp [hs_ne, hd1_ne]; rw [Real.sq_sqrt (le_of_lt hd1_pos)]
        rw [hr_alt]; ring
    have hE_frob : frobSq E = (4 * d / (d + 1) ^ 2) * ∑ q ∈ U, (σ q * (T q : ℝ) - μ) ^ 2 := by
      rw [hE_exp, frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
      simp only [↓reduceIte, zero_pow (by norm_num : 2 ≠ 0), zero_add]
      have hterm : ∀ q ∈ U,
          (if q = 0 then (0 : ℝ) else 2 / (d + 1) * ((T q : ℝ) - μ * σ q)) ^ 2 =
          (4 / (d + 1) ^ 2) * (σ q * (T q : ℝ) - μ) ^ 2 := fun q hq => by
        have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
        simp only [hq0, ↓reduceIte]
        have hsq : ((T q : ℝ) - μ * σ q) ^ 2 = (σ q * (T q : ℝ) - μ) ^ 2 := by
          calc ((T q : ℝ) - μ * σ q) ^ 2 = (σ q) ^ 2 * ((T q : ℝ) - μ * σ q) ^ 2 := by
                rw [hσ_sq q hq, one_mul]
            _ = (σ q * (T q : ℝ) - μ * (σ q) ^ 2) ^ 2 := by ring
            _ = (σ q * (T q : ℝ) - μ) ^ 2 := by rw [hσ_sq q hq, mul_one]
        rw [mul_pow, div_pow, hsq]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]; ring
    -- Matrix identity: `E = d (Δ - ρ Δ - Δ ρ) + Δ²`!
    have hE_rhs : E = matAdd (matSmul (d : ℂ) (matSub Δ (matAdd (matMul ρ Δ) (matMul Δ ρ))))
        (matMul Δ Δ) := by
      simp only [E]; rw [hrt_eq]
      have hρ2 : matMul ρ ρ = ρ := stateProj_idem hunit
      ext x y
      simp only [matMul_sub_left, matMul_sub_right, matMul_smul_left, matMul_smul_right, hρ2,
        matSub, matAdd, matSmul]
      have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd_ne
      push_cast; field_simp [hdC]; ring
    have hE_ub : Real.sqrt (frobSq E) ≤ d * y + y ^ 2 := by
      rw [hE_rhs]
      have htri := sqrt_frobSq_add_le
        (matSmul (d : ℂ) (matSub Δ (matAdd (matMul ρ Δ) (matMul Δ ρ)))) (matMul Δ Δ)
      have h1 : Real.sqrt (frobSq (matSmul (d : ℂ) (matSub Δ (matAdd (matMul ρ Δ) (matMul Δ ρ))))) ≤ d * y := by
        rw [frobSq_smul, Complex.normSq_ofReal, ← sq, Real.sqrt_mul (sq_nonneg d),
            Real.sqrt_sq (le_of_lt hd_pos), ← hy_eq]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (frobSq_proj_cancel (stateProj_herm ψ) (stateProj_idem hunit) hΔ_herm))
          (le_of_lt hd_pos)
      have h2 : Real.sqrt (frobSq (matMul Δ Δ)) ≤ y ^ 2 := by
        rw [← hy_eq, Real.sq_sqrt (frobSq_nonneg Δ)]
        rw [Real.sqrt_le_iff]; exact ⟨frobSq_nonneg Δ, by
          have := frobSq_matMul_le Δ Δ; linarith⟩
      linarith
    have hE_sq : frobSq E ≤ (d * y + y ^ 2) ^ 2 := by
      have hnn : 0 ≤ d * y + y ^ 2 := add_nonneg (mul_nonneg (le_of_lt hd_pos) (Real.sqrt_nonneg _)) (sq_nonneg _)
      exact (Real.sqrt_le_iff.mp hE_ub).2
    rw [hE_frob] at hE_sq
    have hfac_pos : 0 < (d + 1) ^ 2 / (4 * d) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hE_sq (le_of_lt hfac_pos)
    have hcancel : (d + 1) ^ 2 / (4 * d) * (4 * d / (d + 1) ^ 2 *
        ∑ q ∈ U, (σ q * (T q : ℝ) - μ) ^ 2) = ∑ q ∈ U, (σ q * (T q : ℝ) - μ) ^ 2 := by
      field_simp [hd_ne, hd1_ne]
    linarith
  · -- Goal 2: `∑ σ q * T q = signCubeSum n σ`
    exact hsum_signCube
  · -- Goal 3: `∑ σ q * T q ≤ (d² - 1) * μ` (from `Tr(rt³) ≤ 1`!)
    have htr3_le : (matTr (matMul rt (matMul rt rt))).re ≤ 1 := by
      have h := matTr_cube_re_le rt
      rw [hrt_frob, Real.sqrt_one, one_pow] at h; exact h
    rw [hrt3_tr] at htr3_le
    have h1 : d + 3 * d * (d - 1) + (2 * d / ((d + 1) * Real.sqrt (d + 1))) *
        ∑ q ∈ U, σ q * (T q : ℝ) ≤ d ^ 3 := by
      simpa only [one_mul] using (div_le_iff₀ (pow_pos hd_pos 3)).mp htr3_le
    have h2 : (2 * d / ((d + 1) * Real.sqrt (d + 1))) * ∑ q ∈ U, σ q * (T q : ℝ) ≤
        d * (d - 1) * (d - 2) := by linarith
    have hmul := mul_le_mul_of_nonneg_left h2
      (le_of_lt (show 0 < (d + 1) * Real.sqrt (d + 1) / (2 * d) by positivity))
    have hlhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) *
        (2 * d / ((d + 1) * Real.sqrt (d + 1)) * ∑ q ∈ U, σ q * (T q : ℝ)) =
        ∑ q ∈ U, σ q * (T q : ℝ) := by field_simp [hd_ne, hd1_ne, hs_ne]
    have hrhs : (d + 1) * Real.sqrt (d + 1) / (2 * d) * (d * (d - 1) * (d - 2)) =
        (d ^ 2 - 1) * μ := by simp only [μ]; field_simp [hd_ne]; ring
    linarith
  · -- Goal 4: exact matrix-free bound on `(d² - 1) * μ - signCubeSum n σ`!
    have hρ2 : matMul ρ ρ = ρ := stateProj_idem hunit
    have hρ_tr : matTr ρ = 1 := by
      rw [← hρ2, matTr_mul_self_herm (stateProj_herm ψ)]
      have : frobSq ρ = 1 := by
        have hf : frobSq ρ = ((innerProd ψ ψ).re) ^ 2 := by
          simp only [frobSq, ρ, stateProj, map_mul, Complex.star_def, Complex.normSq_conj,
            innerProd_self_re, sq]
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum]
        rw [hf, hunit, Complex.one_re]; norm_num
      rw [this, Complex.ofReal_one]
    -- Compute `Tr(ρ Δ)` from `1 = frobSq rt = Tr(rt²) = Tr(ρ) - (2/d) Tr(ρ Δ) + (1/d²) frobSq Δ`!
    have hρΔ_tr : (matTr (matMul ρ Δ)).re = y ^ 2 / (2 * d) := by
      have h1 : matTr (matMul rt rt) = (1 : ℂ) := by
        rw [matTr_mul_self_herm hrt_herm, hrt_frob, Complex.ofReal_one]
      have h2 : matTr (matMul rt rt) =
          matTr ρ - ((2 / d : ℝ) : ℂ) * matTr (matMul ρ Δ) +
            ((1 / d ^ 2 : ℝ) : ℂ) * matTr (matMul Δ Δ) := by
        rw [hrt_eq, matMul_sub_left, matMul_sub_right, matMul_sub_right, hρ2,
            matMul_smul_left, matMul_smul_right, matMul_smul_right, matMul_smul_left,
            matTr_sub, matTr_sub, matTr_sub, matTr_smul, matTr_smul, matTr_smul, matTr_smul,
            matTr_mul_comm Δ ρ]
        push_cast; ring
      rw [h1, hρ_tr, matTr_mul_self_herm hΔ_herm, hΔ_frob, ← hy_sq] at h2
      have hre := congr_arg Complex.re h2
      simp only [Complex.one_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
      have hd_ne2 : d ≠ 0 := hd_ne
      field_simp [hd_ne2] at hre ⊢; linarith
    -- Expand `Tr(rt³) = 1 - (3/d) Tr(ρ Δ) + (3/d²) Tr(ρ Δ²) - (1/d³) Tr(Δ³)`!
    have hrt3_exp : matTr (matMul rt (matMul rt rt)) =
        1 - ((3 / d : ℝ) : ℂ) * matTr (matMul ρ Δ) +
          ((3 / d ^ 2 : ℝ) : ℂ) * matTr (matMul ρ (matMul Δ Δ)) -
          ((1 / d ^ 3 : ℝ) : ℂ) * matTr (matMul Δ (matMul Δ Δ)) := by
      rw [hrt_eq]
      simp only [matMul_sub_left, matMul_sub_right, matMul_smul_left, matMul_smul_right,
        matTr_sub, matTr_smul, hρ2]
      have hc0 : matTr (matMul ρ (matMul ρ Δ)) = matTr (matMul ρ Δ) := by
        rw [← matMul_assoc, hρ2]
      have hc1 : matTr (matMul ρ (matMul Δ ρ)) = matTr (matMul ρ Δ) := by
        rw [← matMul_assoc, matTr_mul_comm (matMul ρ Δ) ρ, ← matMul_assoc, hρ2]
      have hc3 : matTr (matMul Δ (matMul ρ Δ)) = matTr (matMul ρ (matMul Δ Δ)) := by
        rw [matTr_mul_comm Δ, matMul_assoc]
      have hc4 : matTr (matMul Δ (matMul Δ ρ)) = matTr (matMul ρ (matMul Δ Δ)) := by
        rw [← matMul_assoc, matTr_mul_comm]
      have hc5 : matTr (matMul Δ ρ) = matTr (matMul ρ Δ) := matTr_mul_comm _ _
      rw [hρ_tr, hc0, hc1, hc3, hc4, hc5]; push_cast; ring
    -- Lower bound `(matTr (matMul ρ (matMul Δ Δ))).re ≥ y⁴ / (4 d²)` via Cauchy–Schwarz!
    have hρΔ2_ge : y ^ 4 / (4 * d ^ 2) ≤ (matTr (matMul ρ (matMul Δ Δ))).re := by
      rw [matTr_stateProj_mul_sq ψ hΔ_herm]
      have hcs := normSq_innerProd_le ψ (matApply Δ ψ)
      rw [hunit, Complex.one_re, one_mul] at hcs
      have hre_sq : (innerProd ψ (matApply Δ ψ)).re ^ 2 ≤
          Complex.normSq (innerProd ψ (matApply Δ ψ)) := by
        rw [Complex.normSq_apply]; nlinarith
      have heq : (innerProd ψ (matApply Δ ψ)).re = y ^ 2 / (2 * d) := by
        rw [← matTr_stateProj_mul]; exact hρΔ_tr
      rw [heq] at hre_sq
      have : (y ^ 2 / (2 * d)) ^ 2 = y ^ 4 / (4 * d ^ 2) := by ring
      linarith
    have hΔ3_le : (matTr (matMul Δ (matMul Δ Δ))).re ≤ y ^ 3 := by
      simpa [hy_eq] using matTr_cube_re_le Δ
    have h1_sub : 1 - (matTr (matMul rt (matMul rt rt))).re ≤
        (3 / (2 * d ^ 2)) * y ^ 2 - (3 / (4 * d ^ 4)) * y ^ 4 + (1 / d ^ 3) * y ^ 3 := by
      have hre := congr_arg Complex.re hrt3_exp
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
      rw [hρΔ_tr] at hre
      have h1 : 3 / d ^ 2 * (y ^ 4 / (4 * d ^ 2)) ≤ 3 / d ^ 2 * (matTr (matMul ρ (matMul Δ Δ))).re :=
        mul_le_mul_of_nonneg_left hρΔ2_ge (by positivity)
      have h2 : 1 / d ^ 3 * (matTr (matMul Δ (matMul Δ Δ))).re ≤ 1 / d ^ 3 * y ^ 3 :=
        mul_le_mul_of_nonneg_left hΔ3_le (by positivity)
      have ha : 3 / d * (y ^ 2 / (2 * d)) = 3 / (2 * d ^ 2) * y ^ 2 := by ring
      have hb : 3 / d ^ 2 * (y ^ 4 / (4 * d ^ 2)) = 3 / (4 * d ^ 4) * y ^ 4 := by ring
      linarith
    -- Convert `1 - Tr(rt³)` to `(d² - 1) * μ - signCubeSum n σ`!
    have hdef_eq : (d ^ 2 - 1) * μ - signCubeSum n σ =
        ((d ^ 2 * (d + 1) * Real.sqrt (d + 1)) / 2) * (1 - (matTr (matMul rt (matMul rt rt))).re) := by
      rw [hrt3_tr, hsum_signCube]
      simp only [μ]; field_simp [hd_ne, hd1_ne, hs_ne]; ring
    rw [hdef_eq]
    have hmul := mul_le_mul_of_nonneg_left h1_sub
      (le_of_lt (show 0 < d ^ 2 * (d + 1) * Real.sqrt (d + 1) / 2 by positivity))
    have hrhs_eq : d ^ 2 * (d + 1) * Real.sqrt (d + 1) / 2 *
        (3 / (2 * d ^ 2) * y ^ 2 - 3 / (4 * d ^ 4) * y ^ 4 + 1 / d ^ 3 * y ^ 3) =
        (d + 1) * Real.sqrt (d + 1) / (2 * d) * (3 / 2 * d * y ^ 2 + y ^ 3 - 3 / (4 * d) * y ^ 4) := by
      field_simp [hd_ne]; ring
    linarith

/-- **Theorem 5 (Universal Quantitative Gap Above Welch/SIC for ALL `n ∈ {2} ∪ {4, 5, 6, …}`)**:
    For every `n = 2` or `n ≥ 4` (`d = 2ⁿ`) and EVERY unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n`,
      `pauliMoment4 n ψ ≥ 2 d / (d + 1) + 16 (d - 1) / (d⁴ (d + 1)³)`. -/
theorem pauliMoment4_ge_welch_add_universal {n : ℕ} (hn : n = 2 ∨ 4 ≤ n)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    pauliMoment4 n ψ ≥ 2 * d / (d + 1) + 16 * (d - 1) / (d ^ 4 * (d + 1) ^ 3) := by
  intro d
  have hn2 : 2 ≤ n := by omega
  have hd_ge4 : 4 ≤ d := by
    have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn2
    linarith
  have hd_pos : 0 < d := by linarith
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨T, hTodd, hL2, _, _, _⟩ := full_space_stability_package hn2 hunit
  set U := Finset.univ.erase (0 : PauliIdx n)
  set c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set r : ℝ := 1 / Real.sqrt (d + 1)
  set μ : ℝ := (d / 2 - 1) * Real.sqrt (d + 1)
  set σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  set D2 : ℝ := ∑ p ∈ U, (|c p| - r) ^ 2
  set y : ℝ := Real.sqrt (d * D2)
  have hD2_nn : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy_nn : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = d * D2 := Real.sq_sqrt (by positivity)
  -- Pointwise lower bound: for every `q ∈ U`, `(σ q * T q - μ)² ≥ 16 / (d² (d + 1))`!
  have hpt : ∀ q ∈ U, 16 / (d ^ 2 * (d + 1)) ≤ (σ q * (T q : ℝ) - μ) ^ 2 := by
    intro q hq
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
    have hσpm : σ q = 1 ∨ σ q = -1 := by simp only [σ, hq0, ↓reduceIte]; split_ifs <;> simp
    -- `σ q * T q` is an odd integer `m = 2k + 1`!
    have hex_odd : ∃ k : ℤ, σ q * (T q : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by
      have hmod := hTodd q hq
      rcases hσpm with hs | hs
      · refine ⟨T q / 2, ?_⟩; rw [hs, one_mul]; exact_mod_cast (by omega : T q = 2 * (T q / 2) + 1)
      · refine ⟨(-T q - 1) / 2, ?_⟩; rw [hs]; push_cast
        have : -T q = 2 * ((-T q - 1) / 2) + 1 := by omega
        have hR : (-(T q : ℝ)) = 2 * (((-T q - 1) / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast this
        linarith
    obtain ⟨k, hk⟩ := hex_odd
    rw [hk]
    set mR : ℝ := ((2 * k + 1 : ℤ) : ℝ)
    by_cases hfar : 1 ≤ |mR - μ|
    · have h1 : 1 ≤ (mR - μ) ^ 2 := by nlinarith [sq_abs (mR - μ)]
      have h2 : 16 / (d ^ 2 * (d + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      linarith
    · push Not at hfar
      have hsum_lt : |mR| + μ ≤ d * Real.sqrt (d + 1) := by
        have hsqrt_gt1 : 1 ≤ Real.sqrt (d + 1) := by
          rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
        have hμ_nn : 0 ≤ μ := mul_nonneg (by linarith) (le_of_lt hs_pos)
        have hm_le : |mR| ≤ μ + 1 := by
          have := abs_sub_abs_le_abs_sub mR μ
          have h1 : |μ| = μ := abs_of_nonneg hμ_nn
          linarith
        have : 2 * μ + 1 = (d - 2) * Real.sqrt (d + 1) + 1 := by simp only [μ]; ring
        nlinarith
      have hsq_diff : 4 ≤ |mR ^ 2 - μ ^ 2| := by
        have hμ2 : μ ^ 2 = (d / 2 - 1) ^ 2 * (d + 1) := by
          simp only [μ, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d + 1)]
        have hd2 : d / 2 = (2 : ℝ) ^ (n - 1) := by
          have : d = 2 * (2 : ℝ) ^ (n - 1) := by
            simp only [d]
            conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
            ring
          linarith
        have hZ := odd_sq_dist_ge_four hn k
        have hR : (4 : ℝ) ≤ |((((2 : ℤ) ^ (n - 1) - 1) ^ 2 * ((2 : ℤ) ^ n + 1) - (2 * k + 1) ^ 2 : ℤ) : ℝ)| := by
          exact_mod_cast hZ
        have heq : ((((2 : ℤ) ^ (n - 1) - 1) ^ 2 * ((2 : ℤ) ^ n + 1) - (2 * k + 1) ^ 2 : ℤ) : ℝ) =
            μ ^ 2 - mR ^ 2 := by
          rw [hμ2, hd2]; simp only [mR, d]; push_cast; ring
        rw [heq, abs_sub_comm] at hR; exact hR
      have hfac : |mR ^ 2 - μ ^ 2| = |mR - μ| * |mR + μ| := by
        rw [← abs_mul]; congr 1; ring
      have hplus : |mR + μ| ≤ d * Real.sqrt (d + 1) := by
        have h1 : |mR + μ| ≤ |mR| + |μ| := abs_add_le mR μ
        have hμ_nn : 0 ≤ μ := mul_nonneg (by linarith) (le_of_lt hs_pos)
        rw [abs_of_nonneg hμ_nn] at h1; linarith
      have h4le : 4 ≤ |mR - μ| * (d * Real.sqrt (d + 1)) := by
        calc (4 : ℝ) ≤ |mR - μ| * |mR + μ| := by rw [← hfac]; exact hsq_diff
          _ ≤ |mR - μ| * (d * Real.sqrt (d + 1)) := mul_le_mul_of_nonneg_left hplus (abs_nonneg _)
      have hdiv : 4 / (d * Real.sqrt (d + 1)) ≤ |mR - μ| :=
        (div_le_iff₀ (by positivity)).mpr h4le
      have hsq := pow_le_pow_left₀ (by positivity) hdiv 2
      have hlhs : (4 / (d * Real.sqrt (d + 1))) ^ 2 = 16 / (d ^ 2 * (d + 1)) := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ d + 1)]; norm_num
      rw [hlhs, sq_abs] at hsq; exact hsq
  have hcardU : (U.card : ℝ) = d ^ 2 - 1 := card_PauliIdx_erase_zero n
  have hsum_lb : (d ^ 2 - 1) * (16 / (d ^ 2 * (d + 1))) ≤
      ∑ q ∈ U, (σ q * (T q : ℝ) - μ) ^ 2 := by
    have := Finset.sum_le_sum hpt
    rwa [Finset.sum_const, nsmul_eq_mul, hcardU] at this
  have hchain : (d ^ 2 - 1) * (16 / (d ^ 2 * (d + 1))) ≤ ((d + 1) ^ 2 / (4 * d)) * (d * y + y ^ 2) ^ 2 :=
    le_trans hsum_lb hL2
  -- Case split `y ≤ d` vs `y > d`!
  have hD2_lb : 16 * (d - 1) / (d ^ 4 * (d + 1) ^ 2) ≤ D2 := by
    by_cases hyd : y ≤ d
    · have h2d : d * y + y ^ 2 ≤ 2 * d * y := by nlinarith
      have hsq2 : (d * y + y ^ 2) ^ 2 ≤ 4 * d ^ 2 * y ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) h2d 2; linarith
      have h3 : (d ^ 2 - 1) * (16 / (d ^ 2 * (d + 1))) ≤
          ((d + 1) ^ 2 / (4 * d)) * (4 * d ^ 2 * y ^ 2) :=
        le_trans hchain (mul_le_mul_of_nonneg_left hsq2 (by positivity))
      rw [hy_sq] at h3
      have hd_ne : d ≠ 0 := ne_of_gt hd_pos
      have hd1_ne : d + 1 ≠ 0 := by linarith
      have hsimp : ((d + 1) ^ 2 / (4 * d)) * (4 * d ^ 2 * (d * D2)) = (d + 1) ^ 2 * d ^ 2 * D2 := by
        field_simp [hd_ne]
      rw [hsimp] at h3
      have hfac : (d ^ 2 - 1) * (16 / (d ^ 2 * (d + 1))) = 16 * (d - 1) / d ^ 2 := by
        field_simp [hd_ne, hd1_ne]; ring
      rw [hfac] at h3
      rw [div_le_iff₀ (by positivity)]
      have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt (show 0 < d ^ 2 by positivity))
      field_simp [hd_ne] at h4; linarith
    · push Not at hyd
      have hy2 : d ^ 2 ≤ d * D2 := by rw [← hy_sq]; nlinarith
      have hd_le : d ≤ D2 := by nlinarith
      have hsmall : 16 * (d - 1) / (d ^ 4 * (d + 1) ^ 2) ≤ d := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : (256 : ℝ) ≤ d ^ 4 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hd_ge4 4
          linarith
        have h5 : (16 : ℝ) * d ≤ d ^ 5 := by nlinarith
        have h6 : (1 : ℝ) ≤ (d + 1) ^ 2 := by nlinarith
        nlinarith
      linarith
  have heps := eps_ge_div_d_add_one hunit
  have hdiv : 16 * (d - 1) / (d ^ 4 * (d + 1) ^ 3) ≤ D2 / (d + 1) := by
    have := div_le_div_of_nonneg_right hD2_lb (by linarith : (0 : ℝ) ≤ d + 1)
    rwa [div_div, show d ^ 4 * (d + 1) ^ 2 * (d + 1) = d ^ 4 * (d + 1) ^ 3 by ring] at this
  linarith

/-- Strict quantitative corollary: for ALL `n ∈ {2} ∪ {4, 5, …}` and every unit pure state `ψ`,
    `pauliMoment4 n ψ > 2 * 2^n / (2^n + 1)` strictly (new elementary proof of Godsil–Roy!). -/
theorem pauliMoment4_gt_welch {n : ℕ} (hn : n = 2 ∨ 4 ≤ n)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1) < pauliMoment4 n ψ := by
  have h := pauliMoment4_ge_welch_add_universal hn hunit
  have hpos : 0 < 16 * ((2 : ℝ) ^ n - 1) / (((2 : ℝ) ^ n) ^ 4 * ((2 : ℝ) ^ n + 1) ^ 3) := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
      have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hsub : 0 < (2 : ℝ) ^ n - 1 := by linarith
    positivity
  linarith

/-- **Corollary (Godsil–Roy 2009, Matrix-Free Lean 4 Proof)**:
    For every `n ∈ {2} ∪ {4, 5, 6, …}`, NO unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n` is a
    Pauli-covariant SIC fiducial (`|⟨ψ | P_p | ψ⟩|² = 1 / (2ⁿ + 1)` for all `p ≠ 0`). -/
theorem no_pauli_sic_all {n : ℕ} (hn : n = 2 ∨ 4 ≤ n)
    {ψ : QState n} (hunit : IsUnitState ψ) :
    ¬ (∀ p : PauliIdx n, p ≠ 0 →
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 / ((2 : ℝ) ^ n + 1)) := by
  intro hsic
  have hgt := pauliMoment4_gt_welch hn hunit
  have hsub := pauliMoment4_sub_welch hunit
  have h0 : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n),
      (((innerProd ψ (pauliApply p ψ)).re) ^ 2 - 1 / ((2 : ℝ) ^ n + 1)) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
    rw [← innerProd_pauliApply_self_normSq p ψ, hsic p hp0]; norm_num
  linarith

/-- Odd-integer `b(2 - b)` secant identity: for any odd integer `x` (`x % 2 = 1`),
    odd integer `m` (`m % 2 = 1`), and real `μ`,
      `(x - μ)² ≥ (μ - m) * (m + 2 - μ) + 2 * (m + 1 - μ) * (x - μ)`. -/
lemma odd_secant_sq_ge (x m : ℤ) (hx : x % 2 = 1) (hm : m % 2 = 1) (μ : ℝ) :
    ((μ - (m : ℝ)) * ((m : ℝ) + 2 - μ) + 2 * ((m : ℝ) + 1 - μ) * ((x : ℝ) - μ)) ≤
      ((x : ℝ) - μ) ^ 2 := by
  have hdiff : ((x : ℝ) - μ) ^ 2 -
      ((μ - (m : ℝ)) * ((m : ℝ) + 2 - μ) + 2 * ((m : ℝ) + 1 - μ) * ((x : ℝ) - μ)) =
      ((x : ℝ) - (m : ℝ)) * ((x : ℝ) - (m : ℝ) - 2) := by ring
  have hnn : (0 : ℝ) ≤ ((x : ℝ) - (m : ℝ)) * ((x : ℝ) - (m : ℝ) - 2) := by
    have hZ : (0 : ℤ) ≤ (x - m) * (x - m - 2) := by
      have heven : (x - m) % 2 = 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℤ, x - m = 2 * k := ⟨(x - m) / 2, by omega⟩
      rw [hk]
      have : (2 * k) * (2 * k - 2) = 4 * (k * (k - 1)) := by ring
      rw [this]
      have hk_nn : 0 ≤ k * (k - 1) := by
        by_cases h1 : 1 ≤ k
        · nlinarith
        · by_cases h0 : k ≤ 0
          · nlinarith
          · omega
      omega
    exact_mod_cast hZ
  linarith

/-- **Sharp `n = 2` General Pure-State Lower Bound (`pauliMoment4_two_ge`)**:
    For every 2-qubit unit pure state `ψ`, `pauliMoment4 2 ψ ≥ 8 / 5 + 34 / 1000` (`= 1.634`,
    vs Welch `8 / 5 = 1.600`). -/
theorem pauliMoment4_two_ge {ψ : QState 2} (hunit : IsUnitState ψ) :
    (8 / 5 : ℝ) + 34 / 1000 ≤ pauliMoment4 2 ψ := by
  obtain ⟨T, hTodd, hL2, _, hsum_le, _⟩ := full_space_stability_package (n := 2) (by norm_num) hunit
  set U := Finset.univ.erase (0 : PauliIdx 2)
  set c : PauliIdx 2 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set σ : PauliIdx 2 → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  set r : ℝ := 1 / Real.sqrt ((2 : ℝ) ^ 2 + 1)
  set D2 : ℝ := ∑ p ∈ U, (|c p| - r) ^ 2
  set y : ℝ := Real.sqrt ((2 : ℝ) ^ 2 * D2)
  have hD2_nn : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy_nn : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 4 * D2 := by
    have : (2 : ℝ) ^ 2 * D2 = 4 * D2 := by norm_num
    rw [show y = Real.sqrt (4 * D2) by simp only [y, this], Real.sq_sqrt (by linarith)]
  have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5_lo : (2.2360 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h5_hi : Real.sqrt 5 < (2.2361 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hμ_eq : ((2 : ℝ) ^ 2 / 2 - 1) * Real.sqrt ((2 : ℝ) ^ 2 + 1) = Real.sqrt 5 := by norm_num
  have hcardU : (U.card : ℝ) = 15 := by
    have h := card_PauliIdx_erase_zero 2
    rw [show ((2 : ℝ) ^ 2) ^ 2 - 1 = 15 by norm_num] at h
    exact h
  -- Apply `odd_secant_sq_ge` with `m = 1` (`μ = √5 ∈ (2, 3)`, so `m + 1 - μ = 2 - √5 < 0`)!
  have hsum_sec : 15 * ((Real.sqrt 5 - 1) * (3 - Real.sqrt 5)) ≤
      ∑ q ∈ U, (σ q * (T q : ℝ) - Real.sqrt 5) ^ 2 := by
    have hpt : ∀ q ∈ U,
        (Real.sqrt 5 - 1) * (3 - Real.sqrt 5) + 2 * (2 - Real.sqrt 5) * (σ q * (T q : ℝ) - Real.sqrt 5) ≤
        (σ q * (T q : ℝ) - Real.sqrt 5) ^ 2 := by
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      have hσpm : σ q = 1 ∨ σ q = -1 := by simp only [σ, hq0, ↓reduceIte]; split_ifs <;> simp
      have hxodd : ∃ x : ℤ, x % 2 = 1 ∧ σ q * (T q : ℝ) = (x : ℝ) := by
        have hm := hTodd q hq
        rcases hσpm with h | h
        · exact ⟨T q, hm, by rw [h, one_mul]⟩
        · exact ⟨-T q, by omega, by rw [h]; push_cast; ring⟩
      obtain ⟨x, hx, hxeq⟩ := hxodd
      rw [hxeq]
      have hsec := odd_secant_sq_ge x 1 hx (by decide) (Real.sqrt 5)
      push_cast at hsec; linarith
    have h1 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardU, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcardU] at h1
    rw [hμ_eq] at hsum_le
    have hle15 : ∑ q ∈ U, σ q * (T q : ℝ) ≤ 15 * Real.sqrt 5 := by linarith
    nlinarith
  rw [hμ_eq] at hL2
  have hcomb : 15 * ((Real.sqrt 5 - 1) * (3 - Real.sqrt 5)) ≤ (25 / 16 : ℝ) * (4 * y + y ^ 2) ^ 2 := by
    have : (((2 : ℝ) ^ 2 + 1) ^ 2 / (4 * (2 : ℝ) ^ 2)) = 25 / 16 := by norm_num
    linarith
  have hy_lb : (0.6475 : ℝ) ≤ y := by
    by_contra hlt; push Not at hlt
    have h1 : 4 * y + y ^ 2 < 4 * 0.6475 + 0.6475 ^ 2 := by nlinarith
    have h2 : (25 / 16 : ℝ) * (4 * y + y ^ 2) ^ 2 < (25 / 16) * (4 * 0.6475 + 0.6475 ^ 2) ^ 2 := by
      nlinarith
    have h3 : (Real.sqrt 5 - 1) * (3 - Real.sqrt 5) = 4 * Real.sqrt 5 - 8 := by nlinarith [h5_sq]
    nlinarith
  have hD2_lb : (0.1048 : ℝ) ≤ D2 := by nlinarith
  -- Apply `eps_ge_concave_of_le_r2` at `D0 = 0.1048 ≤ 1/5`!
  have hconc := eps_ge_concave_of_le_r2 (n := 2) hunit (D2 := 0.1048) (by norm_num) hD2_lb (by norm_num)
  have hsqrtD : (0.3237 : ℝ) ≤ Real.sqrt 0.1048 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2eq : 2 * (2 : ℝ) ^ 2 / ((2 : ℝ) ^ 2 + 1) = 8 / 5 := by norm_num
  rw [h2eq] at hconc
  have hr_eq : 1 / Real.sqrt ((2 : ℝ) ^ 2 + 1) = 1 / Real.sqrt 5 := by norm_num
  rw [hr_eq] at hconc
  have hr_lo : (0.4472 : ℝ) ≤ 1 / Real.sqrt 5 := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hval : (34 / 1000 : ℝ) ≤ (2 * (1 / Real.sqrt 5) * Real.sqrt 0.1048 - 0.1048) ^ 2 := by
    have hlin : (0.1847 : ℝ) ≤ 2 * (1 / Real.sqrt 5) * Real.sqrt 0.1048 - 0.1048 := by nlinarith
    nlinarith
  linarith

/-! ### Section 4: Kramers / Elliptic-Quadric `Q⁻(2n-1, 2)` Stability Theorem (`n = 4` Sharp!) -/

/-- Quadratic form `Q_0(a, b) = a · b ∈ ZMod 2` on phase space `PauliIdx n`. -/
def quadForm0 {n : ℕ} (p : PauliIdx n) : ZMod 2 := dot p.1 p.2

/-- Shifted quadratic form `Q_c(p) = Q_0(p) + ω(c, p)`. -/
def quadForm {n : ℕ} (c p : PauliIdx n) : ZMod 2 := quadForm0 p + symp c p

lemma quadForm0_add {n : ℕ} (p q : PauliIdx n) :
    quadForm0 (p + q) = quadForm0 p + quadForm0 q + symp p q := by
  simp only [quadForm0, Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right, symp, dot_comm q.1 p.2]
  ring

lemma quadForm_add {n : ℕ} (c p q : PauliIdx n) :
    quadForm c (p + q) = quadForm c p + quadForm c q + symp p q := by
  simp only [quadForm, quadForm0_add, symp_add_right]; ring

lemma quadForm_zero {n : ℕ} (c : PauliIdx n) : quadForm c 0 = 0 := by
  simp [quadForm, quadForm0, dot_zero_left, symp_zero_right]

/-- Character sum `∑_p (-1)^{Q_0(p) + ω(a, p)} = (-1)^{Q_0(a)} * 2^n` (completing the square!). -/
lemma sum_quadChar {n : ℕ} (a : PauliIdx n) :
    ∑ p : PauliIdx n, (if quadForm a p = 0 then (1 : ℤ) else -1) =
      (if quadForm0 a = 0 then (1 : ℤ) else -1) * (2 : ℤ) ^ n := by
  -- Note `Q_0(u, v) + ω((a1, a2), (u, v)) = (u + a1) · (v + a2) + a1 · a2`!
  have hshift : ∀ p : PauliIdx n,
      quadForm a p = dot (p.1 + a.1) (p.2 + a.2) + quadForm0 a := by
    intro p
    simp only [quadForm, quadForm0, symp, dot_add_left, dot_add_right, dot_comm a.2 p.1]
    ring_nf
    have h2 : ∀ z : ZMod 2, z * 2 = 0 := fun z => by rcases zmod2_cases z with rfl | rfl <;> decide
    rw [h2, add_zero]
  have hterm : ∀ p : PauliIdx n,
      (if quadForm a p = 0 then (1 : ℤ) else -1) =
      (if quadForm0 a = 0 then (1 : ℤ) else -1) * chi (p.1 + a.1) (p.2 + a.2) := by
    intro p; rw [hshift p]; simp only [chi]
    rcases zmod2_cases (dot (p.1 + a.1) (p.2 + a.2)) with h1 | h1 <;>
    rcases zmod2_cases (quadForm0 a) with h2 | h2 <;> simp [h1, h2]
    decide
  simp_rw [hterm, ← Finset.mul_sum, Fintype.sum_prod_type]
  congr 1
  have hre : ∑ x : F2 n, ∑ y : F2 n, chi (x + a.1) (y + a.2) =
      ∑ u : F2 n, ∑ v : F2 n, chi u v := by
    refine Fintype.sum_equiv (Equiv.addRight a.1) _ _ fun x => ?_
    exact Fintype.sum_equiv (Equiv.addRight a.2) _ _ fun y => rfl
  rw [hre]
  have hinner : ∀ u : F2 n, ∑ v : F2 n, chi u v = if u = 0 then (2 : ℤ) ^ n else 0 := fun u => by
    have : ∑ v : F2 n, chi u v = ∑ v : F2 n, chi v u :=
      Finset.sum_congr rfl fun v _ => chi_comm u v
    rw [this, sum_chi]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq' Finset.univ (0 : F2 n)]; simp

/-- Symplectic character sum: `∑_p (-1)^{ω(a, p)} = if a = 0 then 4^n else 0`. -/
lemma sum_sympSign_univ {n : ℕ} (a : PauliIdx n) :
    ∑ p : PauliIdx n, sympSign a p = if a = 0 then (4 : ℤ) ^ n else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [↓reduceIte, sympSign, symp_zero_left, Finset.sum_const, Finset.card_univ,
      card_PauliIdx, nsmul_eq_mul, mul_one]
    calc ((2 ^ n * 2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by push_cast; rfl
      _ = ((2 * 2 : ℤ) ^ n) := (mul_pow 2 2 n).symm
      _ = (4 : ℤ) ^ n := by norm_num
  · simp only [ha, ↓reduceIte]
    have hex : ∃ v : PauliIdx n, symp a v = 1 := by
      by_cases h1 : a.1 ≠ 0
      · have hexi : ∃ i : Fin n, a.1 i ≠ 0 := by by_contra h; push Not at h; exact h1 (funext h)
        obtain ⟨i, hi⟩ := hexi
        refine ⟨(0, eVec i), ?_⟩
        simp only [symp, dot_zero_right, add_zero, dot_eVec_right]
        exact (zmod2_cases (a.1 i)).resolve_left hi
      · push Not at h1
        have h2 : a.2 ≠ 0 := fun hc => ha (Prod.ext h1 hc)
        have hexi : ∃ i : Fin n, a.2 i ≠ 0 := by by_contra h; push Not at h; exact h2 (funext h)
        obtain ⟨i, hi⟩ := hexi
        refine ⟨(eVec i, 0), ?_⟩
        simp only [symp, dot_zero_right, zero_add, dot_eVec_right]
        exact (zmod2_cases (a.2 i)).resolve_left hi
    obtain ⟨v, hv⟩ := hex
    have hshift : ∑ p : PauliIdx n, sympSign a p = ∑ p : PauliIdx n, sympSign a (p + v) :=
      (Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl).symm
    have hneg : ∑ p : PauliIdx n, sympSign a (p + v) = -(∑ p : PauliIdx n, sympSign a p) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => by rw [sympSign_add_right]; simp [sympSign, hv]
    linarith

/-- Antiunitary Kramers operator `Θ_c(ψ) = P_c (conj ψ)` for `Q_0(c) = 1`. -/
def kramersConj {n : ℕ} (c : PauliIdx n) (ψ : QState n) : QState n :=
  pauliApply c (fun x => star (ψ x))

lemma pauliApply_conj {n : ℕ} (p : PauliIdx n) (ψ : QState n) :
    (fun x => star (pauliApply p ψ x)) =
      ((if quadForm0 p = 0 then (1 : ℂ) else -1)) • pauliApply p (fun x => star (ψ x)) := by
  ext x
  simp only [pauliApply, Pi.smul_apply, smul_eq_mul, star_mul, quadForm0, pauliPh]
  have hchi : star (chi p.2 x : ℂ) = (chi p.2 x : ℂ) := by simp
  rw [hchi]
  rcases zmod2_cases (dot p.1 p.2) with h | h <;> simp [h] <;> ring

/-- **Kramers Orthogonality (`Θ_c² = -I`)**: for every `c` with `Q_0(c) = 1` and every `ψ`,
    `⟨ψ | Θ_c ψ⟩ = 0`! -/
lemma innerProd_kramersConj_zero {n : ℕ} {c : PauliIdx n} (hc : quadForm0 c = 1) (ψ : QState n) :
    innerProd ψ (kramersConj c ψ) = 0 := by
  have h1 : innerProd ψ (kramersConj c ψ) = -(innerProd ψ (kramersConj c ψ)) := by
    simp only [innerProd, kramersConj, pauliApply, pauliPh, show dot c.1 c.2 = 1 from hc,
      show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.addRight c.1) _ _ fun x => ?_
    change star (ψ x) * (Complex.I * (chi c.2 x : ℂ) * star (ψ (x + c.1))) =
      -(star (ψ (x + c.1)) * (Complex.I * (chi c.2 (x + c.1) : ℂ) * star (ψ ((x + c.1) + c.1))))
    rw [f2_add_cancel_right, chi_add_right]
    have hch : chi c.2 c.1 = -1 := by
      simp only [chi, dot_comm c.2 c.1, show dot c.1 c.2 = 1 from hc,
        show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
    rw [hch]; push_cast; ring
  have h2 : (2 : ℂ) * innerProd ψ (kramersConj c ψ) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

lemma innerProd_kramersConj_self {n : ℕ} (c : PauliIdx n) (ψ : QState n) :
    innerProd (kramersConj c ψ) (kramersConj c ψ) = innerProd ψ ψ := by
  rw [kramersConj, innerProd_pauliApply_both]
  simp only [innerProd]
  refine Finset.sum_congr rfl fun x _ => by rw [star_star, mul_comm]

/-- Pauli expectations of `Θ_c ψ`: `⟨Θ_c ψ | P_p | Θ_c ψ⟩ = (-1)^{Q_c(p)} ⟨ψ | P_p | ψ⟩`! -/
lemma pauliExpect_kramersConj {n : ℕ} (c p : PauliIdx n) (ψ : QState n) :
    innerProd (kramersConj c ψ) (pauliApply p (kramersConj c ψ)) =
      (if quadForm c p = 0 then (1 : ℂ) else -1) * innerProd ψ (pauliApply p ψ) := by
  simp only [kramersConj]
  rw [← innerProd_pauliApply_right, pauliApply_comm c p, innerProd_smul_right, pauliApply_invol]
  -- Now compute `innerProd (fun x => star (ψ x)) (pauliApply p (fun x => star (ψ x)))`!
  have hconj : innerProd (fun x => star (ψ x)) (pauliApply p (fun x => star (ψ x))) =
      (if quadForm0 p = 0 then (1 : ℂ) else -1) * star (innerProd ψ (pauliApply p ψ)) := by
    have hpc := pauliApply_conj p ψ
    have hstar : star (innerProd ψ (pauliApply p ψ)) =
        innerProd (fun x => star (ψ x)) (fun x => star (pauliApply p ψ x)) := by
      simp only [innerProd, star_sum, star_mul, star_star]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [hstar, hpc, innerProd_smul_right]
    rcases zmod2_cases (quadForm0 p) with h | h <;> simp [h]
  rw [hconj, ← innerProd_conj_symm, innerProd_pauliApply_right, ← mul_assoc]
  congr 1
  simp only [quadForm, sympSign, symp_comm c p]
  rcases zmod2_cases (quadForm0 p) with h1 | h1 <;> rcases zmod2_cases (symp p c) with h2 | h2
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide]

/-- **10-Line Matrix-Free Quaternionic Kramers Frobenius Inequality**:
    For ANY `c` with `Q_0(c) = 1` and ANY `a : PauliIdx n → ℝ` supported on `Q_c(p) = 0`,
      `2 * frobSq ((pauliExpand a)²) ≤ (frobSq (pauliExpand a))²`!! -/
lemma frobSq_sq_kramers_le {n : ℕ} {c : PauliIdx n} (hc : quadForm0 c = 1)
    {a : PauliIdx n → ℝ} (hsupp : ∀ p : PauliIdx n, quadForm c p ≠ 0 → a p = 0) :
    2 * frobSq (matMul (pauliExpand a) (pauliExpand a)) ≤ (frobSq (pauliExpand a)) ^ 2 := by
  set A := pauliExpand a
  have hAh : IsHermMat A := pauliExpand_herm a
  -- Key equivariance: `matApply A (kramersConj c v) = kramersConj c (matApply A v)` for all `v`!
  have hequiv : ∀ v : QState n, matApply A (kramersConj c v) = kramersConj c (matApply A v) := by
    intro v
    have hA_apply : ∀ u : QState n, matApply A u = ∑ p : PauliIdx n, (a p : ℂ) • pauliApply p u := by
      intro u; ext x
      simp only [matApply, A, pauliExpand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]; congr 1
        exact congr_fun (pauliMat_apply p u) x
    rw [hA_apply, hA_apply]
    simp only [kramersConj]
    have hlin : pauliApply c (fun x => star ((∑ p : PauliIdx n, (a p : ℂ) • pauliApply p v) x)) =
        ∑ p : PauliIdx n, (a p : ℂ) •
          pauliApply c (fun x => star (pauliApply p v x)) := by
      ext x
      simp only [pauliApply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul,
        Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hlin]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : quadForm c p = 0
    · rw [pauliApply_conj p v, pauliApply_smul, pauliApply_comm p c, smul_smul, smul_smul]
      congr 1
      have hsign : (sympSign p c : ℂ) * (a p : ℂ) =
          (a p : ℂ) * (if quadForm0 p = 0 then 1 else -1) := by
        simp only [quadForm, symp_comm c p] at hp
        simp only [sympSign]
        rcases zmod2_cases (quadForm0 p) with h1 | h1 <;> rcases zmod2_cases (symp p c) with h2 | h2
        · simp [h1, h2]
        · simp [h1, h2] at hp
        · simp [h1, h2] at hp
        · simp [h1, h2]
      linear_combination hsign
    · rw [hsupp p hp]; simp
  -- Now apply `bessel_two_orth` column-by-column to `{col_y(A), kramersConj c (col_y(A))}`!
  have hcol : ∀ y : F2 n,
      2 * (∑ x : F2 n, Complex.normSq (matMul A A x y)) ≤
        frobSq A * (∑ z : F2 n, Complex.normSq (A z y)) := by
    intro y
    let u : QState n := fun z => A z y
    let ut : QState n := kramersConj c u
    have horth : innerProd u ut = 0 := innerProd_kramersConj_zero hc u
    have hnorm : (innerProd ut ut).re = (innerProd u u).re := by
      rw [innerProd_kramersConj_self]
    have hrow : ∀ x : F2 n,
        Complex.normSq (matApply A u x) + Complex.normSq (matApply A ut x) ≤
          (∑ z : F2 n, Complex.normSq (A x z)) * (∑ z : F2 n, Complex.normSq (A z y)) := by
      intro x
      let w : QState n := fun z => star (A x z)
      have hwu : innerProd w u = matApply A u x := by
        simp only [innerProd, w, u, matApply, star_star]
      have hwut : innerProd w ut = matApply A ut x := by
        simp only [innerProd, w, matApply, star_star]
      have hww : (innerProd w w).re = ∑ z : F2 n, Complex.normSq (A x z) := by
        simp only [innerProd_self_re, w, Complex.star_def, Complex.normSq_conj]
      have huu : (innerProd u u).re = ∑ z : F2 n, Complex.normSq (A z y) := by
        simp only [innerProd_self_re, u]
      have hb := bessel_two_orth w u ut horth hnorm
      rwa [hwu, hwut, hww, huu] at hb
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun x _ => hrow x
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    have hA_ut : ∑ x : F2 n, Complex.normSq (matApply A ut x) =
        ∑ x : F2 n, Complex.normSq (matApply A u x) := by
      have h1 : (innerProd (matApply A ut) (matApply A ut)).re =
          (innerProd (matApply A u) (matApply A u)).re := by
        rw [hequiv u, innerProd_kramersConj_self]
      simpa [innerProd_self_re] using h1
    have hAu_eq : ∀ x, matApply A u x = matMul A A x y := fun _ => rfl
    simp_rw [hA_ut, hAu_eq] at hsum
    change 2 * ∑ x : F2 n, Complex.normSq (matMul A A x y) ≤
      (∑ x : F2 n, ∑ z : F2 n, Complex.normSq (A x z)) * ∑ z : F2 n, Complex.normSq (A z y)
    linarith
  have htot := Finset.sum_le_sum (s := Finset.univ) fun y _ => hcol y
  rw [← Finset.mul_sum, ← Finset.mul_sum] at htot
  have hl : ∑ y : F2 n, ∑ x : F2 n, Complex.normSq (matMul A A x y) = frobSq (matMul A A) :=
    Finset.sum_comm
  have hr : ∑ y : F2 n, ∑ z : F2 n, Complex.normSq (A z y) = frobSq A := Finset.sum_comm
  rw [hl, hr, ← sq] at htot; exact htot

/-- **Matrix-Free Kramers Cubic Trace Bound**:
    If `frobSq A = 1 / 2` and `A` is supported on `Q_c(p) = 0` (`Q_0(c) = 1`),
    then `(Tr(A³)).re ≤ 1 / 4`! -/
lemma matTr_cube_kramers_le {n : ℕ} {c : PauliIdx n} (hc : quadForm0 c = 1)
    {a : PauliIdx n → ℝ} (hsupp : ∀ p : PauliIdx n, quadForm c p ≠ 0 → a p = 0)
    (hfrob : frobSq (pauliExpand a) = 1 / 2) :
    (matTr (matMul (pauliExpand a) (matMul (pauliExpand a) (pauliExpand a)))).re ≤ 1 / 4 := by
  set A := pauliExpand a
  have hre : (matTr (matMul A (matMul A A))).re ^ 2 ≤
      Complex.normSq (matTr (matMul A (matMul A A))) := by
    rw [Complex.normSq_apply]; nlinarith
  have h1 := normSq_matTr_mul_le A (matMul A A)
  have h2 := frobSq_sq_kramers_le hc hsupp
  rw [hfrob] at h1 h2
  nlinarith

/-- Elliptic-quadric counts from `sum_quadChar` and `sum_sympSign_univ` (for `n ≥ 3`). -/
lemma card_elliptic_quadric {n : ℕ} (hn : 3 ≤ n) {c : PauliIdx n} (hc : quadForm0 c = 1) :
    ((Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c p = 0).card : ℤ) =
      (2 ^ (n - 1) - 1) * (2 ^ n + 1) := by
  have hsum := sum_quadChar c
  simp only [hc, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte] at hsum
  let A := Finset.univ.filter fun p : PauliIdx n => quadForm c p = 0
  let B := Finset.univ.filter fun p : PauliIdx n => ¬quadForm c p = 0
  have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => quadForm c p = 0)
    (fun p => if quadForm c p = 0 then (1 : ℤ) else -1)
  have hA : ∑ p ∈ A, (if quadForm c p = 0 then (1 : ℤ) else -1) = (A.card : ℤ) := by
    have : ∀ p ∈ A, (if quadForm c p = 0 then (1 : ℤ) else -1) = 1 := fun p hp => by
      simp [(Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB : ∑ p ∈ B, (if quadForm c p = 0 then (1 : ℤ) else -1) = -(B.card : ℤ) := by
    have : ∀ p ∈ B, (if quadForm c p = 0 then (1 : ℤ) else -1) = -1 := fun p hp => by
      simp [(Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hAB : (A.card : ℤ) + (B.card : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (PauliIdx n)))
      (p := fun p => quadForm c p = 0)
    have h2 : (Finset.univ : Finset (PauliIdx n)).card = 2 ^ n * 2 ^ n := by
      rw [Finset.card_univ, card_PauliIdx]
    change A.card + B.card = _ at h1
    rw [h2] at h1; exact_mod_cast h1
  have h0A : (0 : PauliIdx n) ∈ A := by simp [A, quadForm_zero]
  have hset : (Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c p = 0) = A.erase 0 := by
    ext p; simp [A, and_comm]
  rw [hset, Finset.card_erase_of_mem h0A]
  have hApos : 1 ≤ A.card := Finset.one_le_card.mpr ⟨0, h0A⟩
  have h2n : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have halg : (2 : ℤ) ^ n * (2 : ℤ) ^ n - (2 : ℤ) ^ n - 2 =
      2 * (((2 : ℤ) ^ (n - 1) - 1) * ((2 : ℤ) ^ n + 1)) := by rw [h2n]; ring
  rw [Nat.cast_sub hApos]; push_cast; linarith

lemma card_elliptic_lines_at {n : ℕ} (hn : 3 ≤ n) {c q : PauliIdx n}
    (hc : quadForm0 c = 1) (hq0 : q ≠ 0) (hqQ : quadForm c q = 0) :
    (Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ quadForm c p = 0 ∧ symp q p = 0).card =
      2 * ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1)) := by
  -- 4-term character sum `∑ p, (1 + (-1)^{ω(q, p)}) * (1 + (-1)^{Q_c(p)}) = 4^n - 2 * 2^n`!
  let f1 : PauliIdx n → ℤ := fun p => sympSign q p
  let f2 : PauliIdx n → ℤ := fun p => if quadForm c p = 0 then 1 else -1
  have hs1 : ∑ p : PauliIdx n, f1 p = 0 := by
    simp only [f1, sum_sympSign_univ, hq0, ↓reduceIte]
  have hs2 : ∑ p : PauliIdx n, f2 p = -((2 : ℤ) ^ n) := by
    have h := sum_quadChar c
    simp only [hc, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte] at h
    simpa [f2] using h
  have hs12 : ∑ p : PauliIdx n, f1 p * f2 p = -((2 : ℤ) ^ n) := by
    have hterm : ∀ p : PauliIdx n, f1 p * f2 p =
        if quadForm (c + q) p = 0 then (1 : ℤ) else -1 := by
      intro p
      simp only [f1, f2, sympSign, quadForm, symp_add_left]
      rcases zmod2_cases (symp q p) with h1 | h1 <;> rcases zmod2_cases (quadForm0 p + symp c p) with h2 | h2
      · simp [h1, h2]
      · simp [h1, h2]
      · have hsum1 : quadForm0 p + (symp c p + 1) = 1 := by rw [← add_assoc, h2, zero_add]
        simp [h1, h2, hsum1]
      · simp only [h1, h2, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, mul_neg, neg_neg, mul_one]
        have : quadForm0 p + (symp c p + 1) = (quadForm0 p + symp c p) + 1 := by ring
        rw [this, h2]; simp [show (1 : ZMod 2) + 1 = 0 by decide]
    simp_rw [hterm, sum_quadChar (c + q)]
    have hcq : quadForm0 (c + q) = 1 := by
      rw [quadForm0_add, hc]
      have : quadForm0 q + symp c q = 0 := hqQ
      rw [show 1 + quadForm0 q + symp c q = 1 + (quadForm0 q + symp c q) by ring, this, add_zero]
    simp [hcq]
  have hprod : ∑ p : PauliIdx n, (1 + f1 p) * (1 + f2 p) = (4 : ℤ) ^ n - 2 * (2 : ℤ) ^ n := by
    have hexp : ∀ p, (1 + f1 p) * (1 + f2 p) = 1 + f1 p + f2 p + f1 p * f2 p := fun _ => by ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have h1 : ∑ _ : PauliIdx n, (1 : ℤ) = (4 : ℤ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul, mul_one]
      calc ((2 ^ n * 2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by push_cast; rfl
        _ = (2 * 2 : ℤ) ^ n := (mul_pow 2 2 n).symm
        _ = (4 : ℤ) ^ n := by norm_num
    rw [h1, hs1, hs2, hs12]; ring
  let A := Finset.univ.filter fun p : PauliIdx n => quadForm c p = 0 ∧ symp q p = 0
  have h4A : ∑ p : PauliIdx n, (1 + f1 p) * (1 + f2 p) = 4 * (A.card : ℤ) := by
    have hterm : ∀ p : PauliIdx n, (1 + f1 p) * (1 + f2 p) =
        if quadForm c p = 0 ∧ symp q p = 0 then 4 else 0 := by
      intro p; simp only [f1, f2, sympSign]
      by_cases h1 : quadForm c p = 0 <;> by_cases h2 : symp q p = 0 <;> simp [h1, h2]
    simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have h0A : (0 : PauliIdx n) ∈ A := by simp [A, quadForm_zero, symp_zero_right]
  have hqA : q ∈ A := by simp [A, hqQ, symp_self]
  have hset : (Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ p ≠ q ∧ quadForm c p = 0 ∧ symp q p = 0) =
      (A.erase 0).erase q := by
    ext p; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]; tauto
  rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hq0, hqA⟩), Finset.card_erase_of_mem h0A]
  have hA2 : 2 ≤ A.card := by
    have hne : (0 : PauliIdx n) ≠ q := Ne.symm hq0
    have hsub : ({0, q} : Finset (PauliIdx n)) ⊆ A := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h0A
      · rw [Finset.mem_singleton.mp hx]; exact hqA
    have := Finset.card_le_card hsub; rwa [Finset.card_pair hne] at this
  have h2n : (2 : ℤ) ^ n = 4 * (2 : ℤ) ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have h2n1 : (2 : ℤ) ^ (n - 1) = 2 * (2 : ℤ) ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have h4n : (4 : ℤ) ^ n = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by
    calc (4 : ℤ) ^ n = (2 * 2 : ℤ) ^ n := by norm_num
      _ = (2 : ℤ) ^ n * (2 : ℤ) ^ n := mul_pow 2 2 n
  have hge1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
  have hA1 : 1 ≤ A.card := by omega
  have hA1' : 1 ≤ A.card - 1 := by omega
  have halg : (4 : ℤ) ^ n - 2 * (2 : ℤ) ^ n - 8 =
      4 * (2 * (((2 : ℤ) ^ (n - 2) - 1) * ((2 : ℤ) ^ (n - 1) + 1))) := by
    rw [h4n, h2n, h2n1]; ring
  zify [hA1, hA1', hge1]; linarith

lemma card_elliptic_centers {n : ℕ} (hn : 2 ≤ n) :
    ((Finset.univ.filter fun c : PauliIdx n => quadForm0 c = 1).card : ℤ) =
      (2 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ n - 1) := by
  have hsum := sum_quadChar (n := n) 0
  simp only [quadForm, quadForm0, Prod.fst_zero, Prod.snd_zero, dot_zero_left, symp_zero_left,
    add_zero, ↓reduceIte, one_mul] at hsum
  let A := Finset.univ.filter fun c : PauliIdx n => quadForm0 c = 0
  let B := Finset.univ.filter fun c : PauliIdx n => quadForm0 c = 1
  have hB_eq : B = Finset.univ.filter fun c : PauliIdx n => ¬quadForm0 c = 0 := by
    ext c; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod2_cases (quadForm0 c) with h | h <;> simp [h]
  have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : PauliIdx n => quadForm0 c = 0)
    (fun c => if dot c.1 c.2 = 0 then (1 : ℤ) else -1)
  have hA : ∑ c ∈ A, (if dot c.1 c.2 = 0 then (1 : ℤ) else -1) = (A.card : ℤ) := by
    have : ∀ c ∈ A, (if dot c.1 c.2 = 0 then (1 : ℤ) else -1) = 1 := fun c hc => by
      have h : dot c.1 c.2 = 0 := (Finset.mem_filter.mp hc).2
      simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB : ∑ c ∈ Finset.univ.filter (fun c : PauliIdx n => ¬quadForm0 c = 0),
      (if dot c.1 c.2 = 0 then (1 : ℤ) else -1) = -(B.card : ℤ) := by
    rw [← hB_eq]
    have : ∀ c ∈ B, (if dot c.1 c.2 = 0 then (1 : ℤ) else -1) = -1 := fun c hc => by
      have h1 : dot c.1 c.2 = 1 := (Finset.mem_filter.mp hc).2
      simp [h1]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring
  have hAB : (A.card : ℤ) + (B.card : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (PauliIdx n)))
      (p := fun c => quadForm0 c = 0)
    rw [← hB_eq] at h1
    have h2 : (Finset.univ : Finset (PauliIdx n)).card = 2 ^ n * 2 ^ n := by
      rw [Finset.card_univ, card_PauliIdx]
    change A.card + B.card = _ at h1
    rw [h2] at h1; exact_mod_cast h1
  have h2n : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have halg : (2 : ℤ) ^ n * (2 : ℤ) ^ n - (2 : ℤ) ^ n =
      2 * ((2 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ n - 1)) := by rw [h2n]; ring
  have hdiff : (A.card : ℤ) - (B.card : ℤ) = (2 : ℤ) ^ n := by linarith
  change (B.card : ℤ) = _; linarith

lemma card_elliptic_centers_containing {n : ℕ} (hn : 2 ≤ n) {p : PauliIdx n} (hp : p ≠ 0) :
    ((Finset.univ.filter fun c : PauliIdx n => quadForm0 c = 1 ∧ quadForm c p = 0).card : ℤ) =
      (2 : ℤ) ^ (n - 2) * ((2 : ℤ) ^ n - 2) := by
  let f1 : PauliIdx n → ℤ := fun c => if quadForm0 c = 0 then 1 else -1
  let f2 : PauliIdx n → ℤ := fun c => if quadForm c p = 0 then 1 else -1
  have hs1 : ∑ c : PauliIdx n, f1 c = (2 : ℤ) ^ n := by
    have h := sum_quadChar (n := n) 0
    simp only [quadForm, quadForm0, Prod.fst_zero, Prod.snd_zero, dot_zero_left, symp_zero_left,
      add_zero, ↓reduceIte, one_mul] at h
    exact h
  have hs2 : ∑ c : PauliIdx n, f2 c = 0 := by
    have hterm : ∀ c : PauliIdx n, f2 c = (if quadForm0 p = 0 then (1 : ℤ) else -1) * sympSign p c := by
      intro c; simp only [f2, quadForm, sympSign, symp_comm c p]
      rcases zmod2_cases (quadForm0 p) with h1 | h1 <;> rcases zmod2_cases (symp p c) with h2 | h2
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2, show (1 : ZMod 2) + 1 = 0 by decide]
    simp only [hterm, ← Finset.mul_sum, sum_sympSign_univ, hp, ↓reduceIte, mul_zero]
  have hs12 : ∑ c : PauliIdx n, f1 c * f2 c = (2 : ℤ) ^ n := by
    have hterm : ∀ c : PauliIdx n, f1 c * f2 c =
        (if quadForm0 p = 0 then (1 : ℤ) else -1) * (if quadForm p c = 0 then 1 else -1) := by
      intro c; simp only [f1, f2, quadForm, symp_comm c p]
      rcases zmod2_cases (quadForm0 c) with h1 | h1 <;>
      rcases zmod2_cases (quadForm0 p) with h2 | h2 <;>
      rcases zmod2_cases (symp p c) with h3 | h3 <;>
        simp [h1, h2, h3, show (1 : ZMod 2) + 1 = 0 by decide]
    simp_rw [hterm, ← Finset.mul_sum, sum_quadChar p]
    rcases zmod2_cases (quadForm0 p) with h | h <;> simp [h]
  -- `∑ c, (1 - f1 c) * (1 + f2 c) = 4 * card`!
  have hprod : ∑ c : PauliIdx n, (1 - f1 c) * (1 + f2 c) = (4 : ℤ) ^ n - 2 * (2 : ℤ) ^ n := by
    have hexp : ∀ c, (1 - f1 c) * (1 + f2 c) = 1 - f1 c + f2 c - f1 c * f2 c := fun _ => by ring
    simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ _ : PauliIdx n, (1 : ℤ) = (4 : ℤ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul, mul_one]
      calc ((2 ^ n * 2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by push_cast; rfl
        _ = (2 * 2 : ℤ) ^ n := (mul_pow 2 2 n).symm
        _ = (4 : ℤ) ^ n := by norm_num
    rw [h1, hs1, hs2, hs12]; ring
  let A := Finset.univ.filter fun c : PauliIdx n => quadForm0 c = 1 ∧ quadForm c p = 0
  have h4A : ∑ c : PauliIdx n, (1 - f1 c) * (1 + f2 c) = 4 * (A.card : ℤ) := by
    have hterm : ∀ c : PauliIdx n, (1 - f1 c) * (1 + f2 c) =
        if quadForm0 c = 1 ∧ quadForm c p = 0 then 4 else 0 := by
      intro c; simp only [f1, f2]
      rcases zmod2_cases (quadForm0 c) with h1 | h1 <;> by_cases h2 : quadForm c p = 0 <;> simp [h1, h2]
    simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have h2n : (2 : ℤ) ^ n = 4 * (2 : ℤ) ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have h4n : (4 : ℤ) ^ n = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by
    calc (4 : ℤ) ^ n = (2 * 2 : ℤ) ^ n := by norm_num
      _ = (2 : ℤ) ^ n * (2 : ℤ) ^ n := mul_pow 2 2 n
  have halg : (4 : ℤ) ^ n - 2 * (2 : ℤ) ^ n = 4 * ((2 : ℤ) ^ (n - 2) * ((2 : ℤ) ^ n - 2)) := by
    rw [h4n, h2n]; ring
  change (A.card : ℤ) = _; linarith

/-- **Kramers / Elliptic-Quadric Stability Package (`n ≥ 4`, fixed `c` with `Q_0(c) = 1`)**:
    On each elliptic quadric `Q_c⁻ = {p ≠ 0 | Q_c(p) = 0}` (`N_- = (d/2 - 1)(d + 1)` points),
    setting `D2_c := ∑_{p ∈ Q_c⁻} (|c p| - r)²` and `y_c := √(d * D2_c)`:
    there exist odd integers `T_c q ∈ 2ℤ + 1` (`q ∈ Q_c⁻`) such that:
    1. `∑_{q ∈ Q_c⁻} (σ q * T_c q - μ_-)² ≤ ((d+1)² / (4 d)) * ((d/2) y_c + (1 / √2) y_c²)²`,
    2. `∑_{q ∈ Q_c⁻} σ q * T_c q ≤ N_- * μ_-`, where `μ_- = (d/4 - 1) √(d + 1)`. -/
lemma kramers_quadric_stability_fixed {n : ℕ} (hn : 4 ≤ n) {ψ : QState n} (hunit : IsUnitState ψ)
    {c0 : PauliIdx n} (hc0 : quadForm0 c0 = 1) :
    let d : ℝ := (2 : ℝ) ^ n
    let r : ℝ := 1 / Real.sqrt (d + 1)
    let μm : ℝ := (d / 4 - 1) * Real.sqrt (d + 1)
    let c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
    let σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
    let Qm := Finset.univ.filter fun p : PauliIdx n => p ≠ 0 ∧ quadForm c0 p = 0
    let D2m : ℝ := ∑ p ∈ Qm, (|c p| - r) ^ 2
    let ym : ℝ := Real.sqrt (d * D2m)
    ∃ Tm : PauliIdx n → ℤ,
      (∀ q ∈ Qm, Tm q % 2 = 1) ∧
      (∑ q ∈ Qm, (σ q * (Tm q : ℝ) - μm) ^ 2 ≤
        ((d + 1) ^ 2 / (4 * d)) * ((d / 2) * ym + ym ^ 2 / Real.sqrt 2) ^ 2) ∧
      (∑ q ∈ Qm, σ q * (Tm q : ℝ) ≤ (d / 2 - 1) * (d + 1) * μm) := by
  intro d r μm c σ Qm D2m ym
  have hd_pos : 0 < d := by positivity
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hs_pos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr (by linarith)
  have hs_ne : Real.sqrt (d + 1) ≠ 0 := ne_of_gt hs_pos
  have hd1_pos : 0 < d + 1 := by linarith
  have hd1_ne : d + 1 ≠ 0 := ne_of_gt hd1_pos
  have hr2 : r ^ 2 = 1 / (d + 1) := by simp only [r, div_pow, one_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
  have hce0 : c 0 = 1 := pauliExpect_zero_re hunit
  have hσ_pm : ∀ q ∈ Qm, σ q = 1 ∨ σ q = -1 := fun q hq => by
    have hq0 : q ≠ 0 := (Finset.mem_filter.mp hq).2.1
    simp only [σ, hq0, ↓reduceIte]; split_ifs <;> simp
  have hσ_sq : ∀ q ∈ Qm, (σ q) ^ 2 = 1 := fun q hq => by
    rcases hσ_pm q hq with h | h <;> rw [h] <;> norm_num
  have hcardQm : (Qm.card : ℝ) = (d / 2 - 1) * (d + 1) := by
    have hZ := card_elliptic_quadric (by omega) hc0
    have hR : (Qm.card : ℝ) = ((2 : ℝ) ^ (n - 1) - 1) * (d + 1) := by
      have hcast := congr_arg (Int.cast (R := ℝ)) hZ
      push_cast at hcast
      simpa [Qm, d] using hcast
    have h2 : (2 : ℝ) ^ (n - 1) = d / 2 := by
      have : d = 2 * (2 : ℝ) ^ (n - 1) := by
        simp only [d]
        conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        ring
      linarith
    rw [hR, h2]
  -- Extract odd integers `Tm q` on `Qm`!
  let σI : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  have hσI_cast : ∀ p, (σI p : ℝ) = σ p := fun p => by simp only [σI, σ]; split_ifs <;> norm_num
  have hexTm : ∀ q : PauliIdx n, ∃ Tq : ℤ,
      (q ∈ Qm → Tq % 2 = 1 ∧
        (∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p) *
          (if quadForm c0 (q + p) = 0 then (1 : ℝ) else 0)) = 2 * (Tq : ℝ)) := by
    intro q
    by_cases hq : q ∈ Qm
    · obtain ⟨hq0, hqQ⟩ := (Finset.mem_filter.mp hq).2
      let Cq := Finset.univ.filter fun p : PauliIdx n =>
        p ≠ 0 ∧ p ≠ q ∧ quadForm c0 p = 0 ∧ symp q p = 0
      let γI : PauliIdx n → ℤ := fun p => if pauliPhase q p = 1 then 1 else -1
      have hγI_eq : ∀ p ∈ Cq, (γI p : ℝ) = (pauliPhase q p).re := fun p hp => by
        have hs : symp q p = 0 := (Finset.mem_filter.mp hp).2.2.2.2
        rcases (pauliPhase_re_cases q p).1 hs with h1 | h1
        · simp [γI, h1]
        · rw [show γI p = -1 by simp only [γI, h1]; norm_num, h1]; norm_num
      have hγI_inv : ∀ p ∈ Cq, γI (q + p) = γI p := fun p hp => by
        have hs : symp q p = 0 := (Finset.mem_filter.mp hp).2.2.2.2
        have hph := pauliPhase_add_right q p
        simp only [sympSign, hs, ↓reduceIte, Int.cast_one, one_mul] at hph
        simp only [γI, hph]
      have hsum_eq : ∑ p ∈ Qm.erase q, (pauliPhase q p).re * σ p * σ (q + p) *
            (if quadForm c0 (q + p) = 0 then (1 : ℝ) else 0) =
          ((∑ p ∈ Cq, γI p * σI p * σI (q + p) : ℤ) : ℝ) := by
        have hsub : Cq = (Qm.erase q).filter (fun p => symp q p = 0) := by
          ext p; simp only [Cq, Qm, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]; tauto
        rw [← Finset.sum_filter_add_sum_filter_not (Qm.erase q) (fun p => symp q p = 0)]
        have hzero : ∑ p ∈ (Qm.erase q).filter (fun p => ¬symp q p = 0),
            (pauliPhase q p).re * σ p * σ (q + p) *
              (if quadForm c0 (q + p) = 0 then (1 : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hs1 : symp q p = 1 := (zmod2_cases (symp q p)).resolve_left (Finset.mem_filter.mp hp).2
          rw [(pauliPhase_re_cases q p).2 hs1]; simp
        rw [hzero, add_zero, ← hsub, Int.cast_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        obtain ⟨_, _, hpQ, hsp⟩ := (Finset.mem_filter.mp hp).2
        have hqpQ : quadForm c0 (q + p) = 0 := by rw [quadForm_add, hqQ, hpQ, hsp]; simp
        simp only [hqpQ, ↓reduceIte, mul_one]
        push_cast; rw [hγI_eq p hp, hσI_cast p, hσI_cast (q + p)]
      have hpar := sum_invol_parity Cq (fun p => q + p) (fun p => γI p * σI p * σI (q + p))
        (fun p hp => by
          obtain ⟨hp0, hpq, hpQ, hsp⟩ := (Finset.mem_filter.mp hp).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
          · intro hc; have := congr_arg (q + ·) hc; rw [pauliIdx_add_cancel_left, add_zero] at this
            exact hpq this
          · intro hc; have := congr_arg (q + ·) hc; rw [pauliIdx_add_cancel_left, pauliIdx_add_self] at this
            exact hp0 this
          · rw [quadForm_add, hqQ, hpQ, hsp]; simp
          · rw [symp_add_right, symp_self, zero_add]; exact hsp)
        (fun p _ => pauliIdx_add_cancel_left q p)
        (fun p _ hc => by
          have := congr_arg (· + p) hc; rw [pauliIdx_add_cancel_right, pauliIdx_add_self] at this
          exact hq0 this)
        (fun p hp => by rw [pauliIdx_add_cancel_left, hγI_inv p hp]; ring)
        (fun p hp => by
          obtain ⟨hp0, hpq, _, _⟩ := (Finset.mem_filter.mp hp).2
          have hqp0 : q + p ≠ 0 := fun hc => hpq (by
            have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
          have h1 : γI p = 1 ∨ γI p = -1 := by simp only [γI]; split_ifs <;> simp
          have h2 : σI p = 1 ∨ σI p = -1 := by simp only [σI, hp0, ↓reduceIte]; split_ifs <;> simp
          have h3 : σI (q + p) = 1 ∨ σI (q + p) = -1 := by
            simp only [σI, hqp0, ↓reduceIte]; split_ifs <;> simp
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
            simp [h1, h2, h3])
        ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1)) (card_elliptic_lines_at (by omega) hc0 hq0 hqQ)
      obtain ⟨Tq, hTq_eq, hTq_mod⟩ := hpar
      refine ⟨Tq, fun _ => ⟨?_, ?_⟩⟩
      · have hodd : (((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1) : ℕ) : ℤ) % 2 = 1 := by
          have h1 : 2 ∣ 2 ^ (n - 2) := ⟨2 ^ (n - 3), by
            conv_lhs => rw [show n - 2 = (n - 3) + 1 by omega, pow_succ]
            ring⟩
          have h2 : 2 ∣ 2 ^ (n - 1) := ⟨2 ^ (n - 2), by
            conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
            ring⟩
          have hge1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by norm_num)
          obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
          have hnat : ((2 ^ (n - 2) - 1) * (2 ^ (n - 1) + 1)) % 2 = 1 := by
            have ha : (2 * k1 - 1) % 2 = 1 := by omega
            have hb : (2 * k2 + 1) % 2 = 1 := by omega
            rw [hk1, hk2, Nat.mul_mod, ha, hb]
          exact_mod_cast hnat
        omega
      · rw [hsum_eq, hTq_eq]; push_cast; ring
    · exact ⟨0, fun h => absurd h hq⟩
  choose Tm hTm using hexTm
  -- Build rank-2 projector `P = stateProj ψ + stateProj (kramersConj c0 ψ)`, `ρ_c = (1/2) P`, `Δ_-`, `ρ̃_c`!
  let ψt := kramersConj c0 ψ
  have hψt_unit : IsUnitState ψt := by rw [IsUnitState, innerProd_kramersConj_self]; exact hunit
  have horth : innerProd ψ ψt = 0 := innerProd_kramersConj_zero hc0 ψ
  let P := matAdd (stateProj ψ) (stateProj ψt)
  have hP_herm : IsHermMat P := isHermMat_add (stateProj_herm ψ) (stateProj_herm ψt)
  have hP_idem : matMul P P = P := by
    have h12 : matMul (stateProj ψ) (stateProj ψt) = fun _ _ => 0 := by
      ext x y; simp only [matMul, stateProj]
      have : ∑ z : F2 n, ψ x * star (ψ z) * (ψt z * star (ψt y)) =
          ψ x * star (ψt y) * innerProd ψ ψt := by
        simp only [innerProd, Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
      rw [this, horth, mul_zero]
    have h21 : matMul (stateProj ψt) (stateProj ψ) = fun _ _ => 0 := by
      ext x y; simp only [matMul, stateProj]
      have h0 : innerProd ψt ψ = 0 := by rw [innerProd_conj_symm, horth, star_zero]
      have : ∑ z : F2 n, ψt x * star (ψt z) * (ψ z * star (ψ y)) =
          ψt x * star (ψ y) * innerProd ψt ψ := by
        simp only [innerProd, Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
      rw [this, h0, mul_zero]
    simp only [P, matMul_add_left, matMul_add_right, stateProj_idem hunit, stateProj_idem hψt_unit,
      h12, h21]
    ext x y; simp [matAdd]
  let ρc := matSmul ((1 / 2 : ℝ) : ℂ) P
  -- Show `ρc = pauliExpand (fun p => if quadForm c0 p = 0 then c p / d else 0)`!
  have hρc_exp : ρc = pauliExpand (fun p => if quadForm c0 p = 0 then c p / d else 0) := by
    have h1 := stateProj_eq_pauliExpand ψ
    have h2 := stateProj_eq_pauliExpand ψt
    have hsum : matSmul ((2 : ℂ) ^ n) P =
        pauliExpand (fun p => (innerProd ψ (pauliApply p ψ)).re +
          (innerProd ψt (pauliApply p ψt)).re) := by
      rw [pauliExpand_add, ← h1, ← h2]; ext x y; simp [P, matSmul, matAdd]; ring
    have hcoeff : ∀ p, (innerProd ψ (pauliApply p ψ)).re + (innerProd ψt (pauliApply p ψt)).re =
        if quadForm c0 p = 0 then 2 * c p else 0 := by
      intro p
      have hpe := congr_arg Complex.re (pauliExpect_kramersConj c0 p ψ)
      by_cases hq : quadForm c0 p = 0
      · simp only [hq, ↓reduceIte, one_mul] at hpe ⊢; simp only [c, ψt]; linarith
      · simp only [hq, ↓reduceIte, neg_mul, one_mul, Complex.neg_re] at hpe ⊢; simp only [ψt]; linarith
    simp_rw [hcoeff] at hsum
    ext x y
    have hxy := congr_fun (congr_fun hsum x) y
    simp only [ρc, matSmul, pauliExpand] at hxy ⊢
    have hdC : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hd_eq : (d : ℂ) = (2 : ℂ) ^ n := by simp [d]
    calc ((1 / 2 : ℝ) : ℂ) * P x y
        = (1 / (2 * (2 : ℂ) ^ n)) * ((2 : ℂ) ^ n * P x y) := by push_cast; field_simp [hdC]
      _ = (1 / (2 * (2 : ℂ) ^ n)) *
            ∑ p : PauliIdx n, (((if quadForm c0 p = 0 then 2 * c p else 0) : ℝ) : ℂ) * pauliMat p x y := by
          rw [hxy]
      _ = ∑ p : PauliIdx n, (((if quadForm c0 p = 0 then c p / d else 0) : ℝ) : ℂ) * pauliMat p x y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hq : quadForm c0 p = 0
          · simp only [hq, ↓reduceIte, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, hd_eq]
            field_simp [hdC]
          · simp [hq]
  -- Define `δm`, `Δm`, `a_rtm`, `rtc`!
  let δm : PauliIdx n → ℝ := fun p => if p ≠ 0 ∧ quadForm c0 p = 0 then c p - r * σ p else 0
  let Δm := pauliExpand δm
  let a_rtm : PauliIdx n → ℝ := fun p =>
    if p = 0 then 1 / d else if quadForm c0 p = 0 then (r / d) * σ p else 0
  let rtc := pauliExpand a_rtm
  have hδm_supp : ∀ p, quadForm c0 p ≠ 0 → δm p = 0 := fun p hp => by simp [δm, hp]
  have hartm_supp : ∀ p, quadForm c0 p ≠ 0 → a_rtm p = 0 := fun p hp => by
    have hp0 : p ≠ 0 := fun h => hp (h ▸ quadForm_zero c0)
    simp [a_rtm, hp0, hp]
  have hrtc_eq : rtc = matSub ρc (matSmul ((1 / d : ℝ) : ℂ) Δm) := by
    rw [hρc_exp, ← pauliExpand_smul, ← pauliExpand_sub]
    dsimp only [rtc]; congr 1; ext p
    by_cases hp0 : p = 0
    · subst hp0; simp [a_rtm, quadForm_zero, hce0, δm]
    · by_cases hpQ : quadForm c0 p = 0
      · simp [a_rtm, hp0, hpQ, δm]; ring
      · simp [a_rtm, hp0, hpQ, δm]
  have hD2m_eq : ∑ p : PauliIdx n, (δm p) ^ 2 = D2m := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : PauliIdx n => p ≠ 0 ∧ quadForm c0 p = 0)]
    have h0 : ∑ p ∈ Finset.univ.filter (fun p : PauliIdx n => ¬(p ≠ 0 ∧ quadForm c0 p = 0)), (δm p) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun p hp => by simp [δm, (Finset.mem_filter.mp hp).2]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp0, hpQ⟩ := (Finset.mem_filter.mp hp).2
    simp only [δm, σ, hp0, hpQ, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    by_cases hcp : 0 ≤ c p
    · simp [hcp, abs_of_nonneg hcp]
    · push Not at hcp; simp [not_le.mpr hcp, abs_of_neg hcp]; ring
  have hD2m_nn : 0 ≤ D2m := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΔm_frob : frobSq Δm = d * D2m := by rw [frobSq_pauliExpand, hD2m_eq]
  have hym_eq : Real.sqrt (frobSq Δm) = ym := by rw [hΔm_frob]
  -- `frobSq rtc = 1 / 2`!
  have hrtc_frob : frobSq rtc = 1 / 2 := by
    rw [frobSq_pauliExpand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))]
    have h0 : (a_rtm 0) ^ 2 = 1 / d ^ 2 := by simp [a_rtm]
    have hrest : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), (a_rtm p) ^ 2 =
        (Qm.card : ℝ) * (1 / (d ^ 2 * (d + 1))) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase 0) (fun p => quadForm c0 p = 0)]
      have hzero : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => ¬quadForm c0 p = 0),
          (a_rtm p) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun p hp => by
          have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).1
          simp [a_rtm, hp0, (Finset.mem_filter.mp hp).2]
      rw [hzero, add_zero]
      have hflt : (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => quadForm c0 p = 0) = Qm := by
        ext p; simp [Qm, and_comm]
      rw [hflt]
      have hterm : ∀ p ∈ Qm, (a_rtm p) ^ 2 = 1 / (d ^ 2 * (d + 1)) := fun p hp => by
        obtain ⟨hp0, hpQ⟩ := (Finset.mem_filter.mp hp).2
        simp only [a_rtm, hp0, hpQ, ↓reduceIte, mul_pow, div_pow, hσ_sq p hp, mul_one, hr2]
        field_simp [hd_ne, hd1_ne]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    rw [h0, hrest, hcardQm]; field_simp [hd_ne, hd1_ne]; ring
  -- Explicit squaring `rtc²`:
  have hrtc2 : matMul rtc rtc = pauliExpand (fun q =>
      if q = 0 then 1 / (2 * d)
      else if quadForm c0 q = 0 then (2 / d ^ 2) * (r * σ q + r ^ 2 * (Tm q : ℝ))
      else 0) := by
    rw [matMul_pauliExpand_self]
    congr 1; ext q
    by_cases hq0 : q = 0
    · subst hq0
      simp only [↓reduceIte]
      have hsq_eq : ∑ p : PauliIdx n, (pauliPhase 0 p).re * a_rtm p * a_rtm (0 + p) =
          ∑ p : PauliIdx n, (a_rtm p) ^ 2 :=
        Finset.sum_congr rfl fun p _ => by rw [pauliPhase_zero_left, Complex.one_re, zero_add]; ring
      rw [hsq_eq]
      have hf := hrtc_frob; rw [frobSq_pauliExpand] at hf
      have : d * ∑ p : PauliIdx n, (a_rtm p) ^ 2 = 1 / 2 := hf
      field_simp [hd_ne]; linarith
    · simp only [hq0, ↓reduceIte]
      by_cases hqQ : quadForm c0 q = 0
      · simp only [hqQ, ↓reduceIte]
        have hqM : q ∈ Qm := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0, hqQ⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n)),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hq0, Finset.mem_univ q⟩)]
        have ht0 : (pauliPhase q 0).re * a_rtm 0 * a_rtm (q + 0) = (r / d ^ 2) * σ q := by
          rw [pauliPhase_zero_right, Complex.one_re, add_zero]
          simp only [a_rtm, ↓reduceIte, hq0, hqQ]; ring
        have htq : (pauliPhase q q).re * a_rtm q * a_rtm (q + q) = (r / d ^ 2) * σ q := by
          rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self]
          simp only [a_rtm, ↓reduceIte, hq0, hqQ]; ring
        have hrest : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).erase q,
            (pauliPhase q p).re * a_rtm p * a_rtm (q + p) =
            (r ^ 2 / d ^ 2) * (2 * (Tm q : ℝ)) := by
          rw [← (hTm q hqM).2, Finset.mul_sum]
          rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ.erase 0).erase q) (fun p => quadForm c0 p = 0)]
          have hzero : ∑ p ∈ ((Finset.univ.erase (0 : PauliIdx n)).erase q).filter (fun p => ¬quadForm c0 p = 0),
              (pauliPhase q p).re * a_rtm p * a_rtm (q + p) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).2).1
            simp [a_rtm, hp0, (Finset.mem_filter.mp hp).2]
          rw [hzero, add_zero]
          have hflt : ((Finset.univ.erase (0 : PauliIdx n)).erase q).filter (fun p => quadForm c0 p = 0) =
              Qm.erase q := by
            ext p; simp only [Qm, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]; tauto
          rw [hflt]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
          obtain ⟨hp0, hpQ⟩ := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
          have hqp0 : q + p ≠ 0 := fun hc => hpq (by
            have := congr_arg (q + ·) hc; simpa [pauliIdx_add_cancel_left] using this)
          simp only [a_rtm, hp0, hpQ, hqp0, ↓reduceIte]
          by_cases hqpQ : quadForm c0 (q + p) = 0
          · simp [hqpQ]; ring
          · simp [hqpQ]
        rw [ht0, htq, hrest]; ring
      · -- If `Q_c(q) ≠ 0`, every term `(pauliPhase q p).re * a_rtm p * a_rtm (q + p) = 0`!
        simp only [hqQ, ↓reduceIte]
        refine Finset.sum_eq_zero fun p _ => ?_
        by_cases hs : symp q p = 0
        · by_cases hpQ : quadForm c0 p = 0
          · have hqpQ : quadForm c0 (q + p) ≠ 0 := by rw [quadForm_add, hpQ, hs, add_zero, add_zero]; exact hqQ
            rw [hartm_supp (q + p) hqpQ, mul_zero]
          · rw [hartm_supp p hpQ, mul_zero, zero_mul]
        · have hs1 : symp q p = 1 := (zmod2_cases (symp q p)).resolve_left hs
          rw [(pauliPhase_re_cases q p).2 hs1]; simp
  refine ⟨Tm, fun q hq => (hTm q hq).1, ?_, ?_⟩
  · -- Goal 1: `L²` Kramers bound with `(d/2) ym + ym² / √2`!
    let Em := matSmul ((d ^ 2 : ℝ) : ℂ) (matSub (matMul rtc rtc) (matSmul ((1 / 2 : ℝ) : ℂ) rtc))
    have hEm_exp : Em = pauliExpand (fun q =>
        if q ≠ 0 ∧ quadForm c0 q = 0 then (2 / (d + 1)) * ((Tm q : ℝ) - μm * σ q) else 0) := by
      simp only [Em]; rw [hrtc2, ← pauliExpand_smul, ← pauliExpand_sub, ← pauliExpand_smul]
      congr 1; ext q
      by_cases hq0 : q = 0
      · subst hq0; simp only [a_rtm, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
        field_simp [hd_ne]; ring
      · by_cases hqQ : quadForm c0 q = 0
        · simp only [hq0, hqQ, ne_eq, not_false_eq_true, and_self, ↓reduceIte, a_rtm, μm]
          have hr_eq : d ^ 2 * (2 / d ^ 2 * (r * σ q + r ^ 2 * (Tm q : ℝ)) - 1 / 2 * (r / d * σ q)) =
              2 * r ^ 2 * (Tm q : ℝ) - (d / 2 - 2) * r * σ q := by field_simp [hd_ne]; ring
          rw [hr_eq, hr2]
          have hr_alt : r = Real.sqrt (d + 1) / (d + 1) := by
            simp only [r]; field_simp [hs_ne, hd1_ne]; rw [Real.sq_sqrt (le_of_lt hd1_pos)]
          rw [hr_alt]; ring
        · simp [hq0, hqQ, a_rtm]
    have hEm_frob : frobSq Em = (4 * d / (d + 1) ^ 2) * ∑ q ∈ Qm, (σ q * (Tm q : ℝ) - μm) ^ 2 := by
      rw [hEm_exp, frobSq_pauliExpand,
          ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun q : PauliIdx n => q ≠ 0 ∧ quadForm c0 q = 0)]
      have h0 : ∑ q ∈ Finset.univ.filter (fun q : PauliIdx n => ¬(q ≠ 0 ∧ quadForm c0 q = 0)),
          (if q ≠ 0 ∧ quadForm c0 q = 0 then 2 / (d + 1) * ((Tm q : ℝ) - μm * σ q) else 0) ^ 2 = 0 :=
        Finset.sum_eq_zero fun q hq => by simp [(Finset.mem_filter.mp hq).2]
      rw [h0, add_zero]
      have hterm : ∀ q ∈ Qm,
          (if q ≠ 0 ∧ quadForm c0 q = 0 then 2 / (d + 1) * ((Tm q : ℝ) - μm * σ q) else 0) ^ 2 =
          (4 / (d + 1) ^ 2) * (σ q * (Tm q : ℝ) - μm) ^ 2 := fun q hq => by
        obtain ⟨hq0, hqQ⟩ := (Finset.mem_filter.mp hq).2
        simp only [hq0, hqQ, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        have hsq : ((Tm q : ℝ) - μm * σ q) ^ 2 = (σ q * (Tm q : ℝ) - μm) ^ 2 := by
          calc ((Tm q : ℝ) - μm * σ q) ^ 2 = (σ q) ^ 2 * ((Tm q : ℝ) - μm * σ q) ^ 2 := by
                rw [hσ_sq q hq, one_mul]
            _ = (σ q * (Tm q : ℝ) - μm * (σ q) ^ 2) ^ 2 := by ring
            _ = (σ q * (Tm q : ℝ) - μm) ^ 2 := by rw [hσ_sq q hq, mul_one]
        rw [mul_pow, div_pow, hsq]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]; ring
    -- Exact identity `Em = (d/2) * (Δm - P Δm - Δm P) + Δm²`!
    have hEm_rhs : Em = matAdd
        (matSmul ((d / 2 : ℝ) : ℂ) (matSub Δm (matAdd (matMul P Δm) (matMul Δm P))))
        (matMul Δm Δm) := by
      simp only [Em]; rw [hrtc_eq]
      ext x y
      simp only [ρc, matMul_sub_left, matMul_sub_right, matMul_smul_left, matMul_smul_right,
        hP_idem, matSub, matAdd, matSmul]
      have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd_ne
      push_cast; field_simp [hdC]; ring
    have hEm_ub : Real.sqrt (frobSq Em) ≤ (d / 2) * ym + ym ^ 2 / Real.sqrt 2 := by
      rw [hEm_rhs]
      have htri := sqrt_frobSq_add_le
        (matSmul ((d / 2 : ℝ) : ℂ) (matSub Δm (matAdd (matMul P Δm) (matMul Δm P)))) (matMul Δm Δm)
      have h1 : Real.sqrt (frobSq (matSmul ((d / 2 : ℝ) : ℂ)
          (matSub Δm (matAdd (matMul P Δm) (matMul Δm P))))) ≤ (d / 2) * ym := by
        rw [frobSq_smul, Complex.normSq_ofReal, ← sq, Real.sqrt_mul (sq_nonneg (d / 2)),
            Real.sqrt_sq (by linarith : (0 : ℝ) ≤ d / 2), ← hym_eq]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (frobSq_proj_cancel hP_herm hP_idem (pauliExpand_herm δm)))
          (by linarith)
      have h2 : Real.sqrt (frobSq (matMul Δm Δm)) ≤ ym ^ 2 / Real.sqrt 2 := by
        have hk := frobSq_sq_kramers_le hc0 hδm_supp
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← hym_eq,
            Real.sq_sqrt (frobSq_nonneg Δm)]
        linarith
      linarith
    have hEm_sq : frobSq Em ≤ ((d / 2) * ym + ym ^ 2 / Real.sqrt 2) ^ 2 :=
      (Real.sqrt_le_iff.mp hEm_ub).2
    rw [hEm_frob] at hEm_sq
    have hmul := mul_le_mul_of_nonneg_left hEm_sq (le_of_lt (show 0 < (d + 1) ^ 2 / (4 * d) by positivity))
    have hcancel : (d + 1) ^ 2 / (4 * d) * (4 * d / (d + 1) ^ 2 *
        ∑ q ∈ Qm, (σ q * (Tm q : ℝ) - μm) ^ 2) = ∑ q ∈ Qm, (σ q * (Tm q : ℝ) - μm) ^ 2 := by
      field_simp [hd_ne, hd1_ne]
    linarith
  · -- Goal 2: `∑_{q ∈ Qm} σ q * Tm q ≤ (d/2 - 1)(d + 1) μm` from `Tr(rtc³) ≤ 1 / 4`!
    have htr3 := matTr_cube_kramers_le hc0 hartm_supp hrtc_frob
    rw [hrtc2, matTr_pauliExpand_mul] at htr3
    have hre : ((2 : ℂ) ^ n * ∑ p : PauliIdx n,
        ((a_rtm p * (if p = 0 then 1 / (2 * d)
          else if quadForm c0 p = 0 then 2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ)) else 0) : ℝ) : ℂ)).re =
        d * ∑ p : PauliIdx n, a_rtm p * (if p = 0 then 1 / (2 * d)
          else if quadForm c0 p = 0 then 2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ)) else 0) := by
      have h2c : (2 : ℂ) ^ n = (d : ℂ) := by simp [d]
      rw [h2c, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx n))] at htr3
    have h0 : a_rtm 0 * (if (0 : PauliIdx n) = 0 then 1 / (2 * d)
        else if quadForm c0 0 = 0 then 2 / d ^ 2 * (r * σ 0 + r ^ 2 * (Tm 0 : ℝ)) else 0) =
        1 / (2 * d ^ 2) := by simp [a_rtm]; ring
    have hrest : ∑ p ∈ Finset.univ.erase (0 : PauliIdx n), a_rtm p * (if p = 0 then 1 / (2 * d)
        else if quadForm c0 p = 0 then 2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ)) else 0) =
        (Qm.card : ℝ) * (2 * r ^ 2 / d ^ 3) + (2 * r ^ 3 / d ^ 3) * ∑ p ∈ Qm, σ p * (Tm p : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase 0) (fun p => quadForm c0 p = 0)]
      have hzero : ∑ p ∈ (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => ¬quadForm c0 p = 0),
          a_rtm p * (if p = 0 then 1 / (2 * d)
            else if quadForm c0 p = 0 then 2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ)) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => by
          have hp0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).1
          simp [a_rtm, hp0, (Finset.mem_filter.mp hp).2]
      rw [hzero, add_zero]
      have hflt : (Finset.univ.erase (0 : PauliIdx n)).filter (fun p => quadForm c0 p = 0) = Qm := by
        ext p; simp [Qm, and_comm]
      rw [hflt]
      have hterm : ∀ p ∈ Qm, a_rtm p * (if p = 0 then 1 / (2 * d)
          else if quadForm c0 p = 0 then 2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ)) else 0) =
          2 * r ^ 2 / d ^ 3 + (2 * r ^ 3 / d ^ 3) * (σ p * (Tm p : ℝ)) := fun p hp => by
        obtain ⟨hp0, hpQ⟩ := (Finset.mem_filter.mp hp).2
        simp only [a_rtm, hp0, hpQ, ↓reduceIte]
        have : (r / d * σ p) * (2 / d ^ 2 * (r * σ p + r ^ 2 * (Tm p : ℝ))) =
            (2 * r ^ 2 / d ^ 3) * (σ p) ^ 2 + (2 * r ^ 3 / d ^ 3) * (σ p * (Tm p : ℝ)) := by ring
        rw [this, hσ_sq p hp, mul_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
    rw [h0, hrest, hcardQm] at htr3
    have hr3 : r ^ 3 = 1 / ((d + 1) * Real.sqrt (d + 1)) := by
      calc r ^ 3 = r ^ 2 * r := by ring
        _ = (1 / (d + 1)) * (1 / Real.sqrt (d + 1)) := by rw [hr2]
        _ = 1 / ((d + 1) * Real.sqrt (d + 1)) := by rw [one_div_mul_one_div]
    rw [hr2, hr3] at htr3
    -- Clear denominators cleanly!
    have hmul := mul_le_mul_of_nonneg_left htr3
      (le_of_lt (show 0 < d ^ 2 * (d + 1) * Real.sqrt (d + 1) / 2 by positivity))
    have hlhs : d ^ 2 * (d + 1) * Real.sqrt (d + 1) / 2 *
        (d * (1 / (2 * d ^ 2) + ((d / 2 - 1) * (d + 1) * (2 * (1 / (d + 1)) / d ^ 3) +
          2 * (1 / ((d + 1) * Real.sqrt (d + 1))) / d ^ 3 * ∑ p ∈ Qm, σ p * (Tm p : ℝ)))) =
        (d * (d + 1) * Real.sqrt (d + 1) / 4 + (d / 2 - 1) * (d + 1) * Real.sqrt (d + 1)) +
          ∑ p ∈ Qm, σ p * (Tm p : ℝ) := by
      field_simp [hd_ne, hd1_ne, hs_ne]; ring
    have hrhs : d ^ 2 * (d + 1) * Real.sqrt (d + 1) / 2 * (1 / 4) -
        (d * (d + 1) * Real.sqrt (d + 1) / 4 + (d / 2 - 1) * (d + 1) * Real.sqrt (d + 1)) =
        (d / 2 - 1) * (d + 1) * μm := by
      simp only [μm]; ring
    linarith

/-- **Theorem 6 (Unconditional Sharp 4-Qubit Lower Bound via Kramers Elliptic-Quadric Stability)**:
    For EVERY 4-qubit unit pure state `|ψ⟩ ∈ (ℂ²)^⊗4`,
      `pauliMoment4 4 ψ ≥ 32 / 17 + 33 / 10000` (`> 1.88565`, vs Welch `32 / 17 ≈ 1.882353`,
      a `57×` boost over naive `W(7, 2)` parity!). -/
theorem pauliMoment4_four_ge_kramers {ψ : QState 4} (hunit : IsUnitState ψ) :
    (32 / 17 : ℝ) + 33 / 10000 ≤ pauliMoment4 4 ψ := by
  set U := Finset.univ.erase (0 : PauliIdx 4)
  set c : PauliIdx 4 → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set r : ℝ := 1 / Real.sqrt ((2 : ℝ) ^ 4 + 1)
  set D2 : ℝ := ∑ p ∈ U, (|c p| - r) ^ 2
  have h17_sq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17_lo : (4.123105 : ℝ) < Real.sqrt 17 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h17_hi : Real.sqrt 17 < (4.12311 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2_lo : (1.414213 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- For EVERY elliptic center `c0` (`Q_0(c0) = 1`), prove `D2m c0 ≥ 0.02014`!
  have hquad_lb : ∀ c0 : PauliIdx 4, quadForm0 c0 = 1 →
      (0.02014 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0 p = 0),
        (|c p| - r) ^ 2 := by
    intro c0 hc0
    obtain ⟨Tm, hTodd, hL2, hsum_le⟩ := kramers_quadric_stability_fixed (n := 4) (by norm_num) hunit hc0
    set Qm := Finset.univ.filter fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0 p = 0
    set σ : PauliIdx 4 → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
    set D2m : ℝ := ∑ p ∈ Qm, (|c p| - r) ^ 2
    set ym : ℝ := Real.sqrt ((2 : ℝ) ^ 4 * D2m)
    have hD2m_nn : 0 ≤ D2m := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hym_nn : 0 ≤ ym := Real.sqrt_nonneg _
    have hym_sq : ym ^ 2 = 16 * D2m := by
      have : (2 : ℝ) ^ 4 * D2m = 16 * D2m := by norm_num
      rw [show ym = Real.sqrt (16 * D2m) by simp only [ym, this], Real.sq_sqrt (by linarith)]
    have hμm_eq : ((2 : ℝ) ^ 4 / 4 - 1) * Real.sqrt ((2 : ℝ) ^ 4 + 1) = 3 * Real.sqrt 17 := by norm_num
    have hcardQm : (Qm.card : ℝ) = 119 := by
      have hZ := card_elliptic_quadric (n := 4) (by norm_num) hc0
      have : (Qm.card : ℤ) = 119 := by norm_num at hZ; exact hZ
      exact_mod_cast this
    -- Apply `odd_secant_sq_ge` with `m = 11` (`μ_- = 3√17 ∈ (12, 13)`, so `m + 1 - μ_- = 12 - 3√17 < 0`)!
    have hsum_sec : 119 * ((3 * Real.sqrt 17 - 11) * (13 - 3 * Real.sqrt 17)) ≤
        ∑ q ∈ Qm, (σ q * (Tm q : ℝ) - 3 * Real.sqrt 17) ^ 2 := by
      have hpt : ∀ q ∈ Qm,
          (3 * Real.sqrt 17 - 11) * (13 - 3 * Real.sqrt 17) +
            2 * (12 - 3 * Real.sqrt 17) * (σ q * (Tm q : ℝ) - 3 * Real.sqrt 17) ≤
          (σ q * (Tm q : ℝ) - 3 * Real.sqrt 17) ^ 2 := by
        intro q hq
        have hq0 : q ≠ 0 := (Finset.mem_filter.mp hq).2.1
        have hσpm : σ q = 1 ∨ σ q = -1 := by simp only [σ, hq0, ↓reduceIte]; split_ifs <;> simp
        have hxodd : ∃ x : ℤ, x % 2 = 1 ∧ σ q * (Tm q : ℝ) = (x : ℝ) := by
          have hm := hTodd q hq
          rcases hσpm with h | h
          · exact ⟨Tm q, hm, by rw [h, one_mul]⟩
          · exact ⟨-Tm q, by omega, by rw [h]; push_cast; ring⟩
        obtain ⟨x, hx, hxeq⟩ := hxodd
        rw [hxeq]
        have hsec := odd_secant_sq_ge x 11 hx (by decide) (3 * Real.sqrt 17)
        push_cast at hsec; linarith
      have h1 := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardQm, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcardQm] at h1
      rw [hμm_eq] at hsum_le
      have hle119 : ∑ q ∈ Qm, σ q * (Tm q : ℝ) ≤ 119 * (3 * Real.sqrt 17) := by
        have hc119 : ((2 : ℝ) ^ 4 / 2 - 1) * ((2 : ℝ) ^ 4 + 1) = 119 := by norm_num
        rw [hc119] at hsum_le; exact hsum_le
      have hneg : 2 * (12 - 3 * Real.sqrt 17) < 0 := by linarith only [h17_lo]
      nlinarith only [h1, hle119, hneg]
    rw [hμm_eq] at hL2
    have hcomb : 119 * ((3 * Real.sqrt 17 - 11) * (13 - 3 * Real.sqrt 17)) ≤
        (289 / 64 : ℝ) * (8 * ym + ym ^ 2 / Real.sqrt 2) ^ 2 := by
      have ha : ((2 : ℝ) ^ 4 + 1) ^ 2 / (4 * (2 : ℝ) ^ 4) = 289 / 64 := by norm_num
      have hb : (2 : ℝ) ^ 4 / 2 = 8 := by norm_num
      rw [ha, hb] at hL2; exact le_trans hsum_sec hL2
    have hym_lb : (0.5678 : ℝ) ≤ ym := by
      by_contra hlt; push Not at hlt
      have hinv : ym ^ 2 / Real.sqrt 2 ≤ ym ^ 2 / 1.414213 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (le_of_lt h2_lo)
      have hym2 : ym ^ 2 < 0.5678 ^ 2 := by nlinarith only [hym_nn, hlt]
      have hdiv2 : ym ^ 2 / 1.414213 < 0.5678 ^ 2 / 1.414213 :=
        div_lt_div_of_pos_right hym2 (by norm_num)
      have hlin : 8 * ym + ym ^ 2 / Real.sqrt 2 < 8 * 0.5678 + 0.5678 ^ 2 / 1.414213 := by
        linarith only [hlt, hinv, hdiv2]
      have hnn : 0 ≤ 8 * ym + ym ^ 2 / Real.sqrt 2 := by positivity
      have hsq : (289 / 64 : ℝ) * (8 * ym + ym ^ 2 / Real.sqrt 2) ^ 2 <
          (289 / 64 : ℝ) * (8 * 0.5678 + 0.5678 ^ 2 / 1.414213) ^ 2 := by
        nlinarith only [hnn, hlin]
      have hsec : (3 * Real.sqrt 17 - 11) * (13 - 3 * Real.sqrt 17) = 72 * Real.sqrt 17 - 296 := by
        nlinarith only [h17_sq]
      have hnum : (289 / 64 : ℝ) * (8 * 0.5678 + 0.5678 ^ 2 / 1.414213) ^ 2 <
          119 * (72 * 4.123105 - 296) := by norm_num
      linarith only [hcomb, hsq, hsec, h17_lo, hnum]
    nlinarith only [hym_lb, hym_sq]
  -- Average over ALL 120 elliptic centers `c0` (each `p ≠ 0` lies in 56 elliptic quadrics)!
  let C_ell := Finset.univ.filter fun c0 : PauliIdx 4 => quadForm0 c0 = 1
  have hC_card : (C_ell.card : ℝ) = 120 := by
    have hZ := card_elliptic_centers (n := 4) (by norm_num)
    have : (C_ell.card : ℤ) = 120 := by norm_num at hZ; exact hZ
    exact_mod_cast this
  have havg_sum : ∑ c0 ∈ C_ell, ∑ p ∈ Finset.univ.filter (fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0 p = 0),
      (|c p| - r) ^ 2 = 56 * D2 := by
    have hrewrite : ∀ c0 : PauliIdx 4,
        ∑ p ∈ Finset.univ.filter (fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0 p = 0), (|c p| - r) ^ 2 =
        ∑ p ∈ U, if quadForm c0 p = 0 then (|c p| - r) ^ 2 else 0 := by
      intro c0
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [U, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]; tauto
    simp_rw [hrewrite]; rw [Finset.sum_comm]
    have hinner : ∀ p ∈ U, ∑ c0 ∈ C_ell, (if quadForm c0 p = 0 then (|c p| - r) ^ 2 else 0) =
        56 * (|c p| - r) ^ 2 := by
      intro p hp
      have hp0 : p ≠ 0 := (Finset.mem_erase.mp hp).1
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hflt : C_ell.filter (fun c0 => quadForm c0 p = 0) =
          Finset.univ.filter (fun c0 : PauliIdx 4 => quadForm0 c0 = 1 ∧ quadForm c0 p = 0) := by
        ext c0; simp [C_ell]
      rw [hflt]
      have hZ := card_elliptic_centers_containing (n := 4) (by norm_num) hp0
      have : ((Finset.univ.filter fun c0 : PauliIdx 4 => quadForm0 c0 = 1 ∧ quadForm c0 p = 0).card : ℤ) = 56 := by
        norm_num at hZ; exact hZ
      exact_mod_cast this
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hsum_lb : 120 * (0.02014 : ℝ) ≤ 56 * D2 := by
    have h1 := Finset.sum_le_sum (s := C_ell) fun c0 hc0 => hquad_lb c0 (Finset.mem_filter.mp hc0).2
    rw [Finset.sum_const, nsmul_eq_mul, hC_card, havg_sum] at h1; exact h1
  have hD2_lb : (0.04315 : ℝ) ≤ D2 := by linarith only [hsum_lb]
  -- Apply `eps_ge_concave_of_le_r2` at `D0 = 0.04315 ≤ 1 / 17`!
  have hconc := eps_ge_concave_of_le_r2 (n := 4) hunit (D2 := 0.04315) (by norm_num) hD2_lb (by norm_num)
  have h4eq : 2 * (2 : ℝ) ^ 4 / ((2 : ℝ) ^ 4 + 1) = 32 / 17 := by norm_num
  have hr_eq : 1 / Real.sqrt ((2 : ℝ) ^ 4 + 1) = 1 / Real.sqrt 17 := by norm_num
  rw [h4eq, hr_eq] at hconc
  have hsqrtD : (0.20772 : ℝ) ≤ Real.sqrt 0.04315 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr_lo : (0.24253 : ℝ) ≤ 1 / Real.sqrt 17 := by
    rw [le_div_iff₀ (by linarith only [h17_lo])]; linarith only [h17_hi]
  have hval : (33 / 10000 : ℝ) ≤ (2 * (1 / Real.sqrt 17) * Real.sqrt 0.04315 - 0.04315) ^ 2 := by
    have hprod : (0.24253 : ℝ) * 0.20772 ≤ (1 / Real.sqrt 17) * Real.sqrt 0.04315 :=
      mul_le_mul hr_lo hsqrtD (by norm_num) (by linarith only [hr_lo])
    have hlin : (0.05760 : ℝ) ≤ 2 * (1 / Real.sqrt 17) * Real.sqrt 0.04315 - 0.04315 := by
      linarith only [hprod]
    nlinarith only [hlin]
  linarith only [hconc, hval]

/-! ### Section 5: The Matrix-Free Contextuality-Degree-to-Magic Bridge Theorem -/

/-- **Theorem 7 (Matrix-Free Contextuality-Degree-to-Magic Bridge, ALL `n ≥ 2`)**:
    Suppose every sign assignment `σ : PauliIdx n → ℝ` (`σ 0 = 0`, `σ p ∈ {-1, 1}` for `p ≠ 0`)
    satisfies `signCubeSum n σ ≤ Smax`. If `y0 ≥ 0` satisfies
      `((d + 1) √(d + 1) / (2 d)) * ((3/2) d y0² + y0³ - (3 / (4 d)) y0⁴) ≤ (d² - 1) μ - Smax`
    and `y0 ≤ d` (so the quartic is strictly increasing on `[0, y0]`) and `y0² / d < 2 (d - 1)`,
    then for EVERY unit pure state `|ψ⟩ ∈ (ℂ²)^⊗n`,
      `pauliMoment4 n ψ ≥ 1 + (d - 1)³ / ((d - 1) √(d + 1) - (√(d + 1) / 2) * (y0² / d))²`. -/
theorem pauliMoment4_contextuality_bridge {n : ℕ} (hn : 2 ≤ n)
    {Smax y0 : ℝ}
    (hCD : ∀ σ : PauliIdx n → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum n σ ≤ Smax)
    (hy0_nn : 0 ≤ y0) (hy0_le_d : y0 ≤ (2 : ℝ) ^ n)
    (hgap : let d : ℝ := (2 : ℝ) ^ n
      ((d + 1) * Real.sqrt (d + 1) / (2 * d)) *
        ((3 / 2 : ℝ) * d * y0 ^ 2 + y0 ^ 3 - (3 / (4 * d)) * y0 ^ 4) ≤
      (d ^ 2 - 1) * ((d / 2 - 1) * Real.sqrt (d + 1)) - Smax)
    (hD2_lt : y0 ^ 2 / (2 : ℝ) ^ n < 2 * ((2 : ℝ) ^ n - 1))
    {ψ : QState n} (hunit : IsUnitState ψ) :
    let d : ℝ := (2 : ℝ) ^ n
    let L : ℝ := (d - 1) * Real.sqrt (d + 1) - (Real.sqrt (d + 1) / 2) * (y0 ^ 2 / d)
    1 + (d - 1) ^ 3 / L ^ 2 ≤ pauliMoment4 n ψ := by
  intro d L
  have hd_pos : 0 < d := by positivity
  obtain ⟨_, _, _, _, _, htr3_gap⟩ := full_space_stability_package hn hunit
  set U := Finset.univ.erase (0 : PauliIdx n)
  set c : PauliIdx n → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  set σ : PauliIdx n → ℝ := fun p => if p = 0 then 0 else if 0 ≤ c p then 1 else -1
  set r : ℝ := 1 / Real.sqrt (d + 1)
  set D2 : ℝ := ∑ p ∈ U, (|c p| - r) ^ 2
  set y : ℝ := Real.sqrt (d * D2)
  have hD2_nn : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy_nn : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = d * D2 := Real.sq_sqrt (by positivity)
  have hS_le : signCubeSum n σ ≤ Smax :=
    hCD σ (by simp [σ]) (fun p hp => by simp only [σ, hp, ↓reduceIte]; split_ifs <;> simp)
  -- Deduce `y0 ≤ y` from monotonicity of `f(t) = (3/2) d t² + t³ - (3/(4d)) t⁴` on `[0, d]`!
  have hy_ge : y0 ≤ y := by
    by_contra hlt; push Not at hlt
    have hpoly_lt : (3 / 2 : ℝ) * d * y ^ 2 + y ^ 3 - (3 / (4 * d)) * y ^ 4 <
        (3 / 2 : ℝ) * d * y0 ^ 2 + y0 ^ 3 - (3 / (4 * d)) * y0 ^ 4 := by
      have hfac : ((3 / 2 : ℝ) * d * y0 ^ 2 + y0 ^ 3 - (3 / (4 * d)) * y0 ^ 4) -
          ((3 / 2 : ℝ) * d * y ^ 2 + y ^ 3 - (3 / (4 * d)) * y ^ 4) =
          (y0 - y) * ((3 / (4 * d)) * (y0 + y) * (2 * d ^ 2 - (y0 ^ 2 + y ^ 2)) +
            (y0 ^ 2 + y0 * y + y ^ 2)) := by
        field_simp [ne_of_gt hd_pos]; ring
      have hpos1 : 0 < y0 - y := by linarith
      have hpos2 : 0 ≤ 2 * d ^ 2 - (y0 ^ 2 + y ^ 2) := by nlinarith
      have hpos3 : 0 < y0 ^ 2 + y0 * y + y ^ 2 := by nlinarith
      have hpos4 : 0 ≤ (3 / (4 * d)) * (y0 + y) * (2 * d ^ 2 - (y0 ^ 2 + y ^ 2)) := by positivity
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hpoly_lt
      (show 0 < (d + 1) * Real.sqrt (d + 1) / (2 * d) by positivity)
    linarith
  have hD2_lb : y0 ^ 2 / d ≤ D2 := by
    rw [div_le_iff₀ hd_pos, mul_comm D2 d, ← hy_sq]; nlinarith
  exact pauliMoment4_ge_holder_of_D2 hunit hD2_lb hD2_lt

/-- **4-Qubit Contextuality Bridge Specialization (`pauliMoment4_four_of_contextuality_1575`)**:
    Under the 4-qubit Pauli contextuality degree bound `CD(W(7, 2)) ≥ 1575`
    (equivalently `signCubeSum 4 σ ≤ 6615` for all `σ ∈ {±1}^{𝔽₂⁸ \ {0}}`),
    EVERY 4-qubit unit pure state satisfies `pauliMoment4 4 ψ ≥ 193 / 100 = 1.930`
    (`+0.0476` above the Welch bound `32 / 17 ≈ 1.882353`, within `0.0075` of `31 / 16`)! -/
theorem pauliMoment4_four_of_contextuality_1575
    (hCD : ∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615)
    {ψ : QState 4} (hunit : IsUnitState ψ) :
    (193 / 100 : ℝ) ≤ pauliMoment4 4 ψ := by
  have h17_sq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17_lo : (4.12310 : ℝ) < Real.sqrt 17 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h17_hi : Real.sqrt 17 < (4.12311 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hbr := pauliMoment4_contextuality_bridge (n := 4) (by norm_num) (Smax := 6615) (y0 := 3.55)
    hCD (by norm_num) (by norm_num) ?_ (by norm_num) hunit
  · -- Verify `193 / 100 ≤ 1 + 15^3 / L^2` where `L = 15 √17 - (√17 / 2) * (3.55^2 / 16)`!
    dsimp only at hbr
    have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
    have h17 : (2 : ℝ) ^ 4 + 1 = 17 := by norm_num
    have hL_eq : ((2 : ℝ) ^ 4 - 1) * Real.sqrt ((2 : ℝ) ^ 4 + 1) -
        Real.sqrt ((2 : ℝ) ^ 4 + 1) / 2 * (3.55 ^ 2 / (2 : ℝ) ^ 4) =
        (15 - 3.55 ^ 2 / 32) * Real.sqrt 17 := by rw [h17, h16]; ring
    have h15 : ((2 : ℝ) ^ 4 - 1) ^ 3 = 3375 := by norm_num
    rw [hL_eq, h15] at hbr
    have hL_pos : 0 < (15 - 3.55 ^ 2 / 32) * Real.sqrt 17 :=
      mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
    have hrat : (93 / 100 : ℝ) ≤ 3375 / ((15 - 3.55 ^ 2 / 32) * Real.sqrt 17) ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hL_pos), mul_pow, h17_sq]; norm_num
    linarith
  · -- Verify the `hgap` inequality at `y0 = 3.55`, `d = 16`, `Smax = 6615`!
    dsimp only
    have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
    have h17 : (2 : ℝ) ^ 4 + 1 = 17 := by norm_num
    have hlhs_eq : (((2 : ℝ) ^ 4 + 1) * Real.sqrt ((2 : ℝ) ^ 4 + 1) / (2 * (2 : ℝ) ^ 4)) *
        ((3 / 2 : ℝ) * (2 : ℝ) ^ 4 * 3.55 ^ 2 + 3.55 ^ 3 - (3 / (4 * (2 : ℝ) ^ 4)) * 3.55 ^ 4) =
        (17 / 32) * (24 * 3.55 ^ 2 + 3.55 ^ 3 - (3 / 64) * 3.55 ^ 4) * Real.sqrt 17 := by
      rw [h17, h16]; ring
    have hrhs_eq : (((2 : ℝ) ^ 4) ^ 2 - 1) * (((2 : ℝ) ^ 4 / 2 - 1) * Real.sqrt ((2 : ℝ) ^ 4 + 1)) - 6615 =
        1785 * Real.sqrt 17 - 6615 := by rw [h17, h16]; ring
    rw [hlhs_eq, hrhs_eq]
    nlinarith

end MultiQubitMUB
