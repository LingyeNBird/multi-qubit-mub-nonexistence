import MultiQubitMUB.Basic
import MultiQubitMUB.Alltop

/-!
# Theorem 2: Unrestricted Non-Existence of Multi-Qubit Pauli-Covariant MUB Fiducials (`n ≥ 3`)

We prove in complete matrix-free generality on `QState n := F2 n → ℂ`:
1. **Direct Odd-`n` Theorem (`no_pauli_two_valued_odd`)**: For every odd `n = 2k + 1 ≥ 3`,
   NO unit vector `|ψ⟩ ∈ (ℂ²)^⊗n` even satisfies `|⟨ψ|P|ψ⟩|² ∈ {0, 2⁻ⁿ}` for all `P ≠ I`
   (no basis-partition hypothesis needed; proved directly from `ρ² = ρ` and irrationality of `√2`).
2. **Main Theorem 2 (`no_pauli_mub_fiducial`)**: For EVERY `n ≥ 3` (both odd and even),
   NO unit vector `|ψ⟩ ∈ (ℂ²)^⊗n` generates `2ⁿ` pairwise mutually unbiased orthonormal bases
   under the `n`-qubit Pauli group `𝒫ₙ`.
   - Completely resolves Conjecture 1 of Damski, Bistroń, Ponterio, Czartowski, Życzkowski
     (`arXiv:2603.15550`) in full unrestricted generality (`damski_conjecture_1`), removing both
     the `ω₈` phase ansatz and equimodularity.
   - Rules out the conjectured product WH-MUB maximal magic states (`arXiv:2502.17550` / Problem E28,
     originally conjectured for `n ≠ 1, 3`) for all `n ≥ 4` (with Theorem 2 holding for all `n ≥ 3`).
3. **Sharpness (`exists_pauli_mub_fiducial_two`)**: For `n = 2`, `|ψ₂⟩ = (1/2)(1, 1, 1, i)` IS
   a 2-qubit Pauli-covariant MUB fiducial generating 4 pairwise MUBs.
-/

namespace MultiQubitMUB

open scoped Classical

/-- `n`-qubit pure state vector `|ψ⟩ ∈ (ℂ²)^⊗n`, represented as `F2 n → ℂ`. -/
abbrev QState (n : ℕ) := F2 n → ℂ

/-- Hermitian inner product `⟨ψ | φ⟩ = ∑_x conj(ψ x) * φ x`. -/
def innerProd {n : ℕ} (ψ φ : QState n) : ℂ :=
  ∑ x : F2 n, star (ψ x) * φ x

/-- Unit-norm state condition `⟨ψ | ψ⟩ = 1`. -/
def IsUnitState {n : ℕ} (ψ : QState n) : Prop :=
  innerProd ψ ψ = 1

lemma innerProd_conj_symm {n : ℕ} (ψ φ : QState n) :
    innerProd φ ψ = star (innerProd ψ φ) := by
  simp only [innerProd, star_sum, star_mul, star_star]

lemma innerProd_add_right {n : ℕ} (ψ φ₁ φ₂ : QState n) :
    innerProd ψ (φ₁ + φ₂) = innerProd ψ φ₁ + innerProd ψ φ₂ := by
  simp only [innerProd, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma innerProd_sub_right {n : ℕ} (ψ φ₁ φ₂ : QState n) :
    innerProd ψ (φ₁ - φ₂) = innerProd ψ φ₁ - innerProd ψ φ₂ := by
  simp only [innerProd, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma innerProd_smul_right {n : ℕ} (ψ φ : QState n) (c : ℂ) :
    innerProd ψ (c • φ) = c * innerProd ψ φ := by
  simp only [innerProd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma innerProd_smul_left {n : ℕ} (ψ φ : QState n) (c : ℂ) :
    innerProd (c • ψ) φ = star c * innerProd ψ φ := by
  simp only [innerProd, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma innerProd_sum_right {n : ℕ} {ι : Type*} (s : Finset ι) (ψ : QState n) (f : ι → QState n) :
    innerProd ψ (∑ i ∈ s, f i) = ∑ i ∈ s, innerProd ψ (f i) := by
  simp only [innerProd, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma innerProd_sum_left {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QState n) (φ : QState n) :
    innerProd (∑ i ∈ s, f i) φ = ∑ i ∈ s, innerProd (f i) φ := by
  simp only [innerProd, Finset.sum_apply, star_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma innerProd_self_eq_sum_normSq {n : ℕ} (ψ : QState n) :
    innerProd ψ ψ = ((∑ x : F2 n, Complex.normSq (ψ x) : ℝ) : ℂ) := by
  simp only [innerProd, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj]

lemma innerProd_self_re {n : ℕ} (ψ : QState n) :
    (innerProd ψ ψ).re = ∑ x : F2 n, Complex.normSq (ψ x) := by
  rw [innerProd_self_eq_sum_normSq, Complex.ofReal_re]

lemma innerProd_self_re_nonneg {n : ℕ} (ψ : QState n) :
    0 ≤ (innerProd ψ ψ).re := by
  rw [innerProd_self_re]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

lemma innerProd_self_eq_zero_iff {n : ℕ} (ψ : QState n) :
    innerProd ψ ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    have hre : ∑ x : F2 n, Complex.normSq (ψ x) = 0 := by
      rw [← innerProd_self_re, h, Complex.zero_re]
    ext x
    have hx : Complex.normSq (ψ x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ => Complex.normSq_nonneg (ψ y)).mp hre x
        (Finset.mem_univ x)
    exact Complex.normSq_eq_zero.mp hx
  · intro h; rw [h]; simp [innerProd]

/-! ### Phase Space `𝔽₂²ⁿ` and Hermitian Involutive Pauli Operators -/

/-- Phase-space index `(a, b) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ` labeling the Hermitian Pauli `P_{(a,b)} = i^(a·b) Z^b X^a`. -/
abbrev PauliIdx (n : ℕ) := F2 n × F2 n

lemma pauliIdx_add_self {n : ℕ} (p : PauliIdx n) : p + p = 0 :=
  Prod.ext (f2_add_self p.1) (f2_add_self p.2)

lemma pauliIdx_add_cancel_left {n : ℕ} (p q : PauliIdx n) : p + (p + q) = q := by
  rw [← add_assoc, pauliIdx_add_self, zero_add]

lemma pauliIdx_add_cancel_right {n : ℕ} (p q : PauliIdx n) : (p + q) + q = p := by
  rw [add_assoc, pauliIdx_add_self, add_zero]

/-- Symplectic form `ω((a,b), (c,d)) = a·d + b·c` on `𝔽₂ⁿ × 𝔽₂ⁿ`. -/
def symp {n : ℕ} (p q : PauliIdx n) : ZMod 2 :=
  dot p.1 q.2 + dot p.2 q.1

lemma symp_self {n : ℕ} (p : PauliIdx n) : symp p p = 0 := by
  simp only [symp, dot_comm p.2 p.1]
  rcases zmod2_cases (dot p.1 p.2) with h | h <;> rw [h] <;> decide

lemma symp_comm {n : ℕ} (p q : PauliIdx n) : symp p q = symp q p := by
  simp only [symp, dot_comm p.1 q.2, dot_comm p.2 q.1, add_comm]

lemma symp_add_left {n : ℕ} (p₁ p₂ q : PauliIdx n) : symp (p₁ + p₂) q = symp p₁ q + symp p₂ q := by
  simp only [symp, Prod.fst_add, Prod.snd_add, dot_add_left]
  ring

lemma symp_add_right {n : ℕ} (p q₁ q₂ : PauliIdx n) : symp p (q₁ + q₂) = symp p q₁ + symp p q₂ := by
  rw [symp_comm, symp_add_left, symp_comm q₁, symp_comm q₂]

lemma symp_zero_left {n : ℕ} (q : PauliIdx n) : symp 0 q = 0 := by
  simp [symp, dot_zero_left]

lemma symp_zero_right {n : ℕ} (p : PauliIdx n) : symp p 0 = 0 := by
  simp [symp, dot_zero_right]

lemma symp_smul_left {n : ℕ} (c : ZMod 2) (p q : PauliIdx n) : symp (c • p) q = c * symp p q := by
  rcases zmod2_cases c with rfl | rfl <;> simp [symp_zero_left]

lemma symp_smul_right {n : ℕ} (c : ZMod 2) (p q : PauliIdx n) : symp p (c • q) = c * symp p q := by
  rcases zmod2_cases c with rfl | rfl <;> simp [symp_zero_right]

lemma symp_sum_left {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → PauliIdx n) (q : PauliIdx n) :
    symp (∑ i ∈ s, f i) q = ∑ i ∈ s, symp (f i) q := by
  induction s using Finset.cons_induction with
  | empty => simp [symp_zero_left]
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, symp_add_left, ih]

lemma symp_sum_right {n : ℕ} {ι : Type*} (p : PauliIdx n) (s : Finset ι) (f : ι → PauliIdx n) :
    symp p (∑ i ∈ s, f i) = ∑ i ∈ s, symp p (f i) := by
  rw [symp_comm, symp_sum_left]
  refine Finset.sum_congr rfl fun i _ => symp_comm _ _

/-- Symplectic sign `(-1)^{ω(p, q)} ∈ {-1, 1}`. -/
def sympSign {n : ℕ} (p q : PauliIdx n) : ℤ :=
  if symp p q = 0 then 1 else -1

lemma sympSign_comm {n : ℕ} (p q : PauliIdx n) : sympSign p q = sympSign q p := by
  simp only [sympSign, symp_comm]

lemma sympSign_add_left {n : ℕ} (p₁ p₂ q : PauliIdx n) :
    sympSign (p₁ + p₂) q = sympSign p₁ q * sympSign p₂ q := by
  simp only [sympSign, symp_add_left]
  rcases zmod2_cases (symp p₁ q) with h1 | h1 <;> rcases zmod2_cases (symp p₂ q) with h2 | h2
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]; decide

lemma sympSign_add_right {n : ℕ} (p q₁ q₂ : PauliIdx n) :
    sympSign p (q₁ + q₂) = sympSign p q₁ * sympSign p q₂ := by
  rw [sympSign_comm, sympSign_add_left, sympSign_comm q₁, sympSign_comm q₂]

/-- Phase factor `i^{a·b}` ensuring `P_{(a,b)} = i^{a·b} Z^b X^a` is Hermitian and involutive. -/
def pauliPh {n : ℕ} (p : PauliIdx n) : ℂ :=
  if dot p.1 p.2 = 0 then 1 else Complex.I

lemma pauliPh_normSq {n : ℕ} (p : PauliIdx n) : Complex.normSq (pauliPh p) = 1 := by
  simp only [pauliPh]; split_ifs <;> simp [Complex.normSq_I]

lemma pauliPh_mul_star {n : ℕ} (p : PauliIdx n) : star (pauliPh p) * pauliPh p = 1 := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj, pauliPh_normSq]; simp

lemma pauliPh_sq {n : ℕ} (p : PauliIdx n) : pauliPh p * pauliPh p = (chi p.2 p.1 : ℂ) := by
  simp only [pauliPh, chi, dot_comm p.2 p.1]
  split_ifs <;> simp

lemma pauliPh_mul_chi {n : ℕ} (p : PauliIdx n) :
    pauliPh p * (chi p.2 p.1 : ℂ) = star (pauliPh p) := by
  simp only [pauliPh, chi, dot_comm p.2 p.1]
  split_ifs <;> simp

/-- Action of the Hermitian involutive Pauli operator `P_{(a,b)}` on `ψ : QState n`. -/
def pauliApply {n : ℕ} (p : PauliIdx n) (ψ : QState n) : QState n :=
  fun x => pauliPh p * (chi p.2 x : ℂ) * ψ (x + p.1)

lemma pauliApply_zero {n : ℕ} (ψ : QState n) : pauliApply 0 ψ = ψ := by
  ext x; simp [pauliApply, pauliPh, dot_zero_left, chi_zero_left]

lemma pauliApply_add {n : ℕ} (p : PauliIdx n) (ψ φ : QState n) :
    pauliApply p (ψ + φ) = pauliApply p ψ + pauliApply p φ := by
  ext x; simp [pauliApply, mul_add]

lemma pauliApply_smul {n : ℕ} (p : PauliIdx n) (c : ℂ) (ψ : QState n) :
    pauliApply p (c • ψ) = c • pauliApply p ψ := by
  ext x; simp [pauliApply]; ring

/-- Every Pauli operator is an involution: `P_p² = I`. -/
lemma pauliApply_invol {n : ℕ} (p : PauliIdx n) (ψ : QState n) :
    pauliApply p (pauliApply p ψ) = ψ := by
  ext x
  simp only [pauliApply, f2_add_cancel_right, chi_add_right]
  have hsq : (chi p.2 x : ℂ) * (chi p.2 x : ℂ) = 1 := by
    rw [← Int.cast_mul, chi_mul_self, Int.cast_one]
  calc pauliPh p * (chi p.2 x : ℂ) * (pauliPh p * ((chi p.2 x * chi p.2 p.1 : ℤ) : ℂ) * ψ x)
      = (pauliPh p * pauliPh p) * (chi p.2 p.1 : ℂ) * ((chi p.2 x : ℂ) * (chi p.2 x : ℂ)) * ψ x := by
        push_cast; ring
    _ = (chi p.2 p.1 : ℂ) * (chi p.2 p.1 : ℂ) * 1 * ψ x := by rw [pauliPh_sq, hsq]
    _ = ψ x := by rw [← Int.cast_mul, chi_mul_self]; simp

/-- Every Pauli operator is Hermitian: `⟨φ | P_p ψ⟩ = ⟨P_p φ | ψ⟩`. -/
lemma innerProd_pauliApply_right {n : ℕ} (p : PauliIdx n) (φ ψ : QState n) :
    innerProd φ (pauliApply p ψ) = innerProd (pauliApply p φ) ψ := by
  simp only [innerProd, pauliApply]
  refine Fintype.sum_equiv (Equiv.addRight p.1) _ _ fun x => ?_
  change star (φ x) * (pauliPh p * (chi p.2 x : ℂ) * ψ (x + p.1)) =
    star (pauliPh p * (chi p.2 (x + p.1) : ℂ) * φ ((x + p.1) + p.1)) * ψ (x + p.1)
  rw [f2_add_cancel_right, star_mul, star_mul]
  have hchi_star : star (chi p.2 (x + p.1) : ℂ) = (chi p.2 x : ℂ) * (chi p.2 p.1 : ℂ) := by
    rw [chi_add_right]; push_cast; simp
  rw [hchi_star]
  have hph := pauliPh_mul_chi p
  have hchi2 : (chi p.2 p.1 : ℂ) * (chi p.2 p.1 : ℂ) = 1 := by
    rw [← Int.cast_mul, chi_mul_self, Int.cast_one]
  calc star (φ x) * (pauliPh p * (chi p.2 x : ℂ) * ψ (x + p.1))
      = star (φ x) * (pauliPh p * (chi p.2 p.1 : ℂ)) * (chi p.2 p.1 : ℂ) * (chi p.2 x : ℂ) * ψ (x + p.1) := by
        calc star (φ x) * (pauliPh p * (chi p.2 x : ℂ) * ψ (x + p.1))
            = star (φ x) * pauliPh p * ((chi p.2 p.1 : ℂ) * (chi p.2 p.1 : ℂ)) * (chi p.2 x : ℂ) * ψ (x + p.1) := by
              rw [hchi2]; ring
          _ = _ := by ring
    _ = star (φ x) * star (pauliPh p) * (chi p.2 p.1 : ℂ) * (chi p.2 x : ℂ) * ψ (x + p.1) := by rw [hph]
    _ = star (φ x) * ((chi p.2 x : ℂ) * (chi p.2 p.1 : ℂ) * star (pauliPh p)) * ψ (x + p.1) := by ring

/-- Every Pauli operator is unitary: `⟨P_p φ | P_p ψ⟩ = ⟨φ | ψ⟩`. -/
lemma innerProd_pauliApply_both {n : ℕ} (p : PauliIdx n) (φ ψ : QState n) :
    innerProd (pauliApply p φ) (pauliApply p ψ) = innerProd φ ψ := by
  rw [← innerProd_pauliApply_right, pauliApply_invol]

/-- Composition phase `pauliPhase p q ∈ {±1, ±i}` such that `P_p P_q = pauliPhase p q • P_{p+q}`. -/
def pauliPhase {n : ℕ} (p q : PauliIdx n) : ℂ :=
  pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * star (pauliPh (p + q))

lemma pauliPhase_normSq {n : ℕ} (p q : PauliIdx n) : Complex.normSq (pauliPhase p q) = 1 := by
  have hchi : Complex.normSq (chi q.2 p.1 : ℂ) = 1 := by
    rcases chi_eq_one_or_neg_one q.2 p.1 with h | h <;> simp [h]
  simp only [pauliPhase, map_mul, pauliPh_normSq, hchi, Complex.star_def, Complex.normSq_conj, mul_one]

lemma pauliPhase_ne_zero {n : ℕ} (p q : PauliIdx n) : pauliPhase p q ≠ 0 := by
  intro h
  have := pauliPhase_normSq p q
  rw [h, map_zero] at this
  norm_num at this

lemma pauliPhase_zero_left {n : ℕ} (q : PauliIdx n) : pauliPhase 0 q = 1 := by
  simp only [pauliPhase, zero_add, pauliPh, Prod.fst_zero, Prod.snd_zero, dot_zero_left,
    ↓reduceIte, one_mul, chi_zero_right, Int.cast_one, mul_one]
  rw [mul_comm]; exact pauliPh_mul_star q

lemma pauliPhase_zero_right {n : ℕ} (p : PauliIdx n) : pauliPhase p 0 = 1 := by
  simp only [pauliPhase, add_zero, pauliPh, Prod.fst_zero, Prod.snd_zero, dot_zero_right,
    ↓reduceIte, mul_one, chi_zero_left, Int.cast_one]
  rw [mul_comm]; exact pauliPh_mul_star p

lemma pauliPhase_self {n : ℕ} (p : PauliIdx n) : pauliPhase p p = 1 := by
  simp only [pauliPhase, pauliIdx_add_self]
  have h0 : pauliPh (0 : PauliIdx n) = 1 := by simp [pauliPh, dot_zero_left]
  rw [h0, star_one, mul_one, pauliPh_sq, ← Int.cast_mul, chi_mul_self, Int.cast_one]

lemma pauliApply_comp {n : ℕ} (p q : PauliIdx n) (ψ : QState n) :
    pauliApply p (pauliApply q ψ) = pauliPhase p q • pauliApply (p + q) ψ := by
  ext x
  simp only [pauliApply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, pauliPhase,
    chi_add_left, chi_add_right]
  have hstar := pauliPh_mul_star (p + q)
  have hassoc : x + p.1 + q.1 = x + (p.1 + q.1) := add_assoc x p.1 q.1
  rw [hassoc]
  calc pauliPh p * (chi p.2 x : ℂ) * (pauliPh q * ((chi q.2 x * chi q.2 p.1 : ℤ) : ℂ) * ψ (x + (p.1 + q.1)))
      = pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * 1 *
          ((chi p.2 x : ℂ) * (chi q.2 x : ℂ)) * ψ (x + (p.1 + q.1)) := by push_cast; ring
    _ = pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * (star (pauliPh (p + q)) * pauliPh (p + q)) *
          ((chi p.2 x : ℂ) * (chi q.2 x : ℂ)) * ψ (x + (p.1 + q.1)) := by rw [hstar]
    _ = pauliPh p * pauliPh q * (chi q.2 p.1 : ℂ) * star (pauliPh (p + q)) *
          (pauliPh (p + q) * ((chi p.2 x * chi q.2 x : ℤ) : ℂ) * ψ (x + (p.1 + q.1))) := by
        push_cast; ring

/-- Commutation relation: `pauliPhase p q = (-1)^{ω(p,q)} * pauliPhase q p`. -/
lemma pauliPhase_comm {n : ℕ} (p q : PauliIdx n) :
    pauliPhase p q = (sympSign p q : ℂ) * pauliPhase q p := by
  have hchi : (chi q.2 p.1 : ℂ) = (sympSign p q : ℂ) * (chi p.2 q.1 : ℂ) := by
    norm_cast
    simp only [chi, sympSign, symp, dot_comm q.2 p.1]
    rcases zmod2_cases (dot p.1 q.2) with h1 | h1 <;> rcases zmod2_cases (dot p.2 q.1) with h2 | h2
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]; decide
  simp only [pauliPhase, add_comm p q]
  rw [hchi]; ring

/-- Operator commutation law: `P_p P_q = (-1)^{ω(p,q)} P_q P_p`. -/
lemma pauliApply_comm {n : ℕ} (p q : PauliIdx n) (ψ : QState n) :
    pauliApply p (pauliApply q ψ) = (sympSign p q : ℂ) • pauliApply q (pauliApply p ψ) := by
  rw [pauliApply_comp, pauliApply_comp, add_comm p q, pauliPhase_comm, smul_smul]

/-- Explicit real/imaginary classification of `pauliPhase p q`:
    - If `symp p q = 0`: `pauliPhase p q ∈ {+1, -1}` (real integer sign).
    - If `symp p q = 1`: `(pauliPhase p q).re = 0` (purely imaginary). -/
lemma pauliPhase_re_cases {n : ℕ} (p q : PauliIdx n) :
    (symp p q = 0 → pauliPhase p q = 1 ∨ pauliPhase p q = -1) ∧
    (symp p q = 1 → (pauliPhase p q).re = 0) := by
  have hdot : dot (p + q).1 (p + q).2 = dot p.1 p.2 + dot q.1 q.2 + symp p q := by
    simp only [Prod.fst_add, Prod.snd_add, dot_add_left, dot_add_right, symp, dot_comm q.1 p.2]
    ring
  have h1 := zmod2_cases (dot p.1 p.2)
  have h2 := zmod2_cases (dot q.1 q.2)
  have h3 := chi_eq_one_or_neg_one q.2 p.1
  constructor
  · intro hs
    simp only [pauliPhase, pauliPh, hdot, hs, add_zero]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    all_goals
      simp [h1, h2, h3, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]
  · intro hs
    simp only [pauliPhase, pauliPh, hdot, hs]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    all_goals
      simp [h1, h2, h3, show (1 : ZMod 2) + 1 = 0 by decide, show (1 : ZMod 2) ≠ 0 by decide]

/-- Pauli expectation value `⟨ψ | P_p | ψ⟩` is always real. -/
lemma innerProd_pauliApply_self_real {n : ℕ} (p : PauliIdx n) (ψ : QState n) :
    ((innerProd ψ (pauliApply p ψ)).re : ℂ) = innerProd ψ (pauliApply p ψ) := by
  have hconj : star (innerProd ψ (pauliApply p ψ)) = innerProd ψ (pauliApply p ψ) := by
    rw [← innerProd_conj_symm, innerProd_pauliApply_right]
  apply Complex.ext
  · simp
  · have him := congr_arg Complex.im hconj
    rw [Complex.star_def, Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

lemma innerProd_pauliApply_self_normSq {n : ℕ} (p : PauliIdx n) (ψ : QState n) :
    Complex.normSq (innerProd ψ (pauliApply p ψ)) = (innerProd ψ (pauliApply p ψ)).re ^ 2 := by
  have him : (innerProd ψ (pauliApply p ψ)).im = 0 := by
    have := congr_arg Complex.im (innerProd_pauliApply_self_real p ψ)
    simpa using this.symm
  rw [Complex.normSq_apply, him]; ring

/-! ### Pauli Completeness, Parseval, and Symplectic Self-Duality -/

/-- **Pauli Completeness Identity** (matrix-free `ρ = 2⁻ⁿ ∑_p ⟨ψ|P_p|ψ⟩ P_p`):
    for all `ψ, φ : QState n`, `∑_p ⟨ψ|P_p|ψ⟩ P_p φ = 2ⁿ ⟨ψ|φ⟩ ψ`. -/
lemma pauli_completeness {n : ℕ} (ψ φ : QState n) :
    ∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) • pauliApply p φ =
      ((2 : ℂ) ^ n * innerProd ψ φ) • ψ := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, innerProd, pauliApply,
    Fintype.sum_prod_type]
  -- Swap sum over `b` inside sum over `y`!
  have hinner : ∀ a : F2 n,
      (∑ b : F2 n, (∑ y : F2 n, star (ψ y) * (pauliPh (a, b) * (chi b y : ℂ) * ψ (y + a))) *
        (pauliPh (a, b) * (chi b x : ℂ) * φ (x + a))) =
      (2 : ℂ) ^ n * star (ψ (x + a)) * φ (x + a) * ψ x := by
    intro a
    calc ∑ b : F2 n, (∑ y : F2 n, star (ψ y) * (pauliPh (a, b) * (chi b y : ℂ) * ψ (y + a))) *
            (pauliPh (a, b) * (chi b x : ℂ) * φ (x + a))
        = ∑ b : F2 n, ∑ y : F2 n,
            (chi b (x + y + a) : ℂ) * (star (ψ y) * ψ (y + a) * φ (x + a)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hsq := pauliPh_sq (a, b)
          have hchi : (chi b (x + y + a) : ℂ) =
              (chi b x : ℂ) * (chi b y : ℂ) * (chi b a : ℂ) := by
            rw [chi_add_right, chi_add_right]; push_cast; ring
          rw [hchi]
          calc star (ψ y) * (pauliPh (a, b) * (chi b y : ℂ) * ψ (y + a)) *
                (pauliPh (a, b) * (chi b x : ℂ) * φ (x + a))
              = (pauliPh (a, b) * pauliPh (a, b)) * ((chi b x : ℂ) * (chi b y : ℂ)) *
                  (star (ψ y) * ψ (y + a) * φ (x + a)) := by ring
            _ = (chi b a : ℂ) * ((chi b x : ℂ) * (chi b y : ℂ)) *
                  (star (ψ y) * ψ (y + a) * φ (x + a)) := by rw [hsq]
            _ = _ := by ring
      _ = ∑ y : F2 n, (∑ b : F2 n, (chi b (x + y + a) : ℂ)) * (star (ψ y) * ψ (y + a) * φ (x + a)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]
      _ = ∑ y : F2 n, if y = x + a then (2 : ℂ) ^ n * (star (ψ y) * ψ (y + a) * φ (x + a)) else 0 := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Int.cast_sum, sum_chi]
          have hiff : x + y + a = 0 ↔ y = x + a := by
            constructor
            · intro h
              have h1 := congr_arg (y + ·) h
              have h2 : y + (x + y + a) = x + a := by
                rw [add_comm x y, add_assoc, ← add_assoc y y, f2_add_self, zero_add]
              rw [h2, add_zero] at h1; exact h1.symm
            · intro hy; rw [hy, f2_add_cancel_left, f2_add_self]
          by_cases h : y = x + a
          · have hxya : x + y + a = 0 := hiff.mpr h
            rw [hxya]; simp only [h, ↓reduceIte]; push_cast; rfl
          · have hxya : x + y + a ≠ 0 := fun hc => h (hiff.mp hc)
            simp only [hxya, h, ↓reduceIte, Int.cast_zero, zero_mul]
      _ = (2 : ℂ) ^ n * star (ψ (x + a)) * φ (x + a) * ψ x := by
          rw [Finset.sum_ite_eq' Finset.univ (x + a)]
          simp [f2_add_cancel_right]; ring
  simp_rw [hinner]
  calc ∑ a : F2 n, (2 : ℂ) ^ n * star (ψ (x + a)) * φ (x + a) * ψ x
      = (2 : ℂ) ^ n * (∑ a : F2 n, star (ψ (x + a)) * φ (x + a)) * ψ x := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => by ring
    _ = (2 : ℂ) ^ n * (∑ z : F2 n, star (ψ z) * φ z) * ψ x := by
        congr 2
        exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun _ => rfl

/-- **Pauli Parseval Identity**: `∑_p ⟨ψ|P_p|ψ⟩ ⟨φ|P_p|φ⟩ = 2ⁿ |⟨ψ|φ⟩|²`. -/
lemma pauli_parseval {n : ℕ} (ψ φ : QState n) :
    ∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) * innerProd φ (pauliApply p φ) =
      (2 : ℂ) ^ n * (Complex.normSq (innerProd ψ φ) : ℂ) := by
  have h := congr_arg (innerProd φ) (pauli_completeness ψ φ)
  rw [innerProd_sum_right, innerProd_smul_right] at h
  have h1 : (∑ p : PauliIdx n, innerProd φ (innerProd ψ (pauliApply p ψ) • pauliApply p φ)) =
      ∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) * innerProd φ (pauliApply p φ) := by
    refine Finset.sum_congr rfl fun p _ => innerProd_smul_right _ _ _
  rw [h1] at h
  rw [h, innerProd_conj_symm ψ φ, mul_assoc, Complex.star_def, Complex.mul_conj]

/-- **Special Case (`φ = ψ`)**: `∑_p |⟨ψ|P_p|ψ⟩|² = 2ⁿ` for any unit state `ψ`. -/
lemma sum_normSq_pauliExpect {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) :
    ∑ p : PauliIdx n, Complex.normSq (innerProd ψ (pauliApply p ψ)) = (2 : ℝ) ^ n := by
  have h := pauli_parseval ψ ψ
  rw [hunit] at h
  have hre := congr_arg Complex.re h
  have hlhs : (∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) * innerProd ψ (pauliApply p ψ)).re =
      ∑ p : PauliIdx n, Complex.normSq (innerProd ψ (pauliApply p ψ)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [innerProd_pauliApply_self_normSq]
    have hr := innerProd_pauliApply_self_real p ψ
    conv_lhs => rw [← hr]
    simp [sq]
  rw [hlhs] at hre
  have hrhs : ((2 : ℂ) ^ n * (Complex.normSq (1 : ℂ) : ℂ)).re = (2 : ℝ) ^ n := by
    rw [Complex.normSq_one, Complex.ofReal_one, mul_one,
      show (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) by norm_cast, Complex.ofReal_re]
  rw [hrhs] at hre
  exact hre

/-- **Symplectic WHT Self-Duality**: `∑_p (-1)^{ω(p,q)} |⟨ψ|P_p|ψ⟩|² = 2ⁿ |⟨ψ|P_q|ψ⟩|²`. -/
lemma pauli_symp_self_dual {n : ℕ} (ψ : QState n) (q : PauliIdx n) :
    ∑ p : PauliIdx n, (sympSign p q : ℝ) * Complex.normSq (innerProd ψ (pauliApply p ψ)) =
      (2 : ℝ) ^ n * Complex.normSq (innerProd ψ (pauliApply q ψ)) := by
  have h := pauli_parseval ψ (pauliApply q ψ)
  have hterm : ∀ p : PauliIdx n,
      innerProd (pauliApply q ψ) (pauliApply p (pauliApply q ψ)) =
        (sympSign p q : ℂ) * innerProd ψ (pauliApply p ψ) := by
    intro p
    rw [← innerProd_pauliApply_right, pauliApply_comm q p, sympSign_comm q p,
      innerProd_smul_right, pauliApply_invol]
  simp_rw [hterm] at h
  have hre := congr_arg Complex.re h
  have hlhs : (∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) *
      ((sympSign p q : ℂ) * innerProd ψ (pauliApply p ψ))).re =
      ∑ p : PauliIdx n, (sympSign p q : ℝ) * Complex.normSq (innerProd ψ (pauliApply p ψ)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [innerProd_pauliApply_self_normSq]
    have hr := innerProd_pauliApply_self_real p ψ
    conv_lhs => rw [← hr]
    simp only [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hlhs] at hre
  have hrhs : ((2 : ℂ) ^ n * (Complex.normSq (innerProd ψ (pauliApply q ψ)) : ℂ)).re =
      (2 : ℝ) ^ n * Complex.normSq (innerProd ψ (pauliApply q ψ)) := by
    have : (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hrhs] at hre
  exact hre

/-- **Purity Identity (`ρ² = ρ` in Pauli basis)**:
    `∑_p ⟨ψ|P_p|ψ⟩ * pauliPhase q p * ⟨ψ|P_{q+p}|ψ⟩ = 2ⁿ ⟨ψ|P_q|ψ⟩` for any unit state `ψ`. -/
lemma pauli_purity_identity {n : ℕ} {ψ : QState n} (hunit : IsUnitState ψ) (q : PauliIdx n) :
    ∑ p : PauliIdx n, innerProd ψ (pauliApply p ψ) * pauliPhase q p *
        innerProd ψ (pauliApply (q + p) ψ) =
      (2 : ℂ) ^ n * innerProd ψ (pauliApply q ψ) := by
  have h := congr_arg (innerProd (pauliApply q ψ)) (pauli_completeness ψ ψ)
  rw [hunit, mul_one, innerProd_sum_right, innerProd_smul_right] at h
  have hrhs : innerProd (pauliApply q ψ) ψ = innerProd ψ (pauliApply q ψ) := by
    rw [← innerProd_pauliApply_right]
  rw [hrhs] at h
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [innerProd_smul_right, ← innerProd_pauliApply_right, pauliApply_comp, innerProd_smul_right]
  ring

/-! ### Part I: Direct 5-Line Proof for ALL Odd `n ≥ 3` (No Basis Partition Required!) -/

/-- Elementary irrationality of `√2` in `ℤ`: `a² = 2 b² → b = 0`. -/
lemma int_sq_ne_two_mul_sq (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  suffices ∀ (n : ℕ) (x y : ℕ), x + y ≤ n → x ^ 2 = 2 * y ^ 2 → y = 0 by
    have hnat : a.natAbs ^ 2 = 2 * b.natAbs ^ 2 := by zify; simpa [sq_abs] using h
    have hb0 := this (a.natAbs + b.natAbs) a.natAbs b.natAbs le_rfl hnat
    exact Int.natAbs_eq_zero.mp hb0
  intro n
  induction n with
  | zero => intro x y hxy _; omega
  | succ m ih =>
    intro x y hxy hsq
    by_cases hy : y = 0
    · exact hy
    · have hx_even : 2 ∣ x := by
        have h2 : 2 ∣ x ^ 2 := ⟨y ^ 2, hsq⟩
        exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      obtain ⟨x', rfl⟩ := hx_even
      have hy_sq : y ^ 2 = 2 * x' ^ 2 := by linarith
      have hy_even : 2 ∣ y := by
        have h2 : 2 ∣ y ^ 2 := ⟨x' ^ 2, hy_sq⟩
        exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      obtain ⟨y', rfl⟩ := hy_even
      have hx'_sq : x' ^ 2 = 2 * y' ^ 2 := by linarith
      have hy'0 : y' = 0 := ih x' y' (by omega) hx'_sq
      omega

/-- **Strong Odd-`n` Theorem (No Basis Partition Required!)**:
    For every odd `n = 2k + 1 ≥ 3`, NO pure state `|ψ⟩ ∈ (ℂ²)^⊗n` even satisfies
    `|⟨ψ|P|ψ⟩|² ∈ {0, 2⁻ⁿ}` for all non-identity Paulis `P ≠ I`. -/
theorem no_pauli_two_valued_odd (k : ℕ) (hk : 1 ≤ k) (ψ : QState (2 * k + 1))
    (hunit : IsUnitState ψ) :
    ¬ (∀ p : PauliIdx (2 * k + 1), p ≠ 0 →
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 0 ∨
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 / (2 : ℝ) ^ (2 * k + 1)) := by
  intro htwo
  have hunit' : innerProd ψ ψ = 1 := hunit
  let c : PauliIdx (2 * k + 1) → ℝ := fun p => (innerProd ψ (pauliApply p ψ)).re
  have hc_real : ∀ p : PauliIdx (2 * k + 1), (c p : ℂ) = innerProd ψ (pauliApply p ψ) :=
    fun p => innerProd_pauliApply_self_real p ψ
  have hc_sq : ∀ p : PauliIdx (2 * k + 1), (c p) ^ 2 = Complex.normSq (innerProd ψ (pauliApply p ψ)) :=
    fun p => (innerProd_pauliApply_self_normSq p ψ).symm
  have hc0 : c 0 = 1 := by
    simp [c, pauliApply_zero, hunit']
  -- Pick some `q ≠ 0` with `c q ≠ 0` (exists since `∑_p c_p² = 2^(2k+1) > 1 = c_0²`)!
  have hex_q : ∃ q : PauliIdx (2 * k + 1), q ≠ 0 ∧ c q ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsum := sum_normSq_pauliExpect hunit
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx (2 * k + 1)))] at hsum
    have h0 : Complex.normSq (innerProd ψ (pauliApply 0 ψ)) = 1 := by
      rw [← hc_sq 0, hc0]; norm_num
    have hrest : ∑ p ∈ Finset.univ.erase (0 : PauliIdx (2 * k + 1)),
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [← hc_sq p, hall p (Finset.mem_erase.mp hp).1]; norm_num
    rw [h0, hrest, add_zero] at hsum
    have h2n : (2 : ℝ) ^ (2 * k + 1) ≥ 8 := by
      have : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  obtain ⟨q, hq_ne, hcq_ne⟩ := hex_q
  have hcq_sq : (c q) ^ 2 = 1 / (2 : ℝ) ^ (2 * k + 1) := by
    rcases htwo q hq_ne with h0 | hval
    · exfalso; apply hcq_ne; rw [← hc_sq q] at h0; exact sq_eq_zero_iff.mp h0
    · rw [hc_sq q]; exact hval
  -- Take real part of `pauli_purity_identity hunit q`!
  have hpur := congr_arg Complex.re (pauli_purity_identity hunit q)
  have hrhs : ((2 : ℂ) ^ (2 * k + 1) * innerProd ψ (pauliApply q ψ)).re = (2 : ℝ) ^ (2 * k + 1) * c q := by
    have h2c : (2 : ℂ) ^ (2 * k + 1) = (((2 : ℝ) ^ (2 * k + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [← hc_real q, h2c, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hlhs : (∑ p : PauliIdx (2 * k + 1), innerProd ψ (pauliApply p ψ) * pauliPhase q p *
      innerProd ψ (pauliApply (q + p) ψ)).re =
      ∑ p : PauliIdx (2 * k + 1), (pauliPhase q p).re * c p * c (q + p) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hc_real p, ← hc_real (q + p)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hlhs, hrhs] at hpur
  -- Peel off `p = 0` and `p = q` from the sum!
  let S : Finset (PauliIdx (2 * k + 1)) := (Finset.univ.erase (0 : PauliIdx (2 * k + 1))).erase q
  have hq_in : q ∈ Finset.univ.erase (0 : PauliIdx (2 * k + 1)) :=
    Finset.mem_erase.mpr ⟨hq_ne, Finset.mem_univ q⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : PauliIdx (2 * k + 1))),
      ← Finset.add_sum_erase _ _ hq_in] at hpur
  have ht0 : (pauliPhase q 0).re * c 0 * c (q + 0) = c q := by
    rw [pauliPhase_zero_right, Complex.one_re, hc0, add_zero]; ring
  have htq : (pauliPhase q q).re * c q * c (q + q) = c q := by
    rw [pauliPhase_self, Complex.one_re, pauliIdx_add_self, hc0]; ring
  rw [ht0, htq] at hpur
  -- Multiply by `2^(2k+1)`: every term in `S` is an integer!
  have hterm_int : ∀ p ∈ S, ∃ m : ℤ,
      (m : ℝ) = (2 : ℝ) ^ (2 * k + 1) * ((pauliPhase q p).re * c p * c (q + p)) := by
    intro p hp
    have hp_ne_q : p ≠ q := (Finset.mem_erase.mp hp).1
    have hp_ne_0 : p ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    have hqp_ne_0 : q + p ≠ 0 := fun hc => by
      have := congr_arg (q + ·) hc
      rw [pauliIdx_add_cancel_left, add_zero] at this
      exact hp_ne_q this
    have hprod_int : ∃ s : ℤ, (s : ℝ) = (2 : ℝ) ^ (2 * k + 1) * (c p * c (q + p)) := by
      have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * k + 1) := by positivity
      have hcp := htwo p hp_ne_0
      have hcqp := htwo (q + p) hqp_ne_0
      rw [← hc_sq p] at hcp
      rw [← hc_sq (q + p)] at hcqp
      rcases hcp with hp0 | hpv
      · refine ⟨0, ?_⟩; rw [sq_eq_zero_iff.mp hp0]; simp
      · rcases hcqp with hqp0 | hqpv
        · refine ⟨0, ?_⟩; rw [sq_eq_zero_iff.mp hqp0]; simp
        · have hsq1 : ((2 : ℝ) ^ (2 * k + 1) * (c p * c (q + p))) ^ 2 = 1 := by
            have : ((2 : ℝ) ^ (2 * k + 1) * (c p * c (q + p))) ^ 2 =
                ((2 : ℝ) ^ (2 * k + 1)) ^ 2 * (c p) ^ 2 * (c (q + p)) ^ 2 := by ring
            rw [this, hpv, hqpv]; field_simp [ne_of_gt h2n_pos]
          rcases sq_eq_one_iff.mp hsq1 with h1 | h1
          · exact ⟨1, by simpa using h1.symm⟩
          · exact ⟨-1, by simpa using h1.symm⟩
    obtain ⟨s, hs⟩ := hprod_int
    rcases zmod2_cases (symp q p) with hsymp | hsymp
    · rcases (pauliPhase_re_cases q p).1 hsymp with hph | hph
      · refine ⟨s, ?_⟩; rw [hph, Complex.one_re, one_mul, hs]
      · refine ⟨-s, ?_⟩; rw [hph, Complex.neg_re, Complex.one_re]; push_cast; linarith
    · refine ⟨0, ?_⟩; rw [(pauliPhase_re_cases q p).2 hsymp]; simp
  choose mInt hmInt using hterm_int
  let M : ℤ := ∑ p ∈ S.attach, mInt p.1 p.2
  have hM_real : (M : ℝ) = (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) - 2) * c q := by
    have hsumM : (M : ℝ) = ∑ p ∈ S, (2 : ℝ) ^ (2 * k + 1) * ((pauliPhase q p).re * c p * c (q + p)) := by
      simp only [M, Int.cast_sum]
      rw [← Finset.sum_attach S]
      refine Finset.sum_congr rfl fun p _ => hmInt p.1 p.2
    have hsum_eq : ∑ p ∈ S, (pauliPhase q p).re * c p * c (q + p) =
        ((2 : ℝ) ^ (2 * k + 1) - 2) * c q := by linarith
    rw [hsumM, ← Finset.mul_sum, hsum_eq]; ring
  -- Square both sides: `M² = 2 * (2^k * (2^(2k+1) - 2))²` with `2^k * (2^(2k+1) - 2) > 0`!
  have hM_sq_real : ((M : ℝ)) ^ 2 = ((2 * ((2 : ℤ) ^ k * ((2 : ℤ) ^ (2 * k + 1) - 2)) ^ 2 : ℤ) : ℝ) := by
    rw [hM_real]
    have h2n_ne : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
    have h2odd : (2 : ℝ) ^ (2 * k + 1) = 2 * ((2 : ℝ) ^ k) ^ 2 := by
      rw [pow_succ, mul_comm 2 k, pow_mul]; ring
    calc ((2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) - 2) * c q) ^ 2
        = ((2 : ℝ) ^ (2 * k + 1)) ^ 2 * ((2 : ℝ) ^ (2 * k + 1) - 2) ^ 2 * (c q) ^ 2 := by ring
      _ = ((2 : ℝ) ^ (2 * k + 1)) ^ 2 * ((2 : ℝ) ^ (2 * k + 1) - 2) ^ 2 * (1 / (2 : ℝ) ^ (2 * k + 1)) := by rw [hcq_sq]
      _ = (2 : ℝ) ^ (2 * k + 1) * ((2 : ℝ) ^ (2 * k + 1) - 2) ^ 2 := by field_simp [h2n_ne]
      _ = 2 * ((2 : ℝ) ^ k * ((2 : ℝ) ^ (2 * k + 1) - 2)) ^ 2 := by
          conv_lhs => rw [h2odd]
          ring
      _ = _ := by push_cast; ring
  have hM_sq : M ^ 2 = 2 * ((2 : ℤ) ^ k * ((2 : ℤ) ^ (2 * k + 1) - 2)) ^ 2 := by
    exact_mod_cast hM_sq_real
  have hb0 := int_sq_ne_two_mul_sq M ((2 : ℤ) ^ k * ((2 : ℤ) ^ (2 * k + 1) - 2)) hM_sq
  have hb_pos : (0 : ℤ) < (2 : ℤ) ^ k * ((2 : ℤ) ^ (2 * k + 1) - 2) := by
    have h1 : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
    have h2 : (8 : ℤ) ≤ (2 : ℤ) ^ (2 * k + 1) := by
      have : (2 : ℤ) ^ 3 ≤ (2 : ℤ) ^ (2 * k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    nlinarith
  linarith

/-! ### Part II: Symplectic Orthogonal Complement & Lagrangian Reduction (All `n ≥ 3`) -/

/-- **Pauli-Covariant MUB Fiducial State**:
    a unit vector `|ψ⟩ ∈ (ℂ²)^⊗n` whose Pauli orbit `{P_p |ψ⟩}` partitions into `2ⁿ`
    pairwise mutually unbiased orthonormal bases. -/
def IsPauliMubFiducial (n : ℕ) (ψ : QState n) : Prop :=
  IsUnitState ψ ∧
  ∃ (basisIdx : PauliIdx n → Fin (2 ^ n)),
    (∀ p q : PauliIdx n, basisIdx p = basisIdx q → p ≠ q →
      innerProd (pauliApply p ψ) (pauliApply q ψ) = 0) ∧
    (∀ p q : PauliIdx n, basisIdx p ≠ basisIdx q →
      Complex.normSq (innerProd (pauliApply p ψ) (pauliApply q ψ)) = 1 / (2 : ℝ) ^ n)

/-- Symplectic orthogonal complement `H^⊥ = {p | ∀ h ∈ H, symp p h = 0}`. -/
def sympOrth {n : ℕ} (H : Submodule (ZMod 2) (PauliIdx n)) : Submodule (ZMod 2) (PauliIdx n) where
  carrier := {p : PauliIdx n | ∀ h ∈ H, symp p h = 0}
  add_mem' {p₁ p₂} h₁ h₂ h hh := by rw [symp_add_left, h₁ h hh, h₂ h hh, add_zero]
  zero_mem' h _ := symp_zero_left h
  smul_mem' c p hp h hh := by
    rcases zmod2_cases c with rfl | rfl
    · simp [symp_zero_left]
    · simpa using hp h hh

lemma mem_sympOrth_iff {n : ℕ} {H : Submodule (ZMod 2) (PauliIdx n)} {p : PauliIdx n} :
    p ∈ sympOrth H ↔ ∀ h ∈ H, symp p h = 0 := Iff.rfl

/-- Symplectic character sum over a subspace `H ≤ PauliIdx n`. -/
lemma sum_sympSign_submodule {n : ℕ} (H : Submodule (ZMod 2) (PauliIdx n)) (p : PauliIdx n) :
    ∑ h : H, sympSign p h.1 = if p ∈ sympOrth H then (Fintype.card H : ℤ) else 0 := by
  by_cases hp : p ∈ sympOrth H
  · simp only [hp, ↓reduceIte]
    have h1 : ∀ h : H, sympSign p h.1 = 1 := fun h => by simp [sympSign, hp h.1 h.2]
    simp [h1]
  · simp only [hp, ↓reduceIte]
    rw [mem_sympOrth_iff] at hp
    push Not at hp
    obtain ⟨v, hv, hne⟩ := hp
    have hs1 : symp p v = 1 := by
      rcases zmod2_cases (symp p v) with h | h
      · exact absurd h hne
      · exact h
    let vSub : H := ⟨v, hv⟩
    have hshift : ∑ h : H, sympSign p h.1 = ∑ h : H, sympSign p (h + vSub).1 :=
      (Fintype.sum_equiv (Equiv.addRight vSub) _ _ (fun _ => rfl)).symm
    have hneg : ∑ h : H, sympSign p (h + vSub).1 = -(∑ h : H, sympSign p h.1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      change sympSign p (h.1 + v) = -sympSign p h.1
      rw [sympSign_add_right]
      simp [sympSign, hs1]
    linarith

lemma card_submodule_pauli {n : ℕ} (H : Submodule (ZMod 2) (PauliIdx n)) :
    Fintype.card H = 2 ^ Module.finrank (ZMod 2) H := by
  have e := Module.finBasis (ZMod 2) H
  have hcard := Fintype.card_congr e.equivFun.toEquiv
  simp [Fintype.card_pi, ZMod.card] at hcard
  exact hcard

/-- Rank-nullity bound for symplectic orthogonal complement: `2n ≤ finrank H^⊥ + finrank H`. -/
lemma finrank_sympOrth_ge {n : ℕ} (H : Submodule (ZMod 2) (PauliIdx n)) :
    2 * n ≤ Module.finrank (ZMod 2) (sympOrth H) + Module.finrank (ZMod 2) H := by
  let L : PauliIdx n →ₗ[ZMod 2] (H →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun p =>
        { toFun := fun h => symp p h.1
          map_add' := fun h₁ h₂ => symp_add_right p h₁.1 h₂.1
          map_smul' := fun c h => by
            rcases zmod2_cases c with rfl | rfl <;> simp [symp_zero_right] }
      map_add' := fun p₁ p₂ => by ext h; exact symp_add_left p₁ p₂ h.1
      map_smul' := fun c p => by
        ext h; rcases zmod2_cases c with rfl | rfl <;> simp [symp_zero_left] }
  have hker : LinearMap.ker L = sympOrth H := by
    ext p
    simp only [LinearMap.mem_ker, mem_sympOrth_iff]
    constructor
    · intro hp h hh; simpa [L] using LinearMap.congr_fun hp ⟨h, hh⟩
    · intro hp; ext ⟨h, hh⟩; simpa [L] using hp h hh
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, Module.finrank_prod, Module.finrank_fin_fun] at hrn
  have hle : Module.finrank (ZMod 2) (LinearMap.range L) ≤
      Module.finrank (ZMod 2) (H →ₗ[ZMod 2] ZMod 2) := Submodule.finrank_le _
  have hdual : Module.finrank (ZMod 2) (H →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) H := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  omega

/-- **Lemma 1 (Lagrangian Zero Subgroup)**:
    For any Pauli-covariant MUB fiducial `|ψ⟩`, the basis fiber `H = {p | basisIdx p = basisIdx 0}`
    is a Lagrangian (`n`-dimensional maximal abelian) subspace: `sympOrth H = H` and `finrank H = n`. -/
lemma mub_zero_lagrangian {n : ℕ} {ψ : QState n} (h : IsPauliMubFiducial n ψ) :
    ∃ H : Submodule (ZMod 2) (PauliIdx n),
      Module.finrank (ZMod 2) H = n ∧
      sympOrth H = H ∧
      (∀ p ∈ H, p ≠ 0 → innerProd ψ (pauliApply p ψ) = 0) ∧
      (∀ p : PauliIdx n, p ∉ H →
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 / (2 : ℝ) ^ n) := by
  obtain ⟨hunit, basisIdx, horth, hmub⟩ := h
  have hmem_iff : ∀ p : PauliIdx n,
      basisIdx p = basisIdx 0 ↔ (p = 0 ∨ innerProd ψ (pauliApply p ψ) = 0) := by
    intro p
    constructor
    · intro hp
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      · right
        have := horth 0 p hp.symm (Ne.symm hp0)
        simpa [pauliApply_zero] using this
    · intro hp
      rcases hp with rfl | hz
      · rfl
      · by_contra hne
        have hns := hmub 0 p (Ne.symm hne)
        rw [pauliApply_zero, hz, map_zero] at hns
        have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ n := by positivity
        linarith
  let H : Submodule (ZMod 2) (PauliIdx n) :=
    { carrier := {p : PauliIdx n | basisIdx p = basisIdx 0}
      zero_mem' := rfl
      add_mem' := fun {p q} hp hq => by
        change basisIdx (p + q) = basisIdx 0
        rw [hmem_iff]
        by_cases hpq : p = q
        · left; rw [hpq, pauliIdx_add_self]
        · right
          have h0 := horth p q (hp.trans hq.symm) hpq
          rw [← innerProd_pauliApply_right, pauliApply_comp, innerProd_smul_right] at h0
          exact (mul_eq_zero.mp h0).resolve_left (pauliPhase_ne_zero p q)
      smul_mem' := fun c p hp => by
        rcases zmod2_cases c with rfl | rfl
        · change basisIdx ((0 : ZMod 2) • p) = basisIdx 0; simp
        · simpa using hp }
  have hunit' : innerProd ψ ψ = 1 := hunit
  have hH_zero : ∀ p ∈ H, p ≠ 0 → innerProd ψ (pauliApply p ψ) = 0 := fun p hp hp0 =>
    ((hmem_iff p).mp hp).resolve_left hp0
  have hH_out : ∀ p : PauliIdx n, p ∉ H →
      Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 / (2 : ℝ) ^ n := fun p hp => by
    have hne : basisIdx 0 ≠ basisIdx p := fun hc => hp hc.symm
    simpa [pauliApply_zero] using hmub 0 p hne
  -- Compute `Fintype.card H = 2^n` directly from Parseval `∑_p |⟨ψ|P_p|ψ⟩|² = 2^n`!
  have hcardH : Fintype.card H = 2 ^ n := by
    have hsum := sum_normSq_pauliExpect hunit
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : PauliIdx n => p ∈ H)] at hsum
    have hsumH : ∑ p ∈ Finset.univ.filter (fun p : PauliIdx n => p ∈ H),
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 := by
      have h0mem : (0 : PauliIdx n) ∈ Finset.univ.filter (fun p : PauliIdx n => p ∈ H) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ 0, H.zero_mem⟩
      rw [← Finset.add_sum_erase _ _ h0mem]
      have h0 : Complex.normSq (innerProd ψ (pauliApply 0 ψ)) = 1 := by
        simp [pauliApply_zero, hunit', Complex.normSq_one]
      have hrest : ∑ p ∈ (Finset.univ.filter (fun p : PauliIdx n => p ∈ H)).erase 0,
          Complex.normSq (innerProd ψ (pauliApply p ψ)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
        rw [hH_zero p (Finset.mem_filter.mp hmem).2 hne, map_zero]
      rw [h0, hrest, add_zero]
    have hsumOut : ∑ p ∈ Finset.univ.filter (fun p : PauliIdx n => p ∉ H),
        Complex.normSq (innerProd ψ (pauliApply p ψ)) =
        ((Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card : ℝ) * (1 / (2 : ℝ) ^ n) := by
      rw [Finset.sum_congr rfl fun p hp => hH_out p (Finset.mem_filter.mp hp).2,
        Finset.sum_const, nsmul_eq_mul]
    rw [hsumH, hsumOut] at hsum
    have hcard_tot : (Finset.univ.filter (fun p : PauliIdx n => p ∈ H)).card +
        (Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card = 2 ^ n * 2 ^ n := by
      have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (PauliIdx n))
        (fun p => p ∈ H) (fun _ => (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_prod,
        Fintype.card_pi, ZMod.card, Finset.prod_const, Fintype.card_fin] at h1
      exact h1
    have hcard_eq : (Finset.univ.filter (fun p : PauliIdx n => p ∈ H)).card = Fintype.card H := by
      rw [← Fintype.card_coe]; exact Fintype.card_congr (Equiv.subtypeEquivRight fun p => by simp)
    have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    have hnot_real : ((Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card : ℝ) =
        (2 : ℝ) ^ n * (2 : ℝ) ^ n - (2 : ℝ) ^ n := by
      have h1 : ((Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card : ℝ) * (1 / (2 : ℝ) ^ n) =
          (2 : ℝ) ^ n - 1 := by linarith
      have h2 : ((Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card : ℝ) / (2 : ℝ) ^ n =
          (2 : ℝ) ^ n - 1 := by rw [div_eq_mul_one_div]; exact h1
      rw [div_eq_iff h2n_ne] at h2; linarith
    have hle : 2 ^ n ≤ 2 ^ n * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
    have hnot_nat : (Finset.univ.filter (fun p : PauliIdx n => p ∉ H)).card = 2 ^ n * 2 ^ n - 2 ^ n := by
      have hcast : ((2 ^ n * 2 ^ n - 2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n * (2 : ℝ) ^ n - (2 : ℝ) ^ n := by
        rw [Nat.cast_sub hle]; push_cast; ring
      exact_mod_cast hnot_real.trans hcast.symm
    omega
  have hfinH : Module.finrank (ZMod 2) H = n := by
    have hc := card_submodule_pauli H
    rw [hcardH] at hc
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) hc).symm
  -- Symplectic WHT Self-Duality summed over `q ∈ H` gives `∑_{p ∈ H^⊥} |⟨ψ|P_p|ψ⟩|² = 1`!
  have hdual_sum : ∑ p : sympOrth H, Complex.normSq (innerProd ψ (pauliApply p.1 ψ)) = 1 := by
    have hsum_q : ∑ q : H, ∑ p : PauliIdx n,
        (sympSign p q.1 : ℝ) * Complex.normSq (innerProd ψ (pauliApply p ψ)) =
        ∑ q : H, (2 : ℝ) ^ n * Complex.normSq (innerProd ψ (pauliApply q.1 ψ)) :=
      Finset.sum_congr rfl fun q _ => pauli_symp_self_dual ψ q.1
    rw [Finset.sum_comm] at hsum_q
    have hlhs : (∑ p : PauliIdx n, ∑ q : H,
        (sympSign p q.1 : ℝ) * Complex.normSq (innerProd ψ (pauliApply p ψ))) =
        (2 : ℝ) ^ n * ∑ p : sympOrth H, Complex.normSq (innerProd ψ (pauliApply p.1 ψ)) := by
      have h1 : ∀ p : PauliIdx n, (∑ q : H,
          (sympSign p q.1 : ℝ) * Complex.normSq (innerProd ψ (pauliApply p ψ))) =
          if p ∈ sympOrth H then (2 : ℝ) ^ n * Complex.normSq (innerProd ψ (pauliApply p ψ)) else 0 := by
        intro p
        rw [← Finset.sum_mul, ← Int.cast_sum, sum_sympSign_submodule, hcardH]
        split_ifs <;> simp
      simp_rw [h1, ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      exact Finset.sum_subtype (Finset.univ.filter (fun p : PauliIdx n => p ∈ sympOrth H))
        (p := fun p => p ∈ sympOrth H)
        (fun p => by simp) (fun p => Complex.normSq (innerProd ψ (pauliApply p ψ)))
    have hrhs : (∑ q : H, (2 : ℝ) ^ n * Complex.normSq (innerProd ψ (pauliApply q.1 ψ))) =
        (2 : ℝ) ^ n := by
      rw [← Finset.mul_sum]
      have h0sub : (⟨0, H.zero_mem⟩ : H) ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ h0sub]
      have h0 : Complex.normSq (innerProd ψ (pauliApply 0 ψ)) = 1 := by
        simp [pauliApply_zero, hunit', Complex.normSq_one]
      have hrest : ∑ q ∈ Finset.univ.erase (⟨0, H.zero_mem⟩ : H),
          Complex.normSq (innerProd ψ (pauliApply q.1 ψ)) = 0 := by
        refine Finset.sum_eq_zero fun q hq => ?_
        have hne : q.1 ≠ 0 := fun hc => (Finset.mem_erase.mp hq).1 (Subtype.ext hc)
        rw [hH_zero q.1 q.2 hne, map_zero]
      rw [h0, hrest, add_zero, mul_one]
    rw [hlhs, hrhs] at hsum_q
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0) (by linarith)
  have hsub : sympOrth H ≤ H := by
    intro p hp
    by_cases hp0 : p = 0
    · rw [hp0]; exact H.zero_mem
    · have h0sub : (⟨0, (sympOrth H).zero_mem⟩ : sympOrth H) ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ h0sub] at hdual_sum
      have h0 : Complex.normSq (innerProd ψ (pauliApply 0 ψ)) = 1 := by
        simp [pauliApply_zero, hunit', Complex.normSq_one]
      have hrest0 : ∑ q ∈ Finset.univ.erase (⟨0, (sympOrth H).zero_mem⟩ : sympOrth H),
          Complex.normSq (innerProd ψ (pauliApply q.1 ψ)) = 0 := by linarith
      have hp_mem : (⟨p, hp⟩ : sympOrth H) ∈ Finset.univ.erase (⟨0, (sympOrth H).zero_mem⟩ : sympOrth H) :=
        Finset.mem_erase.mpr ⟨fun hc => hp0 (congr_arg Subtype.val hc), Finset.mem_univ _⟩
      have hp_ns : Complex.normSq (innerProd ψ (pauliApply p ψ)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun q _ => Complex.normSq_nonneg _).mp hrest0 ⟨p, hp⟩ hp_mem
      have hp_z : innerProd ψ (pauliApply p ψ) = 0 := Complex.normSq_eq_zero.mp hp_ns
      exact (hmem_iff p).mpr (Or.inr hp_z)
  have hlag : sympOrth H = H := by
    apply Submodule.eq_of_le_of_finrank_eq hsub
    have hge := finrank_sympOrth_ge H
    have hle := Submodule.finrank_mono hsub
    omega
  exact ⟨H, hfinH, hlag, hH_zero, hH_out⟩

/-! ### Symplectic Basis, Joint `+1` Eigenstate, and Reduction to `IsAlltop` -/

/-- **Explicit Symplectic Basis Construction** (zero induction!):
    every Lagrangian subspace `H` admits bases `f, e : Fin n → PauliIdx n` with `f` spanning `H`,
    `symp (f i) (f j) = 0`, `symp (e i) (e j) = 0`, and `symp (e i) (f j) = δᵢⱼ`. -/
lemma exists_symplectic_basis {n : ℕ} (H : Submodule (ZMod 2) (PauliIdx n))
    (hfin : Module.finrank (ZMod 2) H = n) (hlag : sympOrth H = H) :
    ∃ (f e : Fin n → PauliIdx n),
      (∀ j, f j ∈ H) ∧
      LinearIndependent (ZMod 2) f ∧
      (∀ i j, symp (f i) (f j) = 0) ∧
      (∀ i j, symp (e i) (e j) = 0) ∧
      (∀ i j, symp (e i) (f j) = if i = j then 1 else 0) := by
  let bH : Module.Basis (Fin n) (ZMod 2) H := Module.finBasisOfFinrankEq (ZMod 2) H hfin
  let f : Fin n → PauliIdx n := fun j => (bH j).1
  have hf_mem : ∀ j, f j ∈ H := fun j => (bH j).2
  have hf_li : LinearIndependent (ZMod 2) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsub : ∑ j : Fin n, c j • bH j = 0 := by
      apply Subtype.ext
      simpa [f] using hc
    exact Fintype.linearIndependent_iff.mp bH.linearIndependent c hsub
  have hff : ∀ i j, symp (f i) (f j) = 0 := fun i j => by
    have hi : f i ∈ sympOrth H := by rw [hlag]; exact hf_mem i
    exact hi (f j) (hf_mem j)
  -- Surjective evaluation map `L : PauliIdx n →ₗ[ZMod 2] F2 n`, `L v j = symp v (f j)`.
  let L : PauliIdx n →ₗ[ZMod 2] F2 n :=
    { toFun := fun v j => symp v (f j)
      map_add' := fun v w => by ext j; exact symp_add_left v w (f j)
      map_smul' := fun c v => by ext j; exact symp_smul_left c v (f j) }
  have hker : LinearMap.ker L = H := by
    ext v
    rw [LinearMap.mem_ker, ← hlag, mem_sympOrth_iff]
    constructor
    · intro hv h hh
      have hex : ∃ c : Fin n → ZMod 2, h = ∑ j : Fin n, c j • f j := by
        refine ⟨fun j => bH.repr ⟨h, hh⟩ j, ?_⟩
        have hsum := congr_arg (Submodule.subtype H) (bH.sum_repr ⟨h, hh⟩)
        rw [map_sum] at hsum
        simpa [f] using hsum.symm
      obtain ⟨c, rfl⟩ := hex
      rw [symp_sum_right]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [symp_smul_right]
      have hj : symp v (f j) = 0 := congr_fun hv j
      rw [hj, mul_zero]
    · intro hv
      ext j
      exact hv (f j) (hf_mem j)
  have hrange_top : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    rw [hker, hfin, Module.finrank_prod, Module.finrank_fin_fun] at hrn
    rw [Module.finrank_fin_fun]
    omega
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp hrange_top
  choose e₀ he₀ using fun i : Fin n => hsurj (eVec i)
  have he₀_f : ∀ i j, symp (e₀ i) (f j) = if i = j then 1 else 0 := fun i j => by
    have := congr_fun (he₀ i) j
    simpa [L, eVec, Pi.single_apply, eq_comm] using this
  -- Explicit 1-line Gram–Schmidt orthogonalization making `e` isotropic!
  let e : Fin n → PauliIdx n := fun i =>
    e₀ i + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), symp (e₀ i) (e₀ j) • f j
  have hef : ∀ i k, symp (e i) (f k) = if i = k then 1 else 0 := fun i k => by
    simp only [e, symp_add_left, symp_sum_left]
    have hz : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        symp (symp (e₀ i) (e₀ j) • f j) (f k) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [symp_smul_left, hff j k, mul_zero]
    rw [hz, add_zero, he₀_f]
  have hee_lt : ∀ i k : Fin n, k < i → symp (e i) (e k) = 0 := fun i k hki => by
    simp only [e]
    rw [symp_add_left, symp_add_right, symp_add_right, symp_sum_left, symp_sum_right, symp_sum_left]
    simp_rw [symp_sum_right]
    have hsum1 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        symp (symp (e₀ i) (e₀ j) • f j) (e₀ k) = symp (e₀ i) (e₀ k) := by
      have hterm : ∀ j : Fin n, symp (symp (e₀ i) (e₀ j) • f j) (e₀ k) =
          if j = k then symp (e₀ i) (e₀ j) else 0 := fun j => by
        rw [symp_smul_left, symp_comm (f j), he₀_f k j]
        by_cases hjk : j = k
        · subst hjk; simp
        · have hkj : k ≠ j := Ne.symm hjk
          simp [hjk, hkj]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq']
      simp [hki]
    have hsum2 : ∑ l ∈ Finset.univ.filter (fun l : Fin n => l < k),
        symp (e₀ i) (symp (e₀ k) (e₀ l) • f l) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hlk : l < k := (Finset.mem_filter.mp hl).2
      have hil : i ≠ l := ne_of_gt (lt_trans hlk hki)
      rw [symp_smul_right, he₀_f i l]; simp [hil]
    have hsum3 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i),
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => l < k),
        symp (symp (e₀ i) (e₀ j) • f j) (symp (e₀ k) (e₀ l) • f l) = 0 := by
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
      rw [symp_smul_left, symp_smul_right, hff j l, mul_zero, mul_zero]
    rw [hsum1, hsum2, hsum3]
    simp only [add_zero]
    rcases zmod2_cases (symp (e₀ i) (e₀ k)) with h | h <;> rw [h] <;> decide
  have hee : ∀ i k, symp (e i) (e k) = 0 := fun i k => by
    rcases lt_trichotomy i k with hik | rfl | hki
    · rw [symp_comm]; exact hee_lt k i hik
    · exact symp_self (e i)
    · exact hee_lt i k hki
  exact ⟨f, e, hf_mem, hf_li, hff, hee, hef⟩

/-- Ordered product `∏_{i < k} P_{g i}^{x i}` applied to a state `w : QState n`. -/
def applyProd {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) : (k : ℕ) → k ≤ n → QState n → QState n
  | 0, _, w => w
  | k + 1, hk, w =>
      let prev := applyProd g x k (Nat.le_of_succ_le hk) w
      if x ⟨k, hk⟩ = 0 then prev else pauliApply (g ⟨k, hk⟩) prev

/-- Linear combination `∑_{i < k} x_i g_i` in `PauliIdx n`. -/
def linComb {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) : (k : ℕ) → k ≤ n → PauliIdx n
  | 0, _ => 0
  | k + 1, hk =>
      linComb g x k (Nat.le_of_succ_le hk) + x ⟨k, hk⟩ • g ⟨k, hk⟩

lemma linComb_eq_sum {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) (k : ℕ) (hk : k ≤ n) :
    linComb g x k hk = ∑ i : Fin k, x ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ • g ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ := by
  induction k with
  | zero => simp [linComb]
  | succ m ih =>
    rw [linComb, ih (Nat.le_of_succ_le hk), Fin.sum_univ_castSucc]
    rfl

lemma applyProd_zero {n : ℕ} (g : Fin n → PauliIdx n) (k : ℕ) (hk : k ≤ n) (w : QState n) :
    applyProd g 0 k hk w = w := by
  induction k with
  | zero => rfl
  | succ m ih => simp [applyProd, ih]

lemma applyProd_add {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) (k : ℕ) (hk : k ≤ n)
    (w₁ w₂ : QState n) :
    applyProd g x k hk (w₁ + w₂) = applyProd g x k hk w₁ + applyProd g x k hk w₂ := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [applyProd, ih]
    split_ifs
    · rfl
    · exact pauliApply_add _ _ _

lemma applyProd_smul {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) (k : ℕ) (hk : k ≤ n)
    (c : ℂ) (w : QState n) :
    applyProd g x k hk (c • w) = c • applyProd g x k hk w := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [applyProd, ih]
    split_ifs
    · rfl
    · exact pauliApply_smul _ _ _

/-- `applyProd g x k` equals a unit scalar times `pauliApply (linComb g x k)`. -/
lemma applyProd_eq_phase_pauli {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) (k : ℕ) (hk : k ≤ n) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧
      ∀ w : QState n, applyProd g x k hk w = c • pauliApply (linComb g x k hk) w := by
  induction k with
  | zero => exact ⟨1, Complex.normSq_one, fun w => by simp [applyProd, linComb, pauliApply_zero]⟩
  | succ m ih =>
    obtain ⟨c, hc, heq⟩ := ih (Nat.le_of_succ_le hk)
    by_cases hx : x ⟨m, hk⟩ = 0
    · refine ⟨c, hc, fun w => ?_⟩
      simp only [applyProd, linComb, hx, ↓reduceIte, zero_smul, add_zero]
      exact heq w
    · have hx1 : x ⟨m, hk⟩ = 1 := (zmod2_cases (x ⟨m, hk⟩)).resolve_left hx
      refine ⟨c * pauliPhase (g ⟨m, hk⟩) (linComb g x m (Nat.le_of_succ_le hk)), ?_, fun w => ?_⟩
      · rw [map_mul, hc, pauliPhase_normSq, mul_one]
      · simp only [applyProd, linComb, hx, ↓reduceIte]
        rw [hx1, one_smul, heq w, pauliApply_smul, pauliApply_comp, smul_smul, add_comm (g ⟨m, hk⟩)]

/-- If `g` is isotropic (`symp (g i) (g j) = 0`), then `applyProd g x k` is Hermitian and unitary. -/
lemma innerProd_applyProd_right {n : ℕ} {g : Fin n → PauliIdx n}
    (hcomm : ∀ i j, symp (g i) (g j) = 0) (x : F2 n) (k : ℕ) (hk : k ≤ n) (u w : QState n) :
    innerProd u (applyProd g x k hk w) = innerProd (applyProd g x k hk u) w := by
  induction k generalizing u w with
  | zero => rfl
  | succ m ih =>
    simp only [applyProd]
    split_ifs
    · exact ih (Nat.le_of_succ_le hk) u w
    · rw [innerProd_pauliApply_right, ih (Nat.le_of_succ_le hk)]
      -- Commute `pauliApply (g ⟨m, hk⟩)` past `applyProd g x m`!
      have hcm : ∀ (j : ℕ) (hj : j ≤ n) (v : QState n),
          applyProd g x j hj (pauliApply (g ⟨m, hk⟩) v) =
          pauliApply (g ⟨m, hk⟩) (applyProd g x j hj v) := by
        intro j hj v
        induction j with
        | zero => rfl
        | succ r ihr =>
          simp only [applyProd]
          split_ifs
          · exact ihr (Nat.le_of_succ_le hj)
          · rw [ihr (Nat.le_of_succ_le hj), pauliApply_comm (g ⟨r, hj⟩) (g ⟨m, hk⟩)]
            simp [sympSign, hcomm]
      rw [hcm m (Nat.le_of_succ_le hk) u]

lemma innerProd_applyProd_both {n : ℕ} (g : Fin n → PauliIdx n) (x : F2 n) (k : ℕ) (hk : k ≤ n)
    (u w : QState n) :
    innerProd (applyProd g x k hk u) (applyProd g x k hk w) = innerProd u w := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [applyProd]
    split_ifs
    · exact ih (Nat.le_of_succ_le hk)
    · rw [innerProd_pauliApply_both, ih (Nat.le_of_succ_le hk)]

/-- Commutation of `pauliApply p` with `applyProd g x k`: picks up `∏_{i < k, x_i = 1} (-1)^{ω(p, g_i)}`. -/
lemma pauliApply_applyProd_comm {n : ℕ} (p : PauliIdx n) (g : Fin n → PauliIdx n) (x : F2 n)
    (k : ℕ) (hk : k ≤ n) (w : QState n) :
    pauliApply p (applyProd g x k hk w) =
      (∏ i : Fin k, if x ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ = 0 then (1 : ℂ)
        else (sympSign p (g ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩) : ℂ)) •
      applyProd g x k hk (pauliApply p w) := by
  induction k with
  | zero => simp [applyProd]
  | succ m ih =>
    simp only [applyProd, Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    by_cases hx : x ⟨m, hk⟩ = 0
    · simp only [hx, ↓reduceIte, mul_one]
      exact ih (Nat.le_of_succ_le hk)
    · simp only [hx, ↓reduceIte]
      rw [pauliApply_comm p (g ⟨m, hk⟩), ih (Nat.le_of_succ_le hk), pauliApply_smul, smul_smul, mul_comm]

/-- For isotropic `g`, `applyProd g` is an additive group action: `applyProd g a (applyProd g x w) = applyProd g (x + a) w`! -/
lemma applyProd_applyProd {n : ℕ} {g : Fin n → PauliIdx n}
    (hcomm : ∀ i j, symp (g i) (g j) = 0) (a x : F2 n) (k : ℕ) (hk : k ≤ n) (w : QState n) :
    applyProd g a k hk (applyProd g x k hk w) = applyProd g (x + a) k hk w := by
  -- First show `pauliApply (g i)` commutes with `applyProd g y m`!
  have hcm : ∀ (i : Fin n) (y : F2 n) (m : ℕ) (hm : m ≤ n) (v : QState n),
      pauliApply (g i) (applyProd g y m hm v) = applyProd g y m hm (pauliApply (g i) v) := by
    intro i y m hm v
    rw [pauliApply_applyProd_comm]
    have hprod1 : (∏ j : Fin m, if y ⟨j.1, Nat.lt_of_lt_of_le j.2 hm⟩ = 0 then (1 : ℂ)
        else (sympSign (g i) (g ⟨j.1, Nat.lt_of_lt_of_le j.2 hm⟩) : ℂ)) = 1 :=
      Finset.prod_eq_one fun j _ => by split_ifs <;> simp [sympSign, hcomm]
    rw [hprod1, one_smul]
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [applyProd, Pi.add_apply]
    rcases zmod2_cases (a ⟨m, hk⟩) with ha | ha <;> rcases zmod2_cases (x ⟨m, hk⟩) with hx | hx
    · simp only [ha, hx, add_zero, ↓reduceIte]
      exact ih (Nat.le_of_succ_le hk)
    · simp only [ha, hx, add_zero, ↓reduceIte, show (1 : ZMod 2) ≠ 0 by decide]
      rw [← hcm ⟨m, hk⟩ a m (Nat.le_of_succ_le hk), ih (Nat.le_of_succ_le hk)]
    · simp only [ha, hx, zero_add, ↓reduceIte, show (1 : ZMod 2) ≠ 0 by decide]
      rw [ih (Nat.le_of_succ_le hk)]
    · simp only [ha, hx, ↓reduceIte, show (1 : ZMod 2) ≠ 0 by decide, show (1 : ZMod 2) + 1 = 0 by decide]
      rw [← hcm ⟨m, hk⟩ a m (Nat.le_of_succ_le hk), pauliApply_invol, ih (Nat.le_of_succ_le hk)]

/-- Iterated projector `∏_{j < k} (I + P_{f j}) / 2`. -/
noncomputable def projK {n : ℕ} (f : Fin n → PauliIdx n) : (k : ℕ) → k ≤ n → QState n → QState n
  | 0, _, w => w
  | k + 1, hk, w =>
      let prev := projK f k (Nat.le_of_succ_le hk) w
      (1 / 2 : ℂ) • (prev + pauliApply (f ⟨k, hk⟩) prev)

/-- `projK f k w = 2⁻ᵏ ∑_{u : Fin k → ZMod 2} applyProd f u_ext k w`. -/
lemma projK_eq_sum {n : ℕ} (f : Fin n → PauliIdx n) (k : ℕ) (hk : k ≤ n) (w : QState n) :
    projK f k hk w =
      ((1 / 2 : ℂ) ^ k) • ∑ u : F2 k,
        applyProd f (fun i => if h : i.1 < k then u ⟨i.1, h⟩ else 0) k hk w := by
  induction k with
  | zero =>
    simp only [projK, pow_zero, one_smul]
    have h0 : (Finset.univ : Finset (F2 0)) = {0} := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact funext fun i => Fin.elim0 i
    rw [h0, Finset.sum_singleton]; rfl
  | succ m ih =>
    simp only [projK, ih (Nat.le_of_succ_le hk), pow_succ, mul_comm ((1 / 2 : ℂ) ^ m)]
    rw [pauliApply_smul, ← smul_add, smul_smul]
    congr 1
    -- Split `u : F2 (m + 1)` by its last bit `t = u ⟨m, _⟩ ∈ {0, 1}`!
    let e : (F2 m × ZMod 2) ≃ F2 (m + 1) :=
      { toFun := fun ⟨u, t⟩ => Fin.snoc u t
        invFun := fun v => (fun i => v i.castSucc, v (Fin.last m))
        left_inv := fun ⟨u, t⟩ => by
          ext i
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun v => by
          ext j
          refine Fin.lastCases (by simp [Fin.snoc_last]) (fun i => by simp [Fin.snoc_castSucc]) j }
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hsplit : ∀ u : F2 m,
        (∑ t : ZMod 2, applyProd f (fun i => if h : i.1 < m + 1 then (e (u, t)) ⟨i.1, h⟩ else 0) (m + 1) hk w) =
        applyProd f (fun i => if h : i.1 < m then u ⟨i.1, h⟩ else 0) m (Nat.le_of_succ_le hk) w +
        pauliApply (f ⟨m, hk⟩) (applyProd f (fun i => if h : i.1 < m then u ⟨i.1, h⟩ else 0) m (Nat.le_of_succ_le hk) w) := by
      intro u
      rw [sum_zmod2]
      have hagree : ∀ (t : ZMod 2) (r : ℕ) (hr : r ≤ m),
          applyProd f (fun i => if h : i.1 < m + 1 then (Fin.snoc u t : F2 (m + 1)) ⟨i.1, h⟩ else 0) r (le_trans hr (Nat.le_of_succ_le hk)) w =
          applyProd f (fun i => if h : i.1 < m then u ⟨i.1, h⟩ else 0) r (le_trans hr (Nat.le_of_succ_le hk)) w := by
        intro t r hr
        induction r with
        | zero => rfl
        | succ r' ihr' =>
          have hlt : r' < m := hr
          have hlt1 : r' < m + 1 := Nat.lt_succ_of_lt hlt
          simp only [applyProd, hlt, hlt1, ↓reduceDIte]
          have hsn : (Fin.snoc u t : F2 (m + 1)) ⟨r', hlt1⟩ = u ⟨r', hlt⟩ := by
            have : (⟨r', hlt1⟩ : Fin (m + 1)) = (⟨r', hlt⟩ : Fin m).castSucc := rfl
            rw [this, Fin.snoc_castSucc]
          rw [hsn, ihr' (Nat.le_of_succ_le hr)]
      have hm_lt : m < m + 1 := Nat.lt_succ_self m
      have hsn0 : (Fin.snoc u (0 : ZMod 2) : F2 (m + 1)) ⟨m, hm_lt⟩ = 0 := by
        have : (⟨m, hm_lt⟩ : Fin (m + 1)) = Fin.last m := rfl
        rw [this, Fin.snoc_last]
      have hsn1 : (Fin.snoc u (1 : ZMod 2) : F2 (m + 1)) ⟨m, hm_lt⟩ = 1 := by
        have : (⟨m, hm_lt⟩ : Fin (m + 1)) = Fin.last m := rfl
        rw [this, Fin.snoc_last]
      simp only [e, Equiv.coe_fn_mk, applyProd, hm_lt, ↓reduceDIte, hsn0, hsn1,
        show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
      rw [hagree 0 m le_rfl, hagree 1 m le_rfl]
    simp_rw [hsplit, Finset.sum_add_distrib]
    congr 1
    -- Push `pauliApply` into the sum
    ext x
    simp [pauliApply, Finset.sum_apply, Finset.mul_sum]

/-- Every output of `projK f n` is a joint `+1` eigenstate of all `P_{f j}`. -/
lemma pauliApply_projK {n : ℕ} {f : Fin n → PauliIdx n}
    (hcomm : ∀ i j, symp (f i) (f j) = 0) (k : ℕ) (hk : k ≤ n) (j : Fin n) (hjk : j.1 < k) (w : QState n) :
    pauliApply (f j) (projK f k hk w) = projK f k hk w := by
  induction k with
  | zero => omega
  | succ m ih =>
    simp only [projK]
    by_cases hjm : j.1 = m
    · have hj_eq : j = ⟨m, hk⟩ := Fin.ext hjm
      rw [hj_eq, pauliApply_smul, pauliApply_add, pauliApply_invol, add_comm]
    · have hlt : j.1 < m := by omega
      rw [pauliApply_smul, pauliApply_add, pauliApply_comm (f j) (f ⟨m, hk⟩)]
      simp only [sympSign, hcomm, ↓reduceIte, Int.cast_one, one_smul]
      rw [ih (Nat.le_of_succ_le hk) hlt]

/-- Standard computational basis vector `|x₀⟩ : QState n`. -/
def stdBasis {n : ℕ} (x₀ : F2 n) : QState n :=
  fun x => if x = x₀ then 1 else 0

/-- Trace of any Pauli operator `P_p` is `2ⁿ` if `p = 0`, else `0`. -/
lemma trace_pauliApply {n : ℕ} (p : PauliIdx n) :
    ∑ x : F2 n, innerProd (stdBasis x) (pauliApply p (stdBasis x)) =
      if p = 0 then (2 : ℂ) ^ n else 0 := by
  have hdiag : ∀ x : F2 n, innerProd (stdBasis x) (pauliApply p (stdBasis x)) =
      if p.1 = 0 then (chi p.2 x : ℂ) else 0 := by
    intro x
    simp only [innerProd, stdBasis, pauliApply]
    have hterm : ∀ y : F2 n,
        star (if y = x then (1 : ℂ) else 0) * (pauliPh p * (chi p.2 y : ℂ) * (if y + p.1 = x then 1 else 0)) =
        if y = x then (if p.1 = 0 then (chi p.2 x : ℂ) else 0) else 0 := by
      intro y
      by_cases hy : y = x
      · subst hy
        have hiff : y + p.1 = y ↔ p.1 = 0 := by
          constructor
          · intro h; have := congr_arg (y + ·) h; simpa [f2_add_cancel_left, f2_add_self] using this
          · intro h; rw [h, add_zero]
        by_cases hp1 : p.1 = 0
        · simp [hp1, pauliPh, dot_zero_left]
        · have hne : y + p.1 ≠ y := fun hc => hp1 (hiff.mp hc)
          simp [hp1, hne]
      · simp [hy]
    simp_rw [hterm]
    simp
  simp_rw [hdiag]
  by_cases hp1 : p.1 = 0
  · simp only [hp1, ↓reduceIte]
    have hch : (∑ x : F2 n, (chi p.2 x : ℂ)) = ((∑ x : F2 n, chi x p.2 : ℤ) : ℂ) := by
      rw [Int.cast_sum]; refine Finset.sum_congr rfl fun x _ => by rw [chi_comm]
    rw [hch, sum_chi]
    by_cases hp2 : p.2 = 0
    · have hp0 : p = 0 := Prod.ext hp1 hp2
      simp [hp0]
    · have hpne : p ≠ 0 := fun hc => hp2 (congr_arg Prod.snd hc)
      simp [hp2, hpne]
  · have hpne : p ≠ 0 := fun hc => hp1 (congr_arg Prod.fst hc)
    simp [hp1, hpne]

/-- **Existence of Joint `+1` Eigenstate `v₀`** for any `n` linearly independent commuting Paulis. -/
lemma exists_joint_eigenstate {n : ℕ} {f : Fin n → PauliIdx n}
    (hcomm : ∀ i j, symp (f i) (f j) = 0) (hli : LinearIndependent (ZMod 2) f) :
    ∃ v₀ : QState n, IsUnitState v₀ ∧ ∀ j : Fin n, pauliApply (f j) v₀ = v₀ := by
  -- Compute trace of `projK f n`: it equals `1 ≠ 0`!
  have htr : ∑ x : F2 n, innerProd (stdBasis x) (projK f n le_rfl (stdBasis x)) = 1 := by
    simp_rw [projK_eq_sum f n le_rfl, innerProd_smul_right, innerProd_sum_right, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ u : F2 n,
        (∑ x : F2 n, innerProd (stdBasis x) (applyProd f (fun i => if h : i.1 < n then u ⟨i.1, h⟩ else 0) n le_rfl (stdBasis x))) =
        if u = 0 then (2 : ℂ) ^ n else 0 := by
      intro u
      have hu_eq : (fun i : Fin n => if h : i.1 < n then u ⟨i.1, h⟩ else 0) = u := by
        ext i; simp [i.2]
      rw [hu_eq]
      by_cases hu0 : u = 0
      · subst hu0
        simp only [applyProd_zero, ↓reduceIte]
        have h1 : ∀ x : F2 n, innerProd (stdBasis x) (stdBasis x) = 1 := fun x => by
          simp only [innerProd, stdBasis]
          have : ∀ y : F2 n, star (if y = x then (1 : ℂ) else 0) * (if y = x then 1 else 0) =
              if y = x then 1 else 0 := fun y => by split_ifs <;> simp
          simp_rw [this]; simp
        simp_rw [h1]
        simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_pi, ZMod.card]
      · simp only [hu0, ↓reduceIte]
        obtain ⟨c, _, heq⟩ := applyProd_eq_phase_pauli f u n le_rfl
        simp_rw [heq, innerProd_smul_right, ← Finset.mul_sum, trace_pauliApply]
        have hlin_ne : linComb f u n le_rfl ≠ 0 := by
          rw [linComb_eq_sum]
          intro hc
          have h0 := Fintype.linearIndependent_iff.mp hli u (by simpa using hc)
          exact hu0 (funext h0)
        simp [hlin_ne]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq' Finset.univ (0 : F2 n)]
    simp only [Finset.mem_univ, ↓reduceIte, one_div, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))
  -- Therefore `∃ x₀, projK f n (stdBasis x₀) ≠ 0`!
  have hex : ∃ x₀ : F2 n, projK f n le_rfl (stdBasis x₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz : ∑ x : F2 n, innerProd (stdBasis x) (projK f n le_rfl (stdBasis x)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => by rw [hall x]; simp [innerProd]
    rw [hz] at htr
    exact zero_ne_one htr
  obtain ⟨x₀, hx₀⟩ := hex
  let w : QState n := projK f n le_rfl (stdBasis x₀)
  have hw_pos : 0 < (innerProd w w).re := by
    have hnn := innerProd_self_re_nonneg w
    have hne : (innerProd w w).re ≠ 0 := by
      intro h0
      apply hx₀
      rw [← innerProd_self_eq_zero_iff]
      rw [innerProd_self_eq_sum_normSq]
      rw [innerProd_self_re] at h0
      rw [h0, Complex.ofReal_zero]
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  let r : ℝ := Real.sqrt (innerProd w w).re
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hw_pos
  let v₀ : QState n := ((1 / r : ℝ) : ℂ) • w
  refine ⟨v₀, ?_, fun j => ?_⟩
  · -- `IsUnitState v₀`
    simp only [IsUnitState, v₀, innerProd_smul_left, innerProd_smul_right, Complex.star_def,
      Complex.conj_ofReal]
    rw [innerProd_self_eq_sum_normSq, ← innerProd_self_re]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have hval : 1 / r * (1 / r) * (innerProd w w).re = 1 := by
      have hsq : r * r = (innerProd w w).re := Real.mul_self_sqrt (le_of_lt hw_pos)
      field_simp [ne_of_gt hr_pos]; linarith
    rw [hval, Complex.ofReal_one]
  · -- `pauliApply (f j) v₀ = v₀`
    simp only [v₀, pauliApply_smul]
    congr 1
    exact pauliApply_projK hcomm n le_rfl j j.2 (stdBasis x₀)

/-- **THEOREM 2 (Unrestricted Non-Existence of Pauli-Covariant MUB Fiducials, All `n ≥ 3`)**:
    For every `n ≥ 3`, NO unit vector `|ψ⟩ ∈ (ℂ²)^⊗n` generates `2ⁿ` pairwise mutually unbiased
    orthonormal bases under the `n`-qubit Pauli group `𝒫ₙ`. -/
theorem no_pauli_mub_fiducial (n : ℕ) (hn : 3 ≤ n) (ψ : QState n) :
    ¬ IsPauliMubFiducial n ψ := by
  intro hmub
  -- Step 1: Extract Lagrangian zero subgroup `H`
  obtain ⟨H, hfinH, hlag, hH_zero, hH_out⟩ := mub_zero_lagrangian hmub
  -- Step 2: Construct symplectic basis `(f, e)` for `H`
  obtain ⟨f, e, hf_mem, hf_li, hff, hee, hef⟩ := exists_symplectic_basis H hfinH hlag
  -- Step 3: Construct joint `+1` eigenstate `v₀` of `{P_{f j}}`
  obtain ⟨v₀, hv₀_unit, hv₀_eig⟩ := exists_joint_eigenstate hff hf_li
  -- Step 4: Build orthonormal basis `v x := applyProd e x n v₀`
  let v : F2 n → QState n := fun x => applyProd e x n le_rfl v₀
  have hv_feig : ∀ (j : Fin n) (x : F2 n),
      pauliApply (f j) (v x) = (if x j = 0 then (1 : ℂ) else -1) • v x := by
    intro j x
    simp only [v]
    rw [pauliApply_applyProd_comm, hv₀_eig j]
    congr 1
    have hterm : ∀ i : Fin n,
        (if x i = 0 then (1 : ℂ) else (sympSign (f j) (e i) : ℂ)) =
        if i = j then (if x j = 0 then (1 : ℂ) else -1) else 1 := fun i => by
      by_cases hij : i = j
      · subst hij
        have hs : symp (f i) (e i) = 1 := by rw [symp_comm, hef i i]; simp
        simp [sympSign, hs]
      · have hs : symp (f j) (e i) = 0 := by rw [symp_comm, hef i j]; simp [hij]
        simp [hij, sympSign, hs]
    have hprod : (∏ i : Fin n, if x ⟨i.1, i.2⟩ = 0 then (1 : ℂ)
        else (sympSign (f j) (e ⟨i.1, i.2⟩) : ℂ)) =
        ∏ i : Fin n, if i = j then (if x j = 0 then (1 : ℂ) else -1) else 1 :=
      Finset.prod_congr rfl fun i _ => hterm i
    rw [hprod, Finset.prod_ite_eq']
    simp
  have hv_Fprod : ∀ (b x : F2 n),
      applyProd f b n le_rfl (v x) = (chi b x : ℂ) • v x := by
    intro b x
    have haux : ∀ (k : ℕ) (hk : k ≤ n),
        applyProd f b k hk (v x) =
        (∏ i : Fin k, if b ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ = 0 then (1 : ℂ)
          else (if x ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ = 0 then 1 else -1)) • v x := by
      intro k hk
      induction k with
      | zero => simp [applyProd]
      | succ m ih =>
        simp only [applyProd, Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        by_cases hb : b ⟨m, hk⟩ = 0
        · simp only [hb, ↓reduceIte, mul_one]
          exact ih (Nat.le_of_succ_le hk)
        · simp only [hb, ↓reduceIte]
          rw [ih (Nat.le_of_succ_le hk), pauliApply_smul, hv_feig, smul_smul, mul_comm]
    rw [haux n le_rfl]
    congr 1
    have hchi_prod : (chi b x : ℂ) = ∏ i : Fin n,
        if b i = 0 then (1 : ℂ) else (if x i = 0 then 1 else -1) := by
      have hchi_int : (chi b x : ℤ) = ∏ i : Fin n,
          if b i = 0 then (1 : ℤ) else (if x i = 0 then 1 else -1) := by
        have h1 : ∀ (S : Finset (Fin n)),
            (if (∑ i ∈ S, b i * x i) = 0 then (1 : ℤ) else -1) =
            ∏ i ∈ S, if b i = 0 then (1 : ℤ) else (if x i = 0 then 1 else -1) := by
          intro S
          induction S using Finset.cons_induction with
          | empty => simp
          | cons a t ha iht =>
            rw [Finset.sum_cons, Finset.prod_cons, ← iht]
            rcases zmod2_cases (b a) with hba | hba <;>
              rcases zmod2_cases (x a) with hxa | hxa <;>
              rcases zmod2_cases (∑ i ∈ t, b i * x i) with hs | hs
            all_goals simp [hba, hxa, hs, show (1 : ZMod 2) + 1 = 0 by decide,
              show (1 : ZMod 2) ≠ 0 by decide]
        exact h1 Finset.univ
      rw [hchi_int, Int.cast_prod]
      refine Finset.prod_congr rfl fun i _ => by split_ifs <;> simp
    exact hchi_prod.symm
  have hv_ortho : ∀ x y : F2 n, innerProd (v x) (v y) = if x = y then 1 else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, v]
      rw [innerProd_applyProd_both]
      exact hv₀_unit
    · simp only [hxy, ↓reduceIte]
      have hex : ∃ j : Fin n, x j ≠ y j := by
        by_contra hall; push Not at hall; exact hxy (funext hall)
      obtain ⟨j, hj⟩ := hex
      have hEq : innerProd (v x) (v y) = -innerProd (v x) (v y) := by
        calc innerProd (v x) (v y)
            = innerProd (pauliApply (f j) (v x)) (pauliApply (f j) (v y)) :=
              (innerProd_pauliApply_both (f j) (v x) (v y)).symm
          _ = star (if x j = 0 then (1 : ℂ) else -1) * (if y j = 0 then (1 : ℂ) else -1) *
              innerProd (v x) (v y) := by
              rw [hv_feig j x, hv_feig j y, innerProd_smul_left, innerProd_smul_right]; ring
          _ = -innerProd (v x) (v y) := by
              rcases zmod2_cases (x j) with hx | hx <;> rcases zmod2_cases (y j) with hy | hy
              · exact absurd (hx.trans hy.symm) hj
              · simp [hx, hy]
              · simp [hx, hy]
              · exact absurd (hx.trans hy.symm) hj
      have h2 : (2 : ℂ) * innerProd (v x) (v y) = 0 := by linear_combination hEq
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  -- Orthonormal basis expansion: `∀ w : QState n, w = ∑ x, innerProd (v x) w • v x`!
  have hv_li : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc x
    have h0 := congr_arg (innerProd (v x)) hc
    simp only [innerProd_sum_right, innerProd_smul_right, hv_ortho, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h0
    have hzero : innerProd (v x) (0 : QState n) = 0 := by simp [innerProd]
    rw [hzero] at h0
    exact h0
  have hv_span : Submodule.span ℂ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv_li, Module.finrank_pi]
  have hv_expand : ∀ w : QState n, w = ∑ x : F2 n, innerProd (v x) w • v x := by
    intro w
    let r : QState n := w - ∑ x : F2 n, innerProd (v x) w • v x
    have hr_orth : ∀ y : F2 n, innerProd (v y) r = 0 := fun y => by
      simp only [r, innerProd_sub_right, innerProd_sum_right, innerProd_smul_right, hv_ortho,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self]
    have hr_mem : r ∈ Submodule.span ℂ (Set.range v) := by rw [hv_span]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hr_mem
    obtain ⟨c, hc⟩ := hr_mem
    have hrr : innerProd r r = 0 := by
      conv_lhs => arg 1; rw [← hc]
      rw [innerProd_sum_left]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [innerProd_smul_left, hr_orth y, mul_zero]
    have hr0 : r = 0 := (innerProd_self_eq_zero_iff r).mp hrr
    exact sub_eq_zero.mp hr0
  have hv_parseval : ∀ u w : QState n,
      innerProd u w = ∑ x : F2 n, star (innerProd (v x) u) * innerProd (v x) w := by
    intro u w
    conv_lhs => rw [hv_expand u]
    rw [innerProd_sum_left]
    refine Finset.sum_congr rfl fun x _ => by rw [innerProd_smul_left]
  -- Step 5: Compute `⟨ψ | F_b E_a ψ⟩ = ∑_x (-1)^{b·x} conj(⟨v_x|ψ⟩) ⟨v_{x+a}|ψ⟩`!
  let α : F2 n → ℂ := fun x => innerProd (v x) ψ
  have hFE_eval : ∀ a b : F2 n,
      ∃ c : ℂ, Complex.normSq c = 1 ∧
        c * innerProd ψ (pauliApply (linComb e a n le_rfl + linComb f b n le_rfl) ψ) =
          ∑ x : F2 n, (chi b x : ℂ) * star (α x) * α (x + a) := by
    intro a b
    obtain ⟨ca, hca, hea⟩ := applyProd_eq_phase_pauli e a n le_rfl
    obtain ⟨cb, hcb, hfb⟩ := applyProd_eq_phase_pauli f b n le_rfl
    let q_ab := linComb f b n le_rfl
    let p_ab := linComb e a n le_rfl
    refine ⟨cb * ca * pauliPhase q_ab p_ab, ?_, ?_⟩
    · simp only [map_mul, hcb, hca, pauliPhase_normSq, mul_one]
    · have hlhs : innerProd ψ (applyProd f b n le_rfl (applyProd e a n le_rfl ψ)) =
          cb * ca * pauliPhase q_ab p_ab *
            innerProd ψ (pauliApply (p_ab + q_ab) ψ) := by
        rw [hea ψ, applyProd_smul, hfb _, innerProd_smul_right, innerProd_smul_right,
          pauliApply_comp, innerProd_smul_right, add_comm q_ab p_ab]
        ring
      rw [← hlhs, hv_parseval ψ (applyProd f b n le_rfl (applyProd e a n le_rfl ψ))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [innerProd_applyProd_right hff, hv_Fprod, innerProd_smul_left,
        innerProd_applyProd_right hee]
      have hv_shift : applyProd e a n le_rfl (v x) = v (x + a) := by
        simp only [v]; exact applyProd_applyProd hee a x n le_rfl v₀
      rw [hv_shift]
      have hc_star : star (chi b x : ℂ) = (chi b x : ℂ) := by simp
      rw [hc_star]; simp only [α]; ring
  -- Step 6: Extract equimodularity (`|α x|² = 2⁻ⁿ`) from `a = 0`!
  have hα_norm : ∀ x : F2 n, Complex.normSq (α x) = 1 / (2 : ℝ) ^ n := by
    have hsum_b : ∀ b : F2 n,
        ∑ x : F2 n, (chi b x : ℂ) * (Complex.normSq (α x) : ℂ) = if b = 0 then 1 else 0 := by
      intro b
      by_cases hb : b = 0
      · subst hb
        simp only [↓reduceIte]
        have h1 : ∀ x : F2 n, (chi 0 x : ℂ) * (Complex.normSq (α x) : ℂ) =
            star (α x) * α x := fun x => by
          rw [chi_zero_left, Int.cast_one, one_mul, mul_comm, Complex.star_def, Complex.mul_conj]
        simp_rw [h1]
        rw [← hv_parseval ψ ψ]
        exact hmub.1
      · simp only [hb, ↓reduceIte]
        obtain ⟨c, _, heq⟩ := hFE_eval 0 b
        have hsum_eq : (∑ x : F2 n, (chi b x : ℂ) * (Complex.normSq (α x) : ℂ)) =
            ∑ x : F2 n, (chi b x : ℂ) * star (α x) * α (x + 0) := by
          refine Finset.sum_congr rfl fun x _ => by
            rw [add_zero, mul_assoc, mul_comm (star (α x)), Complex.star_def, Complex.mul_conj]
        rw [hsum_eq, ← heq]
        have hlin0 : linComb e 0 n le_rfl = 0 := by rw [linComb_eq_sum]; simp
        rw [hlin0, zero_add]
        have hmemH : linComb f b n le_rfl ∈ H := by
          rw [linComb_eq_sum]
          exact Submodule.sum_mem H fun i _ => Submodule.smul_mem H _ (hf_mem _)
        have hne0 : linComb f b n le_rfl ≠ 0 := by
          rw [linComb_eq_sum]
          intro h0
          exact hb (funext (Fintype.linearIndependent_iff.mp hf_li b (by simpa using h0)))
        rw [hH_zero _ hmemH hne0, mul_zero]
    intro x
    have hinv := wht_inversion (R := ℂ) (fun y => (Complex.normSq (α y) : ℂ)) x
    simp_rw [hsum_b] at hinv
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      chi_zero_left, Int.cast_one] at hinv
    have hre := congr_arg Complex.re hinv
    have hrhs : ((2 : ℂ) ^ n * (Complex.normSq (α x) : ℂ)).re = (2 : ℝ) ^ n * Complex.normSq (α x) := by
      rw [show (2 : ℂ) ^ n = (((2 : ℝ) ^ n : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hrhs, Complex.one_re] at hre
    have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    rw [eq_div_iff h2n_ne, mul_comm]; exact hre.symm
  -- Step 7: Define `φ x := √(2ⁿ) * α x` and verify `IsAlltop n φ`!
  let s2n : ℝ := Real.sqrt ((2 : ℝ) ^ n)
  have hs2n_sq : s2n ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  let φ : F2 n → ℂ := fun x => (s2n : ℂ) * α x
  have halltop : IsAlltop n φ := by
    refine ⟨fun x => ?_, fun a ha b => ?_⟩
    · simp only [φ, map_mul, Complex.normSq_ofReal, hα_norm x, ← sq, hs2n_sq]
      field_simp [show (2 : ℝ) ^ n ≠ 0 by positivity]
    · obtain ⟨c, hc, heq⟩ := hFE_eval a b
      have hfactor : ∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a) =
          (((2 : ℝ) ^ n : ℝ) : ℂ) * ∑ x : F2 n, (chi b x : ℂ) * star (α x) * α (x + a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hs2n_star : star (s2n : ℂ) = (s2n : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
        simp only [φ, star_mul, hs2n_star]
        have hsqC : (s2n : ℂ) * (s2n : ℂ) = (((2 : ℝ) ^ n : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← sq, hs2n_sq]
        calc (chi b x : ℂ) * (star (α x) * (s2n : ℂ)) * ((s2n : ℂ) * α (x + a))
            = ((s2n : ℂ) * (s2n : ℂ)) * ((chi b x : ℂ) * star (α x) * α (x + a)) := by ring
          _ = _ := by rw [hsqC]
      -- Show `linComb e a n + linComb f b n ∉ H` because `a ≠ 0`!
      have hnotH : linComb e a n le_rfl + linComb f b n le_rfl ∉ H := by
        intro hmem
        have hex : ∃ k : Fin n, a k ≠ 0 := by
          by_contra hall; push Not at hall; exact ha (funext hall)
        obtain ⟨k, hk⟩ := hex
        have hmem_orth : linComb e a n le_rfl + linComb f b n le_rfl ∈ sympOrth H := by
          rw [hlag]; exact hmem
        have h0 := hmem_orth (f k) (hf_mem k)
        rw [symp_add_left, linComb_eq_sum, linComb_eq_sum, symp_sum_left, symp_sum_left] at h0
        have hf0 : ∑ i : Fin n, symp (b i • f i) (f k) = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [symp_smul_left, hff i k, mul_zero]
        have he_val : ∑ i : Fin n, symp (a i • e i) (f k) = a k := by
          have ht : ∀ i : Fin n, symp (a i • e i) (f k) = if i = k then a i else 0 := fun i => by
            rw [symp_smul_left, hef i k]; split_ifs <;> simp
          simp_rw [ht, Finset.sum_ite_eq']
          simp
        rw [hf0, add_zero, he_val] at h0
        exact hk h0
      rw [hfactor, ← heq, map_mul, map_mul, Complex.normSq_ofReal, hc, one_mul, hH_out _ hnotH]
      field_simp [show (2 : ℝ) ^ n ≠ 0 by positivity]
  -- Step 8: Contradiction with Theorem 1 (`no_alltop_f2`)!
  exact no_alltop_f2 n hn φ halltop

/-! ### Corollary (Damski–Bistroń–Ponterio–Czartowski–Życzkowski Conjecture 1) & Sharpness (`n = 2`) -/

/-- Primitive 8th root of unity `ω₈ = (1 + i)/√2`. -/
noncomputable def omega8 : ℂ :=
  ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I

lemma omega8_pow_eight : omega8 ^ 8 = 1 := by
  have hsq : omega8 ^ 2 = Complex.I := by
    simp only [omega8]
    apply Complex.ext
    · simp [sq]
    · simp [sq]
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      linarith
  calc omega8 ^ 8 = (omega8 ^ 2) ^ 4 := by ring
    _ = Complex.I ^ 4 := by rw [hsq]
    _ = 1 := by norm_num

/-- **Corollary (Resolution of Conjecture 1 of `arXiv:2603.15550` for ALL `n ≥ 3`)**:
    No `ω₈`-phase state `ψ_x = 2^(-n/2) ω₈^{m_x}` generates `2ⁿ` Pauli-covariant MUBs for `n ≥ 3`. -/
theorem damski_conjecture_1 (n : ℕ) (hn : 3 ≤ n) (m : F2 n → ℕ) :
    ¬ IsPauliMubFiducial n (fun x => (((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * omega8 ^ (m x))) :=
  no_pauli_mub_fiducial n hn _

/-- **Sharpness (`n = 2` EXISTS!)**: `|ψ₂⟩ = (1/2)(1, 1, 1, i)` IS a 2-qubit Pauli-covariant MUB fiducial! -/
theorem exists_pauli_mub_fiducial_two : ∃ ψ : QState 2, IsPauliMubFiducial 2 ψ := by
  let ψ : QState 2 := fun x => (1 / 2 : ℂ) * alltopTwo x
  refine ⟨ψ, ?_, ?_⟩
  · -- `IsUnitState ψ`
    rw [IsUnitState, innerProd_self_eq_sum_normSq]
    have hterm : ∀ x : F2 2, Complex.normSq (ψ x) = 1 / 4 := fun x => by
      simp only [ψ, map_mul, exists_alltop_two.1 x, mul_one]
      norm_num [Complex.normSq_apply]
    simp_rw [hterm]
    simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_pi, ZMod.card]
  · -- Partition Pauli operators by their X-part `p.1 ∈ 𝔽₂²` into 4 pairwise MUBs!
    let basisIdx : PauliIdx 2 → Fin (2 ^ 2) := fun p =>
      ⟨(if p.1 0 = 0 then 0 else 2) + (if p.1 1 = 0 then 0 else 1), by split_ifs <;> omega⟩
    have hidx_eq : ∀ p q : PauliIdx 2, basisIdx p = basisIdx q ↔ p.1 = q.1 := by
      intro p q
      constructor
      · intro h
        have hv := congr_arg Fin.val h
        simp only [basisIdx] at hv
        ext i
        have hp0 := zmod2_cases (p.1 0); have hp1 := zmod2_cases (p.1 1)
        have hq0 := zmod2_cases (q.1 0); have hq1 := zmod2_cases (q.1 1)
        fin_cases i
        · rcases hp0 with hp0 | hp0 <;> rcases hp1 with hp1 | hp1 <;>
            rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
            simp [hp0, hp1, hq0, hq1] at hv ⊢
        · rcases hp0 with hp0 | hp0 <;> rcases hp1 with hp1 | hp1 <;>
            rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
            simp [hp0, hp1, hq0, hq1] at hv ⊢
      · intro h; apply Fin.ext; simp [basisIdx, h]
    refine ⟨basisIdx, fun p q heq hne => ?_, fun p q hneq => ?_⟩
    · -- Same X-part (`p.1 = q.1`), different Z-part (`p.2 ≠ q.2`) ⇒ orthogonal!
      have hpq1 : p.1 = q.1 := (hidx_eq p q).mp heq
      have hpq2 : p.2 ≠ q.2 := fun h2 => hne (Prod.ext hpq1 h2)
      have hsum1 : (p + q).1 = 0 := by simp [hpq1, f2_add_self]
      have hsum2 : (p + q).2 ≠ 0 := by
        intro hc
        have := congr_arg (p.2 + ·) hc
        rw [Prod.snd_add, f2_add_cancel_left, add_zero] at this
        exact hpq2 this.symm
      rw [← innerProd_pauliApply_right, pauliApply_comp, innerProd_smul_right]
      have hz : innerProd ψ (pauliApply (p + q) ψ) = 0 := by
        simp only [innerProd, pauliApply, hsum1, add_zero, pauliPh, dot_zero_left, ↓reduceIte, one_mul]
        have hterm : ∀ x : F2 2,
            star (ψ x) * ((chi (p + q).2 x : ℂ) * ψ x) = (1 / 4 : ℂ) * (chi x (p + q).2 : ℂ) := fun x => by
          have h1 : star (ψ x) * ψ x = 1 / 4 := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj]
            simp only [ψ, map_mul, exists_alltop_two.1 x, mul_one]
            norm_num [Complex.normSq_apply]
          calc star (ψ x) * ((chi (p + q).2 x : ℂ) * ψ x)
              = (star (ψ x) * ψ x) * (chi (p + q).2 x : ℂ) := by ring
            _ = (1 / 4 : ℂ) * (chi x (p + q).2 : ℂ) := by rw [h1, chi_comm]
        simp_rw [hterm, ← Finset.mul_sum, ← Int.cast_sum, sum_chi]
        simp only [hsum2, ↓reduceIte, Int.cast_zero, mul_zero]
      rw [hz, mul_zero]
    · -- Different X-part (`p.1 ≠ q.1`) ⇒ mutually unbiased (`|⟨P_p ψ | P_q ψ⟩|² = 1/4`)!
      have hpq1 : p.1 ≠ q.1 := fun h1 => hneq ((hidx_eq p q).mpr h1)
      have hsum1 : (p + q).1 ≠ 0 := by
        intro hc
        have := congr_arg (p.1 + ·) hc
        rw [Prod.fst_add, f2_add_cancel_left, add_zero] at this
        exact hpq1 this.symm
      rw [← innerProd_pauliApply_right, pauliApply_comp, innerProd_smul_right, map_mul,
        pauliPhase_normSq, one_mul]
      have hcalc : innerProd ψ (pauliApply (p + q) ψ) =
          (1 / 4 : ℂ) * pauliPh (p + q) *
            ∑ x : F2 2, (chi (p + q).2 x : ℂ) * star (alltopTwo x) * alltopTwo (x + (p + q).1) := by
        simp only [innerProd, pauliApply, ψ, star_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hhalf : star (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 := by norm_num
        calc star (alltopTwo x) * star (1 / 2 : ℂ) *
              (pauliPh (p + q) * (chi (p + q).2 x : ℂ) * ((1 / 2 : ℂ) * alltopTwo (x + (p + q).1)))
            = (star (1 / 2 : ℂ) * (1 / 2 : ℂ)) * pauliPh (p + q) *
                ((chi (p + q).2 x : ℂ) * star (alltopTwo x) * alltopTwo (x + (p + q).1)) := by ring
          _ = _ := by rw [hhalf]
      rw [hcalc, map_mul, map_mul, pauliPh_normSq, mul_one, exists_alltop_two.2 (p + q).1 hsum1 (p + q).2]
      norm_num [Complex.normSq_apply]

end MultiQubitMUB
