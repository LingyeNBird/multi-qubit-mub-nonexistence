module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt

import MultiQubitMUB

/-!
# Solution: Non-Existence of Multi-Qubit Pauli-Covariant MUB Fiducials and Alltop Phase Functions on `𝔽₂ⁿ` (`n ≥ 3`)

This module pairs with `Challenge.lean` for Palomar Registry / `lake comparator` verification.
Its public imports and public definitions reproduce `Challenge.lean` verbatim (ensuring identical
kernel elaboration), while the private import `MultiQubitMUB` supplies the pure-kernel proofs of
all 10 compared headline theorems.
-/

@[expose] public section

namespace MultiQubitMUB.Challenge

open scoped Classical

/-- Binary vector space `𝔽₂ⁿ = Fin n → ZMod 2`. -/
abbrev F2 (n : ℕ) := Fin n → ZMod 2

/-- Standard bilinear dot product on `𝔽₂ⁿ`. -/
def dot {n : ℕ} (x y : F2 n) : ZMod 2 := ∑ i : Fin n, x i * y i

/-- Integer sign character `(-1)^(x · y) ∈ {-1, 1}`. -/
def chi {n : ℕ} (x y : F2 n) : ℤ := if dot x y = 0 then 1 else -1

/-- Unimodular Alltop function on `𝔽₂ⁿ`: `|φ(x)| = 1` and `|WHT(g_a)(b)|² = 2ⁿ` for all
    `a ≠ 0` and `b ∈ 𝔽₂ⁿ`, where `g_a(x) = conj(φ x) * φ(x + a)`. -/
def IsAlltop (n : ℕ) (φ : F2 n → ℂ) : Prop :=
  (∀ x : F2 n, Complex.normSq (φ x) = 1) ∧
  (∀ a : F2 n, a ≠ 0 → ∀ b : F2 n,
    Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) = (2 : ℝ) ^ n)

/-- Explicit 2-bit Alltop phase function `φ₂(x₀, x₁) = i^(x₀ x₁)` (`(1, 1, 1, i)`). -/
def alltopTwo : F2 2 → ℂ := fun x =>
  if x 0 = 1 ∧ x 1 = 1 then Complex.I else 1

/-- Phase-state Pauli 4th moment `F_n(φ) = ∑_{a,b} |2⁻ⁿ ∑_x (-1)^(b·x) conj(φ x) φ(x + a)|⁴`
    (equivalently `2ⁿ ‖φ‖_{U³(𝔽₂ⁿ)}⁸`). -/
noncomputable def phasePauliMoment4 (n : ℕ) (φ : F2 n → ℂ) : ℝ :=
  ∑ a : F2 n, ∑ b : F2 n,
    (Complex.normSq (∑ x : F2 n, (chi b x : ℂ) * star (φ x) * φ (x + a)) / ((2 : ℝ) ^ n) ^ 2) ^ 2

/-- `n`-qubit pure state vector `|ψ⟩ ∈ (ℂ²)^⊗n`, represented as `F2 n → ℂ`. -/
abbrev QState (n : ℕ) := F2 n → ℂ

/-- Hermitian inner product `⟨ψ | φ⟩ = ∑_x conj(ψ x) * φ x`. -/
def innerProd {n : ℕ} (ψ φ : QState n) : ℂ :=
  ∑ x : F2 n, star (ψ x) * φ x

/-- Unit-norm state condition `⟨ψ | ψ⟩ = 1`. -/
def IsUnitState {n : ℕ} (ψ : QState n) : Prop :=
  innerProd ψ ψ = 1

/-- Phase-space index `(a, b) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ` labeling the Hermitian Pauli `P_{(a,b)} = i^(a·b) Z^b X^a`. -/
abbrev PauliIdx (n : ℕ) := F2 n × F2 n

/-- Phase factor `i^{a·b}` ensuring `P_{(a,b)} = i^{a·b} Z^b X^a` is Hermitian and involutive. -/
def pauliPh {n : ℕ} (p : PauliIdx n) : ℂ :=
  if dot p.1 p.2 = 0 then 1 else Complex.I

/-- Action of the Hermitian involutive Pauli operator `P_{(a,b)}` on `ψ : QState n`. -/
def pauliApply {n : ℕ} (p : PauliIdx n) (ψ : QState n) : QState n :=
  fun x => pauliPh p * (chi p.2 x : ℂ) * ψ (x + p.1)

/-- `n`-qubit Pauli-covariant (product Weyl–Heisenberg) MUB fiducial state: a unit vector
    `|ψ⟩ ∈ (ℂ²)^⊗n` whose Pauli orbit `{P_p |ψ⟩}` partitions into `2ⁿ` pairwise mutually
    unbiased orthonormal bases. -/
def IsPauliMubFiducial (n : ℕ) (ψ : QState n) : Prop :=
  IsUnitState ψ ∧
  ∃ (basisIdx : PauliIdx n → Fin (2 ^ n)),
    (∀ p q : PauliIdx n, basisIdx p = basisIdx q → p ≠ q →
      innerProd (pauliApply p ψ) (pauliApply q ψ) = 0) ∧
    (∀ p q : PauliIdx n, basisIdx p ≠ basisIdx q →
      Complex.normSq (innerProd (pauliApply p ψ) (pauliApply q ψ)) = 1 / (2 : ℝ) ^ n)

/-- Primitive 8th root of unity `ω₈ = (1 + i) / √2`. -/
noncomputable def omega8 : ℂ :=
  ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I

/-- Pauli 4th moment `F_n(ψ) = ∑_{p ∈ 𝔽₂²ⁿ} |⟨ψ | P_p | ψ⟩|⁴` of an `n`-qubit state `ψ`. -/
noncomputable def pauliMoment4 (n : ℕ) (ψ : QState n) : ℝ :=
  ∑ p : PauliIdx n, (Complex.normSq (innerProd ψ (pauliApply p ψ))) ^ 2

/-- Closed-form Pauli 4th moment polynomial of the `GL(n, 𝔽₂)`-invariant, `(H^⊗n ∘ K)`-symmetric
    spike+uniform family. -/
noncomputable def spikeMomentPoly (n : ℕ) (s : ℝ) : ℝ :=
  let d : ℝ := (2 : ℝ) ^ n
  1 + (d - 1) * (2 * (1 - s) ^ 4 + (d / 2 - 1) * (1 - 2 * s) ^ 4 +
    (d / 2) * (-1 + 4 * s - (4 * (d - 1) / d) * s ^ 2) ^ 2)

/-- The explicit `GL(n, 𝔽₂)`-invariant, `(H^⊗n ∘ K)`-symmetric state
    `|ψ_n(s)⟩ = α |0⟩ + β ∑_{x ≠ 0} |x⟩`. -/
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

/-- **Theorem 1**: No unimodular Alltop phase function exists on `𝔽₂ⁿ` for any `n ≥ 3`. -/
theorem no_alltop_f2 (n : ℕ) (hn : 3 ≤ n) (φ : F2 n → ℂ) : ¬ IsAlltop n φ := by
  exact _root_.MultiQubitMUB.no_alltop_f2 n hn φ

/-- Sharpness at `n = 2`: `φ₂ = (1, 1, 1, i)` is an Alltop function on `𝔽₂²`. -/
theorem exists_alltop_two : IsAlltop 2 alltopTwo := by
  exact _root_.MultiQubitMUB.exists_alltop_two

/-- Strict Gowers `U³` / phase-state Pauli 4th-moment lower bound for all `n ≥ 3`. -/
theorem phasePauliMoment4_gt_mub (n : ℕ) (hn : 3 ≤ n) (φ : F2 n → ℂ)
    (hunit : ∀ x : F2 n, Complex.normSq (φ x) = 1) :
    2 - 1 / (2 : ℝ) ^ n < phasePauliMoment4 n φ := by
  exact _root_.MultiQubitMUB.phasePauliMoment4_gt_mub n hn φ hunit

/-- Strong odd-`n` obstruction (no basis partition assumed): for every odd `n = 2k + 1 ≥ 3`,
    no unit vector `|ψ⟩` satisfies `|⟨ψ|P|ψ⟩|² ∈ {0, 2⁻ⁿ}` for all `P ≠ I`. -/
theorem no_pauli_two_valued_odd (k : ℕ) (hk : 1 ≤ k) (ψ : QState (2 * k + 1))
    (hunit : IsUnitState ψ) :
    ¬ ∀ p : PauliIdx (2 * k + 1), p ≠ 0 →
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 0 ∨
        Complex.normSq (innerProd ψ (pauliApply p ψ)) = 1 / (2 : ℝ) ^ (2 * k + 1) := by
  exact _root_.MultiQubitMUB.no_pauli_two_valued_odd k hk ψ hunit

/-- **Theorem 2**: For every `n ≥ 3`, no unit vector `|ψ⟩ ∈ (ℂ²)^⊗n` is an `n`-qubit
    Pauli-covariant (product Weyl–Heisenberg) MUB fiducial state. -/
theorem no_pauli_mub_fiducial (n : ℕ) (hn : 3 ≤ n) (ψ : QState n) :
    ¬ IsPauliMubFiducial n ψ := by
  exact _root_.MultiQubitMUB.no_pauli_mub_fiducial n hn ψ

/-- Resolution of Conjecture 1 of Damski et al. (`arXiv:2603.15550`) for all `n ≥ 3`:
    no `ω₈`-phase state `ψ_x = 2^(-n/2) ω₈^{m_x}` is an `n`-qubit Pauli-covariant MUB fiducial. -/
theorem damski_conjecture_1 (n : ℕ) (hn : 3 ≤ n) (m : F2 n → ℕ) :
    ¬ IsPauliMubFiducial n
      (fun x : F2 n => ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) * omega8 ^ (m x)) := by
  exact _root_.MultiQubitMUB.damski_conjecture_1 n hn m

/-- Sharpness at `n = 2`: there exists a two-qubit Pauli-covariant MUB fiducial state. -/
theorem exists_pauli_mub_fiducial_two : ∃ ψ : QState 2, IsPauliMubFiducial 2 ψ := by
  exact _root_.MultiQubitMUB.exists_pauli_mub_fiducial_two

/-- Exact closed-form Pauli 4th moment for the `GL(n, 𝔽₂)`-invariant spike+uniform family (`n ≥ 1`). -/
theorem pauliMoment4_spikeState {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hf : SpikeFeasible n s) :
    pauliMoment4 n (spikeState n s) = spikeMomentPoly n s := by
  exact _root_.MultiQubitMUB.pauliMoment4_spikeState hn hf

/-- Exact recovery of the 3-qubit Hoggar SIC (`F₃ = 16 / 9`) at `n = 3, s = 2 / 3`. -/
theorem hoggar_sic_three :
    IsUnitState (spikeState 3 (2 / 3)) ∧
    pauliMoment4 3 (spikeState 3 (2 / 3)) = 16 / 9 := by
  exact _root_.MultiQubitMUB.hoggar_sic_three

/-- Certified 4-qubit unit pure state achieving `F₄ < 2.150521`. -/
theorem four_qubit_spike_bound :
    IsUnitState (spikeState 4 (622543 / 1000000)) ∧
    pauliMoment4 4 (spikeState 4 (622543 / 1000000)) < 2150521 / 1000000 := by
  exact _root_.MultiQubitMUB.four_qubit_spike_bound

end MultiQubitMUB.Challenge
