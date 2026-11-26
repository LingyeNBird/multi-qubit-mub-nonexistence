module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Binary Vector Space `𝔽₂ⁿ` and Walsh–Hadamard Transform

Provides foundational definitions and lemmas for `F2 n := Fin n → ZMod 2`:
- Standard inner product `dot x y : ZMod 2`.
- Real/integer/complex sign character `chi x y ∈ {-1, +1}` and its multiplicativity & orthogonality.
- Walsh–Hadamard Transform inversion over any ring (specialized to `ℂ`, `ℝ`, `ℤ`, `GaussianInt`).
- Affine subspace character sums and dimension/cardinality parity lemmas for orthogonal complements.
-/

@[expose] public section

namespace MultiQubitMUB

open scoped Classical

abbrev F2 (n : ℕ) := Fin n → ZMod 2

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ t : ZMod 2, f t = f 0 + f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext a; rcases zmod2_cases a with rfl | rfl <;> simp
  rw [h, Finset.sum_pair zero_ne_one]

/-- Standard bilinear dot product on `𝔽₂ⁿ`. -/
def dot {n : ℕ} (x y : F2 n) : ZMod 2 := ∑ i : Fin n, x i * y i

lemma dot_comm {n : ℕ} (x y : F2 n) : dot x y = dot y x := by
  simp only [dot, mul_comm]

lemma dot_add_left {n : ℕ} (x y z : F2 n) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (x y z : F2 n) : dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_zero_left {n : ℕ} (y : F2 n) : dot 0 y = 0 := by simp [dot]
lemma dot_zero_right {n : ℕ} (x : F2 n) : dot x 0 = 0 := by simp [dot]

lemma f2_add_self {n : ℕ} (x : F2 n) : x + x = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (x i) with h | h
  · simp [h]
  · simp [h]; decide

lemma f2_neg_eq {n : ℕ} (x : F2 n) : -x = x :=
  (eq_neg_of_add_eq_zero_left (f2_add_self x)).symm

lemma f2_sub_eq_add {n : ℕ} (x y : F2 n) : x - y = x + y := by
  rw [sub_eq_add_neg, f2_neg_eq]

lemma f2_add_cancel_right {n : ℕ} (x y : F2 n) : (x + y) + y = x := by
  rw [add_assoc, f2_add_self, add_zero]

lemma f2_add_cancel_left {n : ℕ} (x y : F2 n) : x + (x + y) = y := by
  rw [← add_assoc, f2_add_self, zero_add]

/-- Integer sign character `(-1)^(x · y) ∈ {-1, 1}`. -/
def chi {n : ℕ} (x y : F2 n) : ℤ := if dot x y = 0 then 1 else -1

lemma chi_comm {n : ℕ} (x y : F2 n) : chi x y = chi y x := by
  simp only [chi, dot_comm]

lemma chi_zero_left {n : ℕ} (y : F2 n) : chi 0 y = 1 := by
  simp [chi, dot_zero_left]

lemma chi_zero_right {n : ℕ} (x : F2 n) : chi x 0 = 1 := by
  simp [chi, dot_zero_right]

lemma chi_add_left {n : ℕ} (x y z : F2 n) : chi (x + y) z = chi x z * chi y z := by
  simp only [chi, dot_add_left]
  rcases zmod2_cases (dot x z) with h1 | h1 <;> rcases zmod2_cases (dot y z) with h2 | h2
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]; decide

lemma chi_add_right {n : ℕ} (x y z : F2 n) : chi x (y + z) = chi x y * chi x z := by
  rw [chi_comm, chi_add_left, chi_comm y, chi_comm z]

lemma chi_mul_self {n : ℕ} (x y : F2 n) : chi x y * chi x y = 1 := by
  simp only [chi]; split_ifs <;> norm_num

lemma chi_eq_one_or_neg_one {n : ℕ} (x y : F2 n) : chi x y = 1 ∨ chi x y = -1 := by
  simp only [chi]; split_ifs <;> simp

/-- Standard basis vector `e_i` in `𝔽₂ⁿ`. -/
def eVec {n : ℕ} (i : Fin n) : F2 n := Pi.single i 1

lemma dot_eVec_left {n : ℕ} (i : Fin n) (x : F2 n) : dot (eVec i) x = x i := by
  simp [dot, eVec, Pi.single_apply]

lemma dot_eVec_right {n : ℕ} (x : F2 n) (i : Fin n) : dot x (eVec i) = x i := by
  rw [dot_comm, dot_eVec_left]

/-- Character orthogonality on `𝔽₂ⁿ`: `∑ x, χ(x, y) = 2^n` if `y = 0`, else `0`. -/
lemma sum_chi {n : ℕ} (y : F2 n) :
    ∑ x : F2 n, chi x y = if y = 0 then (2 : ℤ) ^ n else 0 := by
  by_cases hy : y = 0
  · subst hy
    simp [chi_zero_right, Fintype.card_pi, ZMod.card]
  · simp only [hy, ↓reduceIte]
    have hex : ∃ i : Fin n, y i ≠ 0 := by
      by_contra h; push Not at h; exact hy (funext h)
    obtain ⟨i, hi⟩ := hex
    have hdot : dot (eVec i) y = 1 := by
      rw [dot_eVec_left]
      rcases zmod2_cases (y i) with h | h
      · exact absurd h hi
      · exact h
    have hshift : ∑ x : F2 n, chi x y = ∑ x : F2 n, chi (x + eVec i) y :=
      (Fintype.sum_equiv (Equiv.addRight (eVec i)) _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : F2 n, chi (x + eVec i) y = -(∑ x : F2 n, chi x y) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_add_left]
      simp [chi, hdot]
    linarith

/-- Walsh–Hadamard inversion over any commutative ring `R` (via `Int.cast`). -/
lemma wht_inversion {n : ℕ} {R : Type*} [CommRing R] (f : F2 n → R) (x : F2 n) :
    ∑ u : F2 n, (chi u x : R) * (∑ y : F2 n, (chi u y : R) * f y) = (2 : R) ^ n * f x := by
  calc ∑ u : F2 n, (chi u x : R) * (∑ y : F2 n, (chi u y : R) * f y)
      = ∑ u : F2 n, ∑ y : F2 n, (chi u x : R) * ((chi u y : R) * f y) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ y : F2 n, ∑ u : F2 n, (chi u (x + y) : R) * f y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
        rw [← mul_assoc, ← Int.cast_mul, ← chi_add_right]
    _ = ∑ y : F2 n, (∑ u : F2 n, (chi u (x + y) : R)) * f y := by
        simp_rw [← Finset.sum_mul]
    _ = ∑ y : F2 n, ((if x + y = 0 then (2 : ℤ) ^ n else 0 : ℤ) : R) * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Int.cast_sum, sum_chi]
    _ = ∑ y : F2 n, (if y = x then (2 : R) ^ n * f y else 0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hiff : x + y = 0 ↔ y = x := by
          constructor
          · intro h
            have h1 := congr_arg (x + ·) h
            simpa [f2_add_cancel_left] using h1
          · intro hy; rw [hy]; exact f2_add_self x
        by_cases h : y = x
        · simp [h, f2_add_self]
        · simp [h, show x + y ≠ 0 from fun hc => h (hiff.mp hc)]
    _ = (2 : R) ^ n * f x := by simp

/-- Orthogonal complement of a linear subspace `U ≤ 𝔽₂ⁿ` with respect to `dot`. -/
def orth {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) : Submodule (ZMod 2) (F2 n) where
  carrier := {a : F2 n | ∀ v ∈ U, dot v a = 0}
  add_mem' {a b} ha hb v hv := by rw [dot_add_right, ha v hv, hb v hv, add_zero]
  zero_mem' v _ := dot_zero_right v
  smul_mem' c a ha v hv := by
    rcases zmod2_cases c with rfl | rfl
    · simp [dot_zero_right]
    · simpa using ha v hv

lemma mem_orth_iff {n : ℕ} {U : Submodule (ZMod 2) (F2 n)} {a : F2 n} :
    a ∈ orth U ↔ ∀ v ∈ U, dot v a = 0 := Iff.rfl

/-- Character sum over a linear subspace `U ≤ 𝔽₂ⁿ`. -/
lemma sum_chi_submodule {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) (a : F2 n) :
    ∑ u : U, chi u.1 a = if a ∈ orth U then (Fintype.card U : ℤ) else 0 := by
  by_cases ha : a ∈ orth U
  · simp only [ha, ↓reduceIte]
    have h1 : ∀ u : U, chi u.1 a = 1 := fun u => by simp [chi, ha u.1 u.2]
    simp [h1]
  · simp only [ha, ↓reduceIte]
    rw [mem_orth_iff] at ha
    push Not at ha
    obtain ⟨v, hv, hdot_ne⟩ := ha
    have hdot : dot v a = 1 := by
      rcases zmod2_cases (dot v a) with h | h
      · exact absurd h hdot_ne
      · exact h
    let vSub : U := ⟨v, hv⟩
    have hshift : ∑ u : U, chi u.1 a = ∑ u : U, chi (u + vSub).1 a :=
      (Fintype.sum_equiv (Equiv.addRight vSub) _ _ (fun _ => rfl)).symm
    have hneg : ∑ u : U, chi (u + vSub).1 a = -(∑ u : U, chi u.1 a) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      change chi (u.1 + v) a = -chi u.1 a
      rw [chi_add_left]
      simp [chi, hdot]
    linarith

/-- Character sum over an affine subspace `u₀ + U`. -/
lemma sum_chi_affine {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) (u₀ a : F2 n) :
    ∑ u : U, chi (u₀ + u.1) a =
      if a ∈ orth U then (Fintype.card U : ℤ) * chi u₀ a else 0 := by
  have h : ∑ u : U, chi (u₀ + u.1) a = chi u₀ a * ∑ u : U, chi u.1 a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => chi_add_left u₀ u.1 a
  rw [h, sum_chi_submodule]
  split_ifs <;> ring

/-- Cardinality of a subspace `U ≤ 𝔽₂ⁿ` is `2 ^ finrank U`. -/
lemma card_submodule_f2 {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) :
    Fintype.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have e := Module.finBasis (ZMod 2) U
  have hcard := Fintype.card_congr e.equivFun.toEquiv
  simp [Fintype.card_pi, ZMod.card] at hcard
  exact hcard

/-- The linear evaluation map `a ↦ (v ↦ dot v a)` from `𝔽₂ⁿ` to `U →ₗ[ZMod 2] ZMod 2`. -/
def orthEvalMap {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) :
    F2 n →ₗ[ZMod 2] (U →ₗ[ZMod 2] ZMod 2) where
  toFun a :=
    { toFun := fun v => dot v.1 a
      map_add' := fun v w => dot_add_left v.1 w.1 a
      map_smul' := fun c v => by
        rcases zmod2_cases c with rfl | rfl <;> simp [dot_zero_left] }
  map_add' a b := by
    ext v; exact dot_add_right v.1 a b
  map_smul' c a := by
    ext v; rcases zmod2_cases c with rfl | rfl <;> simp [dot_zero_right]

lemma ker_orthEvalMap {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) :
    LinearMap.ker (orthEvalMap U) = orth U := by
  ext a
  simp only [LinearMap.mem_ker, mem_orth_iff]
  constructor
  · intro h v hv
    have := LinearMap.congr_fun h ⟨v, hv⟩
    simpa [orthEvalMap] using this
  · intro h
    ext ⟨v, hv⟩
    simpa [orthEvalMap] using h v hv

/-- Rank-nullity bound: `finrank (orth U) ≥ n - finrank U`. -/
lemma finrank_orth_ge {n : ℕ} (U : Submodule (ZMod 2) (F2 n)) :
    n ≤ Module.finrank (ZMod 2) (orth U) + Module.finrank (ZMod 2) U := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (orthEvalMap U)
  rw [ker_orthEvalMap, Module.finrank_fin_fun] at hrn
  have hle : Module.finrank (ZMod 2) (LinearMap.range (orthEvalMap U)) ≤
      Module.finrank (ZMod 2) (U →ₗ[ZMod 2] ZMod 2) := Submodule.finrank_le _
  have hdual : Module.finrank (ZMod 2) (U →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) U := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  omega

/-- Hyperplane `b^⊥ = {a | dot a b = 0}`. -/
def perpVec {n : ℕ} (b : F2 n) : Submodule (ZMod 2) (F2 n) where
  carrier := {a : F2 n | dot a b = 0}
  add_mem' {a₁ a₂} h₁ h₂ := by
    change dot (a₁ + a₂) b = 0
    rw [dot_add_left, h₁, h₂, add_zero]
  zero_mem' := dot_zero_left b
  smul_mem' c a ha := by
    change dot (c • a) b = 0
    rcases zmod2_cases c with rfl | rfl
    · simp [dot_zero_left]
    · simpa using ha

lemma finrank_inf_perpVec_ge {n : ℕ} (W : Submodule (ZMod 2) (F2 n)) (b : F2 n) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) + 1 := by
  let φ : W →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun w => dot w.1 b
      map_add' := fun w₁ w₂ => dot_add_left w₁.1 w₂.1 b
      map_smul' := fun c w => by
        rcases zmod2_cases c with rfl | rfl <;> simp [dot_zero_left] }
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hr1 : Module.finrank (ZMod 2) (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa [Module.finrank_self] using this
  let e : LinearMap.ker φ ≃ₗ[ZMod 2] (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) :=
    { toFun := fun ⟨⟨w, hw⟩, hker⟩ => ⟨w, hw, by simpa [φ, perpVec] using hker⟩
      invFun := fun ⟨w, hw, hb⟩ => ⟨⟨w, hw⟩, by simpa [φ, perpVec] using hb⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq] at hrn
  omega

/-- Parity of the sum of signs: `∑ x ∈ S, s x ≡ |S| (mod 2)` when every `s x ∈ {-1, 1}`. -/
lemma sum_signs_parity {α : Type*} (S : Finset α) (s : α → ℤ)
    (hs : ∀ x ∈ S, s x = 1 ∨ s x = -1) :
    (∑ x ∈ S, s x) % 2 = (S.card : ℤ) % 2 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.card_cons, Nat.cast_add, Nat.cast_one]
    have hsa := hs a (Finset.mem_cons_self a t)
    have iht := ih (fun x hx => hs x (Finset.mem_cons_of_mem hx))
    rcases hsa with h | h <;> omega

/-- Number of elements of `W` with `dot a b = 1` is EVEN if `finrank W ≥ 2`. -/
lemma even_card_dot_one {n : ℕ} (W : Submodule (ZMod 2) (F2 n)) (b : F2 n)
    (hdim : 2 ≤ Module.finrank (ZMod 2) W) :
    Even (Finset.univ.filter (fun a : F2 n => a ∈ W ∧ dot a b = 1)).card := by
  let S0 := Finset.univ.filter (fun a : F2 n => a ∈ W ∧ dot a b = 0)
  let S1 := Finset.univ.filter (fun a : F2 n => a ∈ W ∧ dot a b = 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_filter]
    intro a _ h0 h1; rw [h0.2] at h1; exact zero_ne_one h1.2
  have hunion : S0 ∪ S1 = Finset.univ.filter (fun a : F2 n => a ∈ W) := by
    ext a
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases zmod2_cases (dot a b) with hd | hd
      · left; exact ⟨h, hd⟩
      · right; exact ⟨h, hd⟩
  have hsum : S0.card + S1.card = Fintype.card W := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Fintype.card_subtype]
  have hS0 : S0.card = Fintype.card (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) := by
    have heq : S0 = Finset.univ.filter (fun a : F2 n => a ∈ (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n))) := by
      ext a; simp [S0, perpVec]
    rw [heq, ← Fintype.card_subtype]
  rw [hS0, card_submodule_f2, card_submodule_f2] at hsum
  have hd_inf : 1 ≤ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) := by
    have := finrank_inf_perpVec_ge W b; omega
  have hev1 : Even (2 ^ Module.finrank (ZMod 2) W) :=
    even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have hev2 : Even (2 ^ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n))) :=
    even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  change Even S1.card
  rw [even_iff_two_dvd] at hev1 hev2 ⊢
  obtain ⟨p, hp⟩ := hev1
  obtain ⟨q, hq⟩ := hev2
  rw [hp, hq] at hsum
  exact ⟨p - q, by omega⟩

/-- Number of NONZERO elements of `W` with `dot a b = 0` is ODD if `finrank W ≥ 2`. -/
lemma odd_card_nonzero_dot_zero {n : ℕ} (W : Submodule (ZMod 2) (F2 n)) (b : F2 n)
    (hdim : 2 ≤ Module.finrank (ZMod 2) W) :
    Odd (Finset.univ.filter (fun a : F2 n => a ≠ 0 ∧ a ∈ W ∧ dot a b = 0)).card := by
  let S0 := Finset.univ.filter (fun a : F2 n => a ∈ W ∧ dot a b = 0)
  let S0' := Finset.univ.filter (fun a : F2 n => a ≠ 0 ∧ a ∈ W ∧ dot a b = 0)
  have h0 : (0 : F2 n) ∈ S0 := by
    simp [S0, dot_zero_left]
  have herase : S0' = S0.erase 0 := by
    ext a; simp [S0, S0']
  have hcard_S0 : S0.card = 2 ^ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) := by
    have heq : S0 = Finset.univ.filter (fun a : F2 n => a ∈ (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n))) := by
      ext a; simp [S0, perpVec]
    rw [heq, ← Fintype.card_subtype, card_submodule_f2]
  have hd_inf : 1 ≤ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) := by
    have := finrank_inf_perpVec_ge W b; omega
  change Odd S0'.card
  rw [herase, Finset.card_erase_of_mem h0, hcard_S0]
  have hpos : 2 ≤ 2 ^ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd_inf
  have hev : 2 ∣ 2 ^ Module.finrank (ZMod 2) (W ⊓ perpVec b : Submodule (ZMod 2) (F2 n)) :=
    dvd_pow_self 2 (by omega)
  obtain ⟨q, hq⟩ := hev
  refine ⟨q - 1, ?_⟩
  omega

end MultiQubitMUB
