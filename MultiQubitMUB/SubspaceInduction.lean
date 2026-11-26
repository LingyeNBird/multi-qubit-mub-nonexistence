import MultiQubitMUB.GaussianInt
import MultiQubitMUB.Basic

/-!
# The 2-Adic Subspace Induction Theorem on `𝔽₂ⁿ`

Proves the pure algebraic core of the non-existence of even-qubit Pauli-covariant MUB fiducials
and Alltop functions on `𝔽₂^(2k)` (`k ≥ 2`).
-/

namespace MultiQubitMUB

open scoped Classical

/-- Indicator monomial `u^S ∈ {0, 1} ⊆ ℤ[i]` for `S : Finset (Fin m)`. -/
def monom {m : ℕ} (S : Finset (Fin m)) (u : F2 m) : GI :=
  if ∀ i ∈ S, u i = 1 then 1 else 0

/-- Support `{i | u i = 1}` of a binary vector `u : 𝔽₂ᵐ`. -/
def supp {m : ℕ} (u : F2 m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => u i = 1)

/-- Characteristic vector `1_S : 𝔽₂ᵐ` of a subset `S : Finset (Fin m)`. -/
def indVec {m : ℕ} (S : Finset (Fin m)) : F2 m :=
  fun i => if i ∈ S then 1 else 0

lemma mem_supp_iff {m : ℕ} {u : F2 m} {i : Fin m} : i ∈ supp u ↔ u i = 1 := by
  simp [supp]

lemma supp_indVec {m : ℕ} (S : Finset (Fin m)) : supp (indVec S) = S := by
  ext i; simp [supp, indVec]

lemma indVec_supp {m : ℕ} (u : F2 m) : indVec (supp u) = u := by
  ext i
  simp only [indVec, mem_supp_iff]
  rcases zmod2_cases (u i) with h | h <;> simp [h]

lemma supp_injective {m : ℕ} : Function.Injective (@supp m) := by
  intro u v h
  rw [← indVec_supp u, ← indVec_supp v, h]

lemma monom_eq_ite_subset {m : ℕ} (S : Finset (Fin m)) (u : F2 m) :
    monom S u = if S ⊆ supp u then 1 else 0 := by
  simp only [monom, Finset.subset_iff, mem_supp_iff]

lemma monom_mul {m : ℕ} (S T : Finset (Fin m)) (u : F2 m) :
    monom S u * monom T u = monom (S ∪ T) u := by
  simp only [monom_eq_ite_subset, Finset.union_subset_iff]
  split_ifs <;> simp_all

/-- Cardinality of `{u : 𝔽₂ᵐ | S ⊆ supp u}` is `2^(m - |S|)`. -/
lemma sum_monom {m : ℕ} (S : Finset (Fin m)) :
    ∑ u : F2 m, monom S u = (2 : GI) ^ (m - S.card) := by
  simp_rw [monom_eq_ite_subset]
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun u : F2 m => S ⊆ supp u)).card = 2 ^ (m - S.card) := by
    let e : {u : F2 m // S ⊆ supp u} ≃ Finset {i : Fin m // i ∉ S} :=
      { toFun := fun ⟨u, _⟩ => Finset.univ.filter (fun j => u j.1 = 1)
        invFun := fun A => ⟨fun i => if h : i ∈ S then 1 else if (⟨i, h⟩ : {i : Fin m // i ∉ S}) ∈ A then 1 else 0, by
          intro i hi; simp [mem_supp_iff, hi]⟩
        left_inv := fun ⟨u, hu⟩ => by
          ext i
          by_cases hi : i ∈ S
          · simp [hi, mem_supp_iff.mp (hu hi)]
          · simp only [hi, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases zmod2_cases (u i) with h | h <;> simp [h]
        right_inv := fun A => by
          ext ⟨i, hi⟩
          simp [hi] }
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_finset, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_coe]
  rw [hcard]
  norm_cast

/-- Möbius coefficient `c_S(f) = ∑_{supp u ⊆ S} (-1)^(|S| - |supp u|) f(u)`. -/
def mobiusCoeff {m : ℕ} (f : F2 m → GI) (S : Finset (Fin m)) : GI :=
  ∑ u : F2 m, if supp u ⊆ S then (-1 : GI) ^ (S.card - (supp u).card) * f u else 0

/-- Alternating sum over subsets `A ⊆ R` vanishes when `R` is nonempty. -/
lemma sum_neg_one_pow_card_powerset {m : ℕ} (R : Finset (Fin m)) :
    ∑ A ∈ R.powerset, (-1 : GI) ^ A.card = if R = ∅ then 1 else 0 := by
  by_cases hR : R = ∅
  · subst hR; simp
  · simp only [hR, ↓reduceIte]
    have hne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hR
    obtain ⟨a, ha⟩ := hne
    let R' := R.erase a
    have hpow : R.powerset = R'.powerset ∪ R'.powerset.image (insert a) := by
      ext A
      simp only [Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hA
        by_cases haA : a ∈ A
        · right; refine ⟨A.erase a, ?_, Finset.insert_erase haA⟩
          intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hA (Finset.mem_erase.mp hx).2⟩
        · left
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun h => haA (h ▸ hx), hA hx⟩
      · rintro (hA | ⟨B, hB, rfl⟩)
        · exact hA.trans (Finset.erase_subset a R)
        · exact Finset.insert_subset ha (hB.trans (Finset.erase_subset a R))
    have hdisj : Disjoint R'.powerset (R'.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro A hA1 hA2
      rcases Finset.mem_image.mp hA2 with ⟨B, _, rfl⟩
      have h1 : a ∈ R' := Finset.mem_powerset.mp hA1 (Finset.mem_insert_self a B)
      exact (Finset.notMem_erase a R) h1
    have hinj : Set.InjOn (insert a) (R'.powerset : Set (Finset (Fin m))) := by
      intro B₁ hB₁ B₂ hB₂ heq
      have h1 : a ∉ B₁ := fun hc => Finset.notMem_erase a R (Finset.mem_powerset.mp hB₁ hc)
      have h2 : a ∉ B₂ := fun hc => Finset.notMem_erase a R (Finset.mem_powerset.mp hB₂ hc)
      have := congr_arg (fun s => Finset.erase s a) heq
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
    rw [hpow, Finset.sum_union hdisj, Finset.sum_image hinj]
    have hneg : ∑ B ∈ R'.powerset, (-1 : GI) ^ (insert a B).card =
        -(∑ B ∈ R'.powerset, (-1 : GI) ^ B.card) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun B hB => ?_
      have hna : a ∉ B := fun hc => Finset.notMem_erase a R (Finset.mem_powerset.mp hB hc)
      rw [Finset.card_insert_of_notMem hna, pow_succ]
      ring
    rw [hneg, add_neg_cancel]

/-- Exact Möbius inversion on `𝔽₂ᵐ` into `ℤ[i]`. -/
lemma mobius_inversion {m : ℕ} (f : F2 m → GI) (u : F2 m) :
    ∑ S : Finset (Fin m), mobiusCoeff f S * monom S u = f u := by
  simp_rw [mobiusCoeff, monom_eq_ite_subset, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ v : F2 m,
      (∑ S : Finset (Fin m),
        (if supp v ⊆ S then (-1 : GI) ^ (S.card - (supp v).card) * f v else 0) *
          (if S ⊆ supp u then 1 else 0)) =
      if v = u then f v else 0 := by
    intro v
    by_cases hsub : supp v ⊆ supp u
    · let R := supp u \ supp v
      have hfilt : (∑ S : Finset (Fin m),
          (if supp v ⊆ S then (-1 : GI) ^ (S.card - (supp v).card) * f v else 0) *
            (if S ⊆ supp u then 1 else 0)) =
          (∑ A ∈ R.powerset, (-1 : GI) ^ A.card) * f v := by
        rw [Finset.sum_mul]
        have hbi : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => supp v ⊆ S ∧ S ⊆ supp u),
            (-1 : GI) ^ (S.card - (supp v).card) * f v =
            ∑ A ∈ R.powerset, (-1 : GI) ^ A.card * f v := by
          refine Finset.sum_nbij (fun S => S \ supp v) ?_ ?_ ?_ ?_
          · intro S hS
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
            rw [Finset.mem_powerset]
            exact Finset.sdiff_subset_sdiff hS.2 Finset.Subset.rfl
          · intro S₁ hS₁ S₂ hS₂ heq
            dsimp only at heq
            have h1 : supp v ⊆ S₁ := (Finset.mem_filter.mp hS₁).2.1
            have h2 : supp v ⊆ S₂ := (Finset.mem_filter.mp hS₂).2.1
            rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, heq]
          · intro A hA
            have hA' : A ⊆ R := Finset.mem_powerset.mp (Finset.mem_coe.mp hA)
            refine ⟨supp v ∪ A, ?_, ?_⟩
            · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                Finset.subset_union_left,
                Finset.union_subset hsub (hA'.trans Finset.sdiff_subset)⟩)
            · dsimp only
              have hdisj : Disjoint A (supp v) :=
                Disjoint.mono_left hA' Finset.sdiff_disjoint
              rw [Finset.union_sdiff_cancel_left hdisj.symm]
          · intro S hS
            have h1 : supp v ⊆ S := (Finset.mem_filter.mp hS).2.1
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h1]
        rw [← hbi, Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases h1 : supp v ⊆ S <;> by_cases h2 : S ⊆ supp u <;> simp [h1, h2]
      rw [hfilt, sum_neg_one_pow_card_powerset]
      have hiff : R = ∅ ↔ v = u := by
        constructor
        · intro hR
          have heq : supp v = supp u :=
            Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hR)
          exact supp_injective heq
        · rintro rfl; simp [R]
      by_cases hvu : v = u
      · simp [hvu, hiff.mpr hvu]
      · simp [hvu, show R ≠ ∅ from fun hc => hvu (hiff.mp hc)]
    · have hne : v ≠ u := fun h => hsub (h ▸ Finset.Subset.rfl)
      simp only [hne, ↓reduceIte]
      refine Finset.sum_eq_zero fun S _ => ?_
      by_cases h1 : supp v ⊆ S
      · have h2 : ¬ S ⊆ supp u := fun h2 => hsub (h1.trans h2)
        simp [h1, h2]
      · simp [h1]
  simp_rw [hterm]
  simp

/-- Exact WHT-to-subcube identity:
    `∑ u, χ(u, x) f(u) = ∑ T, (-2)^|T| x^T (∑ u, u^T f(u))`. -/
lemma wht_eq_subcube_sum {n : ℕ} (f : F2 n → GI) (x : F2 n) :
    ∑ u : F2 n, (chi u x : GI) * f u =
      ∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T x * (∑ u : F2 n, monom T u * f u) := by
  have hchi : ∀ u : F2 n, (chi u x : GI) =
      ∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T x * monom T u := by
    intro u
    have hprod : (chi u x : GI) =
        ∏ i : Fin n, ((-2 : GI) * (if u i = 1 ∧ x i = 1 then 1 else 0) + 1) := by
      have hfactor : ∀ i : Fin n,
          ((-2 : GI) * (if u i = 1 ∧ x i = 1 then 1 else 0) + 1) =
            if u i * x i = 0 then 1 else -1 := by
        intro i
        rcases zmod2_cases (u i) with hu | hu <;> rcases zmod2_cases (x i) with hx | hx
        · simp [hu, hx]
        · simp [hu, hx]
        · simp [hu, hx]
        · simp only [hu, hx, mul_one, one_ne_zero, ↓reduceIte, and_self]; ring
      simp_rw [hfactor]
      have hgen : ∀ (S : Finset (Fin n)),
          (∏ i ∈ S, (if u i * x i = 0 then (1 : GI) else -1)) =
            if (∑ i ∈ S, u i * x i) = 0 then 1 else -1 := by
        intro S
        induction S using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
          rw [Finset.prod_cons, Finset.sum_cons, ih]
          rcases zmod2_cases (u a * x a) with h1 | h1 <;>
            rcases zmod2_cases (∑ i ∈ s, u i * x i) with h2 | h2
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]; decide
      rw [hgen Finset.univ]
      change (chi u x : GI) = if dot u x = 0 then 1 else -1
      simp only [chi]; split_ifs <;> simp
    rw [hprod]
    have hexp : ∏ i ∈ (Finset.univ : Finset (Fin n)),
        ((-2 : GI) * (if u i = 1 ∧ x i = 1 then 1 else 0) + 1) =
        ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∏ i ∈ T, ((-2 : GI) * (if u i = 1 ∧ x i = 1 then 1 else 0)) := by
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun T _ => by simp
    rw [hexp, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hmon : (∏ i ∈ T, (if u i = 1 ∧ x i = 1 then (1 : GI) else 0)) =
        monom T x * monom T u := by
      by_cases h : ∀ i ∈ T, u i = 1 ∧ x i = 1
      · have h1 : ∀ i ∈ T, (if u i = 1 ∧ x i = 1 then (1 : GI) else 0) = 1 :=
          fun i hi => by simp [h i hi]
        rw [Finset.prod_eq_one h1]
        have hx : ∀ i ∈ T, x i = 1 := fun i hi => (h i hi).2
        have hu : ∀ i ∈ T, u i = 1 := fun i hi => (h i hi).1
        simp only [monom]
        split_ifs
        ring
      · push Not at h
        obtain ⟨i, hi, hne⟩ := h
        have hnotboth : ¬ (u i = 1 ∧ x i = 1) := fun ⟨h1, h2⟩ => hne h1 h2
        have hzero : ∏ j ∈ T, (if u j = 1 ∧ x j = 1 then (1 : GI) else 0) = 0 :=
          Finset.prod_eq_zero hi (by simp [hnotboth])
        rw [hzero]
        simp only [monom]
        split_ifs with h1 h2
        · exfalso; exact hne (h2 i hi) (h1 i hi)
        all_goals ring
    rw [hmon]; ring
  calc ∑ u : F2 n, (chi u x : GI) * f u
      = ∑ u : F2 n, (∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T x * monom T u) * f u := by
        refine Finset.sum_congr rfl fun u _ => by rw [hchi u]
    _ = ∑ u : F2 n, ∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T x * (monom T u * f u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun T _ => by ring
    _ = ∑ T : Finset (Fin n), ∑ u : F2 n, (-2 : GI) ^ T.card * monom T x * (monom T u * f u) := by
        rw [Finset.sum_comm]
    _ = ∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T x * (∑ u : F2 n, monom T u * f u) := by
        refine Finset.sum_congr rfl fun T _ => by rw [← Finset.mul_sum]

/-- Induction predicate `(IH_m)`: every `r`-dim affine subspace sum (`1 ≤ r ≤ m`) of `η` is divisible by `2^(r-1)`. -/
def SubspaceVal {n : ℕ} (η : F2 n → GI) (m : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ m →
    ∀ (U : Submodule (ZMod 2) (F2 n)), Module.finrank (ZMod 2) U = r →
    ∀ (v₀ : F2 n), ((2 : GI) ^ (r - 1)) ∣ (∑ u : U, η (v₀ + u.1))

/-- Correlation congruence `(*_r)` on all `r`-dim affine subspaces and all shifts `b`. -/
def CorrCongr {n : ℕ} (η : F2 n → GI) (r : ℕ) : Prop :=
  ∀ (U : Submodule (ZMod 2) (F2 n)), Module.finrank (ZMod 2) U = r →
  ∀ (v₀ b : F2 n),
    ((2 : GI) ^ r) ∣
      (∑ u : U, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b) +
        (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)))

/-- Linear map `F2 m →ₗ[ZMod 2] F2 n` sending `u ↦ ∑ i, u i • e i`. -/
def evalBasis {n m : ℕ} (e : Fin m → F2 n) : F2 m →ₗ[ZMod 2] F2 n where
  toFun u := ∑ i : Fin m, u i • e i
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.smul_sum, mul_smul]

lemma evalBasis_injective {n m : ℕ} {e : Fin m → F2 n} (hli : LinearIndependent (ZMod 2) e) :
    Function.Injective (evalBasis e) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  exact funext (Fintype.linearIndependent_iff.mp hli u hu)

/-- Pulling back `SubspaceVal` along an injective linear map `evalBasis e`. -/
lemma subspaceVal_pullback {n m k : ℕ} {η : F2 n → GI} {e : Fin k → F2 n}
    (hli : LinearIndependent (ZMod 2) e) (hIH : SubspaceVal η m) (v₀ : F2 n) :
    SubspaceVal (fun u : F2 k => η (v₀ + evalBasis e u)) m := by
  intro r hr1 hrm A hA u₀
  let φ := evalBasis e
  have hinj : Function.Injective φ := evalBasis_injective hli
  let U : Submodule (ZMod 2) (F2 n) := A.map φ
  have hfin : Module.finrank (ZMod 2) U = r := by
    let eqv : A ≃ₗ[ZMod 2] U := LinearEquiv.ofInjective (φ.comp A.subtype)
      (hinj.comp Subtype.val_injective) |>.trans
      (LinearEquiv.ofEq _ _ (by
        ext x; simp [U, LinearMap.mem_range, Submodule.mem_map]))
    rw [← eqv.finrank_eq, hA]
  have hsum : (∑ u : A, η (v₀ + φ (u₀ + u.1))) = ∑ w : U, η ((v₀ + φ u₀) + w.1) := by
    let eqv : A ≃ U :=
      { toFun := fun u => ⟨φ u.1, Submodule.mem_map_of_mem u.2⟩
        invFun := fun w => ⟨(Submodule.mem_map.mp w.2).choose, (Submodule.mem_map.mp w.2).choose_spec.1⟩
        left_inv := fun u => Subtype.ext (hinj (Submodule.mem_map.mp (Submodule.mem_map_of_mem u.2)).choose_spec.2)
        right_inv := fun w => Subtype.ext (Submodule.mem_map.mp w.2).choose_spec.2 }
    refine Fintype.sum_equiv eqv _ _ fun u => ?_
    simp [eqv, map_add, add_assoc]
  rw [hsum]
  exact hIH r hr1 hrm U hfin (v₀ + φ u₀)

/-- Subspace `C_S = {u : F2 m | ∀ i ∉ S, u i = 0}` has `finrank = S.card`. -/
def coordSubspace {m : ℕ} (S : Finset (Fin m)) : Submodule (ZMod 2) (F2 m) where
  carrier := {u : F2 m | ∀ i, i ∉ S → u i = 0}
  add_mem' {u v} hu hv i hi := by simp [hu i hi, hv i hi]
  zero_mem' i _ := rfl
  smul_mem' c u hu i hi := by simp [hu i hi]

lemma mem_coordSubspace_iff {m : ℕ} {S : Finset (Fin m)} {u : F2 m} :
    u ∈ coordSubspace S ↔ supp u ⊆ S := by
  constructor
  · intro h i hi
    by_contra hni
    have h0 := h i hni
    rw [mem_supp_iff] at hi
    rw [h0] at hi; exact zero_ne_one hi
  · intro h i hni
    rcases zmod2_cases (u i) with h0 | h1
    · exact h0
    · exact absurd (h (mem_supp_iff.mpr h1)) hni

lemma finrank_coordSubspace {m : ℕ} (S : Finset (Fin m)) :
    Module.finrank (ZMod 2) (coordSubspace S) = S.card := by
  let e : coordSubspace S ≃ₗ[ZMod 2] (S → ZMod 2) :=
    { toFun := fun u i => u.1 i.1
      invFun := fun f => ⟨fun i => if h : i ∈ S then f ⟨i, h⟩ else 0, by
        intro i hi; simp [hi]⟩
      left_inv := fun ⟨u, hu⟩ => by
        ext i; by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi, hu i hi]
      right_inv := fun f => by
        ext ⟨i, hi⟩; simp [hi]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_coe]

/-- Even-parity subspace `H₀(S) = {u ∈ C_S | ∑ i ∈ S, u i = 0}` has `finrank = S.card - 1` for `S ≠ ∅`. -/
def evenSubspace {m : ℕ} (S : Finset (Fin m)) : Submodule (ZMod 2) (F2 m) where
  carrier := {u : F2 m | u ∈ coordSubspace S ∧ (∑ i ∈ S, u i) = 0}
  add_mem' {u v} hu hv := ⟨(coordSubspace S).add_mem hu.1 hv.1, by
    simp [Finset.sum_add_distrib, hu.2, hv.2]⟩
  zero_mem' := ⟨(coordSubspace S).zero_mem, by simp⟩
  smul_mem' c u hu := ⟨(coordSubspace S).smul_mem c hu.1, by
    simp [← Finset.mul_sum, hu.2]⟩

lemma finrank_evenSubspace {m : ℕ} {S : Finset (Fin m)} (hS : S.Nonempty) :
    Module.finrank (ZMod 2) (evenSubspace S) = S.card - 1 := by
  let φ : coordSubspace S →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => ∑ i ∈ S, u.1 i
      map_add' := fun u v => by simp [Finset.sum_add_distrib]
      map_smul' := fun c u => by simp [← Finset.mul_sum] }
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rcases zmod2_cases y with rfl | rfl
    · exact ⟨0, map_zero φ⟩
    · obtain ⟨i₀, hi₀⟩ := hS
      refine ⟨⟨eVec i₀, ?_⟩, ?_⟩
      · intro i hi
        have hne : i ≠ i₀ := fun h => hi (h ▸ hi₀)
        simp [eVec, hne]
      · simp [φ, eVec, Pi.single_apply, hi₀]
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, Module.finrank_self, finrank_coordSubspace] at hrn
  let eqv : LinearMap.ker φ ≃ₗ[ZMod 2] evenSubspace S :=
    { toFun := fun ⟨⟨u, hu⟩, hker⟩ => ⟨u, hu, by simpa [φ] using hker⟩
      invFun := fun ⟨u, hu, hsum⟩ => ⟨⟨u, hu⟩, by simpa [φ] using hsum⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [eqv.finrank_eq] at hrn
  omega

/-- Parity of `(supp u).card` matches `∑ i ∈ S, u i : ZMod 2` when `supp u ⊆ S`. -/
lemma sum_zmod2_eq_card_supp {m : ℕ} {S : Finset (Fin m)} {u : F2 m} (hu : supp u ⊆ S) :
    (∑ i ∈ S, u i) = ((supp u).card : ZMod 2) := by
  have h1 : ∑ i ∈ S, u i = ∑ i ∈ S, (if i ∈ supp u then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mem_supp_iff]
    rcases zmod2_cases (u i) with h | h <;> simp [h]
  rw [h1, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hu, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Express `mobiusCoeff f S` via `C_S` and `H₀(S)`. -/
lemma mobiusCoeff_eq_subspaces {m : ℕ} (f : F2 m → GI) (S : Finset (Fin m)) :
    mobiusCoeff f S =
      (-1 : GI) ^ S.card * ((2 : GI) * (∑ u : evenSubspace S, f u.1) - ∑ u : coordSubspace S, f u.1) := by
  have hC : (∑ u : coordSubspace S, f u.1) = ∑ u : F2 m, if supp u ⊆ S then f u else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u : F2 m => supp u ⊆ S))
      (fun u => by simp [mem_coordSubspace_iff]) f).symm
  have hH0 : (∑ u : evenSubspace S, f u.1) =
      ∑ u : F2 m, if supp u ⊆ S ∧ Even (supp u).card then f u else 0 := by
    rw [← Finset.sum_filter]
    refine (Finset.sum_subtype (Finset.univ.filter (fun u : F2 m => supp u ⊆ S ∧ Even (supp u).card))
      (fun u => ?_) f).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (supp u ⊆ S ∧ Even (supp u).card) ↔ (u ∈ coordSubspace S ∧ (∑ i ∈ S, u i) = 0)
    constructor
    · rintro ⟨hsub, hev⟩
      refine ⟨mem_coordSubspace_iff.mpr hsub, ?_⟩
      rw [sum_zmod2_eq_card_supp hsub, ZMod.natCast_eq_zero_iff]
      exact even_iff_two_dvd.mp hev
    · rintro ⟨hu, hsum⟩
      have hsub := mem_coordSubspace_iff.mp hu
      rw [sum_zmod2_eq_card_supp hsub, ZMod.natCast_eq_zero_iff] at hsum
      exact ⟨hsub, even_iff_two_dvd.mpr hsum⟩
  rw [hC, hH0, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  unfold mobiusCoeff
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hsub : supp u ⊆ S
  · have hle : (supp u).card ≤ S.card := Finset.card_le_card hsub
    have hpow : (-1 : GI) ^ (S.card - (supp u).card) = (-1 : GI) ^ S.card * (-1 : GI) ^ (supp u).card := by
      have h1 : (-1 : GI) ^ S.card = (-1 : GI) ^ (S.card - (supp u).card) * (-1 : GI) ^ (supp u).card := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [h1, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    by_cases hev : Even (supp u).card
    · simp only [hsub, hev, and_self, ↓reduceIte, hpow, Even.neg_one_pow hev, mul_one]
      ring
    · have hodd : Odd (supp u).card := Nat.not_even_iff_odd.mp hev
      simp only [hsub, hev, and_false, ↓reduceIte, hpow, Odd.neg_one_pow hodd]
      ring
  · simp [hsub]

/-- Sublemma 5a(i): under `SubspaceVal f m`, `2^(|S| - 1) ∣ mobiusCoeff f S` for all nonempty `S`. -/
lemma pow_two_dvd_mobiusCoeff {m : ℕ} {f : F2 m → GI} (hIH : SubspaceVal f m)
    {S : Finset (Fin m)} (hS : S.Nonempty) :
    ((2 : GI) ^ (S.card - 1)) ∣ mobiusCoeff f S := by
  by_cases h1 : S.card = 1
  · rw [h1]; simp
  · have hge2 : 2 ≤ S.card := by
      have := Finset.card_pos.mpr hS; omega
    have hle : S.card ≤ m := by
      have := Finset.card_le_univ S; simpa using this
    rw [mobiusCoeff_eq_subspaces]
    refine dvd_mul_of_dvd_right (dvd_sub ?_ ?_) _
    · have h0 := hIH (S.card - 1) (by omega) (by omega) (evenSubspace S) (finrank_evenSubspace hS) 0
      simp only [zero_add] at h0
      have : (2 : GI) ^ (S.card - 1) = (2 : GI) * (2 : GI) ^ (S.card - 1 - 1) := by
        rw [← pow_succ', show S.card - 1 - 1 + 1 = S.card - 1 by omega]
      rw [this]
      exact mul_dvd_mul_left 2 h0
    · have hC := hIH S.card (by omega) hle (coordSubspace S) (finrank_coordSubspace S) 0
      simpa using hC

/-- Diagonal hyperplane `H_diag(T) = {(u, t) ∈ C_T × 𝔽₂ | (∑ i ∈ T, u i) + t = 0}` in `𝔽₂^(m+1)`. -/
def diagSubspace {m : ℕ} (T : Finset (Fin m)) : Submodule (ZMod 2) (F2 (m + 1)) where
  carrier := {w : F2 (m + 1) | (∀ i : Fin m, i ∉ T → w i.castSucc = 0) ∧
    (∑ i ∈ T, w i.castSucc) + w (Fin.last m) = 0}
  add_mem' {w₁ w₂} h₁ h₂ := ⟨fun i hi => by simp [h₁.1 i hi, h₂.1 i hi], by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    have := congr_arg₂ (· + ·) h₁.2 h₂.2
    simpa [add_assoc, add_left_comm, add_comm] using this⟩
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' c w hw := ⟨fun i hi => by simp [hw.1 i hi], by
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hw.2⟩

/-- Extended coordinate subspace `C_T × 𝔽₂` in `𝔽₂^(m+1)` has `finrank = T.card + 1`. -/
def extCoordSubspace {m : ℕ} (T : Finset (Fin m)) : Submodule (ZMod 2) (F2 (m + 1)) where
  carrier := {w : F2 (m + 1) | ∀ i : Fin m, i ∉ T → w i.castSucc = 0}
  add_mem' {w₁ w₂} h₁ h₂ i hi := by simp [h₁ i hi, h₂ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c w hw i hi := by simp [hw i hi]

lemma finrank_extCoordSubspace {m : ℕ} (T : Finset (Fin m)) :
    Module.finrank (ZMod 2) (extCoordSubspace T) = T.card + 1 := by
  let e : extCoordSubspace T ≃ₗ[ZMod 2] ((T → ZMod 2) × ZMod 2) :=
    { toFun := fun w => (fun i => w.1 i.1.castSucc, w.1 (Fin.last m))
      invFun := fun p => ⟨Fin.snoc (fun i => if h : i ∈ T then p.1 ⟨i, h⟩ else 0) p.2, by
        intro i hi; simp [Fin.snoc_castSucc, hi]⟩
      left_inv := fun ⟨w, hw⟩ => by
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [Fin.snoc_last]
        · by_cases hi : i ∈ T
          · simp [Fin.snoc_castSucc, hi]
          · simp [Fin.snoc_castSucc, hi, hw i hi]
      right_inv := fun ⟨f, t⟩ => by
        ext
        · rename_i i; simp [Fin.snoc_castSucc, i.2]
        · simp [Fin.snoc_last]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_coe]

lemma finrank_diagSubspace {m : ℕ} (T : Finset (Fin m)) :
    Module.finrank (ZMod 2) (diagSubspace T) = T.card := by
  let e : diagSubspace T ≃ₗ[ZMod 2] (T → ZMod 2) :=
    { toFun := fun w i => w.1 i.1.castSucc
      invFun := fun f =>
        ⟨Fin.snoc (fun i => if h : i ∈ T then f ⟨i, h⟩ else 0) (∑ i : T, f i), by
          refine ⟨fun i hi => by simp [Fin.snoc_castSucc, hi], ?_⟩
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          have hs : (∑ i ∈ T, if h : i ∈ T then f ⟨i, h⟩ else 0) = ∑ i : T, f i := by
            rw [← Finset.sum_attach T (fun i => if h : i ∈ T then f ⟨i, h⟩ else 0)]
            change (∑ i : T, if h : i.1 ∈ T then f ⟨i.1, h⟩ else 0) = ∑ i : T, f i
            refine Finset.sum_congr rfl fun i _ => by simp [i.2]
          rw [hs]
          rcases zmod2_cases (∑ i : T, f i) with h | h
          · rw [h]; simp
          · rw [h]; decide⟩
      left_inv := fun ⟨w, hw⟩ => by
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [Fin.snoc_last]
          have h1 : (∑ i : T, w i.1.castSucc) = ∑ i ∈ T, w i.castSucc :=
            Finset.sum_coe_sort T (fun i : Fin m => w i.castSucc)
          rw [h1]
          have h2 := hw.2
          rcases zmod2_cases (∑ i ∈ T, w i.castSucc) with ha | ha <;>
            rcases zmod2_cases (w (Fin.last m)) with hb | hb
          · simp [ha, hb]
          · exfalso; rw [ha, hb] at h2; simp at h2
          · exfalso; rw [ha, hb] at h2; simp at h2
          · simp [ha, hb]
        · by_cases hi : i ∈ T
          · simp [Fin.snoc_castSucc, hi]
          · simp [Fin.snoc_castSucc, hi, hw.1 i hi]
      right_inv := fun f => by
        ext ⟨i, hi⟩; simp [Fin.snoc_castSucc, hi]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_coe]

/-- Express `mobiusCoeff δ T` for `δ u = h (snoc u 1) - h (snoc u 0)` via `extCoordSubspace T` and `diagSubspace T`! -/
lemma mobiusCoeff_diff_eq_subspaces {m : ℕ} (h : F2 (m + 1) → GI) (T : Finset (Fin m)) :
    mobiusCoeff (fun u => h (Fin.snoc u 1) - h (Fin.snoc u 0)) T =
      (-1 : GI) ^ T.card * ((∑ w : extCoordSubspace T, h w.1) - (2 : GI) * ∑ w : diagSubspace T, h w.1) := by
  have hExt : (∑ w : extCoordSubspace T, h w.1) =
      ∑ u : F2 m, if supp u ⊆ T then h (Fin.snoc u 0) + h (Fin.snoc u 1) else 0 := by
    let e : (coordSubspace T × ZMod 2) ≃ extCoordSubspace T :=
      { toFun := fun ⟨⟨u, hu⟩, t⟩ => ⟨Fin.snoc u t, fun i hi => by
          rw [Fin.snoc_castSucc]; exact hu i hi⟩
        invFun := fun ⟨w, hw⟩ => (⟨fun i => w i.castSucc, fun i hi => hw i hi⟩, w (Fin.last m))
        left_inv := fun ⟨⟨u, _⟩, t⟩ => by
          ext i
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun ⟨w, _⟩ => by
          ext j
          refine Fin.lastCases (by simp [Fin.snoc_last]) (fun i => by simp [Fin.snoc_castSucc]) j }
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have h2 : ∀ x : coordSubspace T,
        (∑ t : ZMod 2, h (e (x, t)).1) = h (Fin.snoc x.1 0) + h (Fin.snoc x.1 1) := fun x => by
      rw [sum_zmod2]; rfl
    simp_rw [h2]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u : F2 m => supp u ⊆ T))
      (fun u => by simp [mem_coordSubspace_iff])
      (fun u => h (Fin.snoc u 0) + h (Fin.snoc u 1))).symm
  have hDiag : (∑ w : diagSubspace T, h w.1) =
      ∑ u : F2 m, if supp u ⊆ T then
        (if Even (supp u).card then h (Fin.snoc u 0) else h (Fin.snoc u 1)) else 0 := by
    let e : coordSubspace T ≃ diagSubspace T :=
      { toFun := fun ⟨u, hu⟩ => ⟨Fin.snoc u (∑ i ∈ T, u i),
          ⟨fun i hi => by rw [Fin.snoc_castSucc]; exact hu i hi, by
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            rcases zmod2_cases (∑ i ∈ T, u i) with hs | hs
            · rw [hs]; simp
            · rw [hs]; decide⟩⟩
        invFun := fun ⟨w, hw⟩ => ⟨fun i => w i.castSucc, fun i hi => hw.1 i hi⟩
        left_inv := fun ⟨u, _⟩ => by ext i; simp [Fin.snoc_castSucc]
        right_inv := fun ⟨w, hw⟩ => by
          ext j
          refine Fin.lastCases ?_ (fun i => by simp [Fin.snoc_castSucc]) j
          simp only [Fin.snoc_last]
          have h2 := hw.2
          rcases zmod2_cases (∑ i ∈ T, w i.castSucc) with ha | ha <;>
            rcases zmod2_cases (w (Fin.last m)) with hb | hb
          · simp [ha, hb]
          · exfalso; rw [ha, hb] at h2; simp at h2
          · exfalso; rw [ha, hb] at h2; simp at h2
          · simp [ha, hb] }
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
    have hsub1 : (∑ x : coordSubspace T, h (e x).1) =
        ∑ u ∈ Finset.univ.filter (fun u : F2 m => supp u ⊆ T), h (Fin.snoc u (∑ i ∈ T, u i)) :=
      (Finset.sum_subtype (Finset.univ.filter (fun u : F2 m => supp u ⊆ T))
        (fun u => by simp [mem_coordSubspace_iff])
        (fun u => h (Fin.snoc u (∑ i ∈ T, u i)))).symm
    rw [hsub1, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hsub : supp u ⊆ T := (Finset.mem_filter.mp hu).2
    rw [sum_zmod2_eq_card_supp hsub]
    by_cases hev : Even (supp u).card
    · have hz : ((supp u).card : ZMod 2) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (even_iff_two_dvd.mp hev)
      simp [hev, hz]
    · have hne : ((supp u).card : ZMod 2) ≠ 0 := fun hz =>
        hev (even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hz))
      have h1 : ((supp u).card : ZMod 2) = 1 := by
        rcases zmod2_cases ((supp u).card : ZMod 2) with h | h
        · exact absurd h hne
        · exact h
      simp [hev, h1]
  rw [hExt, hDiag, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  unfold mobiusCoeff
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hsub : supp u ⊆ T
  · have hle : (supp u).card ≤ T.card := Finset.card_le_card hsub
    have hpow : (-1 : GI) ^ (T.card - (supp u).card) = (-1 : GI) ^ T.card * (-1 : GI) ^ (supp u).card := by
      have h1 : (-1 : GI) ^ T.card = (-1 : GI) ^ (T.card - (supp u).card) * (-1 : GI) ^ (supp u).card := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [h1, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    by_cases hev : Even (supp u).card
    · simp only [hsub, hev, ↓reduceIte, hpow, Even.neg_one_pow hev, mul_one]
      ring
    · have hodd : Odd (supp u).card := Nat.not_even_iff_odd.mp hev
      simp only [hsub, hev, ↓reduceIte, hpow, Odd.neg_one_pow hodd]
      ring
  · simp [hsub]

/-- Sublemma 5a(ii): under `SubspaceVal h m` on `𝔽₂^(m+1)`, `2^|T| ∣ mobiusCoeff δ T` for `1 ≤ |T| ≤ m - 1`,
    and `2^(m - 1) ∣ mobiusCoeff δ T` for `|T| = m`. -/
lemma pow_two_dvd_mobiusCoeff_diff {m : ℕ} {h : F2 (m + 1) → GI} (hIH : SubspaceVal h m)
    {T : Finset (Fin m)} (hT : T.Nonempty) :
    (if T.card < m then (2 : GI) ^ T.card else (2 : GI) ^ (m - 1)) ∣
      mobiusCoeff (fun u => h (Fin.snoc u 1) - h (Fin.snoc u 0)) T := by
  by_cases hlt : T.card < m
  · simp only [hlt, ↓reduceIte]
    rw [mobiusCoeff_diff_eq_subspaces]
    refine dvd_mul_of_dvd_right (dvd_sub ?_ ?_) _
    · have h1 := hIH (T.card + 1) (by omega) (by omega) (extCoordSubspace T) (finrank_extCoordSubspace T) 0
      simpa using h1
    · have h2 := hIH T.card (Finset.card_pos.mpr hT) (by omega) (diagSubspace T) (finrank_diagSubspace T) 0
      simp only [zero_add] at h2
      have : (2 : GI) ^ T.card = (2 : GI) * (2 : GI) ^ (T.card - 1) := by
        have hpos := Finset.card_pos.mpr hT
        rw [← pow_succ', show T.card - 1 + 1 = T.card by omega]
      rw [this]
      exact mul_dvd_mul_left 2 h2
  · simp only [hlt, ↓reduceIte]
    have hcard : T.card = m := by
      have hle : T.card ≤ m := by simpa using Finset.card_le_univ T
      omega
    have hlin : mobiusCoeff (fun u => h (Fin.snoc u 1) - h (Fin.snoc u 0)) T =
        mobiusCoeff (fun u => h (Fin.snoc u 1)) T - mobiusCoeff (fun u => h (Fin.snoc u 0)) T := by
      unfold mobiusCoeff
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
    rw [hlin]
    let e0 : Fin m → F2 (m + 1) := fun i => eVec i.castSucc
    have hli0 : LinearIndependent (ZMod 2) e0 := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hval := congr_fun hg i.castSucc
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, e0, eVec,
        Pi.single_apply, Fin.castSucc_inj] at hval
      simpa using hval
    have heval0 : ∀ u : F2 m, evalBasis e0 u = Fin.snoc u 0 := by
      intro u; ext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [evalBasis, e0, eVec, Fin.snoc_last, Fin.castSucc_ne_last]
      · simp [evalBasis, e0, eVec, Pi.single_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
    have hIH0 : SubspaceVal (fun u : F2 m => h (Fin.snoc u 0)) m := by
      have := subspaceVal_pullback hli0 hIH 0
      simpa [heval0] using this
    have hIH1 : SubspaceVal (fun u : F2 m => h (Fin.snoc u 1)) m := by
      have hsnoc1 : ∀ u : F2 m, eVec (Fin.last m) + evalBasis e0 u = Fin.snoc u 1 := by
        intro u; rw [heval0]; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [eVec, Fin.snoc_last]
        · simp [eVec, Fin.snoc_castSucc, Fin.castSucc_ne_last]
      have := subspaceVal_pullback hli0 hIH (eVec (Fin.last m))
      simpa [hsnoc1] using this
    have hd1 := pow_two_dvd_mobiusCoeff hIH1 hT
    have hd0 := pow_two_dvd_mobiusCoeff hIH0 hT
    rw [hcard] at hd1 hd0
    exact dvd_sub hd1 hd0

/-- Sublemma 5b (Product Sum Congruence): under `SubspaceVal h m` on `𝔽₂^(m+1)` (`m ≥ 1`),
    `2^(m - 1) ∣ ∑ u : F2 m, star (h (snoc u 0)) * (h (snoc u 1) - h (snoc u 0))`. -/
lemma pow_two_dvd_product_diff {m : ℕ} (hm : 1 ≤ m) {h : F2 (m + 1) → GI} (hIH : SubspaceVal h m) :
    ((2 : GI) ^ (m - 1)) ∣
      ∑ u : F2 m, star (h (Fin.snoc u 0)) * (h (Fin.snoc u 1) - h (Fin.snoc u 0)) := by
  let f : F2 m → GI := fun u => h (Fin.snoc u 0)
  let δ : F2 m → GI := fun u => h (Fin.snoc u 1) - h (Fin.snoc u 0)
  let e0 : Fin m → F2 (m + 1) := fun i => eVec i.castSucc
  have hli0 : LinearIndependent (ZMod 2) e0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hval := congr_fun hg i.castSucc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, e0, eVec,
      Pi.single_apply, Fin.castSucc_inj] at hval
    simpa using hval
  have heval0 : ∀ u : F2 m, evalBasis e0 u = Fin.snoc u 0 := by
    intro u; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [evalBasis, e0, eVec, Fin.snoc_last, Fin.castSucc_ne_last]
    · simp [evalBasis, e0, eVec, Pi.single_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
  have hIHf : SubspaceVal f m := by
    have := subspaceVal_pullback hli0 hIH 0
    simpa [f, heval0] using this
  have hexp : (∑ u : F2 m, star (f u) * δ u) =
      ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
        star (mobiusCoeff f S) * mobiusCoeff δ T * (2 : GI) ^ (m - (S ∪ T).card) := by
    have hstar_monom : ∀ (S : Finset (Fin m)) (u : F2 m), star (monom S u) = monom S u :=
      fun S u => by simp only [monom]; split_ifs <;> simp
    have hf_exp : ∀ u : F2 m, star (f u) = ∑ S : Finset (Fin m), star (mobiusCoeff f S) * monom S u := by
      intro u
      conv_lhs => rw [← mobius_inversion f u]
      rw [star_sum]
      refine Finset.sum_congr rfl fun S _ => by rw [star_mul, hstar_monom, mul_comm]
    calc ∑ u : F2 m, star (f u) * δ u
        = ∑ u : F2 m, (∑ S : Finset (Fin m), star (mobiusCoeff f S) * monom S u) *
            (∑ T : Finset (Fin m), mobiusCoeff δ T * monom T u) := by
          refine Finset.sum_congr rfl fun u _ => by rw [hf_exp u, mobius_inversion δ u]
      _ = ∑ u : F2 m, ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
            star (mobiusCoeff f S) * mobiusCoeff δ T * (monom S u * monom T u) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => by ring
      _ = ∑ S : Finset (Fin m), ∑ T : Finset (Fin m), ∑ u : F2 m,
            star (mobiusCoeff f S) * mobiusCoeff δ T * monom (S ∪ T) u := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun u _ => by rw [monom_mul]
      _ = ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
            star (mobiusCoeff f S) * mobiusCoeff δ T * (2 : GI) ^ (m - (S ∪ T).card) := by
          refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.mul_sum, sum_monom]
  change ((2 : GI) ^ (m - 1)) ∣ ∑ u : F2 m, star (f u) * δ u
  rw [hexp]
  refine Finset.dvd_sum fun S _ => Finset.dvd_sum fun T _ => ?_
  have hstar_dvd : ∀ (r : ℕ) (z : GI), ((2 : GI) ^ r) ∣ z → ((2 : GI) ^ r) ∣ star z := by
    intro r z ⟨w, hw⟩
    refine ⟨star w, ?_⟩
    rw [hw, star_mul, mul_comm]
    have h2 : star ((2 : GI) ^ r) = (2 : GI) ^ r := by
      rw [gi_two_pow_eq_mk]; ext <;> simp
    rw [h2]
  have hunion_le : (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
  have hunion_m : (S ∪ T).card ≤ m := by simpa using Finset.card_le_univ (S ∪ T)
  by_cases hT0 : T = ∅
  · subst hT0
    by_cases hS0 : S = ∅
    · subst hS0
      simp only [Finset.union_empty, Finset.card_empty, Nat.sub_zero]
      exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega)) _
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
      obtain ⟨wS, hwS⟩ := hstar_dvd (S.card - 1) _ (pow_two_dvd_mobiusCoeff hIHf hSne)
      rw [hwS, Finset.union_empty]
      have hSpos := Finset.card_pos.mpr hSne
      have hSle : S.card ≤ m := by simpa using Finset.card_le_univ S
      have hexp_eq : (2 : GI) ^ (S.card - 1) * (2 : GI) ^ (m - S.card) = (2 : GI) ^ (m - 1) := by
        rw [← pow_add, show S.card - 1 + (m - S.card) = m - 1 by omega]
      exact ⟨wS * mobiusCoeff δ ∅, by rw [← hexp_eq]; ring⟩
  · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT0
    have hdT := pow_two_dvd_mobiusCoeff_diff hIH hTne
    by_cases hTlt : T.card < m
    · simp only [hTlt, ↓reduceIte] at hdT
      obtain ⟨wT, hwT⟩ := hdT
      change mobiusCoeff δ T = (2 : GI) ^ T.card * wT at hwT
      by_cases hS0 : S = ∅
      · subst hS0
        simp only [Finset.empty_union]
        rw [hwT]
        have hexp_ge : (2 : GI) ^ (m - 1) ∣ (2 : GI) ^ T.card * (2 : GI) ^ (m - T.card) := by
          rw [← pow_add]; exact pow_dvd_pow 2 (by omega)
        obtain ⟨k, hk⟩ := hexp_ge
        exact ⟨star (mobiusCoeff f ∅) * wT * k, by
          calc star (mobiusCoeff f ∅) * ((2 : GI) ^ T.card * wT) * (2 : GI) ^ (m - T.card)
              = star (mobiusCoeff f ∅) * wT * ((2 : GI) ^ T.card * (2 : GI) ^ (m - T.card)) := by ring
            _ = star (mobiusCoeff f ∅) * wT * ((2 : GI) ^ (m - 1) * k) := by rw [hk]
            _ = (2 : GI) ^ (m - 1) * (star (mobiusCoeff f ∅) * wT * k) := by ring⟩
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        obtain ⟨wS, hwS⟩ := hstar_dvd (S.card - 1) _ (pow_two_dvd_mobiusCoeff hIHf hSne)
        rw [hwS, hwT]
        have hSpos := Finset.card_pos.mpr hSne
        have hsum_ge : m - 1 ≤ (S.card - 1) + T.card + (m - (S ∪ T).card) := by omega
        obtain ⟨k, hk⟩ := pow_dvd_pow (2 : GI) hsum_ge
        exact ⟨wS * wT * k, by
          have hp : (2 : GI) ^ (S.card - 1) * (2 : GI) ^ T.card * (2 : GI) ^ (m - (S ∪ T).card) =
              (2 : GI) ^ ((S.card - 1) + T.card + (m - (S ∪ T).card)) := by rw [pow_add, pow_add]
          calc ((2 : GI) ^ (S.card - 1) * wS) * ((2 : GI) ^ T.card * wT) * (2 : GI) ^ (m - (S ∪ T).card)
              = wS * wT * ((2 : GI) ^ (S.card - 1) * (2 : GI) ^ T.card * (2 : GI) ^ (m - (S ∪ T).card)) := by ring
            _ = wS * wT * ((2 : GI) ^ (m - 1) * k) := by rw [hp, hk]
            _ = (2 : GI) ^ (m - 1) * (wS * wT * k) := by ring⟩
    · simp only [hTlt, ↓reduceIte] at hdT
      obtain ⟨wT, hwT⟩ := hdT
      change mobiusCoeff δ T = (2 : GI) ^ (m - 1) * wT at hwT
      rw [hwT]
      exact ⟨star (mobiusCoeff f S) * wT * (2 : GI) ^ (m - (S ∪ T).card), by ring⟩

/-- Induction step: `SubspaceVal η m` + `CorrCongr η m` implies `SubspaceVal η (m + 1)`. -/
lemma subspaceVal_step {n m : ℕ} (hm : 1 ≤ m) {η : F2 n → GI}
    (hIH : SubspaceVal η m) (hCorr : CorrCongr η m) :
    SubspaceVal η (m + 1) := by
  intro r hr1 hrm1 W hW v₀
  by_cases hrle : r ≤ m
  · exact hIH r hr1 hrle W hW v₀
  · have hr : r = m + 1 := by omega
    subst hr
    simp only [Nat.add_sub_cancel]
    let bW := Module.finBasisOfFinrankEq (ZMod 2) W hW
    let eExt : Fin (m + 1) → F2 n := fun j => (bW j).1
    have hliExt : LinearIndependent (ZMod 2) eExt := by
      have := bW.linearIndependent
      exact LinearIndependent.map' this W.subtype (Submodule.ker_subtype W)
    let e : Fin m → F2 n := fun i => eExt i.castSucc
    let b : F2 n := eExt (Fin.last m)
    have hli : LinearIndependent (ZMod 2) e := hliExt.comp Fin.castSucc (Fin.castSucc_injective m)
    let V : Submodule (ZMod 2) (F2 n) := Submodule.span (ZMod 2) (Set.range e)
    have hfinV : Module.finrank (ZMod 2) V = m := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    let h : F2 (m + 1) → GI := fun w => η (v₀ + evalBasis eExt w)
    have hIH_h : SubspaceVal h m := subspaceVal_pullback hliExt hIH v₀
    have heqV : ∀ u : F2 m, evalBasis eExt (Fin.snoc u 0) = evalBasis e u := by
      intro u
      simp only [evalBasis, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, e]
    have heqVb : ∀ u : F2 m, evalBasis eExt (Fin.snoc u 1) = evalBasis e u + b := by
      intro u
      simp only [evalBasis, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, one_smul, e, b]
    -- Biject `F2 m ≃ V` via `evalBasis e`
    have hmemV : ∀ u : F2 m, evalBasis e u ∈ V := fun u =>
      show (∑ i : Fin m, u i • e i) ∈ V from
        V.sum_mem fun i _ => V.smul_mem (u i) (Submodule.subset_span ⟨i, rfl⟩)
    let bV := Module.Basis.span hli
    have hsurjV : ∀ v : V, ∃ u : F2 m, evalBasis e u = v.1 := fun v => by
      refine ⟨bV.repr v, ?_⟩
      have hsum := congr_arg Subtype.val (bV.sum_repr v)
      rw [Submodule.coe_sum] at hsum
      simpa [evalBasis, bV] using hsum
    let eqV : F2 m ≃ V :=
      { toFun := fun u => ⟨evalBasis e u, hmemV u⟩
        invFun := fun v => (hsurjV v).choose
        left_inv := fun u => evalBasis_injective hli (hsurjV ⟨evalBasis e u, hmemV u⟩).choose_spec
        right_inv := fun v => Subtype.ext (hsurjV v).choose_spec }
    -- Biject `F2 (m + 1) ≃ W` via `evalBasis eExt`
    have hmemW : ∀ w : F2 (m + 1), evalBasis eExt w ∈ W := fun w =>
      show (∑ j : Fin (m + 1), w j • eExt j) ∈ W from
        W.sum_mem fun j _ => W.smul_mem (w j) (bW j).2
    have hsurjW : ∀ v : W, ∃ w : F2 (m + 1), evalBasis eExt w = v.1 := fun v => by
      refine ⟨bW.repr v, ?_⟩
      have hsum := congr_arg Subtype.val (bW.sum_repr v)
      rw [Submodule.coe_sum] at hsum
      simpa [evalBasis, eExt] using hsum
    let eqW : F2 (m + 1) ≃ W :=
      { toFun := fun w => ⟨evalBasis eExt w, hmemW w⟩
        invFun := fun v => (hsurjW v).choose
        left_inv := fun w => evalBasis_injective hliExt (hsurjW ⟨evalBasis eExt w, hmemW w⟩).choose_spec
        right_inv := fun v => Subtype.ext (hsurjW v).choose_spec }
    -- Translate `∑ w : W, η (v₀ + w.1)` to `∑ u : V, (η (v₀ + u.1) + η (v₀ + u.1 + b))`
    have hsumW : (∑ w : W, η (v₀ + w.1)) = ∑ u : V, (η (v₀ + u.1) + η (v₀ + u.1 + b)) := by
      rw [← Fintype.sum_equiv eqW _ _ (fun _ => rfl)]
      let eSplit : (F2 m × ZMod 2) ≃ F2 (m + 1) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun w => (fun i => w i.castSucc, w (Fin.last m))
          left_inv := fun ⟨u, t⟩ => by
            ext i
            · simp [Fin.snoc_castSucc]
            · simp [Fin.snoc_last]
          right_inv := fun w => by
            ext j; refine Fin.lastCases (by simp [Fin.snoc_last]) (fun i => by simp [Fin.snoc_castSucc]) j }
      rw [← Fintype.sum_equiv eSplit _ _ (fun _ => rfl), Fintype.sum_prod_type]
      have h2 : ∀ u : F2 m, (∑ t : ZMod 2, η (v₀ + (eqW (eSplit (u, t))).1)) =
          η (v₀ + evalBasis e u) + η (v₀ + evalBasis e u + b) := fun u => by
        rw [sum_zmod2]
        change η (v₀ + evalBasis eExt (Fin.snoc u 0)) + η (v₀ + evalBasis eExt (Fin.snoc u 1)) = _
        rw [heqV, heqVb, add_assoc]
      simp_rw [h2]
      exact Fintype.sum_equiv eqV _ _ (fun _ => rfl)
    have hprod_diff : ((2 : GI) ^ (m - 1)) ∣
        ∑ u : V, star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1)) := by
      have hd := pow_two_dvd_product_diff hm hIH_h
      have htr : (∑ u : F2 m, star (h (Fin.snoc u 0)) * (h (Fin.snoc u 1) - h (Fin.snoc u 0))) =
          ∑ u : V, star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1)) := by
        refine Fintype.sum_equiv eqV _ _ fun u => ?_
        simp [h, eqV, heqV, heqVb, add_assoc]
      rwa [htr] at hd
    have hV_ih : ((2 : GI) ^ (m - 1)) ∣ ∑ u : V, η (v₀ + u.1) := hIH m hm le_rfl V hfinV v₀
    have hC0 := hCorr V hfinV v₀ 0
    simp only [add_zero] at hC0
    have hCb := hCorr V hfinV v₀ b
    have h2re : ((2 : GI) ^ m) ∣ ∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1)) := by
      rw [pow_two_dvd_gi_iff] at hV_ih ⊢
      have hre_sum : (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1))).re =
          2 * (∑ u : V, η (v₀ + u.1)).re := by
        simp only [gi_sum_re, Zsqrtd.re_add, gi_star_re, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => by ring
      have him_sum : (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1))).im = 0 := by
        simp only [gi_sum_im, Zsqrtd.im_add, gi_star_im]
        exact Finset.sum_eq_zero fun u _ => by ring
      rw [hre_sum, him_sum]
      refine ⟨?_, dvd_zero _⟩
      have : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
      rw [this]
      exact mul_dvd_mul_left 2 hV_ih.1
    have hnorm : ((2 : GI) ^ m) ∣ ∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1) := by
      have hsplit : ∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1) +
          (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1)) =
          (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1))) +
          (∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1)) := Finset.sum_add_distrib
      rw [hsplit] at hC0
      exact (dvd_add_right h2re).mp hC0
    have h2prod_diff : ((2 : GI) ^ m) ∣
        ∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1)) := by
      have : (2 : GI) ^ m = (2 : GI) * (2 : GI) ^ (m - 1) := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
      rw [this]
      have hmul : ∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1)) =
          (2 : GI) * ∑ u : V, star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
      rw [hmul]
      exact mul_dvd_mul_left 2 hprod_diff
    have h2prod_b : ((2 : GI) ^ m) ∣ ∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1 + b) := by
      have heq : (∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)) =
          (∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1)) +
          (∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * (η (v₀ + u.1 + b) - η (v₀ + u.1))) := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun u _ => by ring
      rw [heq]
      exact dvd_add hnorm h2prod_diff
    have hlin_b : ((2 : GI) ^ m) ∣ ∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b)) := by
      have hsplit : ∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b) +
          (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)) =
          (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b))) +
          (∑ u : V, (2 : GI) * star (η (v₀ + u.1)) * η (v₀ + u.1 + b)) := Finset.sum_add_distrib
      rw [hsplit] at hCb
      exact (dvd_add_left h2prod_b).mp hCb
    rw [hsumW, pow_two_dvd_gi_iff]
    rw [pow_two_dvd_gi_iff] at hlin_b hV_ih
    constructor
    · have hre : (∑ u : V, (η (v₀ + u.1) + η (v₀ + u.1 + b))).re =
          (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b))).re := by
        simp only [gi_sum_re, Zsqrtd.re_add, gi_star_re]
      rw [hre]; exact hlin_b.1
    · have him : (∑ u : V, (η (v₀ + u.1) + η (v₀ + u.1 + b))).im =
          2 * (∑ u : V, η (v₀ + u.1)).im + (∑ u : V, (star (η (v₀ + u.1)) + η (v₀ + u.1 + b))).im := by
        simp only [gi_sum_im, Zsqrtd.im_add, gi_star_im, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => by ring
      rw [him]
      have h2im : (2 : ℤ) ^ m ∣ 2 * (∑ u : V, η (v₀ + u.1)).im := by
        have : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
          rw [← pow_succ', show m - 1 + 1 = m by omega]
        rw [this]
        exact mul_dvd_mul_left 2 hV_ih.2
      exact dvd_add h2im hlin_b.2

/-- Full induction: if `CorrCongr η r` holds for all `1 ≤ r ≤ M`, then `SubspaceVal η (M + 1)` holds! -/
lemma subspaceVal_of_corrCongr {n : ℕ} {η : F2 n → GI} (M : ℕ)
    (hCorr : ∀ r : ℕ, 1 ≤ r → r ≤ M → CorrCongr η r) :
    SubspaceVal η (M + 1) := by
  induction M with
  | zero =>
    intro r hr1 hrle U _ v₀
    have hr : r = 1 := by omega
    subst hr; simp
  | succ M ih =>
    have hIH := ih (fun r hr1 hrle => hCorr r hr1 (by omega))
    exact subspaceVal_step (by omega) hIH (hCorr (M + 1) (by omega) le_rfl)

/-- Final WHT congruence: if `SubspaceVal η (n - 1)` holds for `n ≥ 2` and `w u = 1 + 2 * η u`,
    then `2^n ∣ (∑ u, χ(u, x) w(u)) - (∑ u, χ(u, y) w(u))` for all `x, y : 𝔽₂ⁿ`. -/
lemma pow_two_dvd_wht_sub_of_subspaceVal {n : ℕ} (hn : 2 ≤ n) {η : F2 n → GI}
    (hIH : SubspaceVal η (n - 1)) (x y : F2 n) :
    ((2 : GI) ^ n) ∣
      ((∑ u : F2 n, (chi u x : GI) * (1 + 2 * η u)) -
       (∑ u : F2 n, (chi u y : GI) * (1 + 2 * η u))) := by
  have hconst : ∀ z : F2 n,
      ((2 : GI) ^ n) ∣ ((∑ u : F2 n, (chi u z : GI) * (1 + 2 * η u)) - 2 * ∑ u : F2 n, η u) := by
    intro z
    have hsplit : (∑ u : F2 n, (chi u z : GI) * (1 + 2 * η u)) =
        (∑ u : F2 n, (chi u z : GI)) + 2 * (∑ u : F2 n, (chi u z : GI) * η u) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => by ring
    rw [hsplit]
    have h1 : ((2 : GI) ^ n) ∣ ∑ u : F2 n, (chi u z : GI) := by
      rw [← Int.cast_sum, sum_chi]
      split_ifs
      · simp
      · simp
    rw [wht_eq_subcube_sum η z]
    have h2 : 2 * (∑ T : Finset (Fin n), (-2 : GI) ^ T.card * monom T z * ∑ u : F2 n, monom T u * η u) -
        2 * ∑ u : F2 n, η u =
        ∑ T ∈ Finset.univ.erase (∅ : Finset (Fin n)),
          2 * ((-2 : GI) ^ T.card * monom T z * ∑ u : F2 n, monom T u * η u) := by
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n)))]
      have hemp : monom (∅ : Finset (Fin n)) z = 1 ∧ ∀ u, monom (∅ : Finset (Fin n)) u = 1 :=
        ⟨by simp [monom], fun u => by simp [monom]⟩
      simp [hemp.1, hemp.2]
    rw [add_sub_assoc]
    refine dvd_add h1 ?_
    rw [h2]
    refine Finset.dvd_sum fun T hT => ?_
    have hTne : T ≠ ∅ := (Finset.mem_erase.mp hT).1
    have hTpos : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTne)
    have hTle : T.card ≤ n := by simpa using Finset.card_le_univ T
    by_cases hfull : T.card = n
    · have hdiv : ((2 : GI) ^ n) ∣ (-2 : GI) ^ T.card := by
        rw [hfull, show (-2 : GI) = (-1 : GI) * 2 by ring, mul_pow]
        exact dvd_mul_left _ _
      obtain ⟨k, hk⟩ := hdiv
      exact ⟨2 * k * monom T z * ∑ u : F2 n, monom T u * η u, by rw [hk]; ring⟩
    · have hdim : 1 ≤ n - T.card ∧ n - T.card ≤ n - 1 := by omega
      have hsub_sum : (∑ u : F2 n, monom T u * η u) =
          ∑ u : coordSubspace Tᶜ, η (indVec T + u.1) := by
        have hfilt : (∑ u : F2 n, monom T u * η u) =
            ∑ u ∈ Finset.univ.filter (fun u : F2 n => T ⊆ supp u), η u := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [monom_eq_ite_subset]; split_ifs <;> simp
        rw [hfilt]
        have hsubt : (∑ u : {u : F2 n // T ⊆ supp u}, η u.1) =
            ∑ u ∈ Finset.univ.filter (fun u : F2 n => T ⊆ supp u), η u :=
          (Finset.sum_subtype (Finset.univ.filter (fun u : F2 n => T ⊆ supp u))
            (fun u => by simp) η).symm
        rw [← hsubt]
        let e : coordSubspace Tᶜ ≃ {u : F2 n // T ⊆ supp u} :=
          { toFun := fun ⟨u, hu⟩ => ⟨indVec T + u, by
              intro i hi
              rw [mem_supp_iff, Pi.add_apply]
              have hu0 : u i = 0 := hu i (by simp [hi])
              simp [indVec, hi, hu0]⟩
            invFun := fun ⟨u, hu⟩ => ⟨indVec T + u, by
              intro i hi
              simp only [Finset.mem_compl, not_not] at hi
              rw [Pi.add_apply, mem_supp_iff.mp (hu hi)]
              simp only [indVec, hi, ↓reduceIte]
              decide⟩
            left_inv := fun ⟨u, _⟩ => Subtype.ext (f2_add_cancel_left (indVec T) u)
            right_inv := fun ⟨u, _⟩ => Subtype.ext (f2_add_cancel_left (indVec T) u) }
        exact (Fintype.sum_equiv e (fun u => η (indVec T + u.1)) (fun u => η u.1) (fun _ => rfl)).symm
      have hfin_compl : Module.finrank (ZMod 2) (coordSubspace Tᶜ) = n - T.card := by
        rw [finrank_coordSubspace, Finset.card_compl, Fintype.card_fin]
      have hd_sub := hIH (n - T.card) hdim.1 hdim.2 (coordSubspace Tᶜ) hfin_compl (indVec T)
      rw [← hsub_sum] at hd_sub
      obtain ⟨w, hw⟩ := hd_sub
      rw [hw, show (-2 : GI) = (-1 : GI) * 2 by ring, mul_pow]
      have hexp : (2 : GI) * (2 : GI) ^ T.card * (2 : GI) ^ (n - T.card - 1) = (2 : GI) ^ n := by
        rw [← pow_succ', ← pow_add, show T.card + 1 + (n - T.card - 1) = n by omega]
      exact ⟨(-1 : GI) ^ T.card * monom T z * w, by rw [← hexp]; ring⟩
  have hx := hconst x
  have hy := hconst y
  have := dvd_sub hx hy
  simpa using this

end MultiQubitMUB
