import MultiQubitMUB.FourQubitUnconditionalMUB

/-!
# Exact 4-Qubit Symplectic Contextuality Degrees: `CD(Q⁻(7,2)) = 315` and `CD(W(7,2)) = 1575`

Closes the upper and lower bounds into **exact equalities** (zero `sorry`, zero `native_decide`,
standard three Lean axioms `[propext, Classical.choice, Quot.sound]` only):

1. `cd_Qminus72_eq_315`: For EVERY elliptic quadric `Q⁻(7,2)` (`c ∈ ellCenters 4`, all 120 centers),
   - `∀ s, IsSignAssign s → 315 * 6 ≤ frustPairs (Qminus c) s`, and
   - `∃ s, IsSignAssign s ∧ frustPairs (Qminus c) s = 315 * 6` (simultaneously attained on all 120 quadrics
     by the explicit spike sign assignment `spikeSign4`).
2. `cd_W72_eq_1575`: On the full 4-qubit symplectic polar space `W(7,2)`,
   - `∀ s, IsSignAssign s → 1575 * 6 ≤ frustPairs (nzPts 4) s`, and
   - `∃ s, IsSignAssign s ∧ frustPairs (nzPts 4) s = 1575 * 6`.
3. `signCubeSum_four_max_eq_6615`:
   The maximum of `signCubeSum 4 σ` over all `±1` Pauli sign assignments equals **exactly `6615`**.
-/

namespace MultiQubitMUB

open FourQubitCD

namespace FourQubitCDExact

set_option maxRecDepth 20000 in
private lemma orb1_allPats_covered' :
    (orb1_allPats.all fun p => ((orb1_trees_a ++ orb1_trees_b ++ orb1_trees_c).map Prod.fst).contains p) = true := by
  rfl

set_option maxRecDepth 20000 in
private lemma orb2_allPats_covered' :
    (orb2_allPats.all fun p => ((orb2_trees_a ++ orb2_trees_b).map Prod.fst).contains p) = true := by
  rfl

/-- Unconditional lower bound `CD(Q⁻(7,2)) ≥ 315` on the canonical elliptic quadric `Qminus c0_88`. -/
private theorem frustPairs_Qminus88_ge_315 {s4 : PauliIdx 4 → ℤ} (hs4 : IsSignAssign s4) :
    315 * 6 ≤ frustPairs (Qminus c0_88) s4 := by
  by_contra hlt; push Not at hlt
  -- Step 1: Move the minimum hyperplane slice to `c0_88` via `O⁻(8,2)` transvections.
  have hne_out : (outPts c0_88).Nonempty := ⟨c0_88, by
    rw [outPts, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [quadForm, symp_self, add_zero]; exact quadForm0_c0_88⟩⟩
  obtain ⟨po, hpo_mem, hpo_min⟩ := Finset.exists_min_image (outPts c0_88)
    (fun p => frustPairs (slicePts c0_88 p) s4) hne_out
  obtain ⟨us4, _, hus4⟩ := exists_Ominus_word_pout_to_88 hpo_mem
  let s4' := applyTransvWord us4 s4
  have hs4' : IsSignAssign s4' := applyTransvWord_isSignAssign us4 hs4
  obtain ⟨hQeq, _, hmin'⟩ := hus4 s4
  have hmin_s4' := hmin' hpo_min
  have hQlt' : frustPairs (Qminus c0_88) s4' < 315 * 6 := by rw [hQeq]; exact hlt
  have hcard_out : (outPts c0_88).card = 136 := by
    have hcardQ := card_elliptic_quadric (n := 4) (by norm_num) quadForm0_c0_88
    have h256 : (Finset.univ : Finset (PauliIdx 4)).card = 256 := by
      rw [Finset.card_univ, card_PauliIdx]; norm_num
    have hpart : (outPts c0_88).card + (Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0).card = 256 := by
      rw [← h256, ← Finset.card_union_of_disjoint]
      · refine congr_arg Finset.card (Finset.ext fun p => ?_)
        simp only [outPts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases zmod2_cases (quadForm c0_88 p) with h | h <;> simp [h]
      · rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [outPts, Finset.mem_filter] at hp1 hp2
        rw [hp1.2] at hp2; exact absurd hp2.2 (by decide)
    have hQ0 : (Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0).card =
        (Finset.univ.filter fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0_88 p = 0).card + 1 := by
      have hmem0 : (0 : PauliIdx 4) ∈ Finset.univ.filter fun p : PauliIdx 4 => quadForm c0_88 p = 0 := by
        simp [quadForm_zero]
      rw [← Finset.card_erase_add_one hmem0]
      refine congr_arg (· + 1) (congr_arg Finset.card (Finset.ext fun p => ?_))
      simp [and_comm]
    have h119 : (Finset.univ.filter fun p : PauliIdx 4 => p ≠ 0 ∧ quadForm c0_88 p = 0).card = 119 := by
      norm_num at hcardQ; exact_mod_cast hcardQ
    omega
  have hsum_sl : 136 * frustPairs (slicePts c0_88 c0_88) s4' ≤ 40 * frustPairs (Qminus c0_88) s4' := by
    rw [double_count_Qminus72_slices quadForm0_c0_88 s4', ← hcard_out, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun p hp => hmin_s4' p hp
  have hdvd_Q : 6 ∣ frustPairs (Qminus c0_88) s4' := by
    refine dvd_six_frustPairs (Qminus c0_88) (by simp [Qminus, nzPts]) ?_ s4'
    intro p hp q hq hne hs
    simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
    refine ⟨fun h => hne (by
      have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm), ?_⟩
    rw [quadForm_add, hp.2, hq.2, hs]; simp
  have hdvd_A : 6 ∣ frustPairs (nzPts 3) (restrictA s4') := by
    refine dvd_six_frustPairs (nzPts 3) (by simp [nzPts]) ?_ (restrictA s4')
    intro p _ q _ hne _
    simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; exact hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  rw [frustPairs_slice_eq_restrictA] at hsum_sl
  have hfA_le : frustPairs (nzPts 3) (restrictA s4') ≤ 92 * 6 := by
    obtain ⟨kQ, hkQ⟩ := hdvd_Q; obtain ⟨kA, hkA⟩ := hdvd_A; omega
  -- Step 2: Move the minimum `Q⁻(5,2)` inside `W(5,2)` to `c0_09` via lifted 3-qubit transvection.
  have hne_c3 : (ellCenters 3).Nonempty := ⟨c0_09, by
    rw [ellCenters, Finset.mem_filter]; exact ⟨Finset.mem_univ _, quadForm0_c0_09⟩⟩
  obtain ⟨c3, hc3_mem, hc3_min⟩ := Finset.exists_min_image (ellCenters 3)
    (fun c => frustPairs (Qminus c) (restrictA s4')) hne_c3
  let s4'' := liftTransv3 (c3 + c0_09) s4'
  have hs4'' : IsSignAssign s4'' := liftTransv3_isSignAssign _ hs4'
  have hQlt'' : frustPairs (Qminus c0_88) s4'' < 315 * 6 := by
    rw [liftTransv3_preserves_Qminus]; exact hQlt'
  have hmin'' := liftTransv3_preserves_minSlice (c3 + c0_09) hmin_s4'
  have hres'' : restrictA s4'' = applyTransv (c3 + c0_09) (restrictA s4') :=
    liftTransv3_restrictA _ _
  have hfA_eq'' : frustPairs (nzPts 3) (restrictA s4'') = frustPairs (nzPts 3) (restrictA s4') := by
    rw [hres'']
    refine frustPairs_applyTransv (c3 + c0_09) (nzPts 3) (nzPts 3) (fun p => ?_) (restrictA s4')
    simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun hp0 h => hp0 (by rw [← transvPt_invol _ p, h, transvPt_zero]),
           fun ht0 h => ht0 (by rw [h, transvPt_zero])⟩
  have hfA_le'' : frustPairs (nzPts 3) (restrictA s4'') ≤ 92 * 6 := by rw [hfA_eq'']; exact hfA_le
  have hc3_Q0 : quadForm0 c3 = 1 := (Finset.mem_filter.mp hc3_mem).2
  have hmin_c3'' : ∀ c ∈ ellCenters 3,
      frustPairs (Qminus c0_09) (restrictA s4'') ≤ frustPairs (Qminus c) (restrictA s4'') := by
    intro c hc
    rw [hres'', ← frustPairs_Qminus_eq_of_ellCenter hc3_Q0 quadForm0_c0_09]
    let u := c3 + c0_09
    rcases zmod2_cases (quadForm c u) with hcu | hcu
    · have hc'_mem : c + u ∈ ellCenters 3 := by
        simp only [ellCenters, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        have hq : quadForm c u = 0 := hcu
        rw [quadForm0_add, hc]
        have : quadForm0 u + symp c u = 0 := hq
        rw [add_assoc, this, add_zero]
      have hmap : frustPairs (Qminus c) (applyTransv u (restrictA s4')) =
          frustPairs (Qminus (c + u)) (restrictA s4') := by
        refine frustPairs_applyTransv u (Qminus c) (Qminus (c + u)) (fun p => ?_) _
        simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
        have hm : quadForm (c + u) (transvPt u p) = quadForm c p := by
          have := quadForm_transvPt_move hcu (transvPt u p)
          rw [transvPt_invol] at this; exact this.symm
        rw [hm]
        exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
               fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
      rw [hmap]; exact hc3_min (c + u) hc'_mem
    · have hmap : frustPairs (Qminus c) (applyTransv u (restrictA s4')) =
          frustPairs (Qminus c) (restrictA s4') := by
        refine frustPairs_applyTransv u (Qminus c) (Qminus c) (fun p => ?_) _
        simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
          quadForm_transvPt_fix hcu]
        exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
               fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
      rw [hmap]; exact hc3_min c hc
  have hcard_c3 : (ellCenters 3).card = 28 := by
    have hZ := card_elliptic_centers (n := 3) (by norm_num)
    norm_num at hZ; exact_mod_cast hZ
  have hsum_28 : 28 * frustPairs (Qminus c0_09) (restrictA s4'') ≤ 4 * frustPairs (nzPts 3) (restrictA s4'') := by
    rw [double_count_W52_Qminus52, ← hcard_c3, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => hmin_c3'' c hc
  have hdvd_27 : 6 ∣ frustPairs (Qminus c0_09) (restrictA s4'') := by
    refine dvd_six_frustPairs (Qminus c0_09) (by simp [Qminus, nzPts]) ?_ _
    intro p hp q hq hne hs
    simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
    refine ⟨fun h => hne (by
      have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm), ?_⟩
    rw [quadForm_add, hp.2, hq.2, hs]; simp
  have hf27_le : frustPairs (Qminus c0_09) (restrictA s4'') ≤ 13 * 6 := by
    obtain ⟨k27, hk27⟩ := hdvd_27; omega
  -- Step 3: Classify `restrictA s4''` via Parts 1–3 (`sp42Certs`) and contradict `hQlt''`!
  let s3 := restrictA s4''
  have hs3 : IsSignAssign s3 := restrictA_isSignAssign hs4''
  obtain ⟨r, us1, g1, hus1_Q, hmatch1⟩ := qminus52_le13_classified hs3 hf27_le
  let s3' := applyGauge g1 (applyTransvWord us1 s3)
  have hs3' : IsSignAssign s3' := applyGauge_isSignAssign g1 (applyTransvWord_isSignAssign us1 hs3)
  have hfeq1 : w5FrustEq s3' (applyTransvWord us1 s3) := w5FrustEq_applyGauge g1 _
  have hfA' : frustPairs (nzPts 3) s3' ≤ 92 * 6 := by
    rw [frustPairs_of_w5FrustEq (by simp [nzPts]) hfeq1, frustPairs_nzPts_applyTransvWord]
    exact hfA_le''
  have hmin3' : isMinQminus09 s3' :=
    isMinQminus09_of_w5FrustEq (w5FrustEq_symm hfeq1)
      (isMinQminus09_applyTransvWord_Ominus hus1_Q hmin_c3'')
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
        orb1_stab_covers htrees1 orb1_allPats_covered'
        hs3' hmatch1 hfA' hmin3'
    · have ho2 : orb2_O12 = [1, 3, 6, 7, 10, 11, 20, 24, 25, 28, 32, 33] := rfl
      have htrees2 : checkPatList (if (⟨2, by decide⟩ : Fin 3).val = 1 then orb1_tables else orb2_tables)
          orb2_O12 (orb2_trees_a ++ orb2_trees_b) = true := by
        simp only [show ¬((2 : Nat) = 1) by decide, ↓reduceIte]
        rw [checkPatList_append, ho2, orb2_trees_a_valid, orb2_trees_b_valid]
        rfl
      exact orbit_dpll_hits_sp42 ⟨2, by decide⟩ (Or.inr rfl) orb2_O12 orb2_stab orb2_allPats
        (orb2_trees_a ++ orb2_trees_b)
        orb2_stab_covers htrees2 orb2_allPats_covered'
        hs3' hmatch1 hfA' hmin3'
  obtain ⟨spId, us2, hfeq2⟩ := hhit
  have hfeqTot : w5FrustEq (applyTransvWord (us1 ++ us2) (restrictA s4''))
      (listToSign3 (sp42Certs spId).s64) := by
    rw [applyTransvWord_append]
    exact w5FrustEq_trans (w5FrustEq_applyTransvWord us2 (w5FrustEq_symm hfeq1)) hfeq2
  have h315 := cd315_of_hits_cert (sp42Certs spId) (sp42Certs_valid spId) hs4'' hmin'' (us1 ++ us2) hfeqTot
  omega

/-- Explicit 4-qubit spike sign assignment (`+1` on pure-`X`/`Z` axes, `-1` elsewhere)
    achieving `CD(W(7,2)) = 1575` and `CD(Q⁻(7,2)) = 315` simultaneously on ALL 120 elliptic quadrics! -/
def spikeSign4 (p : PauliIdx 4) : ℤ :=
  if p = 0 then 0 else if p.1 = 0 ∨ p.2 = 0 then 1 else -1

lemma spikeSign4_isSignAssign : IsSignAssign spikeSign4 := by
  refine ⟨by simp [spikeSign4], fun p hp => ?_⟩
  simp only [spikeSign4, hp, ↓reduceIte]
  split_ifs <;> simp

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma card_F2_4 : (Finset.univ : Finset (F2 4)).card = 16 := by
  rw [Finset.card_univ, Fintype.card_pi]; simp [ZMod.card]

private lemma dot_add_right_4 (u x y : F2 4) : dot u (x + y) = dot u x + dot u y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_zero_right_4 (u : F2 4) : dot u 0 = 0 := by
  simp [dot]

private lemma dot_eb_4 (u : F2 4) (i : Fin 4) : dot u (fun k => if k = i then (1 : ZMod 2) else 0) = u i := by
  simp [dot]

private lemma exists_coord_one_4 {u : F2 4} (hu : u ≠ 0) : ∃ i : Fin 4, u i = 1 := by
  by_contra hall; push Not at hall
  exact hu (funext fun i => (zmod2_cases (u i)).resolve_right (hall i))

private lemma card_dot_eq_4 {u : F2 4} (hu : u ≠ 0) (c : ZMod 2) :
    (Finset.univ.filter fun v : F2 4 => dot u v = c).card = 8 := by
  obtain ⟨i, hi⟩ := exists_coord_one_4 hu
  let ei : F2 4 := fun k => if k = i then 1 else 0
  have hdei : dot u ei = 1 := by simpa [ei] using (dot_eb_4 u i).trans hi
  have heq : (Finset.univ.filter fun v : F2 4 => dot u v = 0).card =
      (Finset.univ.filter fun v : F2 4 => dot u v = 1).card := by
    refine Finset.card_bij (fun v _ => v + ei) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [dot_add_right_4, hv, hdei, zero_add]
    · intro v1 _ v2 _ h
      ext k; have hk := congr_fun h k
      have := congr_arg (· + ei k) hk
      simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at this
      exact this
    · intro w hw
      refine ⟨w + ei, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [dot_add_right_4, hw, hdei]; decide
      · ext k; simp [Pi.add_apply, add_assoc, zmod2_add_self]
  have hpart : (Finset.univ.filter fun v : F2 4 => dot u v = 0).card +
      (Finset.univ.filter fun v : F2 4 => dot u v = 1).card = 16 := by
    rw [← Finset.card_union_of_disjoint, ← card_F2_4]
    · refine congr_arg Finset.card (Finset.ext fun v => ?_)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_cases (dot u v)
    · rw [Finset.disjoint_left]; intro v h0 h1
      simp only [Finset.mem_filter] at h0 h1
      rw [h0.2] at h1; exact absurd h1.2 (by decide)
  rcases zmod2_cases c with rfl | rfl <;> omega

private lemma card_dot2_eq_4 {u v : F2 4} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (c1 c2 : ZMod 2) :
    (Finset.univ.filter fun w : F2 4 => dot u w = c1 ∧ dot v w = c2).card = 4 := by
  have hex : ∃ (e1 e2 : F2 4), dot u e1 = 1 ∧ dot v e1 = 0 ∧ dot u e2 = 0 ∧ dot v e2 = 1 := by
    have hdiff : ∃ i : Fin 4, u i ≠ v i := by
      by_contra h; push Not at h; exact huv (funext h)
    obtain ⟨i, hi⟩ := hdiff
    let eb : Fin 4 → F2 4 := fun t k => if k = t then 1 else 0
    have hdb : ∀ (x : F2 4) (t : Fin 4), dot x (eb t) = x t := fun x t => dot_eb_4 x t
    rcases zmod2_cases (u i) with hui | hui <;> rcases zmod2_cases (v i) with hvi | hvi
    · exact absurd (hui.trans hvi.symm) hi
    · obtain ⟨j, huj⟩ := exists_coord_one_4 hu
      rcases zmod2_cases (v j) with hvj | hvj
      · exact ⟨eb j, eb i, by rw [hdb, huj], by rw [hdb, hvj], by rw [hdb, hui], by rw [hdb, hvi]⟩
      · refine ⟨eb j + eb i, eb i, ?_, ?_, by rw [hdb, hui], by rw [hdb, hvi]⟩
        · rw [dot_add_right_4, hdb, hdb, huj, hui, add_zero]
        · rw [dot_add_right_4, hdb, hdb, hvj, hvi]; decide
    · obtain ⟨j, hvj⟩ := exists_coord_one_4 hv
      rcases zmod2_cases (u j) with huj | huj
      · exact ⟨eb i, eb j, by rw [hdb, hui], by rw [hdb, hvi], by rw [hdb, huj], by rw [hdb, hvj]⟩
      · refine ⟨eb i, eb j + eb i, by rw [hdb, hui], by rw [hdb, hvi], ?_, ?_⟩
        · rw [dot_add_right_4, hdb, hdb, huj, hui]; decide
        · rw [dot_add_right_4, hdb, hdb, hvj, hvi, add_zero]
    · exact absurd (hui.trans hvi.symm) hi
  obtain ⟨e1, e2, hu1, hv1, hu2, hv2⟩ := hex
  let F : ZMod 2 → ZMod 2 → Finset (F2 4) := fun a b =>
    Finset.univ.filter fun w : F2 4 => dot u w = a ∧ dot v w = b
  have hcard_eq : ∀ a b : ZMod 2, (F a b).card = (F 0 0).card := by
    intro a b
    let shift : F2 4 := (if a = 1 then e1 else 0) + (if b = 1 then e2 else 0)
    have hsu : dot u shift = a := by
      simp only [shift, dot_add_right_4]
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        simp [dot_zero_right_4, hu1, hu2]
    have hsv : dot v shift = b := by
      simp only [shift, dot_add_right_4]
      rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
        simp [dot_zero_right_4, hv1, hv2]
    symm
    refine Finset.card_bij (fun w _ => w + shift) ?_ ?_ ?_
    · intro w hw
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [dot_add_right_4 u, dot_add_right_4 v, hw.1, hw.2, hsu, hsv, zero_add, zero_add]
      exact ⟨rfl, rfl⟩
    · intro w1 _ w2 _ h
      ext k; have := congr_arg (· + shift k) (congr_fun h k)
      simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at this
      exact this
    · intro w hw
      refine ⟨w + shift, ?_, ?_⟩
      · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [dot_add_right_4 u, dot_add_right_4 v, hw.1, hw.2, hsu, hsv, zmod2_add_self, zmod2_add_self]
        exact ⟨rfl, rfl⟩
      · ext k; simp [Pi.add_apply, add_assoc, zmod2_add_self]
  have hsum4 : (F 0 0).card + (F 0 1).card + (F 1 0).card + (F 1 1).card = 16 := by
    have hdisj : ∀ a1 b1 a2 b2 : ZMod 2, (a1 ≠ a2 ∨ b1 ≠ b2) → Disjoint (F a1 b1) (F a2 b2) := by
      intro a1 b1 a2 b2 hne
      rw [Finset.disjoint_left]; intro w h1 h2
      simp only [F, Finset.mem_filter] at h1 h2
      rcases hne with ha | hb
      · exact ha (h1.2.1.symm.trans h2.2.1)
      · exact hb (h1.2.2.symm.trans h2.2.2)
    have hu1 : Disjoint (F 0 0) (F 0 1) := hdisj 0 0 0 1 (Or.inr (by decide))
    have hu2 : Disjoint (F 1 0) (F 1 1) := hdisj 1 0 1 1 (Or.inr (by decide))
    have hu3 : Disjoint (F 0 0 ∪ F 0 1) (F 1 0 ∪ F 1 1) := by
      simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hdisj 0 0 1 0 (Or.inl (by decide)), hdisj 0 1 1 0 (Or.inl (by decide))⟩,
             ⟨hdisj 0 0 1 1 (Or.inl (by decide)), hdisj 0 1 1 1 (Or.inl (by decide))⟩⟩
    have hall : (F 0 0 ∪ F 0 1) ∪ (F 1 0 ∪ F 1 1) = Finset.univ := by
      ext w
      simp only [F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases zmod2_cases (dot u w) with h1 | h1 <;> rcases zmod2_cases (dot v w) with h2 | h2 <;> simp [h1, h2]
    have hc := congr_arg Finset.card hall
    rw [Finset.card_union_of_disjoint hu3, Finset.card_union_of_disjoint hu1,
        Finset.card_union_of_disjoint hu2, card_F2_4] at hc
    omega
  have h01 := hcard_eq 0 1
  have h10 := hcard_eq 1 0
  have h11 := hcard_eq 1 1
  have hcc := hcard_eq c1 c2
  change (F c1 c2).card = 4
  omega

private lemma card_nz_dot_zero_4 {u : F2 4} (hu : u ≠ 0) :
    (Finset.univ.filter fun v : F2 4 => v ≠ 0 ∧ dot u v = 0).card = 7 := by
  have h0 : (0 : F2 4) ∈ Finset.univ.filter fun v : F2 4 => dot u v = 0 := by
    simp [dot_zero_right_4]
  have heq : (Finset.univ.filter fun v : F2 4 => v ≠ 0 ∧ dot u v = 0) =
      (Finset.univ.filter fun v : F2 4 => dot u v = 0).erase 0 := by
    ext v; simp [Finset.mem_erase]
  rw [heq, Finset.card_erase_of_mem h0, card_dot_eq_4 hu 0]

private lemma card_nz_dot2_zero_4 {u v : F2 4} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (Finset.univ.filter fun w : F2 4 => w ≠ 0 ∧ dot u w = 0 ∧ dot v w = 0).card = 3 := by
  have h0 : (0 : F2 4) ∈ Finset.univ.filter fun w : F2 4 => dot u w = 0 ∧ dot v w = 0 := by
    simp [dot_zero_right_4]
  have heq : (Finset.univ.filter fun w : F2 4 => w ≠ 0 ∧ dot u w = 0 ∧ dot v w = 0) =
      (Finset.univ.filter fun w : F2 4 => dot u w = 0 ∧ dot v w = 0).erase 0 := by
    ext w; simp [Finset.mem_erase]
  rw [heq, Finset.card_erase_of_mem h0, card_dot2_eq_4 hu hv huv 0 0]

/-- Exact frustration count of `spikeSign4` on `W(7,2)`: `frustPairs (nzPts 4) spikeSign4 = 1575 * 6`.
    Proved purely algebraically via `F2 4` linear-functional fiber cardinalities (zero `rfl`, zero `Nat.bitwise`). -/
theorem frustPairs_W72_spikeSign4 : frustPairs (nzPts 4) spikeSign4 = 1575 * 6 := by
  let P : PauliIdx 4 → PauliIdx 4 → Prop := fun p q =>
    p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ symp p q = 0 ∧
    gammaSgn p q * spikeSign4 p * spikeSign4 q * spikeSign4 (p + q) = -1
  let innerCount : F2 4 → F2 4 → ℕ := fun a1 a2 =>
    ∑ b1 : F2 4, ∑ b2 : F2 4, if P (a1, b1) (a2, b2) then 1 else 0
  have h1 : frustPairs (nzPts 4) spikeSign4 = ∑ a1 : F2 4, ∑ a2 : F2 4, innerCount a1 a2 := by
    unfold frustPairs
    rw [Finset.card_filter, Finset.sum_product]
    have hnz : ∀ p : PauliIdx 4,
        (∑ q ∈ nzPts 4, if p ≠ q ∧ symp p q = 0 ∧
            gammaSgn p q * spikeSign4 p * spikeSign4 q * spikeSign4 (p + q) = -1 then 1 else 0) =
        ∑ q : PauliIdx 4, if P p q then 1 else 0 := by
      intro p
      by_cases hp : p = 0
      · subst hp
        simp only [P, ne_eq, not_true_eq_false, false_and, ↓reduceIte, Finset.sum_const_zero]
        refine Finset.sum_eq_zero fun q _ => ?_
        have hs0 : spikeSign4 0 = 0 := spikeSign4_isSignAssign.1
        simp [hs0]
      · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : PauliIdx 4))]
        simp only [P, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
        simp [hp, hq0]
    have h0zero : (∑ q : PauliIdx 4, if P 0 q then 1 else 0) = 0 := by simp [P]
    have hleft : (∑ p ∈ nzPts 4, ∑ q ∈ nzPts 4,
          if p ≠ q ∧ symp p q = 0 ∧
            gammaSgn p q * spikeSign4 p * spikeSign4 q * spikeSign4 (p + q) = -1 then 1 else 0) =
        ∑ p : PauliIdx 4, ∑ q : PauliIdx 4, if P p q then 1 else 0 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : PauliIdx 4)), h0zero, zero_add]
      exact Finset.sum_congr rfl fun p _ => hnz p
    rw [hleft, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    rw [Finset.sum_comm]
  have hsymp_iff : ∀ a1 b1 a2 b2 : F2 4, symp (a1, b1) (a2, b2) = 0 ↔ dot a1 b2 = dot a2 b1 := fun a1 b1 a2 b2 => by
    simp only [symp, dot_comm b1 a2]
    rcases zmod2_cases (dot a1 b2) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2 <;>
      simp [h1, h2] <;> decide
  have hgam_eq : ∀ a1 b1 a2 b2 : F2 4,
      gammaSgn (a1, b1) (a2, b2) = if dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 then 1 else -1 := fun a1 b1 a2 b2 => by
    simp only [gammaSgn, gammaBit, quadForm0]
    by_cases h : dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 <;> simp [h]
  -- Case 1: `a1 = 0, a2 = 0` -> `0`
  have hcase00 : innerCount 0 0 = 0 := by
    refine Finset.sum_eq_zero fun b1 _ => Finset.sum_eq_zero fun b2 _ => ?_
    rw [ite_eq_right_iff]; rintro ⟨hp, hq, hpq, _, hfr⟩
    have hpq0 : ((0 : F2 4), b1) + (0, b2) ≠ 0 := by
      intro h; apply hpq
      have hb : b1 + b2 = 0 := congr_arg Prod.snd h
      have := congr_arg (b1 + ·) hb
      ext k
      · rfl
      · have hk := congr_fun this k
        simp only [Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc, zmod2_add_self, zero_add] at hk
        exact hk.symm
    have hsp : spikeSign4 (0, b1) = 1 := by simp [spikeSign4, hp]
    have hsq : spikeSign4 (0, b2) = 1 := by simp [spikeSign4, hq]
    have hspq : spikeSign4 ((0, b1) + (0, b2)) = 1 := by
      simp only [spikeSign4, hpq0, ↓reduceIte]
      change (if (0 : F2 4) + 0 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = 1
      simp
    have hg : gammaSgn (0, b1) (0, b2) = 1 := by simp [hgam_eq, dot]
    rw [hg, hsp, hsq, hspq] at hfr; norm_num at hfr
  -- Case 2: `a1 = 0, a2 ≠ 0` -> `14`
  have hcase0n : ∀ {a2 : F2 4}, a2 ≠ 0 → innerCount 0 a2 = 14 := by
    intro a2 ha2
    have hdot_zero_l : ∀ x : F2 4, dot (0 : F2 4) x = 0 := fun x => by simp [dot]
    have hiff : ∀ b1 b2 : F2 4, P (0, b1) (a2, b2) ↔ (b1 ≠ 0 ∧ dot a2 b1 = 0) ∧ (b2 = 0 ∨ b2 = b1) := by
      intro b1 b2
      have hq0 : (a2, b2) ≠ 0 := fun h => ha2 (congr_arg Prod.fst h)
      have hpq : (0, b1) ≠ (a2, b2) := fun h => ha2 (congr_arg Prod.fst h).symm
      have hpq0 : ((0 : F2 4), b1) + (a2, b2) ≠ 0 := fun h => ha2 (by simpa using congr_arg Prod.fst h)
      have hg : gammaSgn (0, b1) (a2, b2) = 1 := by simp [hgam_eq, hdot_zero_l]
      have hne_a : (((0 : F2 4), b1) + (a2, b2)).1 ≠ 0 := by simpa using ha2
      have hsum_b : b1 + b2 = 0 ↔ b2 = b1 := by
        constructor
        · intro h; ext k; have := congr_arg (b1 k + ·) (congr_fun h k)
          simp only [Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc, zmod2_add_self, zero_add] at this
          exact this
        · intro h; subst h; ext k; simp [zmod2_add_self]
      by_cases hb1 : b1 = 0
      · subst hb1; simp [P]
      · have hp0 : ((0 : F2 4), b1) ≠ 0 := fun h => hb1 (congr_arg Prod.snd h)
        have hsp : spikeSign4 (0, b1) = 1 := by simp [spikeSign4, hp0]
        have hsq : spikeSign4 (a2, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign4, hq0, ha2]
        have hspq : spikeSign4 ((0, b1) + (a2, b2)) = if b2 = b1 then 1 else -1 := by
          simp only [spikeSign4, hpq0, ↓reduceIte, hne_a, false_or]
          change (if b1 + b2 = 0 then (1 : ℤ) else -1) = _
          simp only [hsum_b]
        simp only [P, hp0, hq0, hpq, hsymp_iff, hdot_zero_l, hg, hsp, hsq, hspq, hb1,
          ne_eq, not_false_eq_true, true_and]
        by_cases hdb : dot a2 b1 = 0
        · simp only [hdb, true_and]
          by_cases hb20 : b2 = 0
          · subst hb20; simp [hb1, Ne.symm hb1]
          · by_cases hb21 : b2 = b1
            · subst hb21; simp [hb20]
            · simp [hb20, hb21]
        · have hdb' : (0 : ZMod 2) ≠ dot a2 b1 := Ne.symm hdb
          simp [hdb, hdb']
    have hinner_b1 : ∀ b1 : F2 4,
        (∑ b2 : F2 4, if P (0, b1) (a2, b2) then 1 else 0) = if b1 ≠ 0 ∧ dot a2 b1 = 0 then 2 else 0 := by
      intro b1
      simp_rw [hiff b1]
      by_cases h : b1 ≠ 0 ∧ dot a2 b1 = 0
      · rw [if_pos h]
        have hsum_eq : (∑ b2 : F2 4, if (b1 ≠ 0 ∧ dot a2 b1 = 0) ∧ (b2 = 0 ∨ b2 = b1) then 1 else 0) =
            (Finset.univ.filter fun b2 : F2 4 => b2 = 0 ∨ b2 = b1).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun b2 _ => by simp [h]
        have hset : (Finset.univ.filter fun b2 : F2 4 => b2 = 0 ∨ b2 = b1) = {0, b1} := by
          ext x; simp
        rw [hsum_eq, hset, Finset.card_pair h.1.symm]
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun b2 _ => by simp [h]
    dsimp only [innerCount]
    simp_rw [hinner_b1, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_nz_dot_zero_4 ha2]
  -- Case 3: `a1 ≠ 0, a2 = 0` -> `14`
  have hcasen0 : ∀ {a1 : F2 4}, a1 ≠ 0 → innerCount a1 0 = 14 := by
    intro a1 ha1
    have hdot_zero_l : ∀ x : F2 4, dot (0 : F2 4) x = 0 := fun x => by simp [dot]
    have hsym : ∀ b1 b2 : F2 4, P (a1, b1) (0, b2) ↔ P (0, b2) (a1, b1) := by
      intro b1 b2
      have hg1 : symp (a1, b1) (0, b2) = 0 → gammaSgn (a1, b1) (0, b2) = 1 := fun hs => by
        have hd : dot a1 b2 = 0 := by simpa [hsymp_iff, hdot_zero_l] using hs
        simp [hgam_eq, hdot_zero_l, hd]
      have hg2 : gammaSgn (0, b2) (a1, b1) = 1 := by simp [hgam_eq, hdot_zero_l]
      simp only [P, ne_comm (a := (a1, b1)), add_comm (a := (a1, b1))]
      have hs : symp (a1, b1) (0, b2) = 0 ↔ symp (0, b2) (a1, b1) = 0 := by
        simp [hsymp_iff, hdot_zero_l, eq_comm]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine ⟨h2, h1, h3, hs.mp h4, ?_⟩
        rw [hg1 h4] at h5; rw [hg2]; linarith
      · rintro ⟨h1, h2, h3, h4, h5⟩
        have h4' := hs.mpr h4
        refine ⟨h2, h1, h3, h4', ?_⟩
        rw [hg2] at h5; rw [hg1 h4']; linarith
    calc innerCount a1 0
        = ∑ b2 : F2 4, ∑ b1 : F2 4, if P (a1, b1) (0, b2) then 1 else 0 := Finset.sum_comm
      _ = innerCount 0 a1 := by dsimp only [innerCount]; simp_rw [hsym]
      _ = 14 := hcase0n ha1
  -- Case 4: `a1 ≠ 0, a2 = a1` -> `14`
  have hcasenn_eq : ∀ {a1 : F2 4}, a1 ≠ 0 → innerCount a1 a1 = 14 := by
    intro a1 ha1
    have hiff : ∀ b1 b2 : F2 4, P (a1, b1) (a1, b2) ↔
        (b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0) ∨ (b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0) := by
      intro b1 b2
      have hp0 : (a1, b1) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hq0 : (a1, b2) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hpq_iff : (a1, b1) ≠ (a1, b2) ↔ b1 ≠ b2 := ⟨fun h hb => h (by rw [hb]), fun h hp => h (congr_arg Prod.snd hp)⟩
      have hsp : spikeSign4 (a1, b1) = if b1 = 0 then 1 else -1 := by simp [spikeSign4, hp0, ha1]
      have hsq : spikeSign4 (a1, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign4, hq0, ha1]
      by_cases hbb : b1 = b2
      · subst hbb
        simp only [P, ne_eq, not_true_eq_false, false_and, and_false, false_iff, not_or, not_and]
        exact ⟨fun h hne _ => hne h, fun h hne _ => hne h⟩
      · have hpq0 : (a1, b1) + (a1, b2) ≠ 0 := by
          intro h; apply hbb
          have hb : b1 + b2 = 0 := congr_arg Prod.snd h
          ext k; have := congr_arg (b1 k + ·) (congr_fun hb k)
          simp only [Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc, zmod2_add_self, zero_add] at this
          exact this.symm
        have haa0 : a1 + a1 = 0 := funext fun k => zmod2_add_self (a1 k)
        have hspq : spikeSign4 ((a1, b1) + (a1, b2)) = 1 := by
          simp only [spikeSign4, hpq0, ↓reduceIte]
          change (if a1 + a1 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = 1
          simp [haa0]
        simp only [P, hp0, hq0, hpq_iff, hbb, hsymp_iff, hsp, hsq, hspq, ne_eq, not_false_eq_true, true_and]
        by_cases hcomm : dot a1 b2 = dot a1 b1
        · have hg : gammaSgn (a1, b1) (a1, b2) = 1 := by
            rw [hgam_eq, hcomm, zmod2_mul_self, zmod2_add_self]; simp
          simp only [hcomm, hg, true_and]
          by_cases hb1 : b1 = 0
          · subst hb1; simp [Ne.symm hbb, dot_zero_right_4] at hcomm ⊢
          · by_cases hb2 : b2 = 0
            · subst hb2; simp [hb1, dot_zero_right_4] at hcomm ⊢; exact hcomm.symm
            · simp [hb1, hb2]
        · simp only [hcomm, false_and, false_iff, not_or, not_and]
          refine ⟨fun hb1 _ hb20 => hcomm (by rw [hb1, dot_zero_right_4, hb20]),
                  fun hb2 _ hb10 => hcomm (by rw [hb2, dot_zero_right_4, hb10])⟩
    dsimp only [innerCount]
    simp_rw [hiff]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 4))]
    have h0 : (∑ b2 : F2 4, if (0 : F2 4) = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ (0 : F2 4) ≠ 0 ∧ dot a1 0 = 0 then 1 else 0) = 7 := by
      simp only [true_and, ne_eq, not_true_eq_false, false_and, and_false, or_false]
      rw [← Finset.card_filter, card_nz_dot_zero_4 ha1]
    have hrest : ∑ b1 ∈ Finset.univ.erase (0 : F2 4),
        (∑ b2 : F2 4, if b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0 then 1 else 0) = 7 := by
      have heach : ∀ b1 ∈ Finset.univ.erase (0 : F2 4),
          (∑ b2 : F2 4, if b1 = 0 ∧ b2 ≠ 0 ∧ dot a1 b2 = 0 ∨ b2 = 0 ∧ b1 ≠ 0 ∧ dot a1 b1 = 0 then 1 else 0) =
          if dot a1 b1 = 0 then 1 else 0 := by
        intro b1 hb1
        have hb10 : b1 ≠ 0 := (Finset.mem_erase.mp hb1).1
        simp only [hb10, false_and, false_or, ne_eq, not_false_eq_true, true_and]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 4))]
        have hzero : ∑ b2 ∈ Finset.univ.erase (0 : F2 4), (if b2 = 0 ∧ dot a1 b1 = 0 then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun b2 hb2 => by simp [(Finset.mem_erase.mp hb2).1]
        rw [hzero, add_zero]; simp
      rw [Finset.sum_congr rfl heach, ← Finset.card_filter]
      have hfilt : ((Finset.univ.erase (0 : F2 4)).filter fun b1 => dot a1 b1 = 0) =
          Finset.univ.filter fun b1 => b1 ≠ 0 ∧ dot a1 b1 = 0 := by
        ext b1; simp [Finset.mem_erase]
      rw [hfilt, card_nz_dot_zero_4 ha1]
    rw [h0, hrest]
  -- Case 5: `a1 ≠ 0, a2 ≠ 0, a1 ≠ a2` -> `42`
  have hcasenn_ne : ∀ {a1 a2 : F2 4}, a1 ≠ 0 → a2 ≠ 0 → a1 ≠ a2 → innerCount a1 a2 = 42 := by
    intro a1 a2 ha1 ha2 ha12
    have ha12_sum : a1 + a2 ≠ 0 := fun h => ha12 (by
      ext k; have := congr_arg (a1 k + ·) (congr_fun h k)
      simp only [Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc, zmod2_add_self, zero_add] at this
      exact this.symm)
    have hiff : ∀ b1 b2 : F2 4, P (a1, b1) (a2, b2) ↔
        b1 ≠ 0 ∧ b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = dot a2 b1 ∧ dot a1 b1 * dot a2 b2 + dot a1 b2 = 0 := by
      intro b1 b2
      have hp0 : (a1, b1) ≠ 0 := fun h => ha1 (congr_arg Prod.fst h)
      have hq0 : (a2, b2) ≠ 0 := fun h => ha2 (congr_arg Prod.fst h)
      have hpq : (a1, b1) ≠ (a2, b2) := fun h => ha12 (congr_arg Prod.fst h)
      have hpq0 : (a1, b1) + (a2, b2) ≠ 0 := fun h => ha12_sum (congr_arg Prod.fst h)
      have hsp : spikeSign4 (a1, b1) = if b1 = 0 then 1 else -1 := by simp [spikeSign4, hp0, ha1]
      have hsq : spikeSign4 (a2, b2) = if b2 = 0 then 1 else -1 := by simp [spikeSign4, hq0, ha2]
      have hsum_b : b1 + b2 = 0 ↔ b1 = b2 := by
        constructor
        · intro h; ext k; have := congr_arg (b1 k + ·) (congr_fun h k)
          simp only [Pi.add_apply, Pi.zero_apply, add_zero, ← add_assoc, zmod2_add_self, zero_add] at this
          exact this.symm
        · intro h; subst h; ext k; simp [zmod2_add_self]
      have hspq : spikeSign4 ((a1, b1) + (a2, b2)) = if b1 = b2 then 1 else -1 := by
        simp only [spikeSign4, hpq0, ↓reduceIte]
        change (if a1 + a2 = 0 ∨ b1 + b2 = 0 then (1 : ℤ) else -1) = _
        simp only [ha12_sum, false_or, hsum_b]
      simp only [P, hp0, hq0, hpq, hsymp_iff, hgam_eq, hsp, hsq, hspq, ne_eq, not_false_eq_true, true_and]
      by_cases hb1 : b1 = 0
      · subst hb1
        simp only [↓reduceIte, not_true_eq_false, false_and, iff_false, not_and]
        intro hcomm
        have hd0 : dot a1 b2 = 0 := by simpa [dot_zero_right_4] using hcomm
        simp only [dot_zero_right_4, zero_mul, zero_add, hd0, ↓reduceIte]
        by_cases hb20 : b2 = 0
        · subst hb20; simp
        · simp [hb20, Ne.symm hb20]
      · by_cases hb2 : b2 = 0
        · subst hb2
          simp only [hb1, ↓reduceIte, not_true_eq_false, false_and, and_false, iff_false, not_and]
          intro _; simp only [dot_zero_right_4, mul_zero, add_zero, ↓reduceIte]; norm_num
        · by_cases hbb : b1 = b2
          · subst hbb
            simp only [hb1, ↓reduceIte, not_true_eq_false, false_and, and_false, iff_false, not_and]
            intro hcomm
            rw [← hcomm, zmod2_mul_self, zmod2_add_self]; norm_num
          · simp only [hb1, hb2, hbb, ↓reduceIte, not_false_eq_true, true_and]
            by_cases hcomm : dot a1 b2 = dot a2 b1
            · simp only [hcomm, true_and]
              by_cases hg : dot a1 b1 * dot a2 b2 + dot a1 b2 = 0
              · simp [hg]
              · simp [hg]
            · simp [hcomm]
    -- Evaluate inner sum over `b2` as a function of `(b1 ≠ 0, dot a1 b1, dot a2 b1)`!
    have hinner_b1 : ∀ b1 : F2 4,
        (∑ b2 : F2 4, if P (a1, b1) (a2, b2) then 1 else 0) =
        if b1 = 0 then 0
        else if dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 6
        else if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 3
        else if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 3
        else 0 := by
      intro b1
      simp_rw [hiff b1]
      by_cases hb1 : b1 = 0
      · subst hb1; simp
      · simp only [hb1, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
        rcases zmod2_cases (dot a1 b1) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2
        · -- `(0, 0)`: `b2 ≠ 0, b2 ≠ b1, dot a1 b2 = 0` -> `8 - 2 = 6`
          simp only [h1, h2, ↓reduceIte, zero_mul, zero_add, and_self]
          have hset : (Finset.univ.filter fun b2 : F2 4 => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 0) =
              ((Finset.univ.filter fun b2 : F2 4 => dot a1 b2 = 0).erase 0).erase b1 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            exact ⟨fun ⟨a, b, c⟩ => ⟨b.symm, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a.symm, c⟩⟩
          have h0m : (0 : F2 4) ∈ Finset.univ.filter fun b2 : F2 4 => dot a1 b2 = 0 := by
            simp [dot_zero_right_4]
          have hb1m : b1 ∈ (Finset.univ.filter fun b2 : F2 4 => dot a1 b2 = 0).erase 0 := by
            simp [Finset.mem_erase, hb1, h1]
          rw [← Finset.card_filter, hset, Finset.card_erase_of_mem hb1m,
              Finset.card_erase_of_mem h0m, card_dot_eq_4 ha1 0]
        · -- `(0, 1)`: `dot a1 b2 = 1` and `0 * _ + 1 = 0` impossible -> `0`
          simp only [h1, h2, zero_mul, zero_add]
          have hno : ∀ b2 : F2 4, ¬(b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 1 ∧ dot a1 b2 = 0) := fun b2 ⟨_, _, ha, hb⟩ =>
            absurd (ha.symm.trans hb) (by decide)
          simp only [hno, ↓reduceIte, Finset.sum_const_zero]
          have h01 : (0 : ZMod 2) ≠ 1 := by decide
          simp [h01]
        · -- `(1, 0)`: `b2 ≠ 0, dot a1 b2 = 0, dot a2 b2 = 0` (`b1 ≠ b2` automatic) -> `3`
          have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [h1, h2, h10, false_and, true_and, ↓reduceIte, one_mul]
          have hset : (Finset.univ.filter fun b2 : F2 4 => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 0 ∧ dot a2 b2 + dot a1 b2 = 0) =
              Finset.univ.filter fun b2 : F2 4 => b2 ≠ 0 ∧ dot a1 b2 = 0 ∧ dot a2 b2 = 0 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨h1', _, h3', h4'⟩; rw [h3', add_zero] at h4'; exact ⟨h1', h3', h4'⟩
            · rintro ⟨h1', h3', h4'⟩
              refine ⟨h1', fun heq => h10 (by rw [← h1, heq, h3']), h3', by rw [h3', h4', add_zero]⟩
          rw [← Finset.card_filter, hset, card_nz_dot2_zero_4 ha1 ha2 ha12]
        · -- `(1, 1)`: `b2 ≠ b1, dot a1 b2 = 1, dot a2 b2 = 1` (`b2 ≠ 0` automatic) -> `4 - 1 = 3`
          have h10 : (1 : ZMod 2) ≠ 0 := by decide
          simp only [h1, h2, h10, and_false, true_and, ↓reduceIte, one_mul]
          have hset : (Finset.univ.filter fun b2 : F2 4 => b2 ≠ 0 ∧ b1 ≠ b2 ∧ dot a1 b2 = 1 ∧ dot a2 b2 + dot a1 b2 = 0) =
              (Finset.univ.filter fun b2 : F2 4 => dot a1 b2 = 1 ∧ dot a2 b2 = 1).erase b1 := by
            ext b2; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨_, hne, hd1, hd2⟩
              refine ⟨hne.symm, hd1, ?_⟩
              rw [hd1] at hd2
              rcases zmod2_cases (dot a2 b2) with hc | hc
              · rw [hc] at hd2; exact absurd hd2 (by decide)
              · exact hc
            · rintro ⟨hne, hd1, hd2⟩
              refine ⟨fun h0 => h10 (by rw [← hd1, h0, dot_zero_right_4]), hne.symm, hd1, ?_⟩
              rw [hd1, hd2]; decide
          have hb1m : b1 ∈ Finset.univ.filter fun b2 : F2 4 => dot a1 b2 = 1 ∧ dot a2 b2 = 1 := by
            simp [h1, h2]
          rw [← Finset.card_filter, hset, Finset.card_erase_of_mem hb1m, card_dot2_eq_4 ha1 ha2 ha12 1 1]
    dsimp only [innerCount]
    simp_rw [hinner_b1]
    -- Split sum over `b1` into the 3 nonzero classes: `3*6 + 4*3 + 4*3 = 42`!
    have hsplit : ∀ b1 : F2 4,
        (if b1 = 0 then 0
          else if dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 6
          else if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 3
          else if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 3
          else 0) =
        (if b1 ≠ 0 ∧ dot a1 b1 = 0 ∧ dot a2 b1 = 0 then 6 else 0) +
        (if dot a1 b1 = 1 ∧ dot a2 b1 = 0 then 3 else 0) +
        (if dot a1 b1 = 1 ∧ dot a2 b1 = 1 then 3 else 0) := by
      intro b1
      by_cases hb1 : b1 = 0
      · subst hb1; simp [dot_zero_right_4]
      · rcases zmod2_cases (dot a1 b1) with h1 | h1 <;> rcases zmod2_cases (dot a2 b1) with h2 | h2 <;>
          simp [hb1, h1, h2]
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [card_nz_dot2_zero_4 ha1 ha2 ha12, card_dot2_eq_4 ha1 ha2 ha12 1 0, card_dot2_eq_4 ha1 ha2 ha12 1 1]
  -- Assemble over `a1, a2 : F2 4`!
  rw [h1, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 4))]
  have hcard15 : (Finset.univ.erase (0 : F2 4)).card = 15 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_F2_4]
  have hrow0 : ∑ a2 : F2 4, innerCount 0 a2 = 210 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 4)), hcase00, zero_add]
    rw [Finset.sum_congr rfl fun a2 ha2 => hcase0n (Finset.mem_erase.mp ha2).1,
        Finset.sum_const, smul_eq_mul, hcard15]
  have hrown : ∀ a1 ∈ Finset.univ.erase (0 : F2 4), ∑ a2 : F2 4, innerCount a1 a2 = 616 := by
    intro a1 ha1
    have ha10 : a1 ≠ 0 := (Finset.mem_erase.mp ha1).1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F2 4)), hcasen0 ha10]
    rw [← Finset.add_sum_erase (Finset.univ.erase 0) _ (Finset.mem_erase.mpr ⟨ha10, Finset.mem_univ _⟩),
        hcasenn_eq ha10]
    have hcard14 : ((Finset.univ.erase (0 : F2 4)).erase a1).card = 14 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha10, Finset.mem_univ _⟩), hcard15]
    rw [Finset.sum_congr rfl fun a2 ha2 =>
          hcasenn_ne ha10 (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha2)).1
            (Finset.mem_erase.mp ha2).1.symm,
        Finset.sum_const, smul_eq_mul, hcard14]
    norm_num
  rw [hrow0, Finset.sum_congr rfl hrown, Finset.sum_const, smul_eq_mul, hcard15]

end FourQubitCDExact

open FourQubitCDExact

/-- **Unconditional Lower Bound `CD(Q⁻(7,2)) ≥ 315`** on EVERY one of the 120 elliptic quadrics! -/
theorem frustPairs_Qminus72_ge_315 {c : PauliIdx 4} (hc : c ∈ ellCenters 4)
    {s : PauliIdx 4 → ℤ} (hs : IsSignAssign s) :
    315 * 6 ≤ frustPairs (Qminus c) s := by
  have hcQ : quadForm0 c = 1 := (Finset.mem_filter.mp hc).2
  rw [frustPairs_Qminus_eq_of_ellCenter hcQ quadForm0_c0_88]
  exact frustPairs_Qminus88_ge_315 (applyTransv_isSignAssign _ hs)

/-- **Unconditional Lower Bound `CD(W(7,2)) ≥ 1575`** in integer frustrated-pair form. -/
theorem frustPairs_W72_ge_1575 {s : PauliIdx 4 → ℤ} (hs : IsSignAssign s) :
    1575 * 6 ≤ frustPairs (nzPts 4) s := by
  have hcard120 : (ellCenters 4).card = 120 := by
    have hZ := card_elliptic_centers (n := 4) (by norm_num)
    norm_num at hZ; exact_mod_cast hZ
  have h120 : 120 * (315 * 6) ≤ 24 * frustPairs (nzPts 4) s := by
    rw [double_count_W72_Qminus, ← hcard120, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => frustPairs_Qminus72_ge_315 hc hs
  omega

/-- Simultaneous tightness on ALL 120 elliptic quadrics `Q⁻(7,2)` under `spikeSign4`! -/
theorem frustPairs_Qminus72_spikeSign4 {c : PauliIdx 4} (hc : c ∈ ellCenters 4) :
    frustPairs (Qminus c) spikeSign4 = 315 * 6 := by
  have hge := frustPairs_Qminus72_ge_315 hc spikeSign4_isSignAssign
  have hcard120 : (ellCenters 4).card = 120 := by
    have hZ := card_elliptic_centers (n := 4) (by norm_num)
    norm_num at hZ; exact_mod_cast hZ
  have hsum : ∑ c' ∈ ellCenters 4, frustPairs (Qminus c') spikeSign4 = 120 * (315 * 6) := by
    rw [← double_count_W72_Qminus, frustPairs_W72_spikeSign4]
  have hrest : 119 * (315 * 6) ≤ ∑ c' ∈ (ellCenters 4).erase c, frustPairs (Qminus c') spikeSign4 := by
    have hcard119 : ((ellCenters 4).erase c).card = 119 := by
      rw [Finset.card_erase_of_mem hc, hcard120]
    rw [← hcard119, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c' hc' =>
      frustPairs_Qminus72_ge_315 (Finset.mem_of_mem_erase hc') spikeSign4_isSignAssign
  have hsplit := Finset.add_sum_erase (ellCenters 4) (fun c' => frustPairs (Qminus c') spikeSign4) hc
  omega

/-- **Exact Contextuality Degree of `Q⁻(7,2)`: `CD(Q⁻(7,2)) = 315`** (for all 120 elliptic quadrics). -/
theorem cd_Qminus72_eq_315 {c : PauliIdx 4} (hc : c ∈ ellCenters 4) :
    (∀ s : PauliIdx 4 → ℤ, IsSignAssign s → 315 * 6 ≤ frustPairs (Qminus c) s) ∧
    (∃ s : PauliIdx 4 → ℤ, IsSignAssign s ∧ frustPairs (Qminus c) s = 315 * 6) :=
  ⟨fun _ hs => frustPairs_Qminus72_ge_315 hc hs,
   ⟨spikeSign4, spikeSign4_isSignAssign, frustPairs_Qminus72_spikeSign4 hc⟩⟩

/-- **Exact Contextuality Degree of `W(7,2)`: `CD(W(7,2)) = 1575`**. -/
theorem cd_W72_eq_1575 :
    (∀ s : PauliIdx 4 → ℤ, IsSignAssign s → 1575 * 6 ≤ frustPairs (nzPts 4) s) ∧
    (∃ s : PauliIdx 4 → ℤ, IsSignAssign s ∧ frustPairs (nzPts 4) s = 1575 * 6) :=
  ⟨fun _ hs => frustPairs_W72_ge_1575 hs,
   ⟨spikeSign4, spikeSign4_isSignAssign, frustPairs_W72_spikeSign4⟩⟩

/-- **Exact 4-Qubit Sign-Cube Maximum (`max signCubeSum 4 = 6615`)**:
    Every `±1` Pauli sign assignment satisfies `signCubeSum 4 σ ≤ 6615`, and `spikeSign4`
    attains `signCubeSum 4 σ = 6615` with equality! -/
theorem signCubeSum_four_max_eq_6615 :
    (∀ σ : PauliIdx 4 → ℝ, σ 0 = 0 →
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) → signCubeSum 4 σ ≤ 6615) ∧
    (∃ σ : PauliIdx 4 → ℝ, σ 0 = 0 ∧
      (∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1) ∧ signCubeSum 4 σ = 6615) := by
  refine ⟨signCubeSum_four_le_6615, ?_⟩
  let σ : PauliIdx 4 → ℝ := fun p => (spikeSign4 p : ℝ)
  have h0 : σ 0 = 0 := by simp [σ, spikeSign4_isSignAssign.1]
  have hpm : ∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
    rcases spikeSign4_isSignAssign.2 p hp with h | h <;> simp [σ, h]
  refine ⟨σ, h0, hpm, ?_⟩
  have hbr := (signCubeSum_eq_frustPairs h0 hpm).2
  have hseq : (fun p : PauliIdx 4 => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = spikeSign4 := by
    ext p; by_cases hp : p = 0
    · subst hp; simp [spikeSign4_isSignAssign.1]
    · simp only [hp, ↓reduceIte]
      rcases spikeSign4_isSignAssign.2 p hp with h | h
      · simp [σ, h]
      · simp only [σ, h]; norm_num
  rw [hseq, frustPairs_W72_spikeSign4] at hbr
  norm_num at hbr ⊢
  exact hbr

end MultiQubitMUB
