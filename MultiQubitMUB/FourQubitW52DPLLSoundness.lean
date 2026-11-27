import MultiQubitMUB.FourQubitW52DPLL

set_option linter.constructorNameAsVariable false

/-!
# Soundness of Shared 36-Bit + 144-Bit SIMD DPLL Engine (Parts 2a & 2b: Orbits 2 and 1)

Proves:
1. Shared `w5FrustEq`, `flipB36`, and `isMinQminus09` invariance/congruence API (also reused by Orbit 0).
2. Exact `A₂₇ ⊔ B₃₆` frustrated-pair splits for `W(5,2)` and for all 27 other elliptic quadrics `Q⁻(5,2)`.
3. Carry-free 144-bit SIMD nibble extraction (`nibble_extract`) and `simdStarLB` / `initPatSimd` soundness.
4. Master DPLL soundness `sound_checkTree36` (`S, G, U, M, O`) and stabilizer coverage `orbit_dpll_hits_sp42`
   covering BOTH Orbit 2 (`f₂₇ = 13`) and Orbit 1 (`f₂₇ = 12`).
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Shared `w5FrustEq`, `flipB36`, `isMinQminus09`, and `wlines315` Bridge -/

/-- Two 3-qubit sign assignments have identical line frustrations on all 315 lines of `W(5,2)`. -/
def w5FrustEq (s1 s2 : PauliIdx 3 → ℤ) : Prop :=
  ∀ a b : PauliIdx 3, a ≠ 0 → b ≠ 0 → a ≠ b → symp a b = 0 →
    s1 a * s1 b * s1 (a + b) = s2 a * s2 b * s2 (a + b)

lemma w5FrustEq_refl (s : PauliIdx 3 → ℤ) : w5FrustEq s s := fun _ _ _ _ _ _ => rfl

lemma w5FrustEq_symm {s1 s2 : PauliIdx 3 → ℤ} (h : w5FrustEq s1 s2) : w5FrustEq s2 s1 :=
  fun a b ha hb hab hsp => (h a b ha hb hab hsp).symm

lemma w5FrustEq_trans {s1 s2 s3 : PauliIdx 3 → ℤ} (h12 : w5FrustEq s1 s2) (h23 : w5FrustEq s2 s3) :
    w5FrustEq s1 s3 :=
  fun a b ha hb hab hsp => (h12 a b ha hb hab hsp).trans (h23 a b ha hb hab hsp)

lemma w5FrustEq_applyGauge (g : PauliIdx 3) (s : PauliIdx 3 → ℤ) :
    w5FrustEq (applyGauge g s) s := by
  intro a b _ _ _ _
  simp only [applyGauge]
  have h1 : sympSign g a * sympSign g b * sympSign g (a + b) = 1 := by
    rw [sympSign_add_right]
    have hsq : ∀ x : PauliIdx 3, sympSign g x * sympSign g x = 1 := fun x => by
      simp only [sympSign]; rcases zmod2_cases (symp g x) with h | h <;> rw [h] <;> decide
    calc sympSign g a * sympSign g b * (sympSign g a * sympSign g b)
        = (sympSign g a * sympSign g a) * (sympSign g b * sympSign g b) := by ring
      _ = 1 * 1 := by rw [hsq a, hsq b]
      _ = 1 := one_mul 1
  calc sympSign g a * s a * (sympSign g b * s b) * (sympSign g (a + b) * s (a + b))
      = (sympSign g a * sympSign g b * sympSign g (a + b)) * (s a * s b * s (a + b)) := by ring
    _ = 1 * (s a * s b * s (a + b)) := by rw [h1]
    _ = s a * s b * s (a + b) := one_mul _

/-- Flip all signs on `B₃₆ = {p | Q_{09}(p) = 1}` when `neg = true`, leaving `A₂₇` untouched. -/
def flipB36 (neg : Bool) (s : PauliIdx 3 → ℤ) (p : PauliIdx 3) : ℤ :=
  if neg && decide (quadForm c0_09 p = 1) then -s p else s p

lemma flipB36_isSignAssign (neg : Bool) {s : PauliIdx 3 → ℤ} (hs : IsSignAssign s) :
    IsSignAssign (flipB36 neg s) := by
  refine ⟨?_, fun p hp => ?_⟩
  · have hq0 : quadForm c0_09 0 = 0 := by rw [← dec3_zero, c0_09, quadForm_dec3]; decide
    simp [flipB36, hq0, hs.1]
  · unfold flipB36
    split_ifs
    · rcases hs.2 p hp with h | h <;> simp [h]
    · exact hs.2 p hp

lemma flipB36_on_A27 (neg : Bool) (s : PauliIdx 3 → ℤ) {p : PauliIdx 3} (hp : quadForm c0_09 p = 0) :
    flipB36 neg s p = s p := by
  simp [flipB36, hp]

lemma flipB36_on_B36 (neg : Bool) (s : PauliIdx 3 → ℤ) {p : PauliIdx 3} (hp : quadForm c0_09 p = 1) :
    flipB36 neg s p = (if neg then -1 else 1) * s p := by
  cases neg <;> simp [flipB36, hp]

lemma w5FrustEq_flipB36 (neg : Bool) (s : PauliIdx 3 → ℤ) :
    w5FrustEq (flipB36 neg s) s := by
  intro a b _ _ _ hsp
  have hab : quadForm c0_09 (a + b) = quadForm c0_09 a + quadForm c0_09 b := by
    rw [quadForm_add, hsp, add_zero]
  cases neg
  · simp [flipB36]
  · simp only [flipB36, Bool.true_and, decide_eq_true_eq, hab]
    rcases zmod2_cases (quadForm c0_09 a) with ha | ha <;>
    rcases zmod2_cases (quadForm c0_09 b) with hb | hb <;>
    simp [ha, hb] <;> ring

lemma w5FrustEq_applyTransv (u : PauliIdx 3) {s1 s2 : PauliIdx 3 → ℤ} (h : w5FrustEq s1 s2) :
    w5FrustEq (applyTransv u s1) (applyTransv u s2) := by
  intro a b ha hb hab hsp
  have hta : transvPt u a ≠ 0 := fun hc => ha (by rw [← transvPt_invol u a, hc, transvPt_zero])
  have htb : transvPt u b ≠ 0 := fun hc => hb (by rw [← transvPt_invol u b, hc, transvPt_zero])
  have htab : transvPt u a ≠ transvPt u b := fun hc => hab (by
    have := congr_arg (transvPt u) hc; simpa [transvPt_invol] using this)
  have htsp : symp (transvPt u a) (transvPt u b) = 0 := by rw [symp_transvPt]; exact hsp
  have hadd : transvPt u (a + b) = transvPt u a + transvPt u b := transvPt_add u a b
  simp only [applyTransv, hadd]
  have heq := h (transvPt u a) (transvPt u b) hta htb htab htsp
  calc transvSgn u a * s1 (transvPt u a) * (transvSgn u b * s1 (transvPt u b)) *
        (transvSgn u (a + b) * s1 (transvPt u a + transvPt u b))
      = (transvSgn u a * transvSgn u b * transvSgn u (a + b)) *
        (s1 (transvPt u a) * s1 (transvPt u b) * s1 (transvPt u a + transvPt u b)) := by ring
    _ = (transvSgn u a * transvSgn u b * transvSgn u (a + b)) *
        (s2 (transvPt u a) * s2 (transvPt u b) * s2 (transvPt u a + transvPt u b)) := by rw [heq]
    _ = transvSgn u a * s2 (transvPt u a) * (transvSgn u b * s2 (transvPt u b)) *
        (transvSgn u (a + b) * s2 (transvPt u a + transvPt u b)) := by ring

lemma w5FrustEq_applyTransvWord (us : List (PauliIdx 3)) {s1 s2 : PauliIdx 3 → ℤ}
    (h : w5FrustEq s1 s2) :
    w5FrustEq (applyTransvWord us s1) (applyTransvWord us s2) := by
  induction us generalizing s1 s2 with
  | nil => exact h
  | cons u us ih =>
    simp only [applyTransvWord]
    exact ih (w5FrustEq_applyTransv u h)

lemma frustPairs_of_w5FrustEq {S : Finset (PauliIdx 3)} (h0 : (0 : PauliIdx 3) ∉ S)
    {s1 s2 : PauliIdx 3 → ℤ} (h : w5FrustEq s1 s2) :
    frustPairs S s1 = frustPairs S s2 := by
  unfold frustPairs
  refine congr_arg Finset.card (Finset.ext fun pq => ?_)
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor <;> rintro ⟨⟨hp, hq⟩, hne, hsp, hfr⟩
  · have hp0 : pq.1 ≠ 0 := fun hc => h0 (hc ▸ hp)
    have hq0 : pq.2 ≠ 0 := fun hc => h0 (hc ▸ hq)
    have heq := h pq.1 pq.2 hp0 hq0 hne hsp
    refine ⟨⟨hp, hq⟩, hne, hsp, ?_⟩
    calc gammaSgn pq.1 pq.2 * s2 pq.1 * s2 pq.2 * s2 (pq.1 + pq.2)
        = gammaSgn pq.1 pq.2 * (s2 pq.1 * s2 pq.2 * s2 (pq.1 + pq.2)) := by ring
      _ = gammaSgn pq.1 pq.2 * (s1 pq.1 * s1 pq.2 * s1 (pq.1 + pq.2)) := by rw [← heq]
      _ = -1 := by linarith
  · have hp0 : pq.1 ≠ 0 := fun hc => h0 (hc ▸ hp)
    have hq0 : pq.2 ≠ 0 := fun hc => h0 (hc ▸ hq)
    have heq := h pq.1 pq.2 hp0 hq0 hne hsp
    refine ⟨⟨hp, hq⟩, hne, hsp, ?_⟩
    calc gammaSgn pq.1 pq.2 * s1 pq.1 * s1 pq.2 * s1 (pq.1 + pq.2)
        = gammaSgn pq.1 pq.2 * (s1 pq.1 * s1 pq.2 * s1 (pq.1 + pq.2)) := by ring
      _ = gammaSgn pq.1 pq.2 * (s2 pq.1 * s2 pq.2 * s2 (pq.1 + pq.2)) := by rw [heq]
      _ = -1 := by linarith

/-- Predicate stating `Qminus c0_09` minimizes frustrated pairs among all 28 elliptic `Q⁻(5,2)` quadrics. -/
def isMinQminus09 (s3 : PauliIdx 3 → ℤ) : Prop :=
  ∀ c ∈ ellCenters 3, frustPairs (Qminus c0_09) s3 ≤ frustPairs (Qminus c) s3

lemma isMinQminus09_of_w5FrustEq {s1 s2 : PauliIdx 3 → ℤ} (h : w5FrustEq s1 s2)
    (hmin : isMinQminus09 s1) : isMinQminus09 s2 := by
  intro c hc
  have h0_mem : ∀ d : PauliIdx 3, (0 : PauliIdx 3) ∉ Qminus d := fun d => by
    simp [Qminus, nzPts]
  rw [← frustPairs_of_w5FrustEq (h0_mem c0_09) h, ← frustPairs_of_w5FrustEq (h0_mem c) h]
  exact hmin c hc

lemma isMinQminus09_applyTransv_Ominus {u : PauliIdx 3} (hu : quadForm c0_09 u = 1)
    {s3 : PauliIdx 3 → ℤ} (hmin : isMinQminus09 s3) :
    isMinQminus09 (applyTransv u s3) := by
  have hfix09 : frustPairs (Qminus c0_09) (applyTransv u s3) = frustPairs (Qminus c0_09) s3 := by
    refine frustPairs_applyTransv u (Qminus c0_09) (Qminus c0_09) (fun p => ?_) s3
    simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      quadForm_transvPt_fix hu]
    exact ⟨fun ⟨hp0, h⟩ => ⟨fun hc => hp0 (by rw [← transvPt_invol u p, hc, transvPt_zero]), h⟩,
           fun ⟨ht0, h⟩ => ⟨fun hc => ht0 (by rw [hc, transvPt_zero]), h⟩⟩
  intro c hc
  rw [hfix09]
  rcases zmod2_cases (quadForm c u) with hcu | hcu
  · have hc'_mem : c + u ∈ ellCenters 3 := by
      simp only [ellCenters, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [quadForm0_add, hc]
      have hq : quadForm0 u + symp c u = 0 := hcu
      rw [add_assoc, hq, add_zero]
    have hmap : frustPairs (Qminus c) (applyTransv u s3) = frustPairs (Qminus (c + u)) s3 := by
      refine frustPairs_applyTransv u (Qminus c) (Qminus (c + u)) (fun p => ?_) s3
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      have hm : quadForm (c + u) (transvPt u p) = quadForm c p := by
        have := quadForm_transvPt_move hcu (transvPt u p)
        rw [transvPt_invol] at this; exact this.symm
      rw [hm]
      exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
             fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
    rw [hmap]; exact hmin (c + u) hc'_mem
  · have hmap : frustPairs (Qminus c) (applyTransv u s3) = frustPairs (Qminus c) s3 := by
      refine frustPairs_applyTransv u (Qminus c) (Qminus c) (fun p => ?_) s3
      simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        quadForm_transvPt_fix hcu]
      exact ⟨fun ⟨hp0, h⟩ => ⟨fun h0 => hp0 (by rw [← transvPt_invol u p, h0, transvPt_zero]), h⟩,
             fun ⟨ht0, h⟩ => ⟨fun h0 => ht0 (by rw [h0, transvPt_zero]), h⟩⟩
    rw [hmap]; exact hmin c hc

lemma isMinQminus09_applyTransvWord_Ominus {us : List (PauliIdx 3)}
    (hus : ∀ u ∈ us, quadForm c0_09 u = 1) {s3 : PauliIdx 3 → ℤ} (hmin : isMinQminus09 s3) :
    isMinQminus09 (applyTransvWord us s3) := by
  induction us generalizing s3 with
  | nil => exact hmin
  | cons u us ih =>
    simp only [applyTransvWord]
    exact ih (fun w hw => hus w (List.mem_cons_of_mem u hw))
      (isMinQminus09_applyTransv_Ominus (hus u (List.mem_cons_self ..)) hmin)

lemma frustPairs_nzPts_applyTransv (u : PauliIdx 3) (s : PauliIdx 3 → ℤ) :
    frustPairs (nzPts 3) (applyTransv u s) = frustPairs (nzPts 3) s := by
  refine frustPairs_applyTransv u (nzPts 3) (nzPts 3) (fun p => ?_) s
  simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun hp0 hc => hp0 (by rw [← transvPt_invol u p, hc, transvPt_zero]),
         fun ht0 hc => ht0 (by rw [hc, transvPt_zero])⟩

lemma frustPairs_nzPts_applyTransvWord (us : List (PauliIdx 3)) (s : PauliIdx 3 → ℤ) :
    frustPairs (nzPts 3) (applyTransvWord us s) = frustPairs (nzPts 3) s := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    simp only [applyTransvWord, ih, frustPairs_nzPts_applyTransv]

/-- Exact evaluation of `applyTransvWord us s p` via `us.reverse.foldl` tracking `(cur, sg)`. -/
lemma applyTransvWord_eq_reverse_foldl (us : List (PauliIdx 3)) (s : PauliIdx 3 → ℤ) :
    ∀ (p : PauliIdx 3) (acc : ℤ),
      acc * applyTransvWord us s p =
        let res := us.reverse.foldl
          (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (p, acc)
        res.2 * s res.1 := by
  induction us generalizing s with
  | nil => intro p acc; rfl
  | cons u us ih =>
    intro p acc
    simp only [applyTransvWord, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h := ih (applyTransv u s) p acc
    dsimp only at h ⊢
    rw [h]
    simp only [applyTransv]
    ring

/-- Bridge from `wlines315.all` Boolean check to `w5FrustEq` against `sp42Certs spId`. -/
lemma sp42S64List_getD_eq (spId : Fin 42) :
    sp42S64List.getD spId.val [] = (sp42Certs spId).s64 := by
  rcases spId with ⟨v, hv⟩
  interval_cases v <;> rfl

lemma w5FrustEq_of_wlines315_all {sOut : Nat → ℤ} {s3 : PauliIdx 3 → ℤ} {spId : Fin 42}
    (hagree : ∀ v : Fin 64, sOut v.val = s3 (dec3 v))
    (hall : (wlines315.all fun (a, b, c, _) =>
      sOut a * sOut b * sOut c ==
        getS64 (sp42S64List.getD spId.val []) a * getS64 (sp42S64List.getD spId.val []) b *
        getS64 (sp42S64List.getD spId.val []) c) = true) :
    w5FrustEq s3 (listToSign3 (sp42Certs spId).s64) := by
  rw [sp42S64List_getD_eq] at hall
  rw [List.all_eq_true] at hall
  have hmem_wl : ∀ x y : Nat, x < 64 → y < 64 → x ≠ 0 → x < y → y < (x ^^^ y) → symp3 x y = 0 →
      (x, y, x ^^^ y, gamma3_sgn x y) ∈ wlines315 := by
    intro x y hx hy hx0 hxy hyz hsp
    simp only [wlines315, List.mem_flatMap, List.mem_range]
    refine ⟨x, hx, ?_⟩
    have hx0b : (x == 0) = false := beq_false_of_ne hx0
    simp only [hx0b, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range]
    refine ⟨y, hy, ?_⟩
    have h1 : (decide (y ≤ x) || symp3 x y != 0) = false := by
      simp [hsp, show ¬(y ≤ x) by omega]
    simp [h1, show ¬((x ^^^ y) ≤ y) by omega]
  have hchk_ordered : ∀ x y : Fin 64, x.val ≠ 0 → x.val < y.val → y.val < (x.val ^^^ y.val) →
      symp3 x.val y.val = 0 →
      s3 (dec3 x) * s3 (dec3 y) * s3 (dec3 x + dec3 y) =
      listToSign3 (sp42Certs spId).s64 (dec3 x) * listToSign3 (sp42Certs spId).s64 (dec3 y) *
        listToSign3 (sp42Certs spId).s64 (dec3 x + dec3 y) := by
    intro x y hx0 hxy hyz hsp
    have hmem := hmem_wl x.val y.val x.isLt y.isLt hx0 hxy hyz hsp
    have hres := hall (x.val, y.val, x.val ^^^ y.val, gamma3_sgn x.val y.val) hmem
    simp only [beq_iff_eq] at hres
    let z : Fin 64 := ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow (n := 6) x.isLt y.isLt⟩
    have hadd : dec3 x + dec3 y = dec3 z := (dec3_xor x y).symm
    rw [hadd, ← hagree x, ← hagree y, ← hagree z]
    simp only [listToSign3, enc3_dec3]
    exact hres
  have h0e : (enc3 0).val = 0 := by
    have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
    exact congr_arg Fin.val this
  intro a b ha hb hab hsp
  let x := enc3 a; let y := enc3 b; let z := enc3 (a + b)
  have hdx : dec3 x = a := dec3_enc3 a
  have hdy : dec3 y = b := dec3_enc3 b
  have hdz : dec3 z = a + b := dec3_enc3 (a + b)
  have hx0 : x.val ≠ 0 := fun h => ha (equiv3.injective (Fin.ext (h.trans h0e.symm)))
  have hy0 : y.val ≠ 0 := fun h => hb (equiv3.injective (Fin.ext (h.trans h0e.symm)))
  have hz0 : z.val ≠ 0 := fun h => hab (by
    have h0 : a + b = 0 := equiv3.injective (Fin.ext (h.trans h0e.symm))
    have := congr_arg (a + ·) h0; simpa [pauliIdx_add_cancel_left] using this.symm)
  have hxy_ne : x.val ≠ y.val := fun h => hab (by rw [← hdx, ← hdy, Fin.ext h])
  have hxz_ne : x.val ≠ z.val := fun h => hb (by
    have h1 : a = a + b := hdx.symm.trans ((congr_arg dec3 (Fin.ext h)).trans hdz)
    have := congr_arg (a + ·) h1; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
  have hyz_ne : y.val ≠ z.val := fun h => ha (by
    have h1 : b = a + b := hdy.symm.trans ((congr_arg dec3 (Fin.ext h)).trans hdz)
    have := congr_arg (· + b) h1; simpa [pauliIdx_add_self, add_assoc] using this.symm)
  have hxor_xy : x.val ^^^ y.val = z.val := by
    have h1 : dec3 ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow (n := 6) x.isLt y.isLt⟩ = dec3 z := by
      rw [dec3_xor, hdx, hdy, hdz]
    exact congr_arg Fin.val (equiv3.symm.injective h1)
  have hxor_xz : x.val ^^^ z.val = y.val := by
    have h1 : dec3 ⟨x.val ^^^ z.val, Nat.xor_lt_two_pow (n := 6) x.isLt z.isLt⟩ = dec3 y := by
      rw [dec3_xor, hdx, hdz, hdy, pauliIdx_add_cancel_left]
    exact congr_arg Fin.val (equiv3.symm.injective h1)
  have hxor_yz : y.val ^^^ z.val = x.val := by
    have h1 : dec3 ⟨y.val ^^^ z.val, Nat.xor_lt_two_pow (n := 6) y.isLt z.isLt⟩ = dec3 x := by
      rw [dec3_xor, hdy, hdz, hdx, add_comm a b, pauliIdx_add_cancel_left]
    exact congr_arg Fin.val (equiv3.symm.injective h1)
  have symp3_comm_loc : ∀ p q : Nat, symp3 p q = symp3 q p := fun p q => by
    unfold symp3 dot2_3; rw [Nat.xor_comm, Nat.and_comm (p &&& 7), Nat.and_comm (p >>> 3)]
  have toS0 : ∀ p q : Fin 64, symp (dec3 p) (dec3 q) = 0 → symp3 p.val q.val = 0 := fun p q h => by
    rw [symp_dec3] at h; have hlt := symp3_lt2 p.val q.val
    change ((symp3 p.val q.val : Nat) : ZMod 2) = 0 at h
    generalize symp3 p.val q.val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
  have hsp_xy : symp3 x.val y.val = 0 := toS0 x y (by rw [hdx, hdy]; exact hsp)
  have hsp_yx : symp3 y.val x.val = 0 := by rw [symp3_comm_loc]; exact hsp_xy
  have hsp_xz : symp3 x.val z.val = 0 := toS0 x z (by rw [hdx, hdz, symp_add_right, symp_self, hsp, add_zero])
  have hsp_zx : symp3 z.val x.val = 0 := by rw [symp3_comm_loc]; exact hsp_xz
  have hsp_yz : symp3 y.val z.val = 0 := toS0 y z (by rw [hdy, hdz, symp_add_right, symp_comm b a, hsp, symp_self, add_zero])
  have hsp_zy : symp3 z.val y.val = 0 := by rw [symp3_comm_loc]; exact hsp_yz
  -- Order the three distinct values `x.val, y.val, z.val` (6 permutations)!
  rcases lt_or_gt_of_ne hxy_ne with hxy | hyx
  · rcases lt_or_gt_of_ne hyz_ne with hyz | hzy
    · have h := hchk_ordered x y hx0 hxy (by omega) hsp_xy
      rw [hdx, hdy] at h; exact h
    · rcases lt_or_gt_of_ne hxz_ne with hxz | hzx
      · have h := hchk_ordered x z hx0 hxz (by omega) hsp_xz
        rw [hdx, hdz, pauliIdx_add_cancel_left] at h; linarith
      · have h := hchk_ordered z x hz0 hzx (by rw [Nat.xor_comm, hxor_xz]; omega) hsp_zx
        rw [hdz, hdx, show (a + b) + a = b by rw [add_comm (a + b) a, pauliIdx_add_cancel_left]] at h; linarith
  · rcases lt_or_gt_of_ne hxz_ne with hxz | hzx
    · have h := hchk_ordered y x hy0 hyx (by rw [Nat.xor_comm, hxor_xy]; omega) hsp_yx
      rw [hdx, hdy, add_comm b a] at h; linarith
    · rcases lt_or_gt_of_ne hyz_ne with hyz | hzy
      · have h := hchk_ordered y z hy0 hyz (by omega) hsp_yz
        rw [hdy, hdz, show b + (a + b) = a by rw [add_comm a b, pauliIdx_add_cancel_left]] at h; linarith
      · have h := hchk_ordered z y hz0 hzy (by rw [Nat.xor_comm, hxor_yz]; omega) hsp_zy
        rw [hdz, hdy, show (a + b) + b = a by rw [add_assoc, pauliIdx_add_self, add_zero]] at h; linarith

/-! ### Section 2: `B₃₆`, `otherC27`, `pop9`/`pop36`, `lines27`, and `M36` Algebraic Properties -/

lemma symp3_comm (a b : Nat) : symp3 a b = symp3 b a := by
  unfold symp3 dot2_3; rw [Nat.xor_comm, Nat.and_comm (a &&& 7), Nat.and_comm (a >>> 3)]

lemma A27_list_len : A27_list.length = 27 := rfl
lemma B36_list_len : B36_list.length = 36 := rfl

lemma A27_val_props : ∀ i : Fin 27,
    A27_val i.val ≠ 0 ∧ A27_val i.val < 64 ∧ Q3_form 9 (A27_val i.val) = 0 := by decide

lemma B36_val_props : ∀ i : Fin 36,
    B36_val i.val ≠ 0 ∧ B36_val i.val < 64 ∧ Q3_form 9 (B36_val i.val) = 1 := by decide

lemma B36_pt_mem_nz (i : Fin 36) : dec3 (B36_pt i) ∈ nzPts 3 := by
  have hp := B36_val_props i
  simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
  intro h; apply hp.1
  have := congr_arg (fun w => (enc3 w).val) h
  rw [enc3_dec3] at this
  have h0 : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
  rw [h0] at this; exact this

lemma B36_pt_quadForm (i : Fin 36) : quadForm c0_09 (dec3 (B36_pt i)) = 1 := by
  have hp := (B36_val_props i).2.2
  simp only [c0_09, quadForm_dec3, B36_pt, hp]; rfl

lemma A27_idxOf_val (i : Fin 27) : A27_list.idxOf? (A27_val i.val) = some i.val := by
  have hilt : i.val < A27_list.length := by rw [A27_list_len]; exact i.isLt
  have hget : A27_val i.val = A27_list[i.val] := by
    unfold A27_val; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]
  rw [hget, List.idxOf?_eq_some_iff]
  refine ⟨hilt, rfl, fun j hj heq => ?_⟩
  have hj27 : j < 27 := by omega
  have heq' : A27_val j = A27_val i.val := by
    unfold A27_val
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < A27_list.length),
      List.getElem?_eq_getElem hilt, heq]
  exact absurd (congr_arg Fin.val (A27_val_inj (i := ⟨j, hj27⟩) (j := i) heq')) (Nat.ne_of_lt hj)

lemma B36_idxOf_val (i : Fin 36) : B36_list.idxOf? (B36_val i.val) = some i.val := by
  have hilt : i.val < B36_list.length := by rw [B36_list_len]; exact i.isLt
  have hget : B36_val i.val = B36_list[i.val] := by
    unfold B36_val; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]
  rw [hget, List.idxOf?_eq_some_iff]
  refine ⟨hilt, rfl, fun j hj heq => ?_⟩
  have hj36 : j < 36 := by omega
  have heq' : B36_val j = B36_val i.val := by
    unfold B36_val
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < B36_list.length),
      List.getElem?_eq_getElem hilt, heq]
  exact absurd (congr_arg Fin.val (B36_val_inj (i := ⟨j, hj36⟩) (j := i) heq')) (Nat.ne_of_lt hj)

lemma A27_idxOf_none_of_B36 (i : Fin 36) : A27_list.idxOf? (B36_val i.val) = none := by
  rw [List.idxOf?_eq_none_iff]
  intro hmem
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
  have hj27 : j < 27 := by rwa [A27_list_len] at hj
  have h2 := (B36_val_props i).2.2
  have hget : A27_val j = A27_list[j] := by
    unfold A27_val; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have heq' : A27_val j = B36_val i.val := hget.trans heq
  have h1 : Q3_form 9 (B36_val i.val) = 0 := heq' ▸ (A27_val_props ⟨j, hj27⟩).2.2
  omega

/-- Small pure-kernel check confirming `rep27[r]` signs `∈ {±1}` and `f₂₇(rep27[1]) = 12`, `f₂₇(rep27[2]) = 13`. -/
def checkRep27Extra : Bool :=
  ((List.range 3).all fun r =>
    ((rep27_vecs.getD r []).length == 27) &&
    ((List.range 27).all fun i =>
      let v := (rep27_vecs.getD r []).getD i 0
      v == 1 || v == -1)) &&
  (lines27_list.foldl (fun acc (a, b, c, g) =>
    if g * (rep27_vecs.getD 1 []).getD a 0 * (rep27_vecs.getD 1 []).getD b 0 *
       (rep27_vecs.getD 1 []).getD c 0 == -1 then acc + 1 else acc) 0 == 12) &&
  (lines27_list.foldl (fun acc (a, b, c, g) =>
    if g * (rep27_vecs.getD 2 []).getD a 0 * (rep27_vecs.getD 2 []).getD b 0 *
       (rep27_vecs.getD 2 []).getD c 0 == -1 then acc + 1 else acc) 0 == 13) &&
  (lines27_list.foldl (fun acc (a, b, c, g) =>
    if g * (rep27_vecs.getD 0 []).getD a 0 * (rep27_vecs.getD 0 []).getD b 0 *
       (rep27_vecs.getD 0 []).getD c 0 == -1 then acc + 1 else acc) 0 == 9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma checkRep27Extra_ok : checkRep27Extra = true := by rfl

lemma dpll_all_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) :
    ∀ {k}, k < n → p k = true := fun {k} hk =>
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

lemma dpll_getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : Nat} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma dpll_getD_map {α β : Type*} (l : List α) (f : α → β) (d : β) {i : Nat} (hi : i < l.length) :
    (l.map f).getD i d = f l[i] := by
  rw [dpll_getD_eq_getElem _ _ (by simp [hi]), List.getElem_map]

lemma dpll_getD_map_range {α : Type*} (n : Nat) (f : Nat → α) (d : α) {i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [dpll_getD_map _ _ _ (by simp [hi]), List.getElem_range]

lemma dpll_foldl_sum_range (n : Nat) (f : Nat → Nat) (a : Nat) :
    (List.range n).foldl (fun acc k => acc + f k) a = a + ∑ k : Fin n, f k.val := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Fin.sum_univ_castSucc]
    dsimp; omega

lemma dpll_list_range_filter_len (n : Nat) (p : Nat → Bool) :
    ((List.range n).filter p).length =
      ((Finset.univ : Finset (Fin n)).filter fun k => p k.val = true).card := by
  have h1 : ∀ l : List Nat, (l.filter p).length = l.foldl (fun acc k => acc + if p k then 1 else 0) 0 := by
    intro l
    have hgen : ∀ a, a + (l.filter p).length = l.foldl (fun acc k => acc + if p k then 1 else 0) a := by
      induction l with
      | nil => intro a; simp
      | cons x xs ih =>
        intro a; simp only [List.filter_cons, List.foldl_cons]
        cases hp : p x <;> simp [← ih] <;> omega
    simpa using hgen 0
  rw [h1, dpll_foldl_sum_range, zero_add, Finset.card_filter]

lemma rep27_val_pm1 (r : Fin 3) (i : Fin 27) : rep27_val r i.val = 1 ∨ rep27_val r i.val = -1 := by
  have h := checkRep27Extra_ok
  unfold checkRep27Extra at h
  simp only [Bool.and_eq_true] at h
  have hr := dpll_all_range h.1.1.1 r.isLt
  simp only [Bool.and_eq_true] at hr
  have hi := dpll_all_range hr.2 i.isLt
  simp only [Bool.or_eq_true, beq_iff_eq] at hi
  exact hi

lemma M36_val_symm (oid : Nat) (i j : Fin 36) : M36_val oid i.val j.val = M36_val oid j.val i.val := by
  unfold M36_val
  by_cases hij : i.val = j.val
  · rw [hij]
  · have hsp : symp3 (B36_val i.val) (B36_val j.val) = symp3 (B36_val j.val) (B36_val i.val) :=
      symp3_comm _ _
    by_cases hs : symp3 (B36_val i.val) (B36_val j.val) = 0
    · have hs' : symp3 (B36_val j.val) (B36_val i.val) = 0 := hsp.symm.trans hs
      simp only [beq_false_of_ne hij, beq_false_of_ne (Ne.symm hij), hs, hs', bne_self_eq_false,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, Nat.xor_comm (B36_val j.val) (B36_val i.val)]
      have hgam : gamma3_sgn (B36_val i.val) (B36_val j.val) =
          gamma3_sgn (B36_val j.val) (B36_val i.val) := by
        have h1 : gammaSgn (dec3 (B36_pt i)) (dec3 (B36_pt j)) =
            gammaSgn (dec3 (B36_pt j)) (dec3 (B36_pt i)) :=
          gammaSgn_comm (by simp only [symp_dec3, B36_pt, hs]; rfl)
        simpa only [gammaSgn_dec3, B36_pt] using h1
      rw [hgam]
    · have hs' : symp3 (B36_val j.val) (B36_val i.val) ≠ 0 := fun h => hs (hsp.trans h)
      simp [hij, Ne.symm hij, hs, hs']

lemma M36_val_spec (r : Fin 3) (i j : Fin 36) :
    (M36_val r.val i.val j.val = 0 ∨ M36_val r.val i.val j.val = 1 ∨ M36_val r.val i.val j.val = -1) ∧
    (M36_val r.val i.val j.val ≠ 0 ↔ i ≠ j ∧ symp3 (B36_val i.val) (B36_val j.val) = 0) := by
  by_cases hcond : i ≠ j ∧ symp3 (B36_val i.val) (B36_val j.val) = 0
  · rcases hcond with ⟨hne, hsp⟩
    have hne_v : i.val ≠ j.val := Fin.val_ne_of_ne hne
    have hpi_ne : dec3 (B36_pt i) ≠ dec3 (B36_pt j) :=
      fun h => hne (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))
    have hadd_ne0 : dec3 (B36_pt i) + dec3 (B36_pt j) ≠ 0 := fun h => hpi_ne (by
      have := congr_arg (dec3 (B36_pt i) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
    have hsp_p : symp (dec3 (B36_pt i)) (dec3 (B36_pt j)) = 0 := by
      simp only [symp_dec3, B36_pt, hsp]; rfl
    have hadd_Q : quadForm c0_09 (dec3 (B36_pt i) + dec3 (B36_pt j)) = 0 := by
      rw [quadForm_add, B36_pt_quadForm i, B36_pt_quadForm j, hsp_p]; decide
    let xF : Fin 64 := ⟨B36_val i.val ^^^ B36_val j.val,
      Nat.xor_lt_two_pow (n := 6) (B36_pt i).isLt (B36_pt j).isLt⟩
    have hdx : dec3 xF = dec3 (B36_pt i) + dec3 (B36_pt j) := dec3_xor (B36_pt i) (B36_pt j)
    have hx0 : xF.val ≠ 0 := fun h => hadd_ne0 (by
      rw [← hdx, show xF = 0 from Fin.ext h, dec3_zero])
    have hxQ : Q3_form 9 xF.val = 0 := by
      rw [← hdx, c0_09, quadForm_dec3] at hadd_Q
      have hlt := Q3_form_lt2 9 xF.val
      generalize Q3_form 9 xF.val = m at hlt hadd_Q ⊢; interval_cases m; rfl; exact absurd hadd_Q (by decide)
    obtain ⟨idxA, hidxA⟩ := A27_val_surj xF hx0 hxQ
    have hidxOf : A27_list.idxOf? (B36_val i.val ^^^ B36_val j.val) = some idxA.val := by
      change A27_list.idxOf? xF.val = some idxA.val
      rw [← hidxA]; exact A27_idxOf_val idxA
    have hm_eq : M36_val r.val i.val j.val =
        gamma3_sgn (B36_val i.val) (B36_val j.val) * rep27_val r idxA.val := by
      unfold M36_val rep27_val
      simp only [beq_false_of_ne hne_v, hsp, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, hidxOf]
    have hg : gamma3_sgn (B36_val i.val) (B36_val j.val) = 1 ∨
        gamma3_sgn (B36_val i.val) (B36_val j.val) = -1 := by
      have h1 := gammaSgn_eq_pm1 (dec3 (B36_pt i)) (dec3 (B36_pt j))
      simpa only [gammaSgn_dec3, B36_pt] using h1
    have hr := rep27_val_pm1 r idxA
    rw [hm_eq]
    rcases hg with hg | hg <;> rcases hr with hr | hr <;> rw [hg, hr] <;> simp [hne, hsp]
  · have hm0 : M36_val r.val i.val j.val = 0 := by
      unfold M36_val
      have hcond_b : (i.val == j.val || symp3 (B36_val i.val) (B36_val j.val) != 0) = true := by
        by_cases heq : i.val = j.val
        · simp [heq]
        · have hne : i ≠ j := fun h => heq (congr_arg Fin.val h)
          have hsp : symp3 (B36_val i.val) (B36_val j.val) ≠ 0 := fun h => hcond ⟨hne, h⟩
          simp [heq, hsp]
      rw [if_pos hcond_b]
    rw [hm0]; simp [hcond]

lemma M36_edge_eq (r : Fin 3) {s3 : PauliIdx 3 → ℤ}
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val)
    (i j : Fin 36) (hne0 : M36_val r.val i.val j.val ≠ 0) :
    let pi := dec3 (B36_pt i); let pj := dec3 (B36_pt j)
    pi ≠ pj ∧ symp pi pj = 0 ∧
    M36_val r.val i.val j.val * s3 pi * s3 pj =
      gammaSgn pi pj * s3 pi * s3 pj * s3 (pi + pj) := by
  have hcond := (M36_val_spec r i j).2.mp hne0
  rcases hcond with ⟨hne, hsp⟩
  have hne_v : i.val ≠ j.val := Fin.val_ne_of_ne hne
  have hpi_ne : dec3 (B36_pt i) ≠ dec3 (B36_pt j) :=
    fun h => hne (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))
  have hsp_p : symp (dec3 (B36_pt i)) (dec3 (B36_pt j)) = 0 := by
    simp only [symp_dec3, B36_pt, hsp]; rfl
  refine ⟨hpi_ne, hsp_p, ?_⟩
  have hadd_ne0 : dec3 (B36_pt i) + dec3 (B36_pt j) ≠ 0 := fun h => hpi_ne (by
    have := congr_arg (dec3 (B36_pt i) + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  have hadd_Q : quadForm c0_09 (dec3 (B36_pt i) + dec3 (B36_pt j)) = 0 := by
    rw [quadForm_add, B36_pt_quadForm i, B36_pt_quadForm j, hsp_p]; decide
  let xF : Fin 64 := ⟨B36_val i.val ^^^ B36_val j.val,
    Nat.xor_lt_two_pow (n := 6) (B36_pt i).isLt (B36_pt j).isLt⟩
  have hdx : dec3 xF = dec3 (B36_pt i) + dec3 (B36_pt j) := dec3_xor (B36_pt i) (B36_pt j)
  have hx0 : xF.val ≠ 0 := fun h => hadd_ne0 (by
    rw [← hdx, show xF = 0 from Fin.ext h, dec3_zero])
  have hxQ : Q3_form 9 xF.val = 0 := by
    rw [← hdx, c0_09, quadForm_dec3] at hadd_Q
    have hlt := Q3_form_lt2 9 xF.val
    generalize Q3_form 9 xF.val = m at hlt hadd_Q ⊢; interval_cases m; rfl; exact absurd hadd_Q (by decide)
  obtain ⟨idxA, hidxA⟩ := A27_val_surj xF hx0 hxQ
  have hidxOf : A27_list.idxOf? (B36_val i.val ^^^ B36_val j.val) = some idxA.val := by
    change A27_list.idxOf? xF.val = some idxA.val
    rw [← hidxA]; exact A27_idxOf_val idxA
  have hm_eq : M36_val r.val i.val j.val =
      gamma3_sgn (B36_val i.val) (B36_val j.val) * rep27_val r idxA.val := by
    unfold M36_val rep27_val
    simp only [beq_false_of_ne hne_v, hsp, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, hidxOf]
  have hadd_eq : dec3 (B36_pt i) + dec3 (B36_pt j) = dec3 (A27_pt idxA) := by
    rw [← hdx]; congr 1; exact Fin.ext hidxA.symm
  rw [hm_eq, hadd_eq, hA27 idxA, gammaSgn_dec3]
  change (gamma3_sgn (B36_val i.val) (B36_val j.val) * rep27_val r idxA.val) *
      s3 (dec3 (B36_pt i)) * s3 (dec3 (B36_pt j)) =
    gamma3_sgn (B36_val i.val) (B36_val j.val) * s3 (dec3 (B36_pt i)) * s3 (dec3 (B36_pt j)) *
      rep27_val r idxA.val
  ring

/-! #### Bitwise & `pop9` / `pop36` Helpers -/

lemma testBit_eq_shr_and1 (x k : Nat) :
    ((x >>> k) &&& 1) = if x.testBit k then 1 else 0 := by
  rw [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod]
  split_ifs with h <;> simp_all

lemma shr_and1_eq_one_iff (x k : Nat) :
    ((x >>> k) &&& 1) = 1 ↔ x.testBit k = true := by
  rw [testBit_eq_shr_and1]; cases x.testBit k <;> simp

lemma shr_and1_eq_zero_iff (x k : Nat) :
    ((x >>> k) &&& 1) = 0 ↔ x.testBit k = false := by
  rw [testBit_eq_shr_and1]; cases x.testBit k <;> simp

lemma testBit_bitOr_single (m u i : Nat) :
    (m ||| (1 <<< u)).testBit i = (m.testBit i || decide (i = u)) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hiu : i = u
  · subst hiu; simp
  · have h0 : (decide (u ≤ i) && (1 : Nat).testBit (i - u)) = false := by
      by_cases hle : u ≤ i
      · have h1 : (1 : Nat).testBit (i - u) = false := by
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
            Nat.div_eq_of_lt (show 1 < 2 ^ (i - u) from Nat.one_lt_two_pow (by omega))]
        simp [hle, h1]
      · simp [hle]
    simp [hiu, h0]

lemma foldl_or_bit_testBit (L : List Nat) (f : Nat → Bool) (m0 k : Nat) :
    (L.foldl (fun m v => if f v then m ||| (1 <<< v) else m) m0).testBit k =
      (m0.testBit k || (L.any fun v => f v && decide (k = v))) := by
  induction L generalizing m0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    cases hfx : f x
    · simp
    · simp only [↓reduceIte, Bool.true_and, testBit_bitOr_single, Bool.or_assoc]

lemma foldl_or_val_testBit (L : List Nat) (m0 k : Nat) :
    (L.foldl (fun m v => m ||| (1 <<< v)) m0).testBit k =
      (m0.testBit k || L.any (fun v => decide (k = v))) := by
  have h := foldl_or_bit_testBit L (fun _ => true) m0 k
  simpa using h

lemma coreTables_spec :
    otherC27_list.length = 27 ∧
    lines27_list.length = 45 ∧
    (∀ x < 512, pop9 x = (List.range 9).foldl (fun acc b => acc + ((x >>> b) &&& 1)) 0) ∧
    (∀ k < 27, let ck := otherC27_list.getD k 0
      ck ≠ 0 ∧ ck ≠ 9 ∧ ck < 64 ∧ Q3_0 ck = 1 ∧
      (orb1_tables.slVerts.getD k []).length = 16 ∧
      (orb2_tables.slVerts.getD k []).length = 16) ∧
    (∀ k < 26, otherC27_list.getD k 0 < otherC27_list.getD (k + 1) 0) ∧
    (∀ c < 64, c ≠ 0 → c ≠ 9 → Q3_0 c = 1 → otherC27_list.contains c = true) ∧
    (∀ u < 36,
      pop36 (orb1_tables.pAdj.getD u 0 ||| orb1_tables.nAdj.getD u 0) = 15 ∧
      (orb1_tables.pAdj.getD u 0 &&& orb1_tables.nAdj.getD u 0) = 0 ∧
      pop36 (orb2_tables.pAdj.getD u 0 ||| orb2_tables.nAdj.getD u 0) = 15 ∧
      (orb2_tables.pAdj.getD u 0 &&& orb2_tables.nAdj.getD u 0) = 0) := by
  have h := checkDPLLCoreTables_ok
  unfold checkDPLLCoreTables at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  refine ⟨h1, h2, fun x hx => ?_, fun k hk => ?_, fun k hk => ?_, fun c hc hc0 hc9 hq => ?_, fun u hu => ?_⟩
  · have := dpll_all_range h3 hx; exact beq_iff_eq.mp this
  · have hk' := dpll_all_range h4 hk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at hk'
    exact ⟨hk'.1.1.1.1.1, hk'.1.1.1.1.2, hk'.1.1.1.2, hk'.1.1.2, hk'.1.2, hk'.2⟩
  · exact decide_eq_true_eq.mp (dpll_all_range h5 hk)
  · have hc' := dpll_all_range h6 hc
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, hc0, hc9, hq, not_false_eq_true, and_self,
      decide_true, ↓reduceIte] at hc'
    exact hc'
  · have hu' := dpll_all_range h7 hu
    simp only [Bool.and_eq_true, beq_iff_eq] at hu'
    exact ⟨hu'.1.1.1, hu'.1.1.2, hu'.1.2, hu'.2⟩

lemma pop9_eq_card (x : Nat) (hx : x < 512) :
    pop9 x = ((Finset.univ : Finset (Fin 9)).filter fun b => x.testBit b.val = true).card := by
  rw [coreTables_spec.2.2.1 x hx, dpll_foldl_sum_range, zero_add, Finset.card_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [testBit_eq_shr_and1]

lemma pop36_eq_card (m : Nat) :
    pop36 m = ((Finset.univ : Finset (Fin 36)).filter fun b => m.testBit b.val = true).card := by
  have h511 : ∀ n : Nat, (n &&& 511) < 512 := fun n => by
    have : (n &&& (2 ^ 9 - 1)) = n % 2 ^ 9 := Nat.and_two_pow_sub_one_eq_mod n 9
    change (n &&& (2 ^ 9 - 1)) < 2 ^ 9
    rw [this]; exact Nat.mod_lt _ (by decide)
  have htb : ∀ (q : Nat) (r : Fin 9), ((m >>> q) &&& 511).testBit r.val = m.testBit (q + r.val) := by
    intro q r
    have h511_tb : ∀ x : Fin 9, (511 : Nat).testBit x.val = true := by decide
    have h1 : (511 : Nat).testBit r.val = true := h511_tb r
    rw [Nat.testBit_and, Nat.testBit_shiftRight, h1, Bool.and_true]
  have hpop : ∀ q : Nat, pop9 ((m >>> q) &&& 511) =
      ∑ r : Fin 9, if m.testBit (q + r.val) = true then 1 else 0 := fun q => by
    rw [pop9_eq_card _ (h511 _), Finset.card_filter]
    refine Finset.sum_congr rfl fun r _ => by rw [htb]
  unfold pop36
  change (pop9 ((m &&& 511)) + pop9 (((m >>> 9) &&& 511))) +
      (pop9 (((m >>> 18) &&& 511)) + pop9 (((m >>> 27) &&& 511))) = _
  have h0 : pop9 (m &&& 511) = ∑ r : Fin 9, if m.testBit (0 + r.val) = true then 1 else 0 := by
    simpa using hpop 0
  rw [h0, hpop 9, hpop 18, hpop 27, Finset.card_filter]
  have hfin : ∀ (n : Nat) (f : Nat → Nat), (∑ r : Fin n, f r.val) = ∑ i ∈ Finset.range n, f i :=
    fun n f => Fin.sum_univ_eq_sum_range f n
  rw [hfin 9 (fun i => if m.testBit (0 + i) = true then 1 else 0),
      hfin 9 (fun i => if m.testBit (9 + i) = true then 1 else 0),
      hfin 9 (fun i => if m.testBit (18 + i) = true then 1 else 0),
      hfin 9 (fun i => if m.testBit (27 + i) = true then 1 else 0),
      hfin 36 (fun i => if m.testBit i = true then 1 else 0)]
  have hsplit : ∀ a b (f : Nat → Nat),
      ∑ i ∈ Finset.range (a + b), f i = (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range b, f (a + i) :=
    fun a b f => Finset.sum_range_add f a b
  have h36 : (36 : Nat) = (9 + 9) + (9 + 9) := rfl
  conv_rhs => rw [h36, hsplit 18 18, hsplit 9 9, hsplit 9 9]
  simp only [Nat.zero_add, Nat.add_assoc]
  exact congr_arg _ (congr_arg _ (congr_arg _ (Finset.sum_congr rfl fun i _ => by rw [← Nat.add_assoc])))

lemma pop36_eq_card_of_iff (m : Nat) (P : Fin 36 → Prop) [DecidablePred P]
    (hiff : ∀ v : Fin 36, m.testBit v.val = true ↔ P v) :
    pop36 m = ((Finset.univ : Finset (Fin 36)).filter P).card := by
  rw [pop36_eq_card]
  exact congr_arg Finset.card (Finset.ext fun v => by simp [hiff v])

lemma card_even_of_symm_irrefl {n : Nat} (S : Finset (Fin n × Fin n))
    (hsym : ∀ a b, (a, b) ∈ S → (b, a) ∈ S)
    (hirr : ∀ a, (a, a) ∉ S) :
    2 ∣ S.card := by
  let Slt := S.filter fun p => p.1.val < p.2.val
  let Sgt := S.filter fun p => p.2.val < p.1.val
  have hu : S = Slt ∪ Sgt := by
    ext ⟨a, b⟩
    simp only [Slt, Sgt, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      have hne : a.val ≠ b.val := fun heq => hirr a (Fin.ext heq ▸ h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left; exact ⟨h, hlt⟩
      · right; exact ⟨h, hgt⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdis : Disjoint Slt Sgt := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
  have hbij : Slt.card = Sgt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
    · rintro ⟨a, b⟩ h; simp only [Slt, Sgt, Finset.mem_filter] at h ⊢; exact ⟨hsym a b h.1, h.2⟩
    · rintro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
      simp only [Slt, Sgt, Finset.mem_filter] at h ⊢; exact ⟨hsym a b h.1, h.2⟩
  rw [hu, Finset.card_union_of_disjoint hdis, hbij]
  exact ⟨Sgt.card, by omega⟩

def otherC27_pt (k : Fin 27) : Fin 64 :=
  ⟨otherC27_list.getD k.val 0, (coreTables_spec.2.2.2.1 k.val k.isLt).2.2.1⟩

lemma otherC27_val_inj {i j : Fin 27} (h : otherC27_list.getD i.val 0 = otherC27_list.getD j.val 0) :
    i = j := by
  by_contra hne
  have hstep : ∀ k < 26, otherC27_list.getD k 0 < otherC27_list.getD (k + 1) 0 :=
    coreTables_spec.2.2.2.2.1
  have hmono : ∀ {a b : Nat}, a < b → b < 27 → otherC27_list.getD a 0 < otherC27_list.getD b 0 := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hab) with hlt | rfl
      · exact lt_trans (ih hlt (by omega)) (hstep b (by omega))
      · exact hstep a (by omega)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact absurd h (Nat.ne_of_lt (hmono hlt j.isLt))
  · exact absurd h.symm (Nat.ne_of_lt (hmono hgt i.isLt))

lemma otherC27_pt_mem_ellCenters (k : Fin 27) :
    dec3 (otherC27_pt k) ∈ ellCenters 3 ∧ dec3 (otherC27_pt k) ≠ c0_09 := by
  have hk := coreTables_spec.2.2.2.1 k.val k.isLt
  refine ⟨?_, ?_⟩
  · simp only [ellCenters, Finset.mem_filter, Finset.mem_univ, true_and, quadForm0_dec3, otherC27_pt, hk.2.2.2.1]
    rfl
  · intro h; apply hk.2.1
    have := congr_arg (fun w => (enc3 w).val) h
    simpa [c0_09, enc3_dec3, otherC27_pt] using this

lemma otherC27_pt_surj {c : PauliIdx 3} (hc : c ∈ ellCenters 3) (hne : c ≠ c0_09) :
    ∃ k : Fin 27, dec3 (otherC27_pt k) = c := by
  have h0e : (enc3 0).val = 0 := by
    have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
    exact congr_arg Fin.val this
  have hq : Q3_0 (enc3 c).val = 1 := by
    have h := (Finset.mem_filter.mp hc).2
    rw [← dec3_enc3 c, quadForm0_dec3] at h
    have hlt := Q3_0_lt2 (enc3 c).val
    generalize Q3_0 (enc3 c).val = m at hlt h ⊢; interval_cases m; exact absurd h (by decide); rfl
  have hc0 : (enc3 c).val ≠ 0 := by
    intro h; rw [h] at hq; exact absurd hq (by decide)
  have hc9 : (enc3 c).val ≠ 9 := fun h => hne (by
    rw [← dec3_enc3 c, c0_09]; congr 1; exact Fin.ext h)
  have hmem := coreTables_spec.2.2.2.2.2.1 (enc3 c).val (enc3 c).isLt hc0 hc9 hq
  rw [List.contains_eq_mem, decide_eq_true_eq] at hmem
  obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hmem
  have hk27 : k < 27 := by rwa [coreTables_spec.1] at hk
  refine ⟨⟨k, hk27⟩, ?_⟩
  have hpt : otherC27_pt ⟨k, hk27⟩ = enc3 c := Fin.ext (by
    simp only [otherC27_pt, dpll_getD_eq_getElem _ _ hk, heq])
  rw [hpt, dec3_enc3]

/-! #### Exact `A₂₇ ⊔ B₃₆` Splits for `W(5,2)` and `Q⁻(5,2)` Slices -/

/-- Ordered frustrated edges `(u, v) ∈ Fin 36 × Fin 36` in `B₃₆` for orbit `oid`. -/
def F36_set (oid : Nat) (s3 : PauliIdx 3 → ℤ) : Finset (Fin 36 × Fin 36) :=
  Finset.univ.filter fun uv =>
    M36_val oid uv.1.val uv.2.val * s3 (dec3 (B36_pt uv.1)) * s3 (dec3 (B36_pt uv.2)) = -1

lemma F36_set_even (oid : Nat) (s3 : PauliIdx 3 → ℤ) : 2 ∣ (F36_set oid s3).card := by
  refine card_even_of_symm_irrefl _ ?_ ?_
  · intro a b hab
    simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    rw [M36_val_symm oid b a]; linarith
  · intro a ha
    simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and, M36_val, beq_self_eq_true,
      Bool.true_or, ↓reduceIte, zero_mul] at ha
    omega

private lemma dpll_card_four_split {α : Type*} [DecidableEq α] (U : Finset (α × α)) (f : α → ZMod 2) :
    U.card =
      (U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 0).card +
      (U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 1).card +
      (U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 0).card +
      (U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 1).card := by
  let PAA := U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 0
  let PBB := U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 1
  let PBA := U.filter fun pq => f pq.1 = 1 ∧ f pq.2 = 0
  let PAB := U.filter fun pq => f pq.1 = 0 ∧ f pq.2 = 1
  have hu : U = (PAA ∪ PBB) ∪ (PBA ∪ PAB) := by
    ext ⟨p, q⟩; simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases zmod2_cases (f p) with h1 | h1 <;> rcases zmod2_cases (f q) with h2 | h2
      · left; left; exact ⟨hp, h1, h2⟩
      · right; right; exact ⟨hp, h1, h2⟩
      · right; left; exact ⟨hp, h1, h2⟩
      · left; right; exact ⟨hp, h1, h2⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)) <;> exact h
  have hd1 : Disjoint PAA PBB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd2 : Disjoint PBA PAB := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PBA, PAB, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd3 : Disjoint (PAA ∪ PBB) (PBA ∪ PAB) := Finset.disjoint_left.mpr fun _ h1 h2 => by
    simp only [PAA, PBB, PBA, PAB, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨_, h1a, h1b⟩ | ⟨_, h1a, h1b⟩ <;> rcases h2 with ⟨_, h2a, h2b⟩ | ⟨_, h2a, h2b⟩
    · rw [h1a] at h2a; exact absurd h2a (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1b] at h2b; exact absurd h2b (by decide)
    · rw [h1a] at h2a; exact absurd h2a (by decide)
  conv_lhs => rw [hu]
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint hd2]
  dsimp only [PAA, PBB, PBA, PAB]
  ring

/-- General `A₂₇ ⊔ B₃₆` split for any commuting-closed subset `S ⊆ nzPts 3`. -/
lemma frustPairs_Q09_split {S : Finset (PauliIdx 3)} (hsub : S ⊆ nzPts 3)
    (hclosed : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → symp p q = 0 → p + q ∈ S)
    (s3 : PauliIdx 3 → ℤ) :
    let SA := S.filter fun p => quadForm c0_09 p = 0
    let SB := S.filter fun p => quadForm c0_09 p = 1
    let NBB := ((SB ×ˢ SB).filter fun pq =>
      pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
      gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1).card
    frustPairs S s3 = frustPairs SA s3 + 3 * NBB := by
  intro SA SB NBB
  let P := (S ×ˢ S).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧ gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1
  let PAA := P.filter fun pq => quadForm c0_09 pq.1 = 0 ∧ quadForm c0_09 pq.2 = 0
  let PBB := P.filter fun pq => quadForm c0_09 pq.1 = 1 ∧ quadForm c0_09 pq.2 = 1
  let PBA := P.filter fun pq => quadForm c0_09 pq.1 = 1 ∧ quadForm c0_09 pq.2 = 0
  let PAB := P.filter fun pq => quadForm c0_09 pq.1 = 0 ∧ quadForm c0_09 pq.2 = 1
  have hAA : PAA.card = frustPairs SA s3 := by
    unfold frustPairs
    refine Finset.card_bij (fun pq _ => pq) ?_ (fun _ _ _ _ h => h) ?_
    · rintro ⟨p, q⟩ h; simp only [PAA, P, SA, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.2.1⟩, ⟨h.1.1.2, h.2.2⟩⟩, h.1.2⟩
    · rintro ⟨p, q⟩ h; refine ⟨(p, q), ?_, rfl⟩
      simp only [PAA, P, SA, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.1.2.1⟩, h.2⟩, h.1.1.2, h.1.2.2⟩
  have hBB : PBB.card = NBB := by
    refine Finset.card_bij (fun pq _ => pq) ?_ (fun _ _ _ _ h => h) ?_
    · rintro ⟨p, q⟩ h; simp only [PBB, P, SB, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.2.1⟩, ⟨h.1.1.2, h.2.2⟩⟩, h.1.2⟩
    · rintro ⟨p, q⟩ h; refine ⟨(p, q), ?_, rfl⟩
      simp only [PBB, P, SB, Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.1.2.1⟩, h.2⟩, h.1.1.2, h.1.2.2⟩
  have hBA : PBA.card = NBB := by
    rw [← hBB]
    refine Finset.card_bij (fun pq _ => (pq.1, pq.1 + pq.2)) ?_ ?_ ?_
    · rintro ⟨p, q⟩ h
      simp only [PBA, PBB, P, Finset.mem_filter, Finset.mem_product] at h ⊢
      rcases h with ⟨⟨⟨hpS, hqS⟩, hne, hsp, hfr⟩, hqp, hqq⟩
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp (hsub hqS)).1
      refine ⟨⟨⟨hpS, hclosed p hpS q hqS hne hsp⟩, ?_, ?_, ?_⟩, hqp, ?_⟩
      · intro hc; exact hq0 (by have := congr_arg (p + ·) hc; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
      · rw [symp_add_right, symp_self, hsp, add_zero]
      · rw [gammaSgn_add_right hsp, pauliIdx_add_cancel_left]; linarith
      · rw [quadForm_add, hqp, hqq, hsp]; decide
    · rintro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
      simp only [Prod.mk.injEq] at h
      refine Prod.ext h.1 ?_
      have h2 := congr_arg (p1 + ·) h.2; rw [← h.1] at h2; simpa [pauliIdx_add_cancel_left] using h2
    · rintro ⟨a, b⟩ h
      simp only [PBB, P, Finset.mem_filter, Finset.mem_product] at h
      rcases h with ⟨⟨⟨haS, hbS⟩, hne, hsp, hfr⟩, hqa, hqb⟩
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp (hsub hbS)).1
      refine ⟨(a, a + b), ?_, Prod.ext rfl (pauliIdx_add_cancel_left a b)⟩
      simp only [PBA, P, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨haS, hclosed a haS b hbS hne hsp⟩, ?_, ?_, ?_⟩, hqa, ?_⟩
      · intro hc; exact hb0 (by have := congr_arg (a + ·) hc; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm)
      · rw [symp_add_right, symp_self, hsp, add_zero]
      · rw [gammaSgn_add_right hsp, pauliIdx_add_cancel_left]; linarith
      · rw [quadForm_add, hqa, hqb, hsp]; decide
  have hAB : PAB.card = NBB := by
    rw [← hBA]
    refine Finset.card_bij (fun pq _ => (pq.2, pq.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
    · rintro ⟨p, q⟩ h
      simp only [PAB, PBA, P, Finset.mem_filter, Finset.mem_product] at h ⊢
      rcases h with ⟨⟨⟨hpS, hqS⟩, hne, hsp, hfr⟩, hqp, hqq⟩
      refine ⟨⟨⟨hqS, hpS⟩, Ne.symm hne, by rwa [symp_comm], ?_⟩, hqq, hqp⟩
      rw [gammaSgn_comm (by rwa [symp_comm]), add_comm q p]; linarith
    · rintro ⟨a, b⟩ h
      simp only [PBA, P, Finset.mem_filter, Finset.mem_product] at h
      rcases h with ⟨⟨⟨haS, hbS⟩, hne, hsp, hfr⟩, hqa, hqb⟩
      refine ⟨(b, a), ?_, rfl⟩
      simp only [PAB, P, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hbS, haS⟩, Ne.symm hne, by rwa [symp_comm], ?_⟩, hqb, hqa⟩
      rw [gammaSgn_comm (by rwa [symp_comm]), add_comm b a]; linarith
  change P.card = _
  rw [dpll_card_four_split P (quadForm c0_09)]
  change PAA.card + PBB.card + PBA.card + PAB.card = _
  rw [hAA, hBB, hBA, hAB]; omega

lemma frustPairs_W52_A27_B36_split (r : Fin 3) {s3 : PauliIdx 3 → ℤ}
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) :
    frustPairs (nzPts 3) s3 = frustPairs (Qminus c0_09) s3 + 3 * (F36_set r.val s3).card := by
  have hcl : ∀ p ∈ nzPts 3, ∀ q ∈ nzPts 3, p ≠ q → symp p q = 0 → p + q ∈ nzPts 3 := by
    intro p _ q _ hne _
    simp only [nzPts, Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; exact hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  have hsp := frustPairs_Q09_split (Finset.Subset.refl (nzPts 3)) hcl s3
  dsimp only at hsp
  have hSA : (nzPts 3).filter (fun p => quadForm c0_09 p = 0) = Qminus c0_09 := rfl
  rw [hSA] at hsp
  rw [hsp]; apply congr_arg (frustPairs (Qminus c0_09) s3 + ·); apply congr_arg (3 * ·)
  symm
  refine Finset.card_bij (fun uv _ => (dec3 (B36_pt uv.1), dec3 (B36_pt uv.2))) ?_ ?_ ?_
  · rintro ⟨u, v⟩ huv
    simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    have hne0 : M36_val r.val u.val v.val ≠ 0 := fun h => by rw [h] at huv; norm_num at huv
    have he := M36_edge_eq r hA27 u v hne0
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨B36_pt_mem_nz u, B36_pt_quadForm u⟩, ⟨B36_pt_mem_nz v, B36_pt_quadForm v⟩⟩,
      he.1, he.2.1, by rw [← he.2.2]; exact huv⟩
  · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h.1)))
      (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h.2)))
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true] at hpq
    rcases hpq with ⟨⟨⟨hp0, hpQ⟩, ⟨hq0, hqQ⟩⟩, hne, hsymp, hfr⟩
    have h0e : (enc3 0).val = 0 := by
      have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
      exact congr_arg Fin.val this
    have toQ1 : ∀ x : PauliIdx 3, quadForm c0_09 x = 1 → Q3_form 9 (enc3 x).val = 1 := fun x hx => by
      have h : quadForm c0_09 (dec3 (enc3 x)) = 1 := by rwa [dec3_enc3]
      rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 x).val
      generalize Q3_form 9 (enc3 x).val = m at hlt h ⊢; interval_cases m; exact absurd h (by decide); rfl
    obtain ⟨u, hu⟩ := B36_val_surj (enc3 p) (fun h => hp0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ1 p hpQ)
    obtain ⟨v, hv⟩ := B36_val_surj (enc3 q) (fun h => hq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ1 q hqQ)
    have hdu : dec3 (B36_pt u) = p := by rw [show B36_pt u = enc3 p from Fin.ext hu, dec3_enc3]
    have hdv : dec3 (B36_pt v) = q := by rw [show B36_pt v = enc3 q from Fin.ext hv, dec3_enc3]
    have huv_ne : u ≠ v := fun h => hne (by rw [← hdu, ← hdv, h])
    have huv_sp : symp3 (B36_val u.val) (B36_val v.val) = 0 := by
      have h := hsymp; rw [← hdu, ← hdv, symp_dec3] at h
      change ((symp3 (B36_val u.val) (B36_val v.val) : Nat) : ZMod 2) = 0 at h
      have hlt := symp3_lt2 (B36_val u.val) (B36_val v.val)
      generalize symp3 (B36_val u.val) (B36_val v.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
    have hne0 : M36_val r.val u.val v.val ≠ 0 := (M36_val_spec r u v).2.mpr ⟨huv_ne, huv_sp⟩
    have he := M36_edge_eq r hA27 u v hne0
    refine ⟨(u, v), ?_, Prod.ext hdu hdv⟩
    simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he.2.2, hdu, hdv]; exact hfr

/-! #### `lines27_list` Exact 6-to-1 Count Lemma (Covers BOTH `f₂₇` and `slCA`) -/

private lemma mem_lines27_iff (x : Nat × Nat × Nat × ℤ) :
    x ∈ lines27_list ↔
      x.1 < 27 ∧ x.2.1 < 27 ∧ x.2.2.1 < 27 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 ∧
      symp3 (A27_val x.1) (A27_val x.2.1) = 0 ∧
      A27_val x.2.2.1 = (A27_val x.1 ^^^ A27_val x.2.1) ∧
      x.2.2.2 = gamma3_sgn (A27_val x.1) (A27_val x.2.1) := by
  rcases x with ⟨a, b, c, g⟩
  simp only [lines27_list, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, hmem⟩
    by_cases hbad : (decide (j ≤ i) || symp3 (A27_val i) (A27_val j) != 0) = true
    · rw [if_pos hbad] at hmem; simp at hmem
    · rw [if_neg hbad] at hmem
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_not] at hbad
      cases hidx : A27_list.idxOf? (A27_val i ^^^ A27_val j) with
      | none => rw [hidx] at hmem; simp at hmem
      | some k =>
        rw [hidx] at hmem; dsimp only at hmem
        split_ifs at hmem with hkj
        · simp at hmem
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
          have hclt : c < 27 := by
            have := (List.idxOf?_eq_some_iff.mp hidx).1
            rwa [A27_list_len] at this
          have hceq : A27_val c = A27_val a ^^^ A27_val b := by
            have := (List.idxOf?_eq_some_iff.mp hidx).2.1
            rw [A27_val, dpll_getD_eq_getElem _ _ (by rw [A27_list_len]; exact hclt), this]
          exact ⟨hi, hj, hclt, by omega, by omega, hbad.2, hceq, rfl⟩
  · rintro ⟨ha, hb, hc, hab, hbc, hsp, hxor, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have h1 : (decide (b ≤ a) || symp3 (A27_val a) (A27_val b) != 0) = false := by
      simp [hsp, show ¬(b ≤ a) by omega]
    have hidx : A27_list.idxOf? (A27_val a ^^^ A27_val b) = some c := by
      rw [← hxor]; exact A27_idxOf_val ⟨c, hc⟩
    simp [h1, hidx, show ¬(c ≤ b) by omega]

private lemma lines27_nodup : lines27_list.Nodup := by
  unfold lines27_list
  refine List.nodup_flatMap.mpr ⟨fun i _ => ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun j _ => ?_, ?_⟩
    · split_ifs
      · exact List.nodup_nil
      · cases A27_list.idxOf? (A27_val i ^^^ A27_val j) with
        | none => exact List.nodup_nil
        | some k => dsimp only; split_ifs <;> simp
    · refine List.Pairwise.imp_of_mem (fun {j1 j2} _ _ hne => ?_) (List.nodup_range)
      intro x hx1 hx2
      dsimp only at hx1 hx2
      split_ifs at hx1; · simp at hx1
      split_ifs at hx2; · simp at hx2
      cases h1 : A27_list.idxOf? (A27_val i ^^^ A27_val j1) <;> rw [h1] at hx1 <;> dsimp only at hx1
      · simp at hx1
      · split_ifs at hx1; · simp at hx1
        simp only [List.mem_singleton] at hx1
        cases h2 : A27_list.idxOf? (A27_val i ^^^ A27_val j2) <;> rw [h2] at hx2 <;> dsimp only at hx2
        · simp at hx2
        · split_ifs at hx2; · simp at hx2
          simp only [List.mem_singleton] at hx2
          rw [hx1] at hx2; exact hne (congr_arg (fun t => t.2.1) hx2)
  · refine List.Pairwise.imp_of_mem (fun {i1 i2} _ _ hne => ?_) (List.nodup_range)
    intro x hx1 hx2
    simp only [List.mem_flatMap, List.mem_range] at hx1 hx2
    rcases hx1 with ⟨j1, _, hx1⟩; rcases hx2 with ⟨j2, _, hx2⟩
    split_ifs at hx1; · simp at hx1
    split_ifs at hx2; · simp at hx2
    cases h1 : A27_list.idxOf? (A27_val i1 ^^^ A27_val j1) <;> rw [h1] at hx1 <;> dsimp only at hx1
    · simp at hx1
    · split_ifs at hx1; · simp at hx1
      simp only [List.mem_singleton] at hx1
      cases h2 : A27_list.idxOf? (A27_val i2 ^^^ A27_val j2) <;> rw [h2] at hx2 <;> dsimp only at hx2
      · simp at hx2
      · split_ifs at hx2; · simp at hx2
        simp only [List.mem_singleton] at hx2
        rw [hx1] at hx2; exact hne (congr_arg Prod.fst hx2)

set_option maxHeartbeats 800000 in
lemma lines27_foldl_eq_frustPairs (r : Fin 3) (Q : Nat → Bool)
    (hQcl : ∀ p q : PauliIdx 3, p ∈ Qminus c0_09 → q ∈ Qminus c0_09 → p ≠ q → symp p q = 0 →
      Q (enc3 p).val = true → Q (enc3 q).val = true → Q (enc3 (p + q)).val = true)
    {s3 : PauliIdx 3 → ℤ} (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) :
    6 * lines27_list.foldl (fun acc (a, b, c, g) =>
      if Q (A27_val a) && Q (A27_val b) && Q (A27_val c) &&
         g * (rep27_vecs.getD r.val []).getD a 0 * (rep27_vecs.getD r.val []).getD b 0 *
         (rep27_vecs.getD r.val []).getD c 0 == -1
      then acc + 1 else acc) 0 =
    frustPairs ((Qminus c0_09).filter fun p => Q (enc3 p).val = true) s3 := by
  let pred : Nat × Nat × Nat × ℤ → Bool := fun (a, b, c, g) =>
    Q (A27_val a) && Q (A27_val b) && Q (A27_val c) &&
    (g * (rep27_vecs.getD r.val []).getD a 0 * (rep27_vecs.getD r.val []).getD b 0 *
     (rep27_vecs.getD r.val []).getD c 0 == -1)
  have hfold_len : ∀ l : List (Nat × Nat × Nat × ℤ),
      l.foldl (fun acc t => if pred t then acc + 1 else acc) 0 = (l.filter pred).length := by
    intro l
    have hgen : ∀ a, l.foldl (fun acc t => if pred t then acc + 1 else acc) a = a + (l.filter pred).length := by
      induction l with
      | nil => intro a; simp
      | cons x xs ih =>
        intro a; simp only [List.foldl_cons, List.filter_cons]
        cases hp : pred x <;> simp [ih] <;> omega
    simpa using hgen 0
  have hfold_eq : lines27_list.foldl (fun acc (a, b, c, g) =>
      if Q (A27_val a) && Q (A27_val b) && Q (A27_val c) &&
         g * (rep27_vecs.getD r.val []).getD a 0 * (rep27_vecs.getD r.val []).getD b 0 *
         (rep27_vecs.getD r.val []).getD c 0 == -1
      then acc + 1 else acc) 0 = (lines27_list.filter pred).length := hfold_len lines27_list
  rw [hfold_eq]
  let Lf : Finset (Nat × Nat × Nat × ℤ) := (lines27_list.filter pred).toFinset
  have hLf_card : Lf.card = (lines27_list.filter pred).length :=
    List.toFinset_card_of_nodup (lines27_nodup.filter pred)
  rw [← hLf_card]
  let ptOf : Nat → PauliIdx 3 := fun i => dec3 ⟨A27_val i % 64, Nat.mod_lt _ (by omega)⟩
  have hptOf : ∀ i : Fin 27, ptOf i.val = dec3 (A27_pt i) := fun i => by
    have hlt := (A27_val_props i).2.1
    simp only [ptOf, A27_pt, Nat.mod_eq_of_lt hlt]
  have hpt_inj : ∀ x < 27, ∀ y < 27, ptOf x = ptOf y → x = y := fun x hx y hy h => by
    rw [hptOf ⟨x, hx⟩, hptOf ⟨y, hy⟩] at h
    exact congr_arg Fin.val (A27_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))
  let sixOf : Nat × Nat × Nat × ℤ → Finset (PauliIdx 3 × PauliIdx 3) := fun (a, b, c, _) =>
    let pa := ptOf a; let pb := ptOf b; let pc := ptOf c
    {(pa, pb), (pb, pa), (pa, pc), (pc, pa), (pb, pc), (pc, pb)}
  let SA := (Qminus c0_09).filter fun p => Q (enc3 p).val = true
  let P := (SA ×ˢ SA).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s3 pq.1 * s3 pq.2 * s3 (pq.1 + pq.2) = -1
  have hbi : P = Lf.biUnion sixOf := by
    ext ⟨p, q⟩
    simp only [Finset.mem_biUnion, Lf, List.mem_toFinset, List.mem_filter]
    constructor
    · intro hpq
      simp only [P, SA, Finset.mem_filter, Finset.mem_product] at hpq
      rcases hpq with ⟨⟨⟨hpQ09, hQp⟩, ⟨hqQ09, hQq⟩⟩, hne, hsp, hfr⟩
      have h0e : (enc3 0).val = 0 := by
        have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        exact congr_arg Fin.val this
      have toQ0 : ∀ x : PauliIdx 3, x ∈ Qminus c0_09 → (enc3 x).val ≠ 0 ∧ Q3_form 9 (enc3 x).val = 0 := by
        intro x hx
        simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hx
        refine ⟨fun h => hx.1 (equiv3.injective (Fin.ext (h.trans h0e.symm))), ?_⟩
        have h : quadForm c0_09 (dec3 (enc3 x)) = 0 := by rw [dec3_enc3]; exact hx.2
        rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 x).val
        generalize Q3_form 9 (enc3 x).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
      have hpqQ09 : p + q ∈ Qminus c0_09 := by
        simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hpQ09 hqQ09 ⊢
        exact ⟨fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm),
          by rw [quadForm_add, hpQ09.2, hqQ09.2, hsp]; simp⟩
      have hQpq : Q (enc3 (p + q)).val = true := hQcl p q hpQ09 hqQ09 hne hsp hQp hQq
      obtain ⟨ia, hia⟩ := A27_val_surj (enc3 p) (toQ0 p hpQ09).1 (toQ0 p hpQ09).2
      obtain ⟨ib, hib⟩ := A27_val_surj (enc3 q) (toQ0 q hqQ09).1 (toQ0 q hqQ09).2
      obtain ⟨ic, hic⟩ := A27_val_surj (enc3 (p + q)) (toQ0 (p + q) hpqQ09).1 (toQ0 (p + q) hpqQ09).2
      have hda : ptOf ia.val = p := by rw [hptOf ia, show A27_pt ia = enc3 p from Fin.ext hia, dec3_enc3]
      have hdb : ptOf ib.val = q := by rw [hptOf ib, show A27_pt ib = enc3 q from Fin.ext hib, dec3_enc3]
      have hdc : ptOf ic.val = p + q := by rw [hptOf ic, show A27_pt ic = enc3 (p + q) from Fin.ext hic, dec3_enc3]
      have hne_ab : ia.val ≠ ib.val := fun h => hne (by rw [← hda, ← hdb, h])
      have hne_ac : ia.val ≠ ic.val := fun h => (toQ0 q hqQ09).1 (by
        have h1 : p = p + q := hda.symm.trans ((congr_arg ptOf h).trans hdc)
        have hq0 : q = 0 := by have := congr_arg (p + ·) h1; simpa [pauliIdx_add_self, pauliIdx_add_cancel_left] using this.symm
        rw [hq0, h0e])
      have hne_bc : ib.val ≠ ic.val := fun h => (toQ0 p hpQ09).1 (by
        have h1 : q = p + q := hdb.symm.trans ((congr_arg ptOf h).trans hdc)
        have hp0 : p = 0 := by have := congr_arg (· + q) h1; simpa [pauliIdx_add_self, add_assoc] using this.symm
        rw [hp0, h0e])
      have hmk : ∀ x y z : Fin 27, x.val < y.val → y.val < z.val →
          ({ptOf x.val, ptOf y.val, ptOf z.val} : Finset (PauliIdx 3)) = {p, q, p + q} →
          ∃ t, (t ∈ lines27_list ∧ pred t = true) ∧ (p, q) ∈ sixOf t := by
        intro x y z hxy hyz hset
        have hpx : ptOf x.val ∈ ({p, q, p + q} : Finset (PauliIdx 3)) := hset ▸ by simp
        have hpy : ptOf y.val ∈ ({p, q, p + q} : Finset (PauliIdx 3)) := hset ▸ by simp
        have hpz : ptOf z.val ∈ ({p, q, p + q} : Finset (PauliIdx 3)) := hset ▸ by simp
        have hne_xy : ptOf x.val ≠ ptOf y.val := fun h => Nat.ne_of_lt hxy (congr_arg Fin.val (A27_val_inj (by
          rw [hptOf x, hptOf y] at h; exact congr_arg Fin.val (equiv3.symm.injective h))))
        have hne_xz : ptOf x.val ≠ ptOf z.val := fun h => Nat.ne_of_lt (lt_trans hxy hyz) (congr_arg Fin.val (A27_val_inj (by
          rw [hptOf x, hptOf z] at h; exact congr_arg Fin.val (equiv3.symm.injective h))))
        have hne_yz : ptOf y.val ≠ ptOf z.val := fun h => Nat.ne_of_lt hyz (congr_arg Fin.val (A27_val_inj (by
          rw [hptOf y, hptOf z] at h; exact congr_arg Fin.val (equiv3.symm.injective h))))
        -- Every pair of distinct elements of `{p, q, p+q}` commutes, sums to the third, and has identical frustration!
        have h3 : ∀ u v w : PauliIdx 3,
            u ∈ ({p, q, p + q} : Finset _) → v ∈ ({p, q, p + q} : Finset _) → w ∈ ({p, q, p + q} : Finset _) →
            u ≠ v → u ≠ w → v ≠ w →
            symp u v = 0 ∧ u + v = w ∧ gammaSgn u v * s3 u * s3 v * s3 w = -1 := by
          intro u v w hu hv hw huv huw hvw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
          rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rcases hw with hw | hw | hw
          all_goals simp only [hu, hv, hw] at huv huw hvw ⊢
          all_goals try exact absurd rfl huv
          all_goals try exact absurd rfl huw
          all_goals try exact absurd rfl hvw
          · exact ⟨hsp, trivial, hfr⟩
          · refine ⟨by rw [symp_add_right, symp_self, hsp, add_zero], pauliIdx_add_cancel_left p q, ?_⟩
            rw [gammaSgn_add_right hsp]; linarith
          · refine ⟨by rw [symp_comm, hsp], add_comm q p, ?_⟩
            rw [gammaSgn_comm (by rwa [symp_comm])]; linarith
          · refine ⟨by rw [symp_add_right, symp_comm q p, hsp, symp_self, add_zero],
              by rw [add_comm p q, pauliIdx_add_cancel_left], ?_⟩
            have h1 : gammaSgn q (p + q) = gammaSgn q p := by
              rw [add_comm p q, gammaSgn_add_right (by rwa [symp_comm])]
            rw [h1, gammaSgn_comm (by rwa [symp_comm])]; linarith
          · refine ⟨by rw [symp_add_left, symp_self, symp_comm q p, hsp, add_zero],
              by rw [add_comm p q, add_assoc, pauliIdx_add_self, add_zero], ?_⟩
            rw [gammaSgn_comm (by rw [symp_add_left, symp_self, symp_comm q p, hsp, add_zero]),
                gammaSgn_add_right hsp]; linarith
          · refine ⟨by rw [symp_add_left, hsp, symp_self, add_zero],
              by rw [add_assoc, pauliIdx_add_self, add_zero], ?_⟩
            have h1 : gammaSgn (p + q) q = gammaSgn p q := by
              rw [gammaSgn_comm (by rw [symp_add_left, hsp, symp_self, add_zero]),
                  add_comm p q, gammaSgn_add_right (by rwa [symp_comm]),
                  gammaSgn_comm (by rwa [symp_comm])]
            rw [h1]; linarith
        obtain ⟨hsp_xy, hadd_xy, hfr_xy⟩ := h3 _ _ _ hpx hpy hpz hne_xy hne_xz hne_yz
        have hsp_nat : symp3 (A27_val x.val) (A27_val y.val) = 0 := by
          rw [hptOf x, hptOf y, symp_dec3] at hsp_xy
          change ((symp3 (A27_val x.val) (A27_val y.val) : Nat) : ZMod 2) = 0 at hsp_xy
          have hlt := symp3_lt2 (A27_val x.val) (A27_val y.val)
          generalize symp3 (A27_val x.val) (A27_val y.val) = m at hlt hsp_xy ⊢
          interval_cases m; rfl; exact absurd hsp_xy (by decide)
        have hxor_xyz : A27_val z.val = A27_val x.val ^^^ A27_val y.val := by
          rw [hptOf x, hptOf y, hptOf z, ← dec3_xor] at hadd_xy
          exact (congr_arg Fin.val (equiv3.symm.injective hadd_xy)).symm
        have hQof : ∀ u : Fin 27, ptOf u.val ∈ ({p, q, p + q} : Finset _) → Q (A27_val u.val) = true := by
          intro u hu
          have hvu : (enc3 (ptOf u.val)).val = A27_val u.val := by rw [hptOf u, enc3_dec3]; rfl
          rw [← hvu]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h <;> rw [h] <;> assumption
        have hgam : gamma3_sgn (A27_val x.val) (A27_val y.val) = gammaSgn (ptOf x.val) (ptOf y.val) := by
          rw [hptOf x, hptOf y, gammaSgn_dec3]; rfl
        refine ⟨(x.val, y.val, z.val, gamma3_sgn (A27_val x.val) (A27_val y.val)), ⟨?_, ?_⟩, ?_⟩
        · exact (mem_lines27_iff _).mpr ⟨x.isLt, y.isLt, z.isLt, hxy, hyz, hsp_nat, hxor_xyz, rfl⟩
        · simp only [pred, hQof x hpx, hQof y hpy, hQof z hpz, Bool.true_and, beq_iff_eq]
          rw [hgam]
          change gammaSgn (ptOf x.val) (ptOf y.val) * rep27_val r x.val * rep27_val r y.val * rep27_val r z.val = -1
          rw [← hA27 x, ← hA27 y, ← hA27 z, ← hptOf x, ← hptOf y, ← hptOf z]; exact hfr_xy
        · have hp_in : p ∈ ({ptOf x.val, ptOf y.val, ptOf z.val} : Finset _) := hset.symm ▸ by simp
          have hq_in : q ∈ ({ptOf x.val, ptOf y.val, ptOf z.val} : Finset _) := hset.symm ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp_in hq_in
          simp only [sixOf, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rcases hp_in with hp' | hp' | hp' <;> rcases hq_in with hq' | hq' | hq'
          all_goals simp only [hp', hq'] at hne ⊢
          all_goals try exact absurd rfl hne
          all_goals simp
      have hperm3 : ∀ u v w : PauliIdx 3,
          ({u, w, v} : Finset _) = {u, v, w} ∧ ({w, u, v} : Finset _) = {u, v, w} ∧
          ({v, u, w} : Finset _) = {u, v, w} ∧ ({v, w, u} : Finset _) = {u, v, w} ∧
          ({w, v, u} : Finset _) = {u, v, w} := fun u v w =>
        ⟨Finset.ext fun t => by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
         Finset.ext fun t => by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
         Finset.ext fun t => by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
         Finset.ext fun t => by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
         Finset.ext fun t => by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      rcases lt_or_gt_of_ne hne_ab with hab | hba
      · rcases lt_or_gt_of_ne hne_bc with hbc | hcb
        · exact hmk ia ib ic hab hbc (by rw [hda, hdb, hdc])
        · rcases lt_or_gt_of_ne hne_ac with hac | hca
          · exact hmk ia ic ib hac hcb (by rw [hda, hdb, hdc]; exact (hperm3 p q (p + q)).1)
          · exact hmk ic ia ib hca hab (by rw [hda, hdb, hdc]; exact (hperm3 p q (p + q)).2.1)
      · rcases lt_or_gt_of_ne hne_ac with hac | hca
        · exact hmk ib ia ic hba hac (by rw [hda, hdb, hdc]; exact (hperm3 p q (p + q)).2.2.1)
        · rcases lt_or_gt_of_ne hne_bc with hbc | hcb
          · exact hmk ib ic ia hbc hca (by rw [hda, hdb, hdc]; exact (hperm3 p q (p + q)).2.2.2.1)
          · exact hmk ic ib ia hcb hba (by rw [hda, hdb, hdc]; exact (hperm3 p q (p + q)).2.2.2.2)
    · rintro ⟨⟨a, b, c, g⟩, ⟨hmem, hpr⟩, hpq⟩
      rcases (mem_lines27_iff _).mp hmem with ⟨ha, hb, hc, hab, hbc, hsp, hxor, hg⟩
      dsimp only at ha hb hc hab hbc hsp hxor hg; subst hg
      simp only [pred, Bool.and_eq_true, beq_iff_eq] at hpr
      rcases hpr with ⟨⟨⟨hQa, hQb⟩, hQc⟩, hfr⟩
      let fa : Fin 27 := ⟨a, ha⟩; let fb : Fin 27 := ⟨b, hb⟩; let fc : Fin 27 := ⟨c, hc⟩
      have hpa : ptOf a = dec3 (A27_pt fa) := hptOf fa
      have hpb : ptOf b = dec3 (A27_pt fb) := hptOf fb
      have hpc : ptOf c = dec3 (A27_pt fc) := hptOf fc
      have hadd : ptOf a + ptOf b = ptOf c := by
        rw [hpa, hpb, hpc, ← dec3_xor]; congr 1; exact Fin.ext hxor.symm
      have hsp_ab : symp (ptOf a) (ptOf b) = 0 := by
        rw [hpa, hpb, symp_dec3]; change ((symp3 (A27_val a) (A27_val b) : Nat) : ZMod 2) = 0; rw [hsp]; rfl
      have hne_ab : ptOf a ≠ ptOf b := fun h => Nat.ne_of_lt hab (hpt_inj a ha b hb h)
      have hne_ac : ptOf a ≠ ptOf c := fun h => Nat.ne_of_lt (lt_trans hab hbc) (hpt_inj a ha c hc h)
      have hne_bc : ptOf b ≠ ptOf c := fun h => Nat.ne_of_lt hbc (hpt_inj b hb c hc h)
      have hfr_ab : gammaSgn (ptOf a) (ptOf b) * s3 (ptOf a) * s3 (ptOf b) * s3 (ptOf c) = -1 := by
        rw [hpa, hpb, hpc, gammaSgn_dec3, hA27 fa, hA27 fb, hA27 fc]; exact hfr
      have hma : ptOf a ∈ SA := by
        simp only [SA, Finset.mem_filter, hpa, A27_pt_mem_Qminus, enc3_dec3, true_and]; exact hQa
      have hmb : ptOf b ∈ SA := by
        simp only [SA, Finset.mem_filter, hpb, A27_pt_mem_Qminus, enc3_dec3, true_and]; exact hQb
      have hmc : ptOf c ∈ SA := by
        simp only [SA, Finset.mem_filter, hpc, A27_pt_mem_Qminus, enc3_dec3, true_and]; exact hQc
      simp only [sixOf, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpq
      simp only [P, Finset.mem_filter, Finset.mem_product]
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hma, hmb⟩, hne_ab, hsp_ab, by rw [hadd]; exact hfr_ab⟩
      · refine ⟨⟨hmb, hma⟩, Ne.symm hne_ab, by rwa [symp_comm], ?_⟩
        rw [add_comm, hadd, gammaSgn_comm (by rwa [symp_comm])]; linarith
      · refine ⟨⟨hma, hmc⟩, hne_ac, by rw [← hadd, symp_add_right, symp_self, hsp_ab, add_zero], ?_⟩
        rw [← hadd, pauliIdx_add_cancel_left, gammaSgn_add_right hsp_ab, hadd]; linarith
      · refine ⟨⟨hmc, hma⟩, Ne.symm hne_ac, by rw [← hadd, symp_add_left, symp_self, symp_comm, hsp_ab, add_zero], ?_⟩
        rw [← hadd, add_comm (ptOf a) (ptOf b), add_assoc, pauliIdx_add_self, add_zero,
            gammaSgn_comm (by rw [symp_add_left, symp_comm, hsp_ab, symp_self, add_zero]),
            add_comm (ptOf b) (ptOf a), gammaSgn_add_right hsp_ab, hadd]; linarith
      · refine ⟨⟨hmb, hmc⟩, hne_bc, by rw [← hadd, symp_add_right, symp_comm, hsp_ab, symp_self, add_zero], ?_⟩
        rw [← hadd, add_comm (ptOf a) (ptOf b), pauliIdx_add_cancel_left,
            gammaSgn_add_right (by rwa [symp_comm]), gammaSgn_comm (by rwa [symp_comm]),
            add_comm (ptOf b) (ptOf a), hadd]; linarith
      · refine ⟨⟨hmc, hmb⟩, Ne.symm hne_bc, by rw [← hadd, symp_add_left, hsp_ab, symp_self, add_zero], ?_⟩
        rw [← hadd, add_assoc, pauliIdx_add_self, add_zero,
            gammaSgn_comm (by rw [symp_add_left, hsp_ab, symp_self, add_zero]),
            add_comm (ptOf a) (ptOf b), gammaSgn_add_right (by rwa [symp_comm]),
            gammaSgn_comm (by rwa [symp_comm]), add_comm (ptOf b) (ptOf a), hadd]; linarith
  change 6 * Lf.card = P.card
  rw [hbi, Finset.card_biUnion]
  · have hcard6 : ∀ t ∈ Lf, (sixOf t).card = 6 := by
      rintro ⟨a, b, c, g⟩ ht
      simp only [Lf, List.mem_toFinset, List.mem_filter] at ht
      rcases (mem_lines27_iff _).mp ht.1 with ⟨ha, hb, hc, hab, hbc, _, _, _⟩
      dsimp only at ha hb hc hab hbc
      have hne_ab : ptOf a ≠ ptOf b := fun h => Nat.ne_of_lt hab (hpt_inj a ha b hb h)
      have hne_ac : ptOf a ≠ ptOf c := fun h => Nat.ne_of_lt (lt_trans hab hbc) (hpt_inj a ha c hc h)
      have hne_bc : ptOf b ≠ ptOf c := fun h => Nat.ne_of_lt hbc (hpt_inj b hb c hc h)
      dsimp only [sixOf]
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hne_ab, hne_ac, hne_bc, Ne.symm hne_ab, Ne.symm hne_ac, Ne.symm hne_bc]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hne_ab, hne_ac, hne_bc, Ne.symm hne_ab, Ne.symm hne_ac, Ne.symm hne_bc]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hne_ab, hne_ac, hne_bc, Ne.symm hne_ab, Ne.symm hne_ac, Ne.symm hne_bc]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hne_ab, hne_ac, hne_bc, Ne.symm hne_ab, Ne.symm hne_ac, Ne.symm hne_bc]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hne_ab, hne_ac, hne_bc, Ne.symm hne_ab, Ne.symm hne_ac, Ne.symm hne_bc]; tauto),
          Finset.card_singleton]
    rw [Finset.sum_congr rfl hcard6, Finset.sum_const, smul_eq_mul, mul_comm]
  · rintro ⟨a1, b1, c1, g1⟩ h1 ⟨a2, b2, c2, g2⟩ h2 hne
    simp only [Finset.mem_coe, Lf, List.mem_toFinset, List.mem_filter] at h1 h2
    rcases (mem_lines27_iff _).mp h1.1 with ⟨ha1, hb1, hc1, hab1, hbc1, _, hxor1, hg1⟩
    rcases (mem_lines27_iff _).mp h2.1 with ⟨ha2, hb2, hc2, hab2, hbc2, _, hxor2, hg2⟩
    dsimp only at ha1 hb1 hc1 hab1 hbc1 hxor1 hg1 ha2 hb2 hc2 hab2 hbc2 hxor2 hg2
    subst hg1; subst hg2
    refine Finset.disjoint_left.mpr fun pq hp1 hp2 => hne ?_
    have hadd1 : ptOf a1 + ptOf b1 = ptOf c1 := by
      rw [hptOf ⟨a1, ha1⟩, hptOf ⟨b1, hb1⟩, hptOf ⟨c1, hc1⟩, ← dec3_xor]; congr 1; exact Fin.ext hxor1.symm
    have hadd2 : ptOf a2 + ptOf b2 = ptOf c2 := by
      rw [hptOf ⟨a2, ha2⟩, hptOf ⟨b2, hb2⟩, hptOf ⟨c2, hc2⟩, ← dec3_xor]; congr 1; exact Fin.ext hxor2.symm
    have hset_of : ∀ (x y z : PauliIdx 3), x + y = z →
        pq ∈ ({(x, y), (y, x), (x, z), (z, x), (y, z), (z, y)} : Finset _) →
        ({pq.1, pq.2, pq.1 + pq.2} : Finset _) = {x, y, z} := by
      intro x y z hxy hmem
      have hxz : x + z = y := by rw [← hxy, pauliIdx_add_cancel_left]
      have hzx : z + x = y := by rw [add_comm, hxz]
      have hyz : y + z = x := by rw [← hxy, add_comm x y, pauliIdx_add_cancel_left]
      have hzy : z + y = x := by rw [add_comm, hyz]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · dsimp only; rw [hxy]
      · dsimp only; rw [add_comm, hxy, Finset.insert_comm]
      · dsimp only; rw [hxz]; exact congr_arg (insert x) (Finset.pair_comm z y)
      · dsimp only; rw [hzx, Finset.insert_comm]; exact congr_arg (insert x) (Finset.pair_comm z y)
      · dsimp only; rw [hyz, show ({z, x} : Finset _) = {x, z} from Finset.pair_comm z x, Finset.insert_comm]
      · dsimp only; rw [hzy, Finset.insert_comm z y {x}, show ({z, x} : Finset _) = {x, z} from Finset.pair_comm z x, Finset.insert_comm]
    have hset1 : ({pq.1, pq.2, pq.1 + pq.2} : Finset _) = {ptOf a1, ptOf b1, ptOf c1} := hset_of _ _ _ hadd1 hp1
    have hset2 : ({pq.1, pq.2, pq.1 + pq.2} : Finset _) = {ptOf a2, ptOf b2, ptOf c2} := hset_of _ _ _ hadd2 hp2
    have hsets : ({a1, b1, c1} : Finset Nat) = {a2, b2, c2} := by
      have hpeq : ({ptOf a1, ptOf b1, ptOf c1} : Finset _) = {ptOf a2, ptOf b2, ptOf c2} := hset1.symm.trans hset2
      have hinj : ∀ x < 27, ∀ y < 27, ptOf x = ptOf y → x = y := fun x hx y hy h => by
        rw [hptOf ⟨x, hx⟩, hptOf ⟨y, hy⟩] at h
        exact congr_arg Fin.val (A27_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))
      have mem_iff : ∀ u < 27, ptOf u ∈ ({ptOf a1, ptOf b1, ptOf c1} : Finset _) ↔ u ∈ ({a1, b1, c1} : Finset Nat) := by
        intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => by rcases h with h | h | h; exact Or.inl (hinj u hu a1 ha1 h); exact Or.inr (Or.inl (hinj u hu b1 hb1 h)); exact Or.inr (Or.inr (hinj u hu c1 hc1 h)),
               fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
      have mem_iff2 : ∀ u < 27, ptOf u ∈ ({ptOf a2, ptOf b2, ptOf c2} : Finset _) ↔ u ∈ ({a2, b2, c2} : Finset Nat) := by
        intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => by rcases h with h | h | h; exact Or.inl (hinj u hu a2 ha2 h); exact Or.inr (Or.inl (hinj u hu b2 hb2 h)); exact Or.inr (Or.inr (hinj u hu c2 hc2 h)),
               fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
      ext u
      by_cases hu : u < 27
      · rw [← mem_iff u hu, hpeq, mem_iff2 u hu]
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have ha_eq : a1 = a2 := by
      have h1m : a1 ∈ ({a2, b2, c2} : Finset Nat) := hsets ▸ by simp
      have h2m : a2 ∈ ({a1, b1, c1} : Finset Nat) := hsets.symm ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1m h2m; omega
    have hc_eq : c1 = c2 := by
      have h1m : c1 ∈ ({a2, b2, c2} : Finset Nat) := hsets ▸ by simp
      have h2m : c2 ∈ ({a1, b1, c1} : Finset Nat) := hsets.symm ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1m h2m; omega
    have hb_eq : b1 = b2 := by
      have h1m : b1 ∈ ({a2, b2, c2} : Finset Nat) := hsets ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1m; omega
    subst ha_eq; subst hb_eq; subst hc_eq; rfl

lemma frustPairs_Qminus09_eq_rep27 (r : Fin 3) {s3 : PauliIdx 3 → ℤ}
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) :
    frustPairs (Qminus c0_09) s3 = 6 * (if r.val = 0 then 9 else if r.val = 1 then 12 else 13) := by
  have h := lines27_foldl_eq_frustPairs r (fun _ => true) (fun _ _ _ _ _ _ _ _ => rfl) hA27
  simp only [Finset.filter_true, Bool.true_and, beq_iff_eq] at h
  rw [← h]
  have hchk := checkRep27Extra_ok
  unfold checkRep27Extra at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  rcases r with ⟨v, hv⟩
  interval_cases v
  · dsimp only; rw [hchk.2]; rfl
  · dsimp only; rw [hchk.1.1.2]; rfl
  · dsimp only; rw [hchk.1.2]; rfl

/-- Ordered frustrated edges in `B₃₆` restricted to slice `Qminus (otherC27_pt k)`. -/
def F36_slice (oid : Nat) (k : Fin 27) (s3 : PauliIdx 3 → ℤ) : Finset (Fin 36 × Fin 36) :=
  (F36_set oid s3).filter fun uv =>
    Q3_form (otherC27_list.getD k.val 0) (B36_val uv.1.val) = 0 ∧
    Q3_form (otherC27_list.getD k.val 0) (B36_val uv.2.val) = 0

lemma F36_slice_even (oid : Nat) (k : Fin 27) (s3 : PauliIdx 3 → ℤ) :
    2 ∣ (F36_slice oid k s3).card := by
  refine card_even_of_symm_irrefl _ ?_ ?_
  · intro a b hab
    simp only [F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    exact ⟨by rw [M36_val_symm oid b a]; linarith [hab.1], hab.2.2, hab.2.1⟩
  · intro a ha
    simp only [F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and, M36_val,
      beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at ha
    omega

lemma frustPairs_Qminus_ck_split (r : Fin 3) (f27 : Nat) (k : Fin 27) {s3 : PauliIdx 3 → ℤ}
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) :
    frustPairs (Qminus (dec3 (otherC27_pt k))) s3 =
      6 * ((mkOrb36Tables r.val f27).slCA.getD k.val 0) + 3 * (F36_slice r.val k s3).card := by
  let ck := dec3 (otherC27_pt k)
  let ckN := otherC27_list.getD k.val 0
  have hsub : Qminus ck ⊆ nzPts 3 := Finset.filter_subset _ _
  have hcl : ∀ p ∈ Qminus ck, ∀ q ∈ Qminus ck, p ≠ q → symp p q = 0 → p + q ∈ Qminus ck := by
    intro p hp q hq hne hsp
    simp only [Qminus, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq ⊢
    exact ⟨fun h => hne (by have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm),
      by rw [quadForm_add, hp.2, hq.2, hsp]; simp⟩
  have hsp := frustPairs_Q09_split hsub hcl s3
  dsimp only at hsp
  rw [hsp]
  congr 1
  · have hQcl : ∀ p q : PauliIdx 3, p ∈ Qminus c0_09 → q ∈ Qminus c0_09 → p ≠ q → symp p q = 0 →
        (Q3_form ckN (enc3 p).val == 0) = true → (Q3_form ckN (enc3 q).val == 0) = true →
        (Q3_form ckN (enc3 (p + q)).val == 0) = true := by
      intro p q _ _ _ hsymp hp hq
      simp only [beq_iff_eq] at hp hq ⊢
      have hp' : quadForm ck p = 0 := by
        rw [← dec3_enc3 p]; simp only [ck, quadForm_dec3, otherC27_pt]; change ((Q3_form ckN (enc3 p).val : Nat) : ZMod 2) = 0; rw [hp]; rfl
      have hq' : quadForm ck q = 0 := by
        rw [← dec3_enc3 q]; simp only [ck, quadForm_dec3, otherC27_pt]; change ((Q3_form ckN (enc3 q).val : Nat) : ZMod 2) = 0; rw [hq]; rfl
      have hpq' : quadForm ck (p + q) = 0 := by rw [quadForm_add, hp', hq', hsymp]; simp
      rw [← dec3_enc3 (p + q)] at hpq'; simp only [ck, quadForm_dec3, otherC27_pt] at hpq'
      have hlt := Q3_form_lt2 ckN (enc3 (p + q)).val
      generalize Q3_form ckN (enc3 (p + q)).val = m at hlt hpq' ⊢
      interval_cases m; rfl; exact absurd hpq' (by decide)
    have hlines := lines27_foldl_eq_frustPairs r (fun x => Q3_form ckN x == 0) hQcl hA27
    have hslCA_eq : (mkOrb36Tables r.val f27).slCA.getD k.val 0 =
        lines27_list.foldl (fun acc (a, b, c, g) =>
          if (Q3_form ckN (A27_val a) == 0) && (Q3_form ckN (A27_val b) == 0) &&
             (Q3_form ckN (A27_val c) == 0) &&
             (g * (rep27_vecs.getD r.val []).getD a 0 * (rep27_vecs.getD r.val []).getD b 0 *
              (rep27_vecs.getD r.val []).getD c 0 == -1)
          then acc + 1 else acc) 0 := by
      have hklt : k.val < otherC27_list.length := by rw [coreTables_spec.1]; exact k.isLt
      simp only [mkOrb36Tables]
      rw [dpll_getD_map otherC27_list _ 0 hklt]
      have hck : otherC27_list[k.val] = ckN := (dpll_getD_eq_getElem otherC27_list 0 hklt).symm
      rw [hck]
    rw [hslCA_eq, hlines]
    congr 1
    ext p
    simp only [Qminus, Finset.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨⟨hp, hqck⟩, hq09⟩
      refine ⟨⟨hp, hq09⟩, ?_⟩
      rw [← dec3_enc3 p] at hqck; simp only [ck, quadForm_dec3, otherC27_pt] at hqck
      have hlt := Q3_form_lt2 ckN (enc3 p).val
      generalize Q3_form ckN (enc3 p).val = m at hlt hqck ⊢; interval_cases m; rfl; exact absurd hqck (by decide)
    · rintro ⟨⟨hp, hq09⟩, hqck⟩
      refine ⟨⟨hp, ?_⟩, hq09⟩
      rw [← dec3_enc3 p]; simp only [ck, quadForm_dec3, otherC27_pt]; change ((Q3_form ckN (enc3 p).val : Nat) : ZMod 2) = 0; rw [hqck]; rfl
  · congr 1
    symm
    refine Finset.card_bij (fun uv _ => (dec3 (B36_pt uv.1), dec3 (B36_pt uv.2))) ?_ ?_ ?_
    · rintro ⟨u, v⟩ huv
      simp only [F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      have hne0 : M36_val r.val u.val v.val ≠ 0 := fun h => by have h1 := huv.1; rw [h] at h1; norm_num at h1
      have he := M36_edge_eq r hA27 u v hne0
      simp only [Finset.mem_filter, Finset.mem_product, Qminus]
      refine ⟨⟨⟨⟨B36_pt_mem_nz u, by simp only [ck, quadForm_dec3, otherC27_pt, B36_pt, huv.2.1]; rfl⟩,
          B36_pt_quadForm u⟩,
        ⟨⟨B36_pt_mem_nz v, by simp only [ck, quadForm_dec3, otherC27_pt, B36_pt, huv.2.2]; rfl⟩,
          B36_pt_quadForm v⟩⟩,
        he.1, he.2.1, by rw [← he.2.2]; exact huv.1⟩
    · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h.1)))
        (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h.2)))
    · rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_filter, Finset.mem_product, Qminus, nzPts, Finset.mem_erase,
        Finset.mem_univ, and_true] at hpq
      rcases hpq with ⟨⟨⟨⟨hp0, hpck⟩, hpQ⟩, ⟨⟨hq0, hqck⟩, hqQ⟩⟩, hne, hsymp, hfr⟩
      have h0e : (enc3 0).val = 0 := by
        have : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
        exact congr_arg Fin.val this
      have toQ1 : ∀ x : PauliIdx 3, quadForm c0_09 x = 1 → Q3_form 9 (enc3 x).val = 1 := fun x hx => by
        have h : quadForm c0_09 (dec3 (enc3 x)) = 1 := by rwa [dec3_enc3]
        rw [c0_09, quadForm_dec3] at h; have hlt := Q3_form_lt2 9 (enc3 x).val
        generalize Q3_form 9 (enc3 x).val = m at hlt h ⊢; interval_cases m; exact absurd h (by decide); rfl
      have toQck : ∀ x : PauliIdx 3, quadForm ck x = 0 → Q3_form ckN (enc3 x).val = 0 := fun x hx => by
        have h : quadForm ck (dec3 (enc3 x)) = 0 := by rwa [dec3_enc3]
        simp only [ck, quadForm_dec3, otherC27_pt] at h
        have hlt := Q3_form_lt2 ckN (enc3 x).val
        generalize Q3_form ckN (enc3 x).val = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
      obtain ⟨u, hu⟩ := B36_val_surj (enc3 p) (fun h => hp0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ1 p hpQ)
      obtain ⟨v, hv⟩ := B36_val_surj (enc3 q) (fun h => hq0 (equiv3.injective (Fin.ext (h.trans h0e.symm)))) (toQ1 q hqQ)
      have hdu : dec3 (B36_pt u) = p := by rw [show B36_pt u = enc3 p from Fin.ext hu, dec3_enc3]
      have hdv : dec3 (B36_pt v) = q := by rw [show B36_pt v = enc3 q from Fin.ext hv, dec3_enc3]
      have huv_ne : u ≠ v := fun h => hne (by rw [← hdu, ← hdv, h])
      have huv_sp : symp3 (B36_val u.val) (B36_val v.val) = 0 := by
        have h := hsymp; rw [← hdu, ← hdv, symp_dec3] at h
        change ((symp3 (B36_val u.val) (B36_val v.val) : Nat) : ZMod 2) = 0 at h
        have hlt := symp3_lt2 (B36_val u.val) (B36_val v.val)
        generalize symp3 (B36_val u.val) (B36_val v.val) = m at hlt h ⊢; interval_cases m; rfl; exact absurd h (by decide)
      have hne0 : M36_val r.val u.val v.val ≠ 0 := (M36_val_spec r u v).2.mpr ⟨huv_ne, huv_sp⟩
      have he := M36_edge_eq r hA27 u v hne0
      refine ⟨(u, v), ?_, Prod.ext hdu hdv⟩
      simp only [F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [he.2.2, hdu, hdv]; exact hfr,
        by rw [hu]; exact toQck p hpck, by rw [hv]; exact toQck q hqck⟩

/-! ### Section 3: `Orb36Tables` Specs & Carry-Free 144-Bit SIMD Invariants -/

lemma tbl_pAdj_testBit (oid f27 : Nat) (u v : Fin 36) :
    ((mkOrb36Tables oid f27).pAdj.getD u.val 0).testBit v.val = true ↔
      M36_val oid u.val v.val = 1 := by
  simp only [mkOrb36Tables]
  rw [dpll_getD_map_range 36 _ 0 u.isLt, foldl_or_bit_testBit]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨w, _, hw, rfl⟩; exact hw
  · intro h; exact ⟨v.val, v.isLt, h, rfl⟩

lemma tbl_nAdj_testBit (oid f27 : Nat) (u v : Fin 36) :
    ((mkOrb36Tables oid f27).nAdj.getD u.val 0).testBit v.val = true ↔
      M36_val oid u.val v.val = -1 := by
  simp only [mkOrb36Tables]
  rw [dpll_getD_map_range 36 _ 0 u.isLt, foldl_or_bit_testBit]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨w, _, hw, rfl⟩; exact hw
  · intro h; exact ⟨v.val, v.isLt, h, rfl⟩

lemma edgeSgnMask_eq_M36 (r : Fin 3) (f27 : Nat) (a b : Fin 36) :
    edgeSgnMask (mkOrb36Tables r.val f27).pAdj (mkOrb36Tables r.val f27).nAdj a.val b.val =
      M36_val r.val a.val b.val := by
  unfold edgeSgnMask
  simp only [show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
    show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
    show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
    beq_iff_eq, shr_and1_eq_one_iff, tbl_pAdj_testBit, tbl_nAdj_testBit]
  rcases (M36_val_spec r a b).1 with h | h | h <;> simp [h]

lemma tbl_pInc_eq (oid f27 : Nat) (u : Fin 36) :
    (mkOrb36Tables oid f27).pInc.getD u.val 0 =
      ∑ v : Fin 36, (if M36_val oid u.val v.val = 1 then 1 else 0) * 16 ^ v.val := by
  simp only [mkOrb36Tables]
  rw [dpll_getD_map_range 36 _ 0 u.isLt]
  have hrw : (fun acc v => if M36_val oid u.val v == 1 then acc + (1 <<< (4 * v)) else acc) =
      (fun acc v => acc + (if M36_val oid u.val v = 1 then 1 else 0) * 16 ^ v) := by
    funext acc v
    have hpow : 1 <<< (4 * v) = 16 ^ v := by
      rw [Nat.shiftLeft_eq, one_mul, pow_mul]; norm_num
    by_cases h : M36_val oid u.val v = 1
    · simp [h, hpow]
    · simp [h]
  rw [hrw, dpll_foldl_sum_range, zero_add]

lemma tbl_nInc_eq (oid f27 : Nat) (u : Fin 36) :
    (mkOrb36Tables oid f27).nInc.getD u.val 0 =
      ∑ v : Fin 36, (if M36_val oid u.val v.val = -1 then 1 else 0) * 16 ^ v.val := by
  simp only [mkOrb36Tables]
  rw [dpll_getD_map_range 36 _ 0 u.isLt]
  have hrw : (fun acc v => if M36_val oid u.val v == -1 then acc + (1 <<< (4 * v)) else acc) =
      (fun acc v => acc + (if M36_val oid u.val v = -1 then 1 else 0) * 16 ^ v) := by
    funext acc v
    have hpow : 1 <<< (4 * v) = 16 ^ v := by
      rw [Nat.shiftLeft_eq, one_mul, pow_mul]; norm_num
    by_cases h : M36_val oid u.val v = -1
    · simp [h, hpow]
    · simp [h]
  rw [hrw, dpll_foldl_sum_range, zero_add]

lemma tbl_slVerts_spec (oid f27 : Nat) (k : Fin 27) :
    let vs := (mkOrb36Tables oid f27).slVerts.getD k.val []
    vs.Nodup ∧ ∀ v : Nat, v ∈ vs ↔ v < 36 ∧ Q3_form (otherC27_list.getD k.val 0) (B36_val v) = 0 := by
  have hklt : k.val < otherC27_list.length := by rw [coreTables_spec.1]; exact k.isLt
  have hvs : (mkOrb36Tables oid f27).slVerts.getD k.val [] =
      (List.range 36).filter fun i => Q3_form (otherC27_list.getD k.val 0) (B36_val i) == 0 := by
    simp only [mkOrb36Tables]
    rw [dpll_getD_map otherC27_list _ [] hklt, dpll_getD_eq_getElem otherC27_list 0 hklt]
  rw [hvs]
  refine ⟨List.nodup_range.filter _, fun v => ?_⟩
  simp [List.mem_filter, List.mem_range, beq_iff_eq]

lemma tbl_slMask_testBit (oid f27 : Nat) (k : Fin 27) (v : Fin 36) :
    ((mkOrb36Tables oid f27).slMask.getD k.val 0).testBit v.val = true ↔
      Q3_form (otherC27_list.getD k.val 0) (B36_val v.val) = 0 := by
  have hklt : k.val < otherC27_list.length := by rw [coreTables_spec.1]; exact k.isLt
  have hsm : (mkOrb36Tables oid f27).slMask.getD k.val 0 =
      ((mkOrb36Tables oid f27).slVerts.getD k.val []).foldl (fun m u => m ||| (1 <<< u)) 0 := by
    simp only [mkOrb36Tables]
    rw [dpll_getD_map _ _ 0 (by simp [hklt]), dpll_getD_map otherC27_list _ [] hklt, List.getElem_map]
  rw [hsm, foldl_or_val_testBit]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq]
  have hv := (tbl_slVerts_spec oid f27 k).2
  constructor
  · rintro ⟨w, hw, hvw⟩
    have h2 := (hv w).mp hw |>.2
    first | (rw [← hvw]; exact h2) | (rw [hvw]; exact h2)
  · intro h; exact ⟨v.val, (hv v.val).mpr ⟨v.isLt, h⟩, rfl⟩

/-- Exact carry-free nibble extraction from a 36-lane 4-bit SIMD integer (`∀ u, c u < 16`). -/
lemma nibble_extract (c : Fin 36 → Nat) (hlt : ∀ u : Fin 36, c u < 16) (k : Fin 36) :
    (((∑ u : Fin 36, c u * 16 ^ u.val) >>> (4 * k.val)) &&& 15) = c k := by
  have hlow_lt : ∀ m ≤ 36, ∑ i ∈ Finset.range m, (if h : i < 36 then c ⟨i, h⟩ else 0) * 16 ^ i < 16 ^ m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 : (if h : m < 36 then c ⟨m, h⟩ else 0) ≤ 15 := by
        split_ifs with h'
        · have := hlt ⟨m, h'⟩; omega
        · omega
      have h3 : (if h : m < 36 then c ⟨m, h⟩ else 0) * 16 ^ m ≤ 15 * 16 ^ m :=
        Nat.mul_le_mul_right _ h2
      have hpow : 16 ^ (m + 1) = 16 ^ m + 15 * 16 ^ m := by rw [pow_succ]; omega
      omega
  have hsum_range : ∑ u : Fin 36, c u * 16 ^ u.val =
      ∑ i ∈ Finset.range 36, (if h : i < 36 then c ⟨i, h⟩ else 0) * 16 ^ i := by
    have h1 : ∑ u : Fin 36, c u * 16 ^ u.val =
        ∑ u : Fin 36, (if h : u.val < 36 then c ⟨u.val, h⟩ else 0) * 16 ^ u.val :=
      Finset.sum_congr rfl fun u _ => by simp [u.isLt]
    rw [h1, Fin.sum_univ_eq_sum_range (fun i => (if h : i < 36 then c ⟨i, h⟩ else 0) * 16 ^ i) 36]
  let f : Nat → Nat := fun i => (if h : i < 36 then c ⟨i, h⟩ else 0) * 16 ^ i
  have hsplit1 : ∑ i ∈ Finset.range 36, f i =
      (∑ i ∈ Finset.range (k.val + 1), f i) + ∑ i ∈ Finset.range (36 - (k.val + 1)), f ((k.val + 1) + i) := by
    have h36 : (36 : Nat) = (k.val + 1) + (36 - (k.val + 1)) := by have := k.isLt; omega
    conv_lhs => rw [h36]
    exact Finset.sum_range_add f (k.val + 1) (36 - (k.val + 1))
  have hhi_dvd : 16 ^ (k.val + 1) ∣ ∑ i ∈ Finset.range (36 - (k.val + 1)), f ((k.val + 1) + i) := by
    refine Finset.dvd_sum fun i _ => ?_
    dsimp only [f]
    rw [pow_add]
    exact ⟨(if h : k.val + 1 + i < 36 then c ⟨k.val + 1 + i, h⟩ else 0) * 16 ^ i, by ring⟩
  obtain ⟨Q, hQ⟩ := hhi_dvd
  have htot : ∑ u : Fin 36, c u * 16 ^ u.val =
      (∑ i ∈ Finset.range k.val, f i) + 16 ^ k.val * (c k + 16 * Q) := by
    rw [hsum_range, hsplit1, Finset.sum_range_succ, hQ]
    have hfk : f k.val = c k * 16 ^ k.val := by simp [f, k.isLt]
    rw [hfk, pow_succ]
    ring
  have hLlt : ∑ i ∈ Finset.range k.val, f i < 16 ^ k.val := hlow_lt k.val (Nat.le_of_lt k.isLt)
  have hpow4 : 2 ^ (4 * k.val) = 16 ^ k.val := by rw [pow_mul]; norm_num
  have hand15 : ∀ x : Nat, (x &&& 15) = x % 16 := fun x => by
    have := Nat.and_two_pow_sub_one_eq_mod x 4
    simpa using this
  rw [htot, Nat.shiftRight_eq_div_pow, hpow4, hand15]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hLlt, zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlt k)]

/-- Exact assigned-neighbor frustration count if vertex `v` takes sign `+1` (`cP`) or `-1` (`cN`). -/
def cP_of (oid am nm : Nat) (v : Fin 36) : Nat :=
  ((Finset.univ : Finset (Fin 36)).filter fun u =>
    am.testBit u.val = true ∧
    M36_val oid u.val v.val * (if nm.testBit u.val = true then -1 else 1) = -1).card

def cN_of (oid am nm : Nat) (v : Fin 36) : Nat :=
  ((Finset.univ : Finset (Fin 36)).filter fun u =>
    am.testBit u.val = true ∧
    M36_val oid u.val v.val * (if nm.testBit u.val = true then -1 else 1) * (-1) = -1).card

lemma cP_le_15 (r : Fin 3) (f27 : Nat)
    (hdeg : ∀ u < 36, pop36 ((mkOrb36Tables r.val f27).pAdj.getD u 0 ||| (mkOrb36Tables r.val f27).nAdj.getD u 0) = 15)
    (am nm : Nat) (v : Fin 36) : cP_of r.val am nm v ≤ 15 := by
  have h15 : ((Finset.univ : Finset (Fin 36)).filter fun u => M36_val r.val v.val u.val ≠ 0).card = 15 := by
    rw [← hdeg v.val v.isLt]
    symm
    refine pop36_eq_card_of_iff _ _ fun u => ?_
    rw [Nat.testBit_or, Bool.or_eq_true, tbl_pAdj_testBit, tbl_nAdj_testBit]
    rcases (M36_val_spec r v u).1 with h | h | h <;> simp [h]
  rw [← h15]
  refine Finset.card_le_card fun u hu => ?_
  simp only [cP_of, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  intro h0; rw [M36_val_symm r.val u v, h0, zero_mul] at hu; omega

lemma cN_le_15 (r : Fin 3) (f27 : Nat)
    (hdeg : ∀ u < 36, pop36 ((mkOrb36Tables r.val f27).pAdj.getD u 0 ||| (mkOrb36Tables r.val f27).nAdj.getD u 0) = 15)
    (am nm : Nat) (v : Fin 36) : cN_of r.val am nm v ≤ 15 := by
  have h15 : ((Finset.univ : Finset (Fin 36)).filter fun u => M36_val r.val v.val u.val ≠ 0).card = 15 := by
    rw [← hdeg v.val v.isLt]
    symm
    refine pop36_eq_card_of_iff _ _ fun u => ?_
    rw [Nat.testBit_or, Bool.or_eq_true, tbl_pAdj_testBit, tbl_nAdj_testBit]
    rcases (M36_val_spec r v u).1 with h | h | h <;> simp [h]
  rw [← h15]
  refine Finset.card_le_card fun u hu => ?_
  simp only [cN_of, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  intro h0; rw [M36_val_symm r.val u v, h0, zero_mul, zero_mul] at hu; omega

lemma simdStarLB_spec (oid am nm cpVec cnVec : Nat)
    (hcp_lt : ∀ v : Fin 36, cP_of oid am nm v < 16)
    (hcn_lt : ∀ v : Fin 36, cN_of oid am nm v < 16)
    (hcp : cpVec = ∑ v : Fin 36, cP_of oid am nm v * 16 ^ v.val)
    (hcn : cnVec = ∑ v : Fin 36, cN_of oid am nm v * 16 ^ v.val) :
    simdStarLB 36 am cpVec cnVec 0 =
      ∑ v : Fin 36, if am.testBit v.val = false then min (cP_of oid am nm v) (cN_of oid am nm v) else 0 := by
  have hgen : ∀ n j acc, n + j = 36 →
      simdStarLB n (am >>> j) (cpVec >>> (4 * j)) (cnVec >>> (4 * j)) acc =
        acc + ∑ v ∈ Finset.univ.filter (fun v : Fin 36 => j ≤ v.val),
          if am.testBit v.val = false then min (cP_of oid am nm v) (cN_of oid am nm v) else 0 := by
    intro n
    induction n with
    | zero =>
      intro j acc hj
      have hemp : Finset.univ.filter (fun v : Fin 36 => j ≤ v.val) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro v _; have := v.isLt; omega
      simp [simdStarLB, hemp]
    | succ n ih =>
      intro j acc hj
      have hj36 : j < 36 := by omega
      let jF : Fin 36 := ⟨j, hj36⟩
      unfold simdStarLB
      simp only [show ∀ x y, Nat.shiftRight (x >>> y) 1 = x >>> (y + 1) from fun x y => by
          change (x >>> y) >>> 1 = x >>> (y + 1); rw [← Nat.shiftRight_add],
        show ∀ x y, Nat.shiftRight (x >>> (4 * y)) 4 = x >>> (4 * (y + 1)) from fun x y => by
          change (x >>> (4 * y)) >>> 4 = x >>> (4 * (y + 1)); rw [← Nat.shiftRight_add, show 4 * (y + 1) = 4 * y + 4 by omega]]
      rw [ih (j + 1) _ (by omega)]
      have hflt : Finset.univ.filter (fun v : Fin 36 => j ≤ v.val) =
          insert jF (Finset.univ.filter (fun v : Fin 36 => j + 1 ≤ v.val)) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        constructor
        · intro h
          by_cases hvj : v.val = j
          · left; exact Fin.ext hvj
          · right; omega
        · rintro (rfl | h)
          · exact le_rfl
          · omega
      have hnotmem : jF ∉ Finset.univ.filter (fun v : Fin 36 => j + 1 ≤ v.val) := by simp [jF]
      rw [hflt, Finset.sum_insert hnotmem]
      have hbit : Nat.beq (Nat.land (am >>> j) 1) 0 = !am.testBit j := by
        change (((am >>> j) &&& 1) == 0) = !am.testBit j
        rw [testBit_eq_shr_and1]; cases am.testBit j <;> rfl
      have hcp_j : Nat.land (cpVec >>> (4 * j)) 15 = cP_of oid am nm jF := by
        rw [hcp]; exact nibble_extract (cP_of oid am nm) hcp_lt jF
      have hcn_j : Nat.land (cnVec >>> (4 * j)) 15 = cN_of oid am nm jF := by
        rw [hcn]; exact nibble_extract (cN_of oid am nm) hcn_lt jF
      have hmin_eq : (if Nat.ble (cP_of oid am nm jF) (cN_of oid am nm jF) then cP_of oid am nm jF
          else cN_of oid am nm jF) = min (cP_of oid am nm jF) (cN_of oid am nm jF) := by
        by_cases hle : cP_of oid am nm jF ≤ cN_of oid am nm jF
        · have hb : Nat.ble (cP_of oid am nm jF) (cN_of oid am nm jF) = true := by simpa using hle
          rw [if_pos hb, min_eq_left hle]
        · have hb : Nat.ble (cP_of oid am nm jF) (cN_of oid am nm jF) = false := by
            cases h' : Nat.ble (cP_of oid am nm jF) (cN_of oid am nm jF)
            · rfl
            · exact absurd (Nat.le_of_ble_eq_true h') hle
          rw [if_neg (by rw [hb]; decide), min_eq_right (by omega)]
      change (acc + if Nat.beq (Nat.land (am >>> j) 1) 0 then
          (if Nat.ble (Nat.land (cpVec >>> (4 * j)) 15) (Nat.land (cnVec >>> (4 * j)) 15)
           then Nat.land (cpVec >>> (4 * j)) 15 else Nat.land (cnVec >>> (4 * j)) 15) else 0) + _ = _
      rw [hbit, hcp_j, hcn_j, hmin_eq]
      cases ham : am.testBit j <;> simp [jF, ham] <;> omega
  have h0 := hgen 36 0 0 (by omega)
  simp only [Nat.shiftRight_zero, mul_zero, zero_add] at h0
  rw [h0]
  refine Finset.sum_congr (Finset.ext fun v => by simp) fun _ _ => rfl

/-- Bundled DPLL state invariant at `(am, nm, fc, cpVec, cnVec)` for a sign assignment `s3`. -/
structure SimdInv (oid am nm fc cpVec cnVec : Nat) (s3 : PauliIdx 3 → ℤ) : Prop where
  hA : ∀ u : Fin 36, am.testBit u.val = true →
    s3 (dec3 (B36_pt u)) = if nm.testBit u.val = true then -1 else 1
  hnm : ∀ u : Fin 36, am.testBit u.val = false → nm.testBit u.val = false
  hfc : 2 * fc = ((F36_set oid s3).filter fun uv =>
    am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true).card
  hcp : cpVec = ∑ v : Fin 36, cP_of oid am nm v * 16 ^ v.val
  hcn : cnVec = ∑ v : Fin 36, cN_of oid am nm v * 16 ^ v.val

lemma simdInv_init (oid : Nat) (s3 : PauliIdx 3 → ℤ) :
    SimdInv oid 0 0 0 0 0 s3 := by
  refine ⟨fun u h => by simp at h, fun _ _ => by simp, ?_, ?_, ?_⟩
  · have hemp : ((F36_set oid s3).filter fun uv =>
        (0 : Nat).testBit uv.1.val = true ∧ (0 : Nat).testBit uv.2.val = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro uv _; simp
    rw [hemp]; simp
  · symm; refine Finset.sum_eq_zero fun v _ => ?_
    have hc0 : cP_of oid 0 0 v = 0 := by
      simp [cP_of]
    rw [hc0, zero_mul]
  · symm; refine Finset.sum_eq_zero fun v _ => ?_
    have hc0 : cN_of oid 0 0 v = 0 := by
      simp [cN_of]
    rw [hc0, zero_mul]

/-- Single-vertex assignment step for BOTH `Tree36.S` and `initPatSimd`! -/
lemma simdInv_step (r : Fin 3) (f27 : Nat)
    (hdeg : ∀ u < 36, pop36 ((mkOrb36Tables r.val f27).pAdj.getD u 0 ||| (mkOrb36Tables r.val f27).nAdj.getD u 0) = 15)
    {am nm fc cpVec cnVec : Nat} {s3 : PauliIdx 3 → ℤ}
    (hinv : SimdInv r.val am nm fc cpVec cnVec s3)
    (u : Fin 36) (hu_un : am.testBit u.val = false)
    (isNeg : Bool) (hsu : s3 (dec3 (B36_pt u)) = if isNeg then -1 else 1) :
    let tbl := mkOrb36Tables r.val f27
    let bit := 1 <<< u.val
    let am' := am ||| bit
    let nm' := if isNeg then nm ||| bit else nm
    let fc' := fc + (((if isNeg then cnVec else cpVec) >>> (4 * u.val)) &&& 15)
    let cp' := cpVec + (if isNeg then tbl.pInc.getD u.val 0 else tbl.nInc.getD u.val 0)
    let cn' := cnVec + (if isNeg then tbl.nInc.getD u.val 0 else tbl.pInc.getD u.val 0)
    SimdInv r.val am' nm' fc' cp' cn' s3 := by
  intro tbl bit am' nm' fc' cp' cn'
  have hcp_lt : ∀ v : Fin 36, cP_of r.val am nm v < 16 := fun v => by have := cP_le_15 r f27 hdeg am nm v; omega
  have hcn_lt : ∀ v : Fin 36, cN_of r.val am nm v < 16 := fun v => by have := cN_le_15 r f27 hdeg am nm v; omega
  have ham' : ∀ w : Fin 36, am'.testBit w.val = (am.testBit w.val || decide (w.val = u.val)) := fun w =>
    testBit_bitOr_single am u.val w.val
  have hnm' : ∀ w : Fin 36, nm'.testBit w.val =
      if w = u then isNeg else nm.testBit w.val := fun w => by
    dsimp only [nm', bit]
    by_cases hwu : w = u
    · subst hwu; cases isNeg
      · simp [hinv.hnm w hu_un]
      · simp [testBit_bitOr_single]
    · have hne : w.val ≠ u.val := Fin.val_ne_of_ne hwu
      cases isNeg
      · simp [hwu]
      · rw [if_pos rfl, if_neg hwu, testBit_bitOr_single, decide_eq_false hne, Bool.or_false]
  have hA' : ∀ w : Fin 36, am'.testBit w.val = true →
      s3 (dec3 (B36_pt w)) = if nm'.testBit w.val = true then -1 else 1 := by
    intro w hw
    rw [ham' w, Bool.or_eq_true, decide_eq_true_eq] at hw
    by_cases hwu : w = u
    · subst hwu; rw [hnm' w, if_pos rfl, hsu]
    · have hw_am : am.testBit w.val = true := hw.resolve_right (Fin.val_ne_of_ne hwu)
      rw [hnm' w, if_neg hwu]; exact hinv.hA w hw_am
  have hnm_inv' : ∀ w : Fin 36, am'.testBit w.val = false → nm'.testBit w.val = false := by
    intro w hw
    rw [ham' w, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hw
    rw [hnm' w, if_neg (Fin.ne_of_val_ne hw.2)]
    exact hinv.hnm w hw.1
  have hadd_fc : (((if isNeg then cnVec else cpVec) >>> (4 * u.val)) &&& 15) =
      ((Finset.univ : Finset (Fin 36)).filter fun w =>
        am.testBit w.val = true ∧ (u, w) ∈ F36_set r.val s3).card := by
    cases isNeg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinv.hcp, nibble_extract (cP_of r.val am nm) hcp_lt u]
      dsimp only [cP_of]
      refine congr_arg Finset.card (Finset.ext fun w => ?_)
      simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hw, hfr⟩ <;> refine ⟨hw, ?_⟩
      · rw [M36_val_symm r.val u w, hinv.hA w hw, hsu]; simp only [Bool.false_eq_true, ↓reduceIte]; linarith
      · rw [M36_val_symm r.val w u, ← hinv.hA w hw]; rw [hsu] at hfr; simp only [Bool.false_eq_true, ↓reduceIte] at hfr; linarith
    · simp only [↓reduceIte]
      rw [hinv.hcn, nibble_extract (cN_of r.val am nm) hcn_lt u]
      dsimp only [cN_of]
      refine congr_arg Finset.card (Finset.ext fun w => ?_)
      simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hw, hfr⟩ <;> refine ⟨hw, ?_⟩
      · rw [M36_val_symm r.val u w, hinv.hA w hw, hsu]; simp only [↓reduceIte]; linarith
      · rw [M36_val_symm r.val w u, ← hinv.hA w hw]; rw [hsu] at hfr; simp only [↓reduceIte] at hfr; linarith
  have hfc' : 2 * fc' = ((F36_set r.val s3).filter fun uv =>
      am'.testBit uv.1.val = true ∧ am'.testBit uv.2.val = true).card := by
    let Old := (F36_set r.val s3).filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true
    let NewL := (F36_set r.val s3).filter fun uv => uv.1 = u ∧ am.testBit uv.2.val = true
    let NewR := (F36_set r.val s3).filter fun uv => am.testBit uv.1.val = true ∧ uv.2 = u
    have hu_union : ((F36_set r.val s3).filter fun uv => am'.testBit uv.1.val = true ∧ am'.testBit uv.2.val = true) =
        Old ∪ (NewL ∪ NewR) := by
      ext ⟨a, b⟩
      simp only [Old, NewL, NewR, Finset.mem_union, Finset.mem_filter, ham', Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hab, ha | ha, hb | hb⟩
        · left; exact ⟨hab, ha, hb⟩
        · right; right; exact ⟨hab, ha, Fin.ext hb⟩
        · right; left; exact ⟨hab, Fin.ext ha, hb⟩
        · exfalso; have h1 : a = b := Fin.ext (ha.trans hb.symm); subst h1
          simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and, M36_val,
            beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at hab; omega
      · rintro (⟨hab, ha, hb⟩ | ⟨hab, rfl, hb⟩ | ⟨hab, ha, rfl⟩)
        · exact ⟨hab, Or.inl ha, Or.inl hb⟩
        · exact ⟨hab, Or.inr rfl, Or.inl hb⟩
        · exact ⟨hab, Or.inl ha, Or.inr rfl⟩
    have hd_LR : Disjoint NewL NewR := Finset.disjoint_left.mpr fun ⟨a, b⟩ h1 h2 => by
      simp only [NewL, NewR, Finset.mem_filter] at h1 h2; rw [h1.2.1, hu_un] at h2; exact absurd h2.2.1 (by decide)
    have hd_O : Disjoint Old (NewL ∪ NewR) := Finset.disjoint_left.mpr fun ⟨a, b⟩ h1 h2 => by
      simp only [Old, NewL, NewR, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h2 with ⟨_, rfl, _⟩ | ⟨_, _, rfl⟩
      · rw [hu_un] at h1; exact absurd h1.2.1 (by decide)
      · rw [hu_un] at h1; exact absurd h1.2.2 (by decide)
    have hNewL_card : NewL.card = ((Finset.univ : Finset (Fin 36)).filter fun w =>
        am.testBit w.val = true ∧ (u, w) ∈ F36_set r.val s3).card := by
      refine Finset.card_bij (fun uv _ => uv.2) ?_ ?_ ?_
      · rintro ⟨a, b⟩ h; simp only [NewL, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        rcases h with ⟨hab, rfl, hb⟩; exact ⟨hb, hab⟩
      · rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 hb
        simp only [NewL, Finset.mem_filter] at h1 h2; exact Prod.ext (h1.2.1.trans h2.2.1.symm) hb
      · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        exact ⟨(u, w), by simp [NewL, hw.1, hw.2], rfl⟩
    have hNewR_card : NewR.card = NewL.card := by
      refine Finset.card_bij (fun uv _ => (uv.2, uv.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
      · rintro ⟨a, b⟩ h; simp only [NewR, NewL, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        exact ⟨by rw [M36_val_symm r.val b a]; linarith [h.1], h.2.2, h.2.1⟩
      · rintro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
        simp only [NewR, NewL, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        exact ⟨by rw [M36_val_symm r.val b a]; linarith [h.1], h.2.2, h.2.1⟩
    rw [hu_union, Finset.card_union_of_disjoint hd_O, Finset.card_union_of_disjoint hd_LR, hNewR_card,
        ← hinv.hfc, hNewL_card]
    dsimp only [fc']; rw [hadd_fc]; omega
  have hcP_step : ∀ v : Fin 36, cP_of r.val am' nm' v = cP_of r.val am nm v +
      (if M36_val r.val u.val v.val = (if isNeg then 1 else -1) then 1 else 0) := by
    intro v
    let S0 := (Finset.univ : Finset (Fin 36)).filter fun w =>
      am.testBit w.val = true ∧ M36_val r.val w.val v.val * (if nm.testBit w.val = true then -1 else 1) = -1
    let S1 := (Finset.univ : Finset (Fin 36)).filter fun w =>
      am'.testBit w.val = true ∧ M36_val r.val w.val v.val * (if nm'.testBit w.val = true then -1 else 1) = -1
    have hu_not : u ∉ S0 := by simp [S0, hu_un]
    have hcond_u : (M36_val r.val u.val v.val * (if nm'.testBit u.val = true then -1 else 1) = -1) ↔
        M36_val r.val u.val v.val = (if isNeg then 1 else -1) := by
      rw [hnm' u, if_pos rfl]; cases isNeg <;> simp <;> constructor <;> intro h <;> linarith
    by_cases hhit : M36_val r.val u.val v.val = (if isNeg then 1 else -1)
    · rw [if_pos hhit]
      have heq : S1 = insert u S0 := by
        ext w; simp only [S1, S0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
          ham', Bool.or_eq_true, decide_eq_true_eq]
        by_cases hwu : w = u
        · subst hwu; have hc := hcond_u.mpr hhit; simp only [hc, true_and, or_true, true_iff]; exact Or.inl trivial
        · simp [hwu, Fin.val_ne_of_ne hwu, hnm' w]
      change S1.card = S0.card + 1; rw [heq, Finset.card_insert_of_notMem hu_not]
    · rw [if_neg hhit, add_zero]
      have heq : S1 = S0 := by
        ext w; simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and, ham', Bool.or_eq_true, decide_eq_true_eq]
        by_cases hwu : w = u
        · subst hwu
          have hnc : ¬(M36_val r.val w.val v.val * (if nm'.testBit w.val = true then -1 else 1) = -1) := fun h => hhit (hcond_u.mp h)
          simp only [hu_un, hnc, Bool.false_eq_true, false_and, and_false]
        · simp [hwu, Fin.val_ne_of_ne hwu, hnm' w]
      change S1.card = S0.card; rw [heq]
  have hcN_step : ∀ v : Fin 36, cN_of r.val am' nm' v = cN_of r.val am nm v +
      (if M36_val r.val u.val v.val = (if isNeg then -1 else 1) then 1 else 0) := by
    intro v
    let S0 := (Finset.univ : Finset (Fin 36)).filter fun w =>
      am.testBit w.val = true ∧ M36_val r.val w.val v.val * (if nm.testBit w.val = true then -1 else 1) * (-1) = -1
    let S1 := (Finset.univ : Finset (Fin 36)).filter fun w =>
      am'.testBit w.val = true ∧ M36_val r.val w.val v.val * (if nm'.testBit w.val = true then -1 else 1) * (-1) = -1
    have hu_not : u ∉ S0 := by simp [S0, hu_un]
    have hcond_u : (M36_val r.val u.val v.val * (if nm'.testBit u.val = true then -1 else 1) * (-1) = -1) ↔
        M36_val r.val u.val v.val = (if isNeg then -1 else 1) := by
      rw [hnm' u, if_pos rfl]; cases isNeg <;> simp <;> constructor <;> intro h <;> linarith
    by_cases hhit : M36_val r.val u.val v.val = (if isNeg then -1 else 1)
    · rw [if_pos hhit]
      have heq : S1 = insert u S0 := by
        ext w; simp only [S1, S0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
          ham', Bool.or_eq_true, decide_eq_true_eq]
        by_cases hwu : w = u
        · subst hwu; have hc := hcond_u.mpr hhit; simp only [hc, true_and, or_true, true_iff]; exact Or.inl trivial
        · simp [hwu, Fin.val_ne_of_ne hwu, hnm' w]
      change S1.card = S0.card + 1; rw [heq, Finset.card_insert_of_notMem hu_not]
    · rw [if_neg hhit, add_zero]
      have heq : S1 = S0 := by
        ext w; simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and, ham', Bool.or_eq_true, decide_eq_true_eq]
        by_cases hwu : w = u
        · subst hwu
          have hnc : ¬(M36_val r.val w.val v.val * (if nm'.testBit w.val = true then -1 else 1) * (-1) = -1) := fun h => hhit (hcond_u.mp h)
          simp only [hu_un, hnc, Bool.false_eq_true, false_and, and_false]
        · simp [hwu, Fin.val_ne_of_ne hwu, hnm' w]
      change S1.card = S0.card; rw [heq]
  refine ⟨hA', hnm_inv', hfc', ?_, ?_⟩
  · dsimp only [cp']; rw [hinv.hcp]
    cases isNeg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [tbl_nInc_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by rw [hcP_step v]; simp only [Bool.false_eq_true, ↓reduceIte]; ring
    · simp only [↓reduceIte]
      rw [tbl_pInc_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by rw [hcP_step v]; simp only [↓reduceIte]; ring
  · dsimp only [cn']; rw [hinv.hcn]
    cases isNeg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [tbl_pInc_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by rw [hcN_step v]; simp only [Bool.false_eq_true, ↓reduceIte]; ring
    · simp only [↓reduceIte]
      rw [tbl_nInc_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => by rw [hcN_step v]; simp only [↓reduceIte]; ring

/-! ### Section 4: Soundness of `checkTris36`, `sliceUB/LBLoop`, `checkTree36`, and `orbit_dpll_hits_sp42` -/

lemma sound_checkTris36 (r : Fin 3) (f27 : Nat) {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (am maskOk : Nat) (tris : List (Nat × Nat × Nat)) (used : List (Nat × Nat))
    (hok : checkTris36 (mkOrb36Tables r.val f27).pAdj (mkOrb36Tables r.val f27).nAdj am maskOk tris used = true) :
    ∃ E : Finset (Fin 36 × Fin 36),
      E.card = tris.length ∧
      ∀ uv ∈ E, uv.1.val < uv.2.val ∧ uv ∈ F36_set r.val s3 ∧
        am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false ∧
        maskOk.testBit uv.1.val = true ∧ maskOk.testBit uv.2.val = true ∧
        (uv.1.val, uv.2.val) ∉ used := by
  induction tris generalizing used with
  | nil => exact ⟨∅, rfl, fun _ h => by simp at h⟩
  | cons t rest ih =>
    rcases t with ⟨a, b, c⟩
    unfold checkTris36 at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_true_eq,
      decide_eq_false_iff_not, beq_iff_eq,
      show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
      show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
      show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
      show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
      shr_and1_eq_zero_iff, shr_and1_eq_one_iff] at hok
    rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha35, hb35⟩, hc35⟩, hab⟩, hbc⟩, hama⟩, hamb⟩, hamc⟩, hmka⟩, hmkb⟩, hmkc⟩, hprod⟩, ⟨⟨hu1, hu2⟩, hu3⟩⟩, hrest⟩
    let fa : Fin 36 := ⟨a, by omega⟩; let fb : Fin 36 := ⟨b, by omega⟩; let fc : Fin 36 := ⟨c, by omega⟩
    rw [edgeSgnMask_eq_M36 r f27 fa fb, edgeSgnMask_eq_M36 r f27 fb fc, edgeSgnMask_eq_M36 r f27 fa fc] at hprod
    obtain ⟨E', hE'card, hE'prop⟩ := ih ((a, b) :: (b, c) :: (a, c) :: used) hrest
    have hpm : ∀ u : Fin 36, s3 (dec3 (B36_pt u)) = 1 ∨ s3 (dec3 (B36_pt u)) = -1 := fun u =>
      hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz u)).1
    have hsq : ∀ u : Fin 36, s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt u)) = 1 := fun u => by
      rcases hpm u with h | h <;> rw [h] <;> norm_num
    let eab := M36_val r.val a b * s3 (dec3 (B36_pt fa)) * s3 (dec3 (B36_pt fb))
    let ebc := M36_val r.val b c * s3 (dec3 (B36_pt fb)) * s3 (dec3 (B36_pt fc))
    let eac := M36_val r.val a c * s3 (dec3 (B36_pt fa)) * s3 (dec3 (B36_pt fc))
    have hprod_e : eab * ebc * eac = -1 := by
      dsimp only [eab, ebc, eac]
      calc (M36_val r.val a b * s3 (dec3 (B36_pt fa)) * s3 (dec3 (B36_pt fb))) *
           (M36_val r.val b c * s3 (dec3 (B36_pt fb)) * s3 (dec3 (B36_pt fc))) *
           (M36_val r.val a c * s3 (dec3 (B36_pt fa)) * s3 (dec3 (B36_pt fc)))
          = (M36_val r.val a b * M36_val r.val b c * M36_val r.val a c) *
            (s3 (dec3 (B36_pt fa)) * s3 (dec3 (B36_pt fa))) *
            (s3 (dec3 (B36_pt fb)) * s3 (dec3 (B36_pt fb))) *
            (s3 (dec3 (B36_pt fc)) * s3 (dec3 (B36_pt fc))) := by ring
        _ = (-1) * 1 * 1 * 1 := by rw [hprod, hsq fa, hsq fb, hsq fc]
        _ = -1 := by norm_num
    have hmem_one : (fa, fb) ∈ F36_set r.val s3 ∨ (fb, fc) ∈ F36_set r.val s3 ∨ (fa, fc) ∈ F36_set r.val s3 := by
      have he_pm : ∀ x y : Fin 36, M36_val r.val x.val y.val * s3 (dec3 (B36_pt x)) * s3 (dec3 (B36_pt y)) = 0 ∨
          M36_val r.val x.val y.val * s3 (dec3 (B36_pt x)) * s3 (dec3 (B36_pt y)) = 1 ∨
          M36_val r.val x.val y.val * s3 (dec3 (B36_pt x)) * s3 (dec3 (B36_pt y)) = -1 := fun x y => by
        rcases (M36_val_spec r x y).1 with hm | hm | hm <;> rcases hpm x with hx | hx <;> rcases hpm y with hy | hy <;>
          simp [hm, hx, hy]
      rcases he_pm fa fb with h1 | h1 | h1 <;> rcases he_pm fb fc with h2 | h2 | h2 <;>
      rcases he_pm fa fc with h3 | h3 | h3
      all_goals try (simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and]; first | exact Or.inl h1 | exact Or.inr (Or.inl h2) | exact Or.inr (Or.inr h3))
      all_goals (dsimp only [eab, ebc, eac] at hprod_e; rw [h1, h2, h3] at hprod_e; norm_num at hprod_e)
    have hadd : ∀ e : Fin 36 × Fin 36,
        (e = (fa, fb) ∨ e = (fb, fc) ∨ e = (fa, fc)) → e ∈ F36_set r.val s3 →
        ∃ E : Finset (Fin 36 × Fin 36), E.card = rest.length + 1 ∧
          ∀ uv ∈ E, uv.1.val < uv.2.val ∧ uv ∈ F36_set r.val s3 ∧
            am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false ∧
            maskOk.testBit uv.1.val = true ∧ maskOk.testBit uv.2.val = true ∧
            (uv.1.val, uv.2.val) ∉ used := by
      intro e he_eq he_fr
      have he_not : e ∉ E' := fun hm => by
        have hnu := (hE'prop e hm).2.2.2.2.2.2
        rcases he_eq with rfl | rfl | rfl <;> exact hnu (by simp [fa, fb, fc])
      refine ⟨insert e E', by rw [Finset.card_insert_of_notMem he_not, hE'card], fun uv huv => ?_⟩
      rcases Finset.mem_insert.mp huv with rfl | huv'
      · rcases he_eq with rfl | rfl | rfl
        · exact ⟨hab, he_fr, hama, hamb, hmka, hmkb, hu1⟩
        · exact ⟨hbc, he_fr, hamb, hamc, hmkb, hmkc, hu2⟩
        · exact ⟨lt_trans hab hbc, he_fr, hama, hamc, hmka, hmkc, hu3⟩
      · have h := hE'prop uv huv'
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          fun hm => h.2.2.2.2.2.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))⟩
    rcases hmem_one with h | h | h
    · exact hadd (fa, fb) (Or.inl rfl) h
    · exact hadd (fb, fc) (Or.inr (Or.inl rfl)) h
    · exact hadd (fa, fc) (Or.inr (Or.inr rfl)) h

lemma slice_mask_pop36 (r : Fin 3) (f27 : Nat) {am nm : Nat} {s3 : PauliIdx 3 → ℤ}
    (hA : ∀ v : Fin 36, am.testBit v.val = true → s3 (dec3 (B36_pt v)) = if nm.testBit v.val = true then -1 else 1)
    (slm : Nat) (u : Fin 36) (sgn : ℤ) (hsgn : sgn = 1 ∨ sgn = -1) :
    let tbl := mkOrb36Tables r.val f27
    let posK := (am &&& (am ^^^ nm)) &&& slm
    let negK := (am &&& nm) &&& slm
    let pm := tbl.pAdj.getD u.val 0
    let nmask := tbl.nAdj.getD u.val 0
    (if sgn = -1
     then pop36 (pm &&& posK) + pop36 (nmask &&& negK)
     else pop36 (pm &&& negK) + pop36 (nmask &&& posK)) =
    ((Finset.univ : Finset (Fin 36)).filter fun v =>
      am.testBit v.val = true ∧ slm.testBit v.val = true ∧
      M36_val r.val u.val v.val * sgn * s3 (dec3 (B36_pt v)) = -1).card := by
  intro tbl posK negK pm nmask
  have hposK : ∀ v : Fin 36, posK.testBit v.val = true ↔
      am.testBit v.val = true ∧ nm.testBit v.val = false ∧ slm.testBit v.val = true := fun v => by
    simp only [posK, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true]
    cases am.testBit v.val <;> cases nm.testBit v.val <;> cases slm.testBit v.val <;> simp
  have hnegK : ∀ v : Fin 36, negK.testBit v.val = true ↔
      am.testBit v.val = true ∧ nm.testBit v.val = true ∧ slm.testBit v.val = true := fun v => by
    simp only [negK, Nat.testBit_and, Bool.and_eq_true]
    cases am.testBit v.val <;> cases nm.testBit v.val <;> cases slm.testBit v.val <;> simp
  have hcomb : ∀ (m1 m2 : Nat) (P1 P2 P : Fin 36 → Prop) [DecidablePred P1] [DecidablePred P2] [DecidablePred P],
      (∀ v, m1.testBit v.val = true ↔ P1 v) →
      (∀ v, m2.testBit v.val = true ↔ P2 v) →
      (∀ v, ¬(P1 v ∧ P2 v)) →
      (∀ v, P v ↔ P1 v ∨ P2 v) →
      pop36 m1 + pop36 m2 = ((Finset.univ : Finset (Fin 36)).filter P).card := by
    intro m1 m2 P1 P2 P _ _ _ h1 h2 hdis hun
    rw [pop36_eq_card_of_iff m1 P1 h1, pop36_eq_card_of_iff m2 P2 h2, ← Finset.card_union_of_disjoint]
    · exact congr_arg Finset.card (Finset.ext fun v => by simp [hun v])
    · exact Finset.disjoint_left.mpr fun v hv1 hv2 =>
        hdis v ⟨(Finset.mem_filter.mp hv1).2, (Finset.mem_filter.mp hv2).2⟩
  rcases hsgn with rfl | rfl
  · rw [if_neg (by decide)]
    refine hcomb (pm &&& negK) (nmask &&& posK)
      (fun v => M36_val r.val u.val v.val = 1 ∧ am.testBit v.val = true ∧ nm.testBit v.val = true ∧ slm.testBit v.val = true)
      (fun v => M36_val r.val u.val v.val = -1 ∧ am.testBit v.val = true ∧ nm.testBit v.val = false ∧ slm.testBit v.val = true)
      _ (fun v => by rw [Nat.testBit_and, Bool.and_eq_true, tbl_pAdj_testBit, hnegK v])
      (fun v => by rw [Nat.testBit_and, Bool.and_eq_true, tbl_nAdj_testBit, hposK v])
      (fun v ⟨h1, h2⟩ => by linarith [h1.1, h2.1]) (fun v => ?_)
    constructor
    · rintro ⟨ham, hslm, hfr⟩
      have hsv := hA v ham
      rcases (M36_val_spec r u v).1 with hm | hm | hm <;> cases hnm : nm.testBit v.val
      all_goals rw [hsv, hm, hnm] at hfr
      all_goals try norm_num at hfr
      · exact Or.inl ⟨hm, ham, rfl, hslm⟩
      · exact Or.inr ⟨hm, ham, rfl, hslm⟩
    · rintro (⟨hm, ham, hnm, hslm⟩ | ⟨hm, ham, hnm, hslm⟩) <;>
        exact ⟨ham, hslm, by rw [hm, hA v ham, hnm]; decide⟩
  · rw [if_pos rfl]
    refine hcomb (pm &&& posK) (nmask &&& negK)
      (fun v => M36_val r.val u.val v.val = 1 ∧ am.testBit v.val = true ∧ nm.testBit v.val = false ∧ slm.testBit v.val = true)
      (fun v => M36_val r.val u.val v.val = -1 ∧ am.testBit v.val = true ∧ nm.testBit v.val = true ∧ slm.testBit v.val = true)
      _ (fun v => by rw [Nat.testBit_and, Bool.and_eq_true, tbl_pAdj_testBit, hposK v])
      (fun v => by rw [Nat.testBit_and, Bool.and_eq_true, tbl_nAdj_testBit, hnegK v])
      (fun v ⟨h1, h2⟩ => by linarith [h1.1, h2.1]) (fun v => ?_)
    constructor
    · rintro ⟨ham, hslm, hfr⟩
      have hsv := hA v ham
      rcases (M36_val_spec r u v).1 with hm | hm | hm <;> cases hnm : nm.testBit v.val
      all_goals rw [hsv, hm, hnm] at hfr
      all_goals try norm_num at hfr
      · exact Or.inl ⟨hm, ham, rfl, hslm⟩
      · exact Or.inr ⟨hm, ham, rfl, hslm⟩
    · rintro (⟨hm, ham, hnm, hslm⟩ | ⟨hm, ham, hnm, hslm⟩) <;>
        exact ⟨ham, hslm, by rw [hm, hA v ham, hnm]; decide⟩

lemma sound_sliceUBLoop (r : Fin 3) (f27 : Nat) {am nm : Nat} {s3 : PauliIdx 3 → ℤ}
    (hs3 : IsSignAssign s3)
    (hA : ∀ v : Fin 36, am.testBit v.val = true → s3 (dec3 (B36_pt v)) = if nm.testBit v.val = true then -1 else 1)
    (k : Fin 27) :
    let tbl := mkOrb36Tables r.val f27
    let slm := tbl.slMask.getD k.val 0
    let posK := (am &&& (am ^^^ nm)) &&& slm
    let negK := (am &&& nm) &&& slm
    let unK := slm ^^^ (am &&& slm)
    let res := sliceUBLoop tbl.pAdj tbl.nAdj am nm posK negK unK (tbl.slVerts.getD k.val []) 0 0 0
    (F36_slice r.val k s3).card ≤ 2 * (res.1 / 2 + res.2.1 / 2 + res.2.2) := by
  intro tbl slm posK negK unK res
  have hslv := tbl_slVerts_spec r.val f27 k
  have hF_split : ∀ (S : Finset (Fin 36 × Fin 36)),
      let SAA := S.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true
      let SUA := S.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = true
      let SAU := S.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = false
      let SUU := S.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false
      S.card = SAA.card + SUA.card + SAU.card + SUU.card := by
    intro S SAA SUA SAU SUU
    have hu : S = (SAA ∪ SUA) ∪ (SAU ∪ SUU) := by
      ext ⟨a, b⟩; simp only [SAA, SUA, SAU, SUU, Finset.mem_union, Finset.mem_filter]
      cases am.testBit a.val <;> cases am.testBit b.val <;> simp
    have hd1 : Disjoint SAA SUA := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [SAA, SUA, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
    have hd2 : Disjoint SAU SUU := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [SAU, SUU, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
    have hd3 : Disjoint (SAA ∪ SUA) (SAU ∪ SUU) := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [SAA, SUA, SAU, SUU, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rcases h2 with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;>
        (rw [h] at h'; exact absurd h' (by decide))
    conv_lhs => rw [hu]
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
    omega
  let Fk := F36_slice r.val k s3
  let F_AA := Fk.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true
  let F_UA := Fk.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = true
  let F_AU := Fk.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = false
  let F_UU := Fk.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false
  let E_UU : Finset (Fin 36 × Fin 36) := Finset.univ.filter fun uv =>
    slm.testBit uv.1.val = true ∧ slm.testBit uv.2.val = true ∧
    am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false ∧
    M36_val r.val uv.1.val uv.2.val ≠ 0
  have hFAA_even : 2 ∣ F_AA.card := card_even_of_symm_irrefl _
    (fun a b h => by
      simp only [F_AA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩)
    (fun a h => by
      simp only [F_AA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and, M36_val,
        beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at h; omega)
  have hEUU_even : 2 ∣ E_UU.card := card_even_of_symm_irrefl _
    (fun a b h => by
      simp only [E_UU, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, by rw [M36_val_symm r.val b a]; exact h.2.2.2.2⟩)
    (fun a h => by
      simp only [E_UU, Finset.mem_filter, Finset.mem_univ, true_and, M36_val,
        beq_self_eq_true, Bool.true_or, ↓reduceIte] at h; exact h.2.2.2.2 rfl)
  have hFAU_eq : F_AU.card = F_UA.card := by
    refine Finset.card_bij (fun uv _ => (uv.2, uv.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
    · rintro ⟨a, b⟩ h; simp only [F_AU, F_UA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩
    · rintro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
      simp only [F_AU, F_UA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩
  have hFUU_le : F_UU.card ≤ E_UU.card := by
    refine Finset.card_le_card fun ⟨a, b⟩ h => ?_
    simp only [F_UU, E_UU, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨(tbl_slMask_testBit r.val f27 k a).mpr h.1.2.1, (tbl_slMask_testBit r.val f27 k b).mpr h.1.2.2,
      h.2.1, h.2.2, fun h0 => by rw [h0, zero_mul, zero_mul] at h; omega⟩
  have hunK_tb : ∀ v : Fin 36, unK.testBit v.val = true ↔ am.testBit v.val = false ∧ slm.testBit v.val = true := fun v => by
    simp only [unK, Nat.testBit_xor, Nat.testBit_and]
    cases am.testBit v.val <;> cases slm.testBit v.val <;> simp
  have hloop : ∀ (us : List Nat) (fc2 re2 st : Nat),
      (∀ u ∈ us, u < 36) →
      let out := sliceUBLoop tbl.pAdj tbl.nAdj am nm posK negK unK us fc2 re2 st
      out.1 = fc2 + (us.map fun u =>
        if hu : u < 36 then
          if am.testBit u = true then
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu⟩)) * s3 (dec3 (B36_pt v)) = -1).card
          else 0
        else 0).sum ∧
      out.2.1 = re2 + (us.map fun u =>
        if hu : u < 36 then
          if am.testBit u = false then
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = false ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val ≠ 0).card
          else 0
        else 0).sum ∧
      (us.map fun u =>
        if hu : u < 36 then
          if am.testBit u = false then
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu⟩)) * s3 (dec3 (B36_pt v)) = -1).card
          else 0
        else 0).sum + st ≤ out.2.2 := by
    intro us
    induction us with
    | nil => intro fc2 re2 st _; simp [sliceUBLoop]
    | cons u us ih =>
      intro fc2 re2 st hus
      have hu36 : u < 36 := hus u (List.mem_cons_self ..)
      have hrest : ∀ w ∈ us, w < 36 := fun w hw => hus w (List.mem_cons_of_mem u hw)
      let uF : Fin 36 := ⟨u, hu36⟩
      unfold sliceUBLoop
      have ham_eq : Nat.beq (Nat.land (Nat.shiftRight am u) 1) 1 = am.testBit u := by
        change (((am >>> u) &&& 1) == 1) = am.testBit u
        rw [testBit_eq_shr_and1]; cases am.testBit u <;> rfl
      rw [ham_eq]
      cases ham : am.testBit u
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, hu36, ↓reduceDIte, ham]
        let cP := Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))
        let cN := Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
        let mx := if Nat.ble cP cN then cN else cP
        let rU := pop36 (Nat.land (Nat.lor (tbl.pAdj.getD u 0) (tbl.nAdj.getD u 0)) unK)
        have hih := ih fc2 (Nat.add re2 rU) (Nat.add st mx) hrest
        have hsu_pm : s3 (dec3 (B36_pt uF)) = 1 ∨ s3 (dec3 (B36_pt uF)) = -1 :=
          hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz uF)).1
        have hcp_eq := slice_mask_pop36 r f27 hA slm uF 1 (Or.inl rfl)
        have hcn_eq := slice_mask_pop36 r f27 hA slm uF (-1) (Or.inr rfl)
        simp only [show ¬((1 : ℤ) = -1) by decide, ↓reduceIte] at hcp_eq hcn_eq
        have hr_eq : pop36 ((tbl.pAdj.getD u 0 ||| tbl.nAdj.getD u 0) &&& unK) =
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = false ∧ slm.testBit v.val = true ∧ M36_val r.val u v.val ≠ 0).card := by
          refine pop36_eq_card_of_iff _ _ fun v => ?_
          rw [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true,
              tbl_pAdj_testBit r.val f27 uF v, tbl_nAdj_testBit r.val f27 uF v, hunK_tb v]
          rcases (M36_val_spec r uF v).1 with hm | hm | hm <;> simp [hm, uF] <;> tauto
        have hmx_ge : ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt uF)) * s3 (dec3 (B36_pt v)) = -1).card ≤
            if Nat.ble (pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK))
                (pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK))
            then pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK)
            else pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK) := by
          split_ifs with hble
          · have hle := Nat.le_of_ble_eq_true hble
            rcases hsu_pm with h | h <;> rw [h]
            · rw [← hcp_eq]; exact hle
            · rw [← hcn_eq]
          · have hgt : pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK) ≤
                pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK) := by
              by_contra hlt; apply hble; simp only [Nat.ble_eq]; omega
            rcases hsu_pm with h | h <;> rw [h]
            · rw [← hcp_eq]
            · rw [← hcn_eq]; exact hgt
        refine ⟨by rw [zero_add]; exact hih.1, ?_, ?_⟩
        · have h1 := hih.2.1
          change _ = re2 + pop36 ((tbl.pAdj.getD u 0 ||| tbl.nAdj.getD u 0) &&& unK) + _ at h1
          rw [hr_eq] at h1; change _ = re2 + (_ + _); rw [h1]; omega
        · have h2 := hih.2.2
          change _ + (st + mx) ≤ _ at h2
          have hmx_eq : mx = if Nat.ble (pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK))
              (pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK))
            then pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK)
            else pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK) := rfl
          have hmx_ge' : ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu36⟩)) * s3 (dec3 (B36_pt v)) = -1).card ≤ mx := by
            rw [hmx_eq]; exact hmx_ge
          refine le_trans ?_ h2
          omega
      · simp only [↓reduceIte, List.map_cons, List.sum_cons, hu36, ↓reduceDIte, ham]
        let fU := if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
          then Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
          else Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))
        have hih := ih (Nat.add fc2 fU) re2 st hrest
        have hsu_eq := hA uF ham
        have hnm_eq : Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1 = nm.testBit u := by
          change (((nm >>> u) &&& 1) == 1) = nm.testBit u
          rw [testBit_eq_shr_and1]; cases nm.testBit u <;> rfl
        have hf_eq : (if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
            then Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
            else Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))) =
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt uF)) * s3 (dec3 (B36_pt v)) = -1).card := by
          rw [hnm_eq, hsu_eq]
          cases hnm : nm.testBit u
          · have h := slice_mask_pop36 r f27 hA slm uF 1 (Or.inl rfl)
            simpa [hnm, uF] using h
          · have h := slice_mask_pop36 r f27 hA slm uF (-1) (Or.inr rfl)
            simpa [hnm, uF] using h
        refine ⟨?_, by simp only [Bool.true_eq_false, ↓reduceIte, zero_add]; exact hih.2.1,
            by simp only [Bool.true_eq_false, ↓reduceIte, zero_add]; exact hih.2.2⟩
        have h1 := hih.1
        change _ = fc2 + fU + _ at h1
        have hfU_eq : fU = ((Finset.univ : Finset (Fin 36)).filter fun v =>
            am.testBit v.val = true ∧ slm.testBit v.val = true ∧
            M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu36⟩)) * s3 (dec3 (B36_pt v)) = -1).card := hf_eq
        rw [h1, hfU_eq, Nat.add_assoc]
  have hsum_slv : ∀ g : Fin 36 → Nat,
      ((tbl.slVerts.getD k.val []).map fun u => if hu : u < 36 then g ⟨u, hu⟩ else 0).sum =
      ∑ u : Fin 36, if slm.testBit u.val = true then g u else 0 := by
    intro g
    have hnd := hslv.1
    rw [← List.sum_toFinset _ hnd]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun u hu => ⟨u, ((hslv.2 u).mp (List.mem_toFinset.mp hu)).1⟩) ?_ ?_ ?_ ?_
    · intro u hu
      have hmem := (hslv.2 u).mp (List.mem_toFinset.mp hu)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (tbl_slMask_testBit r.val f27 k ⟨u, hmem.1⟩).mpr hmem.2
    · intro a _ b _ h; exact congr_arg Fin.val h
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hq := (tbl_slMask_testBit r.val f27 k u).mp hu
      exact ⟨u.val, List.mem_toFinset.mpr ((hslv.2 u.val).mpr ⟨u.isLt, hq⟩), Fin.ext rfl⟩
    · intro u hu
      have hmem := (hslv.2 u).mp (List.mem_toFinset.mp hu)
      simp [hmem.1]
  have hlp := hloop (tbl.slVerts.getD k.val []) 0 0 0 (fun u hu => ((hslv.2 u).mp hu).1)
  have hres1 : res.1 = F_AA.card := by
    change (sliceUBLoop _ _ _ _ _ _ _ _ 0 0 0).1 = _
    rw [hlp.1, zero_add]
    have h1 := hsum_slv fun u => if am.testBit u.val = true then
      ((Finset.univ : Finset (Fin 36)).filter fun v =>
        am.testBit v.val = true ∧ slm.testBit v.val = true ∧
        M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card else 0
    rw [h1]
    dsimp only [F_AA, Fk, F36_slice, F36_set]
    rw [Finset.filter_filter, Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1u : slm.testBit u.val = true <;> by_cases h2u : am.testBit u.val = true
    · simp only [h1u, h2u, ↓reduceIte, Finset.card_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      have huq := (tbl_slMask_testBit r.val f27 k u).mp h1u
      have hvq := tbl_slMask_testBit r.val f27 k v
      by_cases h1v : slm.testBit v.val = true <;> by_cases h2v : am.testBit v.val = true
      · have hvq' := hvq.mp h1v
        simp only [h1v, h2v, h2u, huq, hvq', true_and, and_true]
      · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · have hvq' : Q3_form (otherC27_list.getD k.val 0) (B36_val v.val) ≠ 0 := fun h => h1v (hvq.mpr h)
        simp only [h1v, hvq', Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
    · simp only [h1u, h2u, Bool.false_eq_true, ↓reduceIte]
      exact (Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.false_eq_true, false_and, and_false, ↓reduceIte]).symm
    · simp only [h1u, Bool.false_eq_true, ↓reduceIte]
      have huq : Q3_form (otherC27_list.getD k.val 0) (B36_val u.val) ≠ 0 := fun h => h1u ((tbl_slMask_testBit r.val f27 k u).mpr h)
      exact (Finset.sum_eq_zero fun v _ => by simp only [huq, false_and, and_false, ↓reduceIte]).symm
    · simp only [h1u, Bool.false_eq_true, ↓reduceIte]
      exact (Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.false_eq_true, false_and, and_false, ↓reduceIte]).symm
  have hres21 : res.2.1 = E_UU.card := by
    change (sliceUBLoop _ _ _ _ _ _ _ _ 0 0 0).2.1 = _
    rw [hlp.2.1, zero_add]
    have h1 := hsum_slv fun u => if am.testBit u.val = false then
      ((Finset.univ : Finset (Fin 36)).filter fun v =>
        am.testBit v.val = false ∧ slm.testBit v.val = true ∧ M36_val r.val u.val v.val ≠ 0).card else 0
    rw [h1]
    dsimp only [E_UU]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1u : slm.testBit u.val = true <;> by_cases h2u : am.testBit u.val = false
    · simp only [h1u, h2u, ↓reduceIte, Finset.card_filter]
      refine Finset.sum_congr rfl fun v _ => by
        by_cases h1v : slm.testBit v.val = true <;> by_cases h2v : am.testBit v.val = false <;>
          simp [h1u, h2u, h1v, h2v]
    · simp only [h1u, h2u, ↓reduceIte]; exact (Finset.sum_eq_zero fun v _ => by simp [h2u]).symm
    · simp only [h1u, ↓reduceIte]; exact (Finset.sum_eq_zero fun v _ => by simp [h1u]).symm
    · simp only [h1u, ↓reduceIte]; exact (Finset.sum_eq_zero fun v _ => by simp [h1u]).symm
  have hres22 : F_UA.card ≤ res.2.2 := by
    have h2 := hlp.2.2; rw [add_zero] at h2
    have h1 := hsum_slv fun u => if am.testBit u.val = false then
      ((Finset.univ : Finset (Fin 36)).filter fun v =>
        am.testBit v.val = true ∧ slm.testBit v.val = true ∧
        M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card else 0
    rw [h1] at h2
    have hFUA_eq : F_UA.card = ∑ u : Fin 36, if slm.testBit u.val = true then
        if am.testBit u.val = false then
          ((Finset.univ : Finset (Fin 36)).filter fun v =>
            am.testBit v.val = true ∧ slm.testBit v.val = true ∧
            M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card
        else 0 else 0 := by
      dsimp only [F_UA, Fk, F36_slice, F36_set]
      rw [Finset.filter_filter, Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h1u : slm.testBit u.val = true <;> by_cases h2u : am.testBit u.val = false
      · simp only [h1u, h2u, ↓reduceIte, Finset.card_filter]
        refine Finset.sum_congr rfl fun v _ => ?_
        have huq := (tbl_slMask_testBit r.val f27 k u).mp h1u
        have hvq := tbl_slMask_testBit r.val f27 k v
        by_cases h1v : slm.testBit v.val = true <;> by_cases h2v : am.testBit v.val = true
        · have hvq' := hvq.mp h1v
          simp only [h1v, h2v, h2u, huq, hvq', true_and, and_true]
        · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
        · have hvq' : Q3_form (otherC27_list.getD k.val 0) (B36_val v.val) ≠ 0 := fun h => h1v (hvq.mpr h)
          simp only [h1v, hvq', Bool.false_eq_true, false_and, and_false, ↓reduceIte]
        · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · simp only [h1u, h2u, ↓reduceIte]; exact Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.true_eq_false, false_and, and_false, ↓reduceIte]
      · simp only [h1u, ↓reduceIte]
        have huq : Q3_form (otherC27_list.getD k.val 0) (B36_val u.val) ≠ 0 := fun h => h1u ((tbl_slMask_testBit r.val f27 k u).mpr h)
        exact Finset.sum_eq_zero fun v _ => by simp only [huq, false_and, and_false, ↓reduceIte]
      · simp only [h1u, ↓reduceIte]; exact Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.true_eq_false, false_and, and_false, ↓reduceIte]
    rw [hFUA_eq]; exact h2
  have hsp := hF_split Fk
  dsimp only at hsp
  change Fk.card = F_AA.card + F_UA.card + F_AU.card + F_UU.card at hsp
  rcases hFAA_even with ⟨a, ha⟩
  rcases hEUU_even with ⟨b, hb⟩
  change Fk.card ≤ _
  rw [hres1, hres21, ha, hb]
  omega

lemma sound_sliceLBLoop (r : Fin 3) (f27 : Nat) {am nm : Nat} {s3 : PauliIdx 3 → ℤ}
    (hs3 : IsSignAssign s3)
    (hA : ∀ v : Fin 36, am.testBit v.val = true → s3 (dec3 (B36_pt v)) = if nm.testBit v.val = true then -1 else 1)
    (k : Fin 27) (tris : List (Nat × Nat × Nat))
    (htris : checkTris36 (mkOrb36Tables r.val f27).pAdj (mkOrb36Tables r.val f27).nAdj am
      ((mkOrb36Tables r.val f27).slMask.getD k.val 0) tris [] = true) :
    let tbl := mkOrb36Tables r.val f27
    let slm := tbl.slMask.getD k.val 0
    let posK := (am &&& (am ^^^ nm)) &&& slm
    let negK := (am &&& nm) &&& slm
    let res := sliceLBLoop tbl.pAdj tbl.nAdj am nm posK negK (tbl.slVerts.getD k.val []) 0 0
    2 * (res.1 / 2 + res.2 + tris.length) ≤ (F36_slice r.val k s3).card := by
  intro tbl slm posK negK res
  have hslv := tbl_slVerts_spec r.val f27 k
  let Fk := F36_slice r.val k s3
  let F_AA := Fk.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true
  let F_UA := Fk.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = true
  let F_AU := Fk.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = false
  let F_UU := Fk.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false
  have hFk_part : Fk.card = F_AA.card + F_UA.card + F_AU.card + F_UU.card := by
    have hu : Fk = (F_AA ∪ F_UA) ∪ (F_AU ∪ F_UU) := by
      ext ⟨a, b⟩; simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter]
      cases am.testBit a.val <;> cases am.testBit b.val <;> simp
    have hd1 : Disjoint F_AA F_UA := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [F_AA, F_UA, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
    have hd2 : Disjoint F_AU F_UU := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [F_AU, F_UU, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
    have hd3 : Disjoint (F_AA ∪ F_UA) (F_AU ∪ F_UU) := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rcases h2 with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;>
        (rw [h] at h'; exact absurd h' (by decide))
    conv_lhs => rw [hu]
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
    omega
  have hFAA_even : 2 ∣ F_AA.card := card_even_of_symm_irrefl _
    (fun a b h => by
      simp only [F_AA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩)
    (fun a h => by
      simp only [F_AA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and, M36_val,
        beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at h; omega)
  have hFAU_eq : F_AU.card = F_UA.card := by
    refine Finset.card_bij (fun uv _ => (uv.2, uv.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
    · rintro ⟨a, b⟩ h; simp only [F_AU, F_UA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩
    · rintro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
      simp only [F_AU, F_UA, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨⟨by rw [M36_val_symm r.val b a]; linarith [h.1.1], h.1.2.2, h.1.2.1⟩, h.2.2, h.2.1⟩
  have htris_le : 2 * tris.length ≤ F_UU.card := by
    obtain ⟨E, hEcard, hEprop⟩ := sound_checkTris36 r f27 hs3 am slm tris [] htris
    let E' := E.image Prod.swap
    have hdis : Disjoint E E' := Finset.disjoint_left.mpr fun uv h1 h2 => by
      rcases Finset.mem_image.mp h2 with ⟨ab, hab, rfl⟩
      have := (hEprop ab hab).1; have := (hEprop (ab.2, ab.1) h1).1; dsimp at *; omega
    have hE'card : E'.card = E.card := Finset.card_image_of_injective E (fun _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h))
    have hsub : E ∪ E' ⊆ F_UU := by
      intro uv huv
      rcases Finset.mem_union.mp huv with h | h
      · have hp := hEprop uv h
        simp only [F_UU, Fk, F36_slice, Finset.mem_filter]
        exact ⟨⟨hp.2.1, (tbl_slMask_testBit r.val f27 k uv.1).mp hp.2.2.2.2.1,
          (tbl_slMask_testBit r.val f27 k uv.2).mp hp.2.2.2.2.2.1⟩, hp.2.2.1, hp.2.2.2.1⟩
      · rcases Finset.mem_image.mp h with ⟨ab, hab, rfl⟩
        have hp := hEprop ab hab
        simp only [F_UU, Fk, F36_slice, F36_set, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hp ⊢
        exact ⟨⟨by rw [M36_val_symm r.val ab.2 ab.1]; linarith [hp.2.1],
          (tbl_slMask_testBit r.val f27 k ab.2).mp hp.2.2.2.2.2.1,
          (tbl_slMask_testBit r.val f27 k ab.1).mp hp.2.2.2.2.1⟩, hp.2.2.2.1, hp.2.2.1⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hE'card, hEcard] at hle; omega
  have hloop : ∀ (us : List Nat) (fc2 st : Nat),
      (∀ u ∈ us, u < 36) →
      let out := sliceLBLoop tbl.pAdj tbl.nAdj am nm posK negK us fc2 st
      out.1 = fc2 + (us.map fun u =>
        if hu : u < 36 then
          if am.testBit u = true then
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu⟩)) * s3 (dec3 (B36_pt v)) = -1).card
          else 0
        else 0).sum ∧
      out.2 ≤ st + (us.map fun u =>
        if hu : u < 36 then
          if am.testBit u = false then
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu⟩)) * s3 (dec3 (B36_pt v)) = -1).card
          else 0
        else 0).sum := by
    intro us
    induction us with
    | nil => intro fc2 st _; simp [sliceLBLoop]
    | cons u us ih =>
      intro fc2 st hus
      have hu36 : u < 36 := hus u (List.mem_cons_self ..)
      have hrest : ∀ w ∈ us, w < 36 := fun w hw => hus w (List.mem_cons_of_mem u hw)
      let uF : Fin 36 := ⟨u, hu36⟩
      unfold sliceLBLoop
      have ham_eq : Nat.beq (Nat.land (Nat.shiftRight am u) 1) 1 = am.testBit u := by
        change (((am >>> u) &&& 1) == 1) = am.testBit u
        rw [testBit_eq_shr_and1]; cases am.testBit u <;> rfl
      rw [ham_eq]
      cases ham : am.testBit u
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, hu36, ↓reduceDIte, ham]
        let cP := Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))
        let cN := Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
        let mn := if Nat.ble cP cN then cP else cN
        have hih := ih fc2 (Nat.add st mn) hrest
        have hsu_pm : s3 (dec3 (B36_pt uF)) = 1 ∨ s3 (dec3 (B36_pt uF)) = -1 :=
          hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz uF)).1
        have hcp_eq := slice_mask_pop36 r f27 hA slm uF 1 (Or.inl rfl)
        have hcn_eq := slice_mask_pop36 r f27 hA slm uF (-1) (Or.inr rfl)
        simp only [show ¬((1 : ℤ) = -1) by decide, ↓reduceIte] at hcp_eq hcn_eq
        have hmn_le : (if Nat.ble (pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK))
                (pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK))
            then pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK)
            else pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK)) ≤
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt uF)) * s3 (dec3 (B36_pt v)) = -1).card := by
          split_ifs with hble
          · have hle := Nat.le_of_ble_eq_true hble
            rcases hsu_pm with h | h <;> rw [h]
            · rw [← hcp_eq]
            · rw [← hcn_eq]; exact hle
          · have hgt : pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK) ≤
                pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK) := by
              by_contra hlt; apply hble; simp only [Nat.ble_eq]; omega
            rcases hsu_pm with h | h <;> rw [h]
            · rw [← hcp_eq]; exact hgt
            · rw [← hcn_eq]
        refine ⟨by rw [zero_add]; exact hih.1, ?_⟩
        have h2 := hih.2
        change _ ≤ st + mn + _ at h2
        have hmn_eq : mn = if Nat.ble (pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK))
            (pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK))
          then pop36 (tbl.pAdj.getD u 0 &&& negK) + pop36 (tbl.nAdj.getD u 0 &&& posK)
          else pop36 (tbl.pAdj.getD u 0 &&& posK) + pop36 (tbl.nAdj.getD u 0 &&& negK) := rfl
        have hmn_le' : mn ≤ ((Finset.univ : Finset (Fin 36)).filter fun v =>
            am.testBit v.val = true ∧ slm.testBit v.val = true ∧
            M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu36⟩)) * s3 (dec3 (B36_pt v)) = -1).card := by
          rw [hmn_eq]; exact hmn_le
        refine le_trans h2 ?_
        omega
      · simp only [↓reduceIte, List.map_cons, List.sum_cons, hu36, ↓reduceDIte, ham]
        let fU := if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
          then Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
          else Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))
        have hih := ih (Nat.add fc2 fU) st hrest
        have hsu_eq := hA uF ham
        have hnm_eq : Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1 = nm.testBit u := by
          change (((nm >>> u) &&& 1) == 1) = nm.testBit u
          rw [testBit_eq_shr_and1]; cases nm.testBit u <;> rfl
        have hf_eq : (if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
            then Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) posK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) negK))
            else Nat.add (pop36 (Nat.land (tbl.pAdj.getD u 0) negK)) (pop36 (Nat.land (tbl.nAdj.getD u 0) posK))) =
            ((Finset.univ : Finset (Fin 36)).filter fun v =>
              am.testBit v.val = true ∧ slm.testBit v.val = true ∧
              M36_val r.val u v.val * s3 (dec3 (B36_pt uF)) * s3 (dec3 (B36_pt v)) = -1).card := by
          rw [hnm_eq, hsu_eq]
          cases hnm : nm.testBit u
          · have h := slice_mask_pop36 r f27 hA slm uF 1 (Or.inl rfl)
            simpa [hnm, uF] using h
          · have h := slice_mask_pop36 r f27 hA slm uF (-1) (Or.inr rfl)
            simpa [hnm, uF] using h
        refine ⟨?_, by simp only [Bool.true_eq_false, ↓reduceIte, zero_add]; exact hih.2⟩
        have h1 := hih.1
        change _ = fc2 + fU + _ at h1
        have hfU_eq : fU = ((Finset.univ : Finset (Fin 36)).filter fun v =>
            am.testBit v.val = true ∧ slm.testBit v.val = true ∧
            M36_val r.val u v.val * s3 (dec3 (B36_pt ⟨u, hu36⟩)) * s3 (dec3 (B36_pt v)) = -1).card := hf_eq
        rw [h1, hfU_eq, Nat.add_assoc]
  have hsum_slv : ∀ g : Fin 36 → Nat,
      ((tbl.slVerts.getD k.val []).map fun u => if hu : u < 36 then g ⟨u, hu⟩ else 0).sum =
      ∑ u : Fin 36, if slm.testBit u.val = true then g u else 0 := by
    intro g
    rw [← List.sum_toFinset _ hslv.1, ← Finset.sum_filter]
    refine Finset.sum_bij (fun u hu => ⟨u, ((hslv.2 u).mp (List.mem_toFinset.mp hu)).1⟩) ?_ ?_ ?_ ?_
    · intro u hu
      have hmem := (hslv.2 u).mp (List.mem_toFinset.mp hu)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (tbl_slMask_testBit r.val f27 k ⟨u, hmem.1⟩).mpr hmem.2
    · intro a _ b _ h; exact congr_arg Fin.val h
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have hq := (tbl_slMask_testBit r.val f27 k u).mp hu
      exact ⟨u.val, List.mem_toFinset.mpr ((hslv.2 u.val).mpr ⟨u.isLt, hq⟩), Fin.ext rfl⟩
    · intro u hu
      have hmem := (hslv.2 u).mp (List.mem_toFinset.mp hu); simp [hmem.1]
  have hlp := hloop (tbl.slVerts.getD k.val []) 0 0 (fun u hu => ((hslv.2 u).mp hu).1)
  have hres1 : res.1 = F_AA.card := by
    change (sliceLBLoop _ _ _ _ _ _ _ 0 0).1 = _
    rw [hlp.1, zero_add]
    rw [hsum_slv fun u => if am.testBit u.val = true then
      ((Finset.univ : Finset (Fin 36)).filter fun v =>
        am.testBit v.val = true ∧ slm.testBit v.val = true ∧
        M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card else 0]
    dsimp only [F_AA, Fk, F36_slice, F36_set]
    rw [Finset.filter_filter, Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1u : slm.testBit u.val = true <;> by_cases h2u : am.testBit u.val = true
    · simp only [h1u, h2u, ↓reduceIte, Finset.card_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      have huq := (tbl_slMask_testBit r.val f27 k u).mp h1u
      have hvq := tbl_slMask_testBit r.val f27 k v
      by_cases h1v : slm.testBit v.val = true <;> by_cases h2v : am.testBit v.val = true
      · have hvq' := hvq.mp h1v
        simp only [h1v, h2v, h2u, huq, hvq', true_and, and_true]
      · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · have hvq' : Q3_form (otherC27_list.getD k.val 0) (B36_val v.val) ≠ 0 := fun h => h1v (hvq.mpr h)
        simp only [h1v, hvq', Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
    · simp only [h1u, h2u, Bool.false_eq_true, ↓reduceIte]
      exact (Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.false_eq_true, false_and, and_false, ↓reduceIte]).symm
    · simp only [h1u, Bool.false_eq_true, ↓reduceIte]
      have huq : Q3_form (otherC27_list.getD k.val 0) (B36_val u.val) ≠ 0 := fun h => h1u ((tbl_slMask_testBit r.val f27 k u).mpr h)
      exact (Finset.sum_eq_zero fun v _ => by simp only [huq, false_and, and_false, ↓reduceIte]).symm
    · simp only [h1u, Bool.false_eq_true, ↓reduceIte]
      exact (Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.false_eq_true, false_and, and_false, ↓reduceIte]).symm
  have hres2 : res.2 ≤ F_UA.card := by
    have h2 := hlp.2; rw [zero_add] at h2
    rw [hsum_slv fun u => if am.testBit u.val = false then
      ((Finset.univ : Finset (Fin 36)).filter fun v =>
        am.testBit v.val = true ∧ slm.testBit v.val = true ∧
        M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card else 0] at h2
    have hFUA_eq : F_UA.card = ∑ u : Fin 36, if slm.testBit u.val = true then
        if am.testBit u.val = false then
          ((Finset.univ : Finset (Fin 36)).filter fun v =>
            am.testBit v.val = true ∧ slm.testBit v.val = true ∧
            M36_val r.val u.val v.val * s3 (dec3 (B36_pt u)) * s3 (dec3 (B36_pt v)) = -1).card
        else 0 else 0 := by
      dsimp only [F_UA, Fk, F36_slice, F36_set]
      rw [Finset.filter_filter, Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h1u : slm.testBit u.val = true <;> by_cases h2u : am.testBit u.val = false
      · simp only [h1u, h2u, ↓reduceIte, Finset.card_filter]
        refine Finset.sum_congr rfl fun v _ => ?_
        have huq := (tbl_slMask_testBit r.val f27 k u).mp h1u
        have hvq := tbl_slMask_testBit r.val f27 k v
        by_cases h1v : slm.testBit v.val = true <;> by_cases h2v : am.testBit v.val = true
        · have hvq' := hvq.mp h1v
          simp only [h1v, h2v, h2u, huq, hvq', true_and, and_true]
        · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
        · have hvq' : Q3_form (otherC27_list.getD k.val 0) (B36_val v.val) ≠ 0 := fun h => h1v (hvq.mpr h)
          simp only [h1v, hvq', Bool.false_eq_true, false_and, and_false, ↓reduceIte]
        · simp only [h2v, Bool.false_eq_true, false_and, and_false, ↓reduceIte]
      · simp only [h1u, h2u, ↓reduceIte]; exact Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.true_eq_false, false_and, and_false, ↓reduceIte]
      · simp only [h1u, ↓reduceIte]
        have huq : Q3_form (otherC27_list.getD k.val 0) (B36_val u.val) ≠ 0 := fun h => h1u ((tbl_slMask_testBit r.val f27 k u).mpr h)
        exact Finset.sum_eq_zero fun v _ => by simp only [huq, false_and, and_false, ↓reduceIte]
      · simp only [h1u, ↓reduceIte]; exact Finset.sum_eq_zero fun v _ => by simp only [h2u, Bool.true_eq_false, false_and, and_false, ↓reduceIte]
    rw [hFUA_eq]; exact h2
  rcases hFAA_even with ⟨a, ha⟩
  change _ ≤ Fk.card
  rw [hres1, ha]
  omega

/-- Master soundness of `checkTree36` (`S, G, U, M, O`) for Orbit 1 (`f₂₇ = 12`) and Orbit 2 (`f₂₇ = 13`). -/
lemma sound_checkTree36 (r : Fin 3) (hr : r.val = 1 ∨ r.val = 2) (t : Tree36) :
    let f27 := if r.val = 1 then 12 else 13
    let tbl := mkOrb36Tables r.val f27
    ∀ (am nm fc cpVec cnVec : Nat) {s3 : PauliIdx 3 → ℤ},
      IsSignAssign s3 →
      (∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) →
      frustPairs (nzPts 3) s3 ≤ 92 * 6 →
      isMinQminus09 s3 →
      SimdInv r.val am nm fc cpVec cnVec s3 →
      checkTree36 tbl am nm fc cpVec cnVec t = true →
      ∃ (spId : Fin 42) (us : List (PauliIdx 3)),
        w5FrustEq (applyTransvWord us s3) (listToSign3 (sp42Certs spId).s64) := by
  intro f27 tbl
  have hdeg : ∀ u < 36, pop36 (tbl.pAdj.getD u 0 ||| tbl.nAdj.getD u 0) = 15 := by
    intro u hu
    rcases hr with hr1 | hr2
    · have htbl : tbl = orb1_tables := by simp only [tbl, f27, hr1, ↓reduceIte]; exact orb1_tables_eq.symm
      rw [htbl]; exact (coreTables_spec.2.2.2.2.2.2 u hu).1
    · have htbl : tbl = orb2_tables := by simp only [tbl, f27, hr2, show ¬(2 = 1) by decide, ↓reduceIte]; exact orb2_tables_eq.symm
      rw [htbl]; exact (coreTables_spec.2.2.2.2.2.2 u hu).2.2.1
  have hcp_lt : ∀ am nm (v : Fin 36), cP_of r.val am nm v < 16 := fun am nm v => by
    have := cP_le_15 r f27 hdeg am nm v; omega
  have hcn_lt : ∀ am nm (v : Fin 36), cN_of r.val am nm v < 16 := fun am nm v => by
    have := cN_le_15 r f27 hdeg am nm v; omega
  induction t with
  | S u l rT ihl ihr =>
    intro am nm fc cpVec cnVec s3 hs3 hA27 hfA hmin hinv hok
    unfold checkTree36 at hok
    simp only [Bool.and_eq_true,
      show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
      show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
      show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
      show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
      decide_eq_true_eq, beq_iff_eq, shr_and1_eq_zero_iff] at hok
    rcases hok with ⟨⟨hu35, hu_un⟩, ⟨hl_ok, hr_ok⟩⟩
    let uF : Fin 36 := ⟨u, by omega⟩
    rcases hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz uF)).1 with hpos | hneg
    · have hinv' := simdInv_step r f27 hdeg hinv uF hu_un false (by simpa using hpos)
      exact ihl _ _ _ _ _ hs3 hA27 hfA hmin hinv' hl_ok
    · have hinv' := simdInv_step r f27 hdeg hinv uF hu_un true (by simpa using hneg)
      exact ihr _ _ _ _ _ hs3 hA27 hfA hmin hinv' hr_ok
  | G tris =>
    intro am nm fc cpVec cnVec s3 hs3 hA27 hfA hmin hinv hok
    exfalso
    unfold checkTree36 at hok
    simp only [Bool.and_eq_true, show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
      decide_eq_true_eq] at hok
    rcases hok with ⟨htris, h93⟩
    have hf27_eq : frustPairs (Qminus c0_09) s3 = 6 * f27 := by
      have h := frustPairs_Qminus09_eq_rep27 r hA27
      rcases hr with h1 | h1 <;> simp [f27, h1] at h ⊢ <;> exact h
    have hsplit := frustPairs_W52_A27_B36_split r hA27
    rw [hf27_eq] at hsplit
    let F := F36_set r.val s3
    let F_AA := F.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = true
    let F_UA := F.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = true
    let F_AU := F.filter fun uv => am.testBit uv.1.val = true ∧ am.testBit uv.2.val = false
    let F_UU := F.filter fun uv => am.testBit uv.1.val = false ∧ am.testBit uv.2.val = false
    have hF_part : F.card = F_AA.card + F_UA.card + F_AU.card + F_UU.card := by
      have hu : F = (F_AA ∪ F_UA) ∪ (F_AU ∪ F_UU) := by
        ext ⟨a, b⟩; simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter]
        cases am.testBit a.val <;> cases am.testBit b.val <;> simp
      have hd1 : Disjoint F_AA F_UA := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [F_AA, F_UA, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
      have hd2 : Disjoint F_AU F_UU := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [F_AU, F_UU, Finset.mem_filter] at h1 h2; rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
      have hd3 : Disjoint (F_AA ∪ F_UA) (F_AU ∪ F_UU) := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [F_AA, F_UA, F_AU, F_UU, Finset.mem_union, Finset.mem_filter] at h1 h2
        rcases h1 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rcases h2 with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;>
          (rw [h] at h'; exact absurd h' (by decide))
      conv_lhs => rw [hu]
      rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
      omega
    have hFAU_eq : F_AU.card = F_UA.card := by
      refine Finset.card_bij (fun uv _ => (uv.2, uv.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
      · rintro ⟨a, b⟩ h; simp only [F_AU, F_UA, F, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        exact ⟨by rw [M36_val_symm r.val b a]; linarith [h.1], h.2.2, h.2.1⟩
      · rintro ⟨a, b⟩ h; refine ⟨(b, a), ?_, rfl⟩
        simp only [F_AU, F_UA, F, F36_set, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        exact ⟨by rw [M36_val_symm r.val b a]; linarith [h.1], h.2.2, h.2.1⟩
    have hst_le : simdStarLB 36 am cpVec cnVec 0 ≤ F_UA.card := by
      rw [simdStarLB_spec r.val am nm cpVec cnVec (hcp_lt am nm) (hcn_lt am nm) hinv.hcp hinv.hcn]
      have hFUA_sum : F_UA.card = ∑ v : Fin 36, if am.testBit v.val = false then
          ((Finset.univ : Finset (Fin 36)).filter fun u =>
            am.testBit u.val = true ∧ (v, u) ∈ F).card else 0 := by
        conv_lhs => dsimp only [F_UA, F, F36_set]
        rw [Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : am.testBit v.val = false
        · rw [if_pos hv, Finset.card_filter]
          refine Finset.sum_congr rfl fun u _ => by simp only [hv, true_and, F, F36_set, Finset.mem_filter, Finset.mem_univ, and_comm]
        · rw [if_neg hv]; exact Finset.sum_eq_zero fun u _ => by simp [hv]
      rw [hFUA_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases hv : am.testBit v.val = false
      · rw [if_pos hv, if_pos hv]
        rcases hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz v)).1 with hp | hn
        · refine le_trans (min_le_left _ _) ?_
          dsimp only [cP_of]; refine le_of_eq (congr_arg Finset.card (Finset.ext fun u => ?_))
          simp only [F, F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> rintro ⟨hu, hfr⟩ <;> refine ⟨hu, ?_⟩
          · rw [M36_val_symm r.val v u, hp, hinv.hA u hu]; linarith
          · rw [M36_val_symm r.val u v, ← hinv.hA u hu]; rw [hp] at hfr; linarith
        · refine le_trans (min_le_right _ _) ?_
          dsimp only [cN_of]; refine le_of_eq (congr_arg Finset.card (Finset.ext fun u => ?_))
          simp only [F, F36_set, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> rintro ⟨hu, hfr⟩ <;> refine ⟨hu, ?_⟩
          · rw [M36_val_symm r.val v u, hn, hinv.hA u hu]; linarith
          · rw [M36_val_symm r.val u v, ← hinv.hA u hu]; rw [hn] at hfr; linarith
      · rw [if_neg hv, if_neg hv]
    have htris_le : 2 * tris.length ≤ F_UU.card := by
      obtain ⟨E, hEcard, hEprop⟩ := sound_checkTris36 r f27 hs3 am fullMask36 tris [] htris
      let E' := E.image Prod.swap
      have hdis : Disjoint E E' := Finset.disjoint_left.mpr fun uv h1 h2 => by
        rcases Finset.mem_image.mp h2 with ⟨ab, hab, rfl⟩
        have := (hEprop ab hab).1; have := (hEprop (ab.2, ab.1) h1).1; dsimp at *; omega
      have hE'card : E'.card = E.card := Finset.card_image_of_injective E (fun _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h))
      have hsub : E ∪ E' ⊆ F_UU := by
        intro uv huv
        rcases Finset.mem_union.mp huv with h | h
        · have hp := hEprop uv h; simp only [F_UU, F, Finset.mem_filter]; exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
        · rcases Finset.mem_image.mp h with ⟨ab, hab, rfl⟩
          have hp := hEprop ab hab
          simp only [F_UU, F, F36_set, Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap] at hp ⊢
          exact ⟨by rw [M36_val_symm r.val ab.2 ab.1]; linarith [hp.2.1], hp.2.2.2.1, hp.2.2.1⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdis, hE'card, hEcard] at hle; omega
    have hfc_eq : 2 * fc = F_AA.card := hinv.hfc
    have h93' : 93 ≤ f27 + fc + (simdStarLB 36 am cpVec cnVec 0 + tris.length) := h93
    change frustPairs (nzPts 3) s3 = 6 * f27 + 3 * F.card at hsplit
    omega
  | U k =>
    intro am nm fc cpVec cnVec s3 hs3 hA27 hfA hmin hinv hok
    exfalso
    unfold checkTree36 at hok
    simp only [Bool.and_eq_true, show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
      decide_eq_true_eq] at hok
    rcases hok with ⟨hk26, hub_le⟩
    let kF : Fin 27 := ⟨k, by omega⟩
    have hmin_k := hmin (dec3 (otherC27_pt kF)) (otherC27_pt_mem_ellCenters kF).1
    have hf27_eq : frustPairs (Qminus c0_09) s3 = 6 * f27 := by
      have h := frustPairs_Qminus09_eq_rep27 r hA27
      rcases hr with h1 | h1 <;> simp [f27, h1] at h ⊢ <;> exact h
    have hfk_eq := frustPairs_Qminus_ck_split r f27 kF hA27
    have hub := sound_sliceUBLoop r f27 hs3 hinv.hA kF
    have hf27_pos : 1 ≤ f27 := by rcases hr with h1 | h1 <;> simp [f27, h1]
    dsimp only [kF, tbl] at hub hfk_eq hub_le
    simp only [show ∀ a b, Nat.add a b = a + b from fun _ _ => rfl,
      show ∀ a b, Nat.sub a b = a - b from fun _ _ => rfl,
      show ∀ a b, Nat.div a b = a / b from fun _ _ => rfl,
      show ∀ a b, Nat.land a b = (a &&& b) from fun _ _ => rfl,
      show ∀ a b, Nat.xor a b = (a ^^^ b) from fun _ _ => rfl,
      show (mkOrb36Tables r.val f27).f27 = f27 from rfl] at hub_le
    rw [hf27_eq, hfk_eq] at hmin_k
    generalize sliceUBLoop (mkOrb36Tables r.val f27).pAdj (mkOrb36Tables r.val f27).nAdj am nm
      ((am &&& (am ^^^ nm)) &&& (mkOrb36Tables r.val f27).slMask.getD k 0)
      ((am &&& nm) &&& (mkOrb36Tables r.val f27).slMask.getD k 0)
      ((mkOrb36Tables r.val f27).slMask.getD k 0 ^^^ (am &&& (mkOrb36Tables r.val f27).slMask.getD k 0))
      ((mkOrb36Tables r.val f27).slVerts.getD k []) 0 0 0 = out at hub hub_le
    rcases out with ⟨fc2, re2, st⟩
    dsimp only at hub hub_le
    omega
  | M items =>
    intro am nm fc cpVec cnVec s3 hs3 hA27 hfA hmin hinv hok
    exfalso
    unfold checkTree36 at hok
    dsimp only at hok
    cases hres : checkMItems tbl am nm (Nat.land am (Nat.xor am nm)) (Nat.land am nm) items 0 0 with
    | none => rw [hres] at hok; simp at hok
    | some totEx =>
      rw [hres] at hok
      have htot_ge : 369 - 28 * f27 ≤ totEx := Nat.le_of_ble_eq_true hok
      have hf27_eq : frustPairs (Qminus c0_09) s3 = 6 * f27 := by
        have h := frustPairs_Qminus09_eq_rep27 r hA27
        rcases hr with h1 | h1 <;> simp [f27, h1] at h ⊢ <;> exact h
      let f_of : Fin 27 → Nat := fun k => tbl.slCA.getD k.val 0 + (F36_slice r.val k s3).card / 2
      have hfk_6 : ∀ k : Fin 27, frustPairs (Qminus (dec3 (otherC27_pt k))) s3 = 6 * f_of k := fun k => by
        rw [frustPairs_Qminus_ck_split r f27 k hA27]
        rcases F36_slice_even r.val k s3 with ⟨m, hm⟩
        dsimp only [f_of, tbl]; rw [hm]; omega
      have hfk_ge : ∀ k : Fin 27, f27 ≤ f_of k := fun k => by
        have h := hmin (dec3 (otherC27_pt k)) (otherC27_pt_mem_ellCenters k).1
        rw [hf27_eq, hfk_6 k] at h; omega
      have hitems_le : ∀ (its : List (Nat × List (Nat × Nat × Nat))) (seen acc out : Nat),
          checkMItems tbl am nm (Nat.land am (Nat.xor am nm)) (Nat.land am nm) its seen acc = some out →
          out ≤ acc + ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => seen.testBit k.val = false), (f_of k - f27) := by
        intro its
        induction its with
        | nil =>
          intro seen acc out h
          simp only [checkMItems, Option.some.injEq] at h; subst h; omega
        | cons it rest ih =>
          intro seen acc out h
          rcases it with ⟨k, tris⟩
          unfold checkMItems at h
          dsimp only at h
          split_ifs at h with hk htr
          · simp only [Bool.and_eq_true, show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
              show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
              show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
              show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
              decide_eq_true_eq, beq_iff_eq, shr_and1_eq_zero_iff] at hk
            let kF : Fin 27 := ⟨k, by omega⟩
            have hlb := sound_sliceLBLoop r f27 hs3 hinv.hA kF tris htr
            have hex_le : (tbl.slCA.getD k 0 + (sliceLBLoop tbl.pAdj tbl.nAdj am nm
                ((am &&& (am ^^^ nm)) &&& tbl.slMask.getD k 0) ((am &&& nm) &&& tbl.slMask.getD k 0)
                (tbl.slVerts.getD k []) 0 0).1 / 2 +
                ((sliceLBLoop tbl.pAdj tbl.nAdj am nm
                ((am &&& (am ^^^ nm)) &&& tbl.slMask.getD k 0) ((am &&& nm) &&& tbl.slMask.getD k 0)
                (tbl.slVerts.getD k []) 0 0).2 + tris.length)) - f27 ≤ f_of kF - f27 := by
              dsimp only [f_of, kF, tbl] at hlb ⊢; omega
            have hih := ih (seen ||| (1 <<< k)) _ out h
            simp only [show ∀ a b, Nat.add a b = a + b from fun _ _ => rfl,
              show ∀ a b, Nat.sub a b = a - b from fun _ _ => rfl,
              show ∀ a b, Nat.div a b = a / b from fun _ _ => rfl,
              show ∀ a b, Nat.land a b = (a &&& b) from fun _ _ => rfl,
              show ∀ a b, Nat.xor a b = (a ^^^ b) from fun _ _ => rfl,
              show tbl.f27 = f27 from rfl] at hih
            have hflt : Finset.univ.filter (fun j : Fin 27 => seen.testBit j.val = false) =
                insert kF (Finset.univ.filter (fun j : Fin 27 => (seen ||| (1 <<< k)).testBit j.val = false)) := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and,
                testBit_bitOr_single, Bool.or_eq_false_iff, decide_eq_false_iff_not]
              constructor
              · intro h0
                by_cases hjk : j = kF
                · left; exact hjk
                · right; exact ⟨h0, Fin.val_ne_of_ne hjk⟩
              · rintro (rfl | ⟨h0, _⟩)
                · exact hk.2
                · exact h0
            have hnotm : kF ∉ Finset.univ.filter (fun j : Fin 27 => (seen ||| (1 <<< k)).testBit j.val = false) := by
              simp [testBit_bitOr_single, kF]
            rw [hflt, Finset.sum_insert hnotm]
            omega
          all_goals simp at h
      have htot_le := hitems_le items 0 0 totEx hres
      simp only [Nat.zero_testBit, Finset.filter_true, zero_add] at htot_le
      -- Double counting `4 * fA = f27 + ∑_{k : Fin 27} f_of k ≤ 4 * 92 = 368`!
      have hdc := double_count_W52_Qminus52 s3
      have hsum_ell : ∑ c ∈ ellCenters 3, frustPairs (Qminus c) s3 =
          frustPairs (Qminus c0_09) s3 + ∑ k : Fin 27, frustPairs (Qminus (dec3 (otherC27_pt k))) s3 := by
        have hmem09 : c0_09 ∈ ellCenters 3 := by
          simp [ellCenters, quadForm0_c0_09]
        rw [← Finset.add_sum_erase _ _ hmem09]
        apply congr_arg (frustPairs (Qminus c0_09) s3 + ·)
        symm
        refine Finset.sum_bij (fun k _ => dec3 (otherC27_pt k)) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro k _; exact Finset.mem_erase.mpr ⟨(otherC27_pt_mem_ellCenters k).2, (otherC27_pt_mem_ellCenters k).1⟩
        · intro a _ b _ h; exact otherC27_val_inj (congr_arg Fin.val (equiv3.symm.injective h))
        · intro c hc
          obtain ⟨k, hk⟩ := otherC27_pt_surj (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hc).1
          exact ⟨k, Finset.mem_univ _, hk⟩
      rw [hsum_ell, hf27_eq] at hdc
      have hsum6 : ∑ k : Fin 27, frustPairs (Qminus (dec3 (otherC27_pt k))) s3 = 6 * ∑ k : Fin 27, f_of k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hfk_6 k
      rw [hsum6] at hdc
      have hsum_ex : ∑ k : Fin 27, (f_of k - f27) + 27 * f27 = ∑ k : Fin 27, f_of k := by
        have h27 : 27 * f27 = ∑ _k : Fin 27, f27 := by simp
        rw [h27, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfk_ge k)
      have hf27_le13 : f27 ≤ 13 := by rcases hr with h1 | h1 <;> simp [f27, h1]
      omega
  | O spId us =>
    intro am nm fc cpVec cnVec s3 hs3 hA27 hfA hmin hinv hok
    unfold checkTree36 at hok
    simp only [Bool.and_eq_true] at hok
    rcases hok with ⟨⟨⟨ham_full_b, hsp_b⟩, hus_lt⟩, hwl⟩
    have ham_full : am = fullMask36 := Nat.eq_of_beq_eq_true ham_full_b
    have hsp : spId < 42 := decide_eq_true_eq.mp hsp_b
    rw [A27_lit_eq, B36_lit_eq, wlines315_lit_eq] at hwl
    let sInit : Nat → ℤ := fun v =>
      match A27_list.idxOf? v with
      | some idxA => (rep27_vecs.getD r.val []).getD idxA 0
      | none =>
        match B36_list.idxOf? v with
        | some idxB => if Nat.beq (Nat.land (Nat.shiftRight nm idxB) 1) 1 then -1 else 1
        | none => 0
    have hagree : ∀ v : Fin 64, sInit v.val = s3 (dec3 v) := by
      intro v
      by_cases hv0 : v.val = 0
      · have hv_eq : v = 0 := Fin.ext hv0
        rw [hv_eq, dec3_zero, hs3.1]
        have ha0 : A27_list.idxOf? 0 = none := by
          rw [List.idxOf?_eq_none_iff]; intro h; obtain ⟨j, hj, heq⟩ := List.getElem_of_mem h
          have hj27 : j < 27 := by rwa [A27_list_len] at hj
          have hnz := (A27_val_props ⟨j, hj27⟩).1
          rw [A27_val, dpll_getD_eq_getElem _ _ hj, heq] at hnz; exact hnz rfl
        have hb0 : B36_list.idxOf? 0 = none := by
          rw [List.idxOf?_eq_none_iff]; intro h; obtain ⟨j, hj, heq⟩ := List.getElem_of_mem h
          have hj36 : j < 36 := by rwa [B36_list_len] at hj
          have hnz := (B36_val_props ⟨j, hj36⟩).1
          rw [B36_val, dpll_getD_eq_getElem _ _ hj, heq] at hnz; exact hnz rfl
        simp [sInit, ha0, hb0]
      · have hqlt := Q3_form_lt2 9 v.val
        have hq01 : Q3_form 9 v.val = 0 ∨ Q3_form 9 v.val = 1 := by omega
        rcases hq01 with hq0 | hq1
        · obtain ⟨ia, hia⟩ := A27_val_surj v hv0 hq0
          have hpt : A27_pt ia = v := Fin.ext hia
          rw [← hpt, hA27 ia]
          dsimp only [sInit, A27_pt]; rw [A27_idxOf_val ia]; rfl
        · obtain ⟨ib, hib⟩ := B36_val_surj v hv0 hq1
          have hpt : B36_pt ib = v := Fin.ext hib
          have hfull_tb : fullMask36.testBit ib.val = true := by
            have h1 : fullMask36 = 2 ^ 36 - 1 := by decide
            rw [h1, Nat.testBit_two_pow_sub_one]; exact decide_eq_true ib.isLt
          have hsb := hinv.hA ib (ham_full ▸ hfull_tb)
          rw [← hpt, hsb]
          dsimp only [sInit, B36_pt]
          rw [A27_idxOf_none_of_B36 ib, B36_idxOf_val ib]
          change (if (((nm >>> ib.val) &&& 1) == 1) then (-1 : ℤ) else 1) = _
          rw [testBit_eq_shr_and1]; cases nm.testBit ib.val <;> rfl
    let sInitArr : List ℤ := (List.range 64).map sInit
    let sOutArr : List ℤ := (List.range 64).map fun v => applyWord3Nat us (fun w => sInitArr.getD w 0) v
    have hsInitArr : ∀ v : Fin 64, sInitArr.getD v.val 0 = s3 (dec3 v) := fun v => by
      dsimp only [sInitArr]; rw [dpll_getD_map_range 64 sInit 0 v.isLt]; exact hagree v
    have hword_eq : ∀ v : Fin 64, sOutArr.getD v.val 0 = applyTransvWord (word3FromNat us) s3 (dec3 v) := fun v => by
      dsimp only [sOutArr]; rw [dpll_getD_map_range 64 _ 0 v.isLt]
      exact applyWord3Nat_eq_on_inv (fun _ => true) us
        (fun u hu => ⟨decide_eq_true_eq.mp (List.all_eq_true.mp hus_lt u hu), fun _ _ _ => rfl⟩)
        (fun w => sInitArr.getD w 0) s3 (fun w _ => hsInitArr w) v rfl
    have hoid : tbl.oid = r.val := rfl
    rw [hoid] at hwl
    have hwl' : (wlines315.all fun (a, b, c, _) =>
        sOutArr.getD a 0 * sOutArr.getD b 0 * sOutArr.getD c 0 ==
          getS64 (sp42S64List.getD spId []) a * getS64 (sp42S64List.getD spId []) b *
          getS64 (sp42S64List.getD spId []) c) = true := hwl
    have hfeq := w5FrustEq_of_wlines315_all (sOut := fun w => sOutArr.getD w 0) (spId := ⟨spId, hsp⟩) hword_eq hwl'
    exact ⟨⟨spId, hsp⟩, word3FromNat us, hfeq⟩

lemma checkPatList_append (tbl : Orb36Tables) (o12 : List Nat) (a b : List (Nat × Tree36)) :
    checkPatList tbl o12 (a ++ b) = (checkPatList tbl o12 a && checkPatList tbl o12 b) := by
  induction a with
  | nil => simp [checkPatList]
  | cons x xs ih =>
    rcases x with ⟨pat, tree⟩
    simp only [List.cons_append, checkPatList, ih, Bool.and_assoc]

lemma checkPatList_mem {tbl : Orb36Tables} {o12 : List Nat} {trees : List (Nat × Tree36)}
    (hok : checkPatList tbl o12 trees = true) {pat : Nat} {tree : Tree36}
    (hmem : (pat, tree) ∈ trees) :
    let res := initPatSimd tbl o12 pat 12 0 0 0 0 0
    res.1 = true ∧ checkTree36 tbl res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2.1 res.2.2.2.2.2 tree = true := by
  induction trees with
  | nil => simp at hmem
  | cons x xs ih =>
    rcases x with ⟨p0, t0⟩
    unfold checkPatList at hok
    simp only [Bool.and_eq_true] at hok
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq; exact hok.1
    · exact ih hok.2 hrest

/-- Soundness of `initPatSimd`: builds a valid `SimdInv` when `s3` matches 12-bit `pat` on `o12`. -/
lemma sound_initPatSimd (r : Fin 3) (f27 : Nat)
    (hdeg : ∀ u < 36, pop36 ((mkOrb36Tables r.val f27).pAdj.getD u 0 ||| (mkOrb36Tables r.val f27).nAdj.getD u 0) = 15)
    (o12 : List Nat) (pat : Nat) {s3 : PauliIdx 3 → ℤ}
    (hpat : ∀ i : Fin 12, ∀ hu : o12.getD i.val 0 < 36,
      s3 (dec3 (B36_pt ⟨o12.getD i.val 0, hu⟩)) = if pat.testBit i.val = true then -1 else 1) :
    let tbl := mkOrb36Tables r.val f27
    let res := initPatSimd tbl o12 pat 12 0 0 0 0 0
    res.1 = true → SimdInv r.val res.2.1 res.2.2.1 res.2.2.2.1 res.2.2.2.2.1 res.2.2.2.2.2 s3 := by
  intro tbl
  have hgen : ∀ rem am nm fc cp cn, rem ≤ 12 →
      SimdInv r.val am nm fc cp cn s3 →
      (initPatSimd tbl o12 pat rem am nm fc cp cn).1 = true →
      SimdInv r.val
        (initPatSimd tbl o12 pat rem am nm fc cp cn).2.1
        (initPatSimd tbl o12 pat rem am nm fc cp cn).2.2.1
        (initPatSimd tbl o12 pat rem am nm fc cp cn).2.2.2.1
        (initPatSimd tbl o12 pat rem am nm fc cp cn).2.2.2.2.1
        (initPatSimd tbl o12 pat rem am nm fc cp cn).2.2.2.2.2 s3 := by
    intro rem
    induction rem with
    | zero =>
      intro am nm fc cp cn _ hinv _
      exact hinv
    | succ rem ih =>
      intro am nm fc cp cn hle hinv hok
      let i := Nat.sub 11 rem
      have hi12 : i < 12 := by dsimp [i]; omega
      unfold initPatSimd at hok ⊢
      dsimp only at hok ⊢
      split_ifs at hok with hcond hbit
      · have hcond' := hcond
        simp only [Bool.and_eq_true, show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
          show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
          show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
          show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
          decide_eq_true_eq, beq_iff_eq, shr_and1_eq_zero_iff] at hcond'
        have hbit_tb : pat.testBit i = true := by
          change (((pat >>> i) &&& 1) == 1) = true at hbit
          exact (shr_and1_eq_one_iff pat i).mp (beq_iff_eq.mp hbit)
        have hu36 : o12.getD i 0 < 36 := Nat.lt_succ_of_le hcond'.1
        have hsu := hpat ⟨i, hi12⟩ hu36
        rw [if_pos hbit_tb] at hsu
        have hinv' := simdInv_step r f27 hdeg hinv ⟨o12.getD i 0, hu36⟩ hcond'.2 true (by simpa using hsu)
        rw [if_pos hcond, if_pos hbit]
        exact ih _ _ _ _ _ (by omega) hinv' hok
      · have hcond' := hcond
        simp only [Bool.and_eq_true, show ∀ x y, Nat.ble x y = decide (x ≤ y) from fun _ _ => rfl,
          show ∀ x y, Nat.beq x y = (x == y) from fun _ _ => rfl,
          show ∀ x y, Nat.land x y = (x &&& y) from fun _ _ => rfl,
          show ∀ x y, Nat.shiftRight x y = (x >>> y) from fun _ _ => rfl,
          decide_eq_true_eq, beq_iff_eq, shr_and1_eq_zero_iff] at hcond'
        have hbit_tb : pat.testBit i = false := by
          cases htb : pat.testBit i
          · rfl
          · exfalso; apply hbit; change (((pat >>> i) &&& 1) == 1) = true
            exact beq_iff_eq.mpr ((shr_and1_eq_one_iff pat i).mpr htb)
        have hu36 : o12.getD i 0 < 36 := Nat.lt_succ_of_le hcond'.1
        have hsu := hpat ⟨i, hi12⟩ hu36
        rw [if_neg (by rw [hbit_tb]; decide)] at hsu
        have hinv' := simdInv_step r f27 hdeg hinv ⟨o12.getD i 0, hu36⟩ hcond'.2 false (by simpa using hsu)
        rw [if_pos hcond, if_neg hbit]
        exact ih _ _ _ _ _ (by omega) hinv' hok
  exact hgen 12 0 0 0 0 0 le_rfl (simdInv_init r.val s3)

set_option maxHeartbeats 800000 in
/-- Soundness of `stabActionO12`: verified stabilizer element `(neg, g, us)` fixes `rep27[r]` on `A₂₇`
    and acts on `o12` by signed permutation `(p12, s12)`. -/
lemma sound_stabActionO12 (r : Fin 3) (o12 : List Nat) (ho12_len : o12.length = 12)
    (ho12_lt : ∀ v ∈ o12, v < 36) (elem : Bool × Nat × List Nat) (p12 : List Nat) (s12 : Nat)
    (hact : stabActionO12 r.val o12 elem = some (p12, s12)) :
    let (neg, g, us) := elem
    g < 64 ∧ (∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1) ∧
    p12.length = 12 ∧
    (∀ i : Fin 12, p12.getD i.val 0 < 12) ∧
    (∀ i j : Fin 12, p12.getD i.val 0 = p12.getD j.val 0 → i = j) ∧
    ∀ {s3 : PauliIdx 3 → ℤ} (hg : g < 64),
      (∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val) →
      let s3' := flipB36 neg (applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3))
      (∀ a : Fin 27, s3' (dec3 (A27_pt a)) = rep27_val r a.val) ∧
      (∀ i : Fin 12, ∀ hi : o12.getD i.val 0 < 36, ∀ hsrc : o12.getD (p12.getD i.val 0) 0 < 36,
        s3' (dec3 (B36_pt ⟨o12.getD i.val 0, hi⟩)) =
          (if s12.testBit i.val = true then -1 else 1) *
          s3 (dec3 (B36_pt ⟨o12.getD (p12.getD i.val 0) 0, hsrc⟩))) := by
  rcases elem with ⟨neg, g, us⟩
  unfold stabActionO12 at hact
  dsimp only at hact
  have hgu_b : (decide (g < 64) && us.all fun u => decide (u < 64) && (Q3_form 9 u == 1)) = true := by
    cases h' : (decide (g < 64) && us.all fun u => decide (u < 64) && (Q3_form 9 u == 1))
    · rw [h'] at hact; simp at hact
    · rfl
  rw [hgu_b] at hact; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hact
  rw [A27_lit_eq] at hact
  split_ifs at hact with hbad2
  · have hgu : g < 64 ∧ ∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hgu_b
      exact hgu_b
    have hA_fix_b : ((List.range 27).all fun i =>
        applyGauge3Nat g (applyWord3Nat us (fun v =>
          ((List.range 64).map fun w => match A27_list.idxOf? w with
            | some idx => (rep27_vecs.getD r.val []).getD idx 0 | none => 0).getD v 0)) (A27_val i) ==
        (rep27_vecs.getD r.val []).getD i 0) = true := by
      cases h' : ((List.range 27).all fun i =>
        applyGauge3Nat g (applyWord3Nat us (fun v =>
          ((List.range 64).map fun w => match A27_list.idxOf? w with
            | some idx => (rep27_vecs.getD r.val []).getD idx 0 | none => 0).getD v 0)) (A27_val i) ==
        (rep27_vecs.getD r.val []).getD i 0)
      · exfalso; apply hbad2
        change (!((List.range 27).all fun i =>
          applyGauge3Nat g (applyWord3Nat us (fun v =>
            ((List.range 64).map fun w => match A27_list.idxOf? w with
              | some idx => (rep27_vecs.getD r.val []).getD idx 0 | none => 0).getD v 0)) (A27_val i) ==
          (rep27_vecs.getD r.val []).getD i 0)) = true
        exact congr_arg (!·) h'
      · rfl
    -- Verify the `build` loop invariant!
    have hrev_lt : ∀ (ws : List Nat) (p0 : Fin 64) (acc : ℤ), (∀ w ∈ ws, w < 64) →
        (ws.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, acc)).1 < 64 := by
      intro ws
      induction ws with
      | nil => intro p0 _ _; exact p0.isLt
      | cons w ws ih =>
        intro p0 acc hws
        simp only [List.foldl_cons]
        have hw := hws w (List.mem_cons_self ..)
        exact ih ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ _ (fun x hx => hws x (List.mem_cons_of_mem w hx))
    have hrev_eq : ∀ (ws : List Nat) (p0 : Fin 64) (acc : ℤ) (hws : ∀ w ∈ ws, w < 64),
        let resN := ws.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, acc)
        let resP := (word3FromNat ws).foldl
          (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (dec3 p0, acc)
        resP.1 = dec3 ⟨resN.1, hrev_lt ws p0 acc hws⟩ ∧ resP.2 = resN.2 := by
      intro ws
      induction ws with
      | nil => intro p0 acc _; exact ⟨rfl, rfl⟩
      | cons w ws ih =>
        intro p0 acc hws
        have hw := hws w (List.mem_cons_self ..)
        have hrest : ∀ x ∈ ws, x < 64 := fun x hx => hws x (List.mem_cons_of_mem w hx)
        have hpt : transvPt (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 p0) =
            dec3 ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ := by
          rw [show (⟨w % 64, Nat.mod_lt _ (by omega)⟩ : Fin 64) = ⟨w, hw⟩ from Fin.ext (Nat.mod_eq_of_lt hw),
              transvPt_dec3]
        have hsgn : transvSgn (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 p0) = transv3_sgn w p0.val := by
          rw [show (⟨w % 64, Nat.mod_lt _ (by omega)⟩ : Fin 64) = ⟨w, hw⟩ from Fin.ext (Nat.mod_eq_of_lt hw),
              transvSgn_dec3]
        have hpair : (transvPt (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 p0),
            acc * transvSgn (dec3 ⟨w % 64, Nat.mod_lt _ (by omega)⟩) (dec3 p0)) =
            (dec3 ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩, acc * transv3_sgn w p0.val) :=
          Prod.ext hpt (congr_arg (acc * ·) hsgn)
        dsimp only
        simp only [word3FromNat, List.map_cons, List.foldl_cons]
        rw [hpair]
        exact ih ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ (acc * transv3_sgn w p0.val) hrest
    have hus_rev_lt : ∀ w ∈ us.reverse, w < 64 := fun w hw => (hgu.2 w (List.mem_reverse.mp hw)).1
    have hbuild : ∀ k i revP s12cur seen, k + i = 12 →
        revP.length = i →
        (∀ t : Fin 12, t.val < i → revP.reverse.getD t.val 0 < 12) →
        (∀ t : Fin 12, i ≤ t.val → s12cur.testBit t.val = false) →
        (∀ b : Fin 12, seen.testBit b.val = true ↔ ∃ t : Fin 12, t.val < i ∧ revP.reverse.getD t.val 0 = b.val) →
        (∀ t : Fin 12, t.val < i → ∀ ht : o12.getD t.val 0 < 36, ∀ hsrc : o12.getD (revP.reverse.getD t.val 0) 0 < 36,
          let p0 := B36_pt ⟨o12.getD t.val 0, ht⟩
          let res := us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, (1 : ℤ))
          res.1 = B36_val (o12.getD (revP.reverse.getD t.val 0) 0) ∧
          (if neg then (-1 : ℤ) else 1) * res.2 * (if symp3 g p0.val == 0 then 1 else -1) =
            if s12cur.testBit t.val = true then -1 else 1) →
        stabActionO12Build o12 neg g us.reverse k revP s12cur seen = some (p12, s12) →
        p12.length = 12 ∧
        (∀ t : Fin 12, p12.getD t.val 0 < 12) ∧
        (∀ b : Fin 12, ∃ t : Fin 12, p12.getD t.val 0 = b.val) ∧
        (∀ t : Fin 12, ∀ ht : o12.getD t.val 0 < 36, ∀ hsrc : o12.getD (p12.getD t.val 0) 0 < 36,
          let p0 := B36_pt ⟨o12.getD t.val 0, ht⟩
          let res := us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, (1 : ℤ))
          res.1 = B36_val (o12.getD (p12.getD t.val 0) 0) ∧
          (if neg then (-1 : ℤ) else 1) * res.2 * (if symp3 g p0.val == 0 then 1 else -1) =
            if s12.testBit t.val = true then -1 else 1) := by
      intro k
      induction k with
      | zero =>
        intro i revP s12cur seen hi hlen hlt hs12hi hseen hrec hok
        have hi12 : i = 12 := by omega
        subst hi12
        unfold stabActionO12Build at hok
        cases h4095 : (seen == 4095)
        · rw [h4095] at hok; simp at hok
        · rw [h4095] at hok
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hok
          rcases hok with ⟨rfl, rfl⟩
          have h4095_eq : seen = 4095 := beq_iff_eq.mp h4095
          refine ⟨by simp [hlen], fun t => hlt t t.isLt, fun b => ?_, fun t ht hsrc => hrec t t.isLt ht hsrc⟩
          have htb : (4095 : Nat).testBit b.val = true := by
            have h1 : (4095 : Nat) = 2 ^ 12 - 1 := by decide
            rw [h1, Nat.testBit_two_pow_sub_one]; exact decide_eq_true b.isLt
          obtain ⟨t, _, ht⟩ := (hseen b).mp (h4095_eq ▸ htb)
          exact ⟨t, ht⟩
      | succ k ih =>
        intro i revP s12cur seen hi hlen hlt hs12hi hseen hrec hok
        have hi12 : i < 12 := by omega
        have hi_eq : Nat.sub 11 k = i := by change 11 - k = i; omega
        have hunf : stabActionO12Build o12 neg g us.reverse (k + 1) revP s12cur seen =
            let bi := o12.getD i 0
            let p0 := B36_val bi
            let (cur, sg) := us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p0, (1 : ℤ))
            match B36_list.idxOf? cur with
            | none => none
            | some bj =>
              match o12.idxOf? bj with
              | none => none
              | some src =>
                let sgnTot : ℤ := (if neg then -1 else 1) * sg * (if symp3 g p0 == 0 then 1 else -1)
                let s12' := if sgnTot == -1 then Nat.lor s12cur (Nat.shiftLeft 1 i) else s12cur
                stabActionO12Build o12 neg g us.reverse k (src :: revP) s12' (Nat.lor seen (Nat.shiftLeft 1 src)) := by
          rw [stabActionO12Build.eq_2, hi_eq, B36_lit_eq]; rfl
        rw [hunf] at hok; dsimp only at hok
        cases hB : B36_list.idxOf? (us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (B36_val (o12.getD i 0), (1 : ℤ))).1 with
        | none => rw [hB] at hok; simp at hok
        | some bj =>
          rw [hB] at hok; dsimp only at hok
          cases hO : o12.idxOf? bj with
          | none => rw [hO] at hok; simp at hok
          | some src =>
            rw [hO] at hok; dsimp only at hok
            have hsrc_lt : src < 12 := by
              have := (List.idxOf?_eq_some_iff.mp hO).1; rwa [ho12_len] at this
            have hbj_eq : o12.getD src 0 = bj := by
              have h1 := (List.idxOf?_eq_some_iff.mp hO).2.1
              rw [dpll_getD_eq_getElem _ _ (by omega), h1]
            have hbj_lt : bj < 36 := by
              have := (List.idxOf?_eq_some_iff.mp hB).1; rwa [B36_list_len] at this
            have hcur_eq : (us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c))
                (B36_val (o12.getD i 0), (1 : ℤ))).1 = B36_val (o12.getD src 0) := by
              rw [hbj_eq]
              have h1 := (List.idxOf?_eq_some_iff.mp hB).2.1
              symm; rw [B36_val, dpll_getD_eq_getElem _ _ (by rw [B36_list_len]; exact hbj_lt), h1]
            let sg := (us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c))
                (B36_val (o12.getD i 0), (1 : ℤ))).2
            have hsg_pm : sg = 1 ∨ sg = -1 := by
              have hfold_pm : ∀ (ws : List Nat) (p : Nat) (acc : ℤ), (acc = 1 ∨ acc = -1) →
                  (ws.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p, acc)).2 = 1 ∨
                  (ws.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p, acc)).2 = -1 := by
                intro ws
                induction ws with
                | nil => intro _ _ h; exact h
                | cons w ws ihw =>
                  intro p acc hacc; simp only [List.foldl_cons]
                  refine ihw _ _ ?_
                  have hts : transv3_sgn w p = 1 ∨ transv3_sgn w p = -1 := by
                    unfold transv3_sgn; split_ifs <;> simp
                  rcases hacc with rfl | rfl <;> rcases hts with h1 | h1 <;> rw [h1] <;> simp
              exact hfold_pm us.reverse _ 1 (Or.inl rfl)
            let sgnTot : ℤ := (if neg then -1 else 1) * sg * (if symp3 g (B36_val (o12.getD i 0)) == 0 then 1 else -1)
            have hsgnTot_pm : sgnTot = 1 ∨ sgnTot = -1 := by
              dsimp only [sgnTot]
              cases neg <;> rcases hsg_pm with h1 | h1 <;> cases (symp3 g (B36_val (o12.getD i 0)) == 0) <;>
                simp [h1]
            let s12' := if sgnTot == -1 then Nat.lor s12cur (Nat.shiftLeft 1 i) else s12cur
            have hs12'_tb : ∀ t : Fin 12, s12'.testBit t.val =
                if t.val = i then (sgnTot == -1) else s12cur.testBit t.val := by
              intro t
              dsimp only [s12']
              have htb_lor : ∀ m k b, (Nat.lor m (Nat.shiftLeft 1 k)).testBit b = (m.testBit b || decide (b = k)) :=
                fun m k b => testBit_bitOr_single m k b
              by_cases hti : t.val = i
              · rw [if_pos hti]
                cases hst : (sgnTot == -1)
                · simp only [Bool.false_eq_true, ↓reduceIte]; exact hs12hi t (by omega)
                · simp only [↓reduceIte]; rw [htb_lor, decide_eq_true hti, Bool.or_true]
              · rw [if_neg hti]
                cases hst : (sgnTot == -1)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                · simp only [↓reduceIte]; rw [htb_lor, decide_eq_false hti, Bool.or_false]
            have hgetD_rev : ∀ t : Fin 12, t.val < i + 1 →
                (src :: revP).reverse.getD t.val 0 = if t.val < i then revP.reverse.getD t.val 0 else src := by
              intro t ht
              simp only [List.reverse_cons]
              by_cases hti : t.val < i
              · rw [if_pos hti]
                simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show t.val < revP.reverse.length by simp [hlen, hti])]
              · rw [if_neg hti]
                have hteq : t.val = i := by omega
                rw [hteq]
                simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show revP.reverse.length ≤ i by simp [hlen]), hlen]
            refine ih (i + 1) (src :: revP) s12' (seen ||| (1 <<< src)) (by omega)
              (by simp [hlen]) ?_ ?_ ?_ ?_ hok
            · intro t ht; rw [hgetD_rev t ht]; split_ifs with hti
              · exact hlt t hti
              · exact hsrc_lt
            · intro t ht; rw [hs12'_tb t, if_neg (by omega)]; exact hs12hi t (by omega)
            · intro b
              rw [testBit_bitOr_single, Bool.or_eq_true, decide_eq_true_eq, hseen b]
              constructor
              · rintro (⟨t, hti, hteq⟩ | rfl)
                · exact ⟨t, by omega, by rw [hgetD_rev t (by omega), if_pos hti]; exact hteq⟩
                · exact ⟨⟨i, hi12⟩, Nat.lt_succ_self i, by rw [hgetD_rev ⟨i, hi12⟩ (Nat.lt_succ_self i), if_neg (lt_irrefl i)]⟩
              · rintro ⟨t, ht, hteq⟩
                rw [hgetD_rev t ht] at hteq
                by_cases hti : t.val < i
                · rw [if_pos hti] at hteq; exact Or.inl ⟨t, hti, hteq⟩
                · rw [if_neg hti] at hteq; exact Or.inr hteq.symm
            · intro t ht htlt hsrclt
              rw [hgetD_rev t ht] at hsrclt ⊢
              by_cases hti : t.val < i
              · rw [if_pos hti] at hsrclt ⊢
                rw [hs12'_tb t, if_neg (Nat.ne_of_lt hti)]
                exact hrec t hti htlt hsrclt
              · have hteq : t.val = i := by omega
                rw [if_neg hti] at hsrclt ⊢
                rw [hs12'_tb t, if_pos hteq]
                refine ⟨by simpa [B36_pt, hteq] using hcur_eq, ?_⟩
                change (if neg then (-1 : ℤ) else 1) * _ * _ = _
                have hsg_eq : (us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1))
                    ((B36_pt ⟨o12.getD t.val 0, htlt⟩).val, (1 : ℤ))).2 = sg := by
                  simp [sg, B36_pt, hteq]
                have hsp_eq : symp3 g (B36_pt ⟨o12.getD t.val 0, htlt⟩).val = symp3 g (B36_val (o12.getD i 0)) := by
                  simp [B36_pt, hteq]
                rw [hsg_eq, hsp_eq]
                change sgnTot = _
                rcases hsgnTot_pm with h1 | h1 <;> rw [h1] <;> decide
    obtain ⟨hp12_len, hp12_lt, hp12_surj, hp12_rec⟩ :=
      hbuild 12 0 [] 0 0 rfl rfl (fun _ h => by omega) (fun _ _ => by simp)
        (fun b => by simp) (fun _ h => by omega) hact
    -- Surjective map `Fin 12 → Fin 12` is injective!
    have hp12_inj : ∀ i j : Fin 12, p12.getD i.val 0 = p12.getD j.val 0 → i = j := by
      let f : Fin 12 → Fin 12 := fun i => ⟨p12.getD i.val 0, hp12_lt i⟩
      have hsurj : Function.Surjective f := fun b => by
        obtain ⟨t, ht⟩ := hp12_surj b; exact ⟨t, Fin.ext ht⟩
      have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
      intro i j h; exact hinj (Fin.ext h)
    refine ⟨hgu.1, hgu.2, hp12_len, hp12_lt, hp12_inj, ?_⟩
    intro s3 hg hA27
    let s3' := flipB36 neg (applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3))
    have hus_Q : ∀ u ∈ word3FromNat us, quadForm c0_09 u = 1 := by
      intro u hu; rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
      have h := hgu.2 un hun
      simp only [c0_09, quadForm_dec3, Nat.mod_eq_of_lt h.1, h.2]; rfl
    refine ⟨?_, ?_⟩
    · intro a
      have hq0 : quadForm c0_09 (dec3 (A27_pt a)) = 0 := (Finset.mem_filter.mp (A27_pt_mem_Qminus a)).2
      rw [flipB36_on_A27 neg _ hq0]
      let sAInit : Nat → ℤ := fun v =>
        ((List.range 64).map fun w => match A27_list.idxOf? w with
          | some idx => (rep27_vecs.getD r.val []).getD idx 0 | none => 0).getD v 0
      have hinvA : ∀ u ∈ us, u < 64 ∧ ∀ v < 64, (v != 0 && Q3_form 9 v == 0) = true →
          (transv3_pt u v != 0 && Q3_form 9 (transv3_pt u v) == 0) = true := by
        intro u hu
        have hu1 := hgu.2 u hu
        refine ⟨hu1.1, fun v hv hAv => ?_⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hAv ⊢
        let uF : Fin 64 := ⟨u, hu1.1⟩; let vF : Fin 64 := ⟨v, hv⟩
        have hqU : quadForm c0_09 (dec3 uF) = 1 := by simp only [c0_09, quadForm_dec3, uF, hu1.2]; rfl
        have hqV : quadForm c0_09 (dec3 vF) = 0 := by simp only [c0_09, quadForm_dec3, vF, hAv.2]; rfl
        have hqTV : quadForm c0_09 (transvPt (dec3 uF) (dec3 vF)) = 0 := by
          rw [quadForm_transvPt_fix hqU, hqV]
        rw [transvPt_dec3] at hqTV
        have htv_nz : transv3_pt u v ≠ 0 := by
          intro h0
          have ht0 : transvPt (dec3 uF) (dec3 vF) = 0 := by
            rw [transvPt_dec3]; change dec3 ⟨transv3_pt u v, _⟩ = 0
            rw [show (⟨transv3_pt u v, transv3_pt_lt uF vF⟩ : Fin 64) = 0 from Fin.ext h0, dec3_zero]
          have hv0 : dec3 vF = 0 := by rw [← transvPt_invol (dec3 uF) (dec3 vF), ht0, transvPt_zero]
          have h0e : enc3 0 = 0 := by rw [← dec3_zero, enc3_dec3]
          apply hAv.1; have := congr_arg (fun w => (enc3 w).val) hv0; rw [enc3_dec3, h0e] at this; exact this
        have htv_Q : Q3_form 9 (transv3_pt u v) = 0 := by
          rw [c0_09, quadForm_dec3] at hqTV
          have hlt := Q3_form_lt2 9 (transv3_pt u v)
          generalize Q3_form 9 (transv3_pt u v) = m at hlt hqTV ⊢; interval_cases m; rfl; exact absurd hqTV (by decide)
        exact ⟨htv_nz, htv_Q⟩
      have hagA : ∀ v : Fin 64, (v.val != 0 && Q3_form 9 v.val == 0) = true → sAInit v.val = s3 (dec3 v) := by
        intro v hv
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hv
        obtain ⟨ia, hia⟩ := A27_val_surj v hv.1 hv.2
        have hpt : A27_pt ia = v := Fin.ext hia
        rw [← hpt, hA27 ia]
        dsimp only [sAInit]; rw [dpll_getD_map_range 64 _ 0 (A27_pt ia).isLt]
        dsimp only [A27_pt]; rw [A27_idxOf_val ia]; rfl
      have hpa := A27_val_props a
      have hw := applyWord3Nat_eq_on_inv (fun v => v != 0 && Q3_form 9 v == 0) us hinvA sAInit s3 hagA
        (A27_pt a) (by simp [A27_pt, hpa.1, hpa.2.2])
      have hg_eq := applyGauge3Nat_eq ⟨g, hg⟩ (applyWord3Nat us sAInit) (applyTransvWord (word3FromNat us) s3)
        (A27_pt a) hw
      have hfix := dpll_all_range hA_fix_b a.isLt
      simp only [beq_iff_eq] at hfix
      rw [← hg_eq]; exact hfix
    · intro i hi hsrc
      let p0F := B36_pt ⟨o12.getD i.val 0, hi⟩
      let srcF := B36_pt ⟨o12.getD (p12.getD i.val 0) 0, hsrc⟩
      have hrec := hp12_rec i hi hsrc
      dsimp only at hrec
      have hfold := applyTransvWord_eq_reverse_foldl (word3FromNat us) s3 (dec3 p0F) 1
      rw [one_mul] at hfold
      have hrev_map : (word3FromNat us).reverse = word3FromNat us.reverse := by
        simp [word3FromNat, List.map_reverse]
      rw [hrev_map] at hfold
      have hre := hrev_eq us.reverse p0F 1 hus_rev_lt
      dsimp only at hfold hre
      rw [hre.1, hre.2] at hfold
      have hpt_eq : (⟨(us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1))
          (p0F.val, (1 : ℤ))).1, hrev_lt us.reverse p0F 1 hus_rev_lt⟩ : Fin 64) = srcF :=
        Fin.ext hrec.1
      rw [hpt_eq] at hfold
      rw [flipB36_on_B36 neg _ (B36_pt_quadForm ⟨o12.getD i.val 0, hi⟩)]
      simp only [applyGauge, sympSign, symp_dec3]
      have hsp_eq : (if ((symp3 g p0F.val : Nat) : ZMod 2) = 0 then (1 : ℤ) else -1) =
          (if symp3 g p0F.val == 0 then 1 else -1) := by
        have hlt := symp3_lt2 g p0F.val
        generalize symp3 g p0F.val = m at hlt ⊢; interval_cases m <;> decide
      rw [hsp_eq, hfold]
      have hmul : (if neg then (-1 : ℤ) else 1) *
          ((if symp3 g p0F.val == 0 then (1 : ℤ) else -1) *
            ((us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1))
              (p0F.val, (1 : ℤ))).2 * s3 (dec3 srcF))) =
          ((if neg then (-1 : ℤ) else 1) *
            (us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1))
              (p0F.val, (1 : ℤ))).2 * (if symp3 g p0F.val == 0 then (1 : ℤ) else -1)) *
          s3 (dec3 srcF) := by ring
      rw [hmul, hrec.2]

/-- **Master Parts 2a & 2b Theorem (`orbit_dpll_hits_sp42`)**:
    Covers BOTH Orbit 2 (`f₂₇ = 13`, 0 `O` leaves → contradiction) and Orbit 1 (`f₂₇ = 12`, 12 `O` leaves → `sp42Certs`). -/
theorem orbit_dpll_hits_sp42 (r : Fin 3) (hr : r.val = 1 ∨ r.val = 2)
    (o12 : List Nat) (stab : List (Bool × Nat × List Nat))
    (allPats : List Nat) (trees : List (Nat × Tree36))
    (hstab : checkStabCovers r.val o12 stab allPats = true)
    (htrees : checkPatList (if r.val = 1 then orb1_tables else orb2_tables) o12 trees = true)
    (hcov : (allPats.all fun p => (trees.map Prod.fst).contains p) = true)
    {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val r a.val)
    (hfA : frustPairs (nzPts 3) s3 ≤ 92 * 6)
    (hmin : isMinQminus09 s3) :
    ∃ (spId : Fin 42) (us : List (PauliIdx 3)),
      w5FrustEq (applyTransvWord us s3) (listToSign3 (sp42Certs spId).s64) := by
  let f27 := if r.val = 1 then 12 else 13
  let tbl := mkOrb36Tables r.val f27
  have htbl_eq : (if r.val = 1 then orb1_tables else orb2_tables) = tbl := by
    rcases hr with hr1 | hr2
    · simp only [tbl, f27, hr1, ↓reduceIte]; exact orb1_tables_eq
    · simp only [tbl, f27, hr2, show ¬(2 = 1) by decide, ↓reduceIte]; exact orb2_tables_eq
  rw [htbl_eq] at htrees
  have hdeg : ∀ u < 36, pop36 (tbl.pAdj.getD u 0 ||| tbl.nAdj.getD u 0) = 15 := by
    intro u hu
    rcases hr with hr1 | hr2
    · have : tbl = orb1_tables := by simp only [tbl, f27, hr1, ↓reduceIte]; exact orb1_tables_eq.symm
      rw [this]; exact (coreTables_spec.2.2.2.2.2.2 u hu).1
    · have : tbl = orb2_tables := by simp only [tbl, f27, hr2, show ¬(2 = 1) by decide, ↓reduceIte]; exact orb2_tables_eq.symm
      rw [this]; exact (coreTables_spec.2.2.2.2.2.2 u hu).2.2.1
  -- Unpack `checkStabCovers`
  unfold checkStabCovers at hstab
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hstab
  rcases hstab with ⟨⟨⟨ho12_len, ho12_lt⟩, _⟩, hcoll⟩
  cases hacts : checkStabCovers.collectActs r.val o12 stab [] with
  | none => rw [hacts] at hcoll; simp at hcoll
  | some acts =>
    rw [hacts] at hcoll
    have hacts_sound : ∀ (es : List (Bool × Nat × List Nat)) (acc res : List (List Nat × Nat)),
        (∀ a ∈ acc, ∃ e ∈ stab, stabActionO12 r.val o12 e = some a) →
        (∀ e ∈ es, e ∈ stab) →
        checkStabCovers.collectActs r.val o12 es acc = some res →
        ∀ a ∈ res, ∃ e ∈ stab, stabActionO12 r.val o12 e = some a := by
      intro es
      induction es with
      | nil => intro acc res hacc _ h; simp only [checkStabCovers.collectActs, Option.some.injEq] at h; subst h; exact hacc
      | cons e es ih =>
        intro acc res hacc hes h
        unfold checkStabCovers.collectActs at h
        cases h1 : stabActionO12 r.val o12 e with
        | none => rw [h1] at h; simp at h
        | some a =>
          rw [h1] at h
          refine ih (a :: acc) res ?_ (fun x hx => hes x (List.mem_cons_of_mem e hx)) h
          intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨e, hes e (List.mem_cons_self ..), h1⟩
          · exact hacc x hx'
    have hact_mem := hacts_sound stab [] acts (fun _ h => by simp at h) (fun _ h => h) hacts
    -- Read the 12-bit pattern `m0 < 4096` of `s3` on `o12`!
    have ho12_getD_lt : ∀ i : Fin 12, o12.getD i.val 0 < 36 := fun i => by
      have hi : i.val < o12.length := by omega
      rw [dpll_getD_eq_getElem _ _ hi]; exact ho12_lt _ (List.getElem_mem hi)
    let m0 : Nat := (List.range 12).foldl (fun m i =>
      if h : i < 12 then
        if s3 (dec3 (B36_pt ⟨o12.getD i 0, ho12_getD_lt ⟨i, h⟩⟩)) = -1 then m ||| (1 <<< i) else m
      else m) 0
    have hm0_lt : m0 < 4096 := by
      have hgen : ∀ n ≤ 12, (List.range n).foldl (fun m i =>
          if h : i < 12 then
            if s3 (dec3 (B36_pt ⟨o12.getD i 0, ho12_getD_lt ⟨i, h⟩⟩)) = -1 then m ||| (1 <<< i) else m
          else m) 0 < 2 ^ n := by
        intro n hn
        induction n with
        | zero => simp
        | succ n ih =>
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hprev := ih (by omega)
          have h1 : 1 <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, one_mul]
          split_ifs
          · rw [h1]
            exact Nat.or_lt_two_pow (lt_trans hprev (Nat.pow_lt_pow_right (by omega) (by omega)))
              (Nat.pow_lt_pow_right (by omega) (by omega))
          · exact lt_trans hprev (Nat.pow_lt_pow_right (by omega) (by omega))
          · exact lt_trans hprev (Nat.pow_lt_pow_right (by omega) (by omega))
      exact hgen 12 le_rfl
    have hm0_tb : ∀ j : Fin 12, m0.testBit j.val = true ↔
        s3 (dec3 (B36_pt ⟨o12.getD j.val 0, ho12_getD_lt j⟩)) = -1 := by
      intro j
      let f : Nat → Bool := fun i =>
        if h : i < 12 then decide (s3 (dec3 (B36_pt ⟨o12.getD i 0, ho12_getD_lt ⟨i, h⟩⟩)) = -1) else false
      have heq_f : m0 = (List.range 12).foldl (fun m i => if f i then m ||| (1 <<< i) else m) 0 := by
        dsimp only [m0, f]; congr 1; funext m i; split_ifs <;> simp_all
      rw [heq_f, foldl_or_bit_testBit]
      simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, hfw, rfl⟩; simp only [f, hw, ↓reduceDIte, decide_eq_true_eq] at hfw; exact hfw
      · intro h; exact ⟨j.val, j.isLt, by simp only [f, j.isLt, ↓reduceDIte, decide_eq_true_eq]; exact h, rfl⟩
    -- Since `cov == 2^4096 - 1`, `cov.testBit m0 = true`, so some `(pat, (p12, s12))` hits `m0`!
    have hcov_eq : allPats.foldl (fun c pat =>
        acts.foldl (fun c' (p12, s12) => Nat.lor c' (Nat.shiftLeft 1 (preimgO12 p12 s12 pat))) c) 0 =
        Nat.sub (Nat.shiftLeft 1 4096) 1 := Nat.eq_of_beq_eq_true hcoll
    have hcov_tb : (allPats.foldl (fun c pat =>
        acts.foldl (fun c' (p12, s12) => Nat.lor c' (Nat.shiftLeft 1 (preimgO12 p12 s12 pat))) c) 0).testBit m0 = true := by
      rw [hcov_eq]
      have h1 : Nat.sub (Nat.shiftLeft 1 4096) 1 = 2 ^ 4096 - 1 := by
        change (1 <<< 4096) - 1 = _; rw [Nat.shiftLeft_eq, one_mul]
      rw [h1, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hm0_lt
    have hfind_pat : ∀ (ps : List Nat) (c0 : Nat),
        (ps.foldl (fun c pat => acts.foldl (fun c' (p12, s12) => Nat.lor c' (Nat.shiftLeft 1 (preimgO12 p12 s12 pat))) c) c0).testBit m0 = true →
        c0.testBit m0 = true ∨ ∃ pat ∈ ps, ∃ a ∈ acts, preimgO12 a.1 a.2 pat = m0 := by
      intro ps
      induction ps with
      | nil => intro c0 h; exact Or.inl h
      | cons p ps ih =>
        intro c0 h
        simp only [List.foldl_cons] at h
        rcases ih _ h with h1 | ⟨pat, hp, a, ha, heq⟩
        · have hinner : ∀ (as : List (List Nat × Nat)) (c1 : Nat),
              (as.foldl (fun c' (p12, s12) => Nat.lor c' (Nat.shiftLeft 1 (preimgO12 p12 s12 p))) c1).testBit m0 = true →
              c1.testBit m0 = true ∨ ∃ a ∈ as, preimgO12 a.1 a.2 p = m0 := by
            intro as
            induction as with
            | nil => intro c1 hc; exact Or.inl hc
            | cons a as iha =>
              intro c1 hc
              simp only [List.foldl_cons] at hc
              rcases iha _ hc with h2 | ⟨b, hb, hbeq⟩
              · change (c1 ||| (1 <<< preimgO12 a.1 a.2 p)).testBit m0 = true at h2
                rw [testBit_bitOr_single, Bool.or_eq_true, decide_eq_true_eq] at h2
                rcases h2 with h2 | h2
                · exact Or.inl h2
                · exact Or.inr ⟨a, List.mem_cons_self .., h2.symm⟩
              · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, hbeq⟩
          rcases hinner acts c0 h1 with hc0 | ⟨a, ha, heq⟩
          · exact Or.inl hc0
          · exact Or.inr ⟨p, List.mem_cons_self .., a, ha, heq⟩
        · exact Or.inr ⟨pat, List.mem_cons_of_mem p hp, a, ha, heq⟩
    rcases hfind_pat allPats 0 hcov_tb with h0 | ⟨pat, hpat_mem, ⟨p12, s12⟩, hact_in, hpre_eq⟩
    · simp at h0
    · obtain ⟨⟨neg, g, us⟩, _, hstab_act⟩ := hact_mem (p12, s12) hact_in
      obtain ⟨hg, hus_props, hp12_len, hp12_lt, hp12_inj, hact_sem⟩ :=
        sound_stabActionO12 r o12 ho12_len ho12_lt (neg, g, us) p12 s12 hstab_act
      let s3' := flipB36 neg (applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3))
      obtain ⟨hA27', hact_o12⟩ := hact_sem hg hA27
      have hus_Q : ∀ u ∈ word3FromNat us, quadForm c0_09 u = 1 := by
        intro u hu; rcases List.mem_map.mp hu with ⟨un, hun, rfl⟩
        have h := hus_props un hun
        simp only [c0_09, quadForm_dec3, Nat.mod_eq_of_lt h.1, h.2]; rfl
      have hfeq_s3' : w5FrustEq s3' (applyTransvWord (word3FromNat us) s3) :=
        w5FrustEq_trans (w5FrustEq_flipB36 neg _) (w5FrustEq_applyGauge _ _)
      have hs3' : IsSignAssign s3' :=
        flipB36_isSignAssign neg (applyGauge_isSignAssign _ (applyTransvWord_isSignAssign _ hs3))
      have hfA' : frustPairs (nzPts 3) s3' ≤ 92 * 6 := by
        rw [frustPairs_of_w5FrustEq (by simp [nzPts]) hfeq_s3', frustPairs_nzPts_applyTransvWord]
        exact hfA
      have hmin' : isMinQminus09 s3' :=
        isMinQminus09_of_w5FrustEq (w5FrustEq_symm hfeq_s3')
          (isMinQminus09_applyTransvWord_Ominus hus_Q hmin)
      -- Show `s3'` matches `pat` on all 12 vertices of `o12`!
      have hpre_tb : ∀ i : Fin 12,
          (preimgO12 p12 s12 pat).testBit (p12.getD i.val 0) =
            (pat.testBit i.val != s12.testBit i.val) := by
        intro i
        have hgen : ∀ n ≤ 12,
            ((List.range n).foldl (fun m j =>
              let bit := Nat.xor (Nat.land (Nat.shiftRight pat j) 1) (Nat.land (Nat.shiftRight s12 j) 1)
              if Nat.beq bit 1 then Nat.lor m (Nat.shiftLeft 1 (p12.getD j 0)) else m) 0).testBit (p12.getD i.val 0) =
            (decide (i.val < n) && (pat.testBit i.val != s12.testBit i.val)) := by
          intro n hn
          induction n with
          | zero => simp
          | succ n ih =>
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hih := ih (by omega)
            have hbit_n : Nat.beq (Nat.xor (Nat.land (Nat.shiftRight pat n) 1) (Nat.land (Nat.shiftRight s12 n) 1)) 1 =
                (pat.testBit n != s12.testBit n) := by
              change (((((pat >>> n) &&& 1) ^^^ ((s12 >>> n) &&& 1)) == 1)) = (pat.testBit n != s12.testBit n)
              rw [testBit_eq_shr_and1, testBit_eq_shr_and1]
              cases pat.testBit n <;> cases s12.testBit n <;> decide
            dsimp only; rw [hbit_n]
            by_cases hin : i.val = n
            · rw [hin]
              have hnot : ¬(n < n) := by omega
              rw [hin, decide_eq_false hnot, Bool.false_and] at hih
              have htb_lor : ∀ m k b, (Nat.lor m (Nat.shiftLeft 1 k)).testBit b = (m.testBit b || decide (b = k)) :=
                fun m k b => testBit_bitOr_single m k b
              cases hbn : (pat.testBit n != s12.testBit n)
              · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false]; exact hih
              · simp only [↓reduceIte, Bool.and_true]
                rw [htb_lor, decide_eq_true rfl, Bool.or_true, decide_eq_true (Nat.lt_succ_self n)]
            · have hp_ne : p12.getD i.val 0 ≠ p12.getD n 0 := fun h =>
                hin (congr_arg Fin.val (hp12_inj i ⟨n, by omega⟩ h))
              have htb_lor : ∀ m k b, (Nat.lor m (Nat.shiftLeft 1 k)).testBit b = (m.testBit b || decide (b = k)) :=
                fun m k b => testBit_bitOr_single m k b
              cases hbn : (pat.testBit n != s12.testBit n)
              · simp only [Bool.false_eq_true, ↓reduceIte, hih]
                have : decide (i.val < n + 1) = decide (i.val < n) := by
                  by_cases hlt : i.val < n <;> simp [hlt, show i.val < n + 1 ↔ i.val < n by omega]
                rw [this]
              · simp only [↓reduceIte]
                rw [htb_lor, decide_eq_false hp_ne, Bool.or_false, hih]
                have : decide (i.val < n + 1) = decide (i.val < n) := by
                  by_cases hlt : i.val < n <;> simp [hlt, show i.val < n + 1 ↔ i.val < n by omega]
                rw [this]
        have h12 := hgen 12 le_rfl
        simpa [preimgO12, i.isLt] using h12
      have hs3'_pat : ∀ i : Fin 12, ∀ hu : o12.getD i.val 0 < 36,
          s3' (dec3 (B36_pt ⟨o12.getD i.val 0, hu⟩)) = if pat.testBit i.val = true then -1 else 1 := by
        intro i hu
        let j : Fin 12 := ⟨p12.getD i.val 0, hp12_lt i⟩
        have hsrc_lt : o12.getD j.val 0 < 36 := ho12_getD_lt j
        have hact_i := hact_o12 i hu hsrc_lt
        have htb_j : m0.testBit j.val = (pat.testBit i.val != s12.testBit i.val) := by
          rw [← hpre_eq]; exact hpre_tb i
        have hsj_pm : s3 (dec3 (B36_pt ⟨o12.getD j.val 0, hsrc_lt⟩)) = 1 ∨
            s3 (dec3 (B36_pt ⟨o12.getD j.val 0, hsrc_lt⟩)) = -1 :=
          hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz _)).1
        have hsj_eq : s3 (dec3 (B36_pt ⟨o12.getD j.val 0, hsrc_lt⟩)) =
            if (pat.testBit i.val != s12.testBit i.val) = true then -1 else 1 := by
          by_cases h1 : (pat.testBit i.val != s12.testBit i.val) = true
          · rw [if_pos h1]; exact (hm0_tb j).mp (htb_j.trans h1)
          · rw [if_neg h1]
            rcases hsj_pm with hp | hn
            · exact hp
            · exact absurd ((hm0_tb j).mpr hn) (by rw [htb_j]; exact h1)
        dsimp only [s3']; rw [hact_i, hsj_eq]
        cases pat.testBit i.val <;> cases s12.testBit i.val <;> decide
      -- Look up `(pat, tree) ∈ trees` and invoke `sound_checkTree36`!
      have hmem_fst : pat ∈ trees.map Prod.fst := by
        have h := List.all_eq_true.mp hcov pat hpat_mem
        simpa [List.contains_eq_mem] using h
      obtain ⟨⟨p', tree⟩, hpt_mem, hp'_eq⟩ := List.mem_map.mp hmem_fst
      dsimp only at hp'_eq; rw [hp'_eq] at hpt_mem
      obtain ⟨hinit_ok, htree_ok⟩ := checkPatList_mem htrees hpt_mem
      have hinv := sound_initPatSimd r f27 hdeg o12 pat hs3'_pat hinit_ok
      obtain ⟨spId, us2, hfeq2⟩ :=
        sound_checkTree36 r hr tree _ _ _ _ _ hs3' hA27' hfA' hmin' hinv htree_ok
      refine ⟨spId, word3FromNat us ++ us2, ?_⟩
      rw [applyTransvWord_append]
      exact w5FrustEq_trans (w5FrustEq_applyTransvWord us2 (w5FrustEq_symm hfeq_s3')) hfeq2

end FourQubitCD

end MultiQubitMUB

