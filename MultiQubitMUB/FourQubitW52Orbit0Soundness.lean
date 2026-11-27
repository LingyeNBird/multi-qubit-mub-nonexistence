import MultiQubitMUB.FourQubitW52Orbit0
import MultiQubitMUB.FourQubitW52DPLLSoundness

set_option linter.constructorNameAsVariable false

/-!
# Soundness of Part 2c: Zero-Search Spectral & Structural Classification of Orbit 0 (`f₂₇ = 9`)

Proves `orbit0_hits_sp42`: every 3-qubit sign assignment `s3` matching `rep27[0]` on `A₂₇` with
`frustPairs (nzPts 3) s3 ≤ 92 * 6` maps under a 3-qubit transvection word into one of the 42
certified `Sp(6,2)` orbits `sp42Certs`.
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Unpacking the 5 Pure-Kernel `by rfl` Verifications -/

private lemma orb0_M0_eq_M36 (i j : Nat) : orb0_M0 i j = M36_val 0 i j := by
  unfold orb0_M0 M36_val; rfl

private lemma orb0_Mt_fast_eq (i j : Fin 36) : orb0_Mt_fast i.val j.val = orb0_Mt i.val j.val := by
  unfold orb0_Mt_fast
  rw [orb0_Mt_rows_eq, dpll_getD_map_range 36 _ [] i.isLt, dpll_getD_map_range 36 _ 0 j.isLt]

private lemma foldl_sum_range_int (n : Nat) (f : Nat → ℤ) (a : ℤ) :
    (List.range n).foldl (fun acc k => acc + f k) a = a + ∑ k : Fin n, f k.val := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Fin.sum_univ_castSucc]
    dsimp; ring

private lemma orb0_spectral_spec :
    (∀ i j : Fin 36, ∑ k : Fin 36, orb0_R i.val k.val * orb0_R k.val j.val = 36 * orb0_R i.val j.val) ∧
    (∀ i j : Fin 36, orb0_M0 i.val j.val = orb0_M0 j.val i.val) ∧
    (∀ h : Fin 3, ∀ i : Fin 36, orb0_u h.val i.val = 1 ∨ orb0_u h.val i.val = -1) ∧
    (∀ i : Fin 36,
      ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = 1).card = 12 ∧
      ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = -1).card = 3) := by
  have h := checkOrb0Spectral_ok
  unfold checkOrb0Spectral at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hR, hu⟩, hdeg⟩, _⟩
  have hu_pm : ∀ h : Fin 3, ∀ i : Fin 36, orb0_u h.val i.val = 1 ∨ orb0_u h.val i.val = -1 := fun hh i => by
    have hhi := dpll_all_range (dpll_all_range hu hh.isLt) i.isLt
    simp only [Bool.or_eq_true, beq_iff_eq] at hhi; exact hhi
  have hu0_sq : ∀ i : Fin 36, orb0_u0 i.val * orb0_u0 i.val = 1 := fun i => by
    rcases hu_pm ⟨0, by decide⟩ i with h1 | h1 <;> simp [orb0_u0, h1]
  have hgetM0 : ∀ i j : Fin 36,
      (((List.range 36).map fun i => (List.range 36).map fun j =>
        orb0_Mt_fast i j * orb0_u0 i * orb0_u0 j).getD i.val []).getD j.val 0 =
        orb0_M0 i.val j.val := fun i j => by
    rw [dpll_getD_map_range 36 _ [] i.isLt, dpll_getD_map_range 36 _ 0 j.isLt, orb0_Mt_fast_eq i j, orb0_Mt]
    calc orb0_M0 i.val j.val * orb0_u0 i.val * orb0_u0 j.val * orb0_u0 i.val * orb0_u0 j.val
        = orb0_M0 i.val j.val * (orb0_u0 i.val * orb0_u0 i.val) * (orb0_u0 j.val * orb0_u0 j.val) := by ring
      _ = orb0_M0 i.val j.val := by rw [hu0_sq i, hu0_sq j]; ring
  have hgetR : ∀ i j : Fin 36,
      (((List.range 36).map fun i => (List.range 36).map fun j =>
        (if i == j then (18 : ℤ) else 0) - 6 *
          (((List.range 36).map fun i => (List.range 36).map fun j =>
            orb0_Mt_fast i j * orb0_u0 i * orb0_u0 j).getD i []).getD j 0 +
          orb0_u 0 i * orb0_u 0 j + orb0_u 1 i * orb0_u 1 j + orb0_u 2 i * orb0_u 2 j).getD i.val []).getD j.val 0 =
        orb0_R i.val j.val := fun i j => by
    rw [dpll_getD_map_range 36 _ [] i.isLt, dpll_getD_map_range 36 _ 0 j.isLt, hgetM0 i j]
    rfl
  refine ⟨fun i j => ?_, fun i j => ?_, hu_pm, fun i => ?_⟩
  · have hij := dpll_all_range (dpll_all_range hR i.isLt) j.isLt
    simp only [Bool.and_eq_true] at hij
    have hd := beq_iff_eq.mp hij.1.1.1
    rw [foldl_sum_range_int, zero_add, hgetR i j] at hd
    rw [← hd]
    exact Finset.sum_congr rfl fun k _ => by rw [hgetR i k, hgetR k j]
  · have hij := dpll_all_range (dpll_all_range hR i.isLt) j.isLt
    simp only [Bool.and_eq_true] at hij
    have hsym := beq_iff_eq.mp hij.1.1.2
    rw [hgetM0 i j, hgetM0 j i] at hsym; exact hsym
  · have hi := dpll_all_range hdeg i.isLt
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    rw [dpll_list_range_filter_len, dpll_list_range_filter_len] at hi
    constructor
    · rw [← hi.1]; exact congr_arg Finset.card (Finset.ext fun j => by simp [orb0_Mt_fast_eq i j])
    · rw [← hi.2]; exact congr_arg Finset.card (Finset.ext fun j => by simp [orb0_Mt_fast_eq i j])

private lemma orb0_R_symm (i j : Fin 36) : orb0_R i.val j.val = orb0_R j.val i.val := by
  unfold orb0_R
  rw [orb0_spectral_spec.2.1 i j]
  by_cases hij : i.val = j.val
  · simp [hij]
  · simp [beq_false_of_ne hij, beq_false_of_ne (Ne.symm hij)]; ring

private lemma orb0_Mt_symm (i j : Fin 36) : orb0_Mt i.val j.val = orb0_Mt j.val i.val := by
  unfold orb0_Mt; rw [orb0_spectral_spec.2.1 i j]; ring

private lemma orb0_Mt_cases (i j : Fin 36) :
    orb0_Mt i.val j.val = 0 ∨ orb0_Mt i.val j.val = 1 ∨ orb0_Mt i.val j.val = -1 := by
  unfold orb0_Mt; rw [orb0_M0_eq_M36]
  rcases (M36_val_spec ⟨0, by decide⟩ i j).1 with h | h | h <;>
  rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hi | hi <;>
  rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ j with hj | hj <;>
  simp [orb0_u0, h, hi, hj]

private lemma orb0_u0_sq (i : Fin 36) : orb0_u0 i.val * orb0_u0 i.val = 1 := by
  rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with h | h <;> simp [orb0_u0, h]

private lemma orb0_blocks_spec :
    (∀ i : Fin 36, orb0_blk.getD i.val 99 < 4 ∧ orb0_col3.getD i.val 99 < 3) ∧
    (∀ b : Fin 4, ((Finset.univ : Finset (Fin 36)).filter fun i => orb0_blk.getD i.val 99 = b.val).card = 9) ∧
    (∀ i j : Fin 36, orb0_Mt i.val j.val = 1 →
      (orb0_blk.getD i.val 99 = orb0_blk.getD j.val 99 → orb0_col3.getD i.val 99 ≠ orb0_col3.getD j.val 99) ∧
      ¬((orb0_blk.getD i.val 99 = 0 ∧ orb0_blk.getD j.val 99 = 1) ∨
        (orb0_blk.getD i.val 99 = 1 ∧ orb0_blk.getD j.val 99 = 0) ∨
        (orb0_blk.getD i.val 99 = 2 ∧ orb0_blk.getD j.val 99 = 3) ∨
        (orb0_blk.getD i.val 99 = 3 ∧ orb0_blk.getD j.val 99 = 2))) ∧
    (∀ p ∈ ([(0, 2), (0, 3), (1, 2), (1, 3)] : List (Nat × Nat)),
      let Ba := (Finset.univ : Finset (Fin 36)).filter fun i => orb0_blk.getD i.val 99 = p.1
      let Bb := (Finset.univ : Finset (Fin 36)).filter fun i => orb0_blk.getD i.val 99 = p.2
      (∀ u ∈ Ba, (Bb.filter fun v => orb0_Mt u.val v.val = 1).card ≤ 3) ∧
      (∀ v ∈ Bb, (Ba.filter fun u => orb0_Mt u.val v.val = 1).card ≤ 3) ∧
      (∀ u1 ∈ Ba, ∀ u2 ∈ Ba, u1.val < u2.val →
        (Bb.filter fun v => orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1).card ≤ 1) ∧
      (∀ v1 ∈ Bb, ∀ v2 ∈ Bb, v1.val < v2.val →
        (Ba.filter fun u => orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1).card ≤ 1)) ∧
    (∀ s0 s1 s2 s3 : Nat, s0 < 10 → s1 < 10 → s2 < 10 → s3 < 10 →
      6 ≤ s0 + s1 + s2 + s3 → s0 + s1 + s2 + s3 ≤ 10 →
      9 * (s0 + s1 + s2 + s3) - 29 ≤
        (2 * s0 * s0) / 3 + (2 * s1 * s1) / 3 + (2 * s2 * s2) / 3 + (2 * s3 * s3) / 3 +
        2 * (bipBnd s0 s2 + bipBnd s0 s3 + bipBnd s1 s2 + bipBnd s1 s3) →
      (s0 = 9 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 0) ∨
      (s0 = 0 ∧ s1 = 9 ∧ s2 = 0 ∧ s3 = 0) ∨
      (s0 = 0 ∧ s1 = 0 ∧ s2 = 9 ∧ s3 = 0) ∨
      (s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ s3 = 9)) := by
  have h := checkOrb0Blocks_ok
  unfold checkOrb0Blocks at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  have hlen_filter_blk : ∀ (b : Nat) (q : Nat → Bool),
      (((List.range 36).filter fun i => orb0_blk.getD i 99 == b).filter q).length =
      (((Finset.univ : Finset (Fin 36)).filter fun i => orb0_blk.getD i.val 99 = b).filter fun i => q i.val = true).card := by
    intro b q
    rw [List.filter_filter, dpll_list_range_filter_len, Finset.filter_filter]
    exact congr_arg Finset.card (Finset.ext fun i => by simp [and_comm])
  refine ⟨fun i => ?_, fun b => ?_, fun i j hmt => ?_, fun p hp => ?_, fun s0 s1 s2 s3 hs0 hs1 hs2 hs3 hlo hhi hub => ?_⟩
  · have hi := dpll_all_range h1 i.isLt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi; exact hi
  · have hb := dpll_all_range h2 b.isLt
    simp only [beq_iff_eq, dpll_list_range_filter_len] at hb
    exact hb
  · have hij := dpll_all_range (dpll_all_range h3 i.isLt) j.isLt
    rw [orb0_Mt_fast_eq i j, hmt] at hij
    simp only [beq_self_eq_true, ↓reduceIte] at hij
    constructor
    · intro hbeq; simp only [hbeq, beq_self_eq_true, ↓reduceIte] at hij; exact bne_iff_ne.mp hij
    · intro hbad
      have hne : orb0_blk.getD i.val 99 ≠ orb0_blk.getD j.val 99 := by rcases hbad with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
      simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hij
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hij
      rcases hbad with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · rcases hij.1.1.1 with h' | h' <;> exact h' (by assumption)
      · rcases hij.1.1.2 with h' | h' <;> exact h' (by assumption)
      · rcases hij.1.2 with h' | h' <;> exact h' (by assumption)
      · rcases hij.2 with h' | h' <;> exact h' (by assumption)
  · have hpp := List.all_eq_true.mp h4 p hp
    rcases p with ⟨a, b⟩
    dsimp only at hpp ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range, beq_iff_eq] at hpp
    rcases hpp with ⟨⟨⟨ha3, hb3⟩, hac4⟩, hbc4⟩
    refine ⟨fun u hu => ?_, fun v hv => ?_, fun u1 hu1 u2 hu2 hlt => ?_, fun v1 hv1 v2 hv2 hlt => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have h1 := decide_eq_true_eq.mp (ha3 u.val ⟨u.isLt, hu⟩)
      rw [hlen_filter_blk] at h1
      refine le_trans (le_of_eq ?_) h1
      exact congr_arg Finset.card (Finset.ext fun v => by simp [orb0_Mt_fast_eq u v])
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have h1 := decide_eq_true_eq.mp (hb3 v.val ⟨v.isLt, hv⟩)
      rw [hlen_filter_blk] at h1
      refine le_trans (le_of_eq ?_) h1
      exact congr_arg Finset.card (Finset.ext fun u => by simp [orb0_Mt_fast_eq u v])
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
      have h1 := hac4 u1.val ⟨u1.isLt, hu1⟩ u2.val ⟨u2.isLt, hu2⟩
      rw [if_pos hlt, decide_eq_true_eq, hlen_filter_blk] at h1
      refine le_trans (le_of_eq ?_) h1
      exact congr_arg Finset.card (Finset.ext fun v => by simp [orb0_Mt_fast_eq u1 v, orb0_Mt_fast_eq u2 v])
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      have h1 := hbc4 v1.val ⟨v1.isLt, hv1⟩ v2.val ⟨v2.isLt, hv2⟩
      rw [if_pos hlt, decide_eq_true_eq, hlen_filter_blk] at h1
      refine le_trans (le_of_eq ?_) h1
      exact congr_arg Finset.card (Finset.ext fun u => by simp [orb0_Mt_fast_eq u v1, orb0_Mt_fast_eq u v2])
  · have hq := dpll_all_range (dpll_all_range (dpll_all_range (dpll_all_range h5 hs0) hs1) hs2) hs3
    rw [if_pos (by simp [hlo, hhi]), if_pos hub] at hq
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hq
    rcases hq with ((⟨⟨⟨a, b⟩, c⟩, d⟩ | ⟨⟨⟨a, b⟩, c⟩, d⟩) | ⟨⟨⟨a, b⟩, c⟩, d⟩) | ⟨⟨⟨a, b⟩, c⟩, d⟩
    · exact Or.inl ⟨a, b, c, d⟩
    · exact Or.inr (Or.inl ⟨a, b, c, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, d⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, d⟩))

/-! ### Section 2: `orb0_actionB36` Soundness & `Mt`-Edge Preservation -/

set_option maxHeartbeats 800000 in
private lemma sound_orb0_actionB36 {g : Nat} {us : List Nat} {perm : List Nat} {sgn : List ℤ}
    (hact : orb0_actionB36 g us = some (perm, sgn)) :
    g < 64 ∧ (∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1) ∧
    perm.length = 36 ∧ sgn.length = 36 ∧
    (∀ i : Fin 36, perm.getD i.val 0 < 36) ∧
    (∀ i j : Fin 36, perm.getD i.val 0 = perm.getD j.val 0 → i = j) ∧
    ∀ {s3 : PauliIdx 3 → ℤ} (hg : g < 64),
      (∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
      let s3' := applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3)
      (∀ a : Fin 27, s3' (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
      (∀ i : Fin 36, ∀ hp : perm.getD i.val 0 < 36,
        s3' (dec3 (B36_pt i)) = sgn.getD i.val 0 * s3 (dec3 (B36_pt ⟨perm.getD i.val 0, hp⟩))) := by
  unfold orb0_actionB36 at hact
  dsimp only at hact
  have hgu_b : (decide (g < 64) && us.all fun u => decide (u < 64) && (Q3_form 9 u == 1)) = true := by
    cases h' : (decide (g < 64) && us.all fun u => decide (u < 64) && (Q3_form 9 u == 1))
    · rw [h'] at hact; simp at hact
    · rfl
  rw [hgu_b] at hact; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hact
  rw [orb0_A27_eq] at hact
  split_ifs at hact with hbad2
  have hA_fix_b : ((List.range 27).all fun i =>
      applyGauge3Nat g (applyWord3Nat us (fun v =>
        ((List.range 64).map fun w => match A27_list.idxOf? w with
          | some idx => (rep27_vecs.getD 0 []).getD idx 0 | none => 0).getD v 0)) (A27_list.getD i 0) ==
      (rep27_vecs.getD 0 []).getD i 0) = true := by
    by_contra hne
    have hf : ((List.range 27).all fun i =>
      applyGauge3Nat g (applyWord3Nat us (fun v =>
        ((List.range 64).map fun w => match A27_list.idxOf? w with
          | some idx => (rep27_vecs.getD 0 []).getD idx 0 | none => 0).getD v 0)) (A27_list.getD i 0) ==
      (rep27_vecs.getD 0 []).getD i 0) = false := Bool.eq_false_iff.mpr hne
    exact hbad2 (by rw [Bool.not_eq_true']; exact hf)
  have hgu : g < 64 ∧ ∀ u ∈ us, u < 64 ∧ Q3_form 9 u = 1 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hgu_b
    exact hgu_b
  · have hrev_lt : ∀ (ws : List Nat) (p0 : Fin 64) (acc : ℤ), (∀ w ∈ ws, w < 64) →
        (ws.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, acc)).1 < 64 := by
      intro ws; induction ws with
      | nil => intro p0 _ _; exact p0.isLt
      | cons w ws ih =>
        intro p0 acc hws; simp only [List.foldl_cons]
        have hw := hws w (List.mem_cons_self ..)
        exact ih ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ _ (fun x hx => hws x (List.mem_cons_of_mem w hx))
    have hrev_eq : ∀ (ws : List Nat) (p0 : Fin 64) (acc : ℤ) (hws : ∀ w ∈ ws, w < 64),
        let resN := ws.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (p0.val, acc)
        let resP := (word3FromNat ws).foldl
          (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (dec3 p0, acc)
        resP.1 = dec3 ⟨resN.1, hrev_lt ws p0 acc hws⟩ ∧ resP.2 = resN.2 := by
      intro ws; induction ws with
      | nil => intro p0 acc _; exact ⟨rfl, rfl⟩
      | cons w ws ih =>
        intro p0 acc hws
        have hw := hws w (List.mem_cons_self ..)
        have hrest : ∀ x ∈ ws, x < 64 := fun x hx => hws x (List.mem_cons_of_mem w hx)
        have hpt : ∀ hlt : w % 64 < 64, transvPt (dec3 ⟨w % 64, hlt⟩) (dec3 p0) =
            dec3 ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ := fun hlt => by
          rw [show (⟨w % 64, hlt⟩ : Fin 64) = ⟨w, hw⟩ from Fin.ext (Nat.mod_eq_of_lt hw),
              transvPt_dec3]
        have hsgn : ∀ hlt : w % 64 < 64, transvSgn (dec3 ⟨w % 64, hlt⟩) (dec3 p0) = transv3_sgn w p0.val := fun hlt => by
          rw [show (⟨w % 64, hlt⟩ : Fin 64) = ⟨w, hw⟩ from Fin.ext (Nat.mod_eq_of_lt hw),
              transvSgn_dec3]
        have hpair : ∀ hlt : w % 64 < 64, (transvPt (dec3 ⟨w % 64, hlt⟩) (dec3 p0),
            acc * transvSgn (dec3 ⟨w % 64, hlt⟩) (dec3 p0)) =
            (dec3 ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩, acc * transv3_sgn w p0.val) := fun hlt =>
          Prod.ext (hpt hlt) (congr_arg (acc * ·) (hsgn hlt))
        have hih := ih ⟨transv3_pt w p0.val, transv3_pt_lt ⟨w, hw⟩ p0⟩ (acc * transv3_sgn w p0.val) hrest
        dsimp only at hih ⊢
        simp only [word3FromNat, List.map_cons, List.foldl_cons]
        rw [hpair]
        exact hih
    have hus_rev_lt : ∀ w ∈ us.reverse, w < 64 := fun w hw => (hgu.2 w (List.mem_reverse.mp hw)).1
    have hgo : ∀ k i rP rS, k + i = 36 → rP.length = i → rS.length = i →
        (∀ t : Fin 36, t.val < i → rP.reverse.getD t.val 0 < 36) →
        (∀ t : Fin 36, t.val < i →
          let res := us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (B36_val t.val, (1 : ℤ))
          res.1 = B36_val (rP.reverse.getD t.val 0) ∧
          rS.reverse.getD t.val 0 = res.2 * (if symp3 g (B36_val t.val) == 0 then 1 else -1)) →
        orb0_actionB36Go g us.reverse k rP rS = some (perm, sgn) →
        perm.length = 36 ∧ sgn.length = 36 ∧
        (∀ t : Fin 36, perm.getD t.val 0 < 36) ∧
        (∀ t : Fin 36,
          let res := us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (B36_val t.val, (1 : ℤ))
          res.1 = B36_val (perm.getD t.val 0) ∧
          sgn.getD t.val 0 = res.2 * (if symp3 g (B36_val t.val) == 0 then 1 else -1)) := by
      intro k
      induction k with
      | zero =>
        intro i rP rS hi hlp hls hlt hrec hok
        have hi36 : i = 36 := by omega
        subst hi36
        rw [orb0_actionB36Go.eq_1] at hok
        simp only [Option.some.injEq, Prod.mk.injEq] at hok
        rcases hok with ⟨rfl, rfl⟩
        exact ⟨by simp [hlp], by simp [hls], fun t => hlt t t.isLt, fun t => hrec t t.isLt⟩
      | succ k ih =>
        intro i rP rS hi hlp hls hlt hrec hok
        have hi36 : i < 36 := by omega
        have hi_eq : Nat.sub 35 k = i := by change 35 - k = i; omega
        have hunf : orb0_actionB36Go g us.reverse (k + 1) rP rS =
            let p0 := B36_val i
            let (cur, sg) := us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p0, (1 : ℤ))
            match B36_list.idxOf? cur with
            | none => none
            | some j =>
              let sgTot := sg * (if symp3 g p0 == 0 then 1 else -1)
              orb0_actionB36Go g us.reverse k (j :: rP) (sgTot :: rS) := by
          rw [orb0_actionB36Go.eq_2, hi_eq, orb0_B36_eq]; rfl
        rw [hunf] at hok; dsimp only at hok
        cases hB : B36_list.idxOf? (us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (B36_val i, (1 : ℤ))).1 with
        | none => rw [hB] at hok; simp at hok
        | some j =>
          rw [hB] at hok; dsimp only at hok
          have hj36 : j < 36 := by
            have := (List.idxOf?_eq_some_iff.mp hB).1; rwa [B36_list_len] at this
          have hcur : (us.reverse.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (B36_val i, (1 : ℤ))).1 = B36_val j := by
            have h1 := (List.idxOf?_eq_some_iff.mp hB).2.1
            symm; rw [B36_val, dpll_getD_eq_getElem _ _ (by rw [B36_list_len]; exact hj36), h1]
          have hgetP : ∀ t : Fin 36, t.val < i + 1 →
              (j :: rP).reverse.getD t.val 0 = if t.val < i then rP.reverse.getD t.val 0 else j := by
            intro t ht; simp only [List.reverse_cons]
            by_cases hti : t.val < i
            · rw [if_pos hti]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show t.val < rP.reverse.length by simp [hlp, hti])]
            · rw [if_neg hti, show t.val = i by omega]
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show rP.reverse.length ≤ i by simp [hlp]), hlp]
          have hgetS : ∀ (v : ℤ) (t : Fin 36), t.val < i + 1 →
              (v :: rS).reverse.getD t.val 0 = if t.val < i then rS.reverse.getD t.val 0 else v := by
            intro v t ht; simp only [List.reverse_cons]
            by_cases hti : t.val < i
            · rw [if_pos hti]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show t.val < rS.reverse.length by simp [hls, hti])]
            · rw [if_neg hti, show t.val = i by omega]
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show rS.reverse.length ≤ i by simp [hls]), hls]
          refine ih (i + 1) (j :: rP) _ (by omega) (by simp [hlp]) (by simp [hls]) ?_ ?_ hok
          · intro t ht; rw [hgetP t ht]; split_ifs with hti; exact hlt t hti; exact hj36
          · intro t ht; rw [hgetP t ht, hgetS _ t ht]
            by_cases hti : t.val < i
            · rw [if_pos hti, if_pos hti]; exact hrec t hti
            · have hteq : t.val = i := by omega
              rw [if_neg hti, if_neg hti, hteq]; exact ⟨hcur, rfl⟩
    obtain ⟨hplen, hslen, hplt, hprec⟩ :=
      hgo 36 0 [] [] rfl rfl rfl (fun _ h => by omega) (fun _ h => by omega) hact
    -- Injectivity of `perm`: `foldl transvPt` is a composition of involutions!
    have hfold_inj : ∀ (ws : List (PauliIdx 3)) (p q : PauliIdx 3),
        (ws.foldl (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (p, 1)).1 =
        (ws.foldl (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (q, 1)).1 →
        p = q := by
      have hfst : ∀ (ws : List (PauliIdx 3)) (p : PauliIdx 3) (a : ℤ),
          (ws.foldl (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (p, a)).1 =
          ws.foldl (fun c u => transvPt u c) p := by
        intro ws; induction ws with
        | nil => intro _ _; rfl
        | cons w ws ih => intro p a; simp only [List.foldl_cons, ih]
      intro ws p q h
      rw [hfst, hfst] at h
      induction ws generalizing p q with
      | nil => exact h
      | cons w ws ih =>
        simp only [List.foldl_cons] at h
        have h1 := ih (transvPt w p) (transvPt w q) h
        have := congr_arg (transvPt w) h1; simpa [transvPt_invol] using this
    have hpinj : ∀ i j : Fin 36, perm.getD i.val 0 = perm.getD j.val 0 → i = j := by
      intro i j hij
      have hri := hrev_eq us.reverse (B36_pt i) 1 hus_rev_lt
      have hrj := hrev_eq us.reverse (B36_pt j) 1 hus_rev_lt
      have h1 : (us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (B36_val i.val, (1 : ℤ))).1 =
          (us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1)) (B36_val j.val, (1 : ℤ))).1 := by
        rw [(hprec i).1, (hprec j).1, hij]
      have hpeq : ((word3FromNat us.reverse).foldl
          (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (dec3 (B36_pt i), 1)).1 =
          ((word3FromNat us.reverse).foldl
          (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (dec3 (B36_pt j), 1)).1 := by
        rw [hri.1, hrj.1]; congr 1; exact Fin.ext h1
      have hdec := hfold_inj (word3FromNat us.reverse) (dec3 (B36_pt i)) (dec3 (B36_pt j)) hpeq
      exact B36_val_inj (congr_arg Fin.val (equiv3.symm.injective hdec))
    refine ⟨hgu.1, hgu.2, hplen, hslen, hplt, hpinj, ?_⟩
    intro s3 hg hA27
    refine ⟨?_, ?_⟩
    · intro a
      let sAInit : Nat → ℤ := fun v =>
        ((List.range 64).map fun w => match A27_list.idxOf? w with
          | some idx => (rep27_vecs.getD 0 []).getD idx 0 | none => 0).getD v 0
      have hinvA : ∀ u ∈ us, u < 64 ∧ ∀ v < 64, (v != 0 && Q3_form 9 v == 0) = true →
          (transv3_pt u v != 0 && Q3_form 9 (transv3_pt u v) == 0) = true := by
        intro u hu; have hu1 := hgu.2 u hu
        refine ⟨hu1.1, fun v hv hAv => ?_⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hAv ⊢
        let uF : Fin 64 := ⟨u, hu1.1⟩; let vF : Fin 64 := ⟨v, hv⟩
        have hqU : quadForm c0_09 (dec3 uF) = 1 := by simp only [c0_09, quadForm_dec3, uF, hu1.2]; rfl
        have hqV : quadForm c0_09 (dec3 vF) = 0 := by simp only [c0_09, quadForm_dec3, vF, hAv.2]; rfl
        have hqTV : quadForm c0_09 (transvPt (dec3 uF) (dec3 vF)) = 0 := by rw [quadForm_transvPt_fix hqU, hqV]
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
        intro v hv; simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hv
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
    · intro i hp
      have hrec := hprec i
      have hfold := applyTransvWord_eq_reverse_foldl (word3FromNat us) s3 (dec3 (B36_pt i)) 1
      rw [one_mul] at hfold
      have hrev_map : (word3FromNat us).reverse = word3FromNat us.reverse := by simp [word3FromNat, List.map_reverse]
      rw [hrev_map] at hfold
      have hre := hrev_eq us.reverse (B36_pt i) 1 hus_rev_lt
      dsimp only at hfold hre hrec
      rw [hre.1, hre.2] at hfold
      have hpt_eq : (⟨(us.reverse.foldl (fun (cs : Nat × ℤ) u => (transv3_pt u cs.1, cs.2 * transv3_sgn u cs.1))
          ((B36_pt i).val, (1 : ℤ))).1, hrev_lt us.reverse (B36_pt i) 1 hus_rev_lt⟩ : Fin 64) =
          B36_pt ⟨perm.getD i.val 0, hp⟩ := Fin.ext hrec.1
      rw [hpt_eq] at hfold
      simp only [applyGauge, sympSign, symp_dec3]
      have hsp_eq : (if ((symp3 g (B36_pt i).val : Nat) : ZMod 2) = 0 then (1 : ℤ) else -1) =
          (if symp3 g (B36_val i.val) == 0 then 1 else -1) := by
        have hlt := symp3_lt2 g (B36_val i.val)
        change (if ((symp3 g (B36_val i.val) : Nat) : ZMod 2) = 0 then (1 : ℤ) else -1) = _
        generalize symp3 g (B36_val i.val) = m at hlt ⊢; interval_cases m <;> decide
      rw [hsp_eq, hfold, hrec.2]; dsimp only [B36_pt]; ring

/-- Any stabilizer `(g, us)` fixing `rep27[0]` on `A₂₇` and preserving `±u₀` preserves `orb0_Mt`! -/
private lemma orb0_stabU0_preserves_Mt {g : Nat} {us : List Nat} {perm : List Nat} {sgn : List ℤ}
    (hact : orb0_actionB36 g us = some (perm, sgn))
    (hpres : (∀ i : Fin 36, orb0_u0 (perm.getD i.val 0) * sgn.getD i.val 0 = orb0_u0 i.val) ∨
             (∀ i : Fin 36, orb0_u0 (perm.getD i.val 0) * sgn.getD i.val 0 = -orb0_u0 i.val)) :
    ∀ i j : Fin 36, orb0_Mt i.val j.val = orb0_Mt (perm.getD i.val 0) (perm.getD j.val 0) := by
  obtain ⟨hg, hus_props, _, _, hplt, hpinj, hsem⟩ := sound_orb0_actionB36 hact
  -- Build the concrete sign assignment `sU0` equal to `rep27[0]` on `A₂₇` and `u₀` on `B₃₆`!
  let sU0 : PauliIdx 3 → ℤ := fun p =>
    match A27_list.idxOf? (enc3 p).val with
    | some ia => (rep27_vecs.getD 0 []).getD ia 0
    | none =>
      match B36_list.idxOf? (enc3 p).val with
      | some ib => orb0_u0 ib
      | none => 0
  have hsU0_A : ∀ a : Fin 27, sU0 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val := fun a => by
    simp only [sU0, enc3_dec3, A27_pt, A27_idxOf_val a]; rfl
  have hsU0_B : ∀ i : Fin 36, sU0 (dec3 (B36_pt i)) = orb0_u0 i.val := fun i => by
    simp only [sU0, enc3_dec3, B36_pt, A27_idxOf_none_of_B36 i, B36_idxOf_val i]
  obtain ⟨hA', hB'⟩ := hsem hg hsU0_A
  -- Determine `neg` so `flipB36 neg (applyGauge g (applyTransvWord us sU0))` equals `sU0` on `A₂₇ ⊔ B₃₆`!
  have hMt_eq_frust : ∀ s : PauliIdx 3 → ℤ,
      (∀ a : Fin 27, s (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
      (∀ i : Fin 36, s (dec3 (B36_pt i)) = orb0_u0 i.val) →
      ∀ i j : Fin 36, orb0_Mt i.val j.val ≠ 0 →
        let pi := dec3 (B36_pt i); let pj := dec3 (B36_pt j)
        orb0_Mt i.val j.val = gammaSgn pi pj * s pi * s pj * s (pi + pj) := by
    intro s hA hB i j hne0
    have hM0_ne : M36_val 0 i.val j.val ≠ 0 := fun h => hne0 (by unfold orb0_Mt; rw [orb0_M0_eq_M36, h]; simp)
    have he := M36_edge_eq ⟨0, by decide⟩ hA i j hM0_ne
    dsimp only at he ⊢
    rw [← he.2.2, hB i, hB j]; unfold orb0_Mt; rw [orb0_M0_eq_M36]
  have htrans_cocycle : ∀ (u : PauliIdx 3) (s : PauliIdx 3 → ℤ) (a b : PauliIdx 3), symp a b = 0 →
      gammaSgn a b * applyTransv u s a * applyTransv u s b * applyTransv u s (a + b) =
      gammaSgn (transvPt u a) (transvPt u b) * s (transvPt u a) * s (transvPt u b) * s (transvPt u a + transvPt u b) :=
    fun u s a b hsp => line_sign_applyTransv u a b hsp s
  have hword_cocycle : ∀ (ws : List (PauliIdx 3)) (s : PauliIdx 3 → ℤ) (a b : PauliIdx 3), symp a b = 0 →
      let ta := ws.reverse.foldl (fun c u => transvPt u c) a
      let tb := ws.reverse.foldl (fun c u => transvPt u c) b
      symp ta tb = 0 ∧
      gammaSgn a b * applyTransvWord ws s a * applyTransvWord ws s b * applyTransvWord ws s (a + b) =
      gammaSgn ta tb * s ta * s tb * s (ta + tb) := by
    intro ws
    induction ws with
    | nil => intro s a b hsp; exact ⟨hsp, rfl⟩
    | cons w ws ih =>
      intro s a b hsp
      simp only [applyTransvWord, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hsp1, h1⟩ := ih (applyTransv w s) a b hsp
      refine ⟨by rw [symp_transvPt]; exact hsp1, ?_⟩
      rw [h1, htrans_cocycle w s _ _ hsp1]
  -- Track `ta` via `hact`: `us.reverse.foldl transvPt (B36 i) = B36 (perm[i])`!
  have hfold_pt : ∀ i : Fin 36,
      (word3FromNat us).reverse.foldl (fun c u => transvPt u c) (dec3 (B36_pt i)) =
        dec3 (B36_pt ⟨perm.getD i.val 0, hplt i⟩) := by
    intro i
    -- Use `hB'` with delta indicator function `fun p => if p = dec3 (B36_pt ⟨perm[i], _⟩) then 1 else 0`!
    -- Even simpler: evaluate `applyTransvWord_eq_reverse_foldl` on the indicator `fun p => if p = ... then 1 else -1`!
    let tgt := dec3 (B36_pt ⟨perm.getD i.val 0, hplt i⟩)
    have hfst : ∀ (ws : List (PauliIdx 3)) (p : PauliIdx 3) (acc : ℤ),
        (ws.foldl (fun (cs : PauliIdx 3 × ℤ) u => (transvPt u cs.1, cs.2 * transvSgn u cs.1)) (p, acc)).1 =
        ws.foldl (fun c u => transvPt u c) p := by
      intro ws; induction ws with
      | nil => intro _ _; rfl
      | cons w ws ih => intro p acc; simp only [List.foldl_cons, ih]
    let f1 : PauliIdx 3 → ℤ := fun p => if p ∈ Qminus c0_09 then sU0 p else if p = tgt then 1 else -1
    let f2 : PauliIdx 3 → ℤ := fun p => if p ∈ Qminus c0_09 then sU0 p else if p = tgt then -1 else -1
    have hf1A : ∀ a : Fin 27, f1 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val := fun a => by
      simp [f1, A27_pt_mem_Qminus a, hsU0_A a]
    have hf2A : ∀ a : Fin 27, f2 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val := fun a => by
      simp [f2, A27_pt_mem_Qminus a, hsU0_A a]
    have h1 := (hsem hg hf1A).2 i (hplt i)
    have h2 := (hsem hg hf2A).2 i (hplt i)
    have htgt_notA : tgt ∉ Qminus c0_09 := fun hm => by
      have hq0 := (Finset.mem_filter.mp hm).2
      have hq1 := B36_pt_quadForm ⟨perm.getD i.val 0, hplt i⟩
      rw [hq1] at hq0; exact absurd hq0 (by decide)
    have hsgn_ne0 : sgn.getD i.val 0 ≠ 0 := by
      intro h0; rcases hpres with hp | hn
      · have := hp i; rw [h0, mul_zero] at this
        rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with h | h <;> simp [orb0_u0, h] at this
      · have := hn i; rw [h0, mul_zero] at this
        rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with h | h <;> simp [orb0_u0, h] at this
    have hne : applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) f1) (dec3 (B36_pt i)) ≠
               applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) f2) (dec3 (B36_pt i)) := by
      rw [h1, h2]; intro heq
      change sgn.getD i.val 0 * f1 tgt = sgn.getD i.val 0 * f2 tgt at heq
      simp only [f1, f2, htgt_notA, ↓reduceIte] at heq
      have : 2 * sgn.getD i.val 0 = 0 := by linarith
      exact hsgn_ne0 (by omega)
    by_contra hneq
    apply hne
    simp only [applyGauge]
    have hl1 := applyTransvWord_eq_reverse_foldl (word3FromNat us) f1 (dec3 (B36_pt i)) 1
    have hl2 := applyTransvWord_eq_reverse_foldl (word3FromNat us) f2 (dec3 (B36_pt i)) 1
    rw [one_mul] at hl1 hl2
    rw [hl1, hl2]; dsimp only
    rw [hfst]
    have hneq' : (word3FromNat us).reverse.foldl (fun c u => transvPt u c) (dec3 (B36_pt i)) ≠ tgt := hneq
    have hff : f1 ((word3FromNat us).reverse.foldl (fun c u => transvPt u c) (dec3 (B36_pt i))) =
               f2 ((word3FromNat us).reverse.foldl (fun c u => transvPt u c) (dec3 (B36_pt i))) := by
      simp only [f1, f2, hneq', ↓reduceIte]
    rw [hff]
  -- Now compare `orb0_Mt i j` and `orb0_Mt (perm[i]) (perm[j])`!
  suffices hmain : ∀ negB : Bool,
      (∀ i : Fin 36, (if negB then (-1 : ℤ) else 1) * (sgn.getD i.val 0 * orb0_u0 (perm.getD i.val 0)) = orb0_u0 i.val) →
      ∀ i j : Fin 36, orb0_Mt i.val j.val = orb0_Mt (perm.getD i.val 0) (perm.getD j.val 0) by
    rcases hpres with hp | hn
    · exact hmain false (fun i => by simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; rw [mul_comm]; exact hp i)
    · exact hmain true (fun i => by simp only [↓reduceIte]; have := hn i; linarith)
  intro negB hnegB i j
  let sU0' := flipB36 negB (applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) sU0))
  have hsU0'_A : ∀ a : Fin 27, sU0' (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val := fun a => by
    dsimp only [sU0']; rw [flipB36_on_A27 negB _ (Finset.mem_filter.mp (A27_pt_mem_Qminus a)).2]; exact hA' a
  have hsU0'_B : ∀ i : Fin 36, sU0' (dec3 (B36_pt i)) = orb0_u0 i.val := fun i => by
    dsimp only [sU0']; rw [flipB36_on_B36 negB _ (B36_pt_quadForm i), hB' i (hplt i), hsU0_B]
    exact hnegB i
  have hfeq : w5FrustEq sU0' (applyTransvWord (word3FromNat us) sU0) :=
    w5FrustEq_trans (w5FrustEq_flipB36 negB _) (w5FrustEq_applyGauge _ _)
  let piF : Fin 36 := ⟨perm.getD i.val 0, hplt i⟩
  let pjF : Fin 36 := ⟨perm.getD j.val 0, hplt j⟩
  have hsymp_iff : symp (dec3 (B36_pt i)) (dec3 (B36_pt j)) = 0 ↔
      symp (dec3 (B36_pt piF)) (dec3 (B36_pt pjF)) = 0 := by
    have hstep : ∀ (ws : List (PauliIdx 3)) (a b : PauliIdx 3),
        symp (ws.foldl (fun c u => transvPt u c) a) (ws.foldl (fun c u => transvPt u c) b) = symp a b := by
      intro ws; induction ws with
      | nil => intro _ _; rfl
      | cons w ws ih => intro a b; simp only [List.foldl_cons, ih, symp_transvPt]
    rw [← hfold_pt i, ← hfold_pt j, hstep]
  have hne_iff : i ≠ j ↔ piF ≠ pjF := ⟨fun h heq => h (hpinj i j (congr_arg Fin.val heq)), fun h heq => h (by subst heq; rfl)⟩
  by_cases hcond : i ≠ j ∧ symp3 (B36_val i.val) (B36_val j.val) = 0
  · have hM1 : orb0_Mt i.val j.val ≠ 0 := by
      unfold orb0_Mt; rw [orb0_M0_eq_M36]
      have hm := (M36_val_spec ⟨0, by decide⟩ i j).2.mpr hcond
      rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hi | hi <;>
      rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ j with hj | hj <;>
      simp [orb0_u0, hi, hj, hm]
    have hsp1 : symp (dec3 (B36_pt i)) (dec3 (B36_pt j)) = 0 := by
      simp only [symp_dec3, B36_pt, hcond.2]; rfl
    have hsp2 : symp (dec3 (B36_pt piF)) (dec3 (B36_pt pjF)) = 0 := hsymp_iff.mp hsp1
    have hsp2_nat : symp3 (B36_val piF.val) (B36_val pjF.val) = 0 := by
      rw [symp_dec3] at hsp2; change ((symp3 (B36_val piF.val) (B36_val pjF.val) : Nat) : ZMod 2) = 0 at hsp2
      have hlt := symp3_lt2 (B36_val piF.val) (B36_val pjF.val)
      generalize symp3 (B36_val piF.val) (B36_val pjF.val) = m at hlt hsp2 ⊢; interval_cases m; rfl; exact absurd hsp2 (by decide)
    have hM2 : orb0_Mt piF.val pjF.val ≠ 0 := by
      unfold orb0_Mt; rw [orb0_M0_eq_M36]
      have hm := (M36_val_spec ⟨0, by decide⟩ piF pjF).2.mpr ⟨hne_iff.mp hcond.1, hsp2_nat⟩
      rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ piF with hi | hi <;>
      rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ pjF with hj | hj <;>
      simp [orb0_u0, hi, hj, hm]
    rw [hMt_eq_frust sU0' hsU0'_A hsU0'_B i j hM1, hMt_eq_frust sU0 hsU0_A hsU0_B piF pjF hM2]
    have hpi_ne : dec3 (B36_pt i) ≠ dec3 (B36_pt j) :=
      fun h => hcond.1 (B36_val_inj (congr_arg Fin.val (equiv3.symm.injective h)))
    have hfe := hfeq (dec3 (B36_pt i)) (dec3 (B36_pt j))
      (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 (Finset.mem_erase.mp (B36_pt_mem_nz j)).1 hpi_ne hsp1
    have hwc := (hword_cocycle (word3FromNat us) sU0 (dec3 (B36_pt i)) (dec3 (B36_pt j)) hsp1).2
    rw [hfold_pt i, hfold_pt j] at hwc
    calc gammaSgn (dec3 (B36_pt i)) (dec3 (B36_pt j)) * sU0' (dec3 (B36_pt i)) *
          sU0' (dec3 (B36_pt j)) * sU0' (dec3 (B36_pt i) + dec3 (B36_pt j))
        = gammaSgn (dec3 (B36_pt i)) (dec3 (B36_pt j)) *
          (sU0' (dec3 (B36_pt i)) * sU0' (dec3 (B36_pt j)) * sU0' (dec3 (B36_pt i) + dec3 (B36_pt j))) := by ring
      _ = gammaSgn (dec3 (B36_pt i)) (dec3 (B36_pt j)) *
          (applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt i)) *
           applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt j)) *
           applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt i) + dec3 (B36_pt j))) := by rw [hfe]
      _ = gammaSgn (dec3 (B36_pt i)) (dec3 (B36_pt j)) *
          applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt i)) *
          applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt j)) *
          applyTransvWord (word3FromNat us) sU0 (dec3 (B36_pt i) + dec3 (B36_pt j)) := by ring
      _ = _ := hwc
  · have hM1 : orb0_Mt i.val j.val = 0 := by
      unfold orb0_Mt; rw [orb0_M0_eq_M36]
      have h0 : M36_val 0 i.val j.val = 0 := by
        by_contra hne; exact hcond ((M36_val_spec ⟨0, by decide⟩ i j).2.mp hne)
      simp [h0]
    have hM2 : orb0_Mt piF.val pjF.val = 0 := by
      unfold orb0_Mt; rw [orb0_M0_eq_M36]
      have h0 : M36_val 0 piF.val pjF.val = 0 := by
        by_contra hne
        obtain ⟨hne2, hsp2⟩ := (M36_val_spec ⟨0, by decide⟩ piF pjF).2.mp hne
        have hsp1 : symp (dec3 (B36_pt i)) (dec3 (B36_pt j)) = 0 :=
          hsymp_iff.mpr (by simp only [symp_dec3, B36_pt, hsp2]; rfl)
        rw [symp_dec3] at hsp1; change ((symp3 (B36_val i.val) (B36_val j.val) : Nat) : ZMod 2) = 0 at hsp1
        have hlt := symp3_lt2 (B36_val i.val) (B36_val j.val)
        have hsp1_nat : symp3 (B36_val i.val) (B36_val j.val) = 0 := by
          generalize symp3 (B36_val i.val) (B36_val j.val) = m at hlt hsp1 ⊢; interval_cases m; rfl; exact absurd hsp1 (by decide)
        exact hcond ⟨hne_iff.mpr hne2, hsp1_nat⟩
      simp [h0]
    rw [hM1, hM2]

/-! ### Section 3: `K_{3,3,3}` 3-Coloring & `C₄`-Free 3-Regular Bipartite Bounds -/

private lemma three_color_edge_bound (A : Finset (Fin 36)) (col : Fin 36 → Nat)
    (hcol_lt : ∀ i ∈ A, col i < 3)
    (hcol_ok : ∀ i ∈ A, ∀ j ∈ A, orb0_Mt i.val j.val = 1 → col i ≠ col j) :
    ((A ×ˢ A).filter fun ij => orb0_Mt ij.1.val ij.2.val = 1).card ≤ (2 * A.card * A.card) / 3 := by
  let C0 := A.filter fun i => col i = 0
  let C1 := A.filter fun i => col i = 1
  let C2 := A.filter fun i => col i = 2
  have hpart : A.card = C0.card + C1.card + C2.card := by
    have hu : A = (C0 ∪ C1) ∪ C2 := by
      ext i; simp only [C0, C1, C2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hi; have hlt := hcol_lt i hi
        have h012 : col i = 0 ∨ col i = 1 ∨ col i = 2 := by omega
        rcases h012 with h | h | h
        · exact Or.inl (Or.inl ⟨hi, h⟩)
        · exact Or.inl (Or.inr ⟨hi, h⟩)
        · exact Or.inr ⟨hi, h⟩
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    have hd1 : Disjoint C0 C1 := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [C0, C1, Finset.mem_filter] at h1 h2; omega
    have hd2 : Disjoint (C0 ∪ C1) C2 := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [C0, C1, C2, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
    conv_lhs => rw [hu]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  let E := (A ×ˢ A).filter fun ij => orb0_Mt ij.1.val ij.2.val = 1
  let D := (C0 ×ˢ C0) ∪ (C1 ×ˢ C1) ∪ (C2 ×ˢ C2)
  have hsub : E ∪ D ⊆ A ×ˢ A := by
    intro ij hij
    rcases Finset.mem_union.mp hij with h | h
    · exact (Finset.mem_filter.mp h).1
    · simp only [D, C0, C1, C2, Finset.mem_union, Finset.mem_product, Finset.mem_filter] at h ⊢
      rcases h with (⟨⟨a, _⟩, ⟨b, _⟩⟩ | ⟨⟨a, _⟩, ⟨b, _⟩⟩) | ⟨⟨a, _⟩, ⟨b, _⟩⟩ <;> exact ⟨a, b⟩
  have hdisED : Disjoint E D := Finset.disjoint_left.mpr fun ⟨i, j⟩ hE hD => by
    simp only [E, Finset.mem_filter, Finset.mem_product] at hE
    simp only [D, C0, C1, C2, Finset.mem_union, Finset.mem_product, Finset.mem_filter] at hD
    have hne := hcol_ok i hE.1.1 j hE.1.2 hE.2
    rcases hD with (⟨⟨_, a⟩, ⟨_, b⟩⟩ | ⟨⟨_, a⟩, ⟨_, b⟩⟩) | ⟨⟨_, a⟩, ⟨_, b⟩⟩ <;> omega
  have hD_card : D.card = C0.card * C0.card + C1.card * C1.card + C2.card * C2.card := by
    have hd1 : Disjoint (C0 ×ˢ C0) (C1 ×ˢ C1) := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [C0, C1, Finset.mem_product, Finset.mem_filter] at h1 h2; omega
    have hd2 : Disjoint ((C0 ×ˢ C0) ∪ (C1 ×ˢ C1)) (C2 ×ˢ C2) := Finset.disjoint_left.mpr fun _ h1 h2 => by
      simp only [C0, C1, C2, Finset.mem_union, Finset.mem_product, Finset.mem_filter] at h1 h2; omega
    dsimp only [D]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_product, Finset.card_product, Finset.card_product]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisED, Finset.card_product, hD_card] at hle
  have hcs : A.card * A.card ≤ 3 * (C0.card * C0.card + C1.card * C1.card + C2.card * C2.card) := by
    have hZ : ((A.card : ℤ) * A.card) ≤ 3 * ((C0.card : ℤ) * C0.card + C1.card * C1.card + C2.card * C2.card) := by
      have hpZ : (A.card : ℤ) = (C0.card : ℤ) + C1.card + C2.card := by exact_mod_cast hpart
      nlinarith [sq_nonneg ((C0.card : ℤ) - C1.card), sq_nonneg ((C1.card : ℤ) - C2.card),
        sq_nonneg ((C2.card : ℤ) - C0.card)]
    exact_mod_cast hZ
  have h2A : 2 * A.card * A.card = 2 * (A.card * A.card) := by ring
  have h3E : 3 * E.card ≤ 2 * A.card * A.card := by omega
  change E.card ≤ (2 * A.card * A.card) / 3
  omega

private lemma bip_c4free_bound (A B : Finset (Fin 36))
    (hdA : ∀ u ∈ A, (B.filter fun v => orb0_Mt u.val v.val = 1).card ≤ 3)
    (hdB : ∀ v ∈ B, (A.filter fun u => orb0_Mt u.val v.val = 1).card ≤ 3)
    (hc4A : ∀ u1 ∈ A, ∀ u2 ∈ A, u1.val < u2.val →
      (B.filter fun v => orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1).card ≤ 1)
    (hc4B : ∀ v1 ∈ B, ∀ v2 ∈ B, v1.val < v2.val →
      (A.filter fun u => orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1).card ≤ 1) :
    ((A ×ˢ B).filter fun uv => orb0_Mt uv.1.val uv.2.val = 1).card ≤ bipBnd A.card B.card := by
  let E := (A ×ˢ B).filter fun uv => orb0_Mt uv.1.val uv.2.val = 1
  let dA : Fin 36 → Nat := fun u => (B.filter fun v => orb0_Mt u.val v.val = 1).card
  let dB : Fin 36 → Nat := fun v => (A.filter fun u => orb0_Mt u.val v.val = 1).card
  have hmA : E.card = ∑ u ∈ A, dA u := by
    simp only [E, dA, Finset.card_filter, Finset.sum_product]
  have hmB : E.card = ∑ v ∈ B, dB v := by
    simp only [E, dB, Finset.card_filter, Finset.sum_product_right]
  have hb1 : E.card ≤ 3 * A.card := by
    rw [hmA]; calc ∑ u ∈ A, dA u ≤ ∑ _u ∈ A, 3 := Finset.sum_le_sum hdA
      _ = 3 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hb2 : E.card ≤ 3 * B.card := by
    rw [hmB]; calc ∑ v ∈ B, dB v ≤ ∑ _v ∈ B, 3 := Finset.sum_le_sum hdB
      _ = 3 * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Cherry double-counting: `∑_{u ∈ A} dA(u)*(dA(u)-1) ≤ B.card * (B.card - 1)`!
  have hchA : ∑ u ∈ A, dA u * (dA u - 1) ≤ B.card * (B.card - 1) := by
    have h1 : ∑ u ∈ A, dA u * (dA u - 1) =
        ∑ v1 ∈ B, ∑ v2 ∈ B.erase v1, (A.filter fun u => orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1).card := by
      have hlhs : ∀ u ∈ A, dA u * (dA u - 1) =
          ∑ v1 ∈ B, ∑ v2 ∈ B.erase v1, if orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1 then 1 else 0 := by
        intro u _
        let Nu := B.filter fun v => orb0_Mt u.val v.val = 1
        have hcard_off : ((Nu ×ˢ Nu).filter fun p => p.1 ≠ p.2).card = Nu.card * (Nu.card - 1) := by
          have hsub : (Nu ×ˢ Nu).filter (fun p => p.1 = p.2) ⊆ Nu ×ˢ Nu := Finset.filter_subset _ _
          have hdiag : ((Nu ×ˢ Nu).filter fun p => p.1 = p.2).card = Nu.card := by
            refine Finset.card_bij (fun p _ => p.1) (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
              (fun a ha b hb h => Prod.ext h ((Finset.mem_filter.mp ha).2.symm.trans (h.trans (Finset.mem_filter.mp hb).2)))
              (fun x hx => ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩, rfl⟩)
          have htot : ((Nu ×ˢ Nu).filter fun p => p.1 = p.2).card + ((Nu ×ˢ Nu).filter fun p => p.1 ≠ p.2).card = (Nu ×ˢ Nu).card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
            congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
          rw [Finset.card_product, hdiag] at htot
          rcases Nat.eq_zero_or_pos Nu.card with h0 | hpos
          · simp [h0] at htot ⊢; omega
          · have hmul : Nu.card * (Nu.card - 1) + Nu.card = Nu.card * Nu.card := by
              cases h : Nu.card with | zero => omega | succ m => simp [Nat.mul_succ]
            omega
        rw [← hcard_off]
        calc ((Nu ×ˢ Nu).filter fun p => p.1 ≠ p.2).card
            = ∑ v1 ∈ Nu, ∑ v2 ∈ Nu, if v1 ≠ v2 then 1 else 0 := by rw [Finset.card_filter, Finset.sum_product]
          _ = ∑ v1 ∈ B, ∑ v2 ∈ B, if orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1 ∧ v1 ≠ v2 then 1 else 0 := by
                simp only [Nu, Finset.sum_filter]
                refine Finset.sum_congr rfl fun v1 _ => ?_
                by_cases h1 : orb0_Mt u.val v1.val = 1
                · rw [if_pos h1]; refine Finset.sum_congr rfl fun v2 _ => ?_
                  by_cases h2 : orb0_Mt u.val v2.val = 1 <;> by_cases h3 : v1 ≠ v2 <;> simp [h1, h2, h3]
                · rw [if_neg h1]; exact (Finset.sum_eq_zero fun v2 _ => by simp [h1]).symm
          _ = ∑ v1 ∈ B, ∑ v2 ∈ B.erase v1, if orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1 then 1 else 0 := by
                refine Finset.sum_congr rfl fun v1 hv1 => ?_
                rw [← Finset.add_sum_erase _ _ hv1]; simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_add]
                refine Finset.sum_congr rfl fun v2 hv2 => ?_
                have hne : v1 ≠ v2 := Ne.symm (Finset.mem_erase.mp hv2).1
                simp [hne]
      rw [Finset.sum_congr rfl hlhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v2 _ => by rw [Finset.card_filter]
    rw [h1]
    calc ∑ v1 ∈ B, ∑ v2 ∈ B.erase v1, (A.filter fun u => orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1).card
        ≤ ∑ v1 ∈ B, ∑ _v2 ∈ B.erase v1, 1 := by
          refine Finset.sum_le_sum fun v1 hv1 => Finset.sum_le_sum fun v2 hv2 => ?_
          have hv2B : v2 ∈ B := (Finset.mem_erase.mp hv2).2
          have hne : v1.val ≠ v2.val := fun h => (Finset.mem_erase.mp hv2).1 (Fin.ext h.symm)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hc4B v1 hv1 v2 hv2B hlt
          · have hsym : (A.filter fun u => orb0_Mt u.val v1.val = 1 ∧ orb0_Mt u.val v2.val = 1) =
                (A.filter fun u => orb0_Mt u.val v2.val = 1 ∧ orb0_Mt u.val v1.val = 1) :=
              Finset.ext fun u => by simp [and_comm]
            rw [hsym]; exact hc4B v2 hv2B v1 hv1 hgt
      _ = B.card * (B.card - 1) := by
          have : ∀ v1 ∈ B, (∑ _v2 ∈ B.erase v1, (1 : Nat)) = B.card - 1 := fun v1 hv1 => by
            rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hv1]
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  have hchB : ∑ v ∈ B, dB v * (dB v - 1) ≤ A.card * (A.card - 1) := by
    have h1 : ∑ v ∈ B, dB v * (dB v - 1) =
        ∑ u1 ∈ A, ∑ u2 ∈ A.erase u1, (B.filter fun v => orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1).card := by
      have hlhs : ∀ v ∈ B, dB v * (dB v - 1) =
          ∑ u1 ∈ A, ∑ u2 ∈ A.erase u1, if orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1 then 1 else 0 := by
        intro v _
        let Nv := A.filter fun u => orb0_Mt u.val v.val = 1
        have hcard_off : ((Nv ×ˢ Nv).filter fun p => p.1 ≠ p.2).card = Nv.card * (Nv.card - 1) := by
          have hdiag : ((Nv ×ˢ Nv).filter fun p => p.1 = p.2).card = Nv.card := by
            refine Finset.card_bij (fun p _ => p.1) (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
              (fun a ha b hb h => Prod.ext h ((Finset.mem_filter.mp ha).2.symm.trans (h.trans (Finset.mem_filter.mp hb).2)))
              (fun x hx => ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩, rfl⟩)
          have htot : ((Nv ×ˢ Nv).filter fun p => p.1 = p.2).card + ((Nv ×ˢ Nv).filter fun p => p.1 ≠ p.2).card = (Nv ×ˢ Nv).card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
            congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
          rw [Finset.card_product, hdiag] at htot
          rcases Nat.eq_zero_or_pos Nv.card with h0 | hpos
          · simp [h0] at htot ⊢; omega
          · have hmul : Nv.card * (Nv.card - 1) + Nv.card = Nv.card * Nv.card := by
              cases h : Nv.card with | zero => omega | succ m => simp [Nat.mul_succ]
            omega
        rw [← hcard_off]
        calc ((Nv ×ˢ Nv).filter fun p => p.1 ≠ p.2).card
            = ∑ u1 ∈ Nv, ∑ u2 ∈ Nv, if u1 ≠ u2 then 1 else 0 := by rw [Finset.card_filter, Finset.sum_product]
          _ = ∑ u1 ∈ A, ∑ u2 ∈ A, if orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1 ∧ u1 ≠ u2 then 1 else 0 := by
                simp only [Nv, Finset.sum_filter]
                refine Finset.sum_congr rfl fun u1 _ => ?_
                by_cases h1 : orb0_Mt u1.val v.val = 1
                · rw [if_pos h1]; refine Finset.sum_congr rfl fun u2 _ => ?_
                  by_cases h2 : orb0_Mt u2.val v.val = 1 <;> by_cases h3 : u1 ≠ u2 <;> simp [h1, h2, h3]
                · rw [if_neg h1]; exact (Finset.sum_eq_zero fun u2 _ => by simp [h1]).symm
          _ = ∑ u1 ∈ A, ∑ u2 ∈ A.erase u1, if orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1 then 1 else 0 := by
                refine Finset.sum_congr rfl fun u1 hu1 => ?_
                rw [← Finset.add_sum_erase _ _ hu1]; simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte, zero_add]
                refine Finset.sum_congr rfl fun u2 hu2 => ?_
                have hne : u1 ≠ u2 := Ne.symm (Finset.mem_erase.mp hu2).1
                simp [hne]
      rw [Finset.sum_congr rfl hlhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u2 _ => by rw [Finset.card_filter]
    rw [h1]
    calc ∑ u1 ∈ A, ∑ u2 ∈ A.erase u1, (B.filter fun v => orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1).card
        ≤ ∑ u1 ∈ A, ∑ _u2 ∈ A.erase u1, 1 := by
          refine Finset.sum_le_sum fun u1 hu1 => Finset.sum_le_sum fun u2 hu2 => ?_
          have hu2A : u2 ∈ A := (Finset.mem_erase.mp hu2).2
          have hne : u1.val ≠ u2.val := fun h => (Finset.mem_erase.mp hu2).1 (Fin.ext h.symm)
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hc4A u1 hu1 u2 hu2A hlt
          · have hsym : (B.filter fun v => orb0_Mt u1.val v.val = 1 ∧ orb0_Mt u2.val v.val = 1) =
                (B.filter fun v => orb0_Mt u2.val v.val = 1 ∧ orb0_Mt u1.val v.val = 1) :=
              Finset.ext fun v => by simp [and_comm]
            rw [hsym]; exact hc4A u2 hu2A u1 hu1 hgt
      _ = A.card * (A.card - 1) := by
          have : ∀ u1 ∈ A, (∑ _u2 ∈ A.erase u1, (1 : Nat)) = A.card - 1 := fun u1 hu1 => by
            rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hu1]
          rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  have hd_ineq1 : ∀ d : Nat, 2 * d ≤ 2 + d * (d - 1) := fun d => by
    cases d with | zero => omega | succ m =>
      have : 0 ≤ m * m - m := Nat.zero_le _
      cases m with | zero => omega | succ k => simp [Nat.mul_succ, Nat.succ_mul]; nlinarith
  have hd_ineq2 : ∀ d : Nat, 4 * d ≤ 6 + d * (d - 1) := fun d => by
    cases d with | zero => omega | succ m =>
      cases m with | zero => omega | succ k =>
        cases k with | zero => omega | succ j => simp [Nat.mul_succ, Nat.succ_mul]; nlinarith
  have heven_mul : ∀ n : Nat, 2 ∣ n * (n - 1) := fun n => by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · exact ⟨n * k, by rw [hk]; simp only [Nat.add_sub_cancel]; ring⟩
  have hb3 : E.card ≤ A.card + B.card * (B.card - 1) / 2 := by
    have h2 : 2 * E.card ≤ 2 * A.card + B.card * (B.card - 1) := by
      rw [hmA, Finset.mul_sum]
      calc ∑ u ∈ A, 2 * dA u ≤ ∑ u ∈ A, (2 + dA u * (dA u - 1)) := Finset.sum_le_sum fun u _ => hd_ineq1 (dA u)
        _ = 2 * A.card + ∑ u ∈ A, dA u * (dA u - 1) := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * A.card + B.card * (B.card - 1) := Nat.add_le_add_left hchA _
    rcases heven_mul B.card with ⟨q, hq⟩; rw [hq] at h2 ⊢; omega
  have hb4 : E.card ≤ B.card + A.card * (A.card - 1) / 2 := by
    have h2 : 2 * E.card ≤ 2 * B.card + A.card * (A.card - 1) := by
      rw [hmB, Finset.mul_sum]
      calc ∑ v ∈ B, 2 * dB v ≤ ∑ v ∈ B, (2 + dB v * (dB v - 1)) := Finset.sum_le_sum fun v _ => hd_ineq1 (dB v)
        _ = 2 * B.card + ∑ v ∈ B, dB v * (dB v - 1) := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * B.card + A.card * (A.card - 1) := Nat.add_le_add_left hchB _
    rcases heven_mul A.card with ⟨q, hq⟩; rw [hq] at h2 ⊢; omega
  have hb5 : E.card ≤ (3 * A.card + B.card * (B.card - 1) / 2) / 2 := by
    have h4 : 4 * E.card ≤ 6 * A.card + B.card * (B.card - 1) := by
      rw [hmA, Finset.mul_sum]
      calc ∑ u ∈ A, 4 * dA u ≤ ∑ u ∈ A, (6 + dA u * (dA u - 1)) := Finset.sum_le_sum fun u _ => hd_ineq2 (dA u)
        _ = 6 * A.card + ∑ u ∈ A, dA u * (dA u - 1) := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 6 * A.card + B.card * (B.card - 1) := Nat.add_le_add_left hchA _
    rcases heven_mul B.card with ⟨q, hq⟩; rw [hq] at h4 ⊢; omega
  have hb6 : E.card ≤ (3 * B.card + A.card * (A.card - 1) / 2) / 2 := by
    have h4 : 4 * E.card ≤ 6 * B.card + A.card * (A.card - 1) := by
      rw [hmB, Finset.mul_sum]
      calc ∑ v ∈ B, 4 * dB v ≤ ∑ v ∈ B, (6 + dB v * (dB v - 1)) := Finset.sum_le_sum fun v _ => hd_ineq2 (dB v)
        _ = 6 * B.card + ∑ v ∈ B, dB v * (dB v - 1) := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 6 * B.card + A.card * (A.card - 1) := Nat.add_le_add_left hchB _
    rcases heven_mul A.card with ⟨q, hq⟩; rw [hq] at h4 ⊢; omega
  unfold bipBnd
  exact le_min (le_min hb1 hb2) (le_min (le_min hb3 hb4) (le_min hb5 hb6))

/-! ### Section 4: Master Part 2c Theorem (`orbit0_hits_sp42`) -/

private lemma orb0_hit_of_mask {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val)
    {mask spId : Nat} {us : List Nat}
    (hmask : ∀ i : Fin 36, s3 (dec3 (B36_pt i)) = orb0_u0 i.val * (if mask.testBit i.val = true then -1 else 1))
    (hok : orb0_checkHitsSp42 mask spId us = true) :
    ∃ (sp : Fin 42) (ws : List (PauliIdx 3)),
      w5FrustEq (applyTransvWord ws s3) (listToSign3 (sp42Certs sp).s64) := by
  unfold orb0_checkHitsSp42 at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨hsp, hus_lt⟩, hwl⟩
  rw [orb0_A27_eq, orb0_B36_eq, orb0_wlines_eq] at hwl
  let sInit : Nat → ℤ := fun v =>
    match A27_list.idxOf? v with
    | some idxA => (rep27_vecs.getD 0 []).getD idxA 0
    | none =>
      match B36_list.idxOf? v with
      | some idxB => orb0_u0 idxB * (if ((mask >>> idxB) &&& 1) == 1 then (-1 : ℤ) else 1)
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
        rw [← hpt, hA27 ia]; dsimp only [sInit, A27_pt]; rw [A27_idxOf_val ia]; rfl
      · obtain ⟨ib, hib⟩ := B36_val_surj v hv0 hq1
        have hpt : B36_pt ib = v := Fin.ext hib
        rw [← hpt, hmask ib]; dsimp only [sInit, B36_pt]
        rw [A27_idxOf_none_of_B36 ib, B36_idxOf_val ib]; dsimp only; rw [testBit_eq_shr_and1]
        cases mask.testBit ib.val <;> rfl
  let sInitArr : List ℤ := (List.range 64).map sInit
  let sOutArr : List ℤ := (List.range 64).map fun v => applyWord3Nat us (fun w => sInitArr.getD w 0) v
  have hsInitArr : ∀ v : Fin 64, sInitArr.getD v.val 0 = s3 (dec3 v) := fun v => by
    dsimp only [sInitArr]; rw [dpll_getD_map_range 64 sInit 0 v.isLt]; exact hagree v
  have hword_eq : ∀ v : Fin 64, sOutArr.getD v.val 0 = applyTransvWord (word3FromNat us) s3 (dec3 v) := fun v => by
    dsimp only [sOutArr]; rw [dpll_getD_map_range 64 _ 0 v.isLt]
    exact applyWord3Nat_eq_on_inv (fun _ => true) us
      (fun u hu => ⟨decide_eq_true_eq.mp (List.all_eq_true.mp hus_lt u hu), fun _ _ _ => rfl⟩)
      (fun w => sInitArr.getD w 0) s3 (fun w _ => hsInitArr w) v rfl
  have hwl' : (wlines315.all fun (a, b, c, _) =>
      sOutArr.getD a 0 * sOutArr.getD b 0 * sOutArr.getD c 0 ==
        getS64 (sp42S64List.getD spId []) a * getS64 (sp42S64List.getD spId []) b *
          getS64 (sp42S64List.getD spId []) c) = true := hwl
  exact ⟨⟨spId, hsp⟩, word3FromNat us, w5FrustEq_of_wlines315_all (sOut := fun w => sOutArr.getD w 0) (spId := ⟨spId, hsp⟩) hword_eq hwl'⟩

private lemma orb0_applyStabU0_step {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val)
    {target0 g : Nat} {us : List Nat} {perm : List Nat}
    (hchk : orb0_checkStabU0 target0 g us = some perm) :
    perm.length = 36 ∧ perm.getD 0 99 = target0 ∧
    (∀ i : Fin 36, perm.getD i.val 0 < 36) ∧
    (∀ i j : Fin 36, orb0_Mt i.val j.val = orb0_Mt (perm.getD i.val 0) (perm.getD j.val 0)) ∧
    ∃ (s3' : PauliIdx 3 → ℤ),
      IsSignAssign s3' ∧
      w5FrustEq s3' (applyTransvWord (word3FromNat us) s3) ∧
      (∀ a : Fin 27, s3' (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
      (∀ i : Fin 36, ∀ hp : perm.getD i.val 0 < 36,
        orb0_u0 i.val * s3' (dec3 (B36_pt i)) =
          orb0_u0 (perm.getD i.val 0) * s3 (dec3 (B36_pt ⟨perm.getD i.val 0, hp⟩))) := by
  unfold orb0_checkStabU0 at hchk
  cases hact : orb0_actionB36 g us with
  | none => rw [hact] at hchk; simp at hchk
  | some ps =>
    rcases ps with ⟨p', sgn⟩
    rw [hact] at hchk; dsimp only at hchk
    split_ifs at hchk with hok
    · simp only [Option.some.injEq] at hchk; subst hchk
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
      obtain ⟨hg, _, hplen, _, hplt, _, hsem⟩ := sound_orb0_actionB36 hact
      obtain ⟨hA', hB'⟩ := hsem hg hA27
      have hpres : (∀ i : Fin 36, orb0_u0 (p'.getD i.val 0) * sgn.getD i.val 0 = orb0_u0 i.val) ∨
                   (∀ i : Fin 36, orb0_u0 (p'.getD i.val 0) * sgn.getD i.val 0 = -orb0_u0 i.val) := by
        rcases hok.1 with hpos | hneg
        · exact Or.inl fun i => beq_iff_eq.mp (dpll_all_range hpos i.isLt)
        · exact Or.inr fun i => beq_iff_eq.mp (dpll_all_range hneg i.isLt)
      have hMt_pres := orb0_stabU0_preserves_Mt hact hpres
      rcases hpres with hpos | hneg
      · let s3' := applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3)
        refine ⟨hplen, hok.2, hplt, hMt_pres, s3',
          applyGauge_isSignAssign _ (applyTransvWord_isSignAssign _ hs3),
          w5FrustEq_applyGauge _ _, hA', fun i hp => ?_⟩
        dsimp only [s3']; rw [hB' i hp]
        have h1 := hpos i
        have hu := orb0_u0_sq i
        have hu2 := orb0_u0_sq ⟨p'.getD i.val 0, hp⟩
        calc orb0_u0 i.val * (sgn.getD i.val 0 * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)))
            = (orb0_u0 (p'.getD i.val 0) * orb0_u0 (p'.getD i.val 0)) *
              (orb0_u0 i.val * sgn.getD i.val 0 * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩))) := by rw [hu2]; ring
          _ = orb0_u0 (p'.getD i.val 0) * ((orb0_u0 (p'.getD i.val 0) * sgn.getD i.val 0) * orb0_u0 i.val) *
              s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by ring
          _ = orb0_u0 (p'.getD i.val 0) * (orb0_u0 i.val * orb0_u0 i.val) *
              s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by rw [h1]
          _ = orb0_u0 (p'.getD i.val 0) * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by rw [hu]; ring
      · let s3' := flipB36 true (applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3))
        refine ⟨hplen, hok.2, hplt, hMt_pres, s3',
          flipB36_isSignAssign true (applyGauge_isSignAssign _ (applyTransvWord_isSignAssign _ hs3)),
          w5FrustEq_trans (w5FrustEq_flipB36 true _) (w5FrustEq_applyGauge _ _),
          fun a => by dsimp only [s3']; rw [flipB36_on_A27 true _ (Finset.mem_filter.mp (A27_pt_mem_Qminus a)).2]; exact hA' a,
          fun i hp => ?_⟩
        dsimp only [s3']; rw [flipB36_on_B36 true _ (B36_pt_quadForm i), hB' i hp]
        have h1 := hneg i
        have hu := orb0_u0_sq i
        have hu2 := orb0_u0_sq ⟨p'.getD i.val 0, hp⟩
        calc orb0_u0 i.val * ((-1) * (sgn.getD i.val 0 * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩))))
            = (orb0_u0 (p'.getD i.val 0) * orb0_u0 (p'.getD i.val 0)) *
              (orb0_u0 i.val * (-sgn.getD i.val 0) * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩))) := by rw [hu2]; ring
          _ = orb0_u0 (p'.getD i.val 0) * ((-(orb0_u0 (p'.getD i.val 0) * sgn.getD i.val 0)) * orb0_u0 i.val) *
              s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by ring
          _ = orb0_u0 (p'.getD i.val 0) * (orb0_u0 i.val * orb0_u0 i.val) *
              s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by rw [h1]; ring
          _ = orb0_u0 (p'.getD i.val 0) * s3 (dec3 (B36_pt ⟨p'.getD i.val 0, hp⟩)) := by rw [hu]; ring

private lemma natBST_mem_of_allIn {ms : List Nat} {t : NatBST} (hall : t.allIn ms = true) {x : Nat}
    (hmem : t.mem x = true) : ms.contains x = true := by
  induction t with
  | leaf => simp [NatBST.mem] at hmem
  | node v l r ihl ihr =>
    simp only [NatBST.allIn, Bool.and_eq_true] at hall
    unfold NatBST.mem at hmem
    split_ifs at hmem with heq hle
    · rw [Nat.eq_of_beq_eq_true heq]; exact hall.1.1
    · exact ihl hall.1.2 hmem
    · exact ihr hall.2 hmem

private lemma applyInvPerm36_testBit (invP vs : List Nat) (i : Nat) :
    (applyInvPerm36 invP vs).testBit i = true ↔ ∃ v ∈ vs, invP.getD v 0 = i := by
  unfold applyInvPerm36
  have hgen : ∀ (L : List Nat) (acc : Nat),
      (L.foldl (fun nm v => Nat.lor nm (Nat.shiftLeft 1 (invP.getD v 0))) acc).testBit i = true ↔
        acc.testBit i = true ∨ ∃ v ∈ L, invP.getD v 0 = i := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      change (acc ||| (1 <<< invP.getD x 0)).testBit i = true ∨ _ ↔ _
      rw [testBit_bitOr_single, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((ha | hxi) | ⟨v, hv, hvi⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨x, List.mem_cons_self .., hxi.symm⟩
        · exact Or.inr ⟨v, List.mem_cons_of_mem x hv, hvi⟩
      · rintro (ha | ⟨v, hv, hvi⟩)
        · exact Or.inl (Or.inl ha)
        · rcases List.mem_cons.mp hv with rfl | hv'
          · exact Or.inl (Or.inr hvi.symm)
          · exact Or.inr ⟨v, hv', hvi⟩
  simpa using hgen vs 0

set_option maxHeartbeats 4000000 in
/-- **Master Part 2c Theorem (`orbit0_hits_sp42`)**:
    Every sign assignment on Orbit 0 (`f₂₇ = 9`) with `f_A ≤ 92` hits one of the 42 certified
    `Sp(6,2)` orbits `sp42Certs`. -/
theorem orbit0_hits_sp42 {s3 : PauliIdx 3 → ℤ} (hs3 : IsSignAssign s3)
    (hA27 : ∀ a : Fin 27, s3 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val)
    (hfA : frustPairs (nzPts 3) s3 ≤ 92 * 6) :
    ∃ (spId : Fin 42) (us : List (PauliIdx 3)),
      w5FrustEq (applyTransvWord us s3) (listToSign3 (sp42Certs spId).s64) := by
  -- 1. Spectral lower bound: `∑_{h < 3} (u_h · x)² ≥ 600 ⇒ ∃ h, |u_h · x| ≥ 16`!
  have hM0_lb : ∀ (s : PauliIdx 3 → ℤ), IsSignAssign s →
      (∀ a : Fin 27, s (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
      frustPairs (nzPts 3) s ≤ 92 * 6 →
      208 ≤ ∑ i : Fin 36, ∑ j : Fin 36, orb0_M0 i.val j.val * s (dec3 (B36_pt i)) * s (dec3 (B36_pt j)) := by
    intro s hs hAs hfAs
    have hf27 := frustPairs_Qminus09_eq_rep27 ⟨0, by decide⟩ hAs
    dsimp only at hf27
    have hsp := frustPairs_W52_A27_B36_split ⟨0, by decide⟩ hAs
    rw [hf27] at hsp
    change frustPairs (nzPts 3) s = 6 * 9 + 3 * (F36_set 0 s).card at hsp
    have hF_le : (F36_set 0 s).card ≤ 166 := by omega
    have hE_card : ((Finset.univ : Finset (Fin 36 × Fin 36)).filter fun ij => orb0_M0 ij.1.val ij.2.val ≠ 0).card = 540 := by
      have hdeg15 : ∀ i : Fin 36, ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_M0 i.val j.val ≠ 0).card = 15 := by
        intro i
        have hdp := (orb0_spectral_spec.2.2.2 i).1
        have hdn := (orb0_spectral_spec.2.2.2 i).2
        have hdis : Disjoint ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = 1)
            ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = -1) :=
          Finset.disjoint_left.mpr fun j h1 h2 => by
            simp only [Finset.mem_filter] at h1 h2; linarith [h1.2, h2.2]
        have hun : ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_M0 i.val j.val ≠ 0) =
            ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = 1) ∪
            ((Finset.univ : Finset (Fin 36)).filter fun j => orb0_Mt i.val j.val = -1) := by
          ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, orb0_Mt, orb0_M0_eq_M36]
          rcases (M36_val_spec ⟨0, by decide⟩ i j).1 with hm | hm | hm <;>
          rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hi | hi <;>
          rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ j with hj | hj <;>
          simp [orb0_u0, hm, hi, hj]
        rw [hun, Finset.card_union_of_disjoint hdis, hdp, hdn]
      rw [Finset.card_filter, Fintype.sum_prod_type]
      have : ∀ i : Fin 36, (∑ j : Fin 36, if orb0_M0 i.val j.val ≠ 0 then 1 else 0) = 15 := fun i => by
        rw [← Finset.card_filter]; exact hdeg15 i
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; rfl
    have hsum_eq : ∑ i : Fin 36, ∑ j : Fin 36, orb0_M0 i.val j.val * s (dec3 (B36_pt i)) * s (dec3 (B36_pt j)) =
        (540 : ℤ) - 2 * ((F36_set 0 s).card : ℤ) := by
      have hterm : ∀ ij : Fin 36 × Fin 36,
          orb0_M0 ij.1.val ij.2.val * s (dec3 (B36_pt ij.1)) * s (dec3 (B36_pt ij.2)) =
          (if orb0_M0 ij.1.val ij.2.val ≠ 0 then (1 : ℤ) else 0) -
          2 * (if ij ∈ F36_set 0 s then (1 : ℤ) else 0) := by
        rintro ⟨i, j⟩
        simp only [F36_set, Finset.mem_filter, Finset.mem_univ, true_and, orb0_M0_eq_M36]
        rcases (M36_val_spec ⟨0, by decide⟩ i j).1 with hm | hm | hm <;>
        rcases hs.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hi | hi <;>
        rcases hs.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz j)).1 with hj | hj <;>
        simp [hm, hi, hj]
      rw [← Fintype.sum_prod_type', Finset.sum_congr rfl fun ij _ => hterm ij, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      have h1 : (∑ ij : Fin 36 × Fin 36, if orb0_M0 ij.1.val ij.2.val ≠ 0 then (1 : ℤ) else 0) = 540 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hE_card]; norm_num
      have h2 : (∑ ij : Fin 36 × Fin 36, if ij ∈ F36_set 0 s then (1 : ℤ) else 0) = ((F36_set 0 s).card : ℤ) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [h1, h2]
    rw [hsum_eq]; omega
  -- Apply `R² = 36 R` to get `∃ h : Fin 3, 16 ≤ |∑ i, u_h[i] * x[i]|`!
  let x0 : Fin 36 → ℤ := fun i => s3 (dec3 (B36_pt i))
  have hx0_sq : ∀ i : Fin 36, x0 i * x0 i = 1 := fun i => by
    rcases hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with h | h <;> simp [x0, h]
  have hR_nn : 0 ≤ ∑ i : Fin 36, ∑ j : Fin 36, orb0_R i.val j.val * x0 i * x0 j := by
    have hsq : 36 * (∑ i : Fin 36, ∑ j : Fin 36, orb0_R i.val j.val * x0 i * x0 j) =
        ∑ k : Fin 36, (∑ i : Fin 36, orb0_R k.val i.val * x0 i) ^ 2 := by
      have hrhs : ∑ k : Fin 36, (∑ i : Fin 36, orb0_R k.val i.val * x0 i) ^ 2 =
          ∑ i : Fin 36, ∑ j : Fin 36, (∑ k : Fin 36, orb0_R i.val k.val * orb0_R k.val j.val) * x0 i * x0 j := by
        simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => by rw [orb0_R_symm k i]; ring
      rw [hrhs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [orb0_spectral_spec.1 i j]; ring
    have hnn : 0 ≤ ∑ k : Fin 36, (∑ i : Fin 36, orb0_R k.val i.val * x0 i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hR_exp : ∑ i : Fin 36, ∑ j : Fin 36, orb0_R i.val j.val * x0 i * x0 j =
      648 - 6 * (∑ i : Fin 36, ∑ j : Fin 36, orb0_M0 i.val j.val * x0 i * x0 j) +
      (∑ i : Fin 36, orb0_u 0 i.val * x0 i) ^ 2 +
      (∑ i : Fin 36, orb0_u 1 i.val * x0 i) ^ 2 +
      (∑ i : Fin 36, orb0_u 2 i.val * x0 i) ^ 2 := by
    have hdiag : ∑ i : Fin 36, ∑ j : Fin 36, (if i.val == j.val then (18 : ℤ) else 0) * x0 i * x0 j = 648 := by
      have hi : ∀ i : Fin 36, ∑ j : Fin 36, (if i.val == j.val then (18 : ℤ) else 0) * x0 i * x0 j = 18 := fun i => by
        rw [Finset.sum_eq_single i]
        · simp only [beq_self_eq_true, ↓reduceIte]; rw [mul_assoc, hx0_sq i, mul_one]
        · intro j _ hne; simp [beq_false_of_ne (Fin.val_ne_of_ne hne.symm)]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
    have hsq_u : ∀ h : Nat, (∑ i : Fin 36, orb0_u h i.val * x0 i) ^ 2 =
        ∑ i : Fin 36, ∑ j : Fin 36, orb0_u h i.val * orb0_u h j.val * x0 i * x0 j := fun h => by
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsq_u 0, hsq_u 1, hsq_u 2, ← hdiag]
    simp only [orb0_R, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hM0_0 := hM0_lb s3 hs3 hA27 hfA
  have hsum_sq : 600 ≤ (∑ i : Fin 36, orb0_u 0 i.val * x0 i) ^ 2 +
      (∑ i : Fin 36, orb0_u 1 i.val * x0 i) ^ 2 + (∑ i : Fin 36, orb0_u 2 i.val * x0 i) ^ 2 := by
    linarith
  have heven_dot : ∀ h : Fin 3, 2 ∣ ∑ i : Fin 36, orb0_u h.val i.val * x0 i := by
    intro h
    let Sh := (Finset.univ : Finset (Fin 36)).filter fun i => orb0_u h.val i.val * x0 i = -1
    have hdot : ∑ i : Fin 36, orb0_u h.val i.val * x0 i = 36 - 2 * (Sh.card : ℤ) := by
      have ht : ∀ i : Fin 36, orb0_u h.val i.val * x0 i = 1 - 2 * (if i ∈ Sh then (1 : ℤ) else 0) := fun i => by
        simp only [Sh, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases orb0_spectral_spec.2.2.1 h i with hu | hu <;>
        rcases hs3.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hx | hx <;>
        simp [x0, hu, hx]
      rw [Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have : (∑ i : Fin 36, if i ∈ Sh then (1 : ℤ) else 0) = (Sh.card : ℤ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1; exact congr_arg Finset.card (by ext i; simp)
      rw [this]; norm_num
    rw [hdot]; exact ⟨18 - (Sh.card : ℤ), by ring⟩
  have hex_h : ∃ h : Fin 3, 16 ≤ |∑ i : Fin 36, orb0_u h.val i.val * x0 i| := by
    by_contra hno; push Not at hno
    have hle14 : ∀ h : Fin 3, (∑ i : Fin 36, orb0_u h.val i.val * x0 i) ^ 2 ≤ 196 := fun h => by
      have hlt := hno h
      rcases heven_dot h with ⟨m, hm⟩
      rw [hm] at hlt ⊢
      have hm7 : |m| ≤ 7 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)] at hlt; omega
      have hsq : m ^ 2 ≤ 49 := by nlinarith [abs_le.mp hm7]
      nlinarith
    have h0 := hle14 ⟨0, by decide⟩; have h1 := hle14 ⟨1, by decide⟩; have h2 := hle14 ⟨2, by decide⟩
    linarith
  -- 2. Reduce `h ∈ {0, 1, 2}` and sign to `u₀` with `|S| ≤ 10`!
  have hsyms := checkOrb0Syms_ok
  unfold checkOrb0Syms at hsyms
  simp only [Bool.and_eq_true] at hsyms
  rcases hsyms with ⟨⟨⟨⟨⟨⟨hnp0_len, hnp0_ok⟩, hnp0_all⟩, hu1_ok⟩, hu2_ok⟩, hvTo0_ok⟩, hstab00_ok⟩
  have hred_u0 : ∃ (us1 : List (PauliIdx 3)) (s1 : PauliIdx 3 → ℤ),
      IsSignAssign s1 ∧
      w5FrustEq s1 (applyTransvWord us1 s3) ∧
      (∀ a : Fin 27, s1 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
      frustPairs (nzPts 3) s1 ≤ 92 * 6 ∧
      ((Finset.univ : Finset (Fin 36)).filter fun i => orb0_u0 i.val * s1 (dec3 (B36_pt i)) = -1).card ≤ 10 := by
    have hfrom_abs : ∀ (usA : List (PauliIdx 3)) (sA : PauliIdx 3 → ℤ),
        IsSignAssign sA → w5FrustEq sA (applyTransvWord usA s3) →
        (∀ a : Fin 27, sA (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
        frustPairs (nzPts 3) sA ≤ 92 * 6 →
        16 ≤ |∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i))| →
        ∃ (us1 : List (PauliIdx 3)) (s1 : PauliIdx 3 → ℤ),
          IsSignAssign s1 ∧ w5FrustEq s1 (applyTransvWord us1 s3) ∧
          (∀ a : Fin 27, s1 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
          frustPairs (nzPts 3) s1 ≤ 92 * 6 ∧
          ((Finset.univ : Finset (Fin 36)).filter fun i => orb0_u0 i.val * s1 (dec3 (B36_pt i)) = -1).card ≤ 10 := by
      intro usA sA hsA hfeqA hAA hfAA habs
      have hdot_S : ∀ (s : PauliIdx 3 → ℤ), IsSignAssign s →
          ∑ i : Fin 36, orb0_u0 i.val * s (dec3 (B36_pt i)) =
          36 - 2 * (((Finset.univ : Finset (Fin 36)).filter fun i => orb0_u0 i.val * s (dec3 (B36_pt i)) = -1).card : ℤ) := by
        intro s hs
        let S := (Finset.univ : Finset (Fin 36)).filter fun i => orb0_u0 i.val * s (dec3 (B36_pt i)) = -1
        have ht : ∀ i : Fin 36, orb0_u0 i.val * s (dec3 (B36_pt i)) = 1 - 2 * (if i ∈ S then (1 : ℤ) else 0) := fun i => by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hu | hu <;>
          rcases hs.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hx | hx <;>
          simp [orb0_u0, hu, hx]
        rw [Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        have : (∑ i : Fin 36, if i ∈ S then (1 : ℤ) else 0) = (S.card : ℤ) := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [this]; dsimp only [S]; norm_num
      rcases le_or_gt 0 (∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i))) with hnn | hneg
      · rw [abs_of_nonneg hnn, hdot_S sA hsA] at habs
        exact ⟨usA, sA, hsA, hfeqA, hAA, hfAA, by omega⟩
      · rw [abs_of_neg hneg] at habs
        let sB := flipB36 true sA
        have hsB : IsSignAssign sB := flipB36_isSignAssign true hsA
        have hfeqB : w5FrustEq sB (applyTransvWord usA s3) := w5FrustEq_trans (w5FrustEq_flipB36 true sA) hfeqA
        have hAB : ∀ a : Fin 27, sB (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val := fun a => by
          dsimp only [sB]; rw [flipB36_on_A27 true _ (Finset.mem_filter.mp (A27_pt_mem_Qminus a)).2]; exact hAA a
        have hfAB : frustPairs (nzPts 3) sB ≤ 92 * 6 := by
          rw [frustPairs_of_w5FrustEq (by simp [nzPts]) (w5FrustEq_flipB36 true sA)]; exact hfAA
        have hsumB : ∑ i : Fin 36, orb0_u0 i.val * sB (dec3 (B36_pt i)) =
            -(∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i))) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [sB]; rw [flipB36_on_B36 true _ (B36_pt_quadForm i)]; simp only [↓reduceIte]; ring
        rw [hdot_S sB hsB] at hsumB
        exact ⟨usA, sB, hsB, hfeqB, hAB, hfAB, by omega⟩
    have hmapU : ∀ (h : Fin 3) (g : Nat) (us : List Nat),
        orb0_checkMapsU h.val g us = true →
        16 ≤ |∑ i : Fin 36, orb0_u h.val i.val * x0 i| →
        ∃ (usA : List (PauliIdx 3)) (sA : PauliIdx 3 → ℤ),
          IsSignAssign sA ∧ w5FrustEq sA (applyTransvWord usA s3) ∧
          (∀ a : Fin 27, sA (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
          frustPairs (nzPts 3) sA ≤ 92 * 6 ∧
          16 ≤ |∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i))| := by
      intro h g us hchk habs
      unfold orb0_checkMapsU at hchk
      cases hact : orb0_actionB36 g us with
      | none => rw [hact] at hchk; simp at hchk
      | some ps =>
        rcases ps with ⟨perm, sgn⟩
        rw [hact] at hchk; dsimp only at hchk
        obtain ⟨hg, _, _, _, hplt, hpinj, hsem⟩ := sound_orb0_actionB36 hact
        obtain ⟨hA', hB'⟩ := hsem hg hA27
        let sA := applyGauge (dec3 ⟨g, hg⟩) (applyTransvWord (word3FromNat us) s3)
        have hfeqA : w5FrustEq sA (applyTransvWord (word3FromNat us) s3) := w5FrustEq_applyGauge _ _
        have hfAA : frustPairs (nzPts 3) sA ≤ 92 * 6 := by
          rw [frustPairs_of_w5FrustEq (by simp [nzPts]) hfeqA, frustPairs_nzPts_applyTransvWord]; exact hfA
        let f : Fin 36 → Fin 36 := fun i => ⟨perm.getD i.val 0, hplt i⟩
        have hbij : Function.Bijective f :=
          ⟨fun a b hab => hpinj a b (congr_arg Fin.val hab),
           Finite.injective_iff_surjective.mp (fun a b hab => hpinj a b (congr_arg Fin.val hab))⟩
        have hsum_perm : ∑ i : Fin 36, orb0_u h.val (f i).val * x0 (f i) =
            ∑ j : Fin 36, orb0_u h.val j.val * x0 j :=
          Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
        have huh_sq : ∀ i : Fin 36, orb0_u h.val (f i).val * orb0_u h.val (f i).val = 1 := fun i => by
          rcases orb0_spectral_spec.2.2.1 h (f i) with h1 | h1 <;> simp [h1]
        have hu0_sq' := orb0_u0_sq
        simp only [Bool.or_eq_true] at hchk
        refine ⟨word3FromNat us, sA, applyGauge_isSignAssign _ (applyTransvWord_isSignAssign _ hs3),
          hfeqA, hA', hfAA, ?_⟩
        rcases hchk with hpos | hneg
        · have heq_sum : ∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i)) =
              ∑ j : Fin 36, orb0_u h.val j.val * x0 j := by
            rw [← hsum_perm]; refine Finset.sum_congr rfl fun i _ => ?_
            have hp := beq_iff_eq.mp (dpll_all_range hpos i.isLt)
            dsimp only [sA]; rw [hB' i (hplt i)]
            calc orb0_u0 i.val * (sgn.getD i.val 0 * x0 (f i))
                = (orb0_u h.val (f i).val * orb0_u h.val (f i).val) *
                  (orb0_u0 i.val * sgn.getD i.val 0 * x0 (f i)) := by rw [huh_sq i]; ring
              _ = orb0_u h.val (f i).val * ((orb0_u h.val (f i).val * sgn.getD i.val 0) * orb0_u0 i.val) *
                  x0 (f i) := by ring
              _ = orb0_u h.val (f i).val * (orb0_u0 i.val * orb0_u0 i.val) * x0 (f i) := by rw [hp]
              _ = orb0_u h.val (f i).val * x0 (f i) := by rw [hu0_sq' i]; ring
          rw [heq_sum]; exact habs
        · have heq_sum : ∑ i : Fin 36, orb0_u0 i.val * sA (dec3 (B36_pt i)) =
              -(∑ j : Fin 36, orb0_u h.val j.val * x0 j) := by
            rw [← hsum_perm, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
            have hn := beq_iff_eq.mp (dpll_all_range hneg i.isLt)
            dsimp only [sA]; rw [hB' i (hplt i)]
            calc orb0_u0 i.val * (sgn.getD i.val 0 * x0 (f i))
                = (orb0_u h.val (f i).val * orb0_u h.val (f i).val) *
                  (orb0_u0 i.val * sgn.getD i.val 0 * x0 (f i)) := by rw [huh_sq i]; ring
              _ = orb0_u h.val (f i).val * ((orb0_u h.val (f i).val * sgn.getD i.val 0) * orb0_u0 i.val) *
                  x0 (f i) := by ring
              _ = orb0_u h.val (f i).val * ((-orb0_u0 i.val) * orb0_u0 i.val) * x0 (f i) := by rw [hn]
              _ = -(orb0_u h.val (f i).val * x0 (f i)) := by
                    rw [neg_mul, hu0_sq' i]; ring
          rw [heq_sum, abs_neg]; exact habs
    obtain ⟨h, hh⟩ := hex_h
    rcases h with ⟨hv, hlt⟩
    interval_cases hv
    · exact hfrom_abs [] s3 hs3 (w5FrustEq_refl s3) hA27 hfA hh
    · obtain ⟨usA, sA, hsA, hfeqA, hAA, hfAA, habs⟩ := hmapU ⟨1, by decide⟩ orb0_u1ToU0.1 orb0_u1ToU0.2 hu1_ok hh
      exact hfrom_abs usA sA hsA hfeqA hAA hfAA habs
    · obtain ⟨usA, sA, hsA, hfeqA, hAA, hfAA, habs⟩ := hmapU ⟨2, by decide⟩ orb0_u2ToU0.1 orb0_u2ToU0.2 hu2_ok hh
      exact hfrom_abs usA sA hsA hfeqA hAA hfAA habs
  obtain ⟨us1, s1, hs1, hfeq1, hA27_1, hfA1, hk_le10⟩ := hred_u0
  -- 3. Exact `Mt` flip-set energy identity: `e_+(S) - e_-(S) ≥ 9 * k - 29`!
  let flipSet : (PauliIdx 3 → ℤ) → Finset (Fin 36) := fun s =>
    Finset.univ.filter fun i => orb0_u0 i.val * s (dec3 (B36_pt i)) = -1
  let ePlus : Finset (Fin 36) → Nat := fun S => ((S ×ˢ S).filter fun ij => orb0_Mt ij.1.val ij.2.val = 1).card
  let eMinus : Finset (Fin 36) → Nat := fun S => ((S ×ˢ S).filter fun ij => orb0_Mt ij.1.val ij.2.val = -1).card
  have hMt_energy : ∀ (s : PauliIdx 3 → ℤ), IsSignAssign s →
      (∀ a : Fin 27, s (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
      frustPairs (nzPts 3) s ≤ 92 * 6 →
      9 * ((flipSet s).card : ℤ) - 29 ≤ (ePlus (flipSet s) : ℤ) - (eMinus (flipSet s) : ℤ) ∧
      2 ∣ ePlus (flipSet s) ∧ 2 ∣ eMinus (flipSet s) := by
    intro s hs hAs hfAs
    let S := flipSet s
    let y : Fin 36 → ℤ := fun i => orb0_u0 i.val * s (dec3 (B36_pt i))
    have hy_eq : ∀ i : Fin 36, y i = 1 - 2 * (if i ∈ S then (1 : ℤ) else 0) := fun i => by
      simp only [y, S, flipSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hu | hu <;>
      rcases hs.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hx | hx <;>
      simp [orb0_u0, hu, hx]
    have hM0_y : ∑ i : Fin 36, ∑ j : Fin 36, orb0_Mt i.val j.val * y i * y j =
        ∑ i : Fin 36, ∑ j : Fin 36, orb0_M0 i.val j.val * s (dec3 (B36_pt i)) * s (dec3 (B36_pt j)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      dsimp only [orb0_Mt, y]
      have hui := orb0_u0_sq i; have huj := orb0_u0_sq j
      calc orb0_M0 i.val j.val * orb0_u0 i.val * orb0_u0 j.val *
            (orb0_u0 i.val * s (dec3 (B36_pt i))) * (orb0_u0 j.val * s (dec3 (B36_pt j)))
          = orb0_M0 i.val j.val * (orb0_u0 i.val * orb0_u0 i.val) * (orb0_u0 j.val * orb0_u0 j.val) *
            s (dec3 (B36_pt i)) * s (dec3 (B36_pt j)) := by ring
        _ = orb0_M0 i.val j.val * s (dec3 (B36_pt i)) * s (dec3 (B36_pt j)) := by rw [hui, huj]; ring
    have hrow9 : ∀ i : Fin 36, ∑ j : Fin 36, orb0_Mt i.val j.val = 9 := fun i => by
      have ht : ∀ j : Fin 36, orb0_Mt i.val j.val =
          (if orb0_Mt i.val j.val = 1 then (1 : ℤ) else 0) - (if orb0_Mt i.val j.val = -1 then (1 : ℤ) else 0) := fun j => by
        rcases orb0_Mt_cases i j with h | h | h <;> simp [h]
      rw [Finset.sum_congr rfl fun j _ => ht j, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one,
          (orb0_spectral_spec.2.2.2 i).1, (orb0_spectral_spec.2.2.2 i).2]
      norm_num
    have hcol9 : ∀ j : Fin 36, ∑ i : Fin 36, orb0_Mt i.val j.val = 9 := fun j => by
      rw [Finset.sum_congr rfl fun i _ => orb0_Mt_symm i j]; exact hrow9 j
    have hSS_sum : ∑ i ∈ S, ∑ j ∈ S, orb0_Mt i.val j.val = (ePlus S : ℤ) - (eMinus S : ℤ) := by
      rw [← Finset.sum_product']
      have ht : ∀ ij : Fin 36 × Fin 36, orb0_Mt ij.1.val ij.2.val =
          (if orb0_Mt ij.1.val ij.2.val = 1 then (1 : ℤ) else 0) - (if orb0_Mt ij.1.val ij.2.val = -1 then (1 : ℤ) else 0) := fun ij => by
        rcases orb0_Mt_cases ij.1 ij.2 with h | h | h <;> simp [h]
      rw [Finset.sum_congr rfl fun ij _ => ht ij, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
    have hexp : ∑ i : Fin 36, ∑ j : Fin 36, orb0_Mt i.val j.val * y i * y j =
        324 - 36 * (S.card : ℤ) + 4 * ((ePlus S : ℤ) - (eMinus S : ℤ)) := by
      have hterm : ∀ i j : Fin 36, orb0_Mt i.val j.val * y i * y j =
          orb0_Mt i.val j.val -
          2 * (if i ∈ S then orb0_Mt i.val j.val else 0) -
          2 * (if j ∈ S then orb0_Mt i.val j.val else 0) +
          4 * (if i ∈ S ∧ j ∈ S then orb0_Mt i.val j.val else 0) := fun i j => by
        rw [hy_eq i, hy_eq j]; by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj] <;> ring
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have h1 : ∑ i : Fin 36, ∑ j : Fin 36, orb0_Mt i.val j.val = 324 := by
        rw [Finset.sum_congr rfl fun i _ => hrow9 i, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      have h2 : ∑ i : Fin 36, ∑ j : Fin 36, (if i ∈ S then orb0_Mt i.val j.val else 0) = 9 * (S.card : ℤ) := by
        have : ∀ i : Fin 36, ∑ j : Fin 36, (if i ∈ S then orb0_Mt i.val j.val else 0) = if i ∈ S then 9 else 0 := fun i => by
          by_cases hi : i ∈ S <;> simp [hi, hrow9 i]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : Finset.univ.filter (fun i : Fin 36 => i ∈ S) = S := by ext i; simp
        rw [this]; ring
      have h3 : ∑ i : Fin 36, ∑ j : Fin 36, (if j ∈ S then orb0_Mt i.val j.val else 0) = 9 * (S.card : ℤ) := by
        rw [Finset.sum_comm]
        have : ∀ j : Fin 36, ∑ i : Fin 36, (if j ∈ S then orb0_Mt i.val j.val else 0) = if j ∈ S then 9 else 0 := fun j => by
          by_cases hj : j ∈ S <;> simp [hj, hcol9 j]
        rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : Finset.univ.filter (fun j : Fin 36 => j ∈ S) = S := by ext j; simp
        rw [this]; ring
      have h4 : ∑ i : Fin 36, ∑ j : Fin 36, (if i ∈ S ∧ j ∈ S then orb0_Mt i.val j.val else 0) =
          (ePlus S : ℤ) - (eMinus S : ℤ) := by
        rw [← hSS_sum]
        have : ∀ i : Fin 36, ∑ j : Fin 36, (if i ∈ S ∧ j ∈ S then orb0_Mt i.val j.val else 0) =
            if i ∈ S then ∑ j ∈ S, orb0_Mt i.val j.val else 0 := fun i => by
          by_cases hi : i ∈ S
          · simp [hi, Finset.sum_filter]
          · simp [hi]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_filter]
        refine Finset.sum_congr (by ext i; simp) fun _ _ => rfl
      rw [h1, h2, h3, h4]; ring
    have h208 := hM0_lb s hs hAs hfAs
    rw [← hM0_y, hexp] at h208
    have hep_even : 2 ∣ ePlus S := card_even_of_symm_irrefl _
      (fun a b h => by simp only [Finset.mem_filter, Finset.mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, by rw [orb0_Mt_symm b a]; exact h.2⟩)
      (fun a h => by simp only [Finset.mem_filter, orb0_Mt, orb0_M0_eq_M36, M36_val, beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at h; omega)
    have hem_even : 2 ∣ eMinus S := card_even_of_symm_irrefl _
      (fun a b h => by simp only [Finset.mem_filter, Finset.mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, by rw [orb0_Mt_symm b a]; exact h.2⟩)
      (fun a h => by simp only [Finset.mem_filter, orb0_Mt, orb0_M0_eq_M36, M36_val, beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_mul] at h; omega)
    have hgoal : 9 * (S.card : ℤ) - 29 ≤ (ePlus S : ℤ) - (eMinus S : ℤ) := by omega
    exact ⟨hgoal, hep_even, hem_even⟩
  -- Unpack `checkOrb0Hits_ok`!
  have hhits := checkOrb0Hits_ok
  unfold checkOrb0Hits at hhits
  simp only [Bool.and_eq_true] at hhits
  rcases hhits with ⟨hblk9_hits, hcanon_hits⟩
  -- Split `k ≤ 5` vs `6 ≤ k ≤ 10`!
  let S1 := flipSet s1
  by_cases hk6 : 6 ≤ S1.card
  · -- 4. Case `6 ≤ k ≤ 10`: `4 × K_{3,3,3}` + `C₄`-free 3-regular bipartite bounds force whole 9-block!
    let B_of : Nat → Finset (Fin 36) := fun b => S1.filter fun i => orb0_blk.getD i.val 99 = b
    let s0 := (B_of 0).card; let s1c := (B_of 1).card; let s2 := (B_of 2).card; let s3c := (B_of 3).card
    have hblk_lt : ∀ b < 4, (B_of b).card ≤ 9 := fun b hb => by
      have hsub : B_of b ⊆ Finset.univ.filter (fun i : Fin 36 => orb0_blk.getD i.val 99 = b) :=
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      exact le_trans (Finset.card_le_card hsub) (le_of_eq (orb0_blocks_spec.2.1 ⟨b, hb⟩))
    have hsum_k : s0 + s1c + s2 + s3c = S1.card := by
      have hu : S1 = (B_of 0 ∪ B_of 1) ∪ (B_of 2 ∪ B_of 3) := by
        ext i; simp only [B_of, Finset.mem_union, Finset.mem_filter]
        have hlt := (orb0_blocks_spec.1 i).1
        constructor
        · intro hi
          have h0123 : orb0_blk.getD i.val 99 = 0 ∨ orb0_blk.getD i.val 99 = 1 ∨
              orb0_blk.getD i.val 99 = 2 ∨ orb0_blk.getD i.val 99 = 3 := by omega
          rcases h0123 with h | h | h | h
          · exact Or.inl (Or.inl ⟨hi, h⟩)
          · exact Or.inl (Or.inr ⟨hi, h⟩)
          · exact Or.inr (Or.inl ⟨hi, h⟩)
          · exact Or.inr (Or.inr ⟨hi, h⟩)
        · rintro ((⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)) <;> exact h
      have hd1 : Disjoint (B_of 0) (B_of 1) := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [B_of, Finset.mem_filter] at h1 h2; omega
      have hd2 : Disjoint (B_of 2) (B_of 3) := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [B_of, Finset.mem_filter] at h1 h2; omega
      have hd3 : Disjoint (B_of 0 ∪ B_of 1) (B_of 2 ∪ B_of 3) := Finset.disjoint_left.mpr fun _ h1 h2 => by
        simp only [B_of, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
      conv_rhs => rw [hu]
      rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
      dsimp only [s0, s1c, s2, s3c]; omega
    -- Bound `ePlus S1` by sum of 4 intra-blocks + 2 * 4 cross-blocks!
    let eCross : Nat → Nat → Nat := fun a b =>
      (((B_of a) ×ˢ (B_of b)).filter fun ij => orb0_Mt ij.1.val ij.2.val = 1).card
    have heCross_symm : ∀ a b, eCross a b = eCross b a := fun a b => by
      refine Finset.card_bij (fun ij _ => (ij.2, ij.1)) ?_ (fun _ _ _ _ h => Prod.ext (congr_arg Prod.snd h) (congr_arg Prod.fst h)) ?_
      · rintro ⟨i, j⟩ h; simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
        exact ⟨⟨h.1.2, h.1.1⟩, by rw [orb0_Mt_symm j i]; exact h.2⟩
      · rintro ⟨i, j⟩ h; refine ⟨(j, i), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
        exact ⟨⟨h.1.2, h.1.1⟩, by rw [orb0_Mt_symm j i]; exact h.2⟩
    have heCross_zero : eCross 0 1 = 0 ∧ eCross 1 0 = 0 ∧ eCross 2 3 = 0 ∧ eCross 3 2 = 0 := by
      have hz : ∀ a b, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) → eCross a b = 0 := by
        intro a b hab
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨i, j⟩ hij hmt
        simp only [B_of, Finset.mem_product, Finset.mem_filter] at hij
        have hno := (orb0_blocks_spec.2.2.1 i j hmt).2
        rw [hij.1.2, hij.2.2] at hno; exact hno hab
      exact ⟨hz 0 1 (by simp), hz 1 0 (by simp), hz 2 3 (by simp), hz 3 2 (by simp)⟩
    have hePlus_eq : ePlus S1 =
        eCross 0 0 + eCross 1 1 + eCross 2 2 + eCross 3 3 +
        2 * (eCross 0 2 + eCross 0 3 + eCross 1 2 + eCross 1 3) := by
      have hdecomp : ePlus S1 = ∑ a : Fin 4, ∑ b : Fin 4, eCross a.val b.val := by
        have hl : ePlus S1 = ∑ ij ∈ S1 ×ˢ S1, if orb0_Mt ij.1.val ij.2.val = 1 then 1 else 0 := by
          dsimp only [ePlus]; rw [Finset.card_filter]
        have hr : ∑ a : Fin 4, ∑ b : Fin 4, eCross a.val b.val =
            ∑ ij ∈ S1 ×ˢ S1, ∑ a : Fin 4, ∑ b : Fin 4,
              if orb0_blk.getD ij.1.val 99 = a.val ∧ orb0_blk.getD ij.2.val 99 = b.val ∧ orb0_Mt ij.1.val ij.2.val = 1
              then 1 else 0 := by
          have hc : ∀ a b : Fin 4, eCross a.val b.val =
              ∑ ij ∈ S1 ×ˢ S1,
                if orb0_blk.getD ij.1.val 99 = a.val ∧ orb0_blk.getD ij.2.val 99 = b.val ∧ orb0_Mt ij.1.val ij.2.val = 1
                then 1 else 0 := fun a b => by
            dsimp only [eCross, B_of]
            rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
            simp only [Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h1 : orb0_blk.getD i.val 99 = a.val
            · rw [if_pos h1]; refine Finset.sum_congr rfl fun j _ => ?_
              by_cases h2 : orb0_blk.getD j.val 99 = b.val <;> by_cases h3 : orb0_Mt i.val j.val = 1 <;>
                simp only [h1, h2, h3, ↓reduceIte, true_and, false_and, and_false, and_true]
            · rw [if_neg h1]; exact (Finset.sum_eq_zero fun j _ => by simp only [h1, false_and, ↓reduceIte]).symm
          rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hc a b]
          rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
        rw [hl, hr]
        refine Finset.sum_congr rfl fun ij _ => ?_
        let a0 : Fin 4 := ⟨orb0_blk.getD ij.1.val 99, (orb0_blocks_spec.1 ij.1).1⟩
        let b0 : Fin 4 := ⟨orb0_blk.getD ij.2.val 99, (orb0_blocks_spec.1 ij.2).1⟩
        rw [Finset.sum_eq_single a0]
        · rw [Finset.sum_eq_single b0]
          · simp [a0, b0]
          · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.2.1.symm)
          · intro h; exact absurd (Finset.mem_univ b0) h
        · intro a _ ha
          exact Finset.sum_eq_zero fun b _ => by
            rw [if_neg]; intro h; exact ha (Fin.ext h.1.symm)
        · intro h; exact absurd (Finset.mem_univ a0) h
      rw [hdecomp, Fin.sum_univ_four]
      simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl]
      rw [heCross_zero.1, heCross_zero.2.1, heCross_zero.2.2.1, heCross_zero.2.2.2,
          heCross_symm 2 0, heCross_symm 3 0, heCross_symm 2 1, heCross_symm 3 1]
      omega
    have hintra : ∀ b : Nat, eCross b b ≤ (2 * (B_of b).card * (B_of b).card) / 3 := fun b =>
      three_color_edge_bound (B_of b) (fun i => orb0_col3.getD i.val 99)
        (fun i _ => (orb0_blocks_spec.1 i).2)
        (fun i hi j hj hmt => (orb0_blocks_spec.2.2.1 i j hmt).1
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))
    have hcross : ∀ a b : Nat, (a, b) ∈ ([(0, 2), (0, 3), (1, 2), (1, 3)] : List (Nat × Nat)) →
        eCross a b ≤ bipBnd (B_of a).card (B_of b).card := by
      intro a b hab
      obtain ⟨hdA, hdB, hc4A, hc4B⟩ := orb0_blocks_spec.2.2.2.1 (a, b) hab
      have hsubA : B_of a ⊆ Finset.univ.filter fun i : Fin 36 => orb0_blk.getD i.val 99 = a :=
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      have hsubB : B_of b ⊆ Finset.univ.filter fun i : Fin 36 => orb0_blk.getD i.val 99 = b :=
        fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      refine bip_c4free_bound (B_of a) (B_of b)
        (fun u hu => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsubB)) (hdA u (hsubA hu)))
        (fun v hv => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsubA)) (hdB v (hsubB hv)))
        (fun u1 hu1 u2 hu2 hlt => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsubB)) (hc4A u1 (hsubA hu1) u2 (hsubA hu2) hlt))
        (fun v1 hv1 v2 hv2 hlt => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsubA)) (hc4B v1 (hsubB hv1) v2 (hsubB hv2) hlt))
    have henergy : 9 * (S1.card : ℤ) - 29 ≤ (ePlus S1 : ℤ) - (eMinus S1 : ℤ) := (hMt_energy s1 hs1 hA27_1 hfA1).1
    have hep_ge : 9 * S1.card - 29 ≤ ePlus S1 := by omega
    have hub_le : 9 * (s0 + s1c + s2 + s3c) - 29 ≤
        (2 * s0 * s0) / 3 + (2 * s1c * s1c) / 3 + (2 * s2 * s2) / 3 + (2 * s3c * s3c) / 3 +
        2 * (bipBnd s0 s2 + bipBnd s0 s3c + bipBnd s1c s2 + bipBnd s1c s3c) := by
      have hi0 := hintra 0; have hi1 := hintra 1; have hi2 := hintra 2; have hi3 := hintra 3
      have hc02 := hcross 0 2 (by simp); have hc03 := hcross 0 3 (by simp)
      have hc12 := hcross 1 2 (by simp); have hc13 := hcross 1 3 (by simp)
      rw [hsum_k]; dsimp only [s0, s1c, s2, s3c] at hi0 hi1 hi2 hi3 hc02 hc03 hc12 hc13 ⊢
      omega
    have h4cases := orb0_blocks_spec.2.2.2.2 s0 s1c s2 s3c
      (by have := hblk_lt 0 (by decide); omega) (by have := hblk_lt 1 (by decide); omega)
      (by have := hblk_lt 2 (by decide); omega) (by have := hblk_lt 3 (by decide); omega)
      (by omega) (by change S1.card ≤ 10 at hk_le10; omega) hub_le
    -- Extract the unique whole 9-block `b : Fin 4` and hit `orb0_blocks9[b]`!
    have hhit_blk : ∀ b : Fin 4, (B_of b.val).card = 9 → S1.card = 9 →
        ∃ (spId : Fin 42) (us : List (PauliIdx 3)),
          w5FrustEq (applyTransvWord us s3) (listToSign3 (sp42Certs spId).s64) := by
      intro b hb9 hS9
      let fullB := Finset.univ.filter fun i : Fin 36 => orb0_blk.getD i.val 99 = b.val
      have hB_eq_full : B_of b.val = fullB := Finset.eq_of_subset_of_card_le
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
        (by rw [hb9, orb0_blocks_spec.2.1 b])
      have hS1_eq : S1 = fullB := (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hb9, hS9])).symm.trans hB_eq_full
      let blkMask : Nat := (List.range 36).foldl (fun m i => if orb0_blk.getD i 99 == b.val then m ||| (1 <<< i) else m) 0
      have hbm_tb : ∀ i : Fin 36, blkMask.testBit i.val = true ↔ i ∈ S1 := fun i => by
        rw [hS1_eq]; dsimp only [blkMask, fullB]
        rw [foldl_or_bit_testBit]
        simp only [Nat.zero_testBit, Bool.false_or,
          List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨w, _, hw, hwi⟩ => hwi ▸ hw, fun h => ⟨i.val, i.isLt, h, rfl⟩⟩
      have hmask_s1 : ∀ i : Fin 36, s1 (dec3 (B36_pt i)) =
          orb0_u0 i.val * (if blkMask.testBit i.val = true then -1 else 1) := fun i => by
        have hu := orb0_u0_sq i
        by_cases htb : blkMask.testBit i.val = true
        · rw [if_pos htb]
          have hmem : i ∈ S1 := (hbm_tb i).mp htb
          have hneg : orb0_u0 i.val * s1 (dec3 (B36_pt i)) = -1 := (Finset.mem_filter.mp hmem).2
          calc s1 (dec3 (B36_pt i)) = (orb0_u0 i.val * orb0_u0 i.val) * s1 (dec3 (B36_pt i)) := by rw [hu, one_mul]
            _ = orb0_u0 i.val * (orb0_u0 i.val * s1 (dec3 (B36_pt i))) := by ring
            _ = orb0_u0 i.val * (-1) := by rw [hneg]
        · rw [if_neg htb]
          have hnot : i ∉ S1 := fun hm => htb ((hbm_tb i).mpr hm)
          have hne : orb0_u0 i.val * s1 (dec3 (B36_pt i)) ≠ -1 := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
          have hpos : orb0_u0 i.val * s1 (dec3 (B36_pt i)) = 1 := by
            rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hu' | hu' <;>
            rcases hs1.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hx' | hx' <;>
            simp [orb0_u0, hu', hx'] at hne ⊢
          calc s1 (dec3 (B36_pt i)) = (orb0_u0 i.val * orb0_u0 i.val) * s1 (dec3 (B36_pt i)) := by rw [hu, one_mul]
            _ = orb0_u0 i.val * (orb0_u0 i.val * s1 (dec3 (B36_pt i))) := by ring
            _ = orb0_u0 i.val * 1 := by rw [hpos]
      have hok_b := dpll_all_range hblk9_hits b.isLt
      have hbm_getD : ((List.range 4).map fun bb =>
          (List.range 36).foldl (fun m i => if orb0_blk.getD i 99 == bb then m ||| (1 <<< i) else m) 0).getD b.val 0 = blkMask := by
        dsimp only [blkMask]; exact dpll_getD_map_range 4 _ 0 b.isLt
      rw [hbm_getD] at hok_b
      obtain ⟨sp, us2, hfeq2⟩ := orb0_hit_of_mask hs1 hA27_1 hmask_s1 hok_b
      refine ⟨sp, us1 ++ us2, ?_⟩
      rw [applyTransvWord_append]
      exact w5FrustEq_trans (w5FrustEq_applyTransvWord us2 (w5FrustEq_symm hfeq1)) hfeq2
    rcases h4cases with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · exact hhit_blk ⟨0, by decide⟩ a (by omega)
    · exact hhit_blk ⟨1, by decide⟩ b (by omega)
    · exact hhit_blk ⟨2, by decide⟩ c (by omega)
    · exact hhit_blk ⟨3, by decide⟩ d (by omega)
  · -- 5. Case `k ≤ 5`: `V_TO_0` + pigeonhole + `checkOrb0K5Cover_ok` + `orb0_canonK5`!
    have hk5 : S1.card ≤ 5 := by omega
    have hcov_ok := checkOrb0K5Cover_ok
    unfold checkOrb0K5Cover at hcov_ok
    simp only [Bool.and_eq_true] at hcov_ok
    rcases hcov_ok with ⟨⟨⟨⟨⟨hcov0, hcov1⟩, hcov2⟩, hcov3⟩, hcov4⟩, hcov5⟩
    have hinv_ok := orb0_stabInvPerms_ok
    simp only [Bool.and_eq_true, beq_iff_eq] at hinv_ok
    rcases hinv_ok with ⟨hzip_len, hzip_all⟩
    -- Helper: if `orb0_isCovVs vs = true` for `s`'s flip-set vertex list `vs`, then `s` hits `sp42Certs`!
    have hhit_of_cov : ∀ (usA : List (PauliIdx 3)) (sA : PauliIdx 3 → ℤ) (vs : List Nat),
        IsSignAssign sA → w5FrustEq sA (applyTransvWord usA s3) →
        (∀ a : Fin 27, sA (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) →
        (∀ v ∈ vs, v < 36) →
        (∀ i : Fin 36, i.val ∈ vs ↔ i ∈ flipSet sA) →
        orb0_isCovVs vs = true →
        ∃ (spId : Fin 42) (us : List (PauliIdx 3)),
          w5FrustEq (applyTransvWord us s3) (listToSign3 (sp42Certs spId).s64) := by
      intro usA sA vs hsA hfeqA hAA hvs_lt hvs_iff hany
      unfold orb0_isCovVs at hany
      rcases List.any_eq_true.mp hany with ⟨invP, hinvP_mem, hbst⟩
      obtain ⟨idx, hidx_lt, hinvP_eq⟩ := List.getElem_of_mem hinvP_mem
      have hp_lt_len : idx < orb0_stabPerms.length := by omega
      let p := orb0_stabPerms[idx]
      have hpair_mem : (p, invP) ∈ List.zip orb0_stabPerms orb0_stabInvPerms := by
        rw [List.mem_iff_getElem]
        exact ⟨idx, by simp [hp_lt_len, hidx_lt], by simp [p, hinvP_eq]⟩
      have hpair_ok := List.all_eq_true.mp hzip_all (p, invP) hpair_mem
      simp only [Bool.and_eq_true, beq_iff_eq] at hpair_ok
      have hpinv : ∀ j < 36, p.getD j 0 < 36 ∧ invP.getD j 0 < 36 ∧
          p.getD (invP.getD j 0) 0 = j ∧ invP.getD (p.getD j 0) 0 = j := fun j hj => by
        have h1 := dpll_all_range hpair_ok.2 hj
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
        exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
      have hp_mem : p ∈ orb0_stabU00.filterMap fun (g, us) => orb0_checkStabU0 0 g us := by
        rw [orb0_stabPerms_eq]; exact List.getElem_mem hp_lt_len
      rcases List.mem_filterMap.mp hp_mem with ⟨⟨g, usP⟩, _, hchkP⟩
      obtain ⟨_, _, hpltP, _, sB, hsB, hfeqB, hAB, hB_rel⟩ := orb0_applyStabU0_step hsA hAA hchkP
      have hcont : (orb0_canonK5.map fun (m, _, _) => m).contains (applyInvPerm36 invP vs) = true :=
        natBST_mem_of_allIn orb0_canonBST_ok hbst
      rw [List.contains_eq_mem, decide_eq_true_eq] at hcont
      rcases List.mem_map.mp hcont with ⟨⟨mc, spId, usC⟩, hc_mem, hmc_eq⟩
      have hhitC := List.all_eq_true.mp hcanon_hits (mc, spId, usC) hc_mem
      have hmaskB : ∀ i : Fin 36, sB (dec3 (B36_pt i)) =
          orb0_u0 i.val * (if mc.testBit i.val = true then -1 else 1) := by
        intro i
        have htb : mc.testBit i.val = true ↔ i ∈ flipSet sB := by
          dsimp only at hmc_eq
          rw [hmc_eq, applyInvPerm36_testBit]
          have hp_lt := hpltP i
          have hmem_iff : (∃ v ∈ vs, invP.getD v 0 = i.val) ↔ p.getD i.val 0 ∈ vs := by
            constructor
            · rintro ⟨v, hv, hvi⟩
              have hv36 := hvs_lt v hv
              have heq : p.getD i.val 0 = v := by rw [← hvi]; exact (hpinv v hv36).2.2.1
              rwa [heq]
            · intro hmem
              exact ⟨p.getD i.val 0, hmem, (hpinv i.val i.isLt).2.2.2⟩
          rw [hmem_iff, hvs_iff ⟨p.getD i.val 0, hp_lt⟩]
          simp only [flipSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hB_rel i hp_lt]
        have hu := orb0_u0_sq i
        by_cases h1 : mc.testBit i.val = true
        · rw [if_pos h1]
          have hneg : orb0_u0 i.val * sB (dec3 (B36_pt i)) = -1 := (Finset.mem_filter.mp (htb.mp h1)).2
          calc sB (dec3 (B36_pt i)) = (orb0_u0 i.val * orb0_u0 i.val) * sB (dec3 (B36_pt i)) := by rw [hu, one_mul]
            _ = orb0_u0 i.val * (orb0_u0 i.val * sB (dec3 (B36_pt i))) := by ring
            _ = orb0_u0 i.val * (-1) := by rw [hneg]
        · rw [if_neg h1]
          have hnot : i ∉ flipSet sB := fun hm => h1 (htb.mpr hm)
          have hne : orb0_u0 i.val * sB (dec3 (B36_pt i)) ≠ -1 := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
          have hpos : orb0_u0 i.val * sB (dec3 (B36_pt i)) = 1 := by
            rcases orb0_spectral_spec.2.2.1 ⟨0, by decide⟩ i with hu' | hu' <;>
            rcases hsB.2 _ (Finset.mem_erase.mp (B36_pt_mem_nz i)).1 with hx' | hx' <;>
            simp [orb0_u0, hu', hx'] at hne ⊢
          calc sB (dec3 (B36_pt i)) = (orb0_u0 i.val * orb0_u0 i.val) * sB (dec3 (B36_pt i)) := by rw [hu, one_mul]
            _ = orb0_u0 i.val * (orb0_u0 i.val * sB (dec3 (B36_pt i))) := by ring
            _ = orb0_u0 i.val * 1 := by rw [hpos]
      obtain ⟨sp, us2, hfeq2⟩ := orb0_hit_of_mask hsB hAB hmaskB hhitC
      refine ⟨sp, usA ++ (word3FromNat usP ++ us2), ?_⟩
      rw [applyTransvWord_append, applyTransvWord_append]
      have hstep1 : w5FrustEq (applyTransvWord (word3FromNat usP) sA)
          (applyTransvWord (word3FromNat usP) (applyTransvWord usA s3)) :=
        w5FrustEq_applyTransvWord (word3FromNat usP) hfeqA
      exact w5FrustEq_trans (w5FrustEq_applyTransvWord us2 (w5FrustEq_symm (w5FrustEq_trans hfeqB hstep1))) hfeq2
    -- Helper: apply `V_TO_0[v]` to `s1` (`v ∈ S1`) to get `s2` with `0 ∈ flipSet s2`, `|flipSet s2| = |S1|`, and same `Mt`!
    have hmove_v0 : ∀ v ∈ S1, ∃ (us2 : List (PauliIdx 3)) (s2 : PauliIdx 3 → ℤ) (perm : List Nat),
        IsSignAssign s2 ∧ w5FrustEq s2 (applyTransvWord us2 s3) ∧
        (∀ a : Fin 27, s2 (dec3 (A27_pt a)) = rep27_val ⟨0, by decide⟩ a.val) ∧
        frustPairs (nzPts 3) s2 ≤ 92 * 6 ∧
        (⟨0, by decide⟩ : Fin 36) ∈ flipSet s2 ∧
        (flipSet s2).card = S1.card ∧
        (∀ i : Fin 36, ∀ hp : perm.getD i.val 0 < 36, i ∈ flipSet s2 ↔ ⟨perm.getD i.val 0, hp⟩ ∈ S1) ∧
        (∀ i : Fin 36, perm.getD i.val 0 < 36) ∧
        (∀ i j : Fin 36, perm.getD i.val 0 = perm.getD j.val 0 → i = j) ∧
        perm.getD 0 0 = v.val ∧
        (∀ i j : Fin 36, orb0_Mt i.val j.val = orb0_Mt (perm.getD i.val 0) (perm.getD j.val 0)) := by
      intro v hv
      have hok_v := dpll_all_range hvTo0_ok v.isLt
      rcases hv_eq : orb0_vTo0.getD v.val (0, []) with ⟨g, usV⟩
      rw [hv_eq] at hok_v
      cases hchk : orb0_checkStabU0 v.val g usV with
      | none => rw [hchk] at hok_v; simp at hok_v
      | some perm =>
        obtain ⟨hplen, hp0, hplt, hMt_pres, s2, hs2, hfeq2, hA2, hrel2⟩ := orb0_applyStabU0_step hs1 hA27_1 hchk
        have hp0' : perm.getD 0 0 = v.val := by
          have h0lt : 0 < perm.length := by omega
          have h1 : perm.getD 0 99 = perm[0] := dpll_getD_eq_getElem perm 99 h0lt
          have h2 : perm.getD 0 0 = perm[0] := dpll_getD_eq_getElem perm 0 h0lt
          omega
        have hiff : ∀ i : Fin 36, ∀ hp : perm.getD i.val 0 < 36, i ∈ flipSet s2 ↔ ⟨perm.getD i.val 0, hp⟩ ∈ S1 := by
          intro i hp; simp only [flipSet, S1, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hrel2 i hp]
        have h0in : (⟨0, by decide⟩ : Fin 36) ∈ flipSet s2 := by
          rw [hiff ⟨0, by decide⟩ (hplt ⟨0, by decide⟩)]
          convert hv using 1; exact Fin.ext hp0'
        have hpinj : ∀ i j : Fin 36, perm.getD i.val 0 = perm.getD j.val 0 → i = j := by
          unfold orb0_checkStabU0 at hchk
          cases hact : orb0_actionB36 g usV with
          | none => rw [hact] at hchk; simp at hchk
          | some ps =>
            rw [hact] at hchk; dsimp only at hchk; split_ifs at hchk
            · simp only [Option.some.injEq] at hchk; subst hchk
              exact (sound_orb0_actionB36 hact).2.2.2.2.2.1
        let f : Fin 36 → Fin 36 := fun i => ⟨perm.getD i.val 0, hplt i⟩
        have hsurj : Function.Surjective f :=
          Finite.injective_iff_surjective.mp (fun a b hab => hpinj a b (congr_arg Fin.val hab))
        have hcard : (flipSet s2).card = S1.card := by
          refine Finset.card_bij (fun i _ => f i)
            (fun i hi => (hiff i (hplt i)).mp hi)
            (fun a _ b _ hab => hpinj a b (congr_arg Fin.val hab))
            (fun y hy => by obtain ⟨i, hi⟩ := hsurj y; exact ⟨i, (hiff i (hplt i)).mpr (show f i ∈ S1 from hi.symm ▸ hy), hi⟩)
        have hfeq_tot : w5FrustEq s2 (applyTransvWord (us1 ++ word3FromNat usV) s3) := by
          rw [applyTransvWord_append]
          exact w5FrustEq_trans hfeq2 (w5FrustEq_applyTransvWord (word3FromNat usV) hfeq1)
        have hfA2 : frustPairs (nzPts 3) s2 ≤ 92 * 6 := by
          rw [frustPairs_of_w5FrustEq (by simp [nzPts]) hfeq_tot, frustPairs_nzPts_applyTransvWord]; exact hfA
        exact ⟨us1 ++ word3FromNat usV, s2, perm, hs2, hfeq_tot, hA2, hfA2, h0in, hcard, hiff, hplt, hpinj, hp0', hMt_pres⟩
    -- Helper for `np0` membership
    have hnp0_iff : ∀ v : Fin 36, 0 < v.val → orb0_Mt 0 v.val = 1 → ∃ idx : Fin 12, orb0_np0.getD idx.val 0 = v.val := by
      intro v hv0 hmt
      have hc := dpll_all_range hnp0_all v.isLt
      rw [orb0_Mt_fast_eq ⟨0, by decide⟩ v] at hc
      rw [if_pos (by simp [hv0, hmt])] at hc
      rw [List.contains_eq_mem, decide_eq_true_eq] at hc
      obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hc
      have hlen12 : orb0_np0.length = 12 := beq_iff_eq.mp hnp0_len
      exact ⟨⟨idx, by omega⟩, by rw [dpll_getD_eq_getElem _ _ hidx, heq]⟩
    have hnp0_strict : ∀ i j : Fin 12, i.val < j.val → orb0_np0.getD i.val 0 < orb0_np0.getD j.val 0 := by
      have hall : ((List.range 12).all fun a => (List.range 12).all fun b =>
          if a < b then orb0_np0.getD a 0 < orb0_np0.getD b 0 else true) = true := by decide
      intro i j hij
      have h := dpll_all_range (dpll_all_range hall i.isLt) j.isLt
      rw [if_pos hij] at h; exact decide_eq_true_eq.mp h
    have hMt_diag0 : ∀ i : Fin 36, orb0_Mt i.val i.val = 0 := fun i => by
      simp [orb0_Mt, orb0_M0_eq_M36, M36_val]
    have hsum_deg_eq : ∀ (S : Finset (Fin 36)),
        ∑ v ∈ S, ∑ w ∈ S, orb0_Mt v.val w.val = (ePlus S : ℤ) - (eMinus S : ℤ) := by
      intro S
      rw [← Finset.sum_product']
      have ht : ∀ ij : Fin 36 × Fin 36, orb0_Mt ij.1.val ij.2.val =
          (if orb0_Mt ij.1.val ij.2.val = 1 then (1 : ℤ) else 0) - (if orb0_Mt ij.1.val ij.2.val = -1 then (1 : ℤ) else 0) := fun ij => by
        rcases orb0_Mt_cases ij.1 ij.2 with h | h | h <;> simp [h]
      rw [Finset.sum_congr rfl fun ij _ => ht ij, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
    -- Dispatch `k ∈ {0, 1, 2, 3, 4, 5}`!
    rcases hkc : S1.card with _ | _ | _ | _ | _ | _ | n
    · -- k = 0
      have hemp : S1 = ∅ := Finset.card_eq_zero.mp hkc
      exact hhit_of_cov us1 s1 [] hs1 hfeq1 hA27_1 (by simp) (fun i => by simp [S1, hemp]) hcov0
    · -- k = 1
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hkc
      obtain ⟨us2, s2, _, hs2, hfeq2, hA2, _, h0in, hcard2, _, _, _, _, _⟩ := hmove_v0 v (hv ▸ by simp)
      have hS2 : flipSet s2 = {⟨0, by decide⟩} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr h0in) (by simp [hcard2, hkc])).symm
      exact hhit_of_cov us2 s2 [0] hs2 hfeq2 hA2 (by simp)
        (fun i => by rw [hS2]; simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton, Fin.ext_iff]) hcov1
    · -- k = 2
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
      obtain ⟨us2, s2, _, hs2, hfeq2, hA2, _, h0in, hcard2, _, _, _, _, _⟩ := hmove_v0 v hv
      have hrem : ((flipSet s2).erase ⟨0, by decide⟩).card = 1 := by
        rw [Finset.card_erase_of_mem h0in, hcard2, hkc]
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hrem
      have ha_mem : a ∈ (flipSet s2).erase ⟨0, by decide⟩ := ha ▸ by simp
      have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp ha_mem).1 (Fin.ext h))
      have hS2 : flipSet s2 = {⟨0, by decide⟩, a} := by
        rw [← Finset.insert_erase h0in, ha]
      have hc := dpll_all_range hcov2 (show a.val - 1 < 35 by have := a.isLt; omega)
      rw [show a.val - 1 + 1 = a.val by omega] at hc
      refine hhit_of_cov us2 s2 [0, a.val] hs2 hfeq2 hA2 (by simp [a.isLt]) (fun i => ?_) hc
      rw [hS2]; simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    · -- k = 3
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
      obtain ⟨us2, s2, _, hs2, hfeq2, hA2, _, h0in, hcard2, _, _, _, _, _⟩ := hmove_v0 v hv
      have hrem : ((flipSet s2).erase ⟨0, by decide⟩).card = 2 := by
        rw [Finset.card_erase_of_mem h0in, hcard2, hkc]
      obtain ⟨x, y, hxy, hxy_eq⟩ := Finset.card_eq_two.mp hrem
      have hord : ∃ a b : Fin 36, 0 < a.val ∧ a.val < b.val ∧ flipSet s2 = {⟨0, by decide⟩, a, b} := by
        have hx_mem : x ∈ (flipSet s2).erase ⟨0, by decide⟩ := by rw [hxy_eq]; simp
        have hy_mem : y ∈ (flipSet s2).erase ⟨0, by decide⟩ := by rw [hxy_eq]; simp
        have hx_ne0 : 0 < x.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hx_mem).1 (Fin.ext h))
        have hy_ne0 : 0 < y.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hy_mem).1 (Fin.ext h))
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hlt | hgt
        · exact ⟨x, y, hx_ne0, hlt, by rw [← Finset.insert_erase h0in, hxy_eq]⟩
        · exact ⟨y, x, hy_ne0, hgt, by rw [← Finset.insert_erase h0in, hxy_eq, Finset.pair_comm]⟩
      obtain ⟨a, b, ha0, hab, hS2⟩ := hord
      have hc := dpll_all_range (dpll_all_range hcov3 (show a.val - 1 < 35 by have := a.isLt; omega))
        (show b.val - (a.val + 1) < 35 - (a.val - 1 + 1) by have := b.isLt; omega)
      rw [show a.val - 1 + 1 = a.val by omega, show a.val + 1 + (b.val - (a.val + 1)) = b.val by omega] at hc
      refine hhit_of_cov us2 s2 [0, a.val, b.val] hs2 hfeq2 hA2 (by simp [a.isLt, b.isLt]) (fun i => ?_) hc
      rw [hS2]; simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    · -- k = 4: pigeonhole `∃ v ∈ S1` with `deg_{S1}(v) ≥ 2` ⇒ `0` has `≥ 2` `+1`-neighbors in `S2`!
      obtain ⟨he4, hep_ev, hem_ev⟩ := hMt_energy s1 hs1 hA27_1 hfA1
      rw [hkc] at he4
      have he8 : 8 ≤ (ePlus S1 : ℤ) - (eMinus S1 : ℤ) := by
        rcases hep_ev with ⟨p, hp⟩; rcases hem_ev with ⟨q, hq⟩; rw [hp, hq] at he4 ⊢; omega
      have hex_v : ∃ v ∈ S1, (2 : ℤ) ≤ ∑ w ∈ S1, orb0_Mt v.val w.val := by
        by_contra hno; push Not at hno
        have hle : ∑ v ∈ S1, ∑ w ∈ S1, orb0_Mt v.val w.val ≤ ∑ _v ∈ S1, (1 : ℤ) :=
          Finset.sum_le_sum fun v hv => by have := hno v hv; omega
        rw [hsum_deg_eq S1, Finset.sum_const, nsmul_eq_mul, mul_one, hkc] at hle; omega
      obtain ⟨v, hv, hv_deg⟩ := hex_v
      obtain ⟨us2, s2, perm, hs2, hfeq2, hA2, hfA2, h0in, hcard2, hiff, hplt, hpinj, hp0', hMt_pres⟩ := hmove_v0 v hv
      let S2 := flipSet s2
      have hdeg0 : (2 : ℤ) ≤ ∑ w ∈ S2, orb0_Mt 0 w.val := by
        let f : Fin 36 → Fin 36 := fun i => ⟨perm.getD i.val 0, hplt i⟩
        have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp (fun a b hab => hpinj a b (congr_arg Fin.val hab))
        have hsum_eq : ∑ w ∈ S2, orb0_Mt 0 w.val = ∑ w ∈ S1, orb0_Mt v.val w.val := by
          refine Finset.sum_bij (fun i _ => f i) (fun i hi => (hiff i (hplt i)).mp hi)
            (fun a _ b _ hab => hpinj a b (congr_arg Fin.val hab))
            (fun y hy => by obtain ⟨i, hi⟩ := hsurj y; exact ⟨i, (hiff i (hplt i)).mpr (show f i ∈ S1 from hi.symm ▸ hy), hi⟩)
            (fun i _ => by have h := hMt_pres ⟨0, by decide⟩ i; rw [hp0'] at h; exact h)
        rw [hsum_eq]; exact hv_deg
      -- At least 2 vertices in `S2 \ {0}` have `orb0_Mt 0 w = 1`!
      let P0 := (S2.erase ⟨0, by decide⟩).filter fun w => orb0_Mt 0 w.val = 1
      have hP0_ge2 : 2 ≤ P0.card := by
        have hsum_le : ∑ w ∈ S2, orb0_Mt 0 w.val ≤ (P0.card : ℤ) := by
          rw [← Finset.add_sum_erase _ _ h0in, hMt_diag0 ⟨0, by decide⟩, zero_add]
          calc ∑ w ∈ S2.erase ⟨0, by decide⟩, orb0_Mt 0 w.val
              ≤ ∑ w ∈ S2.erase ⟨0, by decide⟩, (if orb0_Mt 0 w.val = 1 then (1 : ℤ) else 0) :=
                Finset.sum_le_sum fun w _ => by rcases orb0_Mt_cases ⟨0, by decide⟩ w with h | h | h <;> simp [h]
            _ = (P0.card : ℤ) := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        omega
      obtain ⟨x, hx, y, hy, hxy_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < P0.card)
      have hord_ab : ∃ a b : Fin 36, a ∈ P0 ∧ b ∈ P0 ∧ a.val < b.val := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy_ne) with hlt | hgt
        · exact ⟨x, y, hx, hy, hlt⟩
        · exact ⟨y, x, hy, hx, hgt⟩
      obtain ⟨a, b, haP, hbP, hab_lt⟩ := hord_ab
      have haS : a ∈ S2.erase ⟨0, by decide⟩ := (Finset.mem_filter.mp haP).1
      have hbS : b ∈ S2.erase ⟨0, by decide⟩ := (Finset.mem_filter.mp hbP).1
      have haMt : orb0_Mt 0 a.val = 1 := (Finset.mem_filter.mp haP).2
      have hbMt : orb0_Mt 0 b.val = 1 := (Finset.mem_filter.mp hbP).2
      have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp haS).1 (Fin.ext h))
      have hb0 : 0 < b.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hbS).1 (Fin.ext h))
      have hrem1 : (((S2.erase ⟨0, by decide⟩).erase a).erase b).card = 1 := by
        have hb_in : b ∈ (S2.erase ⟨0, by decide⟩).erase a := Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), hbS⟩
        rw [Finset.card_erase_of_mem hb_in, Finset.card_erase_of_mem haS, Finset.card_erase_of_mem h0in, hcard2, hkc]
      obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hrem1
      have hc_mem : c ∈ ((S2.erase ⟨0, by decide⟩).erase a).erase b := hc_eq ▸ by simp
      have hc_neb : c ≠ b := (Finset.mem_erase.mp hc_mem).1
      have hc_nea : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_mem).2).1
      have hc_ne0 : c ≠ ⟨0, by decide⟩ := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc_mem).2).2).1
      have hc0 : 0 < c.val := Nat.pos_of_ne_zero (fun h => hc_ne0 (Fin.ext h))
      have hS2_eq : S2 = {⟨0, by decide⟩, a, b, c} := by
        have hb_in : b ∈ (S2.erase ⟨0, by decide⟩).erase a := Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), hbS⟩
        have h1 : (S2.erase ⟨0, by decide⟩).erase a = {b, c} := by rw [← Finset.insert_erase hb_in, hc_eq]
        have h2 : S2.erase ⟨0, by decide⟩ = {a, b, c} := by rw [← Finset.insert_erase haS, h1]
        dsimp only [S2]; rw [← Finset.insert_erase h0in]; exact congr_arg _ h2
      -- Compute `w3 ≥ 4` from `hMt_energy s2`!
      obtain ⟨he4', hep2, hem2⟩ := hMt_energy s2 hs2 hA2 hfA2
      rw [hcard2, hkc] at he4'
      have he8' : 8 ≤ (ePlus S2 : ℤ) - (eMinus S2 : ℤ) := by
        rcases hep2 with ⟨p, hp⟩; rcases hem2 with ⟨q, hq⟩; rw [hp, hq] at he4' ⊢; omega
      have hw3_eq : (ePlus S2 : ℤ) - (eMinus S2 : ℤ) =
          2 * (2 + orb0_Mt 0 c.val + orb0_Mt a.val b.val + orb0_Mt a.val c.val + orb0_Mt b.val c.val) := by
        rw [← hsum_deg_eq S2, hS2_eq]
        have h0a : (⟨0, by decide⟩ : Fin 36) ≠ a := Fin.ne_of_val_ne (show (0 : Nat) ≠ a.val by omega)
        have h0b : (⟨0, by decide⟩ : Fin 36) ≠ b := Fin.ne_of_val_ne (show (0 : Nat) ≠ b.val by omega)
        have h0c : (⟨0, by decide⟩ : Fin 36) ≠ c := hc_ne0.symm
        have hab_ne : a ≠ b := Fin.ne_of_val_ne (by omega)
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
          h0a, h0b, h0c, hab_ne, hc_nea.symm, hc_neb.symm, or_self, not_false_eq_true]
        rw [hMt_diag0 ⟨0, by decide⟩, hMt_diag0 a, hMt_diag0 b, hMt_diag0 c,
            orb0_Mt_symm a ⟨0, by decide⟩, orb0_Mt_symm b ⟨0, by decide⟩, orb0_Mt_symm c ⟨0, by decide⟩,
            orb0_Mt_symm b a, orb0_Mt_symm c a, orb0_Mt_symm c b,
            haMt, hbMt]
        ring
      have hw3_ge4 : 4 ≤ 2 + orb0_Mt 0 c.val + orb0_Mt a.val b.val + orb0_Mt a.val c.val + orb0_Mt b.val c.val := by omega
      obtain ⟨i1, hi1⟩ := hnp0_iff a ha0 haMt
      obtain ⟨i2, hi2⟩ := hnp0_iff b hb0 hbMt
      have hi12 : i1.val < i2.val := by
        by_contra hge
        rcases Nat.eq_or_lt_of_le (Nat.not_lt.mp hge) with heq | hgt
        · have : a.val = b.val := by rw [← hi1, ← hi2, heq]
          omega
        · have := hnp0_strict i2 i1 hgt; rw [hi1, hi2] at this; omega
      have hc4 := dpll_all_range (dpll_all_range (dpll_all_range hcov4 i1.isLt)
        (show i2.val - (i1.val + 1) < 11 - i1.val by have := i2.isLt; omega))
        (show c.val - 1 < 35 by have := c.isLt; omega)
      rw [show i1.val + 1 + (i2.val - (i1.val + 1)) = i2.val by omega, hi1, hi2,
          show c.val - 1 + 1 = c.val by omega] at hc4
      have hc_ne_b : (c.val == a.val || c.val == b.val) = false := by
        simp [Fin.val_ne_of_ne hc_nea, Fin.val_ne_of_ne hc_neb]
      rw [if_neg (by rw [hc_ne_b]; decide), orb0_Mt_fast_eq ⟨0, by decide⟩ c, orb0_Mt_fast_eq a b,
          orb0_Mt_fast_eq a c, orb0_Mt_fast_eq b c, if_pos hw3_ge4] at hc4
      refine hhit_of_cov us2 s2 [0, a.val, b.val, c.val] hs2 hfeq2 hA2
        (by simp [a.isLt, b.isLt, c.isLt]) (fun i => ?_) hc4
      change _ ↔ i ∈ S2; rw [hS2_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    · -- k = 5: pigeonhole `∃ v ∈ S1` with `deg_{S1}(v) ≥ 4` ⇒ ALL 4 other vertices in `S2` are in `np0`!
      obtain ⟨he5, hep_ev, hem_ev⟩ := hMt_energy s1 hs1 hA27_1 hfA1
      rw [hkc] at he5
      have he16 : 16 ≤ (ePlus S1 : ℤ) - (eMinus S1 : ℤ) := by
        change 9 * ((0 + 1 + 1 + 1 + 1 + 1 : Nat) : ℤ) - 29 ≤ (ePlus S1 : ℤ) - (eMinus S1 : ℤ) at he5; omega
      have hex_v : ∃ v ∈ S1, (4 : ℤ) ≤ ∑ w ∈ S1, orb0_Mt v.val w.val := by
        by_contra hno; push Not at hno
        have hle : ∑ v ∈ S1, ∑ w ∈ S1, orb0_Mt v.val w.val ≤ ∑ _v ∈ S1, (3 : ℤ) :=
          Finset.sum_le_sum fun v hv => by have := hno v hv; omega
        rw [hsum_deg_eq S1, Finset.sum_const, nsmul_eq_mul, hkc] at hle; omega
      obtain ⟨v, hv, hv_deg⟩ := hex_v
      obtain ⟨us2, s2, perm, hs2, hfeq2, hA2, hfA2, h0in, hcard2, hiff, hplt, hpinj, hp0', hMt_pres⟩ := hmove_v0 v hv
      let S2 := flipSet s2
      have hdeg0 : (4 : ℤ) ≤ ∑ w ∈ S2, orb0_Mt 0 w.val := by
        let f : Fin 36 → Fin 36 := fun i => ⟨perm.getD i.val 0, hplt i⟩
        have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp (fun a b hab => hpinj a b (congr_arg Fin.val hab))
        have hsum_eq : ∑ w ∈ S2, orb0_Mt 0 w.val = ∑ w ∈ S1, orb0_Mt v.val w.val := by
          refine Finset.sum_bij (fun i _ => f i) (fun i hi => (hiff i (hplt i)).mp hi)
            (fun a _ b _ hab => hpinj a b (congr_arg Fin.val hab))
            (fun y hy => by obtain ⟨i, hi⟩ := hsurj y; exact ⟨i, (hiff i (hplt i)).mpr (show f i ∈ S1 from hi.symm ▸ hy), hi⟩)
            (fun i _ => by have h := hMt_pres ⟨0, by decide⟩ i; rw [hp0'] at h; exact h)
        rw [hsum_eq]; exact hv_deg
      -- All 4 vertices in `S2 \ {0}` MUST have `orb0_Mt 0 w = 1`!
      have hall_np0 : ∀ w ∈ S2.erase ⟨0, by decide⟩, orb0_Mt 0 w.val = 1 := by
        intro w hw
        by_contra hne1
        have hle0 : orb0_Mt 0 w.val ≤ 0 := by
          have hc := orb0_Mt_cases ⟨0, by decide⟩ w
          change orb0_Mt 0 w.val = 0 ∨ orb0_Mt 0 w.val = 1 ∨ orb0_Mt 0 w.val = -1 at hc
          rcases hc with h | h | h <;> omega
        have hsum_le : ∑ u ∈ S2, orb0_Mt 0 u.val ≤ 3 := by
          rw [← Finset.add_sum_erase _ _ h0in, hMt_diag0 ⟨0, by decide⟩, zero_add, ← Finset.add_sum_erase _ _ hw]
          have hrest : ∑ u ∈ (S2.erase ⟨0, by decide⟩).erase w, orb0_Mt 0 u.val ≤
              ∑ _u ∈ (S2.erase ⟨0, by decide⟩).erase w, (1 : ℤ) :=
            Finset.sum_le_sum fun u _ => by
              have hc := orb0_Mt_cases ⟨0, by decide⟩ u
              change orb0_Mt 0 u.val = 0 ∨ orb0_Mt 0 u.val = 1 ∨ orb0_Mt 0 u.val = -1 at hc
              rcases hc with h | h | h <;> omega
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hw,
              Finset.card_erase_of_mem h0in, hcard2, hkc] at hrest
          omega
        omega
      -- Sort the 4 vertices in `S2 \ {0}` in ascending order `a < b < c < d`!
      let R4 := S2.erase ⟨0, by decide⟩
      have hR4_card : R4.card = 4 := by rw [Finset.card_erase_of_mem h0in, hcard2, hkc]
      have hsort4 : ∃ a b c d : Fin 36, a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧ R4 = {a, b, c, d} := by
        let L := R4.sort (· ≤ ·)
        have hL_len : L.length = 4 := by rw [Finset.length_sort, hR4_card]
        have hL_nd : L.Nodup := R4.sort_nodup (· ≤ ·)
        have hL_sorted : L.Pairwise (· ≤ ·) := R4.pairwise_sort (· ≤ ·)
        rcases hLeq : L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩ <;> simp [hLeq] at hL_len
        rw [hLeq] at hL_nd hL_sorted
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, List.nodup_cons] at hL_nd hL_sorted
        have hab : a.val < b.val := lt_of_le_of_ne hL_sorted.1.1 (fun h => hL_nd.1 (Or.inl (Fin.ext h)))
        have hbc : b.val < c.val := lt_of_le_of_ne hL_sorted.2.1.1 (fun h => hL_nd.2.1 (Or.inl (Fin.ext h)))
        have hcd : c.val < d.val := lt_of_le_of_ne hL_sorted.2.2.1 (fun h => hL_nd.2.2.1 (Fin.ext h))
        refine ⟨a, b, c, d, hab, hbc, hcd, ?_⟩
        ext w; rw [← Finset.mem_sort (r := (· ≤ ·))]; change w ∈ L ↔ _; rw [hLeq]; simp
      obtain ⟨a, b, c, d, hab, hbc, hcd, hR4_eq⟩ := hsort4
      have haR : a ∈ R4 := hR4_eq ▸ by simp
      have hbR : b ∈ R4 := hR4_eq ▸ by simp
      have hcR : c ∈ R4 := hR4_eq ▸ by simp
      have hdR : d ∈ R4 := hR4_eq ▸ by simp
      have ha0 : 0 < a.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp haR).1 (Fin.ext h))
      have hb0 : 0 < b.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hbR).1 (Fin.ext h))
      have hc0 : 0 < c.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hcR).1 (Fin.ext h))
      have hd0 : 0 < d.val := Nat.pos_of_ne_zero (fun h => (Finset.mem_erase.mp hdR).1 (Fin.ext h))
      have haMt : orb0_Mt 0 a.val = 1 := hall_np0 a haR
      have hbMt : orb0_Mt 0 b.val = 1 := hall_np0 b hbR
      have hcMt : orb0_Mt 0 c.val = 1 := hall_np0 c hcR
      have hdMt : orb0_Mt 0 d.val = 1 := hall_np0 d hdR
      have hS2_eq : S2 = {⟨0, by decide⟩, a, b, c, d} := by
        dsimp only [S2]; rw [← Finset.insert_erase h0in]; exact congr_arg _ hR4_eq
      obtain ⟨he5', _, _⟩ := hMt_energy s2 hs2 hA2 hfA2
      rw [hcard2, hkc] at he5'
      have hw4_eq : (ePlus S2 : ℤ) - (eMinus S2 : ℤ) =
          2 * (4 + orb0_Mt a.val b.val + orb0_Mt a.val c.val + orb0_Mt a.val d.val +
               orb0_Mt b.val c.val + orb0_Mt b.val d.val + orb0_Mt c.val d.val) := by
        rw [← hsum_deg_eq S2, hS2_eq]
        have h0a : (⟨0, by decide⟩ : Fin 36) ≠ a := Fin.ne_of_val_ne (show (0 : Nat) ≠ a.val by omega)
        have h0b : (⟨0, by decide⟩ : Fin 36) ≠ b := Fin.ne_of_val_ne (show (0 : Nat) ≠ b.val by omega)
        have h0c : (⟨0, by decide⟩ : Fin 36) ≠ c := Fin.ne_of_val_ne (show (0 : Nat) ≠ c.val by omega)
        have h0d : (⟨0, by decide⟩ : Fin 36) ≠ d := Fin.ne_of_val_ne (show (0 : Nat) ≠ d.val by omega)
        have hab' : a ≠ b := Fin.ne_of_val_ne (by omega)
        have hac' : a ≠ c := Fin.ne_of_val_ne (by omega)
        have had' : a ≠ d := Fin.ne_of_val_ne (by omega)
        have hbc' : b ≠ c := Fin.ne_of_val_ne (by omega)
        have hbd' : b ≠ d := Fin.ne_of_val_ne (by omega)
        have hcd' : c ≠ d := Fin.ne_of_val_ne (by omega)
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
          h0a, h0b, h0c, h0d, hab', hac', had', hbc', hbd', hcd', or_self, not_false_eq_true]
        rw [hMt_diag0 ⟨0, by decide⟩, hMt_diag0 a, hMt_diag0 b, hMt_diag0 c, hMt_diag0 d,
            orb0_Mt_symm a ⟨0, by decide⟩, orb0_Mt_symm b ⟨0, by decide⟩,
            orb0_Mt_symm c ⟨0, by decide⟩, orb0_Mt_symm d ⟨0, by decide⟩,
            orb0_Mt_symm b a, orb0_Mt_symm c a, orb0_Mt_symm d a,
            orb0_Mt_symm c b, orb0_Mt_symm d b, orb0_Mt_symm d c,
            haMt, hbMt, hcMt, hdMt]
        ring
      have hw4_ge8 : 8 ≤ 4 + orb0_Mt a.val b.val + orb0_Mt a.val c.val + orb0_Mt a.val d.val +
          orb0_Mt b.val c.val + orb0_Mt b.val d.val + orb0_Mt c.val d.val := by
        change 9 * ((0 + 1 + 1 + 1 + 1 + 1 : Nat) : ℤ) - 29 ≤ (ePlus S2 : ℤ) - (eMinus S2 : ℤ) at he5'
        omega
      obtain ⟨i1, hi1⟩ := hnp0_iff a ha0 haMt
      obtain ⟨i2, hi2⟩ := hnp0_iff b hb0 hbMt
      obtain ⟨i3, hi3⟩ := hnp0_iff c hc0 hcMt
      obtain ⟨i4, hi4⟩ := hnp0_iff d hd0 hdMt
      have hlt_idx : ∀ x y : Fin 12, orb0_np0.getD x.val 0 < orb0_np0.getD y.val 0 → x.val < y.val := by
        intro x y hxy; by_contra hge
        rcases Nat.eq_or_lt_of_le (Nat.not_lt.mp hge) with heq | hgt
        · rw [heq] at hxy; omega
        · have := hnp0_strict y x hgt; omega
      have hi12 : i1.val < i2.val := hlt_idx i1 i2 (by rw [hi1, hi2]; exact hab)
      have hi23 : i2.val < i3.val := hlt_idx i2 i3 (by rw [hi2, hi3]; exact hbc)
      have hi34 : i3.val < i4.val := hlt_idx i3 i4 (by rw [hi3, hi4]; exact hcd)
      have hc5 := dpll_all_range (dpll_all_range (dpll_all_range (dpll_all_range hcov5 i1.isLt)
        (show i2.val - (i1.val + 1) < 11 - i1.val by have := i2.isLt; omega))
        (show i3.val - (i2.val + 1) < 11 - (i1.val + 1 + (i2.val - (i1.val + 1))) by have := i3.isLt; omega))
        (show i4.val - (i3.val + 1) < 11 - ((i1.val + 1 + (i2.val - (i1.val + 1))) + 1 + (i3.val - (i2.val + 1))) by have := i4.isLt; omega)
      rw [show i1.val + 1 + (i2.val - (i1.val + 1)) = i2.val by omega,
          show i2.val + 1 + (i3.val - (i2.val + 1)) = i3.val by omega,
          show i3.val + 1 + (i4.val - (i3.val + 1)) = i4.val by omega,
          hi1, hi2, hi3, hi4,
          orb0_Mt_fast_eq a b, orb0_Mt_fast_eq a c, orb0_Mt_fast_eq a d,
          orb0_Mt_fast_eq b c, orb0_Mt_fast_eq b d, orb0_Mt_fast_eq c d,
          if_pos hw4_ge8] at hc5
      refine hhit_of_cov us2 s2 [0, a.val, b.val, c.val, d.val] hs2 hfeq2 hA2
        (by simp [a.isLt, b.isLt, c.isLt, d.isLt]) (fun i => ?_) hc5
      change _ ↔ i ∈ S2; rw [hS2_eq]; simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    · omega

end FourQubitCD

end MultiQubitMUB
