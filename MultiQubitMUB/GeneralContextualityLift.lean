import MultiQubitMUB.FourQubitUnconditionalMUB

/-!
# Universal Multi-Qubit Contextuality Density Lift (`n ≥ 4`, `ρₙ ≥ 5/17`) & General-`n` Triangle-Line Homomorphism

Establishes two general-`n` symplectic contextuality theorems (zero `sorry`, zero `native_decide`,
standard three Lean axioms `[propext, Classical.choice, Quot.sound]` only):

1. **Universal All-`n ≥ 4` Contextuality Density Upgrade (`frustPairs_ge_five_seventeenths`,
   `signCubeSum_le_seven_seventeenths`)**:
   By symplectic induction `n → n + 1` via double-counting over all ordered hyperbolic pairs
   `(u, v)` (`ω(u, v) = 1`) in `𝔽₂^{2(n+1)}` and explicit `Sp(2n+2, 2)` transvection transport
   `{u, v}⊥ ≃ W(2n-1, 2)`, lifts our unconditional 4-qubit bound `CD(W(7,2)) ≥ 1575` (`ρ₄ = 5/17`)
   to EVERY `n ≥ 4`:
   - `5 * ((2^(2n) - 1) * (2^(2n-1) - 2)) ≤ 17 * frustPairs (nzPts n) s`  (`CD(W(2n-1, 2)) ≥ (5/17) |L(W(2n-1, 2))|`),
   - `signCubeSum n σ ≤ (7/17) * ((2^(2n) - 1) * (2^(2n-1) - 2) / 2)`.
   This universally raises the unconditional multi-qubit Pauli contextuality frustration density
   from the 3-qubit bound `1/5 = 20%` to `5/17 ≈ 29.41%` for all `n ≥ 4`.

2. **General-`n` Exact Triangle-Line Homomorphism (`general_n_triangle_line_homomorphism`)**:
   For EVERY `n ≥ 1` and ANY pairwise commuting triple `b₁, b₂, b₃ : PauliIdx n` with differences
   `a₁ = b₁ + b₂`, `a₂ = b₂ + b₃`, the triangle cocycle on `Bₙ` equals the line cocycle on `Aₙ`:
     `gammaSgn b₁ b₂ * gammaSgn b₂ b₃ * gammaSgn b₁ b₃ = gammaSgn a₁ a₂`
   with ZERO exceptions in any dimension `n`.
-/

namespace MultiQubitMUB

open FourQubitCD

namespace GeneralContextualityLift

/-! ### Part 1: General-`n` Exact Triangle-Line Homomorphism (All `n`) -/

/-- **General-`n` Exact Triangle-Line Homomorphism (`ZMod 2` bit form)**:
    For ANY `n` and ANY pairwise commuting triple `b₁, b₂, b₃ : PauliIdx n`, setting
    `a₁ = b₁ + b₂` and `a₂ = b₂ + b₃`, the sum of triangle cocycle bits equals the line bit
    `gammaBit a₁ a₂` identically (zero exceptions in any dimension). -/
theorem general_n_triangle_line_bit {n : ℕ} (b₁ b₂ b₃ : PauliIdx n)
    (h12 : symp b₁ b₂ = 0) (h23 : symp b₂ b₃ = 0) (_h13 : symp b₁ b₃ = 0) :
    gammaBit b₁ b₂ + gammaBit b₂ b₃ + gammaBit b₁ b₃ = gammaBit (b₁ + b₂) (b₂ + b₃) := by
  have hsq2 : quadForm0 b₂ * quadForm0 b₂ + quadForm0 b₂ = 0 := by
    rcases zmod2_cases (quadForm0 b₂) with h | h
    · simp [h]
    · simp [h]; decide
  simp only [gammaBit, quadForm0_add, h12, h23, add_zero, Prod.fst_add, Prod.snd_add,
    dot_add_left, dot_add_right]
  have hdu2 : dot b₂.1 b₂.2 = quadForm0 b₂ := rfl
  rw [hdu2]
  calc (quadForm0 b₁ * quadForm0 b₂ + dot b₁.1 b₂.2) +
        (quadForm0 b₂ * quadForm0 b₃ + dot b₂.1 b₃.2) +
        (quadForm0 b₁ * quadForm0 b₃ + dot b₁.1 b₃.2)
      = (quadForm0 b₁ * quadForm0 b₂ + dot b₁.1 b₂.2) +
        (quadForm0 b₂ * quadForm0 b₃ + dot b₂.1 b₃.2) +
        (quadForm0 b₁ * quadForm0 b₃ + dot b₁.1 b₃.2) +
        (quadForm0 b₂ * quadForm0 b₂ + quadForm0 b₂) := by rw [hsq2, add_zero]
    _ = _ := by ring

/-- **General-`n` Exact Triangle-Line Homomorphism (`±1` sign form)**:
    For EVERY `n` and EVERY pairwise commuting triple `b₁, b₂, b₃ : PauliIdx n`,
      `gammaSgn b₁ b₂ * gammaSgn b₂ b₃ * gammaSgn b₁ b₃ = gammaSgn (b₁ + b₂) (b₂ + b₃)`. -/
theorem general_n_triangle_line_homomorphism {n : ℕ} (b₁ b₂ b₃ : PauliIdx n)
    (h12 : symp b₁ b₂ = 0) (h23 : symp b₂ b₃ = 0) (h13 : symp b₁ b₃ = 0) :
    gammaSgn b₁ b₂ * gammaSgn b₂ b₃ * gammaSgn b₁ b₃ = gammaSgn (b₁ + b₂) (b₂ + b₃) := by
  have hb := general_n_triangle_line_bit b₁ b₂ b₃ h12 h23 h13
  simp only [gammaSgn]
  rw [← hb]
  rcases zmod2_cases (gammaBit b₁ b₂) with h1 | h1 <;>
  rcases zmod2_cases (gammaBit b₂ b₃) with h2 | h2 <;>
  rcases zmod2_cases (gammaBit b₁ b₃) with h3 | h3 <;>
  simp [h1, h2, h3] <;> decide

/-! ### Part 2: Canonical Embedding `W(2n-1, 2) ↪ W(2n+1, 2)` & Transvection Transport -/

/-- Canonical embedding `PauliIdx n ↪ PauliIdx (n + 1)` zeroing the last qubit coordinate. -/
def embedLast {n : ℕ} (p : PauliIdx n) : PauliIdx (n + 1) :=
  (Fin.snoc p.1 0, Fin.snoc p.2 0)

/-- Projection `PauliIdx (n + 1) → PauliIdx n` dropping the last qubit coordinate. -/
def projInit {n : ℕ} (q : PauliIdx (n + 1)) : PauliIdx n :=
  (Fin.init q.1, Fin.init q.2)

/-- Canonical `X` basis vector on the last qubit `(e_last, 0) : PauliIdx (n + 1)`. -/
def eXLast (n : ℕ) : PauliIdx (n + 1) :=
  (fun i => if i = Fin.last n then 1 else 0, 0)

/-- Canonical `Z` basis vector on the last qubit `(0, e_last) : PauliIdx (n + 1)`. -/
def eZLast (n : ℕ) : PauliIdx (n + 1) :=
  (0, fun i => if i = Fin.last n then 1 else 0)

private lemma dot_snoc_zero {n : ℕ} (a b : F2 n) :
    dot (Fin.snoc a (0 : ZMod 2)) (Fin.snoc b (0 : ZMod 2)) = dot a b := by
  simp only [dot, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]

private lemma dot_eLast_left {n : ℕ} (v : F2 (n + 1)) :
    dot (fun i : Fin (n + 1) => if i = Fin.last n then (1 : ZMod 2) else 0) v = v (Fin.last n) := by
  simp only [dot]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma symp_eXLast {n : ℕ} (q : PauliIdx (n + 1)) :
    symp (eXLast n) q = q.2 (Fin.last n) := by
  simp [symp, eXLast, dot_eLast_left, dot_zero_left]

private lemma symp_eZLast {n : ℕ} (q : PauliIdx (n + 1)) :
    symp (eZLast n) q = q.1 (Fin.last n) := by
  simp [symp, eZLast, dot_zero_left, dot_eLast_left]

private lemma symp_eXLast_eZLast (n : ℕ) : symp (eXLast n) (eZLast n) = 1 := by
  rw [symp_eXLast]; simp [eZLast]

private lemma embedLast_zero {n : ℕ} : embedLast (0 : PauliIdx n) = 0 := by
  apply Prod.ext <;> ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [embedLast]

private lemma embedLast_add {n : ℕ} (p q : PauliIdx n) :
    embedLast (p + q) = embedLast p + embedLast q := by
  apply Prod.ext <;> ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [embedLast]

private lemma projInit_embedLast {n : ℕ} (p : PauliIdx n) : projInit (embedLast p) = p := by
  apply Prod.ext <;> ext j <;> simp [projInit, embedLast]

private lemma embedLast_inj {n : ℕ} {p q : PauliIdx n} (h : embedLast p = embedLast q) : p = q := by
  have := congr_arg projInit h
  rwa [projInit_embedLast, projInit_embedLast] at this

private lemma embedLast_projInit {n : ℕ} {q : PauliIdx (n + 1)}
    (h1 : q.1 (Fin.last n) = 0) (h2 : q.2 (Fin.last n) = 0) :
    embedLast (projInit q) = q := by
  apply Prod.ext <;> ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [embedLast, h1]
  · simp [embedLast, projInit, Fin.init]
  · simp [embedLast, h2]
  · simp [embedLast, projInit, Fin.init]

private lemma symp_embedLast {n : ℕ} (p q : PauliIdx n) :
    symp (embedLast p) (embedLast q) = symp p q := by
  simp only [symp, embedLast, dot_snoc_zero]

private lemma gammaSgn_embedLast {n : ℕ} (p q : PauliIdx n) :
    gammaSgn (embedLast p) (embedLast q) = gammaSgn p q := by
  dsimp only [gammaSgn, gammaBit, quadForm0, embedLast]
  simp only [dot_snoc_zero]
  rfl

private lemma mem_perp_eLast_iff {n : ℕ} (q : PauliIdx (n + 1)) :
    (symp (eXLast n) q = 0 ∧ symp (eZLast n) q = 0) ↔ ∃ p : PauliIdx n, embedLast p = q := by
  rw [symp_eXLast, symp_eZLast]
  constructor
  · rintro ⟨h2, h1⟩; exact ⟨projInit q, embedLast_projInit h1 h2⟩
  · rintro ⟨p, rfl⟩; simp [embedLast]

/-- Hyperbolic-pair complement `{u, v}⊥ \ {0}` in `PauliIdx m`. -/
def hypPerp {m : ℕ} (u v : PauliIdx m) : Finset (PauliIdx m) :=
  (nzPts m).filter fun p => symp u p = 0 ∧ symp v p = 0

/-- Restrict a sign assignment on `PauliIdx (n + 1)` to `PauliIdx n` via `embedLast`. -/
def restrictLast {n : ℕ} (s : PauliIdx (n + 1) → ℤ) : PauliIdx n → ℤ :=
  fun p => s (embedLast p)

private lemma restrictLast_isSignAssign {n : ℕ} {s : PauliIdx (n + 1) → ℤ} (hs : IsSignAssign s) :
    IsSignAssign (restrictLast s) := by
  refine ⟨by simp [restrictLast, embedLast_zero, hs.1], fun p hp => hs.2 (embedLast p) ?_⟩
  intro h; exact hp (embedLast_inj (h.trans embedLast_zero.symm))

private lemma frustPairs_hypPerp_eLast {n : ℕ} (s : PauliIdx (n + 1) → ℤ) :
    frustPairs (hypPerp (eXLast n) (eZLast n)) s = frustPairs (nzPts n) (restrictLast s) := by
  unfold frustPairs
  symm
  refine Finset.card_bij (fun pq _ => (embedLast pq.1, embedLast pq.2)) ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, hypPerp, Finset.mem_erase,
      Finset.mem_univ, and_true] at hpq ⊢
    rcases hpq with ⟨⟨hp0, hq0⟩, hne, hsymp, hfr⟩
    refine ⟨⟨⟨fun h => hp0 (embedLast_inj (h.trans embedLast_zero.symm)),
              (mem_perp_eLast_iff _).mpr ⟨p, rfl⟩⟩,
             ⟨fun h => hq0 (embedLast_inj (h.trans embedLast_zero.symm)),
              (mem_perp_eLast_iff _).mpr ⟨q, rfl⟩⟩⟩,
            fun h => hne (embedLast_inj h), by rwa [symp_embedLast], ?_⟩
    rw [gammaSgn_embedLast, ← embedLast_add]; exact hfr
  · rintro ⟨p1, q1⟩ _ ⟨p2, q2⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (embedLast_inj h.1) (embedLast_inj h.2)
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, hypPerp, Finset.mem_erase,
      Finset.mem_univ, and_true] at hab
    rcases hab with ⟨⟨⟨ha0, haP⟩, ⟨hb0, hbP⟩⟩, hne, hsymp, hfr⟩
    obtain ⟨p, rfl⟩ := (mem_perp_eLast_iff a).mp haP
    obtain ⟨q, rfl⟩ := (mem_perp_eLast_iff b).mp hbP
    refine ⟨(p, q), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, nzPts, Finset.mem_erase,
      Finset.mem_univ, and_true]
    refine ⟨⟨fun h => ha0 (by rw [h, embedLast_zero]),
             fun h => hb0 (by rw [h, embedLast_zero])⟩,
            fun h => hne (by rw [h]), by rwa [symp_embedLast] at hsymp, ?_⟩
    rw [gammaSgn_embedLast, ← embedLast_add] at hfr; exact hfr

/-- Apply a list of transvections to a point `x : PauliIdx m` (right-to-left dual to `applyTransvWord`). -/
def transvWordPt {m : ℕ} : List (PauliIdx m) → PauliIdx m → PauliIdx m
  | [], x => x
  | u :: us, x => transvPt u (transvWordPt us x)

private lemma transvWordPt_zero {m : ℕ} (us : List (PauliIdx m)) : transvWordPt us 0 = 0 := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [transvWordPt, ih, transvPt_zero]

private lemma symp_transvWordPt {m : ℕ} (us : List (PauliIdx m)) (x y : PauliIdx m) :
    symp (transvWordPt us x) (transvWordPt us y) = symp x y := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [transvWordPt, symp_transvPt, ih]

private lemma frustPairs_applyTransvWord_hypPerp {m : ℕ} (us : List (PauliIdx m))
    (u v : PauliIdx m) (s : PauliIdx m → ℤ) :
    frustPairs (hypPerp u v) (applyTransvWord us s) =
      frustPairs (hypPerp (transvWordPt us u) (transvWordPt us v)) s := by
  induction us generalizing u v s with
  | nil => rfl
  | cons w ws ih =>
    simp only [applyTransvWord, transvWordPt]
    rw [ih]
    -- Wait: check order! `applyTransvWord (w :: ws) s = applyTransvWord ws (applyTransv w s)`.
    -- By `ih`: `frustPairs (hypPerp u v) (applyTransvWord ws (applyTransv w s)) = frustPairs (hypPerp (transvWordPt ws u) (transvWordPt ws v)) (applyTransv w s)`.
    refine frustPairs_applyTransv w _ _ (fun p => ?_) s
    simp only [hypPerp, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hp0, h1, h2⟩
      refine ⟨fun h => hp0 (by rw [← transvPt_invol w p, h, transvPt_zero]), ?_, ?_⟩
      · rw [symp_transvPt]; exact h1
      · rw [symp_transvPt]; exact h2
    · rintro ⟨ht0, h1, h2⟩
      refine ⟨fun h => ht0 (by rw [h, transvPt_zero]), ?_, ?_⟩
      · rw [← symp_transvPt w]; exact h1
      · rw [← symp_transvPt w]; exact h2

/-- Existence of an anticommuting partner for any nonzero vector in `PauliIdx m`. -/
private lemma exists_symp_one {m : ℕ} {x : PauliIdx m} (hx : x ≠ 0) :
    ∃ z : PauliIdx m, symp x z = 1 := by
  by_contra hall; push Not at hall
  have hzero : ∀ z : PauliIdx m, symp x z = 0 := fun z =>
    (zmod2_cases (symp x z)).resolve_right (hall z)
  apply hx
  apply Prod.ext <;> ext i
  · have h := hzero (0, fun j => if j = i then 1 else 0)
    simp only [symp, dot_zero_right, dot] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj; simp [hj]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · have h := hzero (fun j => if j = i then 1 else 0, 0)
    simp only [symp, dot_zero_right, dot] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj; simp [hj]
    · intro hm; exact absurd (Finset.mem_univ _) hm

/-- Every nonzero `x` can be mapped to any nonzero `u` by at most 2 symplectic transvections! -/
private lemma exists_transvWord_pt {m : ℕ} {x u : PauliIdx m} (hx : x ≠ 0) (hu : u ≠ 0) :
    ∃ us : List (PauliIdx m), transvWordPt us x = u := by
  by_cases hxu : x = u
  · exact ⟨[], hxu⟩
  · rcases zmod2_cases (symp x u) with hs | hs
    · -- `symp x u = 0`, `x ≠ u`, both nonzero: find `w` with `symp x w = 1` and `symp u w = 1`!
      obtain ⟨z1, hz1⟩ := exists_symp_one hx
      rcases zmod2_cases (symp u z1) with huz1 | huz1
      · obtain ⟨z2, hz2⟩ := exists_symp_one hu
        rcases zmod2_cases (symp x z2) with hxz2 | hxz2
        · -- `w = z1 + z2` has `symp x w = 1` and `symp u w = 1`!
          let w := z1 + z2
          have hxw : symp x w = 1 := by rw [symp_add_right, hz1, hxz2, add_zero]
          have huw : symp u w = 1 := by rw [symp_add_right, huz1, hz2, zero_add]
          refine ⟨[w + u, x + w], ?_⟩
          have h1 : symp (x + w) x = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm, hxw]
          have h2 : symp (w + u) w = 1 := by rw [symp_add_left, symp_self, zero_add, huw]
          have hs1 : x + (x + w) = w := pauliIdx_add_cancel_left x w
          simp only [transvWordPt, transvPt, h1, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, hs1, h2]
          exact pauliIdx_add_cancel_left w u
        · refine ⟨[z2 + u, x + z2], ?_⟩
          have h1 : symp (x + z2) x = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm, hxz2]
          have h2 : symp (z2 + u) z2 = 1 := by rw [symp_add_left, symp_self, zero_add, hz2]
          have hs1 : x + (x + z2) = z2 := pauliIdx_add_cancel_left x z2
          simp only [transvWordPt, transvPt, h1, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, hs1, h2]
          exact pauliIdx_add_cancel_left z2 u
      · refine ⟨[z1 + u, x + z1], ?_⟩
        have h1 : symp (x + z1) x = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm, hz1]
        have h2 : symp (z1 + u) z1 = 1 := by rw [symp_add_left, symp_self, zero_add, huz1]
        have hs1 : x + (x + z1) = z1 := pauliIdx_add_cancel_left x z1
        simp only [transvWordPt, transvPt, h1, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, hs1, h2]
        exact pauliIdx_add_cancel_left z1 u
    · -- `symp x u = 1`: single transvection `[x + u]`!
      refine ⟨[x + u], ?_⟩
      have h1 : symp (x + u) x = 1 := by rw [symp_add_left, symp_self, zero_add, symp_comm, hs]
      simp only [transvWordPt, transvPt, h1, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
      calc x + (x + u) = (x + x) + u := by abel
        _ = u := by simp [pauliIdx_add_self]

/-- **Transitivity of `Sp(2m, 2)` Transvections on Ordered Hyperbolic Pairs** (`∀ m`):
    For any two hyperbolic pairs `(x, y)` and `(u, v)` (`symp x y = 1`, `symp u v = 1`),
    there exists a word `us` of at most 4 transvections mapping `(x, y) ↦ (u, v)`. -/
lemma exists_transvWord_hypPair {m : ℕ} {x y u v : PauliIdx m}
    (hxy : symp x y = 1) (huv : symp u v = 1) :
    ∃ us : List (PauliIdx m), transvWordPt us x = u ∧ transvWordPt us y = v := by
  have hx0 : x ≠ 0 := fun h => by rw [h, symp_zero_left] at hxy; exact absurd hxy (by decide)
  have hu0 : u ≠ 0 := fun h => by rw [h, symp_zero_left] at huv; exact absurd huv (by decide)
  obtain ⟨us1, hus1⟩ := exists_transvWord_pt hx0 hu0
  let v' := transvWordPt us1 y
  have huv' : symp u v' = 1 := by rw [← hus1]; simp only [v', symp_transvWordPt, hxy]
  by_cases hvv : v' = v
  · exact ⟨us1, hus1, hvv⟩
  · rcases zmod2_cases (symp v' v) with hs | hs
    · -- `symp v' v = 0`: apply `T_u` then `T_{v' + v + u}`! (Notice `transvWordPt [a, b] z = T_a (T_b z)`!)
      let w := v' + v + u
      have hwu : symp w u = 0 := by
        simp only [w, symp_add_left, symp_self, add_zero, symp_comm v' u, symp_comm v u, huv', huv]
        decide
      have hwvu : symp w (v' + u) = 1 := by
        simp only [w, symp_add_left, symp_add_right, symp_self, add_zero, zero_add,
          hs, symp_comm v v', symp_comm v' u, symp_comm v u, huv', huv]
        decide
      have huu : symp u u = 0 := symp_self u
      refine ⟨[w, u] ++ us1, ?_, ?_⟩
      · simp only [List.cons_append, List.nil_append, transvWordPt, hus1, transvPt, huu, hwu, ↓reduceIte]
      · simp only [List.cons_append, List.nil_append, transvWordPt, show transvWordPt us1 y = v' from rfl,
          transvPt, huv', hwvu, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
        simp only [w]
        calc v' + u + (v' + v + u) = (v' + v') + (u + u) + v := by abel
          _ = v := by simp [pauliIdx_add_self]
    · -- `symp v' v = 1`: single transvection `[v' + v]` fixes `u` and sends `v' ↦ v`!
      have hwu : symp (v' + v) u = 0 := by
        rw [symp_add_left, symp_comm v' u, symp_comm v u, huv', huv]; decide
      have hwv' : symp (v' + v) v' = 1 := by
        rw [symp_add_left, symp_self, zero_add, symp_comm, hs]
      refine ⟨(v' + v) :: us1, ?_, ?_⟩
      · simp only [transvWordPt, hus1, transvPt, hwu, ↓reduceIte]
      · simp only [transvWordPt, show transvWordPt us1 y = v' from rfl, transvPt, hwv',
          show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte]
        calc v' + (v' + v) = (v' + v') + v := by abel
          _ = v := by simp [pauliIdx_add_self]

/-! ### Part 3: Exact Counting of Hyperbolic Pairs in `PauliIdx m` & `{p, q}⊥` -/

private lemma card_symp_zero_single {m : ℕ} {x : PauliIdx m} (hx : x ≠ 0) :
    (Finset.univ.filter fun z : PauliIdx m => symp x z = 0).card = 2 ^ (2 * m - 1) := by
  obtain ⟨w, hw⟩ := exists_symp_one hx
  have hdisj : Disjoint (Finset.univ.filter fun z : PauliIdx m => symp x z = 0)
      (Finset.univ.filter fun z : PauliIdx m => symp x z = 1) := by
    rw [Finset.disjoint_left]; intro z h0 h1
    simp only [Finset.mem_filter] at h0 h1; rw [h0.2] at h1; exact absurd h1.2 (by decide)
  have hunion : (Finset.univ.filter fun z : PauliIdx m => symp x z = 0) ∪
      (Finset.univ.filter fun z : PauliIdx m => symp x z = 1) = Finset.univ := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod2_cases (symp x z)
  have heq : (Finset.univ.filter fun z : PauliIdx m => symp x z = 0).card =
      (Finset.univ.filter fun z : PauliIdx m => symp x z = 1).card := by
    refine Finset.card_bij (fun z _ => z + w) ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [symp_add_right, hz, hw, zero_add]
    · intro z1 _ z2 _ h; have := congr_arg (· + w) h; simpa [pauliIdx_add_cancel_right] using this
    · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨z + w, ?_, by rw [pauliIdx_add_cancel_right]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [symp_add_right, hz, hw]; decide
  have htot : (Finset.univ : Finset (PauliIdx m)).card = 2 ^ (2 * m) := by
    rw [Finset.card_univ, card_PauliIdx, ← pow_add, ← two_mul]
  have hm1 : 1 ≤ m := by
    by_contra h0; push Not at h0
    have hm0 : m = 0 := by omega
    subst hm0; apply hx; apply Prod.ext <;> ext i <;> exact Fin.elim0 i
  have h2m : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    nth_rw 1 [show 2 * m = (2 * m - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, htot, h2m, ← heq] at hcard; omega

private lemma card_symp_one_single {m : ℕ} {x : PauliIdx m} (hx : x ≠ 0) :
    (Finset.univ.filter fun z : PauliIdx m => symp x z = 1).card = 2 ^ (2 * m - 1) := by
  have h0 := card_symp_zero_single hx
  have hdisj : Disjoint (Finset.univ.filter fun z : PauliIdx m => symp x z = 0)
      (Finset.univ.filter fun z : PauliIdx m => symp x z = 1) := by
    rw [Finset.disjoint_left]; intro z h0 h1
    simp only [Finset.mem_filter] at h0 h1; rw [h0.2] at h1; exact absurd h1.2 (by decide)
  have hunion : (Finset.univ.filter fun z : PauliIdx m => symp x z = 0) ∪
      (Finset.univ.filter fun z : PauliIdx m => symp x z = 1) = Finset.univ := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod2_cases (symp x z)
  have htot : (Finset.univ : Finset (PauliIdx m)).card = 2 ^ (2 * m) := by
    rw [Finset.card_univ, card_PauliIdx, ← pow_add, ← two_mul]
  have hm1 : 1 ≤ m := by
    by_contra h0'; push Not at h0'
    have hm0 : m = 0 := by omega
    subst hm0; apply hx; apply Prod.ext <;> ext i <;> exact Fin.elim0 i
  have h2m : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    nth_rw 1 [show 2 * m = (2 * m - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, htot, h2m, h0] at hcard; omega

/-- Total ordered hyperbolic pairs `(u, v)` (`symp u v = 1`) in `PauliIdx (n + 1)`. -/
private lemma card_all_hypPairs (n : ℕ) :
    ((Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter
      fun uv => symp uv.1 uv.2 = 1).card = (2 ^ (2 * n + 2) - 1) * 2 ^ (2 * n + 1) := by
  have hbij : ((Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter
      fun uv => symp uv.1 uv.2 = 1).card =
      ∑ u ∈ nzPts (n + 1), (Finset.univ.filter fun v : PauliIdx (n + 1) => symp u v = 1).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun uv _ => ⟨uv.1, uv.2⟩) ?_ ?_ ?_
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv
      have hu0 : u ≠ 0 := fun h => by rw [h, symp_zero_left] at huv; exact absurd huv (by decide)
      simp only [Finset.mem_sigma, nzPts, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true]
      exact ⟨hu0, huv⟩
    · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_sigma, nzPts, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at huv
      exact ⟨(u, v), by simp [huv.2], rfl⟩
  rw [hbij]
  have hterm : ∀ u ∈ nzPts (n + 1),
      (Finset.univ.filter fun v : PauliIdx (n + 1) => symp u v = 1).card = 2 ^ (2 * n + 1) := by
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have h := card_symp_one_single hu0
    rwa [show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at h
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hnz : (nzPts (n + 1)).card = 2 ^ (2 * n + 2) - 1 := by
    rw [nzPts, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_PauliIdx, ← pow_add]
    congr 1; congr 1; omega
  rw [hnz]

/-- Number of ordered hyperbolic pairs `(u, v)` inside `{p, q}⊥` for any distinct nonzero commuting `p, q`
    in `PauliIdx (n + 1)` (`n ≥ 1`): ALWAYS `(2^(2n) - 4) * 2^(2n - 1)`, independent of `(p, q)`! -/
private lemma card_hypPairs_in_perp {n : ℕ} (hn : 1 ≤ n) {p q : PauliIdx (n + 1)}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) (hspq : symp p q = 0) :
    ((Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter
      fun uv => symp uv.1 uv.2 = 1 ∧ symp uv.1 p = 0 ∧ symp uv.2 p = 0 ∧
        symp uv.1 q = 0 ∧ symp uv.2 q = 0).card =
      (2 ^ (2 * n) - 4) * 2 ^ (2 * n - 1) := by
  -- Use `Sp(2n+2, 2)` transvection transport to move `p ↦ eX_0` and `q ↦ eX_1`?
  -- Even simpler: direct character-orthogonality / subspace counting on `S := {u | symp p u = 0 ∧ symp q u = 0}`!
  let S : Finset (PauliIdx (n + 1)) := Finset.univ.filter fun u => symp p u = 0 ∧ symp q u = 0
  let R : Finset (PauliIdx (n + 1)) := {0, p, q, p + q}
  have hpq0 : p + q ≠ 0 := fun h => hpq (by
    have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
  have hR_card : R.card = 4 := by
    have h1 : (0 : PauliIdx (n + 1)) ∉ ({p, q, p + q} : Finset _) := by
      simp [hp.symm, hq.symm, hpq0.symm]
    have h2 : p ∉ ({q, p + q} : Finset _) := by
      simp [hpq, show p ≠ p + q from fun h => hq (by
        have := congr_arg (p + ·) h; simpa [pauliIdx_add_cancel_left, pauliIdx_add_self] using this.symm)]
    have h3 : q ∉ ({p + q} : Finset _) := by
      simp [show q ≠ p + q from fun h => hp (by
        have := congr_arg (· + q) h; simpa [pauliIdx_add_cancel_right, pauliIdx_add_self] using this.symm)]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hR_sub : R ⊆ S := by
    intro u hu
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hu
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hu with hu | hu | hu | hu <;> rw [hu]
    · simp [symp_zero_right]
    · exact ⟨symp_self p, by rw [symp_comm]; exact hspq⟩
    · exact ⟨hspq, symp_self q⟩
    · exact ⟨by rw [symp_add_right, symp_self, hspq, zero_add],
             by rw [symp_add_right, symp_comm, hspq, symp_self, add_zero]⟩
  -- Compute `|S| = 2^(2n)` by character sum `∑_z (1 + sympSign p z) * (1 + sympSign q z) = 4 * |S|`!
  have hS_card : S.card = 2 ^ (2 * n) := by
    have hind : ∀ z : PauliIdx (n + 1),
        (if symp p z = 0 ∧ symp q z = 0 then (4 : ℤ) else 0) =
        (1 + sympSign p z) * (1 + sympSign q z) := by
      intro z; simp only [sympSign]
      rcases zmod2_cases (symp p z) with h1 | h1 <;> rcases zmod2_cases (symp q z) with h2 | h2 <;>
        simp [h1, h2]
    have hsum : (4 : ℤ) * (S.card : ℤ) = ∑ z : PauliIdx (n + 1), (1 + sympSign p z) * (1 + sympSign q z) := by
      simp_rw [← hind, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      ring
    have hexp : ∑ z : PauliIdx (n + 1), (1 + sympSign p z) * (1 + sympSign q z) =
        (2 : ℤ) ^ (2 * n + 2) := by
      have hrewrite : ∀ z : PauliIdx (n + 1),
          (1 + sympSign p z) * (1 + sympSign q z) =
          1 + sympSign p z + sympSign q z + sympSign (p + q) z := fun z => by
        rw [sympSign_add_left]; ring
      simp_rw [hrewrite, Finset.sum_add_distrib]
      have hsum_sign : ∀ a : PauliIdx (n + 1), a ≠ 0 → ∑ z : PauliIdx (n + 1), sympSign a z = 0 := by
        intro a ha
        obtain ⟨w, hw⟩ := exists_symp_one ha
        have hshift : ∑ z : PauliIdx (n + 1), sympSign a z = ∑ z : PauliIdx (n + 1), sympSign a (z + w) :=
          (Fintype.sum_equiv (Equiv.addRight w) _ _ fun _ => rfl).symm
        have hneg : ∀ z : PauliIdx (n + 1), sympSign a (z + w) = -sympSign a z := fun z => by
          rw [sympSign_add_right]; simp [sympSign, hw, show (1 : ZMod 2) ≠ 0 by decide]
        simp_rw [hneg, Finset.sum_neg_distrib] at hshift
        linarith
      rw [hsum_sign p hp, hsum_sign q hq, hsum_sign (p + q) hpq0, add_zero, add_zero, add_zero,
          Finset.sum_const, Finset.card_univ, card_PauliIdx, nsmul_eq_mul, mul_one]
      push_cast; rw [← pow_add]; congr 1; omega
    have h4 : (4 : ℤ) * (S.card : ℤ) = (4 : ℤ) * (2 : ℤ) ^ (2 * n) := by
      rw [hsum, hexp, pow_add]; ring
    have hZ : (S.card : ℤ) = (2 : ℤ) ^ (2 * n) := by linarith
    exact_mod_cast hZ
  -- For any `u ∈ S`:
  -- • if `u ∈ R`, `symp u v = 0` for ALL `v ∈ S` (0 partners in `S`);
  -- • if `u ∈ S \ R`, `∃ v₀ ∈ S, symp u v₀ = 1` (by character sum on `S`!), hence EXACTLY `|S|/2 = 2^(2n-1)` partners!
  have hcard_u : ∀ u ∈ S,
      (S.filter fun v => symp u v = 1).card = if u ∈ R then 0 else 2 ^ (2 * n - 1) := by
    intro u hu
    by_cases huR : u ∈ R
    · simp only [huR, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at huR
      rcases huR with huR | huR | huR | huR <;> rw [huR]
      · simp [symp_zero_left]
      · simp [hv.1]
      · simp [hv.2]
      · rw [symp_add_left, hv.1, hv.2, add_zero]; decide
    · simp only [huR, ↓reduceIte]
      -- Compute `∑ v ∈ S, sympSign u v = 0` directly via character sum over ALL `PauliIdx (n + 1)`!
      have hu0 : u ≠ 0 := fun h => huR (by simp [R, h])
      have hup : u + p ≠ 0 := fun h => huR (by
        have : u = p := by have := congr_arg (· + p) h; simpa [pauliIdx_add_cancel_right] using this
        simp [R, this])
      have huq : u + q ≠ 0 := fun h => huR (by
        have : u = q := by have := congr_arg (· + q) h; simpa [pauliIdx_add_cancel_right] using this
        simp [R, this])
      have hupq : u + (p + q) ≠ 0 := fun h => huR (by
        have : u = p + q := by have := congr_arg (· + (p + q)) h; simpa [pauliIdx_add_cancel_right] using this
        simp [R, this])
      have hsum_sign : ∀ a : PauliIdx (n + 1), a ≠ 0 → ∑ z : PauliIdx (n + 1), sympSign a z = 0 := by
        intro a ha; obtain ⟨w, hw⟩ := exists_symp_one ha
        have hshift : ∑ z : PauliIdx (n + 1), sympSign a z = ∑ z : PauliIdx (n + 1), sympSign a (z + w) :=
          (Fintype.sum_equiv (Equiv.addRight w) _ _ fun _ => rfl).symm
        have hneg : ∀ z : PauliIdx (n + 1), sympSign a (z + w) = -sympSign a z := fun z => by
          rw [sympSign_add_right]; simp [sympSign, hw, show (1 : ZMod 2) ≠ 0 by decide]
        simp_rw [hneg, Finset.sum_neg_distrib] at hshift; linarith
      have hS_zero : ∑ v ∈ S, sympSign u v = 0 := by
        have h4sum : (4 : ℤ) * ∑ v ∈ S, sympSign u v =
            ∑ v : PauliIdx (n + 1), sympSign u v * (1 + sympSign p v) * (1 + sympSign q v) := by
          have hind : ∀ v : PauliIdx (n + 1),
              (if symp p v = 0 ∧ symp q v = 0 then (4 : ℤ) * sympSign u v else 0) =
              sympSign u v * (1 + sympSign p v) * (1 + sympSign q v) := by
            intro v; simp only [sympSign]
            rcases zmod2_cases (symp p v) with h1 | h1 <;> rcases zmod2_cases (symp q v) with h2 | h2 <;>
              simp [h1, h2] <;> ring
          simp_rw [← hind, Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.mul_sum]
          rfl
        have hexp : ∀ v : PauliIdx (n + 1),
            sympSign u v * (1 + sympSign p v) * (1 + sympSign q v) =
            sympSign u v + sympSign (u + p) v + sympSign (u + q) v + sympSign (u + (p + q)) v := fun v => by
          rw [sympSign_add_left u p, sympSign_add_left u q, sympSign_add_left u (p + q), sympSign_add_left p q]
          ring
        simp_rw [hexp, Finset.sum_add_distrib] at h4sum
        rw [hsum_sign u hu0, hsum_sign (u + p) hup, hsum_sign (u + q) huq,
            hsum_sign (u + (p + q)) hupq] at h4sum
        linarith
      -- Split `∑ v ∈ S, sympSign u v = |S_0| - |S_1| = 0` and `|S_0| + |S_1| = |S| = 2^(2n)`!
      have hsplit : ∑ v ∈ S, sympSign u v =
          ((S.filter fun v => symp u v = 0).card : ℤ) - ((S.filter fun v => symp u v = 1).card : ℤ) := by
        rw [← Finset.sum_filter_add_sum_filter_not S (fun v => symp u v = 0)]
        have h0 : ∑ v ∈ S.filter (fun v => symp u v = 0), sympSign u v =
            ((S.filter fun v => symp u v = 0).card : ℤ) := by
          calc ∑ v ∈ S.filter (fun v => symp u v = 0), sympSign u v
              = ∑ _v ∈ S.filter (fun v => symp u v = 0), (1 : ℤ) :=
                  Finset.sum_congr rfl fun v hv => by simp [sympSign, (Finset.mem_filter.mp hv).2]
            _ = ((S.filter fun v => symp u v = 0).card : ℤ) := by
                  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        have hflt1 : S.filter (fun v => ¬symp u v = 0) = S.filter (fun v => symp u v = 1) := by
          ext v; simp only [Finset.mem_filter]
          exact ⟨fun ⟨hS, hn0⟩ => ⟨hS, (zmod2_cases _).resolve_left hn0⟩,
                 fun ⟨hS, h1⟩ => ⟨hS, by rw [h1]; decide⟩⟩
        have h1 : ∑ v ∈ S.filter (fun v => ¬symp u v = 0), sympSign u v =
            -((S.filter fun v => symp u v = 1).card : ℤ) := by
          rw [hflt1]
          calc ∑ v ∈ S.filter (fun v => symp u v = 1), sympSign u v
              = ∑ _v ∈ S.filter (fun v => symp u v = 1), (-1 : ℤ) :=
                  Finset.sum_congr rfl fun v hv => by
                    have h := (Finset.mem_filter.mp hv).2
                    simp [sympSign, h, show (1 : ZMod 2) ≠ 0 by decide]
            _ = -((S.filter fun v => symp u v = 1).card : ℤ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]; ring
        rw [h0, h1]; ring
      have hcard_add : (S.filter fun v => symp u v = 0).card + (S.filter fun v => symp u v = 1).card = S.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨hS, _⟩ | ⟨hS, _⟩) <;> exact hS
          · intro hS; rcases zmod2_cases (symp u v) with h | h
            · exact Or.inl ⟨hS, h⟩
            · exact Or.inr ⟨hS, h⟩
        · rw [Finset.disjoint_left]; intro v h0 h1
          simp only [Finset.mem_filter] at h0 h1; rw [h0.2] at h1; exact absurd h1.2 (by decide)
      have h2n : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
        nth_rw 1 [show 2 * n = (2 * n - 1) + 1 by omega]
        rw [pow_succ, mul_comm]
      omega
  -- Sum over `u ∈ S`!
  have hbij : ((Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter
      fun uv => symp uv.1 uv.2 = 1 ∧ symp uv.1 p = 0 ∧ symp uv.2 p = 0 ∧
        symp uv.1 q = 0 ∧ symp uv.2 q = 0).card =
      ∑ u ∈ S, (S.filter fun v => symp u v = 1).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun uv _ => ⟨uv.1, uv.2⟩) ?_ ?_ ?_
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at huv
      simp only [Finset.mem_sigma, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨by rw [symp_comm]; exact huv.2.1, by rw [symp_comm]; exact huv.2.2.2.1⟩,
             ⟨by rw [symp_comm]; exact huv.2.2.1, by rw [symp_comm]; exact huv.2.2.2.2⟩, huv.1⟩
    · rintro ⟨u1, v1⟩ _ ⟨u2, v2⟩ _ h; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_sigma, S, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      refine ⟨(u, v), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨huv.2.2, by rw [symp_comm]; exact huv.1.1, by rw [symp_comm]; exact huv.2.1.1,
             by rw [symp_comm]; exact huv.1.2, by rw [symp_comm]; exact huv.2.1.2⟩
  rw [hbij, Finset.sum_congr rfl hcard_u, Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, smul_eq_mul]
  have hdiff : (S.filter fun u => u ∉ R).card = S.card - R.card := by
    have hflt : S.filter (fun u => u ∉ R) = S \ R := by ext u; simp [Finset.mem_sdiff]
    have hadd := Finset.card_sdiff_add_card_eq_card hR_sub
    rw [hflt]; omega
  rw [hdiff, hS_card, hR_card]

/-- Exact double-counting identity over all hyperbolic pairs `(u, v)` in `PauliIdx (n + 1)` (`n ≥ 1`):
      `∑_{symp u v = 1} frustPairs (hypPerp u v) s = (2^(2n) - 4) * 2^(2n - 1) * frustPairs (nzPts (n + 1)) s`. -/
private lemma double_count_hypPairs {n : ℕ} (hn : 1 ≤ n) (s : PauliIdx (n + 1) → ℤ) :
    ∑ uv ∈ (Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter (fun uv => symp uv.1 uv.2 = 1),
        frustPairs (hypPerp uv.1 uv.2) s =
      (2 ^ (2 * n) - 4) * 2 ^ (2 * n - 1) * frustPairs (nzPts (n + 1)) s := by
  let H := (Finset.univ : Finset (PauliIdx (n + 1) × PauliIdx (n + 1))).filter (fun uv => symp uv.1 uv.2 = 1)
  let F := ((nzPts (n + 1)) ×ˢ (nzPts (n + 1))).filter fun pq =>
    pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0 ∧
    gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1
  have hrewrite : ∀ uv ∈ H, frustPairs (hypPerp uv.1 uv.2) s =
      ∑ pq ∈ F, if symp uv.1 pq.1 = 0 ∧ symp uv.2 pq.1 = 0 ∧ symp uv.1 pq.2 = 0 ∧ symp uv.2 pq.2 = 0 then 1 else 0 := by
    intro uv _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    unfold frustPairs
    refine congr_arg Finset.card (Finset.ext fun pq => ?_)
    simp only [F, hypPerp, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [Finset.sum_congr rfl hrewrite, Finset.sum_comm]
  have hinner : ∀ pq ∈ F,
      (∑ uv ∈ H, if symp uv.1 pq.1 = 0 ∧ symp uv.2 pq.1 = 0 ∧ symp uv.1 pq.2 = 0 ∧ symp uv.2 pq.2 = 0 then 1 else 0) =
      (2 ^ (2 * n) - 4) * 2 ^ (2 * n - 1) := by
    intro pq hpq
    simp only [F, nzPts, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true] at hpq
    rcases hpq with ⟨⟨hp0, hq0⟩, hne, hspq, _⟩
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have hflt : H.filter (fun uv => symp uv.1 pq.1 = 0 ∧ symp uv.2 pq.1 = 0 ∧ symp uv.1 pq.2 = 0 ∧ symp uv.2 pq.2 = 0) =
        Finset.univ.filter (fun uv : PauliIdx (n + 1) × PauliIdx (n + 1) =>
          symp uv.1 uv.2 = 1 ∧ symp uv.1 pq.1 = 0 ∧ symp uv.2 pq.1 = 0 ∧ symp uv.1 pq.2 = 0 ∧ symp uv.2 pq.2 = 0) := by
      ext uv; simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hflt]
    exact card_hypPairs_in_perp hn hp0 hq0 hne hspq
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ### Part 4: Universal All-`n ≥ 4` Contextuality Density Theorems (`ρₙ ≥ 5/17`) -/

/-- Exact bridge from `signCubeSum n σ` to `frustPairs (nzPts n) s` for EVERY `n ≥ 1`. -/
lemma signCubeSum_eq_frustPairs_all {n : ℕ} (hn : 1 ≤ n) {σ : PauliIdx n → ℝ}
    (h0 : σ 0 = 0) (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
    IsSignAssign s ∧
      signCubeSum n σ =
        (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) / 2 - (frustPairs (nzPts n) s : ℝ) := by
  intro s
  have hs_valid : IsSignAssign s :=
    ⟨by simp [s], fun p hp => by simp only [s, hp, ↓reduceIte]; split_ifs <;> simp⟩
  have hs_cast : ∀ p : PauliIdx n, (s p : ℝ) = σ p := fun p => by
    by_cases hp : p = 0
    · subst hp; simp [s, h0]
    · simp only [s, hp, ↓reduceIte]
      rcases hpm p hp with h | h
      · simp [h]
      · have hne : σ p ≠ 1 := by linarith
        simp only [hne, ↓reduceIte, h]; norm_num
  refine ⟨hs_valid, ?_⟩
  let C := ((nzPts n) ×ˢ (nzPts n)).filter fun pq => pq.1 ≠ pq.2 ∧ symp pq.1 pq.2 = 0
  have hsum_eq : signCubeSum n σ =
      (1 / 2 : ℝ) * ∑ pq ∈ C, ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) := by
    unfold signCubeSum
    change (∑ q ∈ nzPts n, σ q * ((1 / 2 : ℝ) * ∑ p ∈ (nzPts n).erase q, (pauliPhase q p).re * σ p * σ (q + p))) = _
    have h1 : ∀ q ∈ nzPts n,
        σ q * ((1 / 2 : ℝ) * ∑ p ∈ (nzPts n).erase q, (pauliPhase q p).re * σ p * σ (q + p)) =
        (1 / 2 : ℝ) * ∑ p ∈ nzPts n,
          if q ≠ p ∧ symp q p = 0 then ((gammaSgn q p * s q * s p * s (q + p) : ℤ) : ℝ) else 0 := by
      intro q hqU
      rw [← mul_assoc, mul_comm (σ q), mul_assoc, Finset.mul_sum]
      refine congr_arg ((1 / 2 : ℝ) * ·) ?_
      rw [← Finset.add_sum_erase (nzPts n) _ hqU]
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hqp : q ≠ p := Ne.symm (Finset.mem_erase.mp hp).1
      rcases zmod2_cases (symp q p) with hsp | hsp
      · simp only [hqp, hsp, not_false_eq_true, and_self, ↓reduceIte,
          pauliPhase_re_eq_gammaSgn hsp, ← hs_cast]
        push_cast; ring
      · simp only [hqp, hsp, show (1 : ZMod 2) ≠ 0 by decide, and_false, ↓reduceIte,
          (pauliPhase_re_cases q p).2 hsp]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_product']
    exact congr_arg ((1 / 2 : ℝ) * ·) (Finset.sum_filter _ _).symm
  have hC_card : C.card = (2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) := by
    have hbij : C.card = ∑ q ∈ nzPts n, ((nzPts n).filter fun p => p ≠ q ∧ symp q p = 0).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun pq _ => ⟨pq.1, pq.2⟩) ?_ ?_ ?_
      · rintro ⟨q, p⟩ hqp
        simp only [C, Finset.mem_filter, Finset.mem_product] at hqp
        simp only [Finset.mem_sigma, Finset.mem_filter]
        exact ⟨hqp.1.1, hqp.1.2, hqp.2.1.symm, hqp.2.2⟩
      · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h; simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; exact Prod.ext h.1 h.2
      · rintro ⟨q, p⟩ hqp
        simp only [Finset.mem_sigma, Finset.mem_filter] at hqp
        exact ⟨(q, p), by simp [C, hqp.1, hqp.2.1, hqp.2.2.1.symm, hqp.2.2.2], rfl⟩
    rw [hbij]
    have hinner : ∀ q ∈ nzPts n, ((nzPts n).filter fun p => p ≠ q ∧ symp q p = 0).card = 2 ^ (2 * n - 1) - 2 := by
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      let A0 := Finset.univ.filter fun p : PauliIdx n => symp q p = 0
      have h0A : (0 : PauliIdx n) ∈ A0 := by simp [A0, symp_zero_right]
      have hqA : q ∈ A0 := by simp [A0, symp_self]
      have hsub : ((nzPts n).filter fun p => p ≠ q ∧ symp q p = 0) = (A0.erase 0).erase q := by
        ext p; simp only [A0, nzPts, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]; tauto
      rw [hsub, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hq0, hqA⟩),
          Finset.card_erase_of_mem h0A, card_symp_zero_single hq0]; omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    have hnz : (nzPts n).card = 2 ^ (2 * n) - 1 := by
      rw [nzPts, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_PauliIdx, ← pow_add, ← two_mul]
    rw [hnz]
  have hsum_val : ∑ pq ∈ C, ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) =
      (C.card : ℝ) - 2 * (frustPairs (nzPts n) s : ℝ) := by
    have hterm : ∀ pq ∈ C,
        ((gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) : ℤ) : ℝ) =
        1 - 2 * (if gammaSgn pq.1 pq.2 * s pq.1 * s pq.2 * s (pq.1 + pq.2) = -1 then (1 : ℝ) else 0) := by
      intro pq hpq
      simp only [C, nzPts, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true] at hpq
      rcases hpq with ⟨⟨hp0, hq0⟩, hne, _⟩
      have hpq0 : pq.1 + pq.2 ≠ 0 := fun h => hne (by
        have := congr_arg (pq.1 + ·) h; simpa [pauliIdx_add_cancel_left] using this.symm)
      rcases gammaSgn_eq_pm1 pq.1 pq.2 with h1 | h1 <;>
      rcases hs_valid.2 pq.1 hp0 with h2 | h2 <;>
      rcases hs_valid.2 pq.2 hq0 with h3 | h3 <;>
      rcases hs_valid.2 (pq.1 + pq.2) hpq0 with h4 | h4 <;>
      simp [h1, h2, h3, h4] <;> norm_num
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    refine congr_arg (Nat.cast : ℕ → ℝ) ?_
    unfold frustPairs
    refine congr_arg Finset.card (Finset.ext fun pq => ?_)
    simp only [C, Finset.mem_filter]; tauto
  rw [hsum_eq, hsum_val, hC_card]; ring

end GeneralContextualityLift

open GeneralContextualityLift

/-- **Universal All-`n ≥ 4` Multi-Qubit Contextuality Density Theorem (`CD(W(2n-1, 2)) ≥ (5/17)|L|`)**:
    For EVERY `n ≥ 4` and EVERY Pauli sign assignment `s : PauliIdx n → ℤ` (`s 0 = 0`, `s p ∈ {±1}`),
      `5 * ((2^(2n) - 1) * (2^(2n - 1) - 2)) ≤ 17 * frustPairs (nzPts n) s`. -/
theorem frustPairs_ge_five_seventeenths {n : ℕ} (hn : 4 ≤ n)
    {s : PauliIdx n → ℤ} (hs : IsSignAssign s) :
    5 * ((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2)) ≤ 17 * frustPairs (nzPts n) s := by
  revert s hs
  induction n, hn using Nat.le_induction with
  | base =>
    intro s hs
    -- Base case `n = 4`: immediate from `signCubeSum_four_le_6615` + `signCubeSum_eq_frustPairs`!
    let σ : PauliIdx 4 → ℝ := fun p => (s p : ℝ)
    have h0 : σ 0 = 0 := by simp [σ, hs.1]
    have hpm : ∀ p : PauliIdx 4, p ≠ 0 → σ p = 1 ∨ σ p = -1 := fun p hp => by
      rcases hs.2 p hp with h | h <;> simp [σ, h]
    have hle := signCubeSum_four_le_6615 σ h0 hpm
    have heq := (signCubeSum_eq_frustPairs h0 hpm).2
    have hseq : (fun p : PauliIdx 4 => if p = 0 then (0 : ℤ) else if σ p = 1 then 1 else -1) = s := by
      ext p; by_cases hp : p = 0
      · subst hp; simp [hs.1]
      · simp only [hp, ↓reduceIte]
        rcases hs.2 p hp with h | h
        · simp [σ, h]
        · simp only [σ, h]; norm_num
    rw [hseq] at heq
    have hR : (9450 : ℝ) ≤ (frustPairs (nzPts 4) s : ℝ) := by linarith
    have hN : 9450 ≤ frustPairs (nzPts 4) s := by exact_mod_cast hR
    norm_num; omega
  | succ k hk ih =>
    intro s hs
    -- Inductive step `k → k + 1` (`k ≥ 4`): average over all hyperbolic pairs `(u, v)`!
    have hk1 : 1 ≤ k := by omega
    have hstep : ∀ uv ∈ (Finset.univ : Finset (PauliIdx (k + 1) × PauliIdx (k + 1))).filter
        (fun uv => symp uv.1 uv.2 = 1),
        5 * ((2 ^ (2 * k) - 1) * (2 ^ (2 * k - 1) - 2)) ≤ 17 * frustPairs (hypPerp uv.1 uv.2) s := by
      intro uv huv
      have hsymp : symp uv.1 uv.2 = 1 := (Finset.mem_filter.mp huv).2
      obtain ⟨us, hu, hv⟩ := exists_transvWord_hypPair (symp_eXLast_eZLast k) hsymp
      let s' := applyTransvWord us s
      have hs' : IsSignAssign s' := applyTransvWord_isSignAssign us hs
      have hfr : frustPairs (hypPerp uv.1 uv.2) s = frustPairs (nzPts k) (restrictLast s') := by
        rw [← frustPairs_hypPerp_eLast, frustPairs_applyTransvWord_hypPerp, hu, hv]
      rw [hfr]
      exact ih (restrictLast_isSignAssign hs')
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, card_all_hypPairs k,
        double_count_hypPairs hk1 s] at hsum
    -- Cancel the positive factor `(2^(2k) - 4) * 2^(2k - 1)` algebraically!
    have hpos : 0 < (2 ^ (2 * k) - 4) * 2 ^ (2 * k - 1) := by
      have h1 : 4 < 2 ^ (2 * k) := by
        calc 4 < 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 0 < 2 ^ (2 * k - 1) := Nat.two_pow_pos _
      exact Nat.mul_pos (by omega) h2
    -- Prove exact Nat identity:
    --   `(2^(2k+2) - 1) * 2^(2k+1) * ((2^(2k) - 1) * (2^(2k-1) - 2))`
    --   `= (2^(2k) - 4) * 2^(2k-1) * ((2^(2(k+1)) - 1) * (2^(2(k+1)-1) - 2))`!
    have hAlg :
        (2 ^ (2 * k + 2) - 1) * 2 ^ (2 * k + 1) * (5 * ((2 ^ (2 * k) - 1) * (2 ^ (2 * k - 1) - 2))) =
        (2 ^ (2 * k) - 4) * 2 ^ (2 * k - 1) *
          (5 * ((2 ^ (2 * (k + 1)) - 1) * (2 ^ (2 * (k + 1) - 1) - 2))) := by
      have hp1 : 2 ^ (2 * k + 1) = 4 * 2 ^ (2 * k - 1) := by
        rw [show 2 * k + 1 = (2 * k - 1) + 2 by omega, pow_add]; ring
      have hp2 : 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
        nth_rw 1 [show 2 * k = (2 * k - 1) + 1 by omega]
        rw [pow_succ, mul_comm]
      have hp3 : 2 ^ (2 * (k + 1) - 1) = 2 * 2 ^ (2 * k) := by
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, pow_succ, mul_comm]
      have hp4 : 2 * (k + 1) = 2 * k + 2 := by omega
      have hge2 : 2 ≤ 2 ^ (2 * k - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hge4 : 4 ≤ 2 ^ (2 * k) := by omega
      have hge1 : 1 ≤ 2 ^ (2 * k) := by omega
      have hge2' : 2 ≤ 2 ^ (2 * (k + 1) - 1) := by omega
      have hp1Z : (2 : ℤ) ^ (2 * k + 1) = 4 * (2 : ℤ) ^ (2 * k - 1) := by exact_mod_cast hp1
      have hp2Z : (2 : ℤ) ^ (2 * k) = 2 * (2 : ℤ) ^ (2 * k - 1) := by exact_mod_cast hp2
      have hp3Z : (2 : ℤ) ^ (2 * (k + 1) - 1) = 2 * (2 : ℤ) ^ (2 * k) := by exact_mod_cast hp3
      zify [hge2, hge4, hge1, hge2', show 1 ≤ 2 ^ (2 * k + 2) from Nat.one_le_pow _ _ (by norm_num),
            show 1 ≤ 2 ^ (2 * (k + 1)) from Nat.one_le_pow _ _ (by norm_num)]
      rw [hp1Z, hp3Z, hp4, hp2Z]; ring
    have hmul : (2 ^ (2 * k) - 4) * 2 ^ (2 * k - 1) *
        (5 * ((2 ^ (2 * (k + 1)) - 1) * (2 ^ (2 * (k + 1) - 1) - 2))) ≤
        (2 ^ (2 * k) - 4) * 2 ^ (2 * k - 1) * (17 * frustPairs (nzPts (k + 1)) s) := by
      rw [← hAlg]; calc
        _ ≤ 17 * ((2 ^ (2 * k) - 4) * 2 ^ (2 * k - 1) * frustPairs (nzPts (k + 1)) s) := hsum
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hmul hpos

/-- **Universal All-`n ≥ 4` Sign-Cube Sum Upper Bound (`signCubeSum_le_seven_seventeenths`)**:
    For EVERY `n ≥ 4` and EVERY Pauli sign assignment `σ : PauliIdx n → ℝ` (`σ 0 = 0`, `σ p ∈ {±1}`),
      `signCubeSum n σ ≤ (7 / 17) * ((2^(2n) - 1) * (2^(2n - 1) - 2) / 2)`.
    At `n = 4`, this recovers exact `6615`; for all `n ≥ 5`, it unconditionally improves the
    best known general-`n` contextuality upper-bound factor from `3/5 = 0.600` to `7/17 ≈ 0.4118`. -/
theorem signCubeSum_le_seven_seventeenths {n : ℕ} (hn : 4 ≤ n)
    (σ : PauliIdx n → ℝ) (h0 : σ 0 = 0)
    (hpm : ∀ p : PauliIdx n, p ≠ 0 → σ p = 1 ∨ σ p = -1) :
    signCubeSum n σ ≤
      (7 / 17 : ℝ) * (((2 : ℝ) ^ (2 * n) - 1) * ((2 : ℝ) ^ (2 * n - 1) - 2) / 2) := by
  let s : PauliIdx n → ℤ := fun p => if p = 0 then 0 else if σ p = 1 then 1 else -1
  have hbridge := signCubeSum_eq_frustPairs_all (by omega) h0 hpm
  have hs : IsSignAssign s := hbridge.1
  have heq : signCubeSum n σ =
      (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) / 2 - (frustPairs (nzPts n) s : ℝ) := hbridge.2
  have hfr := frustPairs_ge_five_seventeenths hn hs
  have hfrR : (5 : ℝ) * (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) ≤
      17 * (frustPairs (nzPts n) s : ℝ) := by exact_mod_cast hfr
  have hcast : (((2 ^ (2 * n) - 1) * (2 ^ (2 * n - 1) - 2) : ℕ) : ℝ) =
      ((2 : ℝ) ^ (2 * n) - 1) * ((2 : ℝ) ^ (2 * n - 1) - 2) := by
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ≤ 2 ^ (2 * n - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]; push_cast; rfl
  rw [hcast] at heq hfrR
  linarith

end MultiQubitMUB
