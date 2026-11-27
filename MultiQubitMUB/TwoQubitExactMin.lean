import MultiQubitMUB.TwoQubitExactCert
import MultiQubitMUB.SpikeFamily

/-!
# Exact Sharp Global Minimum of the 2-Qubit Pauli Fourth Moment: `min F₂(|ψ⟩) = 7/4`

Proves the **exact sharp global lower bound** for ALL 2-qubit pure quantum states `|ψ⟩ ∈ ℂ⁴`
(zero `sorry`, zero `native_decide`, standard three Lean axioms `[propext, Classical.choice, Quot.sound]`):

1. `pauliMoment4_two_ge_seven_fourths`:
   For every unit state `ψ : QState 2`, `(7 / 4 : ℝ) ≤ pauliMoment4 2 ψ`.
2. `pauliMoment4_two_min_eq_seven_fourths`:
   - `∀ ψ : QState 2, IsUnitState ψ → (7 / 4 : ℝ) ≤ pauliMoment4 2 ψ`, and
   - `∃ ψ : QState 2, IsUnitState ψ ∧ pauliMoment4 2 ψ = 7 / 4`
     (attained by the 2-qubit MUB fiducial `spikeState 2 (1/2)`, Clifford-equivalent to `(1, 1, 1, i)/2`).

## Proof Method
Pure degree-8 Hermitian Sum-of-Squares (GNW `t = 8` moment matrix `M₄ ≽ 0`) certified in exact integers
by `MultiQubitMUB.TwoQubitExactCert`:
- `24 * 27648 * (4 * F₂(z) - 7 * ‖z‖⁸) * ‖z‖⁸ = ∑_{σ ∈ S₄} ∑_{o=0..5} copies_o * y_o(z ∘ σ)† A_o y_o(z ∘ σ)`,
- each of the 6 `S₄`-orbit reduced integer blocks `A_o` (sizes `33, 19, 23, 28, 23, 24`) satisfies
  `S_o² * A_o = W_o * W_oᵀ + E_o` with `S_o ∈ {1, 2, 4, 8}` and `E_o` strictly diagonally dominant.
-/

namespace MultiQubitMUB

open TwoQubitExactCert

namespace TwoQubitExactMin

/-! ### Part 1: Monomials, `RowTrie` Semantics & Pure-Kernel Table Bridge Lemmas -/

/-- Monomial `z 0 ^ t.1 * z 1 ^ t.2.1 * z 2 ^ t.2.2.1 * z 3 ^ t.2.2.2`. -/
def monTup (t : Tup4) (z : Fin 4 → ℂ) : ℂ :=
  z 0 ^ t.1 * z 1 ^ t.2.1 * z 2 ^ t.2.2.1 * z 3 ^ t.2.2.2

/-- Degree-4 raw monomial basis (`0..34`). -/
def mon4 (i : Nat) (z : Fin 4 → ℂ) : ℂ :=
  monTup (sym4List.getD i (0, 0, 0, 0)) z

/-- Degree-8 raw monomial basis (`0..164`). -/
def mon8 (i : Nat) (z : Fin 4 → ℂ) : ℂ :=
  monTup (sym8List.getD i (0, 0, 0, 0)) z

private lemma monTup_add (a b : Tup4) (z : Fin 4 → ℂ) :
    monTup (addTup4 a b) z = monTup a z * monTup b z := by
  simp only [monTup, addTup4, pow_add]; ring

private def natToFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

/-- Convert a 4-tuple permutation `p` to a function `Fin 4 → Fin 4`. -/
def permFn (p : Tup4) (k : Fin 4) : Fin 4 :=
  match k.val with
  | 0 => natToFin4 p.1
  | 1 => natToFin4 p.2.1
  | 2 => natToFin4 p.2.2.1
  | _ => natToFin4 p.2.2.2

private def checkPermValid (p : Tup4) : Bool :=
  p.1 < 4 && p.2.1 < 4 && p.2.2.1 < 4 && p.2.2.2 < 4 &&
  p.1 != p.2.1 && p.1 != p.2.2.1 && p.1 != p.2.2.2 &&
  p.2.1 != p.2.2.1 && p.2.1 != p.2.2.2 && p.2.2.1 != p.2.2.2

private lemma s4Perms_valid : s4Perms.all checkPermValid = true := by rfl

private lemma monTup_perm (p : Tup4) (hp : checkPermValid p = true) (t : Tup4) (z : Fin 4 → ℂ) :
    monTup (permTup4 p t) z = monTup t (fun k => z (permFn p k)) := by
  simp only [checkPermValid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  rcases hp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h01⟩, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩
  rcases p with ⟨p0, p1, p2, p3⟩
  dsimp only at h0 h1 h2 h3 h01 h02 h03 h12 h13 h23 ⊢
  interval_cases p0 <;> interval_cases p1 <;> interval_cases p2 <;> interval_cases p3
  all_goals try exact absurd rfl h01
  all_goals try exact absurd rfl h02
  all_goals try exact absurd rfl h03
  all_goals try exact absurd rfl h12
  all_goals try exact absurd rfl h13
  all_goals try exact absurd rfl h23
  all_goals (simp only [monTup, permTup4, permFn, natToFin4, Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]; try ring)

/-- Pure-kernel verification of index/round-trip properties for `sym4Idx`, `sym8Idx`, `buildPermNatTrie`,
    and multinomial convolution `sym4Mult * sym4Mult = sym8Mult`. -/
private def checkTupOf4Table : Bool :=
  (List.range 4).all fun x0 =>
  (List.range 4).all fun x1 =>
  (List.range 4).all fun x2 =>
  (List.range 4).all fun x3 =>
    let t := tupOf4 x0 x1 x2 x3
    let i := sym4Idx t
    i < 35 && sym4List.getD i (0, 0, 0, 0) == t

private def checkAdd4To8Table : Bool :=
  sym4List.all fun c1 =>
  sym4List.all fun c2 =>
    let t := addTup4 c1 c2
    let k := sym8Idx t
    k < 165 && sym8List.getD k (0, 0, 0, 0) == t

private def checkPerm8Table : Bool :=
  s4Perms.all fun p =>
    let pt := buildPermNatTrie p
    (sym8List.zip (List.range 165)).all fun (t, i) =>
      let j := natTrieGet 8 i pt
      j < 165 && sym8List.getD j (0, 0, 0, 0) == permTup4 p t

private def multConvTrieAux (s4 l : List (Tup4 × Int)) (init : RowTrie) : RowTrie :=
  l.foldl (fun tr (c1, m1) =>
    s4.foldl (fun tr (c2, m2) =>
      trieAdd 8 (sym8Idx (addTup4 c1 c2)) 0 (m1 * m2) tr) tr) init

private def multConvTrie : RowTrie :=
  multConvTrieAux (sym4List.zip sym4Mult) (sym4List.zip sym4Mult) RowTrie.empty

private def checkMultConv : Bool :=
  ((List.range 165).zip sym8Mult).all fun (k, m8) =>
    trieGetRow 8 k multConvTrie == [(0, m8)]

set_option maxRecDepth 20000 in
private lemma tupOf4Table_valid : checkTupOf4Table = true := by rfl

set_option maxRecDepth 20000 in
private lemma add4To8Table_valid : checkAdd4To8Table = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma perm8Table_valid : checkPerm8Table = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma multConv_valid : checkMultConv = true := by rfl

private lemma sym4List_len : sym4List.length = 35 := by rfl
private lemma sym8List_len : sym8List.length = 165 := by rfl
private lemma sym4Mult_len : sym4Mult.length = 35 := by rfl
private lemma sym8Mult_len : sym8Mult.length = 165 := by rfl

private lemma list_getD_mem {α : Type*} (l : List α) (d : α) {i : Nat} (hi : i < l.length) :
    l.getD i d ∈ l := by
  simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

private lemma tupOf4_props {x0 x1 x2 x3 : Nat} (h0 : x0 < 4) (h1 : x1 < 4) (h2 : x2 < 4) (h3 : x3 < 4) :
    sym4Idx (tupOf4 x0 x1 x2 x3) < 35 ∧
    sym4List.getD (sym4Idx (tupOf4 x0 x1 x2 x3)) (0, 0, 0, 0) = tupOf4 x0 x1 x2 x3 := by
  have hall := tupOf4Table_valid
  simp only [checkTupOf4Table, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hall
  exact hall x0 h0 x1 h1 x2 h2 x3 h3

private lemma add4To8_props {a b : Nat} (ha : a < 35) (hb : b < 35) :
    let t := addTup4 (sym4List.getD a (0, 0, 0, 0)) (sym4List.getD b (0, 0, 0, 0))
    sym8Idx t < 165 ∧ sym8List.getD (sym8Idx t) (0, 0, 0, 0) = t := by
  have hall := add4To8Table_valid
  simp only [checkAdd4To8Table, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hall
  exact hall _ (list_getD_mem sym4List _ (by rw [sym4List_len]; exact ha))
             _ (list_getD_mem sym4List _ (by rw [sym4List_len]; exact hb))

private lemma perm8_props {p : Tup4} (hp : p ∈ s4Perms) {i : Nat} (hi : i < 165) :
    let j := natTrieGet 8 i (buildPermNatTrie p)
    j < 165 ∧ sym8List.getD j (0, 0, 0, 0) = permTup4 p (sym8List.getD i (0, 0, 0, 0)) := by
  have hall := perm8Table_valid
  simp only [checkPerm8Table, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hall
  have hmem : (sym8List.getD i (0, 0, 0, 0), i) ∈ sym8List.zip (List.range 165) := by
    rw [List.mem_iff_getElem]
    have hlen : (sym8List.zip (List.range 165)).length = 165 := by
      simp [sym8List_len]
    refine ⟨i, by omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_range, List.getD,
      List.getElem?_eq_getElem (by rw [sym8List_len]; exact hi), Option.getD_some]
  exact hall p hp (sym8List.getD i (0, 0, 0, 0), i) hmem

/-! ### Part 2: `RowTrie` Evaluation Algebra -/

/-- Evaluate a sparse row `List (Nat × Int)` against basis `φ : Nat → ℂ`. -/
def evalRow (φ : Nat → ℂ) : List (Nat × Int) → ℂ
  | [] => 0
  | (j, v) :: rest => (v : ℂ) * φ j + evalRow φ rest

/-- Structural evaluation of a `RowTrie` against row basis `ψ` and column basis `φ`. -/
def evalTrieAux (ψ φ : Nat → ℂ) (bitMul keyAcc : Nat) : RowTrie → ℂ
  | RowTrie.empty => 0
  | RowTrie.leaf xs => star (ψ keyAcc) * evalRow φ xs
  | RowTrie.node l r =>
      evalTrieAux ψ φ (bitMul * 2) keyAcc l +
      evalTrieAux ψ φ (bitMul * 2) (keyAcc + bitMul) r

/-- Evaluate a `RowTrie` as a Hermitian quadratic form `∑ (i, j, v), v * star (φ i) * φ j`. -/
def evalTrie (φ : Nat → ℂ) (t : RowTrie) : ℂ :=
  evalTrieAux φ φ 1 0 t

/-- Depth-uniformity invariant: every `RowTrie.leaf` sits at exact depth `d`. -/
inductive DepthTrie : Nat → RowTrie → Prop where
  | empty {d} : DepthTrie d RowTrie.empty
  | leaf {xs} : DepthTrie 0 (RowTrie.leaf xs)
  | node {d l r} : DepthTrie d l → DepthTrie d r → DepthTrie (d + 1) (RowTrie.node l r)

/-- Every column index appearing in a `RowTrie` satisfies predicate `P`. -/
inductive ColPred (P : Nat → Prop) : RowTrie → Prop where
  | empty : ColPred P RowTrie.empty
  | leaf {xs} : (∀ jv ∈ xs, P jv.1) → ColPred P (RowTrie.leaf xs)
  | node {l r} : ColPred P l → ColPred P r → ColPred P (RowTrie.node l r)

/-- Every non-empty leaf key `ka` (with `(bm, ka)` traversal) satisfies `ka < N`. -/
inductive RowBound (N : Nat) : Nat → Nat → RowTrie → Prop where
  | empty {bm ka} : RowBound N bm ka RowTrie.empty
  | leaf {bm ka xs} : (xs ≠ [] → ka < N) → RowBound N bm ka (RowTrie.leaf xs)
  | node {bm ka l r} :
      RowBound N (bm * 2) ka l → RowBound N (bm * 2) (ka + bm) r →
      RowBound N bm ka (RowTrie.node l r)

private lemma evalRow_addAssoc (φ : Nat → ℂ) (j : Nat) (v : Int) (xs : List (Nat × Int)) :
    evalRow φ (addAssoc j v xs) = (v : ℂ) * φ j + evalRow φ xs := by
  induction xs with
  | nil =>
    simp only [addAssoc, evalRow, add_zero]
    split_ifs with hv
    · have hv0 : v = 0 := by simpa using hv
      simp [hv0, evalRow]
    · simp [evalRow]
  | cons kw rest ih =>
    rcases kw with ⟨k, w⟩
    simp only [addAssoc]
    split_ifs with hkj hnv hjk hv0
    · have hkeq : k = j := by simpa using hkj
      have hnv0 : w + v = 0 := by simpa using hnv
      subst hkeq
      simp only [evalRow]
      have hcast : ((w + v : ℤ) : ℂ) = 0 := by exact_mod_cast hnv0
      push_cast at hcast
      linear_combination -(φ k) * hcast
    · have hkeq : k = j := by simpa using hkj
      subst hkeq
      simp only [evalRow, Int.cast_add]; ring
    · have hv : v = 0 := by simpa using hv0
      simp [hv, evalRow]
    · simp only [evalRow]
    · simp only [evalRow, ih]; ring

private lemma addAssoc_colPred {P : Nat → Prop} {j : Nat} (hj : P j) (v : Int)
    {xs : List (Nat × Int)} (hxs : ∀ kv ∈ xs, P kv.1) :
    ∀ kv ∈ addAssoc j v xs, P kv.1 := by
  induction xs with
  | nil =>
    simp only [addAssoc]; split_ifs
    · intro kv h; simp at h
    · intro kv h; simp at h; rcases h with ⟨rfl, _⟩; exact hj
  | cons kw rest ih =>
    rcases kw with ⟨k, w⟩
    have hk : P k := hxs (k, w) (by simp)
    have hrest : ∀ kv ∈ rest, P kv.1 := fun kv h => hxs kv (by simp [h])
    simp only [addAssoc]; split_ifs
    · exact hrest
    · intro kv h; simp at h; rcases h with ⟨rfl, _⟩ | h; exact hk; exact hrest kv h
    · exact hxs
    · intro kv h; simp at h; rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | h; exact hj; exact hk; exact hrest kv h
    · intro kv h; simp at h; rcases h with ⟨rfl, _⟩ | h; exact hk; exact ih hrest kv h

private lemma evalRow_mergeRows (φ : Nat → ℂ) (xs ys : List (Nat × Int)) :
    evalRow φ (mergeRows xs ys) = evalRow φ xs + evalRow φ ys := by
  unfold mergeRows
  induction ys generalizing xs with
  | nil => simp [evalRow]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.foldl_cons, evalRow, ih, evalRow_addAssoc]; ring

private lemma mergeRows_colPred {P : Nat → Prop} {xs ys : List (Nat × Int)}
    (hxs : ∀ kv ∈ xs, P kv.1) (hys : ∀ kv ∈ ys, P kv.1) :
    ∀ kv ∈ mergeRows xs ys, P kv.1 := by
  unfold mergeRows
  induction ys generalizing xs with
  | nil => exact hxs
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.foldl_cons]
    exact ih (addAssoc_colPred (hys (k, v) (by simp)) v hxs) (fun x hx => hys x (by simp [hx]))

private lemma evalRow_scaleRow (φ : Nat → ℂ) (c : Int) (xs : List (Nat × Int)) :
    evalRow φ (scaleRow c xs) = (c : ℂ) * evalRow φ xs := by
  induction xs with
  | nil => simp [scaleRow, evalRow]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [scaleRow]
    split_ifs with h0
    · have hcv : c * v = 0 := by simpa using h0
      have hcast : ((c * v : ℤ) : ℂ) = 0 := by exact_mod_cast hcv
      push_cast at hcast
      simp only [evalRow, ih]; linear_combination -(φ k) * hcast
    · simp only [evalRow, ih, Int.cast_mul]; ring

private lemma scaleRow_colPred {P : Nat → Prop} (c : Int) {xs : List (Nat × Int)}
    (hxs : ∀ kv ∈ xs, P kv.1) : ∀ kv ∈ scaleRow c xs, P kv.1 := by
  induction xs with
  | nil => simp [scaleRow]
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [scaleRow]; split_ifs
    · exact ih fun x hx => hxs x (by simp [hx])
    · intro x hx; simp at hx; rcases hx with ⟨rfl, _⟩ | hx
      · exact hxs (k, v) (by simp)
      · exact ih (fun y hy => hxs y (by simp [hy])) x hx

private lemma evalTrieAux_isEmptyTrie (ψ φ : Nat → ℂ) (bm ka : Nat) (t : RowTrie)
    (he : isEmptyTrie t = true) : evalTrieAux ψ φ bm ka t = 0 := by
  induction t generalizing bm ka with
  | empty => rfl
  | leaf xs =>
    simp only [isEmptyTrie, List.isEmpty_iff] at he
    simp [evalTrieAux, he, evalRow]
  | node l r ihl ihr =>
    simp only [isEmptyTrie, Bool.and_eq_true] at he
    simp [evalTrieAux, ihl _ _ he.1, ihr _ _ he.2]

private lemma evalTrieAux_trieEq (ψ φ : Nat → ℂ) (bm ka : Nat) (t1 t2 : RowTrie)
    (heq : trieEq t1 t2 = true) :
    evalTrieAux ψ φ bm ka t1 = evalTrieAux ψ φ bm ka t2 := by
  induction t1 generalizing t2 bm ka with
  | empty =>
    simp only [trieEq] at heq
    rw [evalTrieAux, evalTrieAux_isEmptyTrie ψ φ bm ka t2 heq]
  | leaf xs =>
    cases t2 with
    | empty =>
      simp only [trieEq] at heq
      rw [evalTrieAux_isEmptyTrie ψ φ bm ka (RowTrie.leaf xs) heq, evalTrieAux]
    | leaf ys =>
      simp only [trieEq, beq_iff_eq] at heq
      rw [heq]
    | node _ _ => simp [trieEq] at heq
  | node l1 r1 ihl ihr =>
    cases t2 with
    | empty =>
      simp only [trieEq] at heq
      rw [evalTrieAux_isEmptyTrie ψ φ bm ka (RowTrie.node l1 r1) heq, evalTrieAux]
    | leaf _ => simp [trieEq] at heq
    | node l2 r2 =>
      simp only [trieEq, Bool.and_eq_true] at heq
      simp only [evalTrieAux, ihl _ _ l2 heq.1, ihr _ _ r2 heq.2]

private lemma depthTrie_trieAdd (d i j : Nat) (v : Int) {t : RowTrie} (ht : DepthTrie d t) :
    DepthTrie d (trieAdd d i j v t) := by
  induction d generalizing i t with
  | zero =>
    cases ht with
    | empty => exact DepthTrie.leaf
    | leaf => exact DepthTrie.leaf
  | succ d ih =>
    cases ht with
    | empty =>
      simp only [trieAdd]; split_ifs
      · exact DepthTrie.node (ih _ DepthTrie.empty) DepthTrie.empty
      · exact DepthTrie.node DepthTrie.empty (ih _ DepthTrie.empty)
    | node hl hr =>
      simp only [trieAdd]; split_ifs
      · exact DepthTrie.node (ih _ hl) hr
      · exact DepthTrie.node hl (ih _ hr)

private lemma colPred_trieAdd {P : Nat → Prop} (d i j : Nat) (hj : P j) (v : Int)
    {t : RowTrie} (ht : DepthTrie d t) (hc : ColPred P t) :
    ColPred P (trieAdd d i j v t) := by
  induction d generalizing i t with
  | zero =>
    cases ht with
    | empty => exact ColPred.leaf (addAssoc_colPred hj v (by simp))
    | leaf =>
      cases hc with | leaf hxs => exact ColPred.leaf (addAssoc_colPred hj v hxs)
  | succ d ih =>
    cases ht with
    | empty =>
      simp only [trieAdd]; split_ifs
      · exact ColPred.node (ih _ DepthTrie.empty ColPred.empty) ColPred.empty
      · exact ColPred.node ColPred.empty (ih _ DepthTrie.empty ColPred.empty)
    | node hl hr =>
      cases hc with | node hcl hcr =>
      simp only [trieAdd]; split_ifs
      · exact ColPred.node (ih _ hl hcl) hcr
      · exact ColPred.node hcl (ih _ hr hcr)

private lemma mul_two_div_even (bm i : Nat) (h : i % 2 = 0) : (bm * 2) * (i / 2) = bm * i := by
  calc (bm * 2) * (i / 2) = bm * (2 * (i / 2)) := by ring
    _ = bm * i := by congr 1; omega

private lemma mul_two_div_odd (bm i : Nat) (h : i % 2 ≠ 0) : bm + (bm * 2) * (i / 2) = bm * i := by
  calc bm + (bm * 2) * (i / 2) = bm * (2 * (i / 2) + 1) := by ring
    _ = bm * i := by congr 1; omega

private lemma rowBound_trieAdd {N : Nat} (d bm ka i j : Nat) (v : Int)
    (hi : ka + bm * i < N) {t : RowTrie} (ht : DepthTrie d t) (hb : RowBound N bm ka t) :
    RowBound N bm ka (trieAdd d i j v t) := by
  induction d generalizing bm ka i t with
  | zero =>
    cases ht with
    | empty => exact RowBound.leaf fun _ => by omega
    | leaf => exact RowBound.leaf fun _ => by omega
  | succ d ih =>
    have hev : i % 2 = 0 → ka + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [mul_two_div_even bm i h]
    have hod : i % 2 ≠ 0 → (ka + bm) + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [add_assoc, mul_two_div_odd bm i h]
    cases ht with
    | empty =>
      simp only [trieAdd]; split_ifs with h
      · have h0 : i % 2 = 0 := by simpa using h
        exact RowBound.node (ih _ _ _ (by rw [hev h0]; exact hi) DepthTrie.empty RowBound.empty) RowBound.empty
      · have h1 : i % 2 ≠ 0 := by simpa using h
        exact RowBound.node RowBound.empty (ih _ _ _ (by rw [hod h1]; exact hi) DepthTrie.empty RowBound.empty)
    | node hl hr =>
      cases hb with | node hbl hbr =>
      simp only [trieAdd]; split_ifs with h
      · have h0 : i % 2 = 0 := by simpa using h
        exact RowBound.node (ih _ _ _ (by rw [hev h0]; exact hi) hl hbl) hbr
      · have h1 : i % 2 ≠ 0 := by simpa using h
        exact RowBound.node hbl (ih _ _ _ (by rw [hod h1]; exact hi) hr hbr)

private lemma evalTrieAux_trieAdd (ψ φ : Nat → ℂ) (d bm ka i j : Nat) (v : Int)
    (hi : i < 2 ^ d) {t : RowTrie} (ht : DepthTrie d t) :
    evalTrieAux ψ φ bm ka (trieAdd d i j v t) =
      (v : ℂ) * star (ψ (ka + bm * i)) * φ j + evalTrieAux ψ φ bm ka t := by
  induction d generalizing bm ka i t with
  | zero =>
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    cases ht with
    | empty =>
      simp only [trieAdd, evalTrieAux, evalRow_addAssoc, evalRow, mul_zero, add_zero]
      ring
    | leaf =>
      simp only [trieAdd, evalTrieAux, evalRow_addAssoc, mul_zero, add_zero]
      ring
  | succ d ih =>
    have hi2 : i / 2 < 2 ^ d := by
      rw [pow_succ] at hi; omega
    have hev : i % 2 = 0 → ka + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [mul_two_div_even bm i h]
    have hod : i % 2 ≠ 0 → (ka + bm) + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [add_assoc, mul_two_div_odd bm i h]
    cases ht with
    | empty =>
      simp only [trieAdd]; split_ifs with h
      · have h0 : i % 2 = 0 := by simpa using h
        simp only [evalTrieAux, ih (bm * 2) ka (i / 2) hi2 DepthTrie.empty, hev h0, add_zero]
      · have h1 : i % 2 ≠ 0 := by simpa using h
        simp only [evalTrieAux, ih (bm * 2) (ka + bm) (i / 2) hi2 DepthTrie.empty, hod h1, zero_add]
    | node hl hr =>
      simp only [trieAdd]; split_ifs with h
      · have h0 : i % 2 = 0 := by simpa using h
        simp only [evalTrieAux, ih (bm * 2) ka (i / 2) hi2 hl, hev h0]; ring
      · have h1 : i % 2 ≠ 0 := by simpa using h
        simp only [evalTrieAux, ih (bm * 2) (ka + bm) (i / 2) hi2 hr, hod h1]; ring

private lemma depthTrie_trieSingleRow (d i : Nat) (xs : List (Nat × Int)) :
    DepthTrie d (trieSingleRow d i xs) := by
  induction d generalizing i with
  | zero => exact DepthTrie.leaf
  | succ d ih =>
    simp only [trieSingleRow]; split_ifs
    · exact DepthTrie.node (ih _) DepthTrie.empty
    · exact DepthTrie.node DepthTrie.empty (ih _)

private lemma evalTrieAux_trieSingleRow (ψ φ : Nat → ℂ) (d bm ka i : Nat)
    (hi : i < 2 ^ d) (xs : List (Nat × Int)) :
    evalTrieAux ψ φ bm ka (trieSingleRow d i xs) =
      star (ψ (ka + bm * i)) * evalRow φ xs := by
  induction d generalizing bm ka i with
  | zero =>
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; simp [trieSingleRow, evalTrieAux]
  | succ d ih =>
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hev : i % 2 = 0 → ka + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [mul_two_div_even bm i h]
    have hod : i % 2 ≠ 0 → (ka + bm) + (bm * 2) * (i / 2) = ka + bm * i := fun h => by
      rw [add_assoc, mul_two_div_odd bm i h]
    simp only [trieSingleRow]; split_ifs with h
    · have h0 : i % 2 = 0 := by simpa using h
      simp only [evalTrieAux, ih (bm * 2) ka (i / 2) hi2, hev h0, add_zero]
    · have h1 : i % 2 ≠ 0 := by simpa using h
      simp only [evalTrieAux, ih (bm * 2) (ka + bm) (i / 2) hi2, hod h1, zero_add]

private lemma depthTrie_trieMerge {d : Nat} {t1 t2 : RowTrie}
    (h1 : DepthTrie d t1) (h2 : DepthTrie d t2) : DepthTrie d (trieMerge t1 t2) := by
  induction h1 generalizing t2 with
  | empty => exact h2
  | leaf =>
    cases h2 with
    | empty => exact DepthTrie.leaf
    | leaf => exact DepthTrie.leaf
  | node hl1 hr1 ihl ihr =>
    cases h2 with
    | empty => exact DepthTrie.node hl1 hr1
    | node hl2 hr2 => exact DepthTrie.node (ihl hl2) (ihr hr2)

private lemma colPred_trieMerge {P : Nat → Prop} {d : Nat} {t1 t2 : RowTrie}
    (h1 : DepthTrie d t1) (h2 : DepthTrie d t2) (c1 : ColPred P t1) (c2 : ColPred P t2) :
    ColPred P (trieMerge t1 t2) := by
  induction h1 generalizing t2 with
  | empty => exact c2
  | leaf =>
    cases h2 with
    | empty => exact c1
    | leaf =>
      cases c1 with | leaf hx =>
      cases c2 with | leaf hy =>
      exact ColPred.leaf (mergeRows_colPred hx hy)
  | node hl1 hr1 ihl ihr =>
    cases h2 with
    | empty => exact c1
    | node hl2 hr2 =>
      cases c1 with | node cl1 cr1 =>
      cases c2 with | node cl2 cr2 =>
      exact ColPred.node (ihl hl2 cl1 cl2) (ihr hr2 cr1 cr2)

private lemma rowBound_trieMerge {N d bm ka : Nat} {t1 t2 : RowTrie}
    (h1 : DepthTrie d t1) (h2 : DepthTrie d t2)
    (b1 : RowBound N bm ka t1) (b2 : RowBound N bm ka t2) :
    RowBound N bm ka (trieMerge t1 t2) := by
  induction h1 generalizing t2 bm ka with
  | empty => exact b2
  | leaf =>
    rename_i xs
    cases h2 with
    | empty => exact b1
    | leaf =>
      rename_i ys
      cases b1 with | leaf hxs =>
      cases b2 with | leaf hys =>
      refine RowBound.leaf fun hne => ?_
      by_cases h1e : xs = []
      · by_cases h2e : ys = []
        · simp [mergeRows, h1e, h2e] at hne
        · exact hys h2e
      · exact hxs h1e
  | node hl1 hr1 ihl ihr =>
    cases h2 with
    | empty => exact b1
    | node hl2 hr2 =>
      cases b1 with | node bl1 br1 =>
      cases b2 with | node bl2 br2 =>
      exact RowBound.node (ihl hl2 bl1 bl2) (ihr hr2 br1 br2)

private lemma evalTrieAux_trieMerge (ψ φ : Nat → ℂ) (bm ka : Nat) {d : Nat} {t1 t2 : RowTrie}
    (h1 : DepthTrie d t1) (h2 : DepthTrie d t2) :
    evalTrieAux ψ φ bm ka (trieMerge t1 t2) =
      evalTrieAux ψ φ bm ka t1 + evalTrieAux ψ φ bm ka t2 := by
  induction h1 generalizing t2 bm ka with
  | empty => simp [trieMerge, evalTrieAux]
  | leaf =>
    cases h2 with
    | empty => simp [trieMerge, evalTrieAux]
    | leaf => simp only [trieMerge, evalTrieAux, evalRow_mergeRows]; ring
  | node hl1 hr1 ihl ihr =>
    cases h2 with
    | empty => simp [trieMerge, evalTrieAux]
    | node hl2 hr2 =>
      simp only [trieMerge, evalTrieAux, ihl _ _ hl2, ihr _ _ hr2]; ring

private lemma depthTrie_trieScale {d : Nat} (c : Int) {t : RowTrie} (ht : DepthTrie d t) :
    DepthTrie d (trieScale c t) := by
  induction ht with
  | empty => exact DepthTrie.empty
  | leaf => exact DepthTrie.leaf
  | node _ _ ihl ihr => exact DepthTrie.node ihl ihr

private lemma colPred_trieScale {P : Nat → Prop} (c : Int) {t : RowTrie} (hc : ColPred P t) :
    ColPred P (trieScale c t) := by
  induction hc with
  | empty => exact ColPred.empty
  | leaf hxs => exact ColPred.leaf (scaleRow_colPred c hxs)
  | node _ _ ihl ihr => exact ColPred.node ihl ihr

private lemma rowBound_trieScale {N bm ka : Nat} (c : Int) {t : RowTrie} (hb : RowBound N bm ka t) :
    RowBound N bm ka (trieScale c t) := by
  induction hb with
  | empty => exact RowBound.empty
  | leaf hxs =>
    refine RowBound.leaf fun hne => hxs fun he => by simp [he, scaleRow] at hne
  | node _ _ ihl ihr => exact RowBound.node ihl ihr

private lemma evalTrieAux_trieScale (ψ φ : Nat → ℂ) (bm ka : Nat) (c : Int) (t : RowTrie) :
    evalTrieAux ψ φ bm ka (trieScale c t) = (c : ℂ) * evalTrieAux ψ φ bm ka t := by
  induction t generalizing bm ka with
  | empty => simp [trieScale, evalTrieAux]
  | leaf xs => simp only [trieScale, evalTrieAux, evalRow_scaleRow]; ring
  | node l r ihl ihr => simp only [trieScale, evalTrieAux, ihl, ihr]; ring

private lemma triePairUp_props {d : Nat} (ts : List RowTrie) (h : ∀ t ∈ ts, DepthTrie d t) :
    (∀ t ∈ triePairUp ts, DepthTrie d t) ∧
    ∀ (ψ φ : Nat → ℂ) (bm ka : Nat),
      ((triePairUp ts).map (evalTrieAux ψ φ bm ka)).sum = (ts.map (evalTrieAux ψ φ bm ka)).sum := by
  match ts with
  | [] => exact ⟨fun _ ht => by simp [triePairUp] at ht, fun _ _ _ _ => rfl⟩
  | [t] => exact ⟨h, fun _ _ _ _ => rfl⟩
  | t1 :: t2 :: rest =>
    have h1 : DepthTrie d t1 := h t1 (by simp)
    have h2 : DepthTrie d t2 := h t2 (by simp)
    have hrest : ∀ t ∈ rest, DepthTrie d t := fun t ht => h t (by simp [ht])
    have ih := triePairUp_props rest hrest
    refine ⟨fun t ht => ?_, fun ψ φ bm ka => ?_⟩
    · simp only [triePairUp, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact depthTrie_trieMerge h1 h2
      · exact ih.1 t ht
    · simp only [triePairUp, List.map_cons, List.sum_cons, evalTrieAux_trieMerge ψ φ bm ka h1 h2,
        ih.2 ψ φ bm ka, add_assoc]

private lemma triePairUp_colPred {P : Nat → Prop} {d : Nat} (ts : List RowTrie)
    (hd : ∀ t ∈ ts, DepthTrie d t) (hc : ∀ t ∈ ts, ColPred P t) :
    ∀ t ∈ triePairUp ts, ColPred P t := by
  match ts with
  | [] => intro t ht; simp [triePairUp] at ht
  | [t] => exact hc
  | t1 :: t2 :: rest =>
    intro t ht
    simp only [triePairUp, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact colPred_trieMerge (hd t1 (by simp)) (hd t2 (by simp)) (hc t1 (by simp)) (hc t2 (by simp))
    · exact triePairUp_colPred rest (fun x hx => hd x (by simp [hx])) (fun x hx => hc x (by simp [hx])) t ht

private lemma triePairUp_rowBound {N d bm ka : Nat} (ts : List RowTrie)
    (hd : ∀ t ∈ ts, DepthTrie d t) (hb : ∀ t ∈ ts, RowBound N bm ka t) :
    ∀ t ∈ triePairUp ts, RowBound N bm ka t := by
  match ts with
  | [] => intro t ht; simp [triePairUp] at ht
  | [t] => exact hb
  | t1 :: t2 :: rest =>
    intro t ht
    simp only [triePairUp, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact rowBound_trieMerge (hd t1 (by simp)) (hd t2 (by simp)) (hb t1 (by simp)) (hb t2 (by simp))
    · exact triePairUp_rowBound rest (fun x hx => hd x (by simp [hx])) (fun x hx => hb x (by simp [hx])) t ht

private lemma foldl_trieMerge_props {d : Nat} (init : RowTrie) (hinit : DepthTrie d init)
    (ts : List RowTrie) (h : ∀ t ∈ ts, DepthTrie d t) :
    DepthTrie d (ts.foldl trieMerge init) ∧
    ∀ (ψ φ : Nat → ℂ) (bm ka : Nat),
      evalTrieAux ψ φ bm ka (ts.foldl trieMerge init) =
        evalTrieAux ψ φ bm ka init + (ts.map (evalTrieAux ψ φ bm ka)).sum := by
  induction ts generalizing init with
  | nil => exact ⟨hinit, fun _ _ _ _ => by simp⟩
  | cons t rest ih =>
    have ht : DepthTrie d t := h t (by simp)
    have hrest : ∀ x ∈ rest, DepthTrie d x := fun x hx => h x (by simp [hx])
    have hstep := ih (trieMerge init t) (depthTrie_trieMerge hinit ht) hrest
    refine ⟨hstep.1, fun ψ φ bm ka => ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, hstep.2,
      evalTrieAux_trieMerge ψ φ bm ka hinit ht, add_assoc]

private lemma trieMergeAll_props (fuel : Nat) {d : Nat} (ts : List RowTrie)
    (h : ∀ t ∈ ts, DepthTrie d t) :
    DepthTrie d (trieMergeAll fuel ts) ∧
    ∀ (ψ φ : Nat → ℂ) (bm ka : Nat),
      evalTrieAux ψ φ bm ka (trieMergeAll fuel ts) = (ts.map (evalTrieAux ψ φ bm ka)).sum := by
  induction fuel generalizing ts with
  | zero =>
    cases ts with
    | nil => exact ⟨DepthTrie.empty, fun _ _ _ _ => by simp [trieMergeAll, evalTrieAux]⟩
    | cons t rest =>
      cases rest with
      | nil => exact ⟨h t (by simp), fun _ _ _ _ => by simp [trieMergeAll]⟩
      | cons t2 rest2 =>
        have hf := foldl_trieMerge_props RowTrie.empty DepthTrie.empty (t :: t2 :: rest2) h
        exact ⟨hf.1, fun ψ φ bm ka => by
          simpa [trieMergeAll, evalTrieAux] using hf.2 ψ φ bm ka⟩
  | succ fuel ih =>
    cases ts with
    | nil => exact ⟨DepthTrie.empty, fun _ _ _ _ => by simp [trieMergeAll, evalTrieAux]⟩
    | cons t rest =>
      cases rest with
      | nil => exact ⟨h t (by simp), fun _ _ _ _ => by simp [trieMergeAll]⟩
      | cons t2 rest2 =>
        have hp := triePairUp_props (t :: t2 :: rest2) h
        have hrec := ih (triePairUp (t :: t2 :: rest2)) hp.1
        exact ⟨hrec.1, fun ψ φ bm ka => by
          simp only [trieMergeAll, hrec.2, hp.2]⟩

private lemma trieMergeAll_colPred {P : Nat → Prop} (fuel : Nat) {d : Nat} (ts : List RowTrie)
    (hd : ∀ t ∈ ts, DepthTrie d t) (hc : ∀ t ∈ ts, ColPred P t) :
    ColPred P (trieMergeAll fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    cases ts with
    | nil => exact ColPred.empty
    | cons t rest =>
      cases rest with
      | nil => exact hc t (by simp)
      | cons t2 rest2 =>
        change ColPred P ((t :: t2 :: rest2).foldl trieMerge RowTrie.empty)
        have hfold : ∀ (init : RowTrie) (l : List RowTrie),
            DepthTrie d init → ColPred P init →
            (∀ x ∈ l, DepthTrie d x) → (∀ x ∈ l, ColPred P x) →
            ColPred P (l.foldl trieMerge init) := by
          intro init l; induction l generalizing init with
          | nil => intro _ hc0 _ _; exact hc0
          | cons a as iha =>
            intro hd0 hc0 hda hca
            exact iha _ (depthTrie_trieMerge hd0 (hda a (by simp)))
              (colPred_trieMerge hd0 (hda a (by simp)) hc0 (hca a (by simp)))
              (fun x hx => hda x (by simp [hx])) (fun x hx => hca x (by simp [hx]))
        exact hfold _ _ DepthTrie.empty ColPred.empty hd hc
  | succ fuel ih =>
    cases ts with
    | nil => exact ColPred.empty
    | cons t rest =>
      cases rest with
      | nil => exact hc t (by simp)
      | cons t2 rest2 =>
        exact ih _ (triePairUp_props _ hd).1 (triePairUp_colPred _ hd hc)

private lemma trieMergeAll_rowBound {N bm ka : Nat} (fuel : Nat) {d : Nat} (ts : List RowTrie)
    (hd : ∀ t ∈ ts, DepthTrie d t) (hb : ∀ t ∈ ts, RowBound N bm ka t) :
    RowBound N bm ka (trieMergeAll fuel ts) := by
  induction fuel generalizing ts with
  | zero =>
    cases ts with
    | nil => exact RowBound.empty
    | cons t rest =>
      cases rest with
      | nil => exact hb t (by simp)
      | cons t2 rest2 =>
        change RowBound N bm ka ((t :: t2 :: rest2).foldl trieMerge RowTrie.empty)
        have hfold : ∀ (init : RowTrie) (l : List RowTrie),
            DepthTrie d init → RowBound N bm ka init →
            (∀ x ∈ l, DepthTrie d x) → (∀ x ∈ l, RowBound N bm ka x) →
            RowBound N bm ka (l.foldl trieMerge init) := by
          intro init l; induction l generalizing init with
          | nil => intro _ hb0 _ _; exact hb0
          | cons a as iha =>
            intro hd0 hb0 hda hba
            exact iha _ (depthTrie_trieMerge hd0 (hda a (by simp)))
              (rowBound_trieMerge hd0 (hda a (by simp)) hb0 (hba a (by simp)))
              (fun x hx => hda x (by simp [hx])) (fun x hx => hba x (by simp [hx]))
        exact hfold _ _ DepthTrie.empty RowBound.empty hd hb
  | succ fuel ih =>
    cases ts with
    | nil => exact RowBound.empty
    | cons t rest =>
      cases rest with
      | nil => exact hb t (by simp)
      | cons t2 rest2 =>
        exact ih _ (triePairUp_props _ hd).1 (triePairUp_rowBound _ hd hb)

/-- Every leaf row of `trieGetRow d i t` inherits `ColPred P t`. -/
private lemma colPred_trieGetRow {P : Nat → Prop} {d : Nat} (i : Nat) {t : RowTrie}
    (hc : ColPred P t) : ∀ kv ∈ trieGetRow d i t, P kv.1 := by
  induction d generalizing i t with
  | zero =>
    cases t with
    | empty => simp [trieGetRow]
    | leaf xs => cases hc with | leaf h => exact h
    | node _ _ => simp [trieGetRow]
  | succ d ih =>
    cases t with
    | empty => simp [trieGetRow]
    | leaf _ => simp [trieGetRow]
    | node l r =>
      cases hc with | node hcl hcr =>
      simp only [trieGetRow]; split_ifs
      · exact ih _ hcl
      · exact ih _ hcr

/-- Out-of-range keys have empty rows when `RowBound N bm ka t` holds (`i < 2 ^ d`). -/
private lemma trieGetRow_eq_nil_of_ge {N d bm ka i : Nat} {t : RowTrie}
    (hb : RowBound N bm ka t) (hi : i < 2 ^ d) (hge : N ≤ ka + bm * i) :
    trieGetRow d i t = [] := by
  induction d generalizing bm ka i t with
  | zero =>
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    cases t with
    | empty => rfl
    | leaf xs =>
      cases hb with | leaf hxs =>
      by_contra hne; have := hxs hne; omega
    | node _ _ => rfl
  | succ d ih =>
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    cases t with
    | empty => rfl
    | leaf _ => rfl
    | node l r =>
      cases hb with | node hbl hbr =>
      simp only [trieGetRow]; split_ifs with h
      · have h0 : i % 2 = 0 := by simpa using h
        exact ih hbl hi2 (by rw [mul_two_div_even bm i h0]; exact hge)
      · have h1 : i % 2 ≠ 0 := by simpa using h
        exact ih hbr hi2 (by rw [add_assoc, mul_two_div_odd bm i h1]; exact hge)

/-- Exact expansion of `evalTrieAux` as a sum over `i ∈ List.range (2 ^ d)` via `trieGetRow`. -/
private lemma evalTrieAux_eq_sum_trieGetRow (ψ φ : Nat → ℂ) (d bm ka : Nat) {t : RowTrie}
    (ht : DepthTrie d t) :
    evalTrieAux ψ φ bm ka t =
      ((List.range (2 ^ d)).map fun i => star (ψ (ka + bm * i)) * evalRow φ (trieGetRow d i t)).sum := by
  induction d generalizing bm ka t with
  | zero =>
    cases ht with
    | empty => simp [evalTrieAux, trieGetRow, evalRow]
    | leaf => simp [evalTrieAux, trieGetRow]
  | succ d ih =>
    have hsplit : ∀ (m : Nat) (f : Nat → ℂ),
        ((List.range (2 * m)).map f).sum =
          ((List.range m).map fun k => f (2 * k)).sum +
          ((List.range m).map fun k => f (2 * k + 1)).sum := by
      intro m f; induction m with
      | zero => simp
      | succ k ihk =>
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.range_succ, List.range_succ,
            List.map_append, List.sum_append, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, List.map_singleton, List.sum_singleton, ihk,
            List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        ring
    rw [pow_succ', hsplit (2 ^ d)]
    cases ht with
    | empty =>
      have h0 : ∀ k : Nat, evalRow φ (trieGetRow (d + 1) k RowTrie.empty) = 0 := fun _ => by
        simp [trieGetRow, evalRow]
      simp [evalTrieAux, h0]
    | node hl hr =>
      simp only [evalTrieAux, ih (bm * 2) ka hl, ih (bm * 2) (ka + bm) hr]
      congr 1
      · refine congr_arg List.sum (List.map_congr_left fun k _ => ?_)
        have hev : (2 * k) % 2 == 0 := by simp
        have hdiv : 2 * k / 2 = k := by omega
        simp only [trieGetRow, hev, ↓reduceIte, hdiv]
        rw [show ka + bm * (2 * k) = ka + bm * 2 * k by ring]
      · refine congr_arg List.sum (List.map_congr_left fun k _ => ?_)
        have hod : ((2 * k + 1) % 2 == 0) = false := by simp
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simp only [trieGetRow, hod, Bool.false_eq_true, ↓reduceIte, hdiv]
        rw [show ka + bm * (2 * k + 1) = ka + bm + bm * 2 * k by ring]

/-- Truncated expansion of `evalTrie` over `List.range N` when `RowBound N 1 0 t` holds (`N ≤ 2 ^ d`). -/
private lemma evalTrie_eq_sum_range (φ : Nat → ℂ) {d N : Nat} (hN : N ≤ 2 ^ d) {t : RowTrie}
    (ht : DepthTrie d t) (hb : RowBound N 1 0 t) :
    evalTrie φ t = ((List.range N).map fun i => star (φ i) * evalRow φ (trieGetRow d i t)).sum := by
  unfold evalTrie
  rw [evalTrieAux_eq_sum_trieGetRow φ φ d 1 0 ht]
  have h2d : 2 ^ d = N + (2 ^ d - N) := by omega
  rw [h2d, List.range_add, List.map_append, List.sum_append]
  have htail : (((List.range (2 ^ d - N)).map (N + ·)).map fun i =>
      star (φ (0 + 1 * i)) * evalRow φ (trieGetRow d i t)).sum = 0 := by
    rw [List.map_map]
    refine List.sum_eq_zero fun c hc => ?_
    simp only [List.mem_map, List.mem_range] at hc
    rcases hc with ⟨k, hk, rfl⟩
    have hrow0 : trieGetRow d (N + k) t = [] := trieGetRow_eq_nil_of_ge hb (by omega) (by omega)
    simp only [Function.comp_apply, hrow0, evalRow, mul_zero]
  rw [htail, add_zero]
  refine congr_arg List.sum (List.map_congr_left fun i _ => ?_)
  simp

/-! ### Part 3: Target Evaluation `evalTrie (mon8 · z) (buildTargetTrie scale) = scale * (4 F₂(ψ) - 7)` -/

/-- Bijection between `F2 2` and `Fin 4` matching `x0 * 2 + x1`. -/
def f2ToFin4 (x : F2 2) : Fin 4 :=
  ⟨(x 0).val * 2 + (x 1).val, by have := (x 0).val_lt; have := (x 1).val_lt; omega⟩

def fin4ToF2 (i : Fin 4) : F2 2 :=
  fun k => if k = 0 then ((i.val / 2 : Nat) : ZMod 2) else ((i.val % 2 : Nat) : ZMod 2)

private lemma f2ToFin4_fin4ToF2 (i : Fin 4) : f2ToFin4 (fin4ToF2 i) = i := by
  fin_cases i <;> decide

private lemma fin4ToF2_f2ToFin4 (x : F2 2) : fin4ToF2 (f2ToFin4 x) = x := by
  ext k; fin_cases k
  · simp only [fin4ToF2, f2ToFin4, ↓reduceIte]
    have h0 := (x 0).val_lt; have h1 := (x 1).val_lt
    rw [show ((x 0).val * 2 + (x 1).val) / 2 = (x 0).val by omega]
    rcases zmod2_cases (x 0) with h | h <;> simp [h]
  · simp only [fin4ToF2, f2ToFin4, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    have h0 := (x 0).val_lt; have h1 := (x 1).val_lt
    rw [show ((x 0).val * 2 + (x 1).val) % 2 = (x 1).val by omega]
    rcases zmod2_cases (x 1) with h | h <;> simp [h]

def equivF2Fin4 : F2 2 ≃ Fin 4 where
  toFun := f2ToFin4
  invFun := fin4ToF2
  left_inv := fin4ToF2_f2ToFin4
  right_inv := f2ToFin4_fin4ToF2

private lemma fin4ToF2_xor (a b : Fin 4) :
    fin4ToF2 ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 2) a.isLt b.isLt⟩ = fin4ToF2 a + fin4ToF2 b := by
  fin_cases a <;> fin_cases b <;> (ext k; fin_cases k <;> decide)

private lemma chi_fin4ToF2 (b x : Fin 4) :
    chi (fin4ToF2 b) (fin4ToF2 x) = if dot2_2 b.val x.val == 1 then -1 else 1 := by
  fin_cases b <;> fin_cases x <;> decide

private def unitTup4 (x : Nat) : Tup4 :=
  (if x == 0 then 1 else 0, if x == 1 then 1 else 0, if x == 2 then 1 else 0, if x == 3 then 1 else 0)

private lemma monTup_unitTup4 (x : Fin 4) (z : Fin 4 → ℂ) : monTup (unitTup4 x.val) z = z x := by
  fin_cases x <;> simp [monTup, unitTup4]

private lemma monTup_tupOf4 (x0 x1 x2 x3 : Fin 4) (z : Fin 4 → ℂ) :
    monTup (tupOf4 x0.val x1.val x2.val x3.val) z = z x0 * z x1 * z x2 * z x3 := by
  have ht : tupOf4 x0.val x1.val x2.val x3.val =
      addTup4 (addTup4 (addTup4 (unitTup4 x0.val) (unitTup4 x1.val)) (unitTup4 x2.val)) (unitTup4 x3.val) := by
    simp [tupOf4, addTup4, unitTup4]
  rw [ht, monTup_add, monTup_add, monTup_add,
      monTup_unitTup4, monTup_unitTup4, monTup_unitTup4, monTup_unitTup4]

private lemma pauliPh_pow4 {n : ℕ} (p : PauliIdx n) : pauliPh p ^ 4 = 1 := by
  simp only [pauliPh]; split_ifs
  · norm_num
  · calc Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [Complex.I_sq]
      _ = 1 := by norm_num

/-- For any `ψ : QState 2` and `z i = ψ (fin4ToF2 i)`, `evalTrie (mon4 · z) buildF4Trie = (pauliMoment4 2 ψ : ℂ)`. -/
private lemma buildF4Trie_props (z : Fin 4 → ℂ) :
    DepthTrie 6 buildF4Trie ∧ RowBound 35 1 0 buildF4Trie ∧
    ColPred (· < 35) buildF4Trie ∧
    evalTrie (mon4 · z) buildF4Trie = (pauliMoment4 2 (fun x => z (f2ToFin4 x)) : ℂ) := by
  -- First prove depth/bounds/eval of `buildF4PauliX0Trie a b x0`!
  have hx0_props : ∀ (a b x0 : Nat) (ha : a < 4) (_hb : b < 4) (hx0 : x0 < 4),
      DepthTrie 6 (buildF4PauliX0Trie a b x0) ∧
      RowBound 35 1 0 (buildF4PauliX0Trie a b x0) ∧
      ColPred (· < 35) (buildF4PauliX0Trie a b x0) ∧
      evalTrie (mon4 · z) (buildF4PauliX0Trie a b x0) =
        ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4,
          ((if dot2_2 b (x0 ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
          star (z ⟨x0, hx0⟩ * z x1 * z x2 * z x3) *
          (z ⟨x0 ^^^ a, Nat.xor_lt_two_pow (n := 2) hx0 ha⟩ *
           z ⟨x1.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x1.isLt ha⟩ *
           z ⟨x2.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x2.isLt ha⟩ *
           z ⟨x3.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x3.isLt ha⟩) := by
    intro a b x0 ha _hb hx0
    have hfold4 : ∀ {α : Type} (f : α → Nat → α) (init : α),
        (List.range 4).foldl f init = f (f (f (f init 0) 1) 2) 3 := by
      intro α f init; rw [show List.range 4 = [0, 1, 2, 3] by decide]; rfl
    -- Helper: foldl of `trieAdd 6` over a list!
    have hstep3 : ∀ (x1 x2 : Fin 4) (t : RowTrie),
        DepthTrie 6 t → RowBound 35 1 0 t → ColPred (· < 35) t →
        let t' := (List.range 4).foldl (fun t x3 =>
          let sgn : Int := if dot2_2 b (x0 ^^^ x1.val ^^^ x2.val ^^^ x3) == 1 then -1 else 1
          let i4 := sym4Idx (tupOf4 x0 x1.val x2.val x3)
          let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1.val ^^^ a) (x2.val ^^^ a) (x3 ^^^ a))
          trieAdd 6 i4 j4 sgn t) t
        DepthTrie 6 t' ∧ RowBound 35 1 0 t' ∧ ColPred (· < 35) t' ∧
        evalTrie (mon4 · z) t' = evalTrie (mon4 · z) t +
          ∑ x3 : Fin 4,
            ((if dot2_2 b (x0 ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
            star (z ⟨x0, hx0⟩ * z x1 * z x2 * z x3) *
            (z ⟨x0 ^^^ a, Nat.xor_lt_two_pow (n := 2) hx0 ha⟩ *
             z ⟨x1.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x1.isLt ha⟩ *
             z ⟨x2.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x2.isLt ha⟩ *
             z ⟨x3.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x3.isLt ha⟩) := by
      intro x1 x2 t hd hrb hcp
      have hterm : ∀ x3 : Fin 4, ∀ tr : RowTrie,
          DepthTrie 6 tr → RowBound 35 1 0 tr → ColPred (· < 35) tr →
          let sgn : Int := if dot2_2 b (x0 ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then -1 else 1
          let i4 := sym4Idx (tupOf4 x0 x1.val x2.val x3.val)
          let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1.val ^^^ a) (x2.val ^^^ a) (x3.val ^^^ a))
          DepthTrie 6 (trieAdd 6 i4 j4 sgn tr) ∧
          RowBound 35 1 0 (trieAdd 6 i4 j4 sgn tr) ∧
          ColPred (· < 35) (trieAdd 6 i4 j4 sgn tr) ∧
          evalTrie (mon4 · z) (trieAdd 6 i4 j4 sgn tr) =
            (sgn : ℂ) *
            star (z ⟨x0, hx0⟩ * z x1 * z x2 * z x3) *
            (z ⟨x0 ^^^ a, Nat.xor_lt_two_pow (n := 2) hx0 ha⟩ *
             z ⟨x1.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x1.isLt ha⟩ *
             z ⟨x2.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x2.isLt ha⟩ *
             z ⟨x3.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x3.isLt ha⟩) +
            evalTrie (mon4 · z) tr := by
        intro x3 tr hdt hrt hct
        have hi := tupOf4_props hx0 x1.isLt x2.isLt x3.isLt
        have hj := tupOf4_props (Nat.xor_lt_two_pow (n := 2) hx0 ha)
          (Nat.xor_lt_two_pow (n := 2) x1.isLt ha) (Nat.xor_lt_two_pow (n := 2) x2.isLt ha)
          (Nat.xor_lt_two_pow (n := 2) x3.isLt ha)
        refine ⟨depthTrie_trieAdd 6 _ _ _ hdt,
                rowBound_trieAdd 6 1 0 _ _ _ (by omega) hdt hrt,
                colPred_trieAdd (P := (· < 35)) 6 _ _ hj.1 _ hdt hct, ?_⟩
        unfold evalTrie
        rw [evalTrieAux_trieAdd (mon4 · z) (mon4 · z) 6 1 0 _ _ _ (by omega) hdt]
        simp only [zero_add, one_mul, mon4, hi.2, hj.2]
        rw [monTup_tupOf4 ⟨x0, hx0⟩ x1 x2 x3 z,
            monTup_tupOf4 ⟨x0 ^^^ a, _⟩ ⟨x1.val ^^^ a, _⟩ ⟨x2.val ^^^ a, _⟩ ⟨x3.val ^^^ a, _⟩ z]
      dsimp only; rw [hfold4]
      have s0 := hterm 0 t hd hrb hcp
      have s1 := hterm 1 _ s0.1 s0.2.1 s0.2.2.1
      have s2 := hterm 2 _ s1.1 s1.2.1 s1.2.2.1
      have s3 := hterm 3 _ s2.1 s2.2.1 s2.2.2.1
      change DepthTrie 6 _ ∧ RowBound 35 1 0 _ ∧ ColPred (· < 35) _ ∧ _ at s0 s1 s2 s3
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl] at s0 s1 s2 s3
      refine ⟨s3.1, s3.2.1, s3.2.2.1, ?_⟩
      rw [s3.2.2.2, s2.2.2.2, s1.2.2.2, s0.2.2.2]
      conv_rhs => rw [Fin.sum_univ_four]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl]
      ring
    have hstep2 : ∀ (x1 : Fin 4) (t : RowTrie),
        DepthTrie 6 t → RowBound 35 1 0 t → ColPred (· < 35) t →
        let t' := (List.range 4).foldl (fun t x2 =>
          (List.range 4).foldl (fun t x3 =>
            let sgn : Int := if dot2_2 b (x0 ^^^ x1.val ^^^ x2 ^^^ x3) == 1 then -1 else 1
            let i4 := sym4Idx (tupOf4 x0 x1.val x2 x3)
            let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1.val ^^^ a) (x2 ^^^ a) (x3 ^^^ a))
            trieAdd 6 i4 j4 sgn t) t) t
        DepthTrie 6 t' ∧ RowBound 35 1 0 t' ∧ ColPred (· < 35) t' ∧
        evalTrie (mon4 · z) t' = evalTrie (mon4 · z) t +
          ∑ x2 : Fin 4, ∑ x3 : Fin 4,
            ((if dot2_2 b (x0 ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
            star (z ⟨x0, hx0⟩ * z x1 * z x2 * z x3) *
            (z ⟨x0 ^^^ a, Nat.xor_lt_two_pow (n := 2) hx0 ha⟩ *
             z ⟨x1.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x1.isLt ha⟩ *
             z ⟨x2.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x2.isLt ha⟩ *
             z ⟨x3.val ^^^ a, Nat.xor_lt_two_pow (n := 2) x3.isLt ha⟩) := by
      intro x1 t hd hrb hcp
      dsimp only
      rw [hfold4 (fun t x2 =>
        (List.range 4).foldl (fun t x3 =>
          let sgn : Int := if dot2_2 b (x0 ^^^ x1.val ^^^ x2 ^^^ x3) == 1 then -1 else 1
          let i4 := sym4Idx (tupOf4 x0 x1.val x2 x3)
          let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1.val ^^^ a) (x2 ^^^ a) (x3 ^^^ a))
          trieAdd 6 i4 j4 sgn t) t) t]
      have s0 := hstep3 x1 0 t hd hrb hcp
      have s1 := hstep3 x1 1 _ s0.1 s0.2.1 s0.2.2.1
      have s2 := hstep3 x1 2 _ s1.1 s1.2.1 s1.2.2.1
      have s3 := hstep3 x1 3 _ s2.1 s2.2.1 s2.2.2.1
      dsimp only at s0 s1 s2 s3
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl] at s0 s1 s2 s3
      refine ⟨s3.1, s3.2.1, s3.2.2.1, ?_⟩
      rw [s3.2.2.2, s2.2.2.2, s1.2.2.2, s0.2.2.2]
      conv_rhs => rw [Fin.sum_univ_four]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl]
      ring
    unfold buildF4PauliX0Trie
    rw [hfold4 (fun t x1 =>
      (List.range 4).foldl (fun t x2 =>
        (List.range 4).foldl (fun t x3 =>
          let sgn : Int := if dot2_2 b (x0 ^^^ x1 ^^^ x2 ^^^ x3) == 1 then -1 else 1
          let i4 := sym4Idx (tupOf4 x0 x1 x2 x3)
          let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1 ^^^ a) (x2 ^^^ a) (x3 ^^^ a))
          trieAdd 6 i4 j4 sgn t) t) t) RowTrie.empty]
    have s0 := hstep2 0 RowTrie.empty DepthTrie.empty RowBound.empty ColPred.empty
    have s1 := hstep2 1 _ s0.1 s0.2.1 s0.2.2.1
    have s2 := hstep2 2 _ s1.1 s1.2.1 s1.2.2.1
    have s3 := hstep2 3 _ s2.1 s2.2.1 s2.2.2.1
    dsimp only at s0 s1 s2 s3
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl] at s0 s1 s2 s3
    refine ⟨s3.1, s3.2.1, s3.2.2.1, ?_⟩
    rw [s3.2.2.2, s2.2.2.2, s1.2.2.2, s0.2.2.2]
    conv_rhs => rw [Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl, evalTrie, evalTrieAux]
    ring
  -- Next assemble `buildF4PauliTrie p` for each `p < 16`!
  have hdot_xor_all : ∀ b x0 x1 x2 x3 : Fin 4,
      ((if dot2_2 b.val x0.val == 1 then (-1 : ℤ) else 1) *
       (if dot2_2 b.val x1.val == 1 then (-1 : ℤ) else 1) *
       (if dot2_2 b.val x2.val == 1 then (-1 : ℤ) else 1) *
       (if dot2_2 b.val x3.val == 1 then (-1 : ℤ) else 1) : ℤ) =
      if dot2_2 b.val (x0.val ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then -1 else 1 := by
    decide
  have hp_props : ∀ (p : Nat) (hp : p < 16),
      DepthTrie 6 (buildF4PauliTrie p) ∧
      RowBound 35 1 0 (buildF4PauliTrie p) ∧
      ColPred (· < 35) (buildF4PauliTrie p) ∧
      evalTrie (mon4 · z) (buildF4PauliTrie p) =
        let a : Fin 4 := ⟨p >>> 2, by rw [Nat.shiftRight_eq_div_pow]; omega⟩
        let b : Fin 4 := ⟨p &&& 3, by rw [Nat.and_two_pow_sub_one_eq_mod p 2]; omega⟩
        let ψ : QState 2 := fun x => z (f2ToFin4 x)
        ((Complex.normSq (innerProd ψ (pauliApply (fin4ToF2 a, fin4ToF2 b) ψ)) ^ 2 : ℝ) : ℂ) := by
    intro p hp
    have ha : p >>> 2 < 4 := by rw [Nat.shiftRight_eq_div_pow]; omega
    have hb : p &&& 3 < 4 := by rw [Nat.and_two_pow_sub_one_eq_mod p 2]; omega
    let aF : Fin 4 := ⟨p >>> 2, ha⟩
    let bF : Fin 4 := ⟨p &&& 3, hb⟩
    let ψ : QState 2 := fun x => z (f2ToFin4 x)
    have hmem : ∀ t ∈ (List.range 4).map fun x0 => buildF4PauliX0Trie aF.val bF.val x0,
        DepthTrie 6 t ∧ RowBound 35 1 0 t ∧ ColPred (· < 35) t := by
      intro t ht; simp only [List.mem_map, List.mem_range] at ht
      rcases ht with ⟨x0, hx0, rfl⟩
      have h := hx0_props aF.val bF.val x0 ha hb hx0
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have hm := trieMergeAll_props 3 ((List.range 4).map fun x0 => buildF4PauliX0Trie aF.val bF.val x0)
      (fun t ht => (hmem t ht).1)
    refine ⟨hm.1,
            trieMergeAll_rowBound 3 _ (fun t ht => (hmem t ht).1) (fun t ht => (hmem t ht).2.1),
            trieMergeAll_colPred 3 _ (fun t ht => (hmem t ht).1) (fun t ht => (hmem t ht).2.2), ?_⟩
    -- Evaluate `innerProd ψ (pauliApply (a, b) ψ)` directly on `Fin 4`!
    have hreal : star (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) =
        innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ) := by
      rw [← innerProd_conj_symm, innerProd_pauliApply_right]
    have hns4 : ((Complex.normSq (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) ^ 2 : ℝ) : ℂ) =
        (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) ^ 4 := by
      have hns : ((Complex.normSq (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) : ℝ) : ℂ) =
          (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) ^ 2 := by
        rw [← Complex.mul_conj, ← Complex.star_def, hreal, sq]
      push_cast; rw [hns]; ring
    have hip : innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ) =
        pauliPh (fin4ToF2 aF, fin4ToF2 bF) *
          ∑ x : Fin 4, ((if dot2_2 bF.val x.val == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
            star (z x) * z ⟨x.val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) x.isLt ha⟩ := by
      unfold innerProd pauliApply
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv equivF2Fin4 _ _ fun x => ?_
      have hx : fin4ToF2 (f2ToFin4 x) = x := fin4ToF2_f2ToFin4 x
      have hxa : f2ToFin4 (x + fin4ToF2 aF) = ⟨(f2ToFin4 x).val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) (f2ToFin4 x).isLt ha⟩ := by
        apply equivF2Fin4.symm.injective
        change fin4ToF2 (f2ToFin4 (x + fin4ToF2 aF)) = fin4ToF2 ⟨(f2ToFin4 x).val ^^^ aF.val, _⟩
        rw [fin4ToF2_f2ToFin4, fin4ToF2_xor, hx]
      have hchi : chi (fin4ToF2 bF) x = if dot2_2 bF.val (f2ToFin4 x).val == 1 then -1 else 1 := by
        conv_lhs => rw [← hx]
        exact chi_fin4ToF2 bF (f2ToFin4 x)
      change star (z (f2ToFin4 x)) * (pauliPh (fin4ToF2 aF, fin4ToF2 bF) * (chi (fin4ToF2 bF) x : ℂ) *
          z (f2ToFin4 (x + fin4ToF2 aF))) =
        pauliPh (fin4ToF2 aF, fin4ToF2 bF) *
          (((if dot2_2 bF.val (f2ToFin4 x).val == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
            star (z (f2ToFin4 x)) * z ⟨(f2ToFin4 x).val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) (f2ToFin4 x).isLt ha⟩)
      rw [hxa, hchi]; ring
    -- Expand `(∑ x, f x) ^ 4` and note `pauliPh ^ 4 = 1`!
    have hpow4 : ((Complex.normSq (innerProd ψ (pauliApply (fin4ToF2 aF, fin4ToF2 bF) ψ)) ^ 2 : ℝ) : ℂ) =
        ∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4,
          ((if dot2_2 bF.val (x0.val ^^^ x1.val ^^^ x2.val ^^^ x3.val) == 1 then (-1 : ℤ) else 1 : ℤ) : ℂ) *
          star (z x0 * z x1 * z x2 * z x3) *
          (z ⟨x0.val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) x0.isLt ha⟩ *
           z ⟨x1.val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) x1.isLt ha⟩ *
           z ⟨x2.val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) x2.isLt ha⟩ *
           z ⟨x3.val ^^^ aF.val, Nat.xor_lt_two_pow (n := 2) x3.isLt ha⟩) := by
      rw [hns4, hip, mul_pow, pauliPh_pow4, one_mul]
      have hexp4 : ∀ f : Fin 4 → ℂ, (∑ x : Fin 4, f x) ^ 4 =
          ∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4, f x0 * f x1 * f x2 * f x3 := fun f => by
        simp only [Fin.sum_univ_four]; ring
      rw [hexp4]
      refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
        Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun x3 _ => ?_
      have hcast := congr_arg (Int.cast : ℤ → ℂ) (hdot_xor_all bF x0 x1 x2 x3)
      simp only [Int.cast_mul, star_mul'] at hcast ⊢
      rw [← hcast]; ring
    change evalTrie (mon4 · z) (trieMergeAll 3 ((List.range 4).map fun x0 => buildF4PauliX0Trie aF.val bF.val x0)) = _
    unfold evalTrie
    rw [hm.2, List.map_map, hpow4]
    have hr4 : List.range 4 = [0, 1, 2, 3] := by decide
    rw [hr4, Fin.sum_univ_four]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply, add_zero,
      Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 by rfl]
    have e0 := (hx0_props aF.val bF.val 0 ha hb (by omega)).2.2.2
    have e1 := (hx0_props aF.val bF.val 1 ha hb (by omega)).2.2.2
    have e2 := (hx0_props aF.val bF.val 2 ha hb (by omega)).2.2.2
    have e3 := (hx0_props aF.val bF.val 3 ha hb (by omega)).2.2.2
    change evalTrie (mon4 · z) (buildF4PauliX0Trie aF.val bF.val 0) +
      (evalTrie (mon4 · z) (buildF4PauliX0Trie aF.val bF.val 1) +
      (evalTrie (mon4 · z) (buildF4PauliX0Trie aF.val bF.val 2) +
       evalTrie (mon4 · z) (buildF4PauliX0Trie aF.val bF.val 3))) = _
    rw [e0, e1, e2, e3]
    have h0 : (⟨0, by omega⟩ : Fin 4) = 0 := rfl
    have h1 : (⟨1, by omega⟩ : Fin 4) = 1 := rfl
    have h2 : (⟨2, by omega⟩ : Fin 4) = 2 := rfl
    have h3 : (⟨3, by omega⟩ : Fin 4) = 3 := rfl
    simp only [h0, h1, h2, h3]; ring
  -- Merge all 16 Paulis!
  have hmem16 : ∀ t ∈ (List.range 16).map buildF4PauliTrie,
      DepthTrie 6 t ∧ RowBound 35 1 0 t ∧ ColPred (· < 35) t := by
    intro t ht; simp only [List.mem_map, List.mem_range] at ht
    rcases ht with ⟨p, hp, rfl⟩
    have h := hp_props p hp; exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hm16 := trieMergeAll_props 5 ((List.range 16).map buildF4PauliTrie) (fun t ht => (hmem16 t ht).1)
  refine ⟨hm16.1,
          trieMergeAll_rowBound 5 _ (fun t ht => (hmem16 t ht).1) (fun t ht => (hmem16 t ht).2.1),
          trieMergeAll_colPred 5 _ (fun t ht => (hmem16 t ht).1) (fun t ht => (hmem16 t ht).2.2), ?_⟩
  unfold buildF4Trie evalTrie
  rw [hm16.2, List.map_map]
  -- Match `∑ p ∈ List.range 16` with `∑ pq : PauliIdx 2`!
  let encP : PauliIdx 2 ≃ Fin 16 :=
    { toFun := fun pq => ⟨(f2ToFin4 pq.1).val * 4 + (f2ToFin4 pq.2).val, by
        have := (f2ToFin4 pq.1).isLt; have := (f2ToFin4 pq.2).isLt; omega⟩
      invFun := fun k => (fin4ToF2 ⟨k.val / 4, by omega⟩, fin4ToF2 ⟨k.val % 4, by omega⟩)
      left_inv := fun ⟨a, b⟩ => by
        have ha : (f2ToFin4 a).val < 4 := (f2ToFin4 a).isLt
        have hb : (f2ToFin4 b).val < 4 := (f2ToFin4 b).isLt
        apply Prod.ext
        · have h1 : (⟨((f2ToFin4 a).val * 4 + (f2ToFin4 b).val) / 4, by omega⟩ : Fin 4) = f2ToFin4 a :=
            Fin.ext (by dsimp only; omega)
          change fin4ToF2 ⟨((f2ToFin4 a).val * 4 + (f2ToFin4 b).val) / 4, _⟩ = a
          rw [h1, fin4ToF2_f2ToFin4]
        · have h2 : (⟨((f2ToFin4 a).val * 4 + (f2ToFin4 b).val) % 4, by omega⟩ : Fin 4) = f2ToFin4 b :=
            Fin.ext (by dsimp only; omega)
          change fin4ToF2 ⟨((f2ToFin4 a).val * 4 + (f2ToFin4 b).val) % 4, _⟩ = b
          rw [h2, fin4ToF2_f2ToFin4]
      right_inv := fun k => Fin.ext (by
        simp only [f2ToFin4_fin4ToF2]; omega) }
  have hsum16 : ∀ f : Nat → ℂ, ((List.range 16).map f).sum = ∑ k : Fin 16, f k.val := fun f => by
    have hgen : ∀ n : Nat, ((List.range n).map f).sum = ∑ k : Fin n, f k.val := fun n => by
      induction n with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            ih, Fin.sum_univ_castSucc]; rfl
    exact hgen 16
  rw [hsum16]
  unfold pauliMoment4
  rw [Complex.ofReal_sum]
  symm
  refine Fintype.sum_equiv encP _ _ fun pq => ?_
  have hp := (hp_props (encP pq).val (encP pq).isLt).2.2.2
  change _ = evalTrie (mon4 · z) (buildF4PauliTrie (encP pq).val)
  rw [hp]
  have ha_eq : (⟨(encP pq).val >>> 2, by rw [Nat.shiftRight_eq_div_pow]; have := (encP pq).isLt; omega⟩ : Fin 4) =
      f2ToFin4 pq.1 := by
    apply Fin.ext
    change ((f2ToFin4 pq.1).val * 4 + (f2ToFin4 pq.2).val) >>> 2 = (f2ToFin4 pq.1).val
    rw [Nat.shiftRight_eq_div_pow]
    have : (f2ToFin4 pq.2).val < 4 := (f2ToFin4 pq.2).isLt; omega
  have hb_eq : (⟨(encP pq).val &&& 3, by rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; omega⟩ : Fin 4) =
      f2ToFin4 pq.2 := by
    apply Fin.ext
    change ((f2ToFin4 pq.1).val * 4 + (f2ToFin4 pq.2).val) &&& 3 = (f2ToFin4 pq.2).val
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2]
    have : (f2ToFin4 pq.2).val < 4 := (f2ToFin4 pq.2).isLt; omega
  dsimp only
  rw [ha_eq, hb_eq, fin4ToF2_f2ToFin4, fin4ToF2_f2ToFin4]

/-- Degree-4 multinomial identity: `(∑ x : Fin 4, normSq (z x)) ^ 4 = ∑ i ∈ range 35, sym4Mult[i] * |mon4 i z|²`. -/
private lemma norm_pow4_eq_sym4Mult (z : Fin 4 → ℂ) :
    ((∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) ^ 4) =
      ((sym4List.zip sym4Mult).map fun (c, m) => (m : ℂ) * star (monTup c z) * monTup c z).sum := by
  have hns : ∀ c : Tup4, star (monTup c z) * monTup c z =
      (Complex.normSq (z 0) : ℂ) ^ c.1 * (Complex.normSq (z 1) : ℂ) ^ c.2.1 *
      (Complex.normSq (z 2) : ℂ) ^ c.2.2.1 * (Complex.normSq (z 3) : ℂ) ^ c.2.2.2 := fun c => by
    have h1 : ∀ w : ℂ, ∀ k : Nat, star (w ^ k) * w ^ k = (Complex.normSq w : ℂ) ^ k := fun w k => by
      rw [star_pow, ← mul_pow, mul_comm, Complex.star_def, Complex.mul_conj]
    simp only [monTup, star_mul']
    rw [← h1 (z 0) c.1, ← h1 (z 1) c.2.1, ← h1 (z 2) c.2.2.1, ← h1 (z 3) c.2.2.2]
    ring
  have hmap : ((sym4List.zip sym4Mult).map fun (c, m) => (m : ℂ) * star (monTup c z) * monTup c z) =
      ((sym4List.zip sym4Mult).map fun (c, m) =>
        (m : ℂ) * ((Complex.normSq (z 0) : ℂ) ^ c.1 * (Complex.normSq (z 1) : ℂ) ^ c.2.1 *
          (Complex.normSq (z 2) : ℂ) ^ c.2.2.1 * (Complex.normSq (z 3) : ℂ) ^ c.2.2.2)) :=
    List.map_congr_left fun x _ => by rcases x with ⟨c, m⟩; dsimp only; rw [mul_assoc, hns]
  rw [hmap, Fin.sum_univ_four]
  generalize (Complex.normSq (z 0) : ℂ) = a0
  generalize (Complex.normSq (z 1) : ℂ) = a1
  generalize (Complex.normSq (z 2) : ℂ) = a2
  generalize (Complex.normSq (z 3) : ℂ) = a3
  dsimp only [sym4List, sym4Mult, List.zip, List.zipWith, List.map, List.sum_cons, List.sum_nil]
  push_cast
  ring

private lemma multConvTrieAux_props (z : Fin 4 → ℂ) (s4 : List (Tup4 × Int))
    (hs4 : ∀ cm ∈ s4, cm.1 ∈ sym4List) (l : List (Tup4 × Int)) (hl : ∀ cm ∈ l, cm.1 ∈ sym4List)
    (t : RowTrie) (hd : DepthTrie 8 t) (hb : RowBound 165 1 0 t) :
    let ψ8 : Nat → ℂ := fun k => star (star (mon8 k z) * mon8 k z)
    DepthTrie 8 (multConvTrieAux s4 l t) ∧ RowBound 165 1 0 (multConvTrieAux s4 l t) ∧
    evalTrieAux ψ8 (fun _ => 1) 1 0 (multConvTrieAux s4 l t) =
      evalTrieAux ψ8 (fun _ => 1) 1 0 t +
      (l.map fun (c1, m1) => (m1 : ℂ) * star (monTup c1 z) * monTup c1 z).sum *
      (s4.map fun (c2, m2) => (m2 : ℂ) * star (monTup c2 z) * monTup c2 z).sum := by
  let ψ8 : Nat → ℂ := fun k => star (star (mon8 k z) * mon8 k z)
  have hinner : ∀ (c1 : Tup4) (hc1 : c1 ∈ sym4List) (m1 : Int) (l2 : List (Tup4 × Int)),
      (∀ cm ∈ l2, cm.1 ∈ sym4List) →
      ∀ t0 : RowTrie, DepthTrie 8 t0 → RowBound 165 1 0 t0 →
      let t' := l2.foldl (fun tr (c2, m2) => trieAdd 8 (sym8Idx (addTup4 c1 c2)) 0 (m1 * m2) tr) t0
      DepthTrie 8 t' ∧ RowBound 165 1 0 t' ∧
      evalTrieAux ψ8 (fun _ => 1) 1 0 t' =
        evalTrieAux ψ8 (fun _ => 1) 1 0 t0 +
        ((m1 : ℂ) * star (monTup c1 z) * monTup c1 z) *
        (l2.map fun (c2, m2) => (m2 : ℂ) * star (monTup c2 z) * monTup c2 z).sum := by
    intro c1 hc1 m1 l2 hl2
    induction l2 with
    | nil => intro t0 hd0 hb0; exact ⟨hd0, hb0, by simp⟩
    | cons cm rest ih =>
      rcases cm with ⟨c2, m2⟩
      intro t0 hd0 hb0
      have hc2 : c2 ∈ sym4List := hl2 (c2, m2) (by simp)
      have hadd := add4To8Table_valid
      simp only [checkAdd4To8Table, List.all_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hadd
      have hk := hadd c1 hc1 c2 hc2
      have hd1 := depthTrie_trieAdd 8 (sym8Idx (addTup4 c1 c2)) 0 (m1 * m2) hd0
      have hb1 := rowBound_trieAdd 8 1 0 (sym8Idx (addTup4 c1 c2)) 0 (m1 * m2) (by omega) hd0 hb0
      have he1 := evalTrieAux_trieAdd ψ8 (fun _ => 1) 8 1 0 (sym8Idx (addTup4 c1 c2)) 0 (m1 * m2) (by omega) hd0
      have hrec := ih (fun x hx => hl2 x (by simp [hx])) _ hd1 hb1
      refine ⟨hrec.1, hrec.2.1, ?_⟩
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, hrec.2.2, he1, zero_add, one_mul, mul_one]
      have hw : star (ψ8 (sym8Idx (addTup4 c1 c2))) =
          (star (monTup c1 z) * monTup c1 z) * (star (monTup c2 z) * monTup c2 z) := by
        simp only [ψ8, star_star, mon8, hk.2, monTup_add, star_mul']; ring
      rw [hw, Int.cast_mul]; ring
  induction l generalizing t with
  | nil => exact ⟨hd, hb, by simp [multConvTrieAux]⟩
  | cons cm rest ih =>
    rcases cm with ⟨c1, m1⟩
    have h1 := hinner c1 (hl (c1, m1) (by simp)) m1 s4 hs4 t hd hb
    have hrec := ih (fun x hx => hl x (by simp [hx])) _ h1.1 h1.2.1
    refine ⟨hrec.1, hrec.2.1, ?_⟩
    simp only [multConvTrieAux, List.foldl_cons, List.map_cons, List.sum_cons] at hrec ⊢
    rw [hrec.2.2, h1.2.2]; ring

/-- Degree-8 multinomial identity: `(∑ x : Fin 4, normSq (z x)) ^ 8 = ∑ i < 165, sym8Mult[i] * |mon8 i z|²`,
    proved by squaring `norm_pow4_eq_sym4Mult` + the `by rfl` convolution check `multConv_valid`! -/
private lemma norm_pow8_eq_sym8Mult (z : Fin 4 → ℂ) :
    ((∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) ^ 8) =
      (((List.range 165).zip sym8Mult).map fun (k, m) => (m : ℂ) * star (mon8 k z) * mon8 k z).sum := by
  have hsq : ((∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) ^ 8) =
      ((∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) ^ 4) * ((∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) ^ 4) := by ring
  rw [hsq, norm_pow4_eq_sym4Mult]
  let w8 : Nat → ℂ := fun k => star (mon8 k z) * mon8 k z
  let ψ8 : Nat → ℂ := fun k => star (w8 k)
  have htr_props := multConvTrieAux_props z (sym4List.zip sym4Mult)
    (fun x hx => (List.of_mem_zip hx).1) (sym4List.zip sym4Mult)
    (fun x hx => (List.of_mem_zip hx).1) RowTrie.empty DepthTrie.empty RowBound.empty
  change DepthTrie 8 multConvTrie ∧ RowBound 165 1 0 multConvTrie ∧
      evalTrieAux ψ8 (fun _ => 1) 1 0 multConvTrie = _ at htr_props
  have htr_eval : evalTrieAux ψ8 (fun _ => 1) 1 0 multConvTrie =
      ((sym4List.zip sym4Mult).map fun (c, m) => (m : ℂ) * star (monTup c z) * monTup c z).sum *
      ((sym4List.zip sym4Mult).map fun (c, m) => (m : ℂ) * star (monTup c z) * monTup c z).sum := by
    simpa [evalTrieAux] using htr_props.2.2
  rw [← htr_eval]
  rw [evalTrieAux_eq_sum_trieGetRow ψ8 (fun _ => 1) 8 1 0 htr_props.1]
  have h256 : 2 ^ 8 = 165 + 91 := by norm_num
  rw [h256, List.range_add, List.map_append, List.sum_append]
  have htail : (((List.range 91).map (165 + ·)).map fun i =>
      star (ψ8 (0 + 1 * i)) * evalRow (fun _ => 1) (trieGetRow 8 i multConvTrie)).sum = 0 := by
    rw [List.map_map]
    refine List.sum_eq_zero fun c hc => ?_
    simp only [List.mem_map, List.mem_range] at hc
    rcases hc with ⟨k, hk, rfl⟩
    have hrow0 : trieGetRow 8 (165 + k) multConvTrie = [] :=
      trieGetRow_eq_nil_of_ge htr_props.2.1 (by omega) (by omega)
    simp only [Function.comp_apply, hrow0, evalRow, mul_zero]
  rw [htail, add_zero]
  have hconv := multConv_valid
  simp only [checkMultConv, List.all_eq_true] at hconv
  have hzip_eq : ((List.range 165).map fun i =>
        star (ψ8 (0 + 1 * i)) * evalRow (fun _ => 1) (trieGetRow 8 i multConvTrie)) =
      ((List.range 165).zip sym8Mult).map fun (k, m) => (m : ℂ) * star (mon8 k z) * mon8 k z := by
    apply List.ext_getElem
    · simp [sym8Mult_len]
    · intro i hi1 hi2
      have hi165 : i < 165 := by simpa using hi1
      have hmem : (i, sym8Mult[i]'(by rw [sym8Mult_len]; exact hi165)) ∈ (List.range 165).zip sym8Mult := by
        rw [List.mem_iff_getElem]
        refine ⟨i, by simp [sym8Mult_len]; omega, by simp⟩
      have hrow : trieGetRow 8 i multConvTrie = [(0, sym8Mult[i]'(by rw [sym8Mult_len]; exact hi165))] := by
        have h1 := hconv (i, sym8Mult[i]'(by rw [sym8Mult_len]; exact hi165)) hmem
        dsimp only at h1
        exact beq_iff_eq.mp h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_zip, zero_add, one_mul]
      change star (ψ8 i) * evalRow (fun _ => 1) (trieGetRow 8 i multConvTrie) = _
      rw [hrow]
      simp only [evalRow, ψ8, star_star, w8, mul_one, add_zero]; ring
  rw [hzip_eq]

/-- **Exact Target Soundness**: For any `z : Fin 4 → ℂ` with `∑ x, normSq (z x) = 1` (i.e. unit state `ψ`),
    `evalTrie (mon8 · z) (buildTargetTrie scale) = (((scale : ℝ) * (4 * pauliMoment4 2 ψ - 7) : ℝ) : ℂ)`. -/
private lemma evalTrie_buildTargetTrie (scale : Int) (z : Fin 4 → ℂ)
    (hunit : ∑ x : Fin 4, Complex.normSq (z x) = 1) :
    evalTrie (mon8 · z) (buildTargetTrie scale) =
      (((scale : ℝ) * (4 * pauliMoment4 2 (fun x => z (f2ToFin4 x)) - 7) : ℝ) : ℂ) := by
  have hf4 := buildF4Trie_props z
  -- First evaluate `t1` (`4 * scale * F₂ * ‖z‖⁸`)!
  let s4Pairs := sym4List.zip sym4Mult
  let f4 := buildF4Trie
  have hpair_trie : ∀ (ci : Tup4) (hci : ci ∈ sym4List) (j4 : Nat) (hj4 : j4 < 35) (v : Int),
      let cj := sym4List.getD j4 (0, 0, 0, 0)
      let t := s4Pairs.foldl (fun t (ck, mk) =>
        trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty
      DepthTrie 8 t ∧
      evalTrie (mon8 · z) t =
        (scale : ℂ) * 4 * ((v : ℂ) * star (monTup ci z) * monTup cj z) *
          (s4Pairs.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum := by
    intro ci hci j4 hj4 v
    have hcj : sym4List.getD j4 (0, 0, 0, 0) ∈ sym4List :=
      list_getD_mem sym4List _ (by rw [sym4List_len]; exact hj4)
    have hfold : ∀ (l : List (Tup4 × Int)), (∀ cm ∈ l, cm.1 ∈ sym4List) →
        ∀ t : RowTrie, DepthTrie 8 t →
        let t' := l.foldl (fun t (ck, mk) =>
          trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 (sym4List.getD j4 (0,0,0,0)) ck))
            (scale * 4 * v * mk) t) t
        DepthTrie 8 t' ∧
        evalTrie (mon8 · z) t' = evalTrie (mon8 · z) t +
          (scale : ℂ) * 4 * ((v : ℂ) * star (monTup ci z) * monTup (sym4List.getD j4 (0,0,0,0)) z) *
            (l.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum := by
      intro l hl
      induction l with
      | nil => intro t hd; exact ⟨hd, by simp⟩
      | cons cm rest ih =>
        rcases cm with ⟨ck, mk⟩
        intro t hd
        have hck : ck ∈ sym4List := hl (ck, mk) (by simp)
        have hadd := add4To8Table_valid
        simp only [checkAdd4To8Table, List.all_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, beq_iff_eq] at hadd
        have hi := hadd ci hci ck hck
        have hj := hadd _ hcj ck hck
        have hd1 := depthTrie_trieAdd 8 (sym8Idx (addTup4 ci ck))
          (sym8Idx (addTup4 (sym4List.getD j4 (0,0,0,0)) ck)) (scale * 4 * v * mk) hd
        have he1 := evalTrieAux_trieAdd (mon8 · z) (mon8 · z) 8 1 0
          (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 (sym4List.getD j4 (0,0,0,0)) ck))
          (scale * 4 * v * mk) (by omega) hd
        have hrec := ih (fun x hx => hl x (by simp [hx])) _ hd1
        refine ⟨hrec.1, ?_⟩
        simp only [List.foldl_cons, List.map_cons, List.sum_cons, hrec.2]
        have hm1 : mon8 (sym8Idx (addTup4 ci ck)) z = monTup ci z * monTup ck z := by
          simp only [mon8, hi.2, monTup_add]
        have hm2 : mon8 (sym8Idx (addTup4 (sym4List.getD j4 (0,0,0,0)) ck)) z =
            monTup (sym4List.getD j4 (0,0,0,0)) z * monTup ck z := by
          simp only [mon8, hj.2, monTup_add]
        change evalTrieAux (mon8 · z) (mon8 · z) 1 0 _ + _ = evalTrieAux (mon8 · z) (mon8 · z) 1 0 t + _
        rw [he1]
        simp only [zero_add, one_mul, hm1, hm2, star_mul']
        push_cast; ring
    have h0 := hfold s4Pairs (fun x hx => (List.of_mem_zip hx).1) RowTrie.empty DepthTrie.empty
    exact ⟨h0.1, by simpa [evalTrie, evalTrieAux] using h0.2⟩
  -- Assemble over `f4Tries`!
  have hf4_row : ∀ (ci : Tup4) (hci : ci ∈ sym4List) (row : List (Nat × Int))
      (hcol : ∀ kv ∈ row, kv.1 < 35),
      let t := if row.isEmpty then RowTrie.empty else trieMergeAll 6 (row.map fun (j4, v) =>
        let cj := sym4List.getD j4 (0, 0, 0, 0)
        s4Pairs.foldl (fun t (ck, mk) =>
          trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty)
      DepthTrie 8 t ∧
      evalTrie (mon8 · z) t =
        (scale : ℂ) * 4 * (star (monTup ci z) * evalRow (mon4 · z) row) *
          (s4Pairs.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum := by
    intro ci hci row hcol
    dsimp only
    split_ifs with hemp
    · have hnil : row = [] := List.isEmpty_iff.mp hemp
      simp [hnil, DepthTrie.empty, evalTrie, evalTrieAux, evalRow]
    · let rowTries := row.map fun (j4, v) =>
        let cj := sym4List.getD j4 (0, 0, 0, 0)
        s4Pairs.foldl (fun t (ck, mk) =>
          trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty
      have hmd : ∀ t ∈ rowTries, DepthTrie 8 t := by
        intro t ht; simp only [rowTries, List.mem_map] at ht
        rcases ht with ⟨⟨j4, v⟩, hjv, rfl⟩
        exact (hpair_trie ci hci j4 (hcol _ hjv) v).1
      have hm := trieMergeAll_props 6 rowTries hmd
      refine ⟨hm.1, ?_⟩
      unfold evalTrie
      rw [hm.2, List.map_map]
      have hrow_sum : ∀ (l : List (Nat × Int)), (∀ kv ∈ l, kv.1 < 35) →
          (l.map (evalTrieAux (mon8 · z) (mon8 · z) 1 0 ∘ fun (j4, v) =>
            let cj := sym4List.getD j4 (0, 0, 0, 0)
            s4Pairs.foldl (fun t (ck, mk) =>
              trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 cj ck))
                (scale * 4 * v * mk) t) RowTrie.empty)).sum =
          (scale : ℂ) * 4 * (star (monTup ci z) * evalRow (mon4 · z) l) *
            (s4Pairs.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum := by
        intro l hl; induction l with
        | nil => simp [evalRow]
        | cons kv rest ih =>
          rcases kv with ⟨j4, v⟩
          simp only [List.map_cons, List.sum_cons, Function.comp_apply, evalRow]
          change evalTrie (mon8 · z) _ + _ = _
          rw [(hpair_trie ci hci j4 (hl (j4, v) (by simp)) v).2, ih (fun x hx => hl x (by simp [hx]))]
          unfold mon4; ring
      exact hrow_sum row hcol
  -- Merge `f4Tries` and `diagTries`!
  let f4Tries := (sym4List.zip (List.range 35)).map fun (ci, i4) =>
    let row := trieGetRow 6 i4 f4
    if row.isEmpty then RowTrie.empty
    else trieMergeAll 6 (row.map fun (j4, v) =>
      let cj := sym4List.getD j4 (0, 0, 0, 0)
      s4Pairs.foldl (fun t (ck, mk) =>
        trieAdd 8 (sym8Idx (addTup4 ci ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty)
  have hf4T_d : ∀ t ∈ f4Tries, DepthTrie 8 t := by
    intro t ht; simp only [f4Tries, List.mem_map] at ht
    rcases ht with ⟨⟨ci, i4⟩, hmem, rfl⟩
    exact (hf4_row ci (List.of_mem_zip hmem).1 (trieGetRow 6 i4 f4) (colPred_trieGetRow i4 hf4.2.2.1)).1
  have ht1 := trieMergeAll_props 7 f4Tries hf4T_d
  let diagTries := ((List.range 165).zip sym8Mult).map fun (ii, m8) =>
    trieSingleRow 8 ii [(ii, -(scale * 7 * m8))]
  have hdiag_d : ∀ t ∈ diagTries, DepthTrie 8 t := by
    intro t ht; simp only [diagTries, List.mem_map] at ht
    rcases ht with ⟨⟨ii, m8⟩, _, rfl⟩; exact depthTrie_trieSingleRow 8 ii _
  have ht2 := trieMergeAll_props 9 diagTries hdiag_d
  unfold buildTargetTrie evalTrie
  rw [evalTrieAux_trieMerge (mon8 · z) (mon8 · z) 1 0 ht1.1 ht2.1, ht1.2, ht2.2]
  -- Evaluate the `t1` sum!
  have hsum1 : (f4Tries.map (evalTrieAux (mon8 · z) (mon8 · z) 1 0)).sum =
      (scale : ℂ) * 4 * evalTrie (mon4 · z) buildF4Trie *
        (s4Pairs.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum := by
    simp only [f4Tries, List.map_map]
    have hlist : ((sym4List.zip (List.range 35)).map fun x =>
          evalTrieAux (mon8 · z) (mon8 · z) 1 0 (let row := trieGetRow 6 x.2 f4
            if row.isEmpty then RowTrie.empty
            else trieMergeAll 6 (row.map fun (j4, v) =>
              let cj := sym4List.getD j4 (0, 0, 0, 0)
              s4Pairs.foldl (fun t (ck, mk) =>
                trieAdd 8 (sym8Idx (addTup4 x.1 ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty))) =
        ((List.range 35).map fun i4 =>
          (scale : ℂ) * 4 * (star (mon4 i4 z) * evalRow (mon4 · z) (trieGetRow 6 i4 f4)) *
            (s4Pairs.map fun (ck, mk) => (mk : ℂ) * star (monTup ck z) * monTup ck z).sum) := by
      apply List.ext_getElem
      · simp [sym4List_len]
      · intro i hi1 hi2
        have hi35 : i < 35 := by simpa using hi2
        have hci_mem : sym4List[i]'(by rw [sym4List_len]; exact hi35) ∈ sym4List :=
          List.getElem_mem _
        simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
        change evalTrie (mon8 · z) _ = _
        rw [(hf4_row _ hci_mem (trieGetRow 6 i f4) (colPred_trieGetRow i hf4.2.2.1)).2]
        simp only [mon4, List.getD, List.getElem?_eq_getElem (by rw [sym4List_len]; exact hi35), Option.getD_some]
    change (((sym4List.zip (List.range 35)).map fun x =>
          evalTrieAux (mon8 · z) (mon8 · z) 1 0 (let row := trieGetRow 6 x.2 f4
            if row.isEmpty then RowTrie.empty
            else trieMergeAll 6 (row.map fun (j4, v) =>
              let cj := sym4List.getD j4 (0, 0, 0, 0)
              s4Pairs.foldl (fun t (ck, mk) =>
                trieAdd 8 (sym8Idx (addTup4 x.1 ck)) (sym8Idx (addTup4 cj ck)) (scale * 4 * v * mk) t) RowTrie.empty)))).sum = _
    rw [hlist]
    have hfactor : ∀ (a b : ℂ) (g : Nat → ℂ) (l : List Nat),
        (l.map fun x => a * g x * b).sum = a * (l.map g).sum * b := by
      intro a b g l; induction l with
      | nil => simp
      | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [hfactor ((scale : ℂ) * 4) _ (fun i4 => star (mon4 i4 z) * evalRow (mon4 · z) (trieGetRow 6 i4 f4)) (List.range 35),
        ← evalTrie_eq_sum_range (mon4 · z) (d := 6) (N := 35) (by norm_num) hf4.1 hf4.2.1]
  -- Evaluate the `diagTries` sum!
  have hsum2 : (diagTries.map (evalTrieAux (mon8 · z) (mon8 · z) 1 0)).sum =
      -((scale : ℂ) * 7) *
        (((List.range 165).zip sym8Mult).map fun (k, m) => (m : ℂ) * star (mon8 k z) * mon8 k z).sum := by
    simp only [diagTries, List.map_map]
    have hlist : (((List.range 165).zip sym8Mult).map fun x =>
          evalTrieAux (mon8 · z) (mon8 · z) 1 0 (trieSingleRow 8 x.1 [(x.1, -(scale * 7 * x.2))])) =
        (((List.range 165).zip sym8Mult).map fun x =>
          -((scale : ℂ) * 7) * ((x.2 : ℂ) * star (mon8 x.1 z) * mon8 x.1 z)) := by
      refine List.map_congr_left fun x hx => ?_
      have hx1 : x.1 < 165 := List.mem_range.mp (List.of_mem_zip hx).1
      rw [evalTrieAux_trieSingleRow (mon8 · z) (mon8 · z) 8 1 0 x.1 (by omega)]
      simp only [zero_add, one_mul, evalRow, add_zero, Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
      ring
    change (((List.range 165).zip sym8Mult).map fun x =>
      evalTrieAux (mon8 · z) (mon8 · z) 1 0 (trieSingleRow 8 x.1 [(x.1, -(scale * 7 * x.2))])).sum = _
    rw [hlist]
    have hmul_sum : ∀ {α : Type} (c : ℂ) (g : α → ℂ) (l : List α),
        (l.map fun x => c * g x).sum = c * (l.map g).sum := by
      intro α c g l; induction l with | nil => simp | cons a as ih => simp [ih, mul_add]
    rw [hmul_sum (-((scale : ℂ) * 7)) (fun x : Nat × Int => (x.2 : ℂ) * star (mon8 x.1 z) * mon8 x.1 z)]
  rw [hsum1, hsum2, hf4.2.2.2, ← norm_pow4_eq_sym4Mult, ← norm_pow8_eq_sym8Mult]
  have huC : (∑ x : Fin 4, (Complex.normSq (z x) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, hunit, Complex.ofReal_one]
  rw [huC]
  push_cast; ring

/-! ### Part 4: Certificate Block Soundness & Hermitian Cholesky + Diagonal Dominance PSD -/

/-- Matrix entry helper `A[i][j]` as integer. -/
private def matGet (M : List (List Int)) (i j : Nat) : Int :=
  (M.getD i []).getD j 0

private lemma dotInt_eq_sum (xs ys : List Int) (n : Nat) (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    dotInt xs ys = ∑ k : Fin n, xs.getD k.val 0 * ys.getD k.val 0 := by
  induction n generalizing xs ys with
  | zero =>
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hx0, hy0, dotInt]
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    cases xs with
    | nil =>
      simp only [dotInt, List.getD_nil, zero_mul, zero_add]
      symm; refine Finset.sum_eq_zero fun k _ => by simp
    | cons x xr =>
      cases ys with
      | nil =>
        simp only [dotInt, List.getD_nil, mul_zero, zero_add]
        symm; refine Finset.sum_eq_zero fun k _ => by simp
      | cons y yr =>
        simp only [dotInt, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ]
        rw [ih xr yr (by simp at hx; omega) (by simp at hy; omega)]

/-- **Hermitian Cholesky + Diagonal Dominance PSD Theorem**:
    If `checkSymAndDD b = true`, then for EVERY complex vector `y : Fin b.r → ℂ`,
    `0 ≤ (∑ p : Fin b.r, ∑ q : Fin b.r, (matGet b.A p.val q.val : ℂ) * star (y p) * y q).re`. -/
private lemma cholesky_dd_nonneg (b : OrbitBlockCert) (hvalid : checkSymAndDD b = true)
    (y : Fin b.r → ℂ) :
    0 ≤ (∑ p : Fin b.r, ∑ q : Fin b.r, (matGet b.A p.val q.val : ℂ) * star (y p) * y q).re := by
  -- Unpack `checkSymAndDD b = true`!
  unfold checkSymAndDD at hvalid
  simp only [Bool.and_eq_true] at hvalid
  obtain ⟨⟨⟨hrows, hsym⟩, _⟩, _⟩ := hvalid
  -- First extract `lenOk` and per-row diagonal dominance from `hrows`!
  let s2 := b.S * b.S
  have hfold_inv : ∀ (l : List (List Int × List Int)) (st : Bool × Nat),
      (l.foldl (fun (acc : Bool × Nat) (aw : List Int × List Int) =>
        let i := acc.2
        if !acc.1 || aw.1.length != b.r || aw.2.length != i + 1 then (false, i + 1)
        else
          let res := (aw.1.zip b.W).foldl (fun (st : Int × Int × Nat) (awj : Int × List Int) =>
            let j := st.2.2
            let eij := s2 * awj.1 - dotInt aw.2 awj.2
            if j == i then (eij, st.2.1, j + 1)
            else (st.1, st.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)
          (res.1 >= res.2.1, i + 1)) st).1 = true →
      st.1 = true ∧
      ∀ k (hk : k < l.length),
        let aw := l[k]'hk
        aw.1.length = b.r ∧ aw.2.length = st.2 + k + 1 ∧
        let res := (aw.1.zip b.W).foldl (fun (st2 : Int × Int × Nat) (awj : Int × List Int) =>
          let j := st2.2.2
          let eij := s2 * awj.1 - dotInt aw.2 awj.2
          if j == st.2 + k then (eij, st2.2.1, j + 1)
          else (st2.1, st2.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)
        res.1 ≥ res.2.1 := by
    intro l; induction l with
    | nil => intro st h; exact ⟨h, fun k hk => by simp at hk⟩
    | cons aw rest ih =>
      intro st h
      simp only [List.foldl_cons] at h
      have hfalse : ∀ (l' : List (List Int × List Int)) (m : Nat),
          (l'.foldl (fun (acc : Bool × Nat) (aw : List Int × List Int) =>
            let i := acc.2
            if !acc.1 || aw.1.length != b.r || aw.2.length != i + 1 then (false, i + 1)
            else
              let res := (aw.1.zip b.W).foldl (fun (st : Int × Int × Nat) (awj : Int × List Int) =>
                let j := st.2.2
                let eij := s2 * awj.1 - dotInt aw.2 awj.2
                if j == i then (eij, st.2.1, j + 1)
                else (st.1, st.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)
              (res.1 >= res.2.1, i + 1)) (false, m)).1 = false := by
        intro l'; induction l' with
        | nil => intro _; rfl
        | cons _ _ ih' => intro m; simp only [List.foldl_cons, Bool.not_false, Bool.true_or, ↓reduceIte]; exact ih' _
      split_ifs at h with hbad
      · rw [hfalse rest] at h; exact absurd h (by decide)
      · have hrec := ih _ h
        simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, not_or] at hbad
        have hst1 : st.1 = true := by cases h1 : st.1; simp [h1] at hbad; rfl
        have hlen1 : aw.1.length = b.r := by by_contra hc; exact hbad.1.2 hc
        have hlen2 : aw.2.length = st.2 + 1 := by by_contra hc; exact hbad.2 hc
        have hdd0 : ((aw.1.zip b.W).foldl (fun (st2 : Int × Int × Nat) (awj : Int × List Int) =>
            let j := st2.2.2
            let eij := s2 * awj.1 - dotInt aw.2 awj.2
            if j == st.2 then (eij, st2.2.1, j + 1)
            else (st2.1, st2.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)).1 ≥
            ((aw.1.zip b.W).foldl (fun (st2 : Int × Int × Nat) (awj : Int × List Int) =>
            let j := st2.2.2
            let eij := s2 * awj.1 - dotInt aw.2 awj.2
            if j == st.2 then (eij, st2.2.1, j + 1)
            else (st2.1, st2.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)).2.1 := by
          simpa [ge_iff_le] using hrec.1
        refine ⟨hst1, fun k hk => ?_⟩
        cases k with
        | zero => exact ⟨hlen1, hlen2, hdd0⟩
        | succ k' =>
          have hsub := hrec.2 k' (by simp at hk; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hsub
  have ⟨hlenOk, hrowOk⟩ := hfold_inv (b.A.zip b.W) _ hrows
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlenOk
  obtain ⟨⟨⟨⟨hSpos, hAlen⟩, hWlen⟩, _⟩, _⟩ := hlenOk
  have hAWlen : (b.A.zip b.W).length = b.r := by simp [hAlen, hWlen]
  -- Extract symmetry `matGet b.A i j = matGet b.A j i`!
  have hAsym : ∀ i j : Fin b.r, matGet b.A i.val j.val = matGet b.A j.val i.val := by
    intro i j
    simp only [List.all_eq_true, beq_iff_eq] at hsym
    have hiA : i.val < b.A.length := by omega
    have hjA : j.val < b.A.length := by omega
    have hrowi_len : (b.A[i.val]'hiA).length = b.r := by
      have := (hrowOk i.val (by omega)).1; simpa using this
    have hmem_i : (b.A[i.val]'hiA, i.val) ∈ b.A.zip (List.range b.r) := by
      rw [List.mem_iff_getElem]; exact ⟨i.val, by simp [hAlen], by simp⟩
    have hmem_j : ((b.A[i.val]'hiA)[j.val]'(by omega), b.A[j.val]'hjA) ∈ (b.A[i.val]'hiA).zip b.A := by
      rw [List.mem_iff_getElem]; exact ⟨j.val, by simp [hrowi_len, hAlen], by simp⟩
    have heq := hsym _ hmem_i _ hmem_j
    simp only [matGet, List.getD, List.getElem?_eq_getElem hiA, List.getElem?_eq_getElem hjA,
      List.getElem?_eq_getElem (by omega : j.val < (b.A[i.val]'hiA).length), Option.getD_some]
    exact heq
  -- Define `E i j = s2 * A[i][j] - dotInt W[i] W[j]`!
  let E : Fin b.r → Fin b.r → ℤ := fun i j =>
    s2 * matGet b.A i.val j.val - dotInt (b.W.getD i.val []) (b.W.getD j.val [])
  have hEsym : ∀ i j : Fin b.r, E i j = E j i := fun i j => by
    have hdot_comm : ∀ xs ys : List Int, dotInt xs ys = dotInt ys xs := fun xs ys => by
      induction xs generalizing ys with
      | nil => cases ys <;> rfl
      | cons x xr ih => cases ys with | nil => rfl | cons y yr => simp [dotInt, mul_comm, ih]
    simp only [E, hAsym i j, hdot_comm]
  -- Extract `E i i ≥ ∑ j ≠ i, |E i j|` from the inner foldl!
  have hEdd : ∀ i : Fin b.r, ∑ j ∈ Finset.univ.erase i, (Int.natAbs (E i j) : ℤ) ≤ E i i := by
    intro i
    have hri := hrowOk i.val (by omega)
    have hiA : i.val < b.A.length := by omega
    have hiW : i.val < b.W.length := by omega
    have hzip_i : (b.A.zip b.W)[i.val]'(by omega) = (b.A[i.val]'hiA, b.W[i.val]'hiW) := by simp
    have hdd_raw := hri.2.2
    rw [hzip_i] at hdd_raw
    -- Track the inner foldl accumulator across `l = aRow.zip b.W`!
    have hinner : ∀ (l : List (Int × List Int)) (st : Int × Int × Nat),
        let res := l.foldl (fun (st : Int × Int × Nat) (awj : Int × List Int) =>
          let j := st.2.2
          let eij := s2 * awj.1 - dotInt (b.W[i.val]'hiW) awj.2
          if j == i.val then (eij, st.2.1, j + 1)
          else (st.1, st.2.1 + Int.natAbs eij, j + 1)) st
        res.2.2 = st.2.2 + l.length ∧
        (∀ k, k < l.length → st.2.2 + k = i.val →
          res.1 = s2 * (l.getD k (0, [])).1 - dotInt (b.W[i.val]'hiW) (l.getD k (0, [])).2) ∧
        res.2.1 = st.2.1 + ((List.range l.length).map fun k =>
          if st.2.2 + k = i.val then (0 : ℤ)
          else (Int.natAbs (s2 * (l.getD k (0, [])).1 - dotInt (b.W[i.val]'hiW) (l.getD k (0, [])).2) : ℤ)).sum := by
      intro l; induction l with
      | nil => intro st; exact ⟨by simp, fun _ hk => by simp at hk, by simp⟩
      | cons awj rest ih =>
        rintro ⟨s1, s2a, s3⟩
        simp only [List.foldl_cons]
        set e0 := s2 * awj.1 - dotInt (b.W[i.val]'hiW) awj.2
        have hrange : ∀ m (f : Nat → ℤ),
            ((List.range (m + 1)).map f).sum = f 0 + ((List.range m).map fun k => f (k + 1)).sum := by
          intro m f; induction m with
          | zero => simp
          | succ k ihk =>
            rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                ihk, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                add_assoc]
        split_ifs with heq
        · have hi_eq : s3 = i.val := by simpa using heq
          have hrec := ih (e0, s2a, s3 + 1)
          dsimp only at hrec
          refine ⟨by rw [hrec.1]; simp; omega, fun k hk hki => ?_, ?_⟩
          · cases k with
            | zero =>
              have hkeep : ∀ (l' : List (Int × List Int)) (st' : Int × Int × Nat),
                  i.val < st'.2.2 →
                  (l'.foldl (fun (st : Int × Int × Nat) (awj : Int × List Int) =>
                    let j := st.2.2
                    let eij := s2 * awj.1 - dotInt (b.W[i.val]'hiW) awj.2
                    if j == i.val then (eij, st.2.1, j + 1)
                    else (st.1, st.2.1 + Int.natAbs eij, j + 1)) st').1 = st'.1 := by
                intro l'; induction l' with
                | nil => intro _ _; rfl
                | cons _ _ ih' =>
                  rintro ⟨a1, a2, a3⟩ hlt; simp only [List.foldl_cons]
                  dsimp only at hlt
                  have hne : (a3 == i.val) = false := by simp; omega
                  simp only [hne, Bool.false_eq_true, ↓reduceIte]
                  exact ih' (a1, a2 + _, a3 + 1) (by dsimp only; omega)
              exact hkeep rest (e0, s2a, s3 + 1) (by dsimp only; omega)
            | succ k' => omega
          · rw [hrec.2.2, List.length_cons, hrange]
            simp only [add_zero, hi_eq, ↓reduceIte, zero_add, List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1]
        · have hi_ne : s3 ≠ i.val := by simpa using heq
          have hrec := ih (s1, s2a + Int.natAbs e0, s3 + 1)
          dsimp only at hrec
          refine ⟨by rw [hrec.1]; simp; omega, fun k hk hki => ?_, ?_⟩
          · cases k with
            | zero => omega
            | succ k' =>
              have := hrec.2.1 k' (by simp at hk; omega) (by omega)
              simpa [List.getD_cons_succ] using this
          · rw [hrec.2.2, List.length_cons, hrange]
            simp only [add_zero, hi_ne, ↓reduceIte, List.getD_cons_zero]
            have htail_eq : ((List.range rest.length).map fun k =>
                  if s3 + 1 + k = i.val then (0 : ℤ)
                  else (Int.natAbs (s2 * (rest.getD k (0, [])).1 - dotInt (b.W[i.val]'hiW) (rest.getD k (0, [])).2) : ℤ)) =
                ((List.range rest.length).map fun k =>
                  if s3 + (k + 1) = i.val then (0 : ℤ)
                  else (Int.natAbs (s2 * ((awj :: rest).getD (k + 1) (0, [])).1 -
                    dotInt (b.W[i.val]'hiW) ((awj :: rest).getD (k + 1) (0, [])).2) : ℤ)) :=
              List.map_congr_left fun k _ => by
                simp only [List.getD_cons_succ, show s3 + 1 + k = s3 + (k + 1) by omega]
            rw [htail_eq, add_assoc]
    have hli : ((b.A[i.val]'hiA).zip b.W).length = b.r := by
      have hlen_a : (b.A[i.val]'hiA).length = b.r := by simpa [hzip_i] using hri.1
      simp [hlen_a, hWlen]
    have hin := hinner ((b.A[i.val]'hiA).zip b.W) (0, 0, 0)
    have h1 := hin.2.1 i.val (by omega) (by simp)
    have h2 := hin.2.2
    have hE_entry : ∀ j : Fin b.r,
        s2 * (((b.A[i.val]'hiA).zip b.W).getD j.val (0, [])).1 -
          dotInt (b.W[i.val]'hiW) (((b.A[i.val]'hiA).zip b.W).getD j.val (0, [])).2 = E i j := fun j => by
      have hlen_a : (b.A[i.val]'hiA).length = b.r := by simpa [hzip_i] using hri.1
      have hj_zip : j.val < ((b.A[i.val]'hiA).zip b.W).length := by omega
      simp only [E, matGet, List.getD, List.getElem?_eq_getElem hiA, List.getElem?_eq_getElem hiW,
        List.getElem?_eq_getElem hj_zip, List.getElem_zip,
        List.getElem?_eq_getElem (by omega : j.val < (b.A[i.val]'hiA).length),
        List.getElem?_eq_getElem (by omega : j.val < b.W.length), Option.getD_some]
    rw [hE_entry i] at h1
    have hsum_eq : (((List.range ((b.A[i.val]'hiA).zip b.W).length).map fun k =>
        if 0 + k = i.val then (0 : ℤ)
        else (Int.natAbs (s2 * (((b.A[i.val]'hiA).zip b.W).getD k (0, [])).1 -
          dotInt (b.W[i.val]'hiW) (((b.A[i.val]'hiA).zip b.W).getD k (0, [])).2) : ℤ)).sum) =
        ∑ j ∈ Finset.univ.erase i, (Int.natAbs (E i j) : ℤ) := by
      rw [hli]
      have hsum_fin : ∀ (n : Nat) (f : Nat → ℤ), ((List.range n).map f).sum = ∑ j : Fin n, f j.val := fun n f => by
        induction n with
        | zero => simp
        | succ m ihm =>
          rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
              ihm, Fin.sum_univ_castSucc]; rfl
      rw [hsum_fin, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [zero_add, ↓reduceIte]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j.val ≠ i.val := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
      simp only [hji, ↓reduceIte, hE_entry j]
    rw [hsum_eq, zero_add] at h2
    simp only [zero_add] at hdd_raw
    rw [h1, h2] at hdd_raw
    exact hdd_raw
  -- Now prove `0 ≤ s2 * Re(y† A y) = ∑_k |∑_i W_{ik} y_i|² + Re(y† E y)`!
  have hs2_decomp : ((s2 : ℤ) : ℂ) * (∑ p : Fin b.r, ∑ q : Fin b.r, (matGet b.A p.val q.val : ℂ) * star (y p) * y q) =
      (∑ k : Fin b.r, ((Complex.normSq (∑ p : Fin b.r, ((b.W.getD p.val []).getD k.val 0 : ℂ) * y p) : ℝ) : ℂ)) +
      (∑ p : Fin b.r, ∑ q : Fin b.r, (E p q : ℂ) * star (y p) * y q) := by
    have hW_expand : ∀ k : Fin b.r,
        ((Complex.normSq (∑ p : Fin b.r, ((b.W.getD p.val []).getD k.val 0 : ℂ) * y p) : ℝ) : ℂ) =
        ∑ p : Fin b.r, ∑ q : Fin b.r,
          ((b.W.getD p.val []).getD k.val 0 : ℂ) * ((b.W.getD q.val []).getD k.val 0 : ℂ) * star (y p) * y q := by
      intro k
      rw [← Complex.mul_conj, ← Complex.star_def, mul_comm, star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [star_mul', Complex.star_def, map_intCast]; ring
    simp_rw [hW_expand]
    conv_rhs => rw [Finset.sum_comm]
    have hswap : (∑ p : Fin b.r, ∑ k : Fin b.r, ∑ q : Fin b.r,
        ((b.W.getD p.val []).getD k.val 0 : ℂ) * ((b.W.getD q.val []).getD k.val 0 : ℂ) * star (y p) * y q) =
      ∑ p : Fin b.r, ∑ q : Fin b.r,
        ((dotInt (b.W.getD p.val []) (b.W.getD q.val []) : ℤ) : ℂ) * star (y p) * y q := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hpW : (b.W.getD p.val []).length ≤ b.r := by
        have hpLt : p.val < b.r := p.isLt
        have hlen := (hrowOk p.val (by omega)).2.1
        have hp' : p.val < b.W.length := by omega
        simp only [List.getD, List.getElem?_eq_getElem hp', Option.getD_some]
        have : (b.A.zip b.W)[p.val]'(by omega) = (b.A[p.val]'(by omega), b.W[p.val]'hp') := by simp
        rw [this] at hlen; dsimp only at hlen; omega
      have hqW : (b.W.getD q.val []).length ≤ b.r := by
        have hqLt : q.val < b.r := q.isLt
        have hlen := (hrowOk q.val (by omega)).2.1
        have hq' : q.val < b.W.length := by omega
        simp only [List.getD, List.getElem?_eq_getElem hq', Option.getD_some]
        have : (b.A.zip b.W)[q.val]'(by omega) = (b.A[q.val]'(by omega), b.W[q.val]'hq') := by simp
        rw [this] at hlen; dsimp only at hlen; omega
      rw [dotInt_eq_sum _ _ b.r hpW hqW, Int.cast_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by push_cast; ring
    rw [hswap, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [E, Int.cast_sub, Int.cast_mul]; ring
  -- Bound `Re(y† E y) ≥ 0` by diagonal dominance!
  have hE_nn : 0 ≤ (∑ p : Fin b.r, ∑ q : Fin b.r, (E p q : ℂ) * star (y p) * y q).re := by
    have hre_term : ∀ p q : Fin b.r,
        ((E p q : ℂ) * star (y p) * y q).re = (E p q : ℝ) * (star (y p) * y q).re := fun p q => by
      rw [mul_assoc, Complex.mul_re]
      simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum, hre_term]
    have hsplit : (∑ p : Fin b.r, ∑ q : Fin b.r, (E p q : ℝ) * (star (y p) * y q).re) =
        (∑ p : Fin b.r, (E p p : ℝ) * Complex.normSq (y p)) +
        (∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p, (E p q : ℝ) * (star (y p) * y q).re) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ p)]
      congr 1; rw [mul_comm (star (y p)), Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    have hoff : ∀ p q : Fin b.r,
        -((Int.natAbs (E p q) : ℝ) / 2 * (Complex.normSq (y p) + Complex.normSq (y q))) ≤
        (E p q : ℝ) * (star (y p) * y q).re := fun p q => by
      have hplus : 0 ≤ Complex.normSq (y p + y q) := Complex.normSq_nonneg _
      have hminus : 0 ≤ Complex.normSq (y p - y q) := Complex.normSq_nonneg _
      have h1 : Complex.normSq (y p + y q) =
          Complex.normSq (y p) + Complex.normSq (y q) + 2 * (star (y p) * y q).re := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
      have h2 : Complex.normSq (y p - y q) =
          Complex.normSq (y p) + Complex.normSq (y q) - 2 * (star (y p) * y q).re := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im]; ring
      have habs : |(star (y p) * y q).re| ≤ (Complex.normSq (y p) + Complex.normSq (y q)) / 2 := by
        rw [abs_le]; constructor <;> linarith
      have hEabs : |(E p q : ℝ)| = (Int.natAbs (E p q) : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
      have hprod : -((Int.natAbs (E p q) : ℝ) * |(star (y p) * y q).re|) ≤ (E p q : ℝ) * (star (y p) * y q).re := by
        have := neg_abs_le ((E p q : ℝ) * (star (y p) * y q).re)
        rwa [abs_mul, hEabs] at this
      have hnnE : 0 ≤ (Int.natAbs (E p q) : ℝ) := Nat.cast_nonneg _
      have hle := mul_le_mul_of_nonneg_left habs hnnE
      linarith
    have hoff_sum : -(∑ p : Fin b.r, (∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) * Complex.normSq (y p)) ≤
        ∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p, (E p q : ℝ) * (star (y p) * y q).re := by
      have hge1 := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) =>
        Finset.sum_le_sum fun q (_ : q ∈ Finset.univ.erase p) => hoff p q
      -- Simplify the LHS using `E p q = E q p`!
      have hsym_sum : (∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p,
            -((Int.natAbs (E p q) : ℝ) / 2 * (Complex.normSq (y p) + Complex.normSq (y q)))) =
          -(∑ p : Fin b.r, (∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) * Complex.normSq (y p)) := by
        have hswap2 : (∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ) * Complex.normSq (y q)) =
            ∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ) * Complex.normSq (y p) := by
          have hrewrite : ∀ f : Fin b.r → Fin b.r → ℝ,
              (∑ p : Fin b.r, ∑ q ∈ Finset.univ.erase p, f p q) =
              ∑ p : Fin b.r, ∑ q : Fin b.r, if q ≠ p then f p q else 0 := fun f =>
            Finset.sum_congr rfl fun p _ => by
              rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ p)]
              simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
              exact Finset.sum_congr rfl fun q hq => by simp [(Finset.mem_erase.mp hq).1]
          rw [hrewrite, hrewrite, Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p = q
          · subst h; simp
          · simp [h, Ne.symm h, hEsym p q]
        have hexp : ∀ p : Fin b.r, ∀ q : Fin b.r,
            -((Int.natAbs (E p q) : ℝ) / 2 * (Complex.normSq (y p) + Complex.normSq (y q))) =
            -(1 / 2 : ℝ) * ((Int.natAbs (E p q) : ℝ) * Complex.normSq (y p)) -
            (1 / 2 : ℝ) * ((Int.natAbs (E p q) : ℝ) * Complex.normSq (y q)) := fun p q => by ring
        simp_rw [hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, hswap2]
        simp_rw [← Finset.sum_mul]; ring
      rw [hsym_sum] at hge1; exact hge1
    rw [hsplit]
    have hdiag_ge : 0 ≤ ∑ p : Fin b.r,
        ((E p p : ℝ) - ∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) * Complex.normSq (y p) := by
      refine Finset.sum_nonneg fun p _ => mul_nonneg ?_ (Complex.normSq_nonneg _)
      have hddR : (∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) ≤ (E p p : ℝ) := by
        have := Int.cast_le (R := ℝ).mpr (hEdd p)
        simpa using this
      linarith
    have hrew : (∑ p : Fin b.r, ((E p p : ℝ) - ∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) * Complex.normSq (y p)) =
        (∑ p : Fin b.r, (E p p : ℝ) * Complex.normSq (y p)) -
        (∑ p : Fin b.r, (∑ q ∈ Finset.univ.erase p, (Int.natAbs (E p q) : ℝ)) * Complex.normSq (y p)) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun p _ => by ring
    linarith
  have hW_nn : 0 ≤ (∑ k : Fin b.r, ((Complex.normSq (∑ p : Fin b.r,
      ((b.W.getD p.val []).getD k.val 0 : ℂ) * y p) : ℝ) : ℂ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _
  have hprod_re : (s2 : ℝ) * (∑ p : Fin b.r, ∑ q : Fin b.r,
      (matGet b.A p.val q.val : ℂ) * star (y p) * y q).re =
      (((s2 : ℤ) : ℂ) * (∑ p : Fin b.r, ∑ q : Fin b.r,
        (matGet b.A p.val q.val : ℂ) * star (y p) * y q)).re := by
    rw [Complex.mul_re]; simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  have hs2_pos : (0 : ℝ) < (s2 : ℝ) := by
    have : (0 : ℤ) < s2 := mul_pos hSpos hSpos
    exact_mod_cast this
  have htot_nn : 0 ≤ (s2 : ℝ) * (∑ p : Fin b.r, ∑ q : Fin b.r,
      (matGet b.A p.val q.val : ℂ) * star (y p) * y q).re := by
    rw [hprod_re, hs2_decomp, Complex.add_re]; linarith
  nlinarith

/-- Evaluate `buildBlockPhiTrie b` as an explicit Hermitian form `y(z)† A y(z)`! -/
private lemma buildBlockPhiTrie_props (b : OrbitBlockCert) (hvalid : checkSymAndDD b = true)
    (z : Fin 4 → ℂ) :
    DepthTrie 8 (buildBlockPhiTrie b) ∧
    RowBound 165 1 0 (buildBlockPhiTrie b) ∧
    ColPred (· < 165) (buildBlockPhiTrie b) ∧
    0 ≤ (evalTrie (mon8 · z) (buildBlockPhiTrie b)).re := by
  have hvalid' := hvalid
  unfold checkSymAndDD at hvalid'
  simp only [Bool.and_eq_true] at hvalid'
  obtain ⟨⟨⟨hrows, _⟩, hqOk⟩, hblkOk⟩ := hvalid'
  -- Extract `b.A.length = b.r`, `b.Qcols.length = b.m`, `b.blk.length = b.m`!
  have hlenOk : b.S > 0 ∧ b.A.length = b.r ∧ b.W.length = b.r ∧ b.Qcols.length = b.m ∧ b.blk.length = b.m := by
    have hstep : ∀ (l : List (List Int × List Int)) (st : Bool × Nat),
        (l.foldl (fun (acc : Bool × Nat) (aw : List Int × List Int) =>
          let i := acc.2
          if !acc.1 || aw.1.length != b.r || aw.2.length != i + 1 then (false, i + 1)
          else
            let res := (aw.1.zip b.W).foldl (fun (st : Int × Int × Nat) (awj : Int × List Int) =>
              let j := st.2.2
              let eij := (b.S * b.S) * awj.1 - dotInt aw.2 awj.2
              if j == i then (eij, st.2.1, j + 1)
              else (st.1, st.2.1 + Int.natAbs eij, j + 1)) (0, 0, 0)
            (res.1 >= res.2.1, i + 1)) st).1 = true → st.1 = true := by
      intro l; induction l with
      | nil => intro _ h; exact h
      | cons _ rest ih =>
        intro st h; simp only [List.foldl_cons] at h
        split_ifs at h with hbad
        · have := ih _ h; simp at this
        · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hbad
          cases h1 : st.1; simp [h1] at hbad; rfl
    have hl := hstep _ _ hrows
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
    exact ⟨hl.1.1.1.1, hl.1.1.1.2, hl.1.1.2, hl.1.2, hl.2⟩
  obtain ⟨_, hAlen, _, hQlen, hBlen⟩ := hlenOk
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hqOk hblkOk
  -- Define `u_i(z) = star (mon4 a_i z) * mon4 ap_i z` and `y_p(z) = ∑_i Q_{p,i} u_i(z)`!
  let uVal : Nat × Nat → ℂ := fun aap => star (mon4 aap.1 z) * mon4 aap.2 z
  let qCoeff (qCol : List (Nat × Int)) (p : Nat) : ℤ :=
    (qCol.map fun (p', v) => if p' = p then v else 0).sum
  let y : Fin b.r → ℂ := fun p =>
    ((b.blk.zip b.Qcols).map fun (aap, qCol) => (qCoeff qCol p.val : ℂ) * uVal aap).sum
  -- Show `dotSparseCol qColI (mulASparseCol b.A qColJ) = ∑ p q : Fin b.r, qCoeff qColI p * matGet b.A p q * qCoeff qColJ q`!
  have hqCol_sum : ∀ (qCol : List (Nat × Int)) (f : Nat → ℤ),
      (∀ pv ∈ qCol, pv.1 < b.r) →
      qCol.foldl (fun s (p, v) => s + v * f p) 0 = ∑ p : Fin b.r, qCoeff qCol p.val * f p.val := by
    intro qCol f hlt
    have hfold : ∀ (init : ℤ) (l : List (Nat × Int)), (∀ pv ∈ l, pv.1 < b.r) →
        l.foldl (fun s (p, v) => s + v * f p) init =
          init + ∑ p : Fin b.r, ((l.map fun (p', v) => if p' = p.val then v else 0).sum) * f p.val := by
      intro init l; induction l generalizing init with
      | nil => intro _; simp
      | cons pv rest ih =>
        rcases pv with ⟨p0, v0⟩
        intro hlt'
        have hp0 : p0 < b.r := hlt' (p0, v0) (by simp)
        simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih (init + v0 * f p0) (fun x hx => hlt' x (by simp [hx]))]
        have hadd : (∑ p : Fin b.r, ((if p0 = p.val then v0 else 0) +
              (rest.map fun (p', v) => if p' = p.val then v else 0).sum) * f p.val) =
            v0 * f p0 + ∑ p : Fin b.r, (rest.map fun (p', v) => if p' = p.val then v else 0).sum * f p.val := by
          simp_rw [add_mul, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single (⟨p0, hp0⟩ : Fin b.r)]
          · simp
          · intro p _ hne; have : p0 ≠ p.val := fun h => hne (Fin.ext h.symm); simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hadd]; ring
    simpa [qCoeff] using hfold 0 qCol hlt
  have hmulA : ∀ (qCol : List (Nat × Int)) (p : Fin b.r),
      (∀ qv ∈ qCol, qv.1 < b.r) →
      (mulASparseCol b.A qCol).getD p.val 0 = ∑ q : Fin b.r, matGet b.A p.val q.val * qCoeff qCol q.val := by
    intro qCol p hlt
    unfold mulASparseCol
    have hpA : p.val < b.A.length := by omega
    simp only [List.getD, List.getElem?_map, List.getElem?_eq_getElem hpA, Option.map_some, Option.getD_some]
    have hcomm : qCol.foldl (fun s (q, v) => s + (b.A[p.val]'hpA).getD q 0 * v) 0 =
        qCol.foldl (fun s (q, v) => s + v * (b.A[p.val]'hpA).getD q 0) 0 := by
      congr 1; funext s qv; ring
    change qCol.foldl (fun s (q, v) => s + (b.A[p.val]'hpA).getD q 0 * v) 0 = _
    rw [hcomm, hqCol_sum qCol (fun q => (b.A[p.val]'hpA).getD q 0) hlt]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [matGet, List.getD, List.getElem?_eq_getElem hpA, Option.getD_some]; ring
  have hdot : ∀ (qColI qColJ : List (Nat × Int)),
      (∀ pv ∈ qColI, pv.1 < b.r) → (∀ qv ∈ qColJ, qv.1 < b.r) →
      dotSparseCol qColI (mulASparseCol b.A qColJ) =
        ∑ p : Fin b.r, ∑ q : Fin b.r, qCoeff qColI p.val * matGet b.A p.val q.val * qCoeff qColJ q.val := by
    intro qColI qColJ hI hJ
    unfold dotSparseCol
    rw [hqCol_sum qColI (fun p => (mulASparseCol b.A qColJ).getD p 0) hI]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hmulA qColJ p hJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  -- Now prove properties of `buildBlockPhiTrie b`!
  let blkTups := b.blk.map fun (a, ap) => (sym4List.getD a (0,0,0,0), sym4List.getD ap (0,0,0,0))
  let Tcols := b.Qcols.map (mulASparseCol b.A)
  let jData := blkTups.zip Tcols
  let iData := blkTups.zip b.Qcols
  have hjData_eq : jData = (b.blk.zip b.Qcols).map fun (aap, qCol) =>
      ((sym4List.getD aap.1 (0,0,0,0), sym4List.getD aap.2 (0,0,0,0)), mulASparseCol b.A qCol) := by
    apply List.ext_getElem
    · simp [jData, blkTups, Tcols, hBlen, hQlen]
    · intro i hi1 hi2; simp [jData, blkTups, Tcols]
  have hiData_eq : iData = (b.blk.zip b.Qcols).map fun (aap, qCol) =>
      ((sym4List.getD aap.1 (0,0,0,0), sym4List.getD aap.2 (0,0,0,0)), qCol) := by
    apply List.ext_getElem
    · simp [iData, blkTups, hBlen, hQlen]
    · intro i hi1 hi2; simp [iData, blkTups]
  have hinner_j : ∀ (aapI : Nat × Nat) (qColI : List (Nat × Int)),
      aapI.1 < 35 → aapI.2 < 35 → (∀ pv ∈ qColI, pv.1 < b.r) →
      let cai := sym4List.getD aapI.1 (0,0,0,0)
      let capi := sym4List.getD aapI.2 (0,0,0,0)
      let t := jData.foldl (fun t ((cc1, cc2), tColJ) =>
        let v := dotSparseCol qColI tColJ
        if v == 0 then t
        else trieAdd 8 (sym8Idx (addTup4 capi cc1)) (sym8Idx (addTup4 cai cc2)) v t) RowTrie.empty
      DepthTrie 8 t ∧ RowBound 165 1 0 t ∧ ColPred (· < 165) t ∧
      evalTrie (mon8 · z) t =
        ((b.blk.zip b.Qcols).map fun (aapJ, qColJ) =>
          (∑ p : Fin b.r, ∑ q : Fin b.r,
            (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
          star (uVal aapI) * uVal aapJ).sum := by
    intro aapI qColI haI hapI hqI
    have hfold : ∀ (l : List ((Nat × Nat) × List (Nat × Int))),
        (∀ x ∈ l, x.1.1 < 35 ∧ x.1.2 < 35 ∧ ∀ qv ∈ x.2, qv.1 < b.r) →
        ∀ t : RowTrie, DepthTrie 8 t → RowBound 165 1 0 t → ColPred (· < 165) t →
        let t' := (l.map fun (aapJ, qColJ) =>
            ((sym4List.getD aapJ.1 (0,0,0,0), sym4List.getD aapJ.2 (0,0,0,0)), mulASparseCol b.A qColJ)).foldl
          (fun t ((cc1, cc2), tColJ) =>
            let v := dotSparseCol qColI tColJ
            if v == 0 then t
            else trieAdd 8 (sym8Idx (addTup4 (sym4List.getD aapI.2 (0,0,0,0)) cc1))
              (sym8Idx (addTup4 (sym4List.getD aapI.1 (0,0,0,0)) cc2)) v t) t
        DepthTrie 8 t' ∧ RowBound 165 1 0 t' ∧ ColPred (· < 165) t' ∧
        evalTrie (mon8 · z) t' = evalTrie (mon8 · z) t +
          (l.map fun (aapJ, qColJ) =>
            (∑ p : Fin b.r, ∑ q : Fin b.r,
              (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
            star (uVal aapI) * uVal aapJ).sum := by
      intro l hl
      induction l with
      | nil => intro t hd hb hc; exact ⟨hd, hb, hc, by simp⟩
      | cons x rest ih =>
        rcases x with ⟨aapJ, qColJ⟩
        intro t hd hb hc
        have ⟨haJ, hapJ, hqJ⟩ := hl (aapJ, qColJ) (by simp)
        have hdot_eq := hdot qColI qColJ hqI hqJ
        have hdotC : ((dotSparseCol qColI (mulASparseCol b.A qColJ) : ℤ) : ℂ) =
            ∑ p : Fin b.r, ∑ q : Fin b.r,
              (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ) := by
          rw [hdot_eq]; push_cast; rfl
        have hi := add4To8_props hapI haJ
        have hj := add4To8_props haI hapJ
        simp only [List.map_cons, List.foldl_cons]
        split_ifs with hv0
        · have hv : dotSparseCol qColI (mulASparseCol b.A qColJ) = 0 := by simpa using hv0
          have hrec := ih (fun y hy => hl y (by simp [hy])) t hd hb hc
          refine ⟨hrec.1, hrec.2.1, hrec.2.2.1, ?_⟩
          rw [hrec.2.2.2, List.sum_cons, ← hdotC, hv, Int.cast_zero, zero_mul, zero_mul, zero_add]
        · let ii := sym8Idx (addTup4 (sym4List.getD aapI.2 (0,0,0,0)) (sym4List.getD aapJ.1 (0,0,0,0)))
          let jj := sym8Idx (addTup4 (sym4List.getD aapI.1 (0,0,0,0)) (sym4List.getD aapJ.2 (0,0,0,0)))
          let vv := dotSparseCol qColI (mulASparseCol b.A qColJ)
          have hii : ii < 165 := hi.1
          have hjj : jj < 165 := hj.1
          have hd1 := depthTrie_trieAdd 8 ii jj vv hd
          have hb1 := rowBound_trieAdd 8 1 0 ii jj vv (by omega) hd hb
          have hc1 := colPred_trieAdd (P := (· < 165)) 8 ii jj hjj vv hd hc
          have he1 := evalTrieAux_trieAdd (mon8 · z) (mon8 · z) 8 1 0 ii jj vv (by omega) hd
          have hrec := ih (fun y hy => hl y (by simp [hy])) _ hd1 hb1 hc1
          refine ⟨hrec.1, hrec.2.1, hrec.2.2.1, ?_⟩
          rw [hrec.2.2.2, List.sum_cons]
          have hm1 : mon8 ii z = monTup (sym4List.getD aapI.2 (0,0,0,0)) z * monTup (sym4List.getD aapJ.1 (0,0,0,0)) z := by
            simp only [ii, mon8, hi.2, monTup_add]
          have hm2 : mon8 jj z = monTup (sym4List.getD aapI.1 (0,0,0,0)) z * monTup (sym4List.getD aapJ.2 (0,0,0,0)) z := by
            simp only [jj, mon8, hj.2, monTup_add]
          change evalTrieAux (mon8 · z) (mon8 · z) 1 0 _ + _ = evalTrieAux (mon8 · z) (mon8 · z) 1 0 t + _
          rw [he1]
          simp only [zero_add, one_mul, hm1, hm2, star_mul']
          have hu_eq : star (monTup (sym4List.getD aapJ.1 (0,0,0,0)) z) *
              star (monTup (sym4List.getD aapI.2 (0,0,0,0)) z) *
              (monTup (sym4List.getD aapI.1 (0,0,0,0)) z * monTup (sym4List.getD aapJ.2 (0,0,0,0)) z) =
              star (uVal aapI) * uVal aapJ := by
            simp only [uVal, mon4, star_mul', star_star]; ring
          dsimp only [vv]
          rw [hdotC]
          linear_combination ((∑ p : Fin b.r, ∑ q : Fin b.r,
            (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ))) * hu_eq
    have hzip_ok : ∀ x ∈ b.blk.zip b.Qcols, x.1.1 < 35 ∧ x.1.2 < 35 ∧ ∀ qv ∈ x.2, qv.1 < b.r := by
      intro x hx
      have h1 := hblkOk x.1 (List.of_mem_zip hx).1
      have h2 := hqOk x.2 (List.of_mem_zip hx).2
      exact ⟨h1.1, h1.2, h2⟩
    dsimp only; rw [hjData_eq]
    have h0 := hfold (b.blk.zip b.Qcols) hzip_ok RowTrie.empty DepthTrie.empty RowBound.empty ColPred.empty
    exact ⟨h0.1, h0.2.1, h0.2.2.1, by simpa [evalTrie, evalTrieAux] using h0.2.2.2⟩
  -- Merge across `iData`!
  let iTries := iData.map fun ((cai, capi), qColI) =>
    jData.foldl (fun t ((cc1, cc2), tColJ) =>
      let v := dotSparseCol qColI tColJ
      if v == 0 then t
      else trieAdd 8 (sym8Idx (addTup4 capi cc1)) (sym8Idx (addTup4 cai cc2)) v t) RowTrie.empty
  have hiTries_eq : iTries = (b.blk.zip b.Qcols).map fun (aapI, qColI) =>
      jData.foldl (fun t ((cc1, cc2), tColJ) =>
        let v := dotSparseCol qColI tColJ
        if v == 0 then t
        else trieAdd 8 (sym8Idx (addTup4 (sym4List.getD aapI.2 (0,0,0,0)) cc1))
          (sym8Idx (addTup4 (sym4List.getD aapI.1 (0,0,0,0)) cc2)) v t) RowTrie.empty := by
    simp only [iTries, hiData_eq, List.map_map]; rfl
  have hiTries_ok : ∀ t ∈ iTries, DepthTrie 8 t ∧ RowBound 165 1 0 t ∧ ColPred (· < 165) t := by
    rw [hiTries_eq]; intro t ht; simp only [List.mem_map] at ht
    rcases ht with ⟨⟨aapI, qColI⟩, hx, rfl⟩
    have h1 := hblkOk aapI (List.of_mem_zip hx).1
    have h2 := hqOk qColI (List.of_mem_zip hx).2
    have hi := hinner_j aapI qColI h1.1 h1.2 h2
    exact ⟨hi.1, hi.2.1, hi.2.2.1⟩
  have hm := trieMergeAll_props 7 iTries (fun t ht => (hiTries_ok t ht).1)
  refine ⟨hm.1,
          trieMergeAll_rowBound 7 iTries (fun t ht => (hiTries_ok t ht).1) (fun t ht => (hiTries_ok t ht).2.1),
          trieMergeAll_colPred 7 iTries (fun t ht => (hiTries_ok t ht).1) (fun t ht => (hiTries_ok t ht).2.2), ?_⟩
  -- Show `evalTrie (mon8 · z) (buildBlockPhiTrie b) = ∑ p q : Fin b.r, A[p][q] * star (y p) * y q`!
  have heval : evalTrie (mon8 · z) (buildBlockPhiTrie b) =
      ∑ p : Fin b.r, ∑ q : Fin b.r, (matGet b.A p.val q.val : ℂ) * star (y p) * y q := by
    change evalTrieAux (mon8 · z) (mon8 · z) 1 0 (trieMergeAll 7 iTries) = _
    rw [hm.2, hiTries_eq, List.map_map]
    have hmap_eq : ((b.blk.zip b.Qcols).map fun x =>
          evalTrie (mon8 · z) (jData.foldl (fun t ((cc1, cc2), tColJ) =>
            let v := dotSparseCol x.2 tColJ
            if v == 0 then t
            else trieAdd 8 (sym8Idx (addTup4 (sym4List.getD x.1.2 (0,0,0,0)) cc1))
              (sym8Idx (addTup4 (sym4List.getD x.1.1 (0,0,0,0)) cc2)) v t) RowTrie.empty)) =
        ((b.blk.zip b.Qcols).map fun (aapI, qColI) =>
          ((b.blk.zip b.Qcols).map fun (aapJ, qColJ) =>
            (∑ p : Fin b.r, ∑ q : Fin b.r,
              (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
            star (uVal aapI) * uVal aapJ).sum) := by
      refine List.map_congr_left fun x hx => ?_
      have h1 := hblkOk x.1 (List.of_mem_zip hx).1
      have h2 := hqOk x.2 (List.of_mem_zip hx).2
      exact (hinner_j x.1 x.2 h1.1 h1.2 h2).2.2.2
    change ((b.blk.zip b.Qcols).map fun x =>
          evalTrie (mon8 · z) (jData.foldl (fun t ((cc1, cc2), tColJ) =>
            let v := dotSparseCol x.2 tColJ
            if v == 0 then t
            else trieAdd 8 (sym8Idx (addTup4 (sym4List.getD x.1.2 (0,0,0,0)) cc1))
              (sym8Idx (addTup4 (sym4List.getD x.1.1 (0,0,0,0)) cc2)) v t) RowTrie.empty)).sum = _
    rw [hmap_eq]
    -- Commute finite `List.sum` with `Finset.sum` over `p, q : Fin b.r`!
    have hlist_fin_comm : ∀ {α : Type} (l : List α) (f : α → Fin b.r → ℂ),
        (l.map fun x => ∑ p : Fin b.r, f x p).sum = ∑ p : Fin b.r, (l.map fun x => f x p).sum := by
      intro α l f; induction l with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
    have hsum_inner : ∀ (aapI : Nat × Nat) (qColI : List (Nat × Int)),
        ((b.blk.zip b.Qcols).map fun (aapJ, qColJ) =>
          (∑ p : Fin b.r, ∑ q : Fin b.r,
            (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
          star (uVal aapI) * uVal aapJ).sum =
        ∑ p : Fin b.r, ∑ q : Fin b.r,
          (matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)) * y q := by
      intro aapI qColI
      have hrw : ∀ (aapJ : Nat × Nat) (qColJ : List (Nat × Int)),
          (∑ p : Fin b.r, ∑ q : Fin b.r,
            (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
          star (uVal aapI) * uVal aapJ =
          ∑ p : Fin b.r, ∑ q : Fin b.r,
            (matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)) *
            ((qCoeff qColJ q.val : ℂ) * uVal aapJ) := fun aapJ qColJ => by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => by ring
      have hmap1 : ((b.blk.zip b.Qcols).map fun (aapJ, qColJ) =>
            (∑ p : Fin b.r, ∑ q : Fin b.r,
              (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
            star (uVal aapI) * uVal aapJ) =
          ((b.blk.zip b.Qcols).map fun x =>
            ∑ p : Fin b.r, ∑ q : Fin b.r,
              (matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)) *
              ((qCoeff x.2 q.val : ℂ) * uVal x.1)) :=
        List.map_congr_left fun x _ => hrw x.1 x.2
      rw [hmap1, hlist_fin_comm _ (fun (x : (Nat × Nat) × List (Nat × Int)) p => ∑ q : Fin b.r,
            (matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)) *
            ((qCoeff x.2 q.val : ℂ) * uVal x.1))]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hlist_fin_comm _ (fun (x : (Nat × Nat) × List (Nat × Int)) q =>
            (matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)) *
            ((qCoeff x.2 q.val : ℂ) * uVal x.1))]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hmul_list : ∀ {α : Type} (c : ℂ) (g : α → ℂ) (l : List α), (l.map fun x => c * g x).sum = c * (l.map g).sum := by
        intro α c g l; induction l with | nil => simp | cons a as ih => simp [ih, mul_add]
      rw [hmul_list ((matGet b.A p.val q.val : ℂ) * ((qCoeff qColI p.val : ℂ) * star (uVal aapI)))
            (fun (x : (Nat × Nat) × List (Nat × Int)) => (qCoeff x.2 q.val : ℂ) * uVal x.1)]
    have hmap2 : ((b.blk.zip b.Qcols).map fun (aapI, qColI) =>
          ((b.blk.zip b.Qcols).map fun (aapJ, qColJ) =>
            (∑ p : Fin b.r, ∑ q : Fin b.r,
              (qCoeff qColI p.val : ℂ) * (matGet b.A p.val q.val : ℂ) * (qCoeff qColJ q.val : ℂ)) *
            star (uVal aapI) * uVal aapJ).sum) =
        ((b.blk.zip b.Qcols).map fun x =>
          ∑ p : Fin b.r, ∑ q : Fin b.r,
            (matGet b.A p.val q.val : ℂ) * ((qCoeff x.2 p.val : ℂ) * star (uVal x.1)) * y q) :=
      List.map_congr_left fun x _ => hsum_inner x.1 x.2
    rw [hmap2, hlist_fin_comm _ (fun (x : (Nat × Nat) × List (Nat × Int)) p => ∑ q : Fin b.r,
          (matGet b.A p.val q.val : ℂ) * ((qCoeff x.2 p.val : ℂ) * star (uVal x.1)) * y q)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hlist_fin_comm _ (fun (x : (Nat × Nat) × List (Nat × Int)) q =>
          (matGet b.A p.val q.val : ℂ) * ((qCoeff x.2 p.val : ℂ) * star (uVal x.1)) * y q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hstar_y : star (y p) = ((b.blk.zip b.Qcols).map fun x =>
        (qCoeff x.2 p.val : ℂ) * star (uVal x.1)).sum := by
      have hstar_list : ∀ l : List ℂ, star l.sum = (l.map star).sum := fun l => by
        induction l with | nil => simp | cons a as ih => simp [ih]
      simp only [y, hstar_list, List.map_map]
      refine congr_arg List.sum (List.map_congr_left fun x _ => ?_)
      rcases x with ⟨aap, qCol⟩; dsimp only
      simp only [Function.comp_apply, Complex.star_def, map_mul, map_intCast]
    rw [hstar_y]
    have hfac : ∀ {α : Type} (a c : ℂ) (g : α → ℂ) (l : List α),
        (l.map fun x => a * g x * c).sum = a * (l.map g).sum * c := by
      intro α a c g l; induction l with | nil => simp | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [hfac (matGet b.A p.val q.val : ℂ) (y q) (fun (x : (Nat × Nat) × List (Nat × Int)) => (qCoeff x.2 p.val : ℂ) * star (uVal x.1))]
  rw [heval]
  exact cholesky_dd_nonneg b hvalid y

private lemma buildRawCertTrie_def :
    buildRawCertTrie = trieMergeAll 4 (allBlockCerts.map fun b => trieScale b.copies (buildBlockPhiTrie b)) := rfl

private lemma buildRawCertTrieAux_props (blocks : List OrbitBlockCert)
    (hall : ∀ b ∈ blocks, checkSymAndDD b = true)
    (hcopies : ∀ b ∈ blocks, (0 : Int) ≤ b.copies) (z : Fin 4 → ℂ) :
    let t := trieMergeAll 4 (blocks.map fun b => trieScale b.copies (buildBlockPhiTrie b))
    DepthTrie 8 t ∧ RowBound 165 1 0 t ∧ ColPred (· < 165) t ∧ 0 ≤ (evalTrie (mon8 · z) t).re := by
  have hts : ∀ t ∈ blocks.map fun b => trieScale b.copies (buildBlockPhiTrie b),
      DepthTrie 8 t ∧ RowBound 165 1 0 t ∧ ColPred (· < 165) t := by
    intro t ht; simp only [List.mem_map] at ht
    rcases ht with ⟨b, hb, rfl⟩
    have hbp := buildBlockPhiTrie_props b (hall b hb) z
    exact ⟨depthTrie_trieScale b.copies hbp.1, rowBound_trieScale b.copies hbp.2.1,
           colPred_trieScale b.copies hbp.2.2.1⟩
  have hm := trieMergeAll_props 4 _ (fun t ht => (hts t ht).1)
  refine ⟨hm.1,
          trieMergeAll_rowBound 4 _ (fun t ht => (hts t ht).1) (fun t ht => (hts t ht).2.1),
          trieMergeAll_colPred 4 _ (fun t ht => (hts t ht).1) (fun t ht => (hts t ht).2.2), ?_⟩
  unfold evalTrie
  rw [hm.2, List.map_map]
  have hlist_re_nn : ∀ l : List ℂ, (∀ c ∈ l, 0 ≤ c.re) → 0 ≤ l.sum.re := by
    intro l hl; induction l with
    | nil => simp
    | cons a as ih => simp only [List.sum_cons, Complex.add_re]; linarith [hl a (by simp), ih fun c hc => hl c (by simp [hc])]
  refine hlist_re_nn _ fun c hc => ?_
  simp only [List.mem_map, Function.comp_apply] at hc
  rcases hc with ⟨b, hb, rfl⟩
  rw [evalTrieAux_trieScale]
  rw [Complex.mul_re]
  simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  have hcp : (0 : ℝ) ≤ (b.copies : ℝ) := by exact_mod_cast hcopies b hb
  exact mul_nonneg hcp (buildBlockPhiTrie_props b (hall b hb) z).2.2.2

/-- Combined pre-symmetrization certificate `buildRawCertTrie` is PSD for every `z : Fin 4 → ℂ`! -/
private lemma buildRawCertTrie_props (z : Fin 4 → ℂ) :
    DepthTrie 8 buildRawCertTrie ∧
    RowBound 165 1 0 buildRawCertTrie ∧
    ColPred (· < 165) buildRawCertTrie ∧
    0 ≤ (evalTrie (mon8 · z) buildRawCertTrie).re := by
  have hall := allBlocks_valid
  simp only [checkAllBlocks, List.all_eq_true] at hall
  have hcopies_nn : allBlockCerts.all (fun b => b.copies >= 0) = true := by rfl
  simp only [List.all_eq_true, decide_eq_true_eq] at hcopies_nn
  rw [buildRawCertTrie_def]
  exact buildRawCertTrieAux_props allBlockCerts hall (fun b hb => hcopies_nn b hb) z

/-- Permuting a depth-8 bounded `RowTrie` by `p ∈ s4Perms` evaluates to `evalTrie (mon8 · (z ∘ permFn p))`! -/
private lemma evalTrie_permuteTrie {p : Tup4} (hp : p ∈ s4Perms) {t : RowTrie}
    (hd : DepthTrie 8 t) (hb : RowBound 165 1 0 t) (hc : ColPred (· < 165) t) (z : Fin 4 → ℂ) :
    evalTrie (mon8 · z) (permuteTrie p t) = evalTrie (mon8 · (fun k => z (permFn p k))) t := by
  have hpv : checkPermValid p = true := by
    have := s4Perms_valid; simp only [List.all_eq_true] at this; exact this p hp
  have hmon_perm : ∀ i : Nat, i < 165 →
      mon8 (natTrieGet 8 i (buildPermNatTrie p)) z = mon8 i (fun k => z (permFn p k)) := fun i hi => by
    have hpr := perm8_props hp hi
    simp only [mon8, hpr.2]
    exact monTup_perm p hpv _ z
  have hrow_perm : ∀ row : List (Nat × Int), (∀ kv ∈ row, kv.1 < 165) →
      evalRow (mon8 · z) (permuteRow (buildPermNatTrie p) row) =
        evalRow (mon8 · (fun k => z (permFn p k))) row := by
    intro row hrow
    unfold permuteRow
    have hfold : ∀ (init : List (Nat × Int)) (l : List (Nat × Int)), (∀ kv ∈ l, kv.1 < 165) →
        evalRow (mon8 · z) (l.foldl (fun acc (jj, v) => addAssoc (natTrieGet 8 jj (buildPermNatTrie p)) v acc) init) =
          evalRow (mon8 · z) init + evalRow (mon8 · (fun k => z (permFn p k))) l := by
      intro init l; induction l generalizing init with
      | nil => intro _; simp [evalRow]
      | cons kv rest ih =>
        rcases kv with ⟨jj, v⟩
        intro hl
        have hjj : jj < 165 := hl (jj, v) (by simp)
        simp only [List.foldl_cons, evalRow, ih _ (fun x hx => hl x (by simp [hx])),
          evalRow_addAssoc, hmon_perm jj hjj]
        ring
    simpa [evalRow] using hfold [] row hrow
  unfold permuteTrie
  have hmd : ∀ tr ∈ (List.range 165).map fun ii =>
      let row := trieGetRow 8 ii t
      if row.isEmpty then RowTrie.empty
      else trieSingleRow 8 (natTrieGet 8 ii (buildPermNatTrie p)) (permuteRow (buildPermNatTrie p) row),
      DepthTrie 8 tr := by
    intro tr htr; simp only [List.mem_map] at htr
    rcases htr with ⟨ii, _, rfl⟩
    split_ifs
    · exact DepthTrie.empty
    · exact depthTrie_trieSingleRow 8 _ _
  have hm := trieMergeAll_props 9 _ hmd
  rw [evalTrie_eq_sum_range (mon8 · (fun k => z (permFn p k))) (d := 8) (N := 165) (by norm_num) hd hb]
  unfold evalTrie
  rw [hm.2, List.map_map]
  refine congr_arg List.sum (List.map_congr_left fun ii hii => ?_)
  have hii165 : ii < 165 := List.mem_range.mp hii
  simp only [Function.comp_apply]
  split_ifs with hemp
  · have hnil : trieGetRow 8 ii t = [] := List.isEmpty_iff.mp hemp
    simp [hnil, evalTrieAux, evalRow]
  · have hpr := perm8_props hp hii165
    rw [evalTrieAux_trieSingleRow (mon8 · z) (mon8 · z) 8 1 0 _ (by omega)]
    simp only [zero_add, one_mul, hmon_perm ii hii165, hrow_perm _ (colPred_trieGetRow ii hc)]

private lemma buildCertFullTrie_def :
    buildCertFullTrie = trieMergeAll 6 (s4Perms.map fun p => permuteTrie p buildRawCertTrie) := rfl

private lemma evalTrie_symS4_nonneg (raw : RowTrie)
    (hd : DepthTrie 8 raw) (hb : RowBound 165 1 0 raw) (hc : ColPred (· < 165) raw)
    (hnn : ∀ w : Fin 4 → ℂ, 0 ≤ (evalTrie (mon8 · w) raw).re) (z : Fin 4 → ℂ) :
    0 ≤ (evalTrie (mon8 · z) (trieMergeAll 6 (s4Perms.map fun p => permuteTrie p raw))).re := by
  have hmd : ∀ tr ∈ s4Perms.map fun p => permuteTrie p raw, DepthTrie 8 tr := by
    intro tr htr; simp only [List.mem_map] at htr
    rcases htr with ⟨p, _, rfl⟩
    unfold permuteTrie
    refine (trieMergeAll_props 9 _ ?_).1
    intro t' ht'; simp only [List.mem_map] at ht'
    rcases ht' with ⟨ii, _, rfl⟩
    split_ifs; exact DepthTrie.empty; exact depthTrie_trieSingleRow 8 _ _
  have hm := trieMergeAll_props 6 _ hmd
  unfold evalTrie
  rw [hm.2, List.map_map]
  have hlist_re_nn : ∀ l : List ℂ, (∀ c ∈ l, 0 ≤ c.re) → 0 ≤ l.sum.re := by
    intro l hl; induction l with
    | nil => simp
    | cons a as ih => simp only [List.sum_cons, Complex.add_re]; linarith [hl a (by simp), ih fun c hc => hl c (by simp [hc])]
  refine hlist_re_nn _ fun c hc' => ?_
  simp only [List.mem_map, Function.comp_apply] at hc'
  rcases hc' with ⟨p, hp, rfl⟩
  change 0 ≤ (evalTrie (mon8 · z) (permuteTrie p raw)).re
  rw [evalTrie_permuteTrie hp hd hb hc z]
  exact hnn (fun k => z (permFn p k))

/-- **Full Certificate Non-Negativity**: `0 ≤ (evalTrie (mon8 · z) buildCertFullTrie).re` for EVERY `z : Fin 4 → ℂ`! -/
private lemma evalTrie_buildCertFullTrie_nonneg (z : Fin 4 → ℂ) :
    0 ≤ (evalTrie (mon8 · z) buildCertFullTrie).re := by
  have hraw := buildRawCertTrie_props z
  rw [buildCertFullTrie_def]
  exact evalTrie_symS4_nonneg buildRawCertTrie hraw.1 hraw.2.1 hraw.2.2.1
    (fun w => (buildRawCertTrie_props w).2.2.2) z

end TwoQubitExactMin

open TwoQubitExactMin

/-! ### Part 5: Main Headline Theorems (`F₂(|ψ⟩) ≥ 7/4` and Exact Global Minimum `min F₂ = 7/4`) -/

/-- **Exact Sharp 2-Qubit Pauli Fourth-Moment Lower Bound (`F₂(|ψ⟩) ≥ 7/4`)**:
    For EVERY 2-qubit pure quantum state `|ψ⟩ ∈ (ℂ²)^⊗2` (`IsUnitState ψ`),
      `7 / 4 ≤ pauliMoment4 2 ψ`.
    Proved unconditionally via a pure-kernel exact integer degree-8 Hermitian SOS certificate
    (zero `sorry`, zero `native_decide`, standard three axioms `[propext, Classical.choice, Quot.sound]` only). -/
theorem pauliMoment4_two_ge_seven_fourths {ψ : QState 2} (hunit : IsUnitState ψ) :
    (7 / 4 : ℝ) ≤ pauliMoment4 2 ψ := by
  let z : Fin 4 → ℂ := fun i => ψ (fin4ToF2 i)
  have hz_eq : (fun x : F2 2 => z (f2ToFin4 x)) = ψ := by
    ext x; simp [z, fin4ToF2_f2ToFin4]
  have hz_unit : ∑ i : Fin 4, Complex.normSq (z i) = 1 := by
    have hu : ∑ x : F2 2, Complex.normSq (ψ x) = 1 := by
      have := congr_arg Complex.re hunit
      rw [innerProd_self_re, Complex.one_re] at this
      exact this
    rw [← hu]
    symm
    exact Fintype.sum_equiv equivF2Fin4 _ _ fun x => by
      change Complex.normSq (ψ x) = Complex.normSq (ψ (fin4ToF2 (f2ToFin4 x)))
      rw [fin4ToF2_f2ToFin4]
  have heq : evalTrie (mon8 · z) buildCertFullTrie = evalTrie (mon8 · z) (buildTargetTrie targetScale) :=
    evalTrieAux_trieEq (mon8 · z) (mon8 · z) 1 0 buildCertFullTrie (buildTargetTrie targetScale) cert_matches_target
  have hnn : 0 ≤ (evalTrie (mon8 · z) (buildTargetTrie targetScale)).re := by
    rw [← heq]; exact evalTrie_buildCertFullTrie_nonneg z
  rw [evalTrie_buildTargetTrie targetScale z hz_unit, hz_eq, Complex.ofReal_re] at hnn
  have hscale_pos : (0 : ℝ) < (targetScale : ℝ) := by
    change (0 : ℝ) < ((24 * 27648 : ℤ) : ℝ); norm_num
  nlinarith

/-- **Exact Global Minimum of the 2-Qubit Pauli Fourth Moment (`min_{|ψ⟩ ∈ ℂP³} F₂(|ψ⟩) = 7/4`)**:
    Every 2-qubit unit state satisfies `7 / 4 ≤ pauliMoment4 2 ψ`, and the explicit 2-qubit MUB
    fiducial `spikeState 2 (1 / 2)` achieves exact equality `pauliMoment4 2 ψ = 7 / 4`. -/
theorem pauliMoment4_two_min_eq_seven_fourths :
    (∀ ψ : QState 2, IsUnitState ψ → (7 / 4 : ℝ) ≤ pauliMoment4 2 ψ) ∧
    (∃ ψ : QState 2, IsUnitState ψ ∧ pauliMoment4 2 ψ = 7 / 4) := by
  refine ⟨fun _ h => pauliMoment4_two_ge_seven_fourths h, ?_⟩
  have hf : SpikeFeasible 2 (1 / 2) := by unfold SpikeFeasible; norm_num
  refine ⟨spikeState 2 (1 / 2), spikeState_unit hf, ?_⟩
  rw [pauliMoment4_spikeState (by norm_num) hf]
  unfold spikeMomentPoly; norm_num

end MultiQubitMUB
