/-!
# Exact Integer Degree-8 SOS Certificate for `F₂(|ψ⟩) ≥ 7/4` (Pure-Kernel `by rfl`)

Auto-generated exact integer certificate data and pure-kernel `Bool` verifiers (zero `sorry`,
zero `native_decide`, zero `Classical`) certifying:
  `24 * 27648 * (4 * F₂(ψ) - 7 * ‖ψ‖⁸) * ‖ψ‖⁸ = ∑_{o=0..5} copies_o * ∑_{σ ∈ S₄} y_o(ψ ∘ σ)† A_o y_o(ψ ∘ σ)`
where each of the 6 reduced symmetric integer blocks `A_o` (sizes `33, 19, 23, 28, 23, 24`)
satisfies `S_o² * A_o = W_o * W_oᵀ + E_o` with `E_o` strictly diagonally dominant.
-/

namespace MultiQubitMUB

namespace TwoQubitExactCert

/-- Exponent 4-tuple `(c0, c1, c2, c3)` for a degree-`k` monomial `z₀^c0 z₁^c1 z₂^c2 z₃^c3`. -/
abbrev Tup4 := Nat × Nat × Nat × Nat

def addTup4 (a b : Tup4) : Tup4 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

def permTup4 (p : Nat × Nat × Nat × Nat) (t : Tup4) : Tup4 :=
  let get (k : Nat) : Nat :=
    if p.1 == k then t.1 else if p.2.1 == k then t.2.1 else if p.2.2.1 == k then t.2.2.1 else t.2.2.2
  (get 0, get 1, get 2, get 3)

def sym4List : List Tup4 := [
  (0, 0, 0, 4), (0, 0, 1, 3), (0, 0, 2, 2), (0, 0, 3, 1), (0, 0, 4, 0),
  (0, 1, 0, 3), (0, 1, 1, 2), (0, 1, 2, 1), (0, 1, 3, 0), (0, 2, 0, 2),
  (0, 2, 1, 1), (0, 2, 2, 0), (0, 3, 0, 1), (0, 3, 1, 0), (0, 4, 0, 0),
  (1, 0, 0, 3), (1, 0, 1, 2), (1, 0, 2, 1), (1, 0, 3, 0), (1, 1, 0, 2),
  (1, 1, 1, 1), (1, 1, 2, 0), (1, 2, 0, 1), (1, 2, 1, 0), (1, 3, 0, 0),
  (2, 0, 0, 2), (2, 0, 1, 1), (2, 0, 2, 0), (2, 1, 0, 1), (2, 1, 1, 0),
  (2, 2, 0, 0), (3, 0, 0, 1), (3, 0, 1, 0), (3, 1, 0, 0), (4, 0, 0, 0)
]

def sym8List : List Tup4 := [
  (0, 0, 0, 8), (0, 0, 1, 7), (0, 0, 2, 6), (0, 0, 3, 5), (0, 0, 4, 4),
  (0, 0, 5, 3), (0, 0, 6, 2), (0, 0, 7, 1), (0, 0, 8, 0), (0, 1, 0, 7),
  (0, 1, 1, 6), (0, 1, 2, 5), (0, 1, 3, 4), (0, 1, 4, 3), (0, 1, 5, 2),
  (0, 1, 6, 1), (0, 1, 7, 0), (0, 2, 0, 6), (0, 2, 1, 5), (0, 2, 2, 4),
  (0, 2, 3, 3), (0, 2, 4, 2), (0, 2, 5, 1), (0, 2, 6, 0), (0, 3, 0, 5),
  (0, 3, 1, 4), (0, 3, 2, 3), (0, 3, 3, 2), (0, 3, 4, 1), (0, 3, 5, 0),
  (0, 4, 0, 4), (0, 4, 1, 3), (0, 4, 2, 2), (0, 4, 3, 1), (0, 4, 4, 0),
  (0, 5, 0, 3), (0, 5, 1, 2), (0, 5, 2, 1), (0, 5, 3, 0), (0, 6, 0, 2),
  (0, 6, 1, 1), (0, 6, 2, 0), (0, 7, 0, 1), (0, 7, 1, 0), (0, 8, 0, 0),
  (1, 0, 0, 7), (1, 0, 1, 6), (1, 0, 2, 5), (1, 0, 3, 4), (1, 0, 4, 3),
  (1, 0, 5, 2), (1, 0, 6, 1), (1, 0, 7, 0), (1, 1, 0, 6), (1, 1, 1, 5),
  (1, 1, 2, 4), (1, 1, 3, 3), (1, 1, 4, 2), (1, 1, 5, 1), (1, 1, 6, 0),
  (1, 2, 0, 5), (1, 2, 1, 4), (1, 2, 2, 3), (1, 2, 3, 2), (1, 2, 4, 1),
  (1, 2, 5, 0), (1, 3, 0, 4), (1, 3, 1, 3), (1, 3, 2, 2), (1, 3, 3, 1),
  (1, 3, 4, 0), (1, 4, 0, 3), (1, 4, 1, 2), (1, 4, 2, 1), (1, 4, 3, 0),
  (1, 5, 0, 2), (1, 5, 1, 1), (1, 5, 2, 0), (1, 6, 0, 1), (1, 6, 1, 0),
  (1, 7, 0, 0), (2, 0, 0, 6), (2, 0, 1, 5), (2, 0, 2, 4), (2, 0, 3, 3),
  (2, 0, 4, 2), (2, 0, 5, 1), (2, 0, 6, 0), (2, 1, 0, 5), (2, 1, 1, 4),
  (2, 1, 2, 3), (2, 1, 3, 2), (2, 1, 4, 1), (2, 1, 5, 0), (2, 2, 0, 4),
  (2, 2, 1, 3), (2, 2, 2, 2), (2, 2, 3, 1), (2, 2, 4, 0), (2, 3, 0, 3),
  (2, 3, 1, 2), (2, 3, 2, 1), (2, 3, 3, 0), (2, 4, 0, 2), (2, 4, 1, 1),
  (2, 4, 2, 0), (2, 5, 0, 1), (2, 5, 1, 0), (2, 6, 0, 0), (3, 0, 0, 5),
  (3, 0, 1, 4), (3, 0, 2, 3), (3, 0, 3, 2), (3, 0, 4, 1), (3, 0, 5, 0),
  (3, 1, 0, 4), (3, 1, 1, 3), (3, 1, 2, 2), (3, 1, 3, 1), (3, 1, 4, 0),
  (3, 2, 0, 3), (3, 2, 1, 2), (3, 2, 2, 1), (3, 2, 3, 0), (3, 3, 0, 2),
  (3, 3, 1, 1), (3, 3, 2, 0), (3, 4, 0, 1), (3, 4, 1, 0), (3, 5, 0, 0),
  (4, 0, 0, 4), (4, 0, 1, 3), (4, 0, 2, 2), (4, 0, 3, 1), (4, 0, 4, 0),
  (4, 1, 0, 3), (4, 1, 1, 2), (4, 1, 2, 1), (4, 1, 3, 0), (4, 2, 0, 2),
  (4, 2, 1, 1), (4, 2, 2, 0), (4, 3, 0, 1), (4, 3, 1, 0), (4, 4, 0, 0),
  (5, 0, 0, 3), (5, 0, 1, 2), (5, 0, 2, 1), (5, 0, 3, 0), (5, 1, 0, 2),
  (5, 1, 1, 1), (5, 1, 2, 0), (5, 2, 0, 1), (5, 2, 1, 0), (5, 3, 0, 0),
  (6, 0, 0, 2), (6, 0, 1, 1), (6, 0, 2, 0), (6, 1, 0, 1), (6, 1, 1, 0),
  (6, 2, 0, 0), (7, 0, 0, 1), (7, 0, 1, 0), (7, 1, 0, 0), (8, 0, 0, 0)
]

def s4Perms : List (Nat × Nat × Nat × Nat) := [
  (0, 1, 2, 3), (0, 1, 3, 2), (0, 2, 1, 3), (0, 2, 3, 1), (0, 3, 1, 2), (0, 3, 2, 1),
  (1, 0, 2, 3), (1, 0, 3, 2), (1, 2, 0, 3), (1, 2, 3, 0), (1, 3, 0, 2), (1, 3, 2, 0),
  (2, 0, 1, 3), (2, 0, 3, 1), (2, 1, 0, 3), (2, 1, 3, 0), (2, 3, 0, 1), (2, 3, 1, 0),
  (3, 0, 1, 2), (3, 0, 2, 1), (3, 1, 0, 2), (3, 1, 2, 0), (3, 2, 0, 1), (3, 2, 1, 0)
]

/-- Binomial `C(n, 3)` for small `n`. -/
def binom3 (n : Nat) : Nat := if n < 3 then 0 else n * (n - 1) * (n - 2) / 6
/-- Binomial `C(n, 2)` for small `n`. -/
def binom2 (n : Nat) : Nat := if n < 2 then 0 else n * (n - 1) / 2

/-- Exact lexicographic index in `sym4List` for `(c0, c1, c2, c3)` with `c0+c1+c2+c3 = 4`. -/
def sym4Idx (t : Tup4) : Nat :=
  let r1 := 4 - t.1
  let r2 := r1 - t.2.1
  (35 - binom3 (r1 + 3)) + (binom2 (r1 + 2) - binom2 (r2 + 2)) + t.2.2.1

/-- Exact lexicographic index in `sym8List` for `(c0, c1, c2, c3)` with `c0+c1+c2+c3 = 8`. -/
def sym8Idx (t : Tup4) : Nat :=
  let r1 := 8 - t.1
  let r2 := r1 - t.2.1
  (165 - binom3 (r1 + 3)) + (binom2 (r1 + 2) - binom2 (r2 + 2)) + t.2.2.1

def sym4Mult : List Int := [Int.ofNat 1, Int.ofNat 4, Int.ofNat 6, Int.ofNat 4, Int.ofNat 1, Int.ofNat 4, Int.ofNat 12, Int.ofNat 12, Int.ofNat 4, Int.ofNat 6, Int.ofNat 12, Int.ofNat 6, Int.ofNat 4, Int.ofNat 4, Int.ofNat 1, Int.ofNat 4, Int.ofNat 12, Int.ofNat 12, Int.ofNat 4, Int.ofNat 12, Int.ofNat 24, Int.ofNat 12, Int.ofNat 12, Int.ofNat 12, Int.ofNat 4, Int.ofNat 6, Int.ofNat 12, Int.ofNat 6, Int.ofNat 12, Int.ofNat 12, Int.ofNat 6, Int.ofNat 4, Int.ofNat 4, Int.ofNat 4, Int.ofNat 1]
def sym8Mult : List Int := [
  1, 8, 28, 56, 70, 56, 28, 8, 1, 8, 56, 168, 280, 280, 168,
  56, 8, 28, 168, 420, 560, 420, 168, 28, 56, 280, 560, 560, 280, 56,
  70, 280, 420, 280, 70, 56, 168, 168, 56, 28, 56, 28, 8, 8, 1,
  8, 56, 168, 280, 280, 168, 56, 8, 56, 336, 840, 1120, 840, 336, 56,
  168, 840, 1680, 1680, 840, 168, 280, 1120, 1680, 1120, 280, 280, 840, 840, 280,
  168, 336, 168, 56, 56, 8, 28, 168, 420, 560, 420, 168, 28, 168, 840,
  1680, 1680, 840, 168, 420, 1680, 2520, 1680, 420, 560, 1680, 1680, 560, 420, 840,
  420, 168, 168, 28, 56, 280, 560, 560, 280, 56, 280, 1120, 1680, 1120, 280,
  560, 1680, 1680, 560, 560, 1120, 560, 280, 280, 56, 70, 280, 420, 280, 70,
  280, 840, 840, 280, 420, 840, 420, 280, 280, 70, 56, 168, 168, 56, 168,
  336, 168, 168, 168, 56, 28, 56, 28, 56, 56, 28, 8, 8, 8, 1
]

/-- Pure depth-`d` binary trie mapping `Nat` keys (up to `2^d - 1`) to sparse `List (Nat × Int)` rows. -/
inductive RowTrie where
  | empty : RowTrie
  | leaf : List (Nat × Int) → RowTrie
  | node : RowTrie → RowTrie → RowTrie
  deriving Repr, BEq

def addAssoc (j : Nat) (v : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => if v == 0 then [] else [(j, v)]
  | (k, w) :: rest =>
    if k == j then
      let nv := w + v
      if nv == 0 then rest else (k, nv) :: rest
    else if j < k then
      if v == 0 then (k, w) :: rest else (j, v) :: (k, w) :: rest
    else (k, w) :: addAssoc j v rest

def trieAdd : Nat → Nat → Nat → Int → RowTrie → RowTrie
  | 0, _, j, v, RowTrie.empty => RowTrie.leaf (addAssoc j v [])
  | 0, _, j, v, RowTrie.leaf xs => RowTrie.leaf (addAssoc j v xs)
  | 0, _, _, _, t => t
  | d + 1, i, j, v, RowTrie.empty =>
    if i % 2 == 0 then RowTrie.node (trieAdd d (i / 2) j v RowTrie.empty) RowTrie.empty
    else RowTrie.node RowTrie.empty (trieAdd d (i / 2) j v RowTrie.empty)
  | d + 1, i, j, v, RowTrie.node l r =>
    if i % 2 == 0 then RowTrie.node (trieAdd d (i / 2) j v l) r
    else RowTrie.node l (trieAdd d (i / 2) j v r)
  | _ + 1, _, _, _, t => t

def trieGetRow : Nat → Nat → RowTrie → List (Nat × Int)
  | 0, _, RowTrie.leaf xs => xs
  | d + 1, i, RowTrie.node l r => if i % 2 == 0 then trieGetRow d (i / 2) l else trieGetRow d (i / 2) r
  | _, _, _ => []

/-- Merge two sorted sparse rows `(j, v)` summing entries at equal `j` and dropping zeros (pure structural recursion!). -/
def mergeRows (xs ys : List (Nat × Int)) : List (Nat × Int) :=
  ys.foldl (fun acc (j, v) => addAssoc j v acc) xs

/-- Structural check that a `RowTrie` contains no nonzero entries. -/
def isEmptyTrie : RowTrie → Bool
  | RowTrie.empty => true
  | RowTrie.leaf xs => xs.isEmpty
  | RowTrie.node l r => isEmptyTrie l && isEmptyTrie r

/-- Structural equality of two same-depth `RowTrie`s up to empty leaves (visits each node ONCE!). -/
def trieEq : RowTrie → RowTrie → Bool
  | RowTrie.empty, t => isEmptyTrie t
  | t, RowTrie.empty => isEmptyTrie t
  | RowTrie.leaf xs, RowTrie.leaf ys => xs == ys
  | RowTrie.node l1 r1, RowTrie.node l2 r2 => trieEq l1 l2 && trieEq r1 r2
  | _, _ => false

/-- Merge two `RowTrie`s of the same depth (`O(nodes)` with stack depth ≤ 8!). -/
def trieMerge : RowTrie → RowTrie → RowTrie
  | RowTrie.empty, t => t
  | t, RowTrie.empty => t
  | RowTrie.leaf xs, RowTrie.leaf ys => RowTrie.leaf (mergeRows xs ys)
  | RowTrie.node l1 r1, RowTrie.node l2 r2 => RowTrie.node (trieMerge l1 l2) (trieMerge r1 r2)
  | t, _ => t

/-- Balanced pairwise reduction of a list of `RowTrie`s (log-depth in the kernel!). -/
def triePairUp : List RowTrie → List RowTrie
  | [] => []
  | [t] => [t]
  | t1 :: t2 :: rest => trieMerge t1 t2 :: triePairUp rest

def trieMergeAll : Nat → List RowTrie → RowTrie
  | _, [] => RowTrie.empty
  | _, [t] => t
  | 0, ts => ts.foldl trieMerge RowTrie.empty
  | fuel + 1, ts => trieMergeAll fuel (triePairUp ts)

/-- Scale all entries of a `RowTrie` by an integer `c`. -/
def scaleRow (c : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => []
  | (j, v) :: rest => let nv := c * v; if nv == 0 then scaleRow c rest else (j, nv) :: scaleRow c rest

def trieScale (c : Int) : RowTrie → RowTrie
  | RowTrie.empty => RowTrie.empty
  | RowTrie.leaf xs => RowTrie.leaf (scaleRow c xs)
  | RowTrie.node l r => RowTrie.node (trieScale c l) (trieScale c r)

/-- Insert an entire sorted sparse row at key `i` into an empty trie of depth `d`. -/
def trieSingleRow : Nat → Nat → List (Nat × Int) → RowTrie
  | 0, _, xs => RowTrie.leaf xs
  | d + 1, i, xs =>
    if i % 2 == 0 then RowTrie.node (trieSingleRow d (i / 2) xs) RowTrie.empty
    else RowTrie.node RowTrie.empty (trieSingleRow d (i / 2) xs)

/-- Depth-`d` binary trie mapping `Nat → Nat` (`O(8)` kernel lookup for permutation tables!). -/
inductive NatTrie where
  | empty : NatTrie
  | leaf : Nat → NatTrie
  | node : NatTrie → NatTrie → NatTrie

def natTrieSet : Nat → Nat → Nat → NatTrie → NatTrie
  | 0, _, v, _ => NatTrie.leaf v
  | d + 1, i, v, NatTrie.empty =>
    if i % 2 == 0 then NatTrie.node (natTrieSet d (i / 2) v NatTrie.empty) NatTrie.empty
    else NatTrie.node NatTrie.empty (natTrieSet d (i / 2) v NatTrie.empty)
  | d + 1, i, v, NatTrie.node l r =>
    if i % 2 == 0 then NatTrie.node (natTrieSet d (i / 2) v l) r
    else NatTrie.node l (natTrieSet d (i / 2) v r)
  | _ + 1, _, _, t => t

def natTrieGet : Nat → Nat → NatTrie → Nat
  | 0, _, NatTrie.leaf v => v
  | d + 1, i, NatTrie.node l r => if i % 2 == 0 then natTrieGet d (i / 2) l else natTrieGet d (i / 2) r
  | _, _, _ => 0

def buildPermNatTrie (p : Tup4) : NatTrie :=
  (sym8List.zip (List.range 165)).foldl (fun nt (t, i) => natTrieSet 8 i (sym8Idx (permTup4 p t)) nt) NatTrie.empty

/-- Collect all `(i, j, v)` entries from a depth-`d` trie (bit-reconstructed key `i`). -/
def trieToEntriesAux (bitMul keyAcc : Nat) : RowTrie → List (Nat × Nat × Int) → List (Nat × Nat × Int)
  | RowTrie.empty, acc => acc
  | RowTrie.leaf xs, acc => xs.foldl (fun a (j, v) => if v == 0 then a else (keyAcc, j, v) :: a) acc
  | RowTrie.node l r, acc =>
    trieToEntriesAux (bitMul * 2) keyAcc l (trieToEntriesAux (bitMul * 2) (keyAcc + bitMul) r acc)

def trieToEntries (t : RowTrie) : List (Nat × Nat × Int) := trieToEntriesAux 1 0 t []

/-- Check that every entry of `t1` equals the corresponding entry of `t2` on `0..n-1`. -/
def trieEqRows (d : Nat) (t1 t2 : RowTrie) : Nat → Bool
  | 0 => true
  | n + 1 => (trieGetRow d n t1 == trieGetRow d n t2) && trieEqRows d t1 t2 n

/-- Compute `F4` trie (depth 6, keys `0..34`) from first principles over all 16 Paulis and `4⁴` tuples! -/
def pop2 (x : Nat) : Nat := (x &&& 1) + ((x >>> 1) &&& 1)
def dot2_2 (a b : Nat) : Nat := pop2 (a &&& b) &&& 1

def tupOf4 (x0 x1 x2 x3 : Nat) : Tup4 :=
  let c (k : Nat) : Nat := (if x0 == k then 1 else 0) + (if x1 == k then 1 else 0) +
    (if x2 == k then 1 else 0) + (if x3 == k then 1 else 0)
  (c 0, c 1, c 2, c 3)

def buildF4PauliX0Trie (a b x0 : Nat) : RowTrie :=
  (List.range 4).foldl (fun t x1 =>
    (List.range 4).foldl (fun t x2 =>
      (List.range 4).foldl (fun t x3 =>
        let sgn : Int := if dot2_2 b (x0 ^^^ x1 ^^^ x2 ^^^ x3) == 1 then -1 else 1
        let i4 := sym4Idx (tupOf4 x0 x1 x2 x3)
        let j4 := sym4Idx (tupOf4 (x0 ^^^ a) (x1 ^^^ a) (x2 ^^^ a) (x3 ^^^ a))
        trieAdd 6 i4 j4 sgn t
      ) t) t) RowTrie.empty

def buildF4PauliTrie (p : Nat) : RowTrie :=
  let a := p >>> 2; let b := p &&& 3
  trieMergeAll 3 ((List.range 4).map fun x0 => buildF4PauliX0Trie a b x0)

def buildF4Trie : RowTrie :=
  trieMergeAll 5 ((List.range 16).map buildF4PauliTrie)

/-- Exact target trie `scale * C_target` (depth 8, keys `0..164`) for `scale * (4 F₂ - 7 ‖ψ‖⁸) ‖ψ‖⁸`. -/
def buildTargetTrie (scale : Int) : RowTrie :=
  let s4Pairs := sym4List.zip sym4Mult
  let f4 := buildF4Trie
  let f4Tries := (sym4List.zip (List.range 35)).map fun (ci, i4) =>
    let row := trieGetRow 6 i4 f4
    if row.isEmpty then RowTrie.empty
    else
      trieMergeAll 6 (row.map fun (j4, v) =>
        let cj := sym4List.getD j4 (0, 0, 0, 0)
        s4Pairs.foldl (fun t (ck, mk) =>
          let ii := sym8Idx (addTup4 ci ck)
          let jj := sym8Idx (addTup4 cj ck)
          trieAdd 8 ii jj (scale * 4 * v * mk) t
        ) RowTrie.empty)
  let t1 := trieMergeAll 7 f4Tries
  let diagTries := ((List.range 165).zip sym8Mult).map fun (ii, m8) =>
    trieSingleRow 8 ii [(ii, -(scale * 7 * m8))]
  trieMerge t1 (trieMergeAll 9 diagTries)

def D_glob : Int := 27648
def targetScale : Int := 24 * D_glob

/-- Structure holding one `S₄`-orbit block certificate `(copies, blk, Q_cols, A, W, S)`. -/
structure OrbitBlockCert where
  r : Nat
  m : Nat
  copies : Int
  blk : List (Nat × Nat)
  /-- Sparse columns of `Q` (length `m`; column `i` lists `(p, Q[p][i])` with `Q[p][i] ≠ 0`). -/
  Qcols : List (List (Nat × Int))
  /-- Symmetric integer matrix `A` (`r × r`). -/
  A : List (List Int)
  /-- Lower-triangular integer Cholesky factor `W` (`r × r`, row `i` has length `i + 1`). -/
  W : List (List Int)
  /-- Cholesky integer scale `S > 0`. -/
  S : Int

def blockCert0 : OrbitBlockCert := {
  r := 33, m := 53, copies := 1, S := 4,
  blk := [(0, 0), (0, 4), (0, 14), (0, 34), (1, 1), (2, 2), (2, 30), (3, 3), (4, 0), (4, 4), (4, 14), (4, 34), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (9, 27), (10, 10), (11, 11), (11, 25), (12, 12), (13, 13), (14, 0), (14, 4), (14, 14), (14, 34), (15, 15), (16, 16), (17, 17), (18, 18), (19, 19), (20, 20), (21, 21), (22, 22), (23, 23), (24, 24), (25, 11), (25, 25), (26, 26), (27, 9), (27, 27), (28, 28), (29, 29), (30, 2), (30, 30), (31, 31), (32, 32), (33, 33), (34, 0), (34, 4), (34, 14), (34, 34)],
  Qcols := [
    [(17, Int.negSucc 0), (19, Int.negSucc 0), (28, Int.negSucc 0), (31, Int.ofNat 1), (32, Int.negSucc 0)],
    [(2, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 2), (22, Int.ofNat 1), (25, Int.ofNat 1), (26, Int.ofNat 1), (28, Int.ofNat 1), (29, Int.negSucc 0), (31, Int.negSucc 1)],
    [(3, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.ofNat 1), (11, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.ofNat 2), (20, Int.negSucc 0), (27, Int.negSucc 0), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(2, Int.ofNat 1), (3, Int.negSucc 0), (7, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.negSucc 0), (20, Int.negSucc 0), (24, Int.ofNat 1), (27, Int.ofNat 1), (28, Int.ofNat 1), (32, Int.ofNat 1)],
    [(5, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (15, Int.ofNat 1), (17, Int.ofNat 2), (18, Int.ofNat 1), (19, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (24, Int.ofNat 1), (25, Int.ofNat 1), (26, Int.ofNat 1), (27, Int.negSucc 0), (28, Int.ofNat 2), (29, Int.ofNat 1), (30, Int.negSucc 0), (31, Int.negSucc 2), (32, Int.ofNat 1)],
    [(5, Int.ofNat 1), (6, Int.ofNat 1), (8, Int.ofNat 1), (17, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.ofNat 3), (27, Int.ofNat 2), (28, Int.negSucc 0), (29, Int.ofNat 1), (31, Int.negSucc 0), (32, Int.negSucc 2)],
    [(1, Int.ofNat 1), (12, Int.negSucc 2), (16, Int.ofNat 3), (21, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.negSucc 0), (24, Int.ofNat 1), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.negSucc 0), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.ofNat 2), (32, Int.ofNat 4)],
    [(5, Int.negSucc 0), (8, Int.negSucc 0), (15, Int.negSucc 0), (20, Int.ofNat 2), (22, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.ofNat 1), (27, Int.negSucc 0), (28, Int.negSucc 0), (29, Int.negSucc 1), (30, Int.negSucc 0), (31, Int.negSucc 1), (32, Int.ofNat 1)],
    [(2, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.ofNat 1), (8, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (23, Int.ofNat 1), (31, Int.negSucc 1)],
    [(20, Int.negSucc 0), (29, Int.ofNat 1), (31, Int.ofNat 1)],
    [(4, Int.negSucc 0), (5, Int.ofNat 1), (6, Int.negSucc 0), (7, Int.ofNat 1), (9, Int.negSucc 0), (12, Int.negSucc 0), (17, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.ofNat 1), (22, Int.ofNat 1), (27, Int.negSucc 0)],
    [(2, Int.negSucc 0), (4, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.ofNat 1), (9, Int.ofNat 1), (21, Int.ofNat 1), (29, Int.negSucc 0)],
    [(8, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.ofNat 1), (17, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.ofNat 2), (20, Int.negSucc 0), (21, Int.ofNat 1), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.ofNat 1), (31, Int.negSucc 0), (32, Int.ofNat 2)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.negSucc 0), (15, Int.negSucc 2), (17, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.ofNat 2), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 1), (28, Int.ofNat 2), (29, Int.ofNat 1), (30, Int.ofNat 1), (31, Int.ofNat 1), (32, Int.ofNat 2)],
    [(7, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.negSucc 1), (15, Int.ofNat 3), (18, Int.ofNat 2), (19, Int.negSucc 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.ofNat 2), (26, Int.negSucc 0), (31, Int.negSucc 0), (32, Int.negSucc 0)],
    [(5, Int.ofNat 1), (9, Int.negSucc 0), (20, Int.ofNat 2), (21, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 1), (27, Int.ofNat 1), (28, Int.ofNat 1), (29, Int.negSucc 1), (30, Int.ofNat 1), (31, Int.negSucc 0)],
    [(7, Int.negSucc 0), (8, Int.negSucc 0), (19, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.ofNat 3), (26, Int.ofNat 1), (27, Int.negSucc 1), (29, Int.negSucc 0)],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (12, Int.ofNat 3), (13, Int.negSucc 2), (21, Int.ofNat 1), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 2), (25, Int.ofNat 1), (26, Int.ofNat 2), (28, Int.ofNat 4), (29, Int.negSucc 2), (30, Int.negSucc 0), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(6, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.ofNat 2), (17, Int.negSucc 0), (18, Int.negSucc 1), (20, Int.negSucc 1), (21, Int.negSucc 0), (22, Int.ofNat 2), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (28, Int.negSucc 0), (29, Int.negSucc 1), (30, Int.negSucc 1), (31, Int.ofNat 1)],
    [(5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (17, Int.negSucc 0), (20, Int.ofNat 1), (23, Int.ofNat 3), (25, Int.ofNat 1), (27, Int.negSucc 1), (29, Int.ofNat 1), (30, Int.ofNat 1)],
    [(0, Int.ofNat 1), (13, Int.negSucc 2), (16, Int.negSucc 2), (21, Int.ofNat 2), (22, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 1), (27, Int.negSucc 2), (29, Int.negSucc 0), (32, Int.ofNat 2)],
    [(8, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (28, Int.negSucc 0), (30, Int.negSucc 0), (31, Int.ofNat 1)],
    [(5, Int.ofNat 1), (10, Int.negSucc 0), (17, Int.negSucc 1), (19, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 1), (26, Int.ofNat 1), (28, Int.ofNat 1), (29, Int.ofNat 1), (30, Int.negSucc 1), (31, Int.negSucc 0)],
    [(3, Int.negSucc 0), (8, Int.ofNat 1), (16, Int.negSucc 0), (19, Int.ofNat 1), (25, Int.ofNat 1), (27, Int.negSucc 0), (28, Int.ofNat 1), (30, Int.negSucc 0)],
    [(4, Int.ofNat 1), (10, Int.negSucc 0), (12, Int.ofNat 1), (17, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc 0), (31, Int.negSucc 0)],
    [(17, Int.ofNat 1), (30, Int.ofNat 1)],
    [(3, Int.ofNat 1), (4, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.ofNat 1), (13, Int.negSucc 0), (17, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (26, Int.ofNat 1), (32, Int.negSucc 0)],
    [(5, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.negSucc 0), (17, Int.ofNat 2), (19, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.ofNat 1), (28, Int.ofNat 2), (29, Int.negSucc 0), (30, Int.negSucc 0), (31, Int.negSucc 1), (32, Int.ofNat 2)],
    [(7, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.ofNat 1), (15, Int.negSucc 2), (17, Int.negSucc 1), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 2), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (30, Int.ofNat 3), (31, Int.ofNat 2), (32, Int.ofNat 3)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.ofNat 2), (14, Int.negSucc 2), (15, Int.ofNat 3), (18, Int.ofNat 3), (19, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 2), (27, Int.negSucc 1), (28, Int.ofNat 2), (29, Int.negSucc 1), (30, Int.ofNat 4), (31, Int.ofNat 1), (32, Int.negSucc 1)],
    [(8, Int.ofNat 1), (9, Int.ofNat 1), (14, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc 0), (31, Int.negSucc 2)],
    [(6, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 2), (25, Int.negSucc 0), (26, Int.negSucc 0), (28, Int.ofNat 2), (29, Int.ofNat 4), (30, Int.ofNat 1), (32, Int.negSucc 1)],
    [(21, Int.ofNat 2), (22, Int.ofNat 2), (23, Int.ofNat 2), (24, Int.ofNat 2), (25, Int.ofNat 2), (26, Int.ofNat 2), (27, Int.negSucc 1), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc 0), (31, Int.ofNat 2), (32, Int.ofNat 4)],
    [(6, Int.negSucc 0), (10, Int.negSucc 1), (11, Int.ofNat 2), (14, Int.negSucc 2), (18, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 2), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.negSucc 2), (28, Int.negSucc 0), (29, Int.negSucc 1), (30, Int.ofNat 1)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.ofNat 2), (10, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 2), (19, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 2), (27, Int.negSucc 1), (28, Int.negSucc 0), (29, Int.ofNat 1), (30, Int.negSucc 1), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(7, Int.ofNat 1), (9, Int.negSucc 1), (11, Int.negSucc 1), (17, Int.ofNat 2), (18, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 2), (21, Int.ofNat 2), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (28, Int.negSucc 2), (31, Int.ofNat 3), (32, Int.ofNat 2)],
    [(5, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.ofNat 1), (17, Int.negSucc 1), (18, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.negSucc 0), (25, Int.ofNat 1), (27, Int.ofNat 1), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc 1), (31, Int.negSucc 0)],
    [(0, Int.ofNat 1), (13, Int.ofNat 3), (16, Int.ofNat 3), (21, Int.negSucc 0), (22, Int.ofNat 2), (23, Int.ofNat 1), (24, Int.ofNat 2), (25, Int.ofNat 2), (26, Int.ofNat 1), (29, Int.negSucc 0), (31, Int.negSucc 2), (32, Int.ofNat 2)],
    [(5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (17, Int.ofNat 1), (20, Int.negSucc 0), (25, Int.ofNat 1), (26, Int.ofNat 3), (27, Int.negSucc 0), (28, Int.negSucc 0), (32, Int.ofNat 1)],
    [(6, Int.negSucc 0), (10, Int.negSucc 1), (11, Int.negSucc 0), (14, Int.ofNat 3), (18, Int.negSucc 1), (19, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.ofNat 2), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 1), (28, Int.negSucc 0), (29, Int.ofNat 1), (30, Int.ofNat 1), (31, Int.ofNat 1)],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (12, Int.negSucc 2), (13, Int.ofNat 3), (21, Int.ofNat 1), (22, Int.ofNat 2), (23, Int.ofNat 2), (24, Int.negSucc 0), (25, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.negSucc 2), (28, Int.negSucc 1), (29, Int.ofNat 3), (30, Int.negSucc 0), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(7, Int.negSucc 0), (8, Int.negSucc 0), (19, Int.negSucc 0), (21, Int.ofNat 3), (22, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (26, Int.ofNat 1), (27, Int.negSucc 0), (28, Int.ofNat 1), (30, Int.negSucc 0), (31, Int.ofNat 3), (32, Int.negSucc 0)],
    [(7, Int.ofNat 1), (9, Int.negSucc 1), (11, Int.ofNat 1), (18, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.ofNat 2), (26, Int.negSucc 0), (27, Int.negSucc 1), (29, Int.ofNat 3), (32, Int.ofNat 2)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.ofNat 2), (10, Int.ofNat 2), (14, Int.ofNat 3), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.ofNat 2), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.negSucc 0), (28, Int.negSucc 3), (29, Int.ofNat 1), (30, Int.negSucc 1), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(1, Int.ofNat 1), (12, Int.ofNat 3), (16, Int.negSucc 2), (21, Int.ofNat 2), (22, Int.ofNat 1), (23, Int.ofNat 2), (24, Int.ofNat 1), (25, Int.ofNat 2), (26, Int.ofNat 2), (27, Int.negSucc 0), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.negSucc 3), (31, Int.negSucc 2), (32, Int.negSucc 1)],
    [(5, Int.ofNat 1), (6, Int.ofNat 1), (8, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1), (24, Int.ofNat 3), (30, Int.ofNat 1), (31, Int.ofNat 1), (32, Int.negSucc 3)],
    [(5, Int.ofNat 1), (19, Int.negSucc 1), (20, Int.negSucc 1), (21, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 2), (28, Int.negSucc 0), (29, Int.negSucc 0), (30, Int.negSucc 0)],
    [(8, Int.ofNat 1), (11, Int.ofNat 1), (14, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (25, Int.ofNat 1), (27, Int.ofNat 1), (28, Int.ofNat 1), (29, Int.ofNat 1), (31, Int.negSucc 0)],
    [(5, Int.negSucc 0), (8, Int.negSucc 0), (11, Int.negSucc 0), (19, Int.negSucc 1), (20, Int.negSucc 0), (22, Int.ofNat 1), (24, Int.negSucc 0), (26, Int.ofNat 1), (27, Int.ofNat 3), (28, Int.ofNat 1), (29, Int.negSucc 0), (30, Int.ofNat 1)],
    [(2, Int.negSucc 0), (3, Int.ofNat 1), (5, Int.ofNat 1), (6, Int.negSucc 0), (17, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1), (26, Int.ofNat 1), (31, Int.negSucc 0), (32, Int.ofNat 1)],
    [(2, Int.ofNat 1), (4, Int.negSucc 0), (11, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (32, Int.negSucc 0)],
    [(3, Int.negSucc 0), (4, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.ofNat 1), (11, Int.negSucc 0), (13, Int.ofNat 1), (17, Int.negSucc 0), (18, Int.ofNat 1), (19, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.ofNat 1), (27, Int.ofNat 1), (30, Int.negSucc 0), (32, Int.negSucc 0)],
    [(19, Int.ofNat 1), (20, Int.ofNat 1), (27, Int.negSucc 0)]
  ],
  A := [
    [Int.ofNat 3024288, Int.ofNat 116208, Int.ofNat 29808, Int.ofNat 166320, Int.ofNat 117936, Int.ofNat 44496, Int.negSucc 132191, Int.ofNat 404784, Int.negSucc 148607, Int.negSucc 132623, Int.negSucc 98063, Int.negSucc 76031, Int.ofNat 114048, Int.negSucc 16847, Int.negSucc 30671, Int.ofNat 126144, Int.ofNat 111456, Int.negSucc 146015, Int.ofNat 120528, Int.negSucc 72575, Int.ofNat 96336, Int.ofNat 101952, Int.ofNat 77760, Int.negSucc 56591, Int.ofNat 80784, Int.ofNat 150768, Int.negSucc 89423, Int.ofNat 93312, Int.negSucc 150335, Int.ofNat 100224, Int.ofNat 113616, Int.negSucc 42335, Int.ofNat 336096],
    [Int.ofNat 116208, Int.ofNat 2958768, Int.negSucc 3023, Int.ofNat 118368, Int.negSucc 11231, Int.ofNat 16848, Int.ofNat 234576, Int.ofNat 224208, Int.negSucc 166751, Int.negSucc 71279, Int.ofNat 86832, Int.negSucc 167183, Int.ofNat 25920, Int.negSucc 34559, Int.negSucc 34127, Int.negSucc 17279, Int.ofNat 53136, Int.negSucc 89855, Int.ofNat 152928, Int.negSucc 32831, Int.ofNat 66960, Int.ofNat 54864, Int.negSucc 15983, Int.ofNat 35424, Int.negSucc 38015, Int.ofNat 84240, Int.ofNat 47088, Int.ofNat 79920, Int.negSucc 106703, Int.ofNat 74304, Int.ofNat 56592, Int.negSucc 33695, Int.ofNat 181872],
    [Int.ofNat 29808, Int.negSucc 3023, Int.ofNat 1523232, Int.ofNat 459648, Int.ofNat 347328, Int.ofNat 383616, Int.negSucc 306719, Int.negSucc 296351, Int.ofNat 344304, Int.ofNat 292896, Int.ofNat 355104, Int.negSucc 425087, Int.negSucc 19007, Int.negSucc 27647, Int.negSucc 78623, Int.negSucc 137375, Int.ofNat 5184, Int.negSucc 29807, Int.ofNat 447984, Int.negSucc 136511, Int.ofNat 124848, Int.ofNat 153360, Int.ofNat 32400, Int.negSucc 124415, Int.negSucc 139535, Int.ofNat 314064, Int.ofNat 130032, Int.negSucc 7343, Int.negSucc 132191, Int.negSucc 47087, Int.negSucc 62207, Int.ofNat 126576, Int.ofNat 382320],
    [Int.ofNat 166320, Int.ofNat 118368, Int.ofNat 459648, Int.ofNat 1675728, Int.ofNat 98064, Int.negSucc 358127, Int.ofNat 346032, Int.ofNat 581472, Int.ofNat 493344, Int.negSucc 113183, Int.negSucc 54431, Int.negSucc 181439, Int.negSucc 108431, Int.ofNat 297648, Int.ofNat 60048, Int.ofNat 22464, Int.negSucc 403919, Int.ofNat 31968, Int.ofNat 154656, Int.negSucc 161567, Int.ofNat 204768, Int.ofNat 165456, Int.negSucc 85103, Int.negSucc 193103, Int.ofNat 135216, Int.ofNat 418176, Int.negSucc 194399, Int.ofNat 53136, Int.ofNat 155952, Int.negSucc 125279, Int.negSucc 55295, Int.ofNat 270864, Int.ofNat 299376],
    [Int.ofNat 117936, Int.negSucc 11231, Int.ofNat 347328, Int.ofNat 98064, Int.ofNat 1510272, Int.ofNat 107136, Int.negSucc 351647, Int.ofNat 399600, Int.negSucc 211679, Int.negSucc 296351, Int.ofNat 433728, Int.ofNat 96336, Int.negSucc 509327, Int.negSucc 333935, Int.ofNat 33264, Int.negSucc 154223, Int.negSucc 172367, Int.ofNat 95904, Int.negSucc 284255, Int.negSucc 47087, Int.negSucc 168479, Int.negSucc 120095, Int.ofNat 60480, Int.negSucc 101087, Int.negSucc 151631, Int.negSucc 121391, Int.negSucc 33263, Int.negSucc 257039, Int.ofNat 18576, Int.negSucc 47519, Int.negSucc 15119, Int.negSucc 121823, Int.negSucc 249695],
    [Int.ofNat 44496, Int.ofNat 16848, Int.ofNat 383616, Int.negSucc 358127, Int.ofNat 107136, Int.ofNat 1595808, Int.ofNat 750492, Int.negSucc 179279, Int.negSucc 240623, Int.ofNat 248832, Int.ofNat 263520, Int.negSucc 158111, Int.ofNat 52272, Int.ofNat 120528, Int.negSucc 24623, Int.negSucc 111023, Int.negSucc 47087, Int.negSucc 45791, Int.ofNat 48384, Int.ofNat 67392, Int.negSucc 12959, Int.negSucc 82079, Int.negSucc 531359, Int.ofNat 441072, Int.negSucc 356831, Int.ofNat 161568, Int.ofNat 427248, Int.ofNat 68256, Int.negSucc 22895, Int.negSucc 78623, Int.ofNat 92448, Int.ofNat 21168, Int.ofNat 864],
    [Int.negSucc 132191, Int.ofNat 234576, Int.negSucc 306719, Int.ofNat 346032, Int.negSucc 351647, Int.ofNat 750492, Int.ofNat 2477736, Int.ofNat 104976, Int.ofNat 263952, Int.negSucc 86399, Int.ofNat 205200, Int.negSucc 40607, Int.negSucc 159407, Int.negSucc 168911, Int.negSucc 16415, Int.ofNat 114048, Int.ofNat 10800, Int.negSucc 3455, Int.ofNat 79920, Int.negSucc 324431, Int.ofNat 121824, Int.ofNat 98928, Int.negSucc 123119, Int.ofNat 115776, Int.negSucc 332639, Int.ofNat 57024, Int.ofNat 186192, Int.negSucc 185759, Int.ofNat 23328, Int.ofNat 864, Int.negSucc 74735, Int.ofNat 82512, Int.ofNat 455760],
    [Int.ofNat 404784, Int.ofNat 224208, Int.negSucc 296351, Int.ofNat 581472, Int.ofNat 399600, Int.negSucc 179279, Int.ofNat 104976, Int.ofNat 2337984, Int.negSucc 17279, Int.ofNat 304992, Int.negSucc 9071, Int.ofNat 62640, Int.ofNat 268704, Int.negSucc 46223, Int.negSucc 71279, Int.ofNat 94176, Int.ofNat 313200, Int.negSucc 135647, Int.ofNat 6048, Int.ofNat 129600, Int.negSucc 44495, Int.ofNat 398736, Int.negSucc 194831, Int.negSucc 194399, Int.negSucc 128735, Int.ofNat 484272, Int.negSucc 194831, Int.ofNat 123120, Int.negSucc 199151, Int.ofNat 29808, Int.ofNat 149472, Int.negSucc 94175, Int.ofNat 87696],
    [Int.negSucc 148607, Int.negSucc 166751, Int.ofNat 344304, Int.ofNat 493344, Int.negSucc 211679, Int.negSucc 240623, Int.ofNat 263952, Int.negSucc 17279, Int.ofNat 1242000, Int.negSucc 198719, Int.ofNat 110160, Int.negSucc 177119, Int.ofNat 106704, Int.negSucc 177551, Int.negSucc 23759, Int.negSucc 3887, Int.ofNat 273024, Int.negSucc 63935, Int.ofNat 152496, Int.negSucc 108863, Int.ofNat 118800, Int.negSucc 301103, Int.ofNat 89856, Int.ofNat 414288, Int.ofNat 32400, Int.negSucc 311903, Int.ofNat 390528, Int.ofNat 45792, Int.negSucc 66095, Int.ofNat 109728, Int.ofNat 28944, Int.ofNat 3024, Int.ofNat 235440],
    [Int.negSucc 132623, Int.negSucc 71279, Int.ofNat 292896, Int.negSucc 113183, Int.negSucc 296351, Int.ofNat 248832, Int.negSucc 86399, Int.ofNat 304992, Int.negSucc 198719, Int.ofNat 1528848, Int.negSucc 84239, Int.ofNat 20736, Int.negSucc 103247, Int.negSucc 42767, Int.negSucc 190511, Int.negSucc 21599, Int.negSucc 60479, Int.ofNat 111456, Int.ofNat 209520, Int.negSucc 114047, Int.ofNat 203472, Int.negSucc 127007, Int.ofNat 187488, Int.ofNat 80784, Int.ofNat 262656, Int.negSucc 107999, Int.ofNat 24624, Int.ofNat 60480, Int.ofNat 225072, Int.negSucc 25487, Int.negSucc 141695, Int.ofNat 291600, Int.ofNat 114480],
    [Int.negSucc 98063, Int.ofNat 86832, Int.ofNat 355104, Int.negSucc 54431, Int.ofNat 433728, Int.ofNat 263520, Int.ofNat 205200, Int.negSucc 9071, Int.ofNat 110160, Int.negSucc 84239, Int.ofNat 1290816, Int.ofNat 139968, Int.ofNat 294624, Int.ofNat 119664, Int.negSucc 100223, Int.ofNat 72144, Int.ofNat 160704, Int.negSucc 50543, Int.negSucc 326591, Int.negSucc 249263, Int.ofNat 214272, Int.ofNat 37584, Int.ofNat 55728, Int.ofNat 44064, Int.ofNat 178416, Int.negSucc 43199, Int.negSucc 149039, Int.ofNat 37584, Int.ofNat 101520, Int.ofNat 107136, Int.ofNat 21168, Int.ofNat 60912, Int.ofNat 376704],
    [Int.negSucc 76031, Int.negSucc 167183, Int.negSucc 425087, Int.negSucc 181439, Int.ofNat 96336, Int.negSucc 158111, Int.negSucc 40607, Int.ofNat 62640, Int.negSucc 177119, Int.ofNat 20736, Int.ofNat 139968, Int.ofNat 1451952, Int.negSucc 106271, Int.ofNat 68688, Int.ofNat 308448, Int.ofNat 132624, Int.negSucc 170207, Int.ofNat 118800, Int.ofNat 250128, Int.ofNat 4320, Int.ofNat 270864, Int.negSucc 14255, Int.ofNat 83376, Int.ofNat 92880, Int.ofNat 147744, Int.ofNat 32832, Int.ofNat 204336, Int.ofNat 213408, Int.ofNat 37584, Int.ofNat 76896, Int.negSucc 163295, Int.ofNat 226368, Int.ofNat 25056],
    [Int.ofNat 114048, Int.ofNat 25920, Int.negSucc 19007, Int.negSucc 108431, Int.negSucc 509327, Int.ofNat 52272, Int.negSucc 159407, Int.ofNat 268704, Int.ofNat 106704, Int.negSucc 103247, Int.ofNat 294624, Int.negSucc 106271, Int.ofNat 2413152, Int.negSucc 64367, Int.ofNat 5184, Int.negSucc 95471, Int.negSucc 150335, Int.ofNat 35856, Int.ofNat 12528, Int.negSucc 106703, Int.ofNat 432, Int.ofNat 21600, Int.ofNat 32400, Int.negSucc 129599, Int.negSucc 72575, Int.ofNat 92736, Int.negSucc 45791, Int.negSucc 118367, Int.ofNat 3456, Int.negSucc 53999, Int.negSucc 23759, Int.ofNat 28512, Int.ofNat 69552],
    [Int.negSucc 16847, Int.negSucc 34559, Int.negSucc 27647, Int.ofNat 297648, Int.negSucc 333935, Int.ofNat 120528, Int.negSucc 168911, Int.negSucc 46223, Int.negSucc 177551, Int.negSucc 42767, Int.ofNat 119664, Int.ofNat 68688, Int.negSucc 64367, Int.ofNat 2538432, Int.ofNat 1728, Int.negSucc 46223, Int.ofNat 25920, Int.ofNat 22032, Int.negSucc 108863, Int.ofNat 26784, Int.negSucc 92015, Int.negSucc 70847, Int.ofNat 16416, Int.ofNat 24624, Int.negSucc 77327, Int.negSucc 136943, Int.ofNat 47088, Int.negSucc 80351, Int.negSucc 17279, Int.ofNat 6480, Int.ofNat 1296, Int.negSucc 87263, Int.negSucc 141695],
    [Int.negSucc 30671, Int.negSucc 34127, Int.negSucc 78623, Int.ofNat 60048, Int.ofNat 33264, Int.negSucc 24623, Int.negSucc 16415, Int.negSucc 71279, Int.negSucc 23759, Int.negSucc 190511, Int.negSucc 100223, Int.ofNat 308448, Int.ofNat 5184, Int.ofNat 1728, Int.ofNat 1640520, Int.ofNat 33480, Int.ofNat 19872, Int.negSucc 17711, Int.ofNat 296352, Int.ofNat 83376, Int.negSucc 43631, Int.negSucc 85103, Int.negSucc 198071, Int.negSucc 72575, Int.ofNat 120960, Int.negSucc 68687, Int.ofNat 65232, Int.negSucc 140615, Int.ofNat 181008, Int.negSucc 192239, Int.ofNat 66528, Int.ofNat 33264, Int.negSucc 171503],
    [Int.ofNat 126144, Int.negSucc 17279, Int.negSucc 137375, Int.ofNat 22464, Int.negSucc 154223, Int.negSucc 111023, Int.ofNat 114048, Int.ofNat 94176, Int.negSucc 3887, Int.negSucc 21599, Int.ofNat 72144, Int.ofNat 132624, Int.negSucc 95471, Int.negSucc 46223, Int.ofNat 33480, Int.ofNat 1608768, Int.negSucc 68687, Int.negSucc 133919, Int.negSucc 132623, Int.negSucc 124847, Int.ofNat 160272, Int.ofNat 138240, Int.negSucc 29807, Int.ofNat 145584, Int.ofNat 72576, Int.ofNat 215136, Int.negSucc 40175, Int.ofNat 111888, Int.negSucc 98927, Int.ofNat 63936, Int.ofNat 103680, Int.ofNat 116208, Int.ofNat 634608],
    [Int.ofNat 111456, Int.ofNat 53136, Int.ofNat 5184, Int.negSucc 403919, Int.negSucc 172367, Int.negSucc 47087, Int.ofNat 10800, Int.ofNat 313200, Int.ofNat 273024, Int.negSucc 60479, Int.ofNat 160704, Int.negSucc 170207, Int.negSucc 150335, Int.ofNat 25920, Int.ofNat 19872, Int.negSucc 68687, Int.ofNat 2453760, Int.ofNat 43632, Int.ofNat 117936, Int.negSucc 121823, Int.ofNat 85968, Int.ofNat 105408, Int.negSucc 36719, Int.negSucc 140399, Int.negSucc 34559, Int.ofNat 249264, Int.negSucc 60047, Int.negSucc 44927, Int.ofNat 56592, Int.negSucc 82943, Int.negSucc 60047, Int.ofNat 134352, Int.ofNat 157248],
    [Int.negSucc 146015, Int.negSucc 89855, Int.negSucc 29807, Int.ofNat 31968, Int.ofNat 95904, Int.negSucc 45791, Int.negSucc 3455, Int.negSucc 135647, Int.negSucc 63935, Int.ofNat 111456, Int.negSucc 50543, Int.ofNat 118800, Int.ofNat 35856, Int.ofNat 22032, Int.negSucc 17711, Int.negSucc 133919, Int.ofNat 43632, Int.ofNat 507168, Int.negSucc 147743, Int.negSucc 33263, Int.ofNat 11232, Int.negSucc 127439, Int.ofNat 83376, Int.negSucc 35855, Int.negSucc 69551, Int.negSucc 206927, Int.ofNat 174528, Int.negSucc 156383, Int.ofNat 178632, Int.negSucc 156815, Int.negSucc 460079, Int.ofNat 242784, Int.negSucc 431135],
    [Int.ofNat 120528, Int.ofNat 152928, Int.ofNat 447984, Int.ofNat 154656, Int.negSucc 284255, Int.ofNat 48384, Int.ofNat 79920, Int.ofNat 6048, Int.ofNat 152496, Int.ofNat 209520, Int.negSucc 326591, Int.ofNat 250128, Int.ofNat 12528, Int.negSucc 108863, Int.ofNat 296352, Int.negSucc 132623, Int.ofNat 117936, Int.negSucc 147743, Int.ofNat 1363392, Int.ofNat 34560, Int.negSucc 109727, Int.ofNat 159840, Int.ofNat 25920, Int.negSucc 137807, Int.negSucc 226367, Int.negSucc 21167, Int.negSucc 9503, Int.negSucc 61343, Int.negSucc 120095, Int.ofNat 5184, Int.negSucc 6479, Int.negSucc 82511, Int.ofNat 148608],
    [Int.negSucc 72575, Int.negSucc 32831, Int.negSucc 136511, Int.negSucc 161567, Int.negSucc 47087, Int.ofNat 67392, Int.negSucc 324431, Int.ofNat 129600, Int.negSucc 108863, Int.negSucc 114047, Int.negSucc 249263, Int.ofNat 4320, Int.negSucc 106703, Int.ofNat 26784, Int.ofNat 83376, Int.negSucc 124847, Int.negSucc 121823, Int.negSucc 33263, Int.ofNat 34560, Int.ofNat 603072, Int.negSucc 243215, Int.negSucc 101951, Int.negSucc 17711, Int.negSucc 43199, Int.ofNat 182304, Int.negSucc 6047, Int.ofNat 101520, Int.ofNat 278640, Int.negSucc 175391, Int.negSucc 88991, Int.ofNat 69120, Int.negSucc 88559, Int.negSucc 599615],
    [Int.ofNat 96336, Int.ofNat 66960, Int.ofNat 124848, Int.ofNat 204768, Int.negSucc 168479, Int.negSucc 12959, Int.ofNat 121824, Int.negSucc 44495, Int.ofNat 118800, Int.ofNat 203472, Int.ofNat 214272, Int.ofNat 270864, Int.ofNat 432, Int.negSucc 92015, Int.negSucc 43631, Int.ofNat 160272, Int.ofNat 85968, Int.ofNat 11232, Int.negSucc 109727, Int.negSucc 243215, Int.ofNat 514080, Int.ofNat 156816, Int.negSucc 54863, Int.ofNat 100656, Int.ofNat 106272, Int.ofNat 258336, Int.ofNat 96336, Int.ofNat 279504, Int.ofNat 37152, Int.ofNat 181872, Int.negSucc 85967, Int.ofNat 273024, Int.ofNat 501984],
    [Int.ofNat 101952, Int.ofNat 54864, Int.ofNat 153360, Int.ofNat 165456, Int.negSucc 120095, Int.negSucc 82079, Int.ofNat 98928, Int.ofNat 398736, Int.negSucc 301103, Int.negSucc 127007, Int.ofNat 37584, Int.negSucc 14255, Int.ofNat 21600, Int.negSucc 70847, Int.negSucc 85103, Int.ofNat 138240, Int.ofNat 105408, Int.negSucc 127439, Int.ofNat 159840, Int.negSucc 101951, Int.ofNat 156816, Int.ofNat 1449360, Int.negSucc 371951, Int.negSucc 350783, Int.negSucc 625535, Int.ofNat 897264, Int.negSucc 557711, Int.ofNat 83376, Int.negSucc 77759, Int.ofNat 412128, Int.ofNat 31536, Int.negSucc 121391, Int.ofNat 219888],
    [Int.ofNat 77760, Int.negSucc 15983, Int.ofNat 32400, Int.negSucc 85103, Int.ofNat 60480, Int.negSucc 531359, Int.negSucc 123119, Int.negSucc 194831, Int.ofNat 89856, Int.ofNat 187488, Int.ofNat 55728, Int.ofNat 83376, Int.ofNat 32400, Int.ofNat 16416, Int.negSucc 198071, Int.negSucc 29807, Int.negSucc 36719, Int.ofNat 83376, Int.ofNat 25920, Int.negSucc 17711, Int.negSucc 54863, Int.negSucc 371951, Int.ofNat 1213488, Int.negSucc 357695, Int.ofNat 616464, Int.negSucc 394415, Int.negSucc 288575, Int.negSucc 122687, Int.negSucc 213407, Int.ofNat 145152, Int.negSucc 63071, Int.negSucc 42335, Int.negSucc 54863],
    [Int.negSucc 56591, Int.ofNat 35424, Int.negSucc 124415, Int.negSucc 193103, Int.negSucc 101087, Int.ofNat 441072, Int.ofNat 115776, Int.negSucc 194399, Int.ofNat 414288, Int.ofNat 80784, Int.ofNat 44064, Int.ofNat 92880, Int.negSucc 129599, Int.ofNat 24624, Int.negSucc 72575, Int.ofNat 145584, Int.negSucc 140399, Int.negSucc 35855, Int.negSucc 137807, Int.negSucc 43199, Int.ofNat 100656, Int.negSucc 350783, Int.negSucc 357695, Int.ofNat 1288656, Int.negSucc 254879, Int.negSucc 428543, Int.ofNat 715824, Int.ofNat 46224, Int.ofNat 199584, Int.ofNat 182304, Int.ofNat 156384, Int.ofNat 91152, Int.ofNat 13824],
    [Int.ofNat 80784, Int.negSucc 38015, Int.negSucc 139535, Int.ofNat 135216, Int.negSucc 151631, Int.negSucc 356831, Int.negSucc 332639, Int.negSucc 128735, Int.ofNat 32400, Int.ofNat 262656, Int.ofNat 178416, Int.ofNat 147744, Int.negSucc 72575, Int.negSucc 77327, Int.ofNat 120960, Int.ofNat 72576, Int.negSucc 34559, Int.negSucc 69551, Int.negSucc 226367, Int.ofNat 182304, Int.ofNat 106272, Int.negSucc 625535, Int.ofNat 616464, Int.negSucc 254879, Int.ofNat 1367280, Int.negSucc 89855, Int.negSucc 290735, Int.ofNat 257040, Int.ofNat 46656, Int.negSucc 200879, Int.ofNat 222480, Int.ofNat 219888, Int.ofNat 60480],
    [Int.ofNat 150768, Int.ofNat 84240, Int.ofNat 314064, Int.ofNat 418176, Int.negSucc 121391, Int.ofNat 161568, Int.ofNat 57024, Int.ofNat 484272, Int.negSucc 311903, Int.negSucc 107999, Int.negSucc 43199, Int.ofNat 32832, Int.ofNat 92736, Int.negSucc 136943, Int.negSucc 68687, Int.ofNat 215136, Int.ofNat 249264, Int.negSucc 206927, Int.negSucc 21167, Int.negSucc 6047, Int.ofNat 258336, Int.ofNat 897264, Int.negSucc 394415, Int.negSucc 428543, Int.negSucc 89855, Int.ofNat 1747440, Int.negSucc 378431, Int.ofNat 336528, Int.negSucc 377999, Int.negSucc 8207, Int.ofNat 319680, Int.ofNat 169344, Int.ofNat 625536],
    [Int.negSucc 89423, Int.ofNat 47088, Int.ofNat 130032, Int.negSucc 194399, Int.negSucc 33263, Int.ofNat 427248, Int.ofNat 186192, Int.negSucc 194831, Int.ofNat 390528, Int.ofNat 24624, Int.negSucc 149039, Int.ofNat 204336, Int.negSucc 45791, Int.ofNat 47088, Int.ofNat 65232, Int.negSucc 40175, Int.negSucc 60047, Int.ofNat 174528, Int.negSucc 9503, Int.ofNat 101520, Int.ofNat 96336, Int.negSucc 557711, Int.negSucc 288575, Int.ofNat 715824, Int.negSucc 290735, Int.negSucc 378431, Int.ofNat 1248912, Int.ofNat 106704, Int.negSucc 112319, Int.negSucc 136511, Int.negSucc 231983, Int.ofNat 206496, Int.negSucc 69119],
    [Int.ofNat 93312, Int.ofNat 79920, Int.negSucc 7343, Int.ofNat 53136, Int.negSucc 257039, Int.ofNat 68256, Int.negSucc 185759, Int.ofNat 123120, Int.ofNat 45792, Int.ofNat 60480, Int.ofNat 37584, Int.ofNat 213408, Int.negSucc 118367, Int.negSucc 80351, Int.negSucc 140615, Int.ofNat 111888, Int.negSucc 44927, Int.negSucc 156383, Int.negSucc 61343, Int.ofNat 278640, Int.ofNat 279504, Int.ofNat 83376, Int.negSucc 122687, Int.ofNat 46224, Int.ofNat 257040, Int.ofNat 336528, Int.ofNat 106704, Int.ofNat 693792, Int.negSucc 235439, Int.ofNat 146448, Int.ofNat 73440, Int.ofNat 79488, Int.ofNat 144720],
    [Int.negSucc 150335, Int.negSucc 106703, Int.negSucc 132191, Int.ofNat 155952, Int.ofNat 18576, Int.negSucc 22895, Int.ofNat 23328, Int.negSucc 199151, Int.negSucc 66095, Int.ofNat 225072, Int.ofNat 101520, Int.ofNat 37584, Int.ofNat 3456, Int.negSucc 17279, Int.ofNat 181008, Int.negSucc 98927, Int.ofNat 56592, Int.ofNat 178632, Int.negSucc 120095, Int.negSucc 175391, Int.ofNat 37152, Int.negSucc 77759, Int.negSucc 213407, Int.ofNat 199584, Int.ofNat 46656, Int.negSucc 377999, Int.negSucc 112319, Int.negSucc 235439, Int.ofNat 783216, Int.negSucc 172799, Int.negSucc 172367, Int.ofNat 276912, Int.negSucc 281663],
    [Int.ofNat 100224, Int.ofNat 74304, Int.negSucc 47087, Int.negSucc 125279, Int.negSucc 47519, Int.negSucc 78623, Int.ofNat 864, Int.ofNat 29808, Int.ofNat 109728, Int.negSucc 25487, Int.ofNat 107136, Int.ofNat 76896, Int.negSucc 53999, Int.ofNat 6480, Int.negSucc 192239, Int.ofNat 63936, Int.negSucc 82943, Int.negSucc 156815, Int.ofNat 5184, Int.negSucc 88991, Int.ofNat 181872, Int.ofNat 412128, Int.ofNat 145152, Int.ofNat 182304, Int.negSucc 200879, Int.negSucc 8207, Int.negSucc 136511, Int.ofNat 146448, Int.negSucc 172799, Int.ofNat 616464, Int.ofNat 124848, Int.negSucc 246239, Int.ofNat 124416],
    [Int.ofNat 113616, Int.ofNat 56592, Int.negSucc 62207, Int.negSucc 55295, Int.negSucc 15119, Int.ofNat 92448, Int.negSucc 74735, Int.ofNat 149472, Int.ofNat 28944, Int.negSucc 141695, Int.ofNat 21168, Int.negSucc 163295, Int.negSucc 23759, Int.ofNat 1296, Int.ofNat 66528, Int.ofNat 103680, Int.negSucc 60047, Int.negSucc 460079, Int.negSucc 6479, Int.ofNat 69120, Int.negSucc 85967, Int.ofNat 31536, Int.negSucc 63071, Int.ofNat 156384, Int.ofNat 222480, Int.ofNat 319680, Int.negSucc 231983, Int.ofNat 73440, Int.negSucc 172367, Int.ofNat 124848, Int.ofNat 669600, Int.negSucc 250559, Int.ofNat 279504],
    [Int.negSucc 42335, Int.negSucc 33695, Int.ofNat 126576, Int.ofNat 270864, Int.negSucc 121823, Int.ofNat 21168, Int.ofNat 82512, Int.negSucc 94175, Int.ofNat 3024, Int.ofNat 291600, Int.ofNat 60912, Int.ofNat 226368, Int.ofNat 28512, Int.negSucc 87263, Int.ofNat 33264, Int.ofNat 116208, Int.ofNat 134352, Int.ofNat 242784, Int.negSucc 82511, Int.negSucc 88559, Int.ofNat 273024, Int.negSucc 121391, Int.negSucc 42335, Int.ofNat 91152, Int.ofNat 219888, Int.ofNat 169344, Int.ofNat 206496, Int.ofNat 79488, Int.ofNat 276912, Int.negSucc 246239, Int.negSucc 250559, Int.ofNat 551664, Int.ofNat 157248],
    [Int.ofNat 336096, Int.ofNat 181872, Int.ofNat 382320, Int.ofNat 299376, Int.negSucc 249695, Int.ofNat 864, Int.ofNat 455760, Int.ofNat 87696, Int.ofNat 235440, Int.ofNat 114480, Int.ofNat 376704, Int.ofNat 25056, Int.ofNat 69552, Int.negSucc 141695, Int.negSucc 171503, Int.ofNat 634608, Int.ofNat 157248, Int.negSucc 431135, Int.ofNat 148608, Int.negSucc 599615, Int.ofNat 501984, Int.ofNat 219888, Int.negSucc 54863, Int.ofNat 13824, Int.ofNat 60480, Int.ofNat 625536, Int.negSucc 69119, Int.ofNat 144720, Int.negSucc 281663, Int.ofNat 124416, Int.ofNat 279504, Int.ofNat 157248, Int.ofNat 1667088]
  ],
  W := [
    [Int.ofNat 6949],
    [Int.ofNat 268, Int.ofNat 6868],
    [Int.ofNat 69, Int.negSucc 9, Int.ofNat 4926],
    [Int.ofNat 383, Int.ofNat 261, Int.ofNat 1488, Int.ofNat 4927],
    [Int.ofNat 272, Int.negSucc 36, Int.ofNat 1124, Int.negSucc 39, Int.ofNat 4766],
    [Int.ofNat 102, Int.ofNat 35, Int.ofNat 1245, Int.negSucc 1548, Int.ofNat 47, Int.ofNat 4633],
    [Int.negSucc 303, Int.ofNat 558, Int.negSucc 990, Int.ofNat 1417, Int.negSucc 912, Int.ofNat 3344, Int.ofNat 4912],
    [Int.ofNat 932, Int.ofNat 486, Int.negSucc 974, Int.ofNat 2084, Int.ofNat 1540, Int.ofNat 299, Int.negSucc 370, Int.ofNat 5320],
    [Int.negSucc 341, Int.negSucc 374, Int.ofNat 1122, Int.ofNat 1309, Int.negSucc 947, Int.negSucc 674, Int.ofNat 1013, Int.ofNat 118, Int.ofNat 3760],
    [Int.negSucc 304, Int.negSucc 153, Int.ofNat 955, Int.negSucc 623, Int.negSucc 1208, Int.ofNat 414, Int.negSucc 416, Int.ofNat 1702, Int.negSucc 1127, Int.ofNat 4118],
    [Int.negSucc 225, Int.ofNat 211, Int.ofNat 1157, Int.negSucc 519, Int.ofNat 1193, Int.ofNat 417, Int.ofNat 952, Int.ofNat 106, Int.ofNat 421, Int.negSucc 206, Int.ofNat 4014],
    [Int.negSucc 174, Int.negSucc 382, Int.negSucc 1378, Int.negSucc 138, Int.ofNat 655, Int.negSucc 221, Int.negSucc 64, Int.negSucc 125, Int.negSucc 200, Int.ofNat 557, Int.ofNat 845, Int.ofNat 4412],
    [Int.ofNat 263, Int.ofNat 50, Int.negSucc 64, Int.negSucc 354, Int.negSucc 1711, Int.ofNat 91, Int.negSucc 798, Int.ofNat 1319, Int.ofNat 385, Int.negSucc 1450, Int.ofNat 1698, Int.negSucc 241, Int.ofNat 5272],
    [Int.negSucc 38, Int.negSucc 78, Int.negSucc 88, Int.ofNat 1001, Int.negSucc 1089, Int.ofNat 787, Int.negSucc 1588, Int.negSucc 372, Int.negSucc 781, Int.negSucc 619, Int.ofNat 1313, Int.ofNat 202, Int.negSucc 1167, Int.ofNat 5558],
    [Int.negSucc 70, Int.negSucc 76, Int.negSucc 254, Int.ofNat 281, Int.ofNat 178, Int.ofNat 78, Int.negSucc 201, Int.negSucc 421, Int.negSucc 10, Int.negSucc 450, Int.negSucc 313, Int.ofNat 1118, Int.ofNat 196, Int.negSucc 90, Int.ofNat 4913],
    [Int.ofNat 290, Int.negSucc 51, Int.negSucc 449, Int.ofNat 189, Int.negSucc 426, Int.negSucc 200, Int.ofNat 307, Int.ofNat 237, Int.negSucc 159, Int.negSucc 146, Int.ofNat 539, Int.ofNat 326, Int.negSucc 631, Int.negSucc 434, Int.ofNat 93, Int.ofNat 4888],
    [Int.ofNat 257, Int.ofNat 114, Int.ofNat 13, Int.negSucc 1341, Int.negSucc 606, Int.negSucc 614, Int.ofNat 734, Int.ofNat 1676, Int.ofNat 1146, Int.negSucc 838, Int.ofNat 334, Int.negSucc 422, Int.negSucc 1496, Int.ofNat 300, Int.ofNat 462, Int.negSucc 562, Int.ofNat 5293],
    [Int.negSucc 335, Int.negSucc 195, Int.negSucc 92, Int.ofNat 168, Int.ofNat 363, Int.negSucc 71, Int.ofNat 39, Int.negSucc 511, Int.negSucc 268, Int.ofNat 703, Int.negSucc 192, Int.ofNat 241, Int.ofNat 677, Int.ofNat 304, Int.negSucc 158, Int.negSucc 248, Int.ofNat 748, Int.ofNat 2358],
    [Int.ofNat 278, Int.ofNat 345, Int.ofNat 1452, Int.ofNat 24, Int.negSucc 1309, Int.negSucc 209, Int.ofNat 424, Int.ofNat 615, Int.negSucc 233, Int.negSucc 124, Int.negSucc 1407, Int.ofNat 1885, Int.ofNat 52, Int.negSucc 123, Int.ofNat 634, Int.negSucc 491, Int.ofNat 94, Int.negSucc 892, Int.ofNat 3164],
    [Int.negSucc 166, Int.negSucc 69, Int.negSucc 440, Int.negSucc 374, Int.negSucc 47, Int.ofNat 231, Int.negSucc 1205, Int.ofNat 408, Int.ofNat 118, Int.negSucc 707, Int.negSucc 703, Int.ofNat 95, Int.negSucc 622, Int.negSucc 253, Int.ofNat 139, Int.negSucc 415, Int.negSucc 696, Int.ofNat 433, Int.ofNat 142, Int.ofNat 2267],
    [Int.ofNat 222, Int.ofNat 147, Int.ofNat 403, Int.ofNat 518, Int.negSucc 667, Int.ofNat 21, Int.ofNat 187, Int.negSucc 109, Int.ofNat 28, Int.ofNat 672, Int.ofNat 997, Int.ofNat 971, Int.negSucc 225, Int.negSucc 674, Int.negSucc 221, Int.ofNat 228, Int.ofNat 444, Int.negSucc 19, Int.negSucc 1125, Int.negSucc 822, Int.ofNat 1409],
    [Int.ofNat 235, Int.ofNat 119, Int.ofNat 495, Int.ofNat 363, Int.negSucc 528, Int.negSucc 295, Int.ofNat 421, Int.ofNat 1295, Int.negSucc 1862, Int.negSucc 1659, Int.ofNat 224, Int.ofNat 323, Int.negSucc 721, Int.negSucc 775, Int.negSucc 315, Int.ofNat 10, Int.negSucc 147, Int.ofNat 121, Int.negSucc 212, Int.negSucc 1216, Int.ofNat 331, Int.ofNat 3338],
    [Int.ofNat 179, Int.negSucc 43, Int.ofNat 103, Int.negSucc 318, Int.ofNat 166, Int.negSucc 1974, Int.ofNat 1103, Int.negSucc 328, Int.negSucc 124, Int.ofNat 1129, Int.ofNat 138, Int.ofNat 36, Int.ofNat 684, Int.ofNat 930, Int.negSucc 482, Int.negSucc 13, Int.negSucc 76, Int.negSucc 230, Int.ofNat 61, Int.ofNat 1440, Int.ofNat 112, Int.negSucc 613, Int.ofNat 2917],
    [Int.negSucc 129, Int.ofNat 88, Int.negSucc 401, Int.negSucc 499, Int.negSucc 240, Int.ofNat 1469, Int.negSucc 621, Int.negSucc 503, Int.ofNat 2440, Int.ofNat 920, Int.ofNat 87, Int.ofNat 262, Int.negSucc 438, Int.ofNat 12, Int.negSucc 258, Int.ofNat 600, Int.negSucc 561, Int.ofNat 81, Int.negSucc 34, Int.negSucc 870, Int.ofNat 70, Int.ofNat 120, Int.negSucc 561, Int.ofNat 2882],
    [Int.ofNat 186, Int.negSucc 95, Int.negSucc 455, Int.ofNat 567, Int.negSucc 407, Int.negSucc 918, Int.negSucc 766, Int.negSucc 600, Int.ofNat 41, Int.ofNat 1377, Int.ofNat 1413, Int.negSucc 46, Int.negSucc 359, Int.negSucc 789, Int.ofNat 512, Int.negSucc 70, Int.ofNat 184, Int.negSucc 705, Int.negSucc 585, Int.ofNat 1952, Int.negSucc 379, Int.negSucc 1667, Int.ofNat 1554, Int.negSucc 688, Int.ofNat 1954],
    [Int.ofNat 347, Int.ofNat 183, Int.ofNat 1016, Int.ofNat 1014, Int.negSucc 656, Int.ofNat 622, Int.negSucc 446, Int.ofNat 1291, Int.negSucc 1907, Int.negSucc 1825, Int.negSucc 15, Int.ofNat 804, Int.negSucc 592, Int.negSucc 1435, Int.negSucc 473, Int.ofNat 309, Int.ofNat 814, Int.negSucc 622, Int.negSucc 1854, Int.negSucc 455, Int.negSucc 520, Int.ofNat 784, Int.ofNat 223, Int.negSucc 319, Int.ofNat 239, Int.ofNat 2609],
    [Int.negSucc 205, Int.ofNat 118, Int.ofNat 425, Int.negSucc 749, Int.negSucc 205, Int.ofNat 1116, Int.ofNat 85, Int.negSucc 185, Int.ofNat 1920, Int.ofNat 311, Int.negSucc 1086, Int.ofNat 1191, Int.ofNat 149, Int.ofNat 640, Int.negSucc 47, Int.ofNat 172, Int.negSucc 385, Int.ofNat 1186, Int.negSucc 851, Int.ofNat 89, Int.ofNat 694, Int.negSucc 1306, Int.negSucc 1442, Int.ofNat 1133, Int.negSucc 33, Int.negSucc 170, Int.ofNat 1738],
    [Int.ofNat 215, Int.ofNat 178, Int.negSucc 25, Int.ofNat 154, Int.negSucc 865, Int.ofNat 297, Int.negSucc 1024, Int.ofNat 413, Int.ofNat 284, Int.negSucc 193, Int.ofNat 599, Int.ofNat 857, Int.negSucc 1134, Int.negSucc 1125, Int.negSucc 591, Int.negSucc 26, Int.negSucc 433, Int.negSucc 160, Int.negSucc 792, Int.ofNat 954, Int.ofNat 1146, Int.negSucc 229, Int.ofNat 22, Int.negSucc 394, Int.negSucc 405, Int.ofNat 119, Int.ofNat 100, Int.ofNat 1118],
    [Int.negSucc 345, Int.negSucc 234, Int.negSucc 424, Int.ofNat 674, Int.ofNat 186, Int.ofNat 268, Int.negSucc 346, Int.negSucc 951, Int.negSucc 225, Int.ofNat 1365, Int.ofNat 726, Int.negSucc 377, Int.ofNat 453, Int.negSucc 289, Int.ofNat 647, Int.negSucc 276, Int.ofNat 1015, Int.ofNat 122, Int.ofNat 363, Int.negSucc 330, Int.negSucc 610, Int.ofNat 752, Int.negSucc 969, Int.ofNat 642, Int.ofNat 49, Int.negSucc 1231, Int.negSucc 264, Int.negSucc 411, Int.ofNat 1333],
    [Int.ofNat 231, Int.ofNat 164, Int.negSucc 155, Int.negSucc 385, Int.negSucc 137, Int.negSucc 363, Int.ofNat 300, Int.ofNat 238, Int.ofNat 497, Int.negSucc 33, Int.ofNat 374, Int.ofNat 210, Int.negSucc 413, Int.ofNat 99, Int.negSucc 569, Int.ofNat 67, Int.negSucc 723, Int.negSucc 558, Int.negSucc 29, Int.negSucc 647, Int.ofNat 1413, Int.ofNat 1538, Int.ofNat 935, Int.ofNat 403, Int.negSucc 235, Int.negSucc 0, Int.negSucc 276, Int.ofNat 239, Int.negSucc 328, Int.ofNat 1144],
    [Int.ofNat 262, Int.ofNat 122, Int.negSucc 204, Int.negSucc 143, Int.negSucc 16, Int.ofNat 320, Int.negSucc 461, Int.ofNat 366, Int.ofNat 437, Int.negSucc 616, Int.ofNat 127, Int.negSucc 543, Int.negSucc 538, Int.negSucc 256, Int.ofNat 321, Int.ofNat 254, Int.negSucc 631, Int.negSucc 2235, Int.negSucc 217, Int.ofNat 46, Int.negSucc 449, Int.ofNat 51, Int.ofNat 402, Int.ofNat 428, Int.ofNat 845, Int.ofNat 885, Int.negSucc 411, Int.negSucc 55, Int.negSucc 91, Int.ofNat 164, Int.ofNat 949],
    [Int.negSucc 96, Int.negSucc 74, Int.ofNat 412, Int.ofNat 767, Int.negSucc 494, Int.ofNat 226, Int.negSucc 112, Int.negSucc 361, Int.negSucc 435, Int.ofNat 994, Int.ofNat 479, Int.ofNat 799, Int.ofNat 246, Int.negSucc 610, Int.negSucc 19, Int.ofNat 272, Int.ofNat 1126, Int.ofNat 885, Int.negSucc 721, Int.ofNat 265, Int.ofNat 52, Int.negSucc 507, Int.negSucc 399, Int.ofNat 604, Int.ofNat 163, Int.ofNat 46, Int.ofNat 277, Int.negSucc 377, Int.ofNat 516, Int.negSucc 612, Int.negSucc 162, Int.ofNat 782],
    [Int.ofNat 774, Int.ofNat 394, Int.ofNat 1232, Int.ofNat 519, Int.negSucc 1164, Int.negSucc 162, Int.ofNat 1481, Int.ofNat 564, Int.negSucc 175, Int.negSucc 147, Int.ofNat 1245, Int.ofNat 532, Int.negSucc 477, Int.negSucc 669, Int.negSucc 401, Int.ofNat 1603, Int.ofNat 109, Int.negSucc 2095, Int.negSucc 795, Int.negSucc 2235, Int.ofNat 393, Int.negSucc 1291, Int.ofNat 53, Int.negSucc 113, Int.ofNat 156, Int.ofNat 558, Int.ofNat 286, Int.ofNat 64, Int.negSucc 498, Int.negSucc 716, Int.negSucc 403, Int.ofNat 854, Int.ofNat 940]
  ]
}

def blockCert1 : OrbitBlockCert := {
  r := 19, m := 28, copies := 3, S := 1,
  blk := [(1, 24), (3, 33), (5, 18), (6, 15), (7, 16), (8, 17), (10, 19), (11, 20), (12, 32), (13, 22), (15, 6), (16, 7), (17, 8), (18, 5), (19, 10), (20, 11), (20, 25), (21, 26), (22, 13), (23, 28), (24, 1), (25, 20), (26, 21), (28, 23), (29, 31), (31, 29), (32, 12), (33, 3)],
  Qcols := [
    [(5, Int.ofNat 1), (8, Int.negSucc 0), (9, Int.ofNat 1), (11, Int.ofNat 1), (13, Int.negSucc 0), (16, Int.ofNat 1), (17, Int.negSucc 0)],
    [(5, Int.ofNat 1), (7, Int.ofNat 1), (8, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.ofNat 1), (12, Int.ofNat 1), (15, Int.negSucc 1)],
    [(4, Int.negSucc 0), (5, Int.negSucc 0), (6, Int.negSucc 0), (8, Int.negSucc 0), (9, Int.negSucc 0), (12, Int.negSucc 0), (13, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.negSucc 0)],
    [(8, Int.negSucc 0), (11, Int.ofNat 1), (13, Int.negSucc 0), (14, Int.negSucc 0), (16, Int.ofNat 1), (18, Int.ofNat 1)],
    [(1, Int.ofNat 1), (11, Int.negSucc 1), (12, Int.negSucc 0), (14, Int.ofNat 2), (17, Int.negSucc 0)],
    [(9, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.negSucc 0)],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (11, Int.negSucc 0), (12, Int.negSucc 0), (14, Int.ofNat 1), (16, Int.negSucc 1), (17, Int.ofNat 1), (18, Int.negSucc 1)],
    [(0, Int.ofNat 1), (10, Int.ofNat 2), (11, Int.ofNat 1), (13, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.ofNat 2), (18, Int.ofNat 1)],
    [(4, Int.negSucc 0), (5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.negSucc 0), (8, Int.ofNat 1), (9, Int.ofNat 1), (10, Int.ofNat 1), (12, Int.ofNat 1), (13, Int.ofNat 1), (15, Int.negSucc 0)],
    [(9, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.negSucc 0)],
    [(8, Int.negSucc 0), (14, Int.negSucc 0), (16, Int.ofNat 1), (18, Int.ofNat 1)],
    [(3, Int.ofNat 1), (13, Int.negSucc 1), (14, Int.ofNat 2), (18, Int.negSucc 1)],
    [(9, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.negSucc 0), (18, Int.ofNat 1)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.negSucc 0), (9, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.negSucc 0), (18, Int.ofNat 1)],
    [(2, Int.negSucc 0), (3, Int.negSucc 0), (13, Int.negSucc 1), (16, Int.negSucc 1), (18, Int.negSucc 0)],
    [(2, Int.ofNat 1), (10, Int.ofNat 2), (11, Int.ofNat 1), (12, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 0)],
    [(0, Int.ofNat 1), (10, Int.negSucc 0), (11, Int.negSucc 1), (13, Int.ofNat 2), (15, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 1)],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (11, Int.ofNat 2), (12, Int.ofNat 2), (14, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.negSucc 1), (18, Int.ofNat 1)],
    [(9, Int.ofNat 1), (16, Int.ofNat 1)],
    [(1, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.ofNat 2), (14, Int.negSucc 0), (17, Int.ofNat 2)],
    [(4, Int.ofNat 1), (7, Int.ofNat 1), (8, Int.negSucc 0), (9, Int.ofNat 1), (13, Int.negSucc 0), (16, Int.ofNat 1)],
    [(2, Int.ofNat 1), (10, Int.negSucc 0), (11, Int.ofNat 1), (12, Int.negSucc 1), (14, Int.ofNat 1), (15, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 0)],
    [(2, Int.negSucc 0), (3, Int.negSucc 0), (13, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 0)],
    [(3, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 0), (18, Int.ofNat 1)],
    [(8, Int.ofNat 1), (10, Int.ofNat 1), (15, Int.negSucc 0)],
    [(8, Int.ofNat 1), (10, Int.ofNat 1), (12, Int.ofNat 1), (15, Int.negSucc 0)],
    [(6, Int.ofNat 1), (8, Int.ofNat 1), (9, Int.ofNat 1), (10, Int.ofNat 1), (15, Int.negSucc 0), (18, Int.negSucc 0)],
    [(4, Int.ofNat 1), (8, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.ofNat 1), (15, Int.negSucc 1), (17, Int.negSucc 0)]
  ],
  A := [
    [Int.ofNat 3123996, Int.ofNat 328320, Int.negSucc 248399, Int.negSucc 243719, Int.ofNat 226368, Int.ofNat 227232, Int.negSucc 177551, Int.ofNat 479568, Int.negSucc 13823, Int.ofNat 53568, Int.ofNat 215136, Int.ofNat 78192, Int.negSucc 229823, Int.negSucc 387935, Int.ofNat 145584, Int.negSucc 341279, Int.negSucc 82943, Int.negSucc 274319, Int.negSucc 490751],
    [Int.ofNat 328320, Int.ofNat 3420576, Int.negSucc 10799, Int.negSucc 84239, Int.ofNat 308880, Int.ofNat 297216, Int.negSucc 224639, Int.ofNat 1054512, Int.ofNat 246672, Int.negSucc 75599, Int.ofNat 16416, Int.negSucc 323567, Int.negSucc 55727, Int.negSucc 355103, Int.ofNat 31104, Int.ofNat 22464, Int.ofNat 291168, Int.ofNat 127008, Int.negSucc 93311],
    [Int.negSucc 248399, Int.negSucc 10799, Int.ofNat 2928528, Int.ofNat 405648, Int.negSucc 274751, Int.negSucc 275183, Int.ofNat 203904, Int.negSucc 598319, Int.negSucc 197855, Int.ofNat 98928, Int.negSucc 60479, Int.negSucc 208223, Int.ofNat 280800, Int.ofNat 165456, Int.ofNat 25920, Int.negSucc 172367, Int.ofNat 89424, Int.ofNat 239760, Int.ofNat 391080],
    [Int.negSucc 243719, Int.negSucc 84239, Int.ofNat 405648, Int.ofNat 3539376, Int.negSucc 589679, Int.negSucc 591839, Int.ofNat 438048, Int.negSucc 1314575, Int.negSucc 111023, Int.ofNat 66096, Int.negSucc 39743, Int.ofNat 73008, Int.ofNat 26352, Int.ofNat 307584, Int.negSucc 138671, Int.ofNat 4752, Int.negSucc 71279, Int.ofNat 101520, Int.ofNat 260928],
    [Int.ofNat 226368, Int.ofNat 308880, Int.negSucc 274751, Int.negSucc 589679, Int.ofNat 3161808, Int.ofNat 2021760, Int.negSucc 1878335, Int.ofNat 1414368, Int.negSucc 66527, Int.negSucc 203039, Int.negSucc 222047, Int.ofNat 324000, Int.ofNat 460080, Int.ofNat 71712, Int.ofNat 704160, Int.ofNat 254880, Int.ofNat 753408, Int.negSucc 372815, Int.ofNat 181008],
    [Int.ofNat 227232, Int.ofNat 297216, Int.negSucc 275183, Int.negSucc 591839, Int.ofNat 2021760, Int.ofNat 3293136, Int.negSucc 1925855, Int.ofNat 1486080, Int.negSucc 59183, Int.negSucc 206927, Int.negSucc 256607, Int.ofNat 359424, Int.ofNat 527472, Int.ofNat 48384, Int.ofNat 744768, Int.ofNat 287712, Int.ofNat 775440, Int.negSucc 432431, Int.ofNat 238896],
    [Int.negSucc 177551, Int.negSucc 224639, Int.ofNat 203904, Int.ofNat 438048, Int.negSucc 1878335, Int.negSucc 1925855, Int.ofNat 2148768, Int.negSucc 1048463, Int.ofNat 54000, Int.ofNat 154656, Int.ofNat 183600, Int.negSucc 312887, Int.negSucc 381455, Int.negSucc 23327, Int.negSucc 527039, Int.negSucc 189215, Int.negSucc 543887, Int.ofNat 268704, Int.negSucc 111455],
    [Int.ofNat 479568, Int.ofNat 1054512, Int.negSucc 598319, Int.negSucc 1314575, Int.ofNat 1414368, Int.ofNat 1486080, Int.negSucc 1048463, Int.ofNat 3204576, Int.negSucc 63071, Int.negSucc 191375, Int.negSucc 312767, Int.ofNat 451008, Int.ofNat 521832, Int.ofNat 268704, Int.ofNat 334368, Int.ofNat 424224, Int.ofNat 759024, Int.negSucc 393551, Int.ofNat 357696],
    [Int.negSucc 13823, Int.ofNat 246672, Int.negSucc 197855, Int.negSucc 111023, Int.negSucc 66527, Int.negSucc 59183, Int.ofNat 54000, Int.negSucc 63071, Int.ofNat 1808784, Int.negSucc 256607, Int.negSucc 469583, Int.negSucc 370655, Int.negSucc 360719, Int.negSucc 667871, Int.negSucc 825119, Int.ofNat 793152, Int.ofNat 760752, Int.ofNat 63936, Int.ofNat 285984],
    [Int.ofNat 53568, Int.negSucc 75599, Int.ofNat 98928, Int.ofNat 66096, Int.negSucc 203039, Int.negSucc 206927, Int.ofNat 154656, Int.negSucc 191375, Int.negSucc 256607, Int.ofNat 951264, Int.negSucc 69983, Int.negSucc 29375, Int.negSucc 139103, Int.negSucc 19439, Int.negSucc 27647, Int.negSucc 724031, Int.negSucc 732239, Int.negSucc 9935, Int.ofNat 40464],
    [Int.ofNat 215136, Int.ofNat 16416, Int.negSucc 60479, Int.negSucc 39743, Int.negSucc 222047, Int.negSucc 256607, Int.ofNat 183600, Int.negSucc 312767, Int.negSucc 469583, Int.negSucc 69983, Int.ofNat 1717200, Int.negSucc 158975, Int.negSucc 422495, Int.negSucc 37151, Int.negSucc 55727, Int.ofNat 179280, Int.negSucc 472607, Int.negSucc 181871, Int.negSucc 375839],
    [Int.ofNat 78192, Int.negSucc 323567, Int.negSucc 208223, Int.ofNat 73008, Int.ofNat 324000, Int.ofNat 359424, Int.negSucc 312887, Int.ofNat 451008, Int.negSucc 370655, Int.negSucc 29375, Int.negSucc 158975, Int.ofNat 1537488, Int.negSucc 123551, Int.ofNat 655776, Int.ofNat 214704, Int.negSucc 26783, Int.ofNat 2160, Int.negSucc 48167, Int.negSucc 121391],
    [Int.negSucc 229823, Int.negSucc 55727, Int.ofNat 280800, Int.ofNat 26352, Int.ofNat 460080, Int.ofNat 527472, Int.negSucc 381455, Int.ofNat 521832, Int.negSucc 360719, Int.negSucc 139103, Int.negSucc 422495, Int.negSucc 123551, Int.ofNat 1316352, Int.ofNat 65664, Int.ofNat 429840, Int.ofNat 268272, Int.ofNat 313200, Int.negSucc 56159, Int.ofNat 246672],
    [Int.negSucc 387935, Int.negSucc 355103, Int.ofNat 165456, Int.ofNat 307584, Int.ofNat 71712, Int.ofNat 48384, Int.negSucc 23327, Int.ofNat 268704, Int.negSucc 667871, Int.negSucc 19439, Int.negSucc 37151, Int.ofNat 655776, Int.ofNat 65664, Int.ofNat 1300320, Int.ofNat 162000, Int.ofNat 19920, Int.ofNat 224640, Int.ofNat 88560, Int.ofNat 174960],
    [Int.ofNat 145584, Int.ofNat 31104, Int.ofNat 25920, Int.negSucc 138671, Int.ofNat 704160, Int.ofNat 744768, Int.negSucc 527039, Int.ofNat 334368, Int.negSucc 825119, Int.negSucc 27647, Int.negSucc 55727, Int.ofNat 214704, Int.ofNat 429840, Int.ofNat 162000, Int.ofNat 2862000, Int.negSucc 673055, Int.ofNat 219888, Int.negSucc 121391, Int.ofNat 256608],
    [Int.negSucc 341279, Int.ofNat 22464, Int.negSucc 172367, Int.ofNat 4752, Int.ofNat 254880, Int.ofNat 287712, Int.negSucc 189215, Int.ofNat 424224, Int.ofNat 793152, Int.negSucc 724031, Int.ofNat 179280, Int.negSucc 26783, Int.ofNat 268272, Int.ofNat 19920, Int.negSucc 673055, Int.ofNat 1885248, Int.ofNat 1101600, Int.negSucc 135215, Int.ofNat 327024],
    [Int.negSucc 82943, Int.ofNat 291168, Int.ofNat 89424, Int.negSucc 71279, Int.ofNat 753408, Int.ofNat 775440, Int.negSucc 543887, Int.ofNat 759024, Int.ofNat 760752, Int.negSucc 732239, Int.negSucc 472607, Int.ofNat 2160, Int.ofNat 313200, Int.ofNat 224640, Int.ofNat 219888, Int.ofNat 1101600, Int.ofNat 3100896, Int.ofNat 138672, Int.ofNat 514944],
    [Int.negSucc 274319, Int.ofNat 127008, Int.ofNat 239760, Int.ofNat 101520, Int.negSucc 372815, Int.negSucc 432431, Int.ofNat 268704, Int.negSucc 393551, Int.ofNat 63936, Int.negSucc 9935, Int.negSucc 181871, Int.negSucc 48167, Int.negSucc 56159, Int.ofNat 88560, Int.negSucc 121391, Int.negSucc 135215, Int.ofNat 138672, Int.ofNat 1181520, Int.ofNat 184896],
    [Int.negSucc 490751, Int.negSucc 93311, Int.ofNat 391080, Int.ofNat 260928, Int.ofNat 181008, Int.ofNat 238896, Int.negSucc 111455, Int.ofNat 357696, Int.ofNat 285984, Int.ofNat 40464, Int.negSucc 375839, Int.negSucc 121391, Int.ofNat 246672, Int.ofNat 174960, Int.ofNat 256608, Int.ofNat 327024, Int.ofNat 514944, Int.ofNat 184896, Int.ofNat 1460160]
  ],
  W := [
    [Int.ofNat 1733],
    [Int.ofNat 189, Int.ofNat 1806],
    [Int.negSucc 142, Int.ofNat 9, Int.ofNat 1669],
    [Int.negSucc 140, Int.negSucc 31, Int.ofNat 231, Int.ofNat 1829],
    [Int.ofNat 131, Int.ofNat 157, Int.negSucc 153, Int.negSucc 289, Int.ofNat 1700],
    [Int.ofNat 131, Int.ofNat 151, Int.negSucc 153, Int.negSucc 290, Int.ofNat 1101, Int.ofNat 1345],
    [Int.negSucc 101, Int.negSucc 113, Int.ofNat 114, Int.ofNat 215, Int.negSucc 1038, Int.negSucc 497, Int.ofNat 785],
    [Int.ofNat 277, Int.ofNat 555, Int.negSucc 337, Int.negSucc 644, Int.ofNat 619, Int.ofNat 331, Int.ofNat 36, Int.ofNat 1294],
    [Int.negSucc 7, Int.ofNat 137, Int.negSucc 119, Int.negSucc 43, Int.negSucc 69, Int.negSucc 24, Int.ofNat 9, Int.negSucc 119, Int.ofNat 1278],
    [Int.ofNat 31, Int.negSucc 44, Int.ofNat 62, Int.ofNat 30, Int.negSucc 106, Int.negSucc 50, Int.ofNat 4, Int.negSucc 39, Int.negSucc 199, Int.ofNat 876],
    [Int.ofNat 124, Int.negSucc 3, Int.negSucc 25, Int.negSucc 8, Int.negSucc 143, Int.negSucc 89, Int.ofNat 9, Int.negSucc 185, Int.negSucc 395, Int.negSucc 203, Int.ofNat 1148],
    [Int.ofNat 45, Int.negSucc 183, Int.negSucc 119, Int.ofNat 55, Int.ofNat 203, Int.ofNat 116, Int.negSucc 74, Int.ofNat 290, Int.negSucc 237, Int.negSucc 46, Int.negSucc 154, Int.ofNat 1066],
    [Int.negSucc 132, Int.negSucc 16, Int.ofNat 157, Int.negSucc 15, Int.ofNat 294, Int.ofNat 181, Int.negSucc 19, Int.ofNat 286, Int.negSucc 220, Int.negSucc 155, Int.negSucc 356, Int.negSucc 357, Int.ofNat 789],
    [Int.negSucc 223, Int.negSucc 172, Int.ofNat 81, Int.ofNat 138, Int.ofNat 106, Int.ofNat 29, Int.ofNat 26, Int.ofNat 360, Int.negSucc 452, Int.negSucc 105, Int.negSucc 106, Int.ofNat 356, Int.negSucc 182, Int.ofNat 736],
    [Int.ofNat 84, Int.ofNat 8, Int.ofNat 23, Int.negSucc 71, Int.ofNat 397, Int.ofNat 207, Int.ofNat 14, Int.negSucc 35, Int.negSucc 623, Int.negSucc 116, Int.negSucc 233, Int.negSucc 59, Int.ofNat 40, Int.negSucc 185, Int.ofNat 1424],
    [Int.negSucc 196, Int.ofNat 33, Int.negSucc 119, Int.ofNat 3, Int.ofNat 152, Int.ofNat 92, Int.ofNat 14, Int.ofNat 230, Int.ofNat 636, Int.negSucc 630, Int.ofNat 346, Int.ofNat 40, Int.ofNat 399, Int.ofNat 280, Int.negSucc 197, Int.ofNat 652],
    [Int.negSucc 47, Int.ofNat 166, Int.ofNat 49, Int.negSucc 45, Int.ofNat 428, Int.ofNat 208, Int.ofNat 29, Int.ofNat 257, Int.ofNat 632, Int.negSucc 607, Int.negSucc 183, Int.negSucc 43, Int.ofNat 36, Int.ofNat 440, Int.ofNat 261, Int.ofNat 220, Int.ofNat 1239],
    [Int.negSucc 157, Int.ofNat 87, Int.ofNat 130, Int.ofNat 28, Int.negSucc 198, Int.negSucc 131, Int.negSucc 38, Int.negSucc 129, Int.ofNat 28, Int.negSucc 42, Int.negSucc 191, Int.ofNat 51, Int.negSucc 35, Int.ofNat 121, Int.negSucc 8, Int.negSucc 126, Int.ofNat 129, Int.ofNat 918],
    [Int.negSucc 282, Int.negSucc 21, Int.ofNat 210, Int.ofNat 94, Int.ofNat 165, Int.ofNat 117, Int.ofNat 55, Int.ofNat 338, Int.ofNat 290, Int.ofNat 145, Int.negSucc 80, Int.negSucc 158, Int.ofNat 16, Int.ofNat 179, Int.ofNat 285, Int.ofNat 191, Int.ofNat 3, Int.ofNat 221, Int.ofNat 843]
  ]
}

def blockCert2 : OrbitBlockCert := {
  r := 23, m := 38, copies := 12, S := 8,
  blk := [(0, 24), (2, 33), (4, 24), (5, 15), (6, 16), (7, 17), (8, 18), (9, 19), (10, 20), (11, 21), (12, 22), (13, 23), (14, 24), (15, 7), (16, 8), (17, 5), (18, 6), (19, 11), (19, 25), (20, 26), (21, 9), (21, 27), (22, 28), (23, 29), (24, 2), (24, 30), (25, 21), (27, 19), (28, 31), (29, 32), (30, 33), (31, 12), (32, 13), (33, 0), (33, 4), (33, 14), (33, 34), (34, 24)],
  Qcols := [
    [(1, Int.ofNat 1), (3, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 0), (21, Int.negSucc 0)],
    [(4, Int.negSucc 0), (6, Int.ofNat 1), (10, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.negSucc 0), (13, Int.negSucc 1), (14, Int.ofNat 2), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 0), (19, Int.negSucc 0), (21, Int.negSucc 2)],
    [(1, Int.negSucc 0), (3, Int.negSucc 0), (4, Int.negSucc 0), (6, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1)],
    [(11, Int.negSucc 0)],
    [(11, Int.ofNat 3), (13, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.negSucc 1)],
    [(12, Int.negSucc 2), (13, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.negSucc 0), (18, Int.ofNat 2), (19, Int.negSucc 0)],
    [(12, Int.ofNat 1)],
    [(4, Int.negSucc 0), (5, Int.ofNat 2), (8, Int.negSucc 1), (9, Int.negSucc 0), (13, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.negSucc 0), (16, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.ofNat 1)],
    [(4, Int.ofNat 1), (5, Int.ofNat 1), (6, Int.ofNat 3), (8, Int.ofNat 2), (9, Int.negSucc 1), (10, Int.negSucc 0), (13, Int.negSucc 1), (14, Int.ofNat 2), (15, Int.negSucc 0), (16, Int.ofNat 2), (17, Int.ofNat 1), (20, Int.ofNat 3), (21, Int.negSucc 0)],
    [(4, Int.negSucc 0), (5, Int.ofNat 2), (8, Int.ofNat 1), (9, Int.ofNat 2), (13, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.ofNat 1)],
    [(1, Int.ofNat 1), (3, Int.ofNat 1), (4, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.ofNat 1), (15, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.negSucc 2), (22, Int.negSucc 0)],
    [(1, Int.negSucc 0), (3, Int.negSucc 0), (6, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 0), (21, Int.negSucc 1), (22, Int.negSucc 0)],
    [(21, Int.ofNat 1)],
    [(1, Int.ofNat 1), (7, Int.negSucc 0), (10, Int.negSucc 0), (11, Int.negSucc 0), (12, Int.negSucc 0), (13, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.ofNat 1), (19, Int.negSucc 0)],
    [(1, Int.ofNat 1), (4, Int.ofNat 1), (6, Int.ofNat 1), (10, Int.negSucc 0), (11, Int.ofNat 1), (12, Int.ofNat 1), (13, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 1), (18, Int.ofNat 1), (20, Int.ofNat 1)],
    [(1, Int.negSucc 0), (6, Int.ofNat 1), (11, Int.negSucc 1), (14, Int.ofNat 1), (15, Int.ofNat 2), (16, Int.negSucc 0), (19, Int.negSucc 1), (20, Int.ofNat 2)],
    [(1, Int.negSucc 0), (4, Int.negSucc 0), (7, Int.negSucc 0), (12, Int.ofNat 2), (14, Int.negSucc 0), (16, Int.ofNat 1), (17, Int.negSucc 0), (18, Int.ofNat 2), (20, Int.ofNat 1)],
    [(0, Int.ofNat 1), (2, Int.negSucc 1), (3, Int.ofNat 1), (6, Int.negSucc 0), (7, Int.negSucc 0), (10, Int.ofNat 1), (14, Int.ofNat 2), (15, Int.ofNat 2), (16, Int.negSucc 1), (17, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.ofNat 3), (22, Int.negSucc 1)],
    [(4, Int.ofNat 1), (5, Int.negSucc 1), (8, Int.ofNat 2), (9, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.ofNat 2), (16, Int.negSucc 0), (18, Int.negSucc 0), (19, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.negSucc 0)],
    [(4, Int.negSucc 0), (5, Int.negSucc 0), (7, Int.negSucc 2), (8, Int.negSucc 1), (9, Int.ofNat 2), (10, Int.negSucc 0), (13, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.negSucc 1), (17, Int.ofNat 1), (22, Int.negSucc 0)],
    [(0, Int.negSucc 0), (2, Int.ofNat 2), (3, Int.negSucc 0), (6, Int.negSucc 1), (7, Int.ofNat 1), (10, Int.ofNat 1), (13, Int.negSucc 1), (16, Int.negSucc 0), (18, Int.negSucc 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.ofNat 1)],
    [(4, Int.ofNat 1), (5, Int.negSucc 1), (8, Int.negSucc 0), (9, Int.negSucc 1), (13, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.negSucc 2), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.negSucc 0)],
    [(10, Int.ofNat 2), (13, Int.negSucc 0), (15, Int.negSucc 1), (17, Int.negSucc 1), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(10, Int.ofNat 2), (14, Int.ofNat 1), (17, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(4, Int.ofNat 1), (7, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.negSucc 0), (13, Int.negSucc 0), (14, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.negSucc 2)],
    [(4, Int.negSucc 0), (5, Int.negSucc 0), (8, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.negSucc 0), (20, Int.ofNat 1), (22, Int.ofNat 1)],
    [(0, Int.negSucc 0), (2, Int.negSucc 0), (3, Int.ofNat 2), (6, Int.ofNat 1), (7, Int.ofNat 1), (10, Int.ofNat 1), (13, Int.ofNat 1), (16, Int.ofNat 2), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.negSucc 1)],
    [(0, Int.ofNat 1), (2, Int.ofNat 1), (3, Int.negSucc 1), (6, Int.negSucc 0), (7, Int.ofNat 2), (10, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.ofNat 1), (17, Int.negSucc 1), (18, Int.negSucc 0), (19, Int.ofNat 2), (22, Int.ofNat 1)],
    [(1, Int.negSucc 0), (2, Int.ofNat 1), (4, Int.negSucc 0), (7, Int.ofNat 1), (9, Int.negSucc 0), (10, Int.ofNat 1), (12, Int.ofNat 1), (13, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 1)],
    [(1, Int.ofNat 1), (2, Int.negSucc 0), (8, Int.ofNat 1), (12, Int.negSucc 0), (14, Int.ofNat 1), (18, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 2)],
    [(4, Int.ofNat 1), (5, Int.ofNat 1), (8, Int.negSucc 0), (9, Int.ofNat 1), (10, Int.negSucc 0), (13, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (21, Int.ofNat 1)],
    [(2, Int.ofNat 1), (3, Int.ofNat 1), (7, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.ofNat 1), (13, Int.negSucc 0), (14, Int.ofNat 1), (15, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.negSucc 1), (20, Int.negSucc 0), (22, Int.ofNat 1)],
    [(2, Int.negSucc 0), (3, Int.negSucc 0), (6, Int.negSucc 0), (11, Int.negSucc 0), (12, Int.negSucc 0), (13, Int.negSucc 0), (14, Int.ofNat 1), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 2), (19, Int.negSucc 0), (21, Int.ofNat 1)],
    [(1, Int.negSucc 0), (2, Int.ofNat 1), (7, Int.ofNat 1), (10, Int.ofNat 1), (11, Int.negSucc 0), (12, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.ofNat 1), (17, Int.negSucc 0), (18, Int.negSucc 0), (20, Int.ofNat 1)],
    [(1, Int.ofNat 1), (2, Int.negSucc 0), (4, Int.ofNat 1), (13, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (22, Int.negSucc 0)],
    [(16, Int.negSucc 0), (18, Int.negSucc 0), (20, Int.ofNat 1)],
    [(22, Int.ofNat 1)],
    [(13, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.ofNat 1), (19, Int.ofNat 1)]
  ],
  A := [
    [Int.ofNat 10894191, Int.ofNat 109296, Int.negSucc 1480463, Int.ofNat 5628096, Int.negSucc 3219263, Int.ofNat 2233008, Int.negSucc 678671, Int.ofNat 2647728, Int.ofNat 3292704, Int.ofNat 2982960, Int.negSucc 138239, Int.negSucc 3882815, Int.negSucc 2749679, Int.ofNat 1967328, Int.negSucc 2231279, Int.negSucc 2221775, Int.negSucc 1687823, Int.negSucc 7789823, Int.ofNat 1173312, Int.negSucc 2226959, Int.negSucc 4337711, Int.ofNat 1168560, Int.ofNat 146880],
    [Int.ofNat 109296, Int.ofNat 1092960, Int.ofNat 253152, Int.negSucc 25919, Int.negSucc 919295, Int.ofNat 617760, Int.ofNat 440640, Int.ofNat 496800, Int.negSucc 13391, Int.ofNat 571104, Int.ofNat 425952, Int.negSucc 280799, Int.ofNat 22464, Int.ofNat 443232, Int.negSucc 371951, Int.ofNat 142560, Int.negSucc 456191, Int.negSucc 343439, Int.ofNat 139104, Int.negSucc 276479, Int.negSucc 479087, Int.ofNat 312336, Int.negSucc 248831],
    [Int.negSucc 1480463, Int.ofNat 253152, Int.ofNat 1584576, Int.negSucc 324431, Int.ofNat 788400, Int.negSucc 466559, Int.ofNat 74736, Int.negSucc 849743, Int.negSucc 513215, Int.negSucc 546047, Int.ofNat 95040, Int.ofNat 369360, Int.negSucc 25919, Int.negSucc 757295, Int.ofNat 267840, Int.ofNat 432432, Int.ofNat 341712, Int.ofNat 1700784, Int.negSucc 208223, Int.ofNat 551232, Int.ofNat 1074816, Int.negSucc 264383, Int.ofNat 34128],
    [Int.ofNat 5628096, Int.negSucc 25919, Int.negSucc 324431, Int.ofNat 4524336, Int.negSucc 2052863, Int.ofNat 1712448, Int.negSucc 563759, Int.ofNat 1629936, Int.ofNat 1692144, Int.ofNat 1600560, Int.negSucc 136079, Int.negSucc 2817071, Int.negSucc 1959551, Int.ofNat 1222128, Int.negSucc 1788911, Int.negSucc 930527, Int.negSucc 1231199, Int.negSucc 4576607, Int.ofNat 652320, Int.negSucc 1453679, Int.negSucc 2836943, Int.ofNat 704160, Int.negSucc 30671],
    [Int.negSucc 3219263, Int.negSucc 919295, Int.ofNat 788400, Int.negSucc 2052863, Int.ofNat 3402000, Int.negSucc 2166047, Int.negSucc 666575, Int.negSucc 2108591, Int.negSucc 154223, Int.negSucc 2018303, Int.ofNat 221184, Int.ofNat 1278720, Int.ofNat 817776, Int.negSucc 1048031, Int.ofNat 849312, Int.ofNat 614304, Int.ofNat 1359936, Int.ofNat 3036960, Int.negSucc 390095, Int.ofNat 939168, Int.ofNat 1808352, Int.negSucc 1255823, Int.ofNat 816048],
    [Int.ofNat 2233008, Int.ofNat 617760, Int.negSucc 466559, Int.ofNat 1712448, Int.negSucc 2166047, Int.ofNat 2461332, Int.negSucc 57023, Int.ofNat 1213920, Int.ofNat 942624, Int.ofNat 832032, Int.negSucc 81647, Int.negSucc 1001807, Int.negSucc 462239, Int.ofNat 1240704, Int.negSucc 833327, Int.negSucc 247967, Int.negSucc 1473551, Int.negSucc 2552687, Int.ofNat 349920, Int.negSucc 898991, Int.negSucc 1748303, Int.ofNat 883008, Int.negSucc 564623],
    [Int.negSucc 678671, Int.ofNat 440640, Int.ofNat 74736, Int.negSucc 563759, Int.negSucc 666575, Int.negSucc 57023, Int.ofNat 1626480, Int.ofNat 533952, Int.negSucc 670031, Int.negSucc 49679, Int.ofNat 461808, Int.ofNat 381888, Int.negSucc 49247, Int.negSucc 462671, Int.ofNat 154656, Int.ofNat 38016, Int.ofNat 212544, Int.ofNat 854064, Int.negSucc 238031, Int.ofNat 227664, Int.ofNat 661392, Int.ofNat 508464, Int.negSucc 334799],
    [Int.ofNat 2647728, Int.ofNat 496800, Int.negSucc 849743, Int.ofNat 1629936, Int.negSucc 2108591, Int.ofNat 1213920, Int.ofNat 533952, Int.ofNat 2433456, Int.ofNat 708048, Int.ofNat 1132272, Int.negSucc 555983, Int.negSucc 1478303, Int.negSucc 749519, Int.ofNat 874368, Int.negSucc 929231, Int.negSucc 314063, Int.negSucc 657935, Int.negSucc 2506895, Int.ofNat 329184, Int.negSucc 886895, Int.negSucc 1724975, Int.ofNat 644544, Int.negSucc 606959],
    [Int.ofNat 3292704, Int.negSucc 13391, Int.negSucc 513215, Int.ofNat 1692144, Int.negSucc 154223, Int.ofNat 942624, Int.negSucc 670031, Int.ofNat 708048, Int.ofNat 2873136, Int.ofNat 47514, Int.ofNat 119232, Int.negSucc 1502927, Int.negSucc 837215, Int.ofNat 1195776, Int.negSucc 1040687, Int.negSucc 538703, Int.negSucc 689039, Int.negSucc 2994191, Int.ofNat 597024, Int.negSucc 915407, Int.negSucc 1971647, Int.ofNat 24192, Int.ofNat 397440],
    [Int.ofNat 2982960, Int.ofNat 571104, Int.negSucc 546047, Int.ofNat 1600560, Int.negSucc 2018303, Int.ofNat 832032, Int.negSucc 49679, Int.ofNat 1132272, Int.ofNat 47514, Int.ofNat 2465424, Int.negSucc 196559, Int.negSucc 1116719, Int.negSucc 793583, Int.ofNat 615600, Int.negSucc 652751, Int.negSucc 725327, Int.negSucc 633743, Int.negSucc 2566511, Int.ofNat 251856, Int.negSucc 833327, Int.negSucc 1371599, Int.ofNat 703728, Int.negSucc 299807],
    [Int.negSucc 138239, Int.ofNat 425952, Int.ofNat 95040, Int.negSucc 136079, Int.ofNat 221184, Int.negSucc 81647, Int.ofNat 461808, Int.negSucc 555983, Int.ofNat 119232, Int.negSucc 196559, Int.ofNat 1454112, Int.ofNat 107136, Int.ofNat 1296, Int.ofNat 294624, Int.negSucc 340847, Int.negSucc 7343, Int.negSucc 174527, Int.ofNat 152064, Int.ofNat 117504, Int.negSucc 149471, Int.negSucc 101519, Int.ofNat 74736, Int.ofNat 325296],
    [Int.negSucc 3882815, Int.negSucc 280799, Int.ofNat 369360, Int.negSucc 2817071, Int.ofNat 1278720, Int.negSucc 1001807, Int.ofNat 381888, Int.negSucc 1478303, Int.negSucc 1502927, Int.negSucc 1116719, Int.ofNat 107136, Int.ofNat 2307312, Int.ofNat 1222992, Int.negSucc 1217375, Int.ofNat 1509840, Int.ofNat 450144, Int.ofNat 774144, Int.ofNat 3416688, Int.negSucc 571103, Int.ofNat 1205712, Int.ofNat 2445552, Int.negSucc 278639, Int.negSucc 41039],
    [Int.negSucc 2749679, Int.ofNat 22464, Int.negSucc 25919, Int.negSucc 1959551, Int.ofNat 817776, Int.negSucc 462239, Int.negSucc 49247, Int.negSucc 749519, Int.negSucc 837215, Int.negSucc 793583, Int.ofNat 1296, Int.ofNat 1222992, Int.ofNat 1281744, Int.negSucc 397007, Int.ofNat 805248, Int.ofNat 449280, Int.ofNat 233280, Int.ofNat 2122848, Int.negSucc 239327, Int.ofNat 613008, Int.ofNat 1064016, Int.negSucc 380591, Int.negSucc 107135],
    [Int.ofNat 1967328, Int.ofNat 443232, Int.negSucc 757295, Int.ofNat 1222128, Int.negSucc 1048031, Int.ofNat 1240704, Int.negSucc 462671, Int.ofNat 874368, Int.ofNat 1195776, Int.ofNat 615600, Int.ofNat 294624, Int.negSucc 1217375, Int.negSucc 397007, Int.ofNat 1965600, Int.negSucc 1251935, Int.ofNat 206496, Int.negSucc 1007855, Int.negSucc 2716847, Int.ofNat 625968, Int.negSucc 987119, Int.negSucc 2284847, Int.ofNat 141696, Int.ofNat 136944],
    [Int.negSucc 2231279, Int.negSucc 371951, Int.ofNat 267840, Int.negSucc 1788911, Int.ofNat 849312, Int.negSucc 833327, Int.ofNat 154656, Int.negSucc 929231, Int.negSucc 1040687, Int.negSucc 652751, Int.negSucc 340847, Int.ofNat 1509840, Int.ofNat 805248, Int.negSucc 1251935, Int.ofNat 1359936, Int.ofNat 18576, Int.ofNat 671328, Int.ofNat 2358720, Int.negSucc 390527, Int.ofNat 986256, Int.ofNat 1916784, Int.negSucc 183599, Int.negSucc 87695],
    [Int.negSucc 2221775, Int.ofNat 142560, Int.ofNat 432432, Int.negSucc 930527, Int.ofNat 614304, Int.negSucc 247967, Int.ofNat 38016, Int.negSucc 314063, Int.negSucc 538703, Int.negSucc 725327, Int.negSucc 7343, Int.ofNat 450144, Int.ofNat 449280, Int.ofNat 206496, Int.ofNat 18576, Int.ofNat 1005696, Int.ofNat 238464, Int.ofNat 1266624, Int.negSucc 102815, Int.ofNat 262656, Int.ofNat 323568, Int.negSucc 355535, Int.ofNat 25056],
    [Int.negSucc 1687823, Int.negSucc 456191, Int.ofNat 341712, Int.negSucc 1231199, Int.ofNat 1359936, Int.negSucc 1473551, Int.ofNat 212544, Int.negSucc 657935, Int.negSucc 689039, Int.negSucc 633743, Int.negSucc 174527, Int.ofNat 774144, Int.ofNat 233280, Int.negSucc 1007855, Int.ofNat 671328, Int.ofNat 238464, Int.ofNat 1159920, Int.ofNat 1819152, Int.negSucc 366767, Int.ofNat 609984, Int.ofNat 1384128, Int.negSucc 437183, Int.ofNat 225504],
    [Int.negSucc 7789823, Int.negSucc 343439, Int.ofNat 1700784, Int.negSucc 4576607, Int.ofNat 3036960, Int.negSucc 2552687, Int.ofNat 854064, Int.negSucc 2506895, Int.negSucc 2994191, Int.negSucc 2566511, Int.ofNat 152064, Int.ofNat 3416688, Int.ofNat 2122848, Int.negSucc 2716847, Int.ofNat 2358720, Int.ofNat 1266624, Int.ofNat 1819152, Int.ofNat 7321968, Int.negSucc 1125359, Int.ofNat 2312064, Int.ofNat 4566240, Int.negSucc 994031, Int.negSucc 95903],
    [Int.ofNat 1173312, Int.ofNat 139104, Int.negSucc 208223, Int.ofNat 652320, Int.negSucc 390095, Int.ofNat 349920, Int.negSucc 238031, Int.ofNat 329184, Int.ofNat 597024, Int.ofNat 251856, Int.ofNat 117504, Int.negSucc 571103, Int.negSucc 239327, Int.ofNat 625968, Int.negSucc 390527, Int.negSucc 102815, Int.negSucc 366767, Int.negSucc 1125359, Int.ofNat 422928, Int.negSucc 269135, Int.negSucc 814751, Int.negSucc 10367, Int.ofNat 120528],
    [Int.negSucc 2226959, Int.negSucc 276479, Int.ofNat 551232, Int.negSucc 1453679, Int.ofNat 939168, Int.negSucc 898991, Int.ofNat 227664, Int.negSucc 886895, Int.negSucc 915407, Int.negSucc 833327, Int.negSucc 149471, Int.ofNat 1205712, Int.ofNat 613008, Int.negSucc 987119, Int.ofNat 986256, Int.ofNat 262656, Int.ofNat 609984, Int.ofNat 2312064, Int.negSucc 269135, Int.ofNat 1018224, Int.ofNat 1623456, Int.negSucc 325727, Int.ofNat 53136],
    [Int.negSucc 4337711, Int.negSucc 479087, Int.ofNat 1074816, Int.negSucc 2836943, Int.ofNat 1808352, Int.negSucc 1748303, Int.ofNat 661392, Int.negSucc 1724975, Int.negSucc 1971647, Int.negSucc 1371599, Int.negSucc 101519, Int.ofNat 2445552, Int.ofNat 1064016, Int.negSucc 2284847, Int.ofNat 1916784, Int.ofNat 323568, Int.ofNat 1384128, Int.ofNat 4566240, Int.negSucc 814751, Int.ofNat 1623456, Int.ofNat 3503088, Int.negSucc 394847, Int.negSucc 86831],
    [Int.ofNat 1168560, Int.ofNat 312336, Int.negSucc 264383, Int.ofNat 704160, Int.negSucc 1255823, Int.ofNat 883008, Int.ofNat 508464, Int.ofNat 644544, Int.ofNat 24192, Int.ofNat 703728, Int.ofNat 74736, Int.negSucc 278639, Int.negSucc 380591, Int.ofNat 141696, Int.negSucc 183599, Int.negSucc 355535, Int.negSucc 437183, Int.negSucc 994031, Int.negSucc 10367, Int.negSucc 325727, Int.negSucc 394847, Int.ofNat 703728, Int.negSucc 323999],
    [Int.ofNat 146880, Int.negSucc 248831, Int.ofNat 34128, Int.negSucc 30671, Int.ofNat 816048, Int.negSucc 564623, Int.negSucc 334799, Int.negSucc 606959, Int.ofNat 397440, Int.negSucc 299807, Int.ofNat 325296, Int.negSucc 41039, Int.negSucc 107135, Int.ofNat 136944, Int.negSucc 87695, Int.ofNat 25056, Int.ofNat 225504, Int.negSucc 95903, Int.ofNat 120528, Int.ofNat 53136, Int.negSucc 86831, Int.negSucc 323999, Int.ofNat 535680]
  ],
  W := [
    [Int.ofNat 26400],
    [Int.ofNat 265, Int.ofNat 8342],
    [Int.negSucc 3588, Int.ofNat 2056, Int.ofNat 9166],
    [Int.ofNat 13644, Int.negSucc 631, Int.ofNat 3219, Int.ofNat 9610],
    [Int.negSucc 7803, Int.negSucc 6804, Int.ofNat 3975, Int.negSucc 4369, Int.ofNat 8679],
    [Int.ofNat 5413, Int.ofNat 4567, Int.negSucc 2161, Int.ofNat 4743, Int.negSucc 4144, Int.ofNat 7920],
    [Int.negSucc 1644, Int.ofNat 3433, Int.negSucc 891, Int.negSucc 893, Int.negSucc 3744, Int.negSucc 2983, Int.ofNat 8050],
    [Int.ofNat 6419, Int.ofNat 3607, Int.negSucc 4228, Int.ofNat 3396, Int.negSucc 3301, Int.negSucc 1574, Int.ofNat 1807, Int.ofNat 7428],
    [Int.ofNat 7982, Int.negSucc 355, Int.negSucc 377, Int.ofNat 39, Int.ofNat 5954, Int.ofNat 5356, Int.ofNat 1174, Int.ofNat 2639, Int.ofNat 6865],
    [Int.ofNat 7232, Int.ofNat 4152, Int.negSucc 1911, Int.ofNat 1306, Int.negSucc 3591, Int.negSucc 3797, Int.negSucc 3832, Int.negSucc 1663, Int.negSucc 489, Int.ofNat 6131],
    [Int.negSucc 334, Int.ofNat 3278, Int.negSucc 202, Int.negSucc 146, Int.ofNat 3919, Int.negSucc 237, Int.ofNat 3901, Int.negSucc 5398, Int.negSucc 143, Int.negSucc 797, Int.ofNat 4628],
    [Int.negSucc 9412, Int.negSucc 1854, Int.negSucc 690, Int.negSucc 5286, Int.negSucc 2835, Int.ofNat 903, Int.ofNat 255, Int.negSucc 2808, Int.negSucc 378, Int.negSucc 122, Int.ofNat 839, Int.ofNat 3038],
    [Int.negSucc 6665, Int.ofNat 384, Int.negSucc 2876, Int.negSucc 2596, Int.ofNat 347, Int.ofNat 1551, Int.negSucc 1787, Int.negSucc 416, Int.negSucc 1222, Int.negSucc 1190, Int.negSucc 381, Int.negSucc 295, Int.ofNat 3619],
    [Int.ofNat 4769, Int.ofNat 3249, Int.negSucc 4148, Int.ofNat 2971, Int.ofNat 2504, Int.ofNat 3291, Int.negSucc 1833, Int.ofNat 371, Int.ofNat 957, Int.negSucc 790, Int.ofNat 1952, Int.negSucc 3250, Int.negSucc 2258, Int.ofNat 4954],
    [Int.negSucc 5408, Int.negSucc 2681, Int.ofNat 354, Int.negSucc 4528, Int.negSucc 3145, Int.negSucc 327, Int.negSucc 780, Int.negSucc 1035, Int.ofNat 10, Int.negSucc 357, Int.negSucc 1297, Int.ofNat 2222, Int.ofNat 1461, Int.negSucc 2021, Int.ofNat 2237],
    [Int.negSucc 5385, Int.ofNat 1265, Int.ofNat 627, Int.ofNat 1323, Int.ofNat 1058, Int.ofNat 880, Int.negSucc 302, Int.ofNat 1816, Int.negSucc 916, Int.negSucc 765, Int.ofNat 45, Int.negSucc 1714, Int.negSucc 1778, Int.ofNat 3487, Int.negSucc 118, Int.ofNat 2516],
    [Int.negSucc 4091, Int.negSucc 3369, Int.ofNat 1540, Int.negSucc 3127, Int.ofNat 1427, Int.negSucc 4126, Int.ofNat 1248, Int.ofNat 1265, Int.negSucc 454, Int.ofNat 1005, Int.negSucc 1190, Int.ofNat 416, Int.negSucc 1593, Int.negSucc 1054, Int.ofNat 268, Int.ofNat 1135, Int.ofNat 1909],
    [Int.negSucc 18884, Int.negSucc 2034, Int.ofNat 4937, Int.negSucc 5454, Int.negSucc 1189, Int.negSucc 2553, Int.ofNat 2239, Int.negSucc 602, Int.negSucc 2883, Int.negSucc 1710, Int.ofNat 121, Int.ofNat 2291, Int.ofNat 3893, Int.negSucc 1488, Int.negSucc 344, Int.ofNat 1342, Int.negSucc 226, Int.ofNat 2061],
    [Int.ofNat 2844, Int.ofNat 977, Int.negSucc 558, Int.ofNat 557, Int.ofNat 984, Int.ofNat 348, Int.negSucc 1140, Int.ofNat 119, Int.ofNat 1299, Int.negSucc 1465, Int.ofNat 1206, Int.negSucc 986, Int.ofNat 68, Int.ofNat 1168, Int.ofNat 1636, Int.negSucc 90, Int.ofNat 149, Int.negSucc 135, Int.ofNat 2086],
    [Int.negSucc 5398, Int.negSucc 1949, Int.ofNat 2172, Int.negSucc 2871, Int.negSucc 1898, Int.negSucc 1130, Int.ofNat 157, Int.negSucc 601, Int.ofNat 512, Int.negSucc 1558, Int.negSucc 609, Int.ofNat 1141, Int.ofNat 1134, Int.ofNat 238, Int.ofNat 1343, Int.negSucc 242, Int.negSucc 400, Int.ofNat 1312, Int.ofNat 931, Int.ofNat 1837],
    [Int.negSucc 10515, Int.negSucc 3340, Int.ofNat 4137, Int.negSucc 5568, Int.negSucc 3439, Int.negSucc 2348, Int.ofNat 1904, Int.negSucc 1741, Int.negSucc 907, Int.ofNat 0, Int.negSucc 666, Int.ofNat 3932, Int.ofNat 1116, Int.negSucc 2736, Int.ofNat 663, Int.ofNat 27, Int.ofNat 732, Int.ofNat 504, Int.ofNat 428, Int.negSucc 866, Int.ofNat 1552],
    [Int.ofNat 2833, Int.ofNat 2306, Int.negSucc 1253, Int.ofNat 1239, Int.negSucc 3706, Int.ofNat 845, Int.ofNat 2226, Int.negSucc 1304, Int.negSucc 347, Int.ofNat 1149, Int.negSucc 439, Int.ofNat 1207, Int.negSucc 608, Int.negSucc 1028, Int.ofNat 351, Int.ofNat 62, Int.ofNat 146, Int.negSucc 650, Int.negSucc 907, Int.ofNat 311, Int.ofNat 122, Int.ofNat 1077],
    [Int.ofNat 356, Int.negSucc 1919, Int.ofNat 808, Int.negSucc 1106, Int.ofNat 3904, Int.negSucc 771, Int.negSucc 272, Int.negSucc 1999, Int.ofNat 1273, Int.negSucc 563, Int.ofNat 379, Int.negSucc 597, Int.negSucc 1359, Int.ofNat 1117, Int.ofNat 653, Int.ofNat 185, Int.negSucc 367, Int.negSucc 187, Int.ofNat 115, Int.ofNat 1004, Int.negSucc 2, Int.negSucc 20, Int.ofNat 1097]
  ]
}

def blockCert3 : OrbitBlockCert := {
  r := 28, m := 48, copies := 3, S := 2,
  blk := [(0, 2), (0, 30), (1, 3), (2, 0), (2, 4), (2, 14), (2, 34), (3, 1), (4, 2), (4, 30), (5, 7), (6, 8), (7, 5), (8, 6), (9, 11), (9, 25), (10, 26), (11, 9), (11, 27), (12, 28), (13, 29), (14, 2), (14, 30), (15, 17), (16, 18), (17, 15), (18, 16), (19, 21), (21, 19), (22, 31), (23, 32), (24, 33), (25, 9), (25, 27), (26, 10), (27, 11), (27, 25), (28, 12), (29, 13), (30, 0), (30, 4), (30, 14), (30, 34), (31, 22), (32, 23), (33, 24), (34, 2), (34, 30)],
  Qcols := [
    [(26, Int.ofNat 1)],
    [(4, Int.negSucc 0), (6, Int.ofNat 1), (9, Int.ofNat 1), (12, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.ofNat 1), (18, Int.ofNat 2), (25, Int.ofNat 1), (26, Int.ofNat 1)],
    [(5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.negSucc 0), (9, Int.negSucc 0), (11, Int.negSucc 0), (14, Int.ofNat 1), (18, Int.negSucc 0), (21, Int.negSucc 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (26, Int.negSucc 1), (27, Int.negSucc 0)],
    [(24, Int.negSucc 0)],
    [(25, Int.negSucc 0)],
    [(2, Int.ofNat 1), (6, Int.negSucc 0), (7, Int.ofNat 1), (13, Int.ofNat 1), (16, Int.negSucc 0), (19, Int.ofNat 2), (22, Int.negSucc 0), (23, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.negSucc 0)],
    [(2, Int.negSucc 0), (3, Int.negSucc 0), (4, Int.ofNat 1), (5, Int.ofNat 1), (10, Int.ofNat 1), (11, Int.negSucc 0), (13, Int.negSucc 0), (15, Int.ofNat 1), (17, Int.negSucc 0), (18, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.ofNat 1), (27, Int.negSucc 0)],
    [(5, Int.ofNat 1), (6, Int.ofNat 1), (7, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.ofNat 1), (14, Int.negSucc 0), (18, Int.ofNat 1), (21, Int.negSucc 1), (22, Int.ofNat 1), (23, Int.ofNat 2), (24, Int.ofNat 2), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 1)],
    [(22, Int.ofNat 1), (23, Int.negSucc 0)],
    [(3, Int.ofNat 1), (5, Int.negSucc 0), (7, Int.negSucc 0), (14, Int.ofNat 1), (15, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 1), (25, Int.ofNat 1), (27, Int.negSucc 0)],
    [(1, Int.ofNat 1), (2, Int.ofNat 1), (3, Int.ofNat 1), (4, Int.negSucc 0), (6, Int.ofNat 1), (11, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.ofNat 2), (19, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.ofNat 1), (24, Int.negSucc 0), (27, Int.ofNat 1)],
    [(1, Int.negSucc 0), (2, Int.ofNat 1), (7, Int.ofNat 1), (11, Int.ofNat 1), (13, Int.ofNat 1), (16, Int.negSucc 0), (18, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1), (23, Int.negSucc 0), (25, Int.ofNat 2), (27, Int.ofNat 1)],
    [(1, Int.ofNat 1), (2, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.negSucc 0), (9, Int.negSucc 0), (13, Int.ofNat 1), (15, Int.ofNat 1), (16, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (22, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 1)],
    [(1, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.ofNat 1), (4, Int.negSucc 0), (5, Int.negSucc 0), (7, Int.negSucc 0), (9, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 2), (22, Int.negSucc 1), (25, Int.ofNat 2)],
    [(5, Int.ofNat 1), (7, Int.ofNat 1), (9, Int.ofNat 1), (14, Int.negSucc 1), (15, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 3), (23, Int.ofNat 1), (24, Int.ofNat 1), (27, Int.negSucc 0)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.negSucc 1), (10, Int.ofNat 1), (13, Int.ofNat 1), (15, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.negSucc 0), (20, Int.ofNat 2), (23, Int.negSucc 0), (24, Int.negSucc 0), (27, Int.negSucc 0)],
    [(6, Int.negSucc 0), (7, Int.ofNat 1), (8, Int.negSucc 0), (9, Int.negSucc 2), (10, Int.negSucc 0), (13, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.ofNat 1), (20, Int.negSucc 1), (21, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 1)],
    [(6, Int.negSucc 0), (11, Int.negSucc 0), (14, Int.ofNat 2), (15, Int.negSucc 1), (25, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.negSucc 1)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.negSucc 1), (10, Int.ofNat 1), (13, Int.negSucc 1), (15, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.negSucc 0), (20, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.negSucc 0), (27, Int.negSucc 0)],
    [(0, Int.ofNat 1), (4, Int.negSucc 0), (5, Int.ofNat 1), (6, Int.ofNat 1), (9, Int.ofNat 1), (13, Int.negSucc 0), (14, Int.negSucc 0), (16, Int.negSucc 1), (17, Int.negSucc 0), (18, Int.ofNat 1), (19, Int.negSucc 0), (23, Int.negSucc 0), (25, Int.ofNat 1), (26, Int.negSucc 1), (27, Int.ofNat 2)],
    [(0, Int.negSucc 0), (3, Int.ofNat 1), (7, Int.negSucc 0), (12, Int.negSucc 0), (14, Int.ofNat 1), (15, Int.negSucc 0), (16, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.negSucc 0), (25, Int.ofNat 2), (26, Int.negSucc 1), (27, Int.ofNat 2)],
    [(2, Int.ofNat 1), (3, Int.ofNat 1), (4, Int.negSucc 0), (16, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1), (21, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.ofNat 2), (27, Int.negSucc 0)],
    [(16, Int.ofNat 1), (26, Int.ofNat 1), (27, Int.negSucc 0)],
    [(1, Int.negSucc 0), (2, Int.negSucc 0), (6, Int.ofNat 1), (9, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.ofNat 1), (14, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.negSucc 1), (24, Int.negSucc 0), (26, Int.negSucc 0)],
    [(1, Int.ofNat 1), (2, Int.negSucc 0), (3, Int.negSucc 0), (4, Int.ofNat 1), (5, Int.ofNat 1), (6, Int.ofNat 1), (10, Int.ofNat 1), (13, Int.negSucc 0), (14, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.ofNat 1), (26, Int.ofNat 2), (27, Int.negSucc 0)],
    [(1, Int.negSucc 0), (2, Int.negSucc 0), (3, Int.negSucc 0), (4, Int.ofNat 1), (7, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (13, Int.negSucc 0), (14, Int.ofNat 1), (17, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1), (23, Int.negSucc 0), (24, Int.ofNat 1), (26, Int.ofNat 1), (27, Int.negSucc 0)],
    [(1, Int.ofNat 1), (2, Int.negSucc 0), (5, Int.negSucc 0), (7, Int.negSucc 0), (12, Int.ofNat 1), (14, Int.ofNat 1), (17, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 2), (24, Int.negSucc 1), (26, Int.ofNat 1)],
    [(5, Int.negSucc 0), (7, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.negSucc 2), (14, Int.negSucc 0), (15, Int.ofNat 2), (18, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1), (25, Int.negSucc 0), (26, Int.negSucc 0), (27, Int.ofNat 1)],
    [(6, Int.ofNat 1), (11, Int.ofNat 1), (12, Int.negSucc 2), (14, Int.ofNat 1), (15, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.negSucc 1), (27, Int.negSucc 0)],
    [(0, Int.negSucc 0), (3, Int.negSucc 0), (5, Int.ofNat 1), (10, Int.ofNat 1), (11, Int.negSucc 0), (12, Int.negSucc 0), (13, Int.negSucc 0), (17, Int.ofNat 1), (24, Int.negSucc 0), (25, Int.ofNat 1)],
    [(0, Int.ofNat 1), (4, Int.ofNat 1), (5, Int.ofNat 1), (12, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.ofNat 1), (17, Int.ofNat 2), (19, Int.negSucc 0), (20, Int.ofNat 1), (22, Int.negSucc 0), (23, Int.ofNat 1), (25, Int.negSucc 0), (26, Int.ofNat 1), (27, Int.negSucc 0)],
    [(5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (8, Int.ofNat 1), (10, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1), (23, Int.ofNat 2), (24, Int.ofNat 2), (25, Int.negSucc 0), (26, Int.negSucc 0)],
    [(5, Int.negSucc 0), (8, Int.ofNat 2), (12, Int.ofNat 1), (13, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 3), (19, Int.ofNat 1), (20, Int.negSucc 1), (21, Int.negSucc 0), (23, Int.ofNat 2), (24, Int.negSucc 0), (25, Int.negSucc 0), (26, Int.ofNat 3)],
    [(5, Int.ofNat 1), (7, Int.ofNat 1), (9, Int.ofNat 1), (14, Int.ofNat 1), (15, Int.ofNat 1), (18, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (27, Int.ofNat 2)],
    [(5, Int.ofNat 1), (8, Int.ofNat 1), (11, Int.ofNat 3), (12, Int.negSucc 0), (13, Int.ofNat 1), (15, Int.negSucc 0), (16, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.negSucc 0), (24, Int.negSucc 0), (26, Int.negSucc 0)],
    [(5, Int.negSucc 0), (8, Int.ofNat 2), (12, Int.ofNat 1), (13, Int.ofNat 2), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 1), (21, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 2), (25, Int.negSucc 0)],
    [(6, Int.negSucc 0), (11, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (25, Int.ofNat 1), (26, Int.negSucc 0), (27, Int.negSucc 1)],
    [(0, Int.ofNat 1), (3, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (11, Int.negSucc 0), (13, Int.ofNat 1), (16, Int.ofNat 1), (18, Int.negSucc 0), (19, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0), (24, Int.ofNat 2), (25, Int.ofNat 2), (26, Int.negSucc 0), (27, Int.negSucc 0)],
    [(0, Int.negSucc 0), (4, Int.ofNat 1), (6, Int.negSucc 0), (7, Int.ofNat 1), (10, Int.negSucc 0), (15, Int.negSucc 0), (16, Int.ofNat 2), (17, Int.ofNat 1), (19, Int.ofNat 2), (21, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.ofNat 2), (25, Int.ofNat 2), (26, Int.ofNat 1)],
    [(3, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.ofNat 1), (19, Int.ofNat 1), (22, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.negSucc 0), (27, Int.negSucc 0)],
    [(4, Int.ofNat 1), (15, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.ofNat 1), (24, Int.ofNat 1), (25, Int.negSucc 0), (27, Int.negSucc 0)],
    [(16, Int.negSucc 0), (24, Int.negSucc 0), (25, Int.negSucc 0)],
    [(17, Int.negSucc 0)],
    [(0, Int.negSucc 0), (4, Int.negSucc 0), (7, Int.ofNat 1), (9, Int.ofNat 1), (10, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.negSucc 1), (21, Int.ofNat 2), (22, Int.negSucc 1), (23, Int.ofNat 1), (25, Int.ofNat 1), (27, Int.negSucc 0)],
    [(0, Int.ofNat 1), (3, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.negSucc 0), (10, Int.negSucc 0), (14, Int.ofNat 1), (15, Int.ofNat 1), (17, Int.negSucc 0), (21, Int.ofNat 2), (22, Int.negSucc 2), (23, Int.ofNat 2), (24, Int.negSucc 0), (26, Int.ofNat 1), (27, Int.negSucc 2)],
    [(5, Int.ofNat 1), (6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.ofNat 1), (12, Int.negSucc 0), (13, Int.negSucc 0), (16, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.ofNat 2), (22, Int.ofNat 1), (23, Int.ofNat 1), (24, Int.ofNat 1), (26, Int.negSucc 1)],
    [(2, Int.negSucc 0), (9, Int.ofNat 1), (12, Int.ofNat 1), (15, Int.ofNat 1), (17, Int.ofNat 1), (18, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.negSucc 0), (23, Int.negSucc 0), (25, Int.ofNat 1)],
    [(17, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.negSucc 0), (27, Int.ofNat 1)]
  ],
  A := [
    [Int.ofNat 2267232, Int.ofNat 273456, Int.negSucc 21599, Int.negSucc 23327, Int.ofNat 12960, Int.negSucc 44927, Int.negSucc 40607, Int.negSucc 69983, Int.negSucc 53135, Int.negSucc 44927, Int.ofNat 22464, Int.negSucc 81647, Int.ofNat 41040, Int.ofNat 2592, Int.negSucc 15119, Int.negSucc 61775, Int.ofNat 18144, Int.negSucc 16847, Int.negSucc 28079, Int.ofNat 147312, Int.ofNat 13392, Int.negSucc 10367, Int.ofNat 3888, Int.ofNat 33264, Int.ofNat 12528, Int.ofNat 47088, Int.ofNat 33696, Int.ofNat 129600],
    [Int.ofNat 273456, Int.ofNat 2236896, Int.ofNat 40608, Int.negSucc 37151, Int.ofNat 27216, Int.ofNat 35424, Int.ofNat 30240, Int.ofNat 50112, Int.negSucc 12527, Int.ofNat 432, Int.negSucc 4319, Int.ofNat 39312, Int.negSucc 1295, Int.ofNat 15984, Int.ofNat 12528, Int.ofNat 47088, Int.negSucc 39743, Int.ofNat 21168, Int.negSucc 51407, Int.negSucc 72143, Int.negSucc 53135, Int.ofNat 19872, Int.ofNat 63504, Int.ofNat 6048, Int.negSucc 1295, Int.ofNat 23328, Int.ofNat 16848, Int.negSucc 74735],
    [Int.negSucc 21599, Int.ofNat 40608, Int.ofNat 1468368, Int.negSucc 673055, Int.ofNat 885168, Int.ofNat 383088, Int.ofNat 145584, Int.negSucc 307151, Int.ofNat 293328, Int.ofNat 211680, Int.ofNat 147744, Int.negSucc 141263, Int.negSucc 114911, Int.negSucc 69119, Int.negSucc 124847, Int.negSucc 163727, Int.negSucc 126143, Int.ofNat 276048, Int.ofNat 137808, Int.negSucc 354671, Int.negSucc 54431, Int.negSucc 54431, Int.ofNat 208656, Int.negSucc 140831, Int.ofNat 249696, Int.ofNat 144288, Int.ofNat 201312, Int.negSucc 165023],
    [Int.negSucc 23327, Int.negSucc 37151, Int.negSucc 673055, Int.ofNat 2337984, Int.negSucc 63503, Int.negSucc 1727, Int.ofNat 372816, Int.negSucc 140831, Int.ofNat 496800, Int.ofNat 449712, Int.ofNat 273024, Int.negSucc 417743, Int.ofNat 322704, Int.ofNat 43632, Int.negSucc 224639, Int.negSucc 192239, Int.negSucc 47087, Int.negSucc 406943, Int.ofNat 168480, Int.negSucc 206063, Int.negSucc 98927, Int.negSucc 13391, Int.negSucc 541295, Int.ofNat 184464, Int.negSucc 374975, Int.negSucc 149903, Int.negSucc 641087, Int.ofNat 101520],
    [Int.ofNat 12960, Int.ofNat 27216, Int.ofNat 885168, Int.negSucc 63503, Int.ofNat 1508976, Int.negSucc 285119, Int.ofNat 317952, Int.ofNat 120528, Int.negSucc 23327, Int.ofNat 176256, Int.ofNat 196128, Int.negSucc 113183, Int.ofNat 240624, Int.ofNat 47088, Int.negSucc 292463, Int.negSucc 268271, Int.negSucc 222479, Int.ofNat 130032, Int.ofNat 121392, Int.negSucc 362015, Int.ofNat 83808, Int.ofNat 5184, Int.ofNat 153792, Int.ofNat 15120, Int.ofNat 131328, Int.ofNat 448416, Int.ofNat 40608, Int.negSucc 122687],
    [Int.negSucc 44927, Int.ofNat 35424, Int.ofNat 383088, Int.negSucc 1727, Int.negSucc 285119, Int.ofNat 1793232, Int.ofNat 16848, Int.negSucc 706751, Int.ofNat 642384, Int.negSucc 435023, Int.negSucc 61775, Int.negSucc 28079, Int.negSucc 291599, Int.ofNat 203040, Int.ofNat 130032, Int.ofNat 111456, Int.negSucc 282527, Int.ofNat 295488, Int.negSucc 118799, Int.negSucc 178415, Int.negSucc 182735, Int.negSucc 37151, Int.ofNat 254880, Int.negSucc 24623, Int.ofNat 66528, Int.negSucc 69983, Int.ofNat 379728, Int.negSucc 258335],
    [Int.negSucc 40607, Int.ofNat 30240, Int.ofNat 145584, Int.ofNat 372816, Int.ofNat 317952, Int.ofNat 16848, Int.ofNat 1394496, Int.ofNat 289440, Int.ofNat 371952, Int.negSucc 174959, Int.negSucc 64367, Int.negSucc 321839, Int.ofNat 50112, Int.negSucc 30239, Int.ofNat 118800, Int.negSucc 57023, Int.negSucc 236303, Int.ofNat 311040, Int.negSucc 112319, Int.negSucc 152495, Int.ofNat 10800, Int.negSucc 32831, Int.negSucc 147311, Int.ofNat 168912, Int.negSucc 28511, Int.ofNat 187488, Int.negSucc 209087, Int.negSucc 287711],
    [Int.negSucc 69983, Int.ofNat 50112, Int.negSucc 307151, Int.negSucc 140831, Int.ofNat 120528, Int.negSucc 706751, Int.ofNat 289440, Int.ofNat 1904256, Int.negSucc 628991, Int.negSucc 425951, Int.negSucc 51407, Int.negSucc 146879, Int.negSucc 39743, Int.negSucc 170639, Int.ofNat 138672, Int.ofNat 157680, Int.negSucc 28943, Int.ofNat 179712, Int.negSucc 172799, Int.negSucc 263519, Int.ofNat 136080, Int.negSucc 46223, Int.ofNat 215136, Int.negSucc 231119, Int.ofNat 40608, Int.negSucc 55727, Int.ofNat 241920, Int.negSucc 342575],
    [Int.negSucc 53135, Int.negSucc 12527, Int.ofNat 293328, Int.ofNat 496800, Int.negSucc 23327, Int.ofNat 642384, Int.ofNat 371952, Int.negSucc 628991, Int.ofNat 1747584, Int.ofNat 137376, Int.ofNat 322272, Int.ofNat 62640, Int.negSucc 146015, Int.negSucc 449711, Int.negSucc 16415, Int.ofNat 60048, Int.ofNat 79920, Int.negSucc 9071, Int.ofNat 114048, Int.negSucc 161999, Int.ofNat 483840, Int.ofNat 10368, Int.negSucc 324575, Int.negSucc 263087, Int.negSucc 129167, Int.negSucc 181439, Int.negSucc 385343, Int.negSucc 110159],
    [Int.negSucc 44927, Int.ofNat 432, Int.ofNat 211680, Int.ofNat 449712, Int.ofNat 176256, Int.negSucc 435023, Int.negSucc 174959, Int.negSucc 425951, Int.ofNat 137376, Int.ofNat 1686096, Int.ofNat 271296, Int.ofNat 343440, Int.negSucc 24623, Int.ofNat 11232, Int.negSucc 114047, Int.negSucc 215135, Int.ofNat 293760, Int.negSucc 358127, Int.negSucc 98495, Int.negSucc 306287, Int.negSucc 131759, Int.negSucc 53135, Int.negSucc 362015, Int.ofNat 167616, Int.negSucc 217727, Int.negSucc 77327, Int.negSucc 317087, Int.negSucc 94607],
    [Int.ofNat 22464, Int.negSucc 4319, Int.ofNat 147744, Int.ofNat 273024, Int.ofNat 196128, Int.negSucc 61775, Int.negSucc 64367, Int.negSucc 51407, Int.ofNat 322272, Int.ofNat 271296, Int.ofNat 2260656, Int.ofNat 260064, Int.negSucc 153791, Int.negSucc 219023, Int.negSucc 208655, Int.negSucc 215567, Int.negSucc 311903, Int.ofNat 599616, Int.negSucc 214271, Int.negSucc 73871, Int.ofNat 257472, Int.ofNat 68688, Int.negSucc 296351, Int.ofNat 288144, Int.ofNat 678240, Int.ofNat 277776, Int.ofNat 293760, Int.ofNat 154656],
    [Int.negSucc 81647, Int.ofNat 39312, Int.negSucc 141263, Int.negSucc 417743, Int.negSucc 113183, Int.negSucc 28079, Int.negSucc 321839, Int.negSucc 146879, Int.ofNat 62640, Int.ofNat 343440, Int.ofNat 260064, Int.ofNat 1428624, Int.ofNat 75600, Int.negSucc 218159, Int.ofNat 171936, Int.ofNat 170208, Int.negSucc 137375, Int.negSucc 85967, Int.negSucc 10799, Int.negSucc 236735, Int.ofNat 253584, Int.ofNat 20304, Int.negSucc 132623, Int.ofNat 28080, Int.ofNat 127440, Int.ofNat 113616, Int.negSucc 83807, Int.negSucc 423359],
    [Int.ofNat 41040, Int.negSucc 1295, Int.negSucc 114911, Int.ofNat 322704, Int.ofNat 240624, Int.negSucc 291599, Int.ofNat 50112, Int.negSucc 39743, Int.negSucc 146015, Int.negSucc 24623, Int.negSucc 153791, Int.ofNat 75600, Int.ofNat 2169936, Int.negSucc 388799, Int.ofNat 263520, Int.ofNat 192672, Int.ofNat 255312, Int.negSucc 209951, Int.negSucc 485135, Int.ofNat 461376, Int.ofNat 394416, Int.ofNat 122688, Int.negSucc 139967, Int.ofNat 304992, Int.negSucc 304991, Int.ofNat 235008, Int.negSucc 585791, Int.ofNat 197856],
    [Int.ofNat 2592, Int.ofNat 15984, Int.negSucc 69119, Int.ofNat 43632, Int.ofNat 47088, Int.ofNat 203040, Int.negSucc 30239, Int.negSucc 170639, Int.negSucc 449711, Int.ofNat 11232, Int.negSucc 219023, Int.negSucc 218159, Int.negSucc 388799, Int.ofNat 875664, Int.negSucc 154655, Int.negSucc 128735, Int.ofNat 101952, Int.negSucc 25487, Int.ofNat 155952, Int.negSucc 219455, Int.negSucc 597887, Int.ofNat 59184, Int.ofNat 306720, Int.ofNat 177984, Int.negSucc 235439, Int.negSucc 22895, Int.ofNat 131760, Int.negSucc 40607],
    [Int.negSucc 15119, Int.ofNat 12528, Int.negSucc 124847, Int.negSucc 224639, Int.negSucc 292463, Int.ofNat 130032, Int.ofNat 118800, Int.ofNat 138672, Int.negSucc 16415, Int.negSucc 114047, Int.negSucc 208655, Int.ofNat 171936, Int.ofNat 263520, Int.negSucc 154655, Int.ofNat 524016, Int.ofNat 291600, Int.negSucc 38879, Int.negSucc 36287, Int.negSucc 196559, Int.ofNat 163728, Int.ofNat 137808, Int.negSucc 28943, Int.ofNat 75168, Int.ofNat 47520, Int.negSucc 11663, Int.ofNat 21168, Int.ofNat 2592, Int.negSucc 84239],
    [Int.negSucc 61775, Int.ofNat 47088, Int.negSucc 163727, Int.negSucc 192239, Int.negSucc 268271, Int.ofNat 111456, Int.negSucc 57023, Int.ofNat 157680, Int.ofNat 60048, Int.negSucc 215135, Int.negSucc 215567, Int.ofNat 170208, Int.ofNat 192672, Int.negSucc 128735, Int.ofNat 291600, Int.ofNat 602208, Int.negSucc 15119, Int.negSucc 14687, Int.negSucc 287711, Int.ofNat 5616, Int.ofNat 147312, Int.negSucc 25055, Int.ofNat 158976, Int.ofNat 63504, Int.negSucc 73007, Int.ofNat 52704, Int.negSucc 5183, Int.negSucc 129599],
    [Int.ofNat 18144, Int.negSucc 39743, Int.negSucc 126143, Int.negSucc 47087, Int.negSucc 222479, Int.negSucc 282527, Int.negSucc 236303, Int.negSucc 28943, Int.ofNat 79920, Int.ofNat 293760, Int.negSucc 311903, Int.negSucc 137375, Int.ofNat 255312, Int.ofNat 101952, Int.negSucc 38879, Int.negSucc 15119, Int.ofNat 869616, Int.negSucc 269567, Int.ofNat 23328, Int.ofNat 161136, Int.negSucc 77327, Int.ofNat 25488, Int.negSucc 170639, Int.negSucc 35855, Int.negSucc 473039, Int.negSucc 279071, Int.negSucc 386207, Int.ofNat 231552],
    [Int.negSucc 16847, Int.ofNat 21168, Int.ofNat 276048, Int.negSucc 406943, Int.ofNat 130032, Int.ofNat 295488, Int.ofNat 311040, Int.ofNat 179712, Int.negSucc 9071, Int.negSucc 358127, Int.ofNat 599616, Int.negSucc 85967, Int.negSucc 209951, Int.negSucc 25487, Int.negSucc 36287, Int.negSucc 14687, Int.negSucc 269567, Int.ofNat 831600, Int.negSucc 79055, Int.negSucc 125279, Int.ofNat 20304, Int.ofNat 44928, Int.negSucc 9503, Int.ofNat 148608, Int.ofNat 337392, Int.ofNat 162864, Int.ofNat 273456, Int.negSucc 117935],
    [Int.negSucc 28079, Int.negSucc 51407, Int.ofNat 137808, Int.ofNat 168480, Int.ofNat 121392, Int.negSucc 118799, Int.negSucc 112319, Int.negSucc 172799, Int.ofNat 114048, Int.negSucc 98495, Int.negSucc 214271, Int.negSucc 10799, Int.negSucc 485135, Int.ofNat 155952, Int.negSucc 196559, Int.negSucc 287711, Int.ofNat 23328, Int.negSucc 79055, Int.ofNat 1296000, Int.negSucc 347759, Int.ofNat 9072, Int.ofNat 56160, Int.negSucc 219887, Int.negSucc 380159, Int.ofNat 116208, Int.negSucc 390095, Int.negSucc 431135, Int.negSucc 108863],
    [Int.ofNat 147312, Int.negSucc 72143, Int.negSucc 354671, Int.negSucc 206063, Int.negSucc 362015, Int.negSucc 178415, Int.negSucc 152495, Int.negSucc 263519, Int.negSucc 161999, Int.negSucc 306287, Int.negSucc 73871, Int.negSucc 236735, Int.ofNat 461376, Int.negSucc 219455, Int.ofNat 163728, Int.ofNat 5616, Int.ofNat 161136, Int.negSucc 125279, Int.negSucc 347759, Int.ofNat 935280, Int.ofNat 191376, Int.negSucc 19871, Int.negSucc 69983, Int.ofNat 91152, Int.ofNat 26784, Int.ofNat 103680, Int.ofNat 17712, Int.ofNat 558144],
    [Int.ofNat 13392, Int.negSucc 53135, Int.negSucc 54431, Int.negSucc 98927, Int.ofNat 83808, Int.negSucc 182735, Int.ofNat 10800, Int.ofNat 136080, Int.ofNat 483840, Int.negSucc 131759, Int.ofNat 257472, Int.ofNat 253584, Int.ofNat 394416, Int.negSucc 597887, Int.ofNat 137808, Int.ofNat 147312, Int.negSucc 77327, Int.ofNat 20304, Int.ofNat 9072, Int.ofNat 191376, Int.ofNat 870048, Int.negSucc 69119, Int.negSucc 274751, Int.negSucc 201311, Int.ofNat 257904, Int.ofNat 26352, Int.negSucc 95471, Int.negSucc 5183],
    [Int.negSucc 10367, Int.ofNat 19872, Int.negSucc 54431, Int.negSucc 13391, Int.ofNat 5184, Int.negSucc 37151, Int.negSucc 32831, Int.negSucc 46223, Int.ofNat 10368, Int.negSucc 53135, Int.ofNat 68688, Int.ofNat 20304, Int.ofNat 122688, Int.ofNat 59184, Int.negSucc 28943, Int.negSucc 25055, Int.ofNat 25488, Int.ofNat 44928, Int.ofNat 56160, Int.negSucc 19871, Int.negSucc 69119, Int.ofNat 231552, Int.ofNat 55296, Int.negSucc 26351, Int.negSucc 67391, Int.negSucc 87263, Int.negSucc 29375, Int.ofNat 31536],
    [Int.ofNat 3888, Int.ofNat 63504, Int.ofNat 208656, Int.negSucc 541295, Int.ofNat 153792, Int.ofNat 254880, Int.negSucc 147311, Int.ofNat 215136, Int.negSucc 324575, Int.negSucc 362015, Int.negSucc 296351, Int.negSucc 132623, Int.negSucc 139967, Int.ofNat 306720, Int.ofNat 75168, Int.ofNat 158976, Int.negSucc 170639, Int.negSucc 9503, Int.negSucc 219887, Int.negSucc 69983, Int.negSucc 274751, Int.ofNat 55296, Int.ofNat 888192, Int.ofNat 30240, Int.negSucc 95039, Int.ofNat 82512, Int.ofNat 477360, Int.negSucc 215567],
    [Int.ofNat 33264, Int.ofNat 6048, Int.negSucc 140831, Int.ofNat 184464, Int.ofNat 15120, Int.negSucc 24623, Int.ofNat 168912, Int.negSucc 231119, Int.negSucc 263087, Int.ofNat 167616, Int.ofNat 288144, Int.ofNat 28080, Int.ofNat 304992, Int.ofNat 177984, Int.ofNat 47520, Int.ofNat 63504, Int.negSucc 35855, Int.ofNat 148608, Int.negSucc 380159, Int.ofNat 91152, Int.negSucc 201311, Int.negSucc 26351, Int.ofNat 30240, Int.ofNat 591840, Int.negSucc 75167, Int.ofNat 371952, Int.negSucc 42335, Int.ofNat 81216],
    [Int.ofNat 12528, Int.negSucc 1295, Int.ofNat 249696, Int.negSucc 374975, Int.ofNat 131328, Int.ofNat 66528, Int.negSucc 28511, Int.ofNat 40608, Int.negSucc 129167, Int.negSucc 217727, Int.ofNat 678240, Int.ofNat 127440, Int.negSucc 304991, Int.negSucc 235439, Int.negSucc 11663, Int.negSucc 73007, Int.negSucc 473039, Int.ofNat 337392, Int.ofNat 116208, Int.ofNat 26784, Int.ofNat 257904, Int.negSucc 67391, Int.negSucc 95039, Int.negSucc 75167, Int.ofNat 745632, Int.ofNat 150336, Int.ofNat 362448, Int.ofNat 7776],
    [Int.ofNat 47088, Int.ofNat 23328, Int.ofNat 144288, Int.negSucc 149903, Int.ofNat 448416, Int.negSucc 69983, Int.ofNat 187488, Int.negSucc 55727, Int.negSucc 181439, Int.negSucc 77327, Int.ofNat 277776, Int.ofNat 113616, Int.ofNat 235008, Int.negSucc 22895, Int.ofNat 21168, Int.ofNat 52704, Int.negSucc 279071, Int.ofNat 162864, Int.negSucc 390095, Int.ofNat 103680, Int.ofNat 26352, Int.negSucc 87263, Int.ofNat 82512, Int.ofNat 371952, Int.ofNat 150336, Int.ofNat 647136, Int.ofNat 106272, Int.ofNat 51840],
    [Int.ofNat 33696, Int.ofNat 16848, Int.ofNat 201312, Int.negSucc 641087, Int.ofNat 40608, Int.ofNat 379728, Int.negSucc 209087, Int.ofNat 241920, Int.negSucc 385343, Int.negSucc 317087, Int.ofNat 293760, Int.negSucc 83807, Int.negSucc 585791, Int.ofNat 131760, Int.ofNat 2592, Int.negSucc 5183, Int.negSucc 386207, Int.ofNat 273456, Int.negSucc 431135, Int.ofNat 17712, Int.negSucc 95471, Int.negSucc 29375, Int.ofNat 477360, Int.negSucc 42335, Int.ofNat 362448, Int.ofNat 106272, Int.ofNat 1000512, Int.negSucc 11663],
    [Int.ofNat 129600, Int.negSucc 74735, Int.negSucc 165023, Int.ofNat 101520, Int.negSucc 122687, Int.negSucc 258335, Int.negSucc 287711, Int.negSucc 342575, Int.negSucc 110159, Int.negSucc 94607, Int.ofNat 154656, Int.negSucc 423359, Int.ofNat 197856, Int.negSucc 40607, Int.negSucc 84239, Int.negSucc 129599, Int.ofNat 231552, Int.negSucc 117935, Int.negSucc 108863, Int.ofNat 558144, Int.negSucc 5183, Int.ofNat 31536, Int.negSucc 215567, Int.ofNat 81216, Int.ofNat 7776, Int.ofNat 51840, Int.negSucc 11663, Int.ofNat 731376]
  ],
  W := [
    [Int.ofNat 3004],
    [Int.ofNat 364, Int.ofNat 2961],
    [Int.negSucc 28, Int.ofNat 58, Int.ofNat 2413],
    [Int.negSucc 30, Int.negSucc 45, Int.negSucc 1114, Int.ofNat 2839],
    [Int.ofNat 17, Int.ofNat 35, Int.ofNat 1466, Int.ofNat 487, Int.ofNat 1898],
    [Int.negSucc 59, Int.ofNat 55, Int.ofNat 633, Int.ofNat 246, Int.negSucc 1153, Int.ofNat 2309],
    [Int.negSucc 53, Int.ofNat 47, Int.ofNat 239, Int.ofNat 619, Int.ofNat 326, Int.ofNat 58, Int.ofNat 2231],
    [Int.negSucc 92, Int.ofNat 79, Int.negSucc 511, Int.negSucc 398, Int.ofNat 752, Int.negSucc 669, Int.ofNat 588, Int.ofNat 2403],
    [Int.negSucc 70, Int.negSucc 7, Int.ofNat 486, Int.ofNat 890, Int.negSucc 651, Int.ofNat 558, Int.ofNat 447, Int.negSucc 547, Int.ofNat 2163],
    [Int.negSucc 59, Int.ofNat 8, Int.ofNat 350, Int.ofNat 770, Int.negSucc 95, Int.negSucc 981, Int.negSucc 526, Int.negSucc 623, Int.ofNat 32, Int.ofNat 2083],
    [Int.ofNat 30, Int.negSucc 9, Int.ofNat 245, Int.ofNat 481, Int.ofNat 100, Int.negSucc 174, Int.negSucc 284, Int.ofNat 38, Int.ofNat 488, Int.ofNat 157, Int.ofNat 2884],
    [Int.negSucc 108, Int.ofNat 66, Int.negSucc 236, Int.negSucc 681, Int.ofNat 119, Int.ofNat 144, Int.negSucc 386, Int.negSucc 316, Int.ofNat 445, Int.ofNat 822, Int.ofNat 347, Int.ofNat 1963],
    [Int.ofNat 55, Int.negSucc 7, Int.negSucc 189, Int.ofNat 381, Int.ofNat 556, Int.negSucc 214, Int.negSucc 69, Int.negSucc 257, Int.negSucc 209, Int.negSucc 321, Int.negSucc 243, Int.ofNat 419, Int.ofNat 2765],
    [Int.ofNat 3, Int.ofNat 21, Int.negSucc 114, Int.ofNat 17, Int.ofNat 183, Int.ofNat 473, Int.negSucc 85, Int.negSucc 210, Int.negSucc 914, Int.ofNat 195, Int.negSucc 135, Int.negSucc 399, Int.negSucc 592, Int.ofNat 1315],
    [Int.negSucc 19, Int.ofNat 19, Int.negSucc 207, Int.negSucc 397, Int.negSucc 353, Int.ofNat 147, Int.ofNat 393, Int.ofNat 175, Int.negSucc 1, Int.ofNat 167, Int.negSucc 155, Int.ofNat 260, Int.ofNat 497, Int.negSucc 172, Int.ofNat 1059],
    [Int.negSucc 81, Int.ofNat 74, Int.negSucc 273, Int.negSucc 377, Int.negSucc 256, Int.ofNat 176, Int.ofNat 62, Int.ofNat 250, Int.ofNat 253, Int.negSucc 71, Int.negSucc 227, Int.ofNat 244, Int.ofNat 358, Int.ofNat 4, Int.ofNat 479, Int.ofNat 1197],
    [Int.ofNat 24, Int.negSucc 56, Int.negSucc 206, Int.negSucc 147, Int.negSucc 269, Int.negSucc 549, Int.negSucc 304, Int.negSucc 108, Int.ofNat 352, Int.ofNat 268, Int.negSucc 516, Int.negSucc 474, Int.ofNat 453, Int.ofNat 704, Int.negSucc 223, Int.negSucc 186, Int.ofNat 1188],
    [Int.negSucc 21, Int.ofNat 31, Int.ofNat 456, Int.negSucc 393, Int.ofNat 22, Int.ofNat 439, Int.ofNat 602, Int.ofNat 297, Int.negSucc 112, Int.negSucc 168, Int.ofNat 968, Int.negSucc 199, Int.negSucc 57, Int.negSucc 147, Int.negSucc 300, Int.ofNat 152, Int.ofNat 4, Int.ofNat 1056],
    [Int.negSucc 36, Int.negSucc 64, Int.ofNat 230, Int.ofNat 326, Int.negSucc 3, Int.negSucc 304, Int.negSucc 307, Int.negSucc 191, Int.ofNat 116, Int.negSucc 629, Int.negSucc 401, Int.ofNat 358, Int.negSucc 932, Int.ofNat 371, Int.ofNat 63, Int.negSucc 663, Int.ofNat 38, Int.ofNat 544, Int.ofNat 1516],
    [Int.ofNat 196, Int.negSucc 121, Int.negSucc 582, Int.negSucc 518, Int.negSucc 178, Int.negSucc 175, Int.negSucc 28, Int.negSucc 622, Int.negSucc 109, Int.negSucc 575, Int.ofNat 82, Int.negSucc 548, Int.ofNat 673, Int.negSucc 569, Int.ofNat 221, Int.negSucc 310, Int.ofNat 233, Int.negSucc 358, Int.negSucc 385, Int.ofNat 821],
    [Int.ofNat 18, Int.negSucc 73, Int.negSucc 87, Int.negSucc 174, Int.ofNat 291, Int.negSucc 125, Int.ofNat 40, Int.ofNat 46, Int.ofNat 1110, Int.negSucc 211, Int.ofNat 203, Int.ofNat 257, Int.ofNat 564, Int.negSucc 650, Int.ofNat 163, Int.negSucc 0, Int.negSucc 168, Int.negSucc 1, Int.ofNat 386, Int.ofNat 238, Int.ofNat 949],
    [Int.negSucc 13, Int.ofNat 29, Int.negSucc 90, Int.negSucc 53, Int.ofNat 95, Int.ofNat 13, Int.negSucc 48, Int.negSucc 120, Int.ofNat 66, Int.negSucc 105, Int.ofNat 101, Int.negSucc 13, Int.ofNat 152, Int.ofNat 269, Int.negSucc 72, Int.negSucc 93, Int.negSucc 134, Int.ofNat 177, Int.ofNat 63, Int.negSucc 152, Int.negSucc 350, Int.ofNat 713],
    [Int.ofNat 5, Int.ofNat 85, Int.ofNat 344, Int.negSucc 625, Int.ofNat 218, Int.ofNat 521, Int.negSucc 173, Int.ofNat 445, Int.negSucc 339, Int.negSucc 171, Int.negSucc 267, Int.negSucc 266, Int.negSucc 87, Int.ofNat 453, Int.ofNat 274, Int.ofNat 273, Int.negSucc 525, Int.negSucc 436, Int.negSucc 307, Int.negSucc 78, Int.negSucc 391, Int.ofNat 106, Int.ofNat 1030],
    [Int.ofNat 44, Int.ofNat 3, Int.negSucc 232, Int.ofNat 169, Int.ofNat 168, Int.ofNat 88, Int.ofNat 255, Int.negSucc 494, Int.negSucc 652, Int.ofNat 275, Int.ofNat 517, Int.negSucc 14, Int.ofNat 365, Int.ofNat 119, Int.ofNat 112, Int.ofNat 430, Int.ofNat 188, Int.ofNat 184, Int.negSucc 381, Int.negSucc 127, Int.negSucc 79, Int.negSucc 324, Int.ofNat 323, Int.ofNat 574],
    [Int.ofNat 17, Int.negSucc 3, Int.ofNat 414, Int.negSucc 365, Int.ofNat 51, Int.ofNat 67, Int.negSucc 2, Int.ofNat 99, Int.negSucc 156, Int.negSucc 286, Int.ofNat 1009, Int.ofNat 169, Int.negSucc 340, Int.negSucc 754, Int.ofNat 81, Int.negSucc 36, Int.negSucc 310, Int.negSucc 141, Int.ofNat 483, Int.ofNat 51, Int.ofNat 311, Int.negSucc 52, Int.negSucc 266, Int.negSucc 103, Int.ofNat 483],
    [Int.ofNat 63, Int.ofNat 24, Int.ofNat 239, Int.negSucc 115, Int.ofNat 789, Int.ofNat 221, Int.ofNat 223, Int.negSucc 298, Int.negSucc 279, Int.negSucc 31, Int.ofNat 445, Int.ofNat 153, Int.ofNat 199, Int.negSucc 278, Int.ofNat 178, Int.ofNat 367, Int.negSucc 75, Int.negSucc 123, Int.negSucc 503, Int.ofNat 52, Int.negSucc 70, Int.negSucc 484, Int.negSucc 106, Int.ofNat 535, Int.negSucc 27, Int.ofNat 508],
    [Int.ofNat 45, Int.ofNat 17, Int.ofNat 334, Int.negSucc 770, Int.ofNat 25, Int.ofNat 662, Int.negSucc 216, Int.ofNat 577, Int.negSucc 440, Int.ofNat 59, Int.ofNat 589, Int.negSucc 424, Int.negSucc 534, Int.negSucc 348, Int.ofNat 63, Int.ofNat 48, Int.negSucc 395, Int.negSucc 433, Int.negSucc 602, Int.negSucc 119, Int.ofNat 339, Int.ofNat 331, Int.ofNat 152, Int.negSucc 168, Int.negSucc 103, Int.negSucc 245, Int.ofNat 470],
    [Int.ofNat 173, Int.negSucc 121, Int.negSucc 267, Int.ofNat 37, Int.negSucc 59, Int.negSucc 400, Int.negSucc 471, Int.negSucc 587, Int.negSucc 119, Int.negSucc 629, Int.ofNat 222, Int.negSucc 770, Int.ofNat 227, Int.negSucc 217, Int.ofNat 135, Int.negSucc 204, Int.ofNat 357, Int.negSucc 122, Int.negSucc 384, Int.ofNat 148, Int.negSucc 3, Int.ofNat 89, Int.negSucc 462, Int.ofNat 198, Int.ofNat 30, Int.negSucc 115, Int.ofNat 140, Int.ofNat 455]
  ]
}

def blockCert4 : OrbitBlockCert := {
  r := 23, m := 38, copies := 12, S := 2,
  blk := [(0, 6), (1, 7), (2, 8), (3, 5), (4, 6), (5, 10), (6, 11), (6, 25), (7, 26), (8, 9), (8, 27), (9, 13), (10, 28), (11, 29), (12, 1), (13, 2), (13, 30), (14, 6), (15, 20), (16, 21), (18, 19), (19, 23), (20, 31), (21, 32), (23, 33), (24, 16), (25, 29), (26, 12), (27, 13), (28, 3), (29, 0), (29, 4), (29, 14), (29, 34), (30, 8), (32, 24), (33, 18), (34, 6)],
  Qcols := [
    [(19, Int.negSucc 0)],
    [(4, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.ofNat 1), (13, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.ofNat 1)],
    [(5, Int.ofNat 1), (6, Int.negSucc 0), (9, Int.ofNat 1), (12, Int.ofNat 1), (22, Int.ofNat 1)],
    [(4, Int.ofNat 1), (5, Int.ofNat 1), (6, Int.negSucc 0), (9, Int.negSucc 0), (12, Int.ofNat 1), (18, Int.ofNat 1)],
    [(9, Int.ofNat 1), (10, Int.ofNat 1), (13, Int.negSucc 0), (18, Int.ofNat 1), (19, Int.ofNat 1), (21, Int.negSucc 0)],
    [(4, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.negSucc 0), (10, Int.negSucc 0), (16, Int.ofNat 1), (19, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(7, Int.ofNat 2), (12, Int.negSucc 0), (18, Int.ofNat 1), (22, Int.negSucc 1)],
    [(8, Int.negSucc 0), (9, Int.negSucc 0), (12, Int.ofNat 1), (22, Int.ofNat 1)],
    [(8, Int.ofNat 1), (9, Int.ofNat 1), (12, Int.negSucc 0), (13, Int.negSucc 2), (22, Int.ofNat 2)],
    [(4, Int.negSucc 0), (10, Int.negSucc 0), (12, Int.negSucc 0), (16, Int.ofNat 1), (18, Int.negSucc 1), (19, Int.negSucc 1), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(5, Int.ofNat 1), (6, Int.negSucc 0), (9, Int.ofNat 1), (10, Int.ofNat 1), (12, Int.ofNat 1), (18, Int.ofNat 1), (22, Int.ofNat 1)],
    [(5, Int.negSucc 0), (6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.ofNat 1), (22, Int.negSucc 0)],
    [(8, Int.ofNat 1), (9, Int.ofNat 1), (12, Int.negSucc 0), (16, Int.ofNat 3), (22, Int.negSucc 0)],
    [(8, Int.negSucc 1), (9, Int.negSucc 1), (12, Int.negSucc 0), (20, Int.negSucc 2), (22, Int.negSucc 0)],
    [(4, Int.negSucc 0), (5, Int.negSucc 0), (6, Int.ofNat 1), (8, Int.negSucc 0), (19, Int.ofNat 1), (22, Int.ofNat 1)],
    [(4, Int.ofNat 1), (7, Int.negSucc 0), (10, Int.ofNat 1), (12, Int.negSucc 0), (13, Int.negSucc 0), (19, Int.negSucc 0), (21, Int.negSucc 0)],
    [(5, Int.negSucc 0), (6, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.ofNat 1), (10, Int.negSucc 0), (20, Int.ofNat 1), (22, Int.negSucc 0)],
    [(8, Int.ofNat 1), (10, Int.negSucc 0), (16, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.negSucc 0)],
    [(1, Int.negSucc 0), (7, Int.ofNat 1), (11, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 0), (18, Int.negSucc 0), (19, Int.ofNat 2), (20, Int.negSucc 0), (22, Int.negSucc 0)],
    [(7, Int.negSucc 0), (11, Int.ofNat 3), (12, Int.negSucc 0), (18, Int.ofNat 1), (22, Int.ofNat 1)],
    [(0, Int.negSucc 0), (1, Int.ofNat 1), (2, Int.negSucc 0), (5, Int.ofNat 1), (6, Int.ofNat 1), (10, Int.ofNat 1), (11, Int.negSucc 1), (12, Int.ofNat 1), (13, Int.ofNat 2), (15, Int.ofNat 1), (17, Int.ofNat 2), (18, Int.negSucc 0), (19, Int.negSucc 1), (20, Int.negSucc 0), (21, Int.ofNat 2), (22, Int.ofNat 1)],
    [(7, Int.negSucc 0), (12, Int.negSucc 0), (15, Int.negSucc 2), (18, Int.ofNat 1), (22, Int.ofNat 1)],
    [(2, Int.negSucc 0), (8, Int.negSucc 0), (9, Int.negSucc 0), (11, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 1), (15, Int.ofNat 1), (16, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.ofNat 1)],
    [(3, Int.ofNat 1), (6, Int.ofNat 1), (9, Int.ofNat 1), (10, Int.negSucc 0), (11, Int.ofNat 1), (18, Int.negSucc 1), (20, Int.ofNat 1), (21, Int.negSucc 1)],
    [(3, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (8, Int.ofNat 1), (10, Int.ofNat 1), (15, Int.negSucc 0), (17, Int.negSucc 1), (21, Int.ofNat 2), (22, Int.ofNat 2)],
    [(0, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (10, Int.negSucc 0), (14, Int.negSucc 0), (15, Int.ofNat 1), (16, Int.negSucc 1), (21, Int.negSucc 1), (22, Int.ofNat 1)],
    [(7, Int.ofNat 1), (12, Int.ofNat 1), (14, Int.ofNat 3), (18, Int.negSucc 0), (22, Int.ofNat 2)],
    [(0, Int.negSucc 0), (5, Int.negSucc 0), (8, Int.negSucc 0), (11, Int.negSucc 0), (13, Int.ofNat 1), (15, Int.ofNat 2), (16, Int.negSucc 0), (18, Int.ofNat 1), (21, Int.negSucc 0)],
    [(3, Int.negSucc 0), (8, Int.ofNat 1), (10, Int.negSucc 0), (11, Int.ofNat 1), (12, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.ofNat 2), (21, Int.negSucc 0), (22, Int.negSucc 0)],
    [(0, Int.ofNat 1), (1, Int.negSucc 0), (2, Int.ofNat 1), (5, Int.ofNat 1), (9, Int.negSucc 0), (11, Int.negSucc 0), (12, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 0), (16, Int.negSucc 0), (17, Int.ofNat 1), (19, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 2)],
    [(1, Int.ofNat 1), (18, Int.ofNat 1), (19, Int.ofNat 1)],
    [(6, Int.negSucc 0), (10, Int.negSucc 0), (11, Int.ofNat 1), (17, Int.negSucc 0)],
    [(6, Int.ofNat 1), (7, Int.negSucc 0), (10, Int.ofNat 1), (15, Int.negSucc 0), (20, Int.negSucc 0)],
    [(14, Int.ofNat 1), (17, Int.ofNat 1)],
    [(3, Int.ofNat 1), (9, Int.ofNat 1), (10, Int.ofNat 1), (12, Int.negSucc 0), (15, Int.negSucc 0), (17, Int.ofNat 2), (20, Int.ofNat 1), (21, Int.ofNat 1)],
    [(3, Int.ofNat 1), (5, Int.negSucc 0), (6, Int.negSucc 0), (7, Int.ofNat 1), (10, Int.negSucc 0), (14, Int.ofNat 1), (17, Int.negSucc 0), (21, Int.ofNat 2), (22, Int.ofNat 1)],
    [(3, Int.negSucc 0), (5, Int.ofNat 1), (6, Int.ofNat 1), (10, Int.ofNat 1), (12, Int.ofNat 1), (14, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.negSucc 1), (22, Int.ofNat 1)],
    [(2, Int.ofNat 1), (14, Int.negSucc 0), (17, Int.negSucc 1), (20, Int.negSucc 0)]
  ],
  A := [
    [Int.ofNat 2194560, Int.negSucc 472607, Int.ofNat 71280, Int.negSucc 445391, Int.ofNat 111024, Int.negSucc 264383, Int.negSucc 206927, Int.ofNat 220320, Int.negSucc 292463, Int.ofNat 427248, Int.ofNat 597888, Int.negSucc 371087, Int.negSucc 316223, Int.ofNat 694224, Int.ofNat 408672, Int.negSucc 270863, Int.ofNat 22896, Int.negSucc 683855, Int.ofNat 336528, Int.negSucc 210815, Int.ofNat 491184, Int.ofNat 109296, Int.negSucc 31967],
    [Int.negSucc 472607, Int.ofNat 2806704, Int.negSucc 514079, Int.ofNat 1582416, Int.negSucc 1206575, Int.negSucc 215567, Int.negSucc 317519, Int.negSucc 755999, Int.ofNat 927504, Int.negSucc 1575503, Int.negSucc 598319, Int.ofNat 228528, Int.ofNat 1430352, Int.negSucc 1933631, Int.negSucc 1402271, Int.negSucc 63071, Int.ofNat 667440, Int.ofNat 2214432, Int.negSucc 1804031, Int.ofNat 806976, Int.negSucc 1627775, Int.ofNat 119232, Int.negSucc 220751],
    [Int.ofNat 71280, Int.negSucc 514079, Int.ofNat 1145664, Int.negSucc 445823, Int.ofNat 402624, Int.negSucc 5183, Int.ofNat 172368, Int.ofNat 260928, Int.negSucc 495935, Int.ofNat 395280, Int.ofNat 450144, Int.negSucc 146447, Int.negSucc 191375, Int.ofNat 686448, Int.ofNat 633312, Int.negSucc 30671, Int.negSucc 316223, Int.negSucc 910223, Int.ofNat 466992, Int.negSucc 281663, Int.ofNat 976320, Int.negSucc 18143, Int.ofNat 39744],
    [Int.negSucc 445391, Int.ofNat 1582416, Int.negSucc 445823, Int.ofNat 4078008, Int.negSucc 2047247, Int.ofNat 983232, Int.ofNat 1407024, Int.negSucc 105035, Int.ofNat 2193696, Int.negSucc 2086127, Int.negSucc 535679, Int.ofNat 403056, Int.ofNat 1471824, Int.negSucc 1413071, Int.negSucc 1099007, Int.negSucc 110159, Int.ofNat 665280, Int.ofNat 1766448, Int.negSucc 1254095, Int.ofNat 122688, Int.negSucc 1442879, Int.ofNat 61776, Int.negSucc 338687],
    [Int.ofNat 111024, Int.negSucc 1206575, Int.ofNat 402624, Int.negSucc 2047247, Int.ofNat 2287872, Int.negSucc 568511, Int.negSucc 231119, Int.ofNat 969408, Int.negSucc 998783, Int.ofNat 1562976, Int.ofNat 812160, Int.ofNat 310176, Int.negSucc 926207, Int.ofNat 1237248, Int.ofNat 747792, Int.ofNat 382320, Int.negSucc 526175, Int.negSucc 1770335, Int.ofNat 790128, Int.negSucc 443663, Int.ofNat 1308528, Int.negSucc 133055, Int.ofNat 241488],
    [Int.negSucc 264383, Int.negSucc 215567, Int.negSucc 5183, Int.ofNat 983232, Int.negSucc 568511, Int.ofNat 1201392, Int.ofNat 1032048, Int.negSucc 39743, Int.ofNat 394848, Int.negSucc 443231, Int.negSucc 193967, Int.ofNat 108000, Int.negSucc 167615, Int.negSucc 357695, Int.ofNat 261360, Int.ofNat 209520, Int.negSucc 638927, Int.negSucc 305855, Int.ofNat 130464, Int.negSucc 83807, Int.ofNat 230256, Int.ofNat 22032, Int.negSucc 114479],
    [Int.negSucc 206927, Int.negSucc 317519, Int.ofNat 172368, Int.ofNat 1407024, Int.negSucc 231119, Int.ofNat 1032048, Int.ofNat 2012256, Int.ofNat 1024272, Int.ofNat 687744, Int.ofNat 35856, Int.negSucc 180575, Int.ofNat 252288, Int.ofNat 371088, Int.negSucc 172799, Int.ofNat 89424, Int.negSucc 269999, Int.negSucc 560303, Int.negSucc 514943, Int.ofNat 173232, Int.negSucc 702431, Int.ofNat 323136, Int.ofNat 65232, Int.negSucc 153791],
    [Int.ofNat 220320, Int.negSucc 755999, Int.ofNat 260928, Int.negSucc 105035, Int.ofNat 969408, Int.negSucc 39743, Int.ofNat 1024272, Int.ofNat 1623456, Int.ofNat 119232, Int.ofNat 918432, Int.ofNat 434160, Int.ofNat 105408, Int.negSucc 102815, Int.ofNat 673056, Int.ofNat 196560, Int.negSucc 489455, Int.negSucc 259199, Int.negSucc 1130975, Int.ofNat 377136, Int.negSucc 761183, Int.ofNat 715392, Int.negSucc 38879, Int.ofNat 12528],
    [Int.negSucc 292463, Int.ofNat 927504, Int.negSucc 495935, Int.ofNat 2193696, Int.negSucc 998783, Int.ofNat 394848, Int.ofNat 687744, Int.ofNat 119232, Int.ofNat 2174688, Int.negSucc 1474415, Int.negSucc 470879, Int.ofNat 635472, Int.ofNat 816048, Int.negSucc 1545695, Int.negSucc 1060127, Int.ofNat 313200, Int.ofNat 43632, Int.ofNat 1575072, Int.negSucc 717551, Int.ofNat 47952, Int.negSucc 1523231, Int.negSucc 168047, Int.ofNat 63072],
    [Int.ofNat 427248, Int.negSucc 1575503, Int.ofNat 395280, Int.negSucc 2086127, Int.ofNat 1562976, Int.negSucc 443231, Int.ofNat 35856, Int.ofNat 918432, Int.negSucc 1474415, Int.ofNat 2272320, Int.ofNat 421632, Int.negSucc 608687, Int.negSucc 912815, Int.ofNat 1852416, Int.ofNat 986688, Int.negSucc 465695, Int.negSucc 160703, Int.negSucc 1958687, Int.ofNat 988416, Int.negSucc 644543, Int.ofNat 1391472, Int.ofNat 72576, Int.ofNat 81216],
    [Int.ofNat 597888, Int.negSucc 598319, Int.ofNat 450144, Int.negSucc 535679, Int.ofNat 812160, Int.negSucc 193967, Int.negSucc 180575, Int.ofNat 434160, Int.negSucc 470879, Int.ofNat 421632, Int.ofNat 1133568, Int.ofNat 216864, Int.negSucc 322703, Int.ofNat 902016, Int.ofNat 660528, Int.ofNat 232416, Int.negSucc 306287, Int.negSucc 1368575, Int.ofNat 261360, Int.negSucc 218159, Int.ofNat 1254096, Int.ofNat 50544, Int.negSucc 120095],
    [Int.negSucc 371087, Int.ofNat 228528, Int.negSucc 146447, Int.ofNat 403056, Int.ofNat 310176, Int.ofNat 108000, Int.ofNat 252288, Int.ofNat 105408, Int.ofNat 635472, Int.negSucc 608687, Int.ofNat 216864, Int.ofNat 1398384, Int.ofNat 372384, Int.negSucc 781919, Int.negSucc 247967, Int.ofNat 989280, Int.negSucc 392687, Int.ofNat 387504, Int.negSucc 73007, Int.negSucc 131759, Int.negSucc 288575, Int.negSucc 5183, Int.negSucc 104975],
    [Int.negSucc 316223, Int.ofNat 1430352, Int.negSucc 191375, Int.ofNat 1471824, Int.negSucc 926207, Int.negSucc 167615, Int.ofNat 371088, Int.negSucc 102815, Int.ofNat 816048, Int.negSucc 912815, Int.negSucc 322703, Int.ofNat 372384, Int.ofNat 1662768, Int.negSucc 1390175, Int.negSucc 838943, Int.negSucc 204767, Int.ofNat 297216, Int.ofNat 1372032, Int.negSucc 1107215, Int.ofNat 46224, Int.negSucc 957311, Int.ofNat 171072, Int.negSucc 429839],
    [Int.ofNat 694224, Int.negSucc 1933631, Int.ofNat 686448, Int.negSucc 1413071, Int.ofNat 1237248, Int.negSucc 357695, Int.negSucc 172799, Int.ofNat 673056, Int.negSucc 1545695, Int.ofNat 1852416, Int.ofNat 902016, Int.negSucc 781919, Int.negSucc 1390175, Int.ofNat 3306096, Int.ofNat 1318032, Int.negSucc 470447, Int.ofNat 532174, Int.negSucc 2377295, Int.ofNat 1459296, Int.negSucc 551231, Int.ofNat 1951344, Int.negSucc 37583, Int.ofNat 277776],
    [Int.ofNat 408672, Int.negSucc 1402271, Int.ofNat 633312, Int.negSucc 1099007, Int.ofNat 747792, Int.ofNat 261360, Int.ofNat 89424, Int.ofNat 196560, Int.negSucc 1060127, Int.ofNat 986688, Int.ofNat 660528, Int.negSucc 247967, Int.negSucc 838943, Int.ofNat 1318032, Int.ofNat 1318464, Int.ofNat 170208, Int.negSucc 603071, Int.negSucc 1855439, Int.ofNat 998352, Int.negSucc 431999, Int.ofNat 1558656, Int.ofNat 7344, Int.negSucc 64367],
    [Int.negSucc 270863, Int.negSucc 63071, Int.negSucc 30671, Int.negSucc 110159, Int.ofNat 382320, Int.ofNat 209520, Int.negSucc 269999, Int.negSucc 489455, Int.ofNat 313200, Int.negSucc 465695, Int.ofNat 232416, Int.ofNat 989280, Int.negSucc 204767, Int.negSucc 470447, Int.ofNat 170208, Int.ofNat 1475280, Int.negSucc 480383, Int.ofNat 97632, Int.ofNat 78624, Int.ofNat 154656, Int.negSucc 123551, Int.negSucc 53999, Int.ofNat 38448],
    [Int.ofNat 22896, Int.ofNat 667440, Int.negSucc 316223, Int.ofNat 665280, Int.negSucc 526175, Int.negSucc 638927, Int.negSucc 560303, Int.negSucc 259199, Int.ofNat 43632, Int.negSucc 160703, Int.negSucc 306287, Int.negSucc 392687, Int.ofNat 297216, Int.ofNat 532174, Int.negSucc 603071, Int.negSucc 480383, Int.ofNat 1731456, Int.ofNat 1031616, Int.negSucc 486863, Int.ofNat 333936, Int.negSucc 908927, Int.ofNat 89424, Int.ofNat 49680],
    [Int.negSucc 683855, Int.ofNat 2214432, Int.negSucc 910223, Int.ofNat 1766448, Int.negSucc 1770335, Int.negSucc 305855, Int.negSucc 514943, Int.negSucc 1130975, Int.ofNat 1575072, Int.negSucc 1958687, Int.negSucc 1368575, Int.ofNat 387504, Int.ofNat 1372032, Int.negSucc 2377295, Int.negSucc 1855439, Int.ofNat 97632, Int.ofNat 1031616, Int.ofNat 3506976, Int.negSucc 1398383, Int.ofNat 807408, Int.negSucc 2857247, Int.ofNat 22464, Int.ofNat 14256],
    [Int.ofNat 336528, Int.negSucc 1804031, Int.ofNat 466992, Int.negSucc 1254095, Int.ofNat 790128, Int.ofNat 130464, Int.ofNat 173232, Int.ofNat 377136, Int.negSucc 717551, Int.ofNat 988416, Int.ofNat 261360, Int.negSucc 73007, Int.negSucc 1107215, Int.ofNat 1459296, Int.ofNat 998352, Int.ofNat 78624, Int.negSucc 486863, Int.negSucc 1398383, Int.ofNat 1629936, Int.negSucc 625967, Int.ofNat 1097712, Int.negSucc 155951, Int.ofNat 308880],
    [Int.negSucc 210815, Int.ofNat 806976, Int.negSucc 281663, Int.ofNat 122688, Int.negSucc 443663, Int.negSucc 83807, Int.negSucc 702431, Int.negSucc 761183, Int.ofNat 47952, Int.negSucc 644543, Int.negSucc 218159, Int.negSucc 131759, Int.ofNat 46224, Int.negSucc 551231, Int.negSucc 431999, Int.ofNat 154656, Int.ofNat 333936, Int.ofNat 807408, Int.negSucc 625967, Int.ofNat 746064, Int.negSucc 574127, Int.ofNat 14256, Int.ofNat 68688],
    [Int.ofNat 491184, Int.negSucc 1627775, Int.ofNat 976320, Int.negSucc 1442879, Int.ofNat 1308528, Int.ofNat 230256, Int.ofNat 323136, Int.ofNat 715392, Int.negSucc 1523231, Int.ofNat 1391472, Int.ofNat 1254096, Int.negSucc 288575, Int.negSucc 957311, Int.ofNat 1951344, Int.ofNat 1558656, Int.negSucc 123551, Int.negSucc 908927, Int.negSucc 2857247, Int.ofNat 1097712, Int.negSucc 574127, Int.ofNat 2625264, Int.ofNat 13392, Int.negSucc 66527],
    [Int.ofNat 109296, Int.ofNat 119232, Int.negSucc 18143, Int.ofNat 61776, Int.negSucc 133055, Int.ofNat 22032, Int.ofNat 65232, Int.negSucc 38879, Int.negSucc 168047, Int.ofNat 72576, Int.ofNat 50544, Int.negSucc 5183, Int.ofNat 171072, Int.negSucc 37583, Int.ofNat 7344, Int.negSucc 53999, Int.ofNat 89424, Int.ofNat 22464, Int.negSucc 155951, Int.ofNat 14256, Int.ofNat 13392, Int.ofNat 260496, Int.negSucc 154655],
    [Int.negSucc 31967, Int.negSucc 220751, Int.ofNat 39744, Int.negSucc 338687, Int.ofNat 241488, Int.negSucc 114479, Int.negSucc 153791, Int.ofNat 12528, Int.ofNat 63072, Int.ofNat 81216, Int.negSucc 120095, Int.negSucc 104975, Int.negSucc 429839, Int.ofNat 277776, Int.negSucc 64367, Int.ofNat 38448, Int.ofNat 49680, Int.ofNat 14256, Int.ofNat 308880, Int.ofNat 68688, Int.negSucc 66527, Int.negSucc 154655, Int.ofNat 390096]
  ],
  W := [
    [Int.ofNat 2959],
    [Int.negSucc 638, Int.ofNat 3286],
    [Int.ofNat 96, Int.negSucc 606, Int.ofNat 2046],
    [Int.negSucc 601, Int.ofNat 1809, Int.negSucc 306, Int.ofNat 3544],
    [Int.ofNat 150, Int.negSucc 1439, Int.ofNat 353, Int.negSucc 1519, Int.ofNat 2145],
    [Int.negSucc 356, Int.negSucc 331, Int.negSucc 91, Int.ofNat 1210, Int.negSucc 384, Int.ofNat 1710],
    [Int.negSucc 279, Int.negSucc 440, Int.ofNat 219, Int.ofNat 1784, Int.ofNat 521, Int.ofNat 1136, Int.ofNat 1721],
    [Int.ofNat 298, Int.negSucc 861, Int.ofNat 240, Int.ofNat 393, Int.ofNat 1447, Int.negSucc 136, Int.ofNat 1423, Int.ofNat 1137],
    [Int.negSucc 394, Int.ofNat 1052, Int.negSucc 638, Int.ofNat 1816, Int.ofNat 263, Int.negSucc 214, Int.ofNat 65, Int.ofNat 387, Int.ofNat 1854],
    [Int.ofNat 577, Int.negSucc 1805, Int.ofNat 210, Int.negSucc 1315, Int.ofNat 695, Int.negSucc 166, Int.ofNat 952, Int.ofNat 25, Int.negSucc 826, Int.ofNat 1263],
    [Int.ofNat 808, Int.negSucc 570, Int.ofNat 673, Int.negSucc 117, Int.ofNat 880, Int.negSucc 77, Int.negSucc 612, Int.ofNat 419, Int.negSucc 371, Int.negSucc 369, Int.ofNat 1209],
    [Int.negSucc 501, Int.ofNat 181, Int.negSucc 208, Int.ofNat 259, Int.ofNat 953, Int.ofNat 203, Int.negSucc 112, Int.negSucc 452, Int.ofNat 822, Int.negSucc 999, Int.ofNat 646, Int.ofNat 1385],
    [Int.negSucc 426, Int.ofNat 1658, Int.ofNat 138, Int.ofNat 754, Int.negSucc 72, Int.negSucc 701, Int.ofNat 904, Int.negSucc 404, Int.ofNat 19, Int.negSucc 275, Int.ofNat 526, Int.ofNat 223, Int.ofNat 1109],
    [Int.ofNat 938, Int.negSucc 2170, Int.ofNat 654, Int.negSucc 270, Int.ofNat 485, Int.negSucc 725, Int.negSucc 275, Int.ofNat 71, Int.negSucc 1569, Int.ofNat 758, Int.ofNat 125, Int.negSucc 291, Int.negSucc 1265, Int.ofNat 1233],
    [Int.ofNat 552, Int.negSucc 1599, Int.ofNat 738, Int.negSucc 265, Int.negSucc 27, Int.ofNat 638, Int.negSucc 342, Int.negSucc 188, Int.negSucc 616, Int.ofNat 143, Int.ofNat 431, Int.negSucc 41, Int.ofNat 130, Int.ofNat 116, Int.ofNat 771],
    [Int.negSucc 365, Int.negSucc 147, Int.negSucc 86, Int.negSucc 117, Int.ofNat 569, Int.ofNat 592, Int.negSucc 1153, Int.negSucc 887, Int.ofNat 981, Int.negSucc 332, Int.ofNat 526, Int.ofNat 822, Int.negSucc 52, Int.negSucc 29, Int.ofNat 291, Int.ofNat 891],
    [Int.ofNat 31, Int.ofNat 818, Int.negSucc 376, Int.ofNat 306, Int.negSucc 154, Int.negSucc 1599, Int.negSucc 252, Int.negSucc 3, Int.negSucc 946, Int.ofNat 473, Int.negSucc 671, Int.ofNat 192, Int.negSucc 704, Int.ofNat 366, Int.negSucc 176, Int.ofNat 295, Int.ofNat 995],
    [Int.negSucc 923, Int.ofNat 2516, Int.negSucc 989, Int.ofNat 467, Int.negSucc 1053, Int.negSucc 1040, Int.negSucc 53, Int.negSucc 496, Int.ofNat 1109, Int.negSucc 312, Int.negSucc 1034, Int.ofNat 528, Int.ofNat 59, Int.negSucc 237, Int.negSucc 379, Int.ofNat 148, Int.ofNat 154, Int.ofNat 503],
    [Int.ofNat 455, Int.negSucc 2107, Int.ofNat 266, Int.negSucc 238, Int.negSucc 185, Int.ofNat 133, Int.ofNat 119, Int.negSucc 260, Int.ofNat 163, Int.negSucc 241, Int.negSucc 334, Int.ofNat 232, Int.negSucc 608, Int.ofNat 496, Int.ofNat 420, Int.negSucc 332, Int.negSucc 290, Int.ofNat 9, Int.ofNat 590],
    [Int.negSucc 284, Int.ofNat 927, Int.negSucc 261, Int.negSucc 405, Int.negSucc 429, Int.ofNat 101, Int.negSucc 923, Int.ofNat 10, Int.negSucc 72, Int.negSucc 66, Int.negSucc 182, Int.negSucc 278, Int.negSucc 100, Int.negSucc 71, Int.negSucc 440, Int.ofNat 230, Int.ofNat 174, Int.negSucc 98, Int.negSucc 240, Int.ofNat 510],
    [Int.ofNat 664, Int.negSucc 1851, Int.ofNat 1328, Int.negSucc 454, Int.ofNat 609, Int.ofNat 848, Int.negSucc 56, Int.ofNat 213, Int.negSucc 1219, Int.negSucc 223, Int.ofNat 1112, Int.negSucc 499, Int.negSucc 42, Int.ofNat 302, Int.ofNat 65, Int.negSucc 285, Int.negSucc 314, Int.negSucc 223, Int.ofNat 52, Int.ofNat 21, Int.ofNat 378],
    [Int.ofNat 148, Int.ofNat 174, Int.ofNat 9, Int.ofNat 7, Int.negSucc 137, Int.ofNat 81, Int.ofNat 201, Int.negSucc 112, Int.negSucc 387, Int.ofNat 100, Int.ofNat 304, Int.ofNat 239, Int.ofNat 85, Int.negSucc 220, Int.negSucc 190, Int.ofNat 154, Int.ofNat 176, Int.ofNat 313, Int.ofNat 101, Int.ofNat 119, Int.negSucc 275, Int.ofNat 484],
    [Int.negSucc 42, Int.negSucc 276, Int.negSucc 1, Int.negSucc 247, Int.ofNat 92, Int.negSucc 133, Int.negSucc 116, Int.negSucc 54, Int.ofNat 513, Int.negSucc 19, Int.negSucc 485, Int.negSucc 399, Int.negSucc 689, Int.ofNat 167, Int.negSucc 155, Int.negSucc 0, Int.negSucc 57, Int.negSucc 170, Int.ofNat 59, Int.ofNat 156, Int.ofNat 83, Int.ofNat 106, Int.ofNat 298]
  ]
}

def blockCert5 : OrbitBlockCert := {
  r := 24, m := 32, copies := 1, S := 1,
  blk := [(0, 20), (1, 21), (3, 19), (4, 20), (5, 23), (6, 31), (7, 32), (8, 22), (10, 33), (12, 16), (13, 17), (14, 20), (15, 29), (16, 12), (17, 13), (18, 28), (19, 3), (20, 0), (20, 4), (20, 14), (20, 34), (21, 1), (22, 8), (23, 5), (24, 26), (26, 24), (28, 18), (29, 15), (31, 6), (32, 7), (33, 10), (34, 20)],
  Qcols := [
    [(7, Int.negSucc 0)],
    [(1, Int.negSucc 0), (17, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1)],
    [(8, Int.ofNat 1), (12, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.negSucc 0), (22, Int.negSucc 0)],
    [(0, Int.negSucc 0), (17, Int.negSucc 0), (23, Int.ofNat 1)],
    [(6, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.negSucc 0)],
    [(5, Int.negSucc 0), (9, Int.ofNat 1), (11, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.negSucc 0)],
    [(2, Int.negSucc 0), (6, Int.negSucc 0), (14, Int.ofNat 1), (17, Int.negSucc 0), (18, Int.negSucc 0), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0)],
    [(9, Int.ofNat 1), (19, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0)],
    [(11, Int.negSucc 0), (14, Int.negSucc 0), (16, Int.negSucc 0), (21, Int.negSucc 0), (23, Int.negSucc 0)],
    [(4, Int.ofNat 1), (7, Int.ofNat 1), (8, Int.negSucc 0), (12, Int.ofNat 1), (18, Int.negSucc 0)],
    [(0, Int.ofNat 1), (1, Int.ofNat 1), (2, Int.negSucc 0), (4, Int.negSucc 0), (5, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (23, Int.negSucc 0)],
    [(16, Int.negSucc 0)],
    [(13, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(5, Int.ofNat 1), (7, Int.negSucc 0), (8, Int.ofNat 1), (10, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(0, Int.negSucc 0), (1, Int.negSucc 0), (2, Int.ofNat 1), (3, Int.ofNat 1), (13, Int.negSucc 0), (17, Int.negSucc 0), (19, Int.ofNat 1), (20, Int.ofNat 1), (22, Int.negSucc 0)],
    [(12, Int.ofNat 1), (17, Int.ofNat 1), (18, Int.ofNat 1), (22, Int.negSucc 0), (23, Int.negSucc 1)],
    [(8, Int.negSucc 0), (9, Int.negSucc 0), (10, Int.ofNat 1), (11, Int.negSucc 0), (18, Int.negSucc 0), (19, Int.negSucc 0), (20, Int.negSucc 0), (21, Int.ofNat 1)],
    [(7, Int.ofNat 1), (18, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0)],
    [(0, Int.ofNat 1), (19, Int.ofNat 1), (22, Int.ofNat 1)],
    [(16, Int.ofNat 1), (19, Int.negSucc 0), (20, Int.negSucc 0)],
    [(15, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (21, Int.ofNat 1)],
    [(1, Int.ofNat 1), (3, Int.negSucc 0), (6, Int.ofNat 1), (13, Int.ofNat 1), (14, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.ofNat 1), (19, Int.ofNat 1), (20, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1), (23, Int.ofNat 1)],
    [(11, Int.ofNat 1), (19, Int.negSucc 0), (20, Int.ofNat 1), (22, Int.negSucc 0), (23, Int.negSucc 1)],
    [(14, Int.ofNat 1), (19, Int.negSucc 0), (21, Int.ofNat 1), (22, Int.ofNat 1)],
    [(12, Int.negSucc 0), (13, Int.ofNat 1), (15, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (20, Int.ofNat 1), (21, Int.negSucc 0), (23, Int.negSucc 0)],
    [(3, Int.negSucc 0), (10, Int.ofNat 1), (15, Int.ofNat 1), (20, Int.ofNat 1), (23, Int.negSucc 0)],
    [(10, Int.negSucc 0), (17, Int.ofNat 1), (18, Int.ofNat 1), (21, Int.negSucc 0), (22, Int.negSucc 0), (23, Int.negSucc 0)],
    [(3, Int.ofNat 1), (17, Int.ofNat 1), (18, Int.ofNat 1), (20, Int.negSucc 0), (22, Int.ofNat 1), (23, Int.negSucc 0)],
    [(4, Int.negSucc 0), (17, Int.negSucc 0), (18, Int.negSucc 0), (22, Int.ofNat 1)],
    [(2, Int.ofNat 1), (4, Int.ofNat 1), (5, Int.ofNat 1), (17, Int.negSucc 0), (19, Int.ofNat 1), (21, Int.negSucc 0)],
    [(6, Int.ofNat 1), (9, Int.negSucc 0), (16, Int.ofNat 1), (19, Int.negSucc 0), (20, Int.ofNat 1), (21, Int.negSucc 0), (23, Int.negSucc 0)],
    [(15, Int.ofNat 1)]
  ],
  A := [
    [Int.ofNat 1649808, Int.ofNat 49680, Int.negSucc 66527, Int.ofNat 38448, Int.negSucc 28943, Int.negSucc 22031, Int.ofNat 15552, Int.negSucc 68687, Int.ofNat 317952, Int.ofNat 220320, Int.negSucc 26783, Int.negSucc 72143, Int.ofNat 8640, Int.negSucc 86399, Int.negSucc 9935, Int.ofNat 39744, Int.ofNat 22032, Int.negSucc 323567, Int.ofNat 156384, Int.negSucc 296783, Int.negSucc 2591, Int.negSucc 559607, Int.negSucc 508895, Int.ofNat 378864],
    [Int.ofNat 49680, Int.ofNat 3016224, Int.negSucc 145583, Int.negSucc 178847, Int.negSucc 110591, Int.ofNat 10368, Int.ofNat 12528, Int.negSucc 408671, Int.ofNat 177120, Int.negSucc 22895, Int.negSucc 15119, Int.negSucc 6479, Int.negSucc 50111, Int.ofNat 10368, Int.negSucc 87263, Int.ofNat 31104, Int.ofNat 343440, Int.ofNat 8208, Int.ofNat 56592, Int.negSucc 80351, Int.negSucc 57887, Int.ofNat 91584, Int.ofNat 98064, Int.negSucc 4751],
    [Int.negSucc 66527, Int.negSucc 145583, Int.ofNat 3038256, Int.ofNat 104544, Int.ofNat 171504, Int.ofNat 12528, Int.negSucc 37583, Int.ofNat 53136, Int.negSucc 89423, Int.ofNat 120528, Int.ofNat 4752, Int.negSucc 2591, Int.negSucc 82943, Int.ofNat 4752, Int.negSucc 73007, Int.negSucc 357263, Int.negSucc 403487, Int.ofNat 114912, Int.ofNat 95472, Int.ofNat 141696, Int.negSucc 38879, Int.negSucc 68687, Int.negSucc 47951, Int.ofNat 72144],
    [Int.ofNat 38448, Int.negSucc 178847, Int.ofNat 104544, Int.ofNat 2690064, Int.ofNat 7344, Int.ofNat 13824, Int.negSucc 86399, Int.ofNat 5184, Int.negSucc 20735, Int.ofNat 403488, Int.negSucc 102383, Int.ofNat 613686, Int.negSucc 3023, Int.ofNat 260496, Int.ofNat 82944, Int.negSucc 40175, Int.negSucc 4751, Int.negSucc 196559, Int.ofNat 46656, Int.ofNat 18576, Int.negSucc 11663, Int.negSucc 35423, Int.negSucc 19439, Int.negSucc 102383],
    [Int.negSucc 28943, Int.negSucc 110591, Int.ofNat 171504, Int.ofNat 7344, Int.ofNat 2500416, Int.negSucc 457919, Int.ofNat 3024, Int.ofNat 64368, Int.negSucc 132623, Int.ofNat 9504, Int.ofNat 40176, Int.ofNat 18144, Int.ofNat 78624, Int.negSucc 42767, Int.ofNat 11232, Int.ofNat 49248, Int.ofNat 28080, Int.ofNat 6480, Int.negSucc 7343, Int.ofNat 9072, Int.negSucc 90719, Int.negSucc 51839, Int.negSucc 41903, Int.ofNat 39744],
    [Int.negSucc 22031, Int.ofNat 10368, Int.ofNat 12528, Int.ofNat 13824, Int.negSucc 457919, Int.ofNat 2394144, Int.negSucc 80351, Int.negSucc 26783, Int.ofNat 69120, Int.ofNat 21600, Int.negSucc 85535, Int.negSucc 73871, Int.negSucc 82079, Int.ofNat 96336, Int.negSucc 10799, Int.negSucc 298079, Int.negSucc 303263, Int.ofNat 68688, Int.ofNat 73440, Int.ofNat 85104, Int.ofNat 64368, Int.ofNat 8208, Int.ofNat 6912, Int.ofNat 10368],
    [Int.ofNat 15552, Int.ofNat 12528, Int.negSucc 37583, Int.negSucc 86399, Int.ofNat 3024, Int.negSucc 80351, Int.ofNat 2529792, Int.negSucc 321407, Int.negSucc 3455, Int.negSucc 3455, Int.ofNat 380160, Int.ofNat 3456, Int.negSucc 390527, Int.ofNat 6048, Int.ofNat 245376, Int.negSucc 320111, Int.negSucc 29375, Int.ofNat 279840, Int.negSucc 92447, Int.negSucc 162431, Int.negSucc 21599, Int.ofNat 149904, Int.ofNat 65232, Int.ofNat 54864],
    [Int.negSucc 68687, Int.negSucc 408671, Int.ofNat 53136, Int.ofNat 5184, Int.ofNat 64368, Int.negSucc 26783, Int.negSucc 321407, Int.ofNat 1570752, Int.negSucc 158975, Int.ofNat 24624, Int.ofNat 55728, Int.ofNat 13392, Int.ofNat 160272, Int.negSucc 366335, Int.ofNat 3024, Int.ofNat 141264, Int.negSucc 32399, Int.negSucc 187487, Int.ofNat 42336, Int.ofNat 38016, Int.negSucc 361583, Int.ofNat 319248, Int.ofNat 34992, Int.negSucc 166751],
    [Int.ofNat 317952, Int.ofNat 177120, Int.negSucc 89423, Int.negSucc 20735, Int.negSucc 132623, Int.ofNat 69120, Int.negSucc 3455, Int.negSucc 158975, Int.ofNat 3111264, Int.ofNat 19872, Int.negSucc 212111, Int.ofNat 95472, Int.negSucc 295487, Int.ofNat 128304, Int.negSucc 18143, Int.ofNat 19008, Int.negSucc 252287, Int.ofNat 205632, Int.ofNat 27216, Int.ofNat 201744, Int.ofNat 155952, Int.negSucc 119231, Int.ofNat 191808, Int.negSucc 88559],
    [Int.ofNat 220320, Int.negSucc 22895, Int.ofNat 120528, Int.ofNat 403488, Int.ofNat 9504, Int.ofNat 21600, Int.negSucc 3455, Int.ofNat 24624, Int.ofNat 19872, Int.ofNat 2549232, Int.negSucc 74303, Int.negSucc 239759, Int.negSucc 20735, Int.negSucc 394847, Int.ofNat 9936, Int.ofNat 368496, Int.negSucc 17711, Int.ofNat 240192, Int.negSucc 115775, Int.ofNat 134784, Int.negSucc 37151, Int.negSucc 168911, Int.ofNat 152928, Int.negSucc 34127],
    [Int.negSucc 26783, Int.negSucc 15119, Int.ofNat 4752, Int.negSucc 102383, Int.ofNat 40176, Int.negSucc 85535, Int.ofNat 380160, Int.ofNat 55728, Int.negSucc 212111, Int.negSucc 74303, Int.ofNat 2744064, Int.negSucc 92447, Int.ofNat 460902, Int.negSucc 23759, Int.negSucc 390527, Int.ofNat 27648, Int.ofNat 22464, Int.negSucc 75167, Int.ofNat 138672, Int.ofNat 119232, Int.negSucc 92447, Int.ofNat 49680, Int.negSucc 93311, Int.negSucc 15983],
    [Int.negSucc 72143, Int.negSucc 6479, Int.negSucc 2591, Int.ofNat 613686, Int.ofNat 18144, Int.negSucc 73871, Int.ofNat 3456, Int.ofNat 13392, Int.ofNat 95472, Int.negSucc 239759, Int.negSucc 92447, Int.ofNat 2693520, Int.negSucc 5183, Int.negSucc 419039, Int.ofNat 102816, Int.ofNat 25488, Int.ofNat 24192, Int.ofNat 239760, Int.negSucc 27647, Int.ofNat 43200, Int.ofNat 33696, Int.negSucc 83807, Int.negSucc 8207, Int.ofNat 27648],
    [Int.ofNat 8640, Int.negSucc 50111, Int.negSucc 82943, Int.negSucc 3023, Int.ofNat 78624, Int.negSucc 82079, Int.negSucc 390527, Int.ofNat 160272, Int.negSucc 295487, Int.negSucc 20735, Int.ofNat 460902, Int.negSucc 5183, Int.ofNat 2850336, Int.negSucc 117503, Int.ofNat 409590, Int.ofNat 75168, Int.negSucc 31967, Int.negSucc 95471, Int.negSucc 294191, Int.negSucc 231551, Int.negSucc 22463, Int.ofNat 184464, Int.ofNat 6480, Int.negSucc 70415],
    [Int.negSucc 86399, Int.ofNat 10368, Int.ofNat 4752, Int.ofNat 260496, Int.negSucc 42767, Int.ofNat 96336, Int.ofNat 6048, Int.negSucc 366335, Int.ofNat 128304, Int.negSucc 394847, Int.negSucc 23759, Int.negSucc 419039, Int.negSucc 117503, Int.ofNat 2555712, Int.negSucc 88127, Int.negSucc 53135, Int.ofNat 277344, Int.ofNat 163728, Int.ofNat 45360, Int.negSucc 31967, Int.negSucc 85967, Int.ofNat 4320, Int.ofNat 72144, Int.ofNat 39744],
    [Int.negSucc 9935, Int.negSucc 87263, Int.negSucc 73007, Int.ofNat 82944, Int.ofNat 11232, Int.negSucc 10799, Int.ofNat 245376, Int.ofNat 3024, Int.negSucc 18143, Int.ofNat 9936, Int.negSucc 390527, Int.ofNat 102816, Int.ofNat 409590, Int.negSucc 88127, Int.ofNat 2695680, Int.ofNat 3456, Int.ofNat 62208, Int.negSucc 32831, Int.ofNat 161136, Int.ofNat 145584, Int.ofNat 15984, Int.negSucc 21167, Int.negSucc 85103, Int.negSucc 47951],
    [Int.ofNat 39744, Int.ofNat 31104, Int.negSucc 357263, Int.negSucc 40175, Int.ofNat 49248, Int.negSucc 298079, Int.negSucc 320111, Int.ofNat 141264, Int.ofNat 19008, Int.ofNat 368496, Int.ofNat 27648, Int.ofNat 25488, Int.ofNat 75168, Int.negSucc 53135, Int.ofNat 3456, Int.ofNat 1606176, Int.negSucc 223775, Int.ofNat 363744, Int.ofNat 60912, Int.ofNat 162864, Int.negSucc 204335, Int.ofNat 144720, Int.negSucc 259199, Int.negSucc 9071],
    [Int.ofNat 22032, Int.ofNat 343440, Int.negSucc 403487, Int.negSucc 4751, Int.ofNat 28080, Int.negSucc 303263, Int.negSucc 29375, Int.negSucc 32399, Int.negSucc 252287, Int.negSucc 17711, Int.ofNat 22464, Int.ofNat 24192, Int.negSucc 31967, Int.ofNat 277344, Int.ofNat 62208, Int.negSucc 223775, Int.ofNat 1494720, Int.ofNat 150768, Int.ofNat 70848, Int.ofNat 162864, Int.ofNat 145584, Int.negSucc 113615, Int.ofNat 31536, Int.negSucc 13823],
    [Int.negSucc 323567, Int.ofNat 8208, Int.ofNat 114912, Int.negSucc 196559, Int.ofNat 6480, Int.ofNat 68688, Int.ofNat 279840, Int.negSucc 187487, Int.ofNat 205632, Int.ofNat 240192, Int.negSucc 75167, Int.ofNat 239760, Int.negSucc 95471, Int.ofNat 163728, Int.negSucc 32831, Int.ofNat 363744, Int.ofNat 150768, Int.ofNat 1546560, Int.negSucc 295919, Int.ofNat 212544, Int.negSucc 99791, Int.negSucc 341711, Int.ofNat 231984, Int.ofNat 339984],
    [Int.ofNat 156384, Int.ofNat 56592, Int.ofNat 95472, Int.ofNat 46656, Int.negSucc 7343, Int.ofNat 73440, Int.negSucc 92447, Int.ofNat 42336, Int.ofNat 27216, Int.negSucc 115775, Int.ofNat 138672, Int.negSucc 27647, Int.negSucc 294191, Int.ofNat 45360, Int.ofNat 161136, Int.ofNat 60912, Int.ofNat 70848, Int.negSucc 295919, Int.ofNat 1732752, Int.negSucc 185759, Int.ofNat 254880, Int.negSucc 568079, Int.negSucc 77759, Int.ofNat 115176],
    [Int.negSucc 296783, Int.negSucc 80351, Int.ofNat 141696, Int.ofNat 18576, Int.ofNat 9072, Int.ofNat 85104, Int.negSucc 162431, Int.ofNat 38016, Int.ofNat 201744, Int.ofNat 134784, Int.ofNat 119232, Int.ofNat 43200, Int.negSucc 231551, Int.negSucc 31967, Int.ofNat 145584, Int.ofNat 162864, Int.ofNat 162864, Int.ofNat 212544, Int.negSucc 185759, Int.ofNat 1584144, Int.negSucc 419903, Int.negSucc 28511, Int.negSucc 377567, Int.negSucc 141263],
    [Int.negSucc 2591, Int.negSucc 57887, Int.negSucc 38879, Int.negSucc 11663, Int.negSucc 90719, Int.ofNat 64368, Int.negSucc 21599, Int.negSucc 361583, Int.ofNat 155952, Int.negSucc 37151, Int.negSucc 92447, Int.ofNat 33696, Int.negSucc 22463, Int.negSucc 85967, Int.ofNat 15984, Int.negSucc 204335, Int.ofNat 145584, Int.negSucc 99791, Int.ofNat 254880, Int.negSucc 419903, Int.ofNat 1686096, Int.ofNat 424224, Int.ofNat 381456, Int.ofNat 36720],
    [Int.negSucc 559607, Int.ofNat 91584, Int.negSucc 68687, Int.negSucc 35423, Int.negSucc 51839, Int.ofNat 8208, Int.ofNat 149904, Int.ofNat 319248, Int.negSucc 119231, Int.negSucc 168911, Int.ofNat 49680, Int.negSucc 83807, Int.ofNat 184464, Int.ofNat 4320, Int.negSucc 21167, Int.ofNat 144720, Int.negSucc 113615, Int.negSucc 341711, Int.negSucc 568079, Int.negSucc 28511, Int.ofNat 424224, Int.ofNat 1806624, Int.negSucc 261791, Int.negSucc 138671],
    [Int.negSucc 508895, Int.ofNat 98064, Int.negSucc 47951, Int.negSucc 19439, Int.negSucc 41903, Int.ofNat 6912, Int.ofNat 65232, Int.ofNat 34992, Int.ofNat 191808, Int.ofNat 152928, Int.negSucc 93311, Int.negSucc 8207, Int.ofNat 6480, Int.ofNat 72144, Int.negSucc 85103, Int.negSucc 259199, Int.ofNat 31536, Int.ofNat 231984, Int.negSucc 77759, Int.negSucc 377567, Int.ofNat 381456, Int.negSucc 261791, Int.ofNat 1533600, Int.negSucc 63935],
    [Int.ofNat 378864, Int.negSucc 4751, Int.ofNat 72144, Int.negSucc 102383, Int.ofNat 39744, Int.ofNat 10368, Int.ofNat 54864, Int.negSucc 166751, Int.negSucc 88559, Int.negSucc 34127, Int.negSucc 15983, Int.ofNat 27648, Int.negSucc 70415, Int.ofNat 39744, Int.negSucc 47951, Int.negSucc 9071, Int.negSucc 13823, Int.ofNat 339984, Int.ofNat 115176, Int.negSucc 141263, Int.ofNat 36720, Int.negSucc 138671, Int.negSucc 63935, Int.ofNat 1388016]
  ],
  W := [
    [Int.ofNat 1248],
    [Int.ofNat 40, Int.ofNat 1710],
    [Int.negSucc 52, Int.negSucc 83, Int.ofNat 1714],
    [Int.ofNat 31, Int.negSucc 104, Int.ofNat 57, Int.ofNat 1607],
    [Int.negSucc 22, Int.negSucc 63, Int.ofNat 96, Int.negSucc 2, Int.ofNat 1547],
    [Int.negSucc 17, Int.ofNat 6, Int.ofNat 7, Int.ofNat 9, Int.negSucc 295, Int.ofNat 1488],
    [Int.ofNat 12, Int.ofNat 7, Int.negSucc 20, Int.negSucc 52, Int.ofNat 4, Int.negSucc 52, Int.ofNat 1559],
    [Int.negSucc 54, Int.negSucc 237, Int.ofNat 18, Int.negSucc 11, Int.ofNat 30, Int.negSucc 11, Int.negSucc 204, Int.ofNat 1173],
    [Int.ofNat 255, Int.ofNat 98, Int.negSucc 38, Int.negSucc 9, Int.negSucc 74, Int.ofNat 34, Int.negSucc 3, Int.negSucc 101, Int.ofNat 1711],
    [Int.ofNat 177, Int.negSucc 17, Int.ofNat 75, Int.ofNat 244, Int.ofNat 4, Int.ofNat 16, Int.ofNat 6, Int.ofNat 28, Int.negSucc 8, Int.ofNat 1536],
    [Int.negSucc 20, Int.negSucc 7, Int.ofNat 2, Int.negSucc 63, Int.ofNat 25, Int.negSucc 51, Int.ofNat 240, Int.ofNat 85, Int.negSucc 112, Int.negSucc 38, Int.ofNat 1602],
    [Int.negSucc 57, Int.negSucc 1, Int.negSucc 2, Int.ofNat 383, Int.ofNat 12, Int.negSucc 49, Int.ofNat 14, Int.ofNat 14, Int.ofNat 69, Int.negSucc 209, Int.negSucc 47, Int.ofNat 1548],
    [Int.ofNat 7, Int.negSucc 28, Int.negSucc 49, Int.negSucc 1, Int.ofNat 53, Int.negSucc 43, Int.negSucc 252, Int.ofNat 86, Int.negSucc 165, Int.negSucc 12, Int.ofNat 307, Int.ofNat 12, Int.ofNat 1599],
    [Int.negSucc 68, Int.ofNat 8, Int.ofNat 1, Int.ofNat 164, Int.negSucc 27, Int.ofNat 57, Int.ofNat 12, Int.negSucc 308, Int.ofNat 65, Int.negSucc 269, Int.ofNat 6, Int.negSucc 347, Int.negSucc 45, Int.ofNat 1460],
    [Int.negSucc 7, Int.negSucc 50, Int.negSucc 44, Int.ofNat 50, Int.ofNat 8, Int.negSucc 5, Int.ofNat 159, Int.ofNat 21, Int.negSucc 4, Int.ofNat 0, Int.negSucc 267, Int.ofNat 44, Int.ofNat 328, Int.negSucc 40, Int.ofNat 1545],
    [Int.ofNat 32, Int.ofNat 17, Int.negSucc 206, Int.negSucc 16, Int.ofNat 46, Int.negSucc 189, Int.negSucc 215, Int.ofNat 88, Int.ofNat 11, Int.ofNat 250, Int.ofNat 45, Int.ofNat 51, Int.negSucc 10, Int.ofNat 53, Int.ofNat 27, Int.ofNat 1143],
    [Int.ofNat 18, Int.ofNat 200, Int.negSucc 224, Int.ofNat 18, Int.ofNat 41, Int.negSucc 194, Int.negSucc 28, Int.ofNat 9, Int.negSucc 159, Int.negSucc 1, Int.ofNat 2, Int.ofNat 12, Int.negSucc 51, Int.ofNat 207, Int.ofNat 58, Int.negSucc 289, Int.ofNat 1054],
    [Int.negSucc 258, Int.ofNat 11, Int.ofNat 60, Int.negSucc 118, Int.negSucc 2, Int.ofNat 43, Int.ofNat 180, Int.negSucc 139, Int.ofNat 150, Int.ofNat 205, Int.negSucc 57, Int.ofNat 195, Int.ofNat 7, Int.ofNat 158, Int.negSucc 44, Int.ofNat 327, Int.ofNat 257, Int.ofNat 1005],
    [Int.ofNat 125, Int.ofNat 30, Int.ofNat 61, Int.ofNat 26, Int.negSucc 4, Int.ofNat 49, Int.negSucc 56, Int.ofNat 38, Int.negSucc 1, Int.negSucc 97, Int.ofNat 95, Int.negSucc 27, Int.negSucc 210, Int.ofNat 9, Int.ofNat 175, Int.ofNat 68, Int.ofNat 76, Int.negSucc 251, Int.ofNat 1202],
    [Int.negSucc 237, Int.negSucc 40, Int.ofNat 73, Int.ofNat 11, Int.negSucc 3, Int.ofNat 53, Int.negSucc 98, Int.negSucc 4, Int.ofNat 156, Int.ofNat 110, Int.ofNat 102, Int.ofNat 30, Int.negSucc 158, Int.negSucc 20, Int.ofNat 154, Int.ofNat 119, Int.ofNat 233, Int.ofNat 30, Int.negSucc 202, Int.ofNat 1099],
    [Int.negSucc 1, Int.negSucc 33, Int.negSucc 23, Int.negSucc 8, Int.negSucc 58, Int.ofNat 32, Int.negSucc 12, Int.negSucc 314, Int.ofNat 71, Int.negSucc 15, Int.negSucc 32, Int.ofNat 22, Int.ofNat 16, Int.negSucc 126, Int.ofNat 2, Int.negSucc 143, Int.ofNat 146, Int.negSucc 125, Int.ofNat 200, Int.negSucc 367, Int.ofNat 1110],
    [Int.negSucc 447, Int.ofNat 64, Int.negSucc 50, Int.negSucc 6, Int.negSucc 33, Int.negSucc 6, Int.ofNat 98, Int.ofNat 283, Int.ofNat 8, Int.negSucc 58, Int.negSucc 4, Int.negSucc 80, Int.ofNat 120, Int.ofNat 14, Int.negSucc 52, Int.ofNat 144, Int.negSucc 74, Int.negSucc 438, Int.negSucc 501, Int.negSucc 154, Int.ofNat 480, Int.ofNat 814],
    [Int.negSucc 407, Int.ofNat 67, Int.negSucc 36, Int.ofNat 1, Int.negSucc 27, Int.negSucc 5, Int.ofNat 44, Int.ofNat 33, Int.ofNat 169, Int.ofNat 149, Int.negSucc 55, Int.negSucc 10, Int.ofNat 41, Int.ofNat 55, Int.negSucc 76, Int.negSucc 248, Int.negSucc 29, Int.ofNat 144, Int.ofNat 60, Int.negSucc 397, Int.ofNat 194, Int.negSucc 609, Int.ofNat 739],
    [Int.ofNat 304, Int.negSucc 9, Int.ofNat 51, Int.negSucc 71, Int.ofNat 27, Int.ofNat 16, Int.ofNat 32, Int.negSucc 125, Int.negSucc 101, Int.negSucc 46, Int.negSucc 14, Int.ofNat 46, Int.negSucc 40, Int.ofNat 28, Int.negSucc 21, Int.ofNat 18, Int.negSucc 17, Int.ofNat 390, Int.ofNat 144, Int.negSucc 28, Int.ofNat 21, Int.ofNat 325, Int.ofNat 284, Int.ofNat 894]
  ]
}

def allBlockCerts : List OrbitBlockCert := [blockCert0, blockCert1, blockCert2, blockCert3, blockCert4, blockCert5]

/-- Fast list dot product for Cholesky rows (length ≤ 33). -/
def dotInt : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotInt xs ys

/-- Check symmetry of `A` (`r × r`) and strict diagonal dominance of `S² * A - W * Wᵀ`. -/
def checkSymAndDD (b : OrbitBlockCert) : Bool :=
  let s2 := b.S * b.S
  let lenOk := b.S > 0 && b.A.length == b.r && b.W.length == b.r && b.Qcols.length == b.m && b.blk.length == b.m
  let rowsOk := (b.A.zip b.W).foldl (fun (acc : Bool × Nat) (aRow, wRow) =>
    let i := acc.2
    if !acc.1 || aRow.length != b.r || wRow.length != i + 1 then (false, i + 1)
    else
      -- Check `E[i][i] >= sum_{j != i} |E[i][j]|` where `E[i][j] = s2 * A[i][j] - dotInt wRow wRow_j`
      let res := (aRow.zip b.W).foldl (fun (st : Int × Int × Nat) (aij, wRowJ) =>
        let j := st.2.2
        let eij := s2 * aij - dotInt wRow wRowJ
        if j == i then (eij, st.2.1, j + 1)
        else (st.1, st.2.1 + Int.natAbs eij, j + 1)
      ) (0, 0, 0)
      (res.1 >= res.2.1, i + 1)
  ) (lenOk, 0)
  -- Also check `A[i][j] == A[j][i]` explicitly!
  let symOk := b.A.zip (List.range b.r) |>.all fun (aRow, i) =>
    aRow.zip b.A |>.all fun (aij, aRowJ) => aij == aRowJ.getD i 0
  let qOk := b.Qcols.all fun col => col.all fun (p, _) => p < b.r
  let blkOk := b.blk.all fun (a, ap) => a < 35 && ap < 35
  rowsOk.1 && symOk && qOk && blkOk

def checkAllBlocks : Bool := allBlockCerts.all checkSymAndDD

/-- Sparse matrix-vector product `A * qCol` for a sparse column `qCol : List (Nat × Int)`. -/
def mulASparseCol (A : List (List Int)) (qCol : List (Nat × Int)) : List Int :=
  A.map fun aRow => qCol.foldl (fun s (q, v) => s + aRow.getD q 0 * v) 0

/-- Sparse dot product `qColᵀ * vec`. -/
def dotSparseCol (qCol : List (Nat × Int)) (vec : List Int) : Int :=
  qCol.foldl (fun s (p, v) => s + v * vec.getD p 0) 0

/-- Accumulate `Phi(Qᵀ A Q)` of one block cert into a depth-8 `RowTrie` (balanced merge!). -/
def buildBlockPhiTrie (b : OrbitBlockCert) : RowTrie :=
  let blkTups := b.blk.map fun (a, ap) => (sym4List.getD a (0,0,0,0), sym4List.getD ap (0,0,0,0))
  -- Precompute `Tcols[j] = A * Qcols[j]` (length `m`, each of length `r`)
  let Tcols := b.Qcols.map (mulASparseCol b.A)
  let jData := blkTups.zip Tcols
  let iData := blkTups.zip b.Qcols
  trieMergeAll 7 (iData.map fun ((cai, capi), qColI) =>
    jData.foldl (fun t ((cc1, cc2), tColJ) =>
      let v := dotSparseCol qColI tColJ
      if v == 0 then t
      else
        let ii := sym8Idx (addTup4 capi cc1)
        let jj := sym8Idx (addTup4 cai cc2)
        trieAdd 8 ii jj v t
    ) RowTrie.empty)

/-- Combined pre-symmetrization certificate trie `∑_{o} copies_o * Phi(Q_oᵀ A_o Q_o)`. -/
def buildRawCertTrie : RowTrie :=
  trieMergeAll 4 (allBlockCerts.map fun b => trieScale b.copies (buildBlockPhiTrie b))

/-- Permute both row and column indices of a depth-8 `RowTrie` by a permutation table `pt : NatTrie`. -/
def permuteRow (pt : NatTrie) (row : List (Nat × Int)) : List (Nat × Int) :=
  row.foldl (fun acc (jj, v) => addAssoc (natTrieGet 8 jj pt) v acc) []

def permuteTrie (p : Tup4) (t : RowTrie) : RowTrie :=
  let pt := buildPermNatTrie p
  let rowTries := (List.range 165).map fun ii =>
    let row := trieGetRow 8 ii t
    if row.isEmpty then RowTrie.empty
    else trieSingleRow 8 (natTrieGet 8 ii pt) (permuteRow pt row)
  trieMergeAll 9 rowTries

/-- Accumulate `∑_{σ ∈ S₄} σ · (∑_{o} copies_o * Phi(Q_oᵀ A_o Q_o))` into a depth-8 `RowTrie`. -/
def buildCertFullTrie : RowTrie :=
  let raw := buildRawCertTrie
  trieMergeAll 6 (s4Perms.map fun p => permuteTrie p raw)

def checkCertMatchesTarget : Bool :=
  trieEq buildCertFullTrie (buildTargetTrie targetScale)

/-- Verify `sym4Idx` and `sym8Idx` match `sym4List` and `sym8List` at every index. -/
def checkSymIdxTables : Bool :=
  ((sym4List.zip (List.range 35)).all fun (t, i) => sym4Idx t == i) &&
  ((sym8List.zip (List.range 165)).all fun (t, i) => sym8Idx t == i)

set_option maxRecDepth 20000 in
theorem symIdxTables_valid : checkSymIdxTables = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem allBlocks_valid : checkAllBlocks = true := by rfl

set_option maxRecDepth 50000 in
set_option maxHeartbeats 8000000 in
theorem cert_matches_target : checkCertMatchesTarget = true := by rfl

end TwoQubitExactCert

end MultiQubitMUB
