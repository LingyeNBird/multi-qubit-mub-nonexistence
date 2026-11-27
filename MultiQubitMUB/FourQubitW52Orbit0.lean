import MultiQubitMUB.FourQubitQminus52
import MultiQubitMUB.FourQubitCDCerts

set_option linter.constructorNameAsVariable false

/-!
# Part 2c: Complete Zero-Search Classification of Orbit 0 (`f₂₇ = 9`, `f_A ≤ 92 ⇒ Sp42`)

Proves `orbit0_hits_sp42` using:
1. Exact spectral projector identity `R₃₆² = 36 R₃₆` (`R₃₆ = 18 I - 6 M₀ + ∑_{h<3} u_h u_hᵀ`)
   forcing `max_h |u_h · x| ≥ 16` (`k = |S| ≤ 10` flips from some `±u_h`).
2. `O⁻(6,2)` stabilizer reduction (`U1_TO_U0`, `U2_TO_U0`, `flipB36`) to `u₀` with `|S| ≤ 10`.
3. `4 × K_{3,3,3}` 3-coloring + `C₄`-free 3-regular bipartite bounds eliminating ALL `6 ≤ k ≤ 10`
   except the 4 whole 9-blocks (`BLOCKS9` → `Sp42`).
4. Pigeonhole + `V_TO_0` + `STAB_U0_0` reducing ALL valid `k ≤ 5` subsets to `134` canonical
   representatives (`CANON_K5` → `Sp42`).
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Pure-Computable Orbit 0 Tables & `by rfl` Verifications -/

def orb0_u_vecs : List (List ℤ) := [
  [1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, -1],
  [1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1],
  [1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1]
]
def orb0_blk : List Nat := [0, 1, 1, 1, 2, 3, 0, 0, 2, 3, 2, 3, 0, 3, 0, 2, 2, 1, 1, 3, 3, 2, 0, 0, 3, 1, 1, 2, 0, 3, 2, 0, 2, 1, 1, 3]
def orb0_col3 : List Nat := [0, 0, 1, 2, 0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 0, 0, 2, 1, 0, 0, 0, 0, 2, 1, 1, 1, 1, 2, 2, 1]
def orb0_np0 : List Nat := [12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31]
def orb0_u1ToU0 : Nat × List Nat := (10, [11, 1])
def orb0_u2ToU0 : Nat × List Nat := (1, [10, 1])
def orb0_vTo0 : List (Nat × List Nat) := [
  (0, []),
  (9, [12, 35, 14]),
  (15, [8, 22, 12]),
  (13, [8, 52, 14]),
  (16, [9, 36, 21, 5]),
  (46, [8, 38, 17, 5]),
  (31, [11, 1, 36, 21]),
  (54, [10, 1, 38, 17]),
  (55, [13, 55, 17, 5]),
  (28, [12, 49, 21, 5]),
  (17, [17, 41, 15, 3]),
  (9, [17, 57, 14, 7]),
  (15, [18, 15, 63, 13]),
  (15, [5, 29, 14, 1]),
  (46, [18, 15, 40, 9]),
  (10, [5, 24, 15, 1]),
  (0, [17, 50, 8, 5]),
  (24, [17, 40, 9, 7]),
  (59, [17, 56, 12, 3]),
  (50, [17, 35, 13, 5]),
  (32, [3, 40, 8, 1]),
  (10, [3, 43, 9, 1]),
  (37, [18, 15, 14, 42, 22, 3]),
  (56, [22, 14, 15, 41, 18, 3]),
  (13, [13, 41, 22, 3]),
  (55, [14, 40, 22, 7]),
  (21, [15, 43, 18, 7]),
  (56, [12, 42, 18, 3]),
  (43, [22, 14, 15, 62, 18, 7]),
  (13, [7, 63, 12, 1]),
  (10, [7, 56, 13, 1]),
  (8, [18, 15, 14, 57, 22, 7]),
  (0, [8, 57, 18, 7]),
  (17, [15, 56, 18, 3]),
  (14, [14, 63, 22, 3]),
  (9, [9, 62, 22, 7])
]
def orb0_stabU00 : List (Nat × List Nat) := [
  (0, []),
  (28, [1, 17, 21]),
  (10, [3, 5, 7]),
  (23, [18, 22, 5, 1]),
  (34, [33, 35, 3, 1]),
  (7, [33, 9, 1, 13, 38, 8, 7]),
  (34, [36, 21, 38, 17]),
  (55, [49, 21, 55, 17]),
  (43, [49, 21, 1, 55, 21]),
  (53, [50, 52, 7, 1]),
  (18, [8, 36, 18, 22, 52, 8, 5]),
  (22, [8, 57, 18, 22, 41, 8, 5])
]
def orb0_blocks9 : List (Nat × List Nat) := [
  (0, []),
  (0, [52, 22, 43, 41, 3]),
  (0, [52, 22, 2, 34, 32, 33, 40, 1]),
  (0, [52, 22, 2, 34, 32, 40, 33, 41])
]
def orb0_canonK5 : List (Nat × Nat × List Nat) := [
  (0, 1, []),
  (1, 2, []),
  (3, 3, []),
  (17, 4, []),
  (65, 4, [52, 22, 34, 32, 40, 41, 33]),
  (4097, 5, []),
  (8193, 5, [32, 33, 3]),
  (65537, 4, [38, 22, 36, 52, 48, 49, 1]),
  (131073, 4, [38, 22, 16, 48, 4, 37]),
  (7, 6, []),
  (19, 7, []),
  (67, 7, [18, 19, 17, 16, 1]),
  (21, 7, [38, 20, 18, 50, 32]),
  (4099, 8, []),
  (8195, 8, [32, 33, 3]),
  (65539, 8, [32, 11, 9]),
  (131075, 8, [33, 42, 43, 40]),
  (8197, 9, []),
  (4101, 6, [36, 60, 30, 46, 38, 6, 11, 14, 13]),
  (65541, 7, [52, 50, 4, 38, 39, 1]),
  (131077, 7, [38, 22, 16, 48, 4, 37]),
  (49, 10, []),
  (81, 11, []),
  (97, 12, []),
  (273, 11, [38, 20, 18, 50, 32]),
  (289, 12, [38, 20, 18, 50, 32]),
  (4113, 13, []),
  (8209, 8, [4, 36, 37, 47, 60, 18, 3]),
  (4129, 13, [4, 36, 52, 16, 24, 17, 25]),
  (8225, 14, []),
  (65553, 13, [36, 16, 9]),
  (131089, 15, []),
  (131105, 13, [4, 36, 24, 17]),
  (65569, 15, [52, 20, 4, 16, 24, 25, 17]),
  (9217, 11, [44, 12, 4, 18, 26, 24, 59]),
  (10241, 16, []),
  (5121, 17, []),
  (67585, 7, [52, 20, 4, 16, 24, 25, 17]),
  (133121, 12, [37, 30, 27, 24, 41, 10, 9, 60]),
  (132097, 16, [37, 12, 54, 25, 15, 34]),
  (66561, 12, [38, 22, 52, 29, 21]),
  (193, 10, [52, 22, 34, 32, 40, 41, 33]),
  (4161, 17, [36, 4, 5, 15, 17, 14]),
  (8257, 11, [36, 18, 26, 24, 27, 19]),
  (8321, 16, [36, 37, 33, 32, 1]),
  (65601, 12, [36, 11, 17]),
  (131137, 7, [36, 18, 26, 24, 27, 19]),
  (131201, 12, [4, 36, 18, 19, 17, 11, 10]),
  (65665, 16, [36, 37, 33, 51, 28, 18]),
  (12289, 14, [4, 11, 24]),
  (20481, 18, []),
  (69633, 13, [36, 52, 48, 32, 17, 1]),
  (135169, 13, [4, 16, 17]),
  (1052673, 19, []),
  (1064961, 17, [38, 22, 16, 12, 56, 53, 28]),
  (4198401, 19, [47, 15, 42, 37, 48, 17, 33]),
  (4210689, 17, [37, 31, 53, 62, 29, 25]),
  (4718593, 11, [37, 29, 24, 43, 31, 36, 19, 55, 63]),
  (4456449, 16, [38, 22, 16, 48, 5, 36, 1]),
  (4325377, 8, [36, 62, 58, 31, 52, 37, 18, 50]),
  (4259841, 14, [38, 22, 16, 48, 4, 37]),
  (40961, 9, [19, 10, 25]),
  (73729, 16, [36, 37, 33, 32, 19, 14, 29, 18]),
  (139265, 11, [4, 36, 24, 17]),
  (163841, 16, [7, 2, 21, 20]),
  (98305, 11, [52, 20, 4, 16, 24, 25, 17]),
  (1056769, 19, [38, 22, 16, 48, 4, 37]),
  (1081345, 17, [38, 22, 13, 57, 48, 24, 45]),
  (1572865, 17, [38, 22, 16, 48, 5, 36, 1]),
  (1310721, 17, [38, 22, 36, 52, 48, 49, 1]),
  (1179649, 13, [38, 22, 16, 48, 4, 37]),
  (1114113, 13, [38, 22, 36, 52, 48, 49, 1]),
  (196609, 10, [38, 22, 16, 48, 4, 37]),
  (327681, 11, [52, 50, 4, 38, 39, 1]),
  (589825, 12, [38, 22, 16, 48, 4, 37]),
  (16842753, 7, [36, 4, 30, 28, 20, 14, 13]),
  (16908289, 12, [36, 4, 29, 22, 12, 10]),
  (17039361, 15, [38, 56, 50, 4, 12, 15]),
  (17301505, 13, [38, 56, 50, 4, 12, 15]),
  (393217, 12, [38, 23, 17, 49, 5, 36, 1]),
  (33685505, 16, [36, 37, 33, 31, 12, 49, 50, 32]),
  (33816577, 13, [54, 22, 30, 18, 52, 23]),
  (28673, 20, []),
  (1060865, 21, []),
  (4206593, 22, []),
  (4231169, 23, []),
  (1073153, 23, [5, 37, 36, 2, 18, 19, 1]),
  (1085441, 24, []),
  (4218881, 24, [4, 36, 37, 2, 18, 19]),
  (6356993, 25, []),
  (20545, 26, []),
  (21505, 26, [36, 37, 33, 32, 1]),
  (1069057, 26, [37, 30, 53, 63, 9, 28, 13]),
  (4214785, 26, [37, 31, 26, 43, 32, 17]),
  (12648449, 20, [36, 44, 40, 13, 34, 18, 21, 32]),
  (1052737, 27, []),
  (1052801, 24, [36, 52, 48, 7, 55, 25, 57]),
  (1053185, 23, [38, 22, 13, 24, 53, 36, 17, 40]),
  (1054721, 21, [38, 22, 16, 12, 28, 48, 33, 17]),
  (1314817, 28, []),
  (1576961, 23, [5, 37, 59, 30, 53, 17, 36]),
  (4268033, 24, [14, 43, 22, 35]),
  (269488129, 29, []),
  (269492225, 21, [32, 40, 8]),
  (269516801, 30, []),
  (269500417, 27, [38, 22, 25, 32, 49, 41, 56]),
  (270008321, 21, [36, 52, 48, 31, 47, 41, 9]),
  (1067009, 25, [36, 38, 42, 33, 41]),
  (270536705, 28, [38, 22, 44, 60, 41, 25]),
  (4198417, 23, [37, 30, 59]),
  (4198433, 28, [5, 16, 17, 1]),
  (4198465, 30, [44, 12, 41, 55, 39, 37]),
  (4198529, 26, [36, 38, 34, 23, 42, 20, 31, 10, 43]),
  (4263937, 23, [14, 43, 22, 35]),
  (272633857, 30, [38, 22, 36, 52, 48, 49, 1]),
  (277348353, 22, [37, 12, 9, 54, 25, 63, 29, 18, 34]),
  (4210753, 31, []),
  (1056801, 24, [36, 52, 48, 33, 62, 56, 22]),
  (1057281, 22, [38, 22, 16, 12, 56, 53, 28]),
  (1318913, 24, [43, 40, 33, 42]),
  (1581057, 27, [38, 22, 16, 48, 4, 37]),
  (537927681, 29, [38, 22, 16, 48, 4, 37]),
  (537952257, 28, [41, 35, 11, 42]),
  (538181633, 30, [38, 22, 13, 17, 57, 5]),
  (538443777, 26, [37, 30, 27, 41, 42, 36, 18, 60]),
  (5255169, 32, []),
  (269496321, 33, []),
  (537931777, 33, [32, 33, 3]),
  (269520897, 34, []),
  (273682433, 34, [38, 22, 36, 52, 48, 49, 1]),
  (269504513, 35, []),
  (537939969, 36, []),
  (12603393, 37, []),
  (276844545, 38, [])
]

def orb0_M0 (i j : Nat) : ℤ :=
  if i == j || symp3 (B36_val i) (B36_val j) != 0 then 0
  else
    match A27_list.idxOf? (B36_val i ^^^ B36_val j) with
    | some idxA => gamma3_sgn (B36_val i) (B36_val j) * (rep27_vecs.getD 0 []).getD idxA 0
    | none => 0

def orb0_u (h i : Nat) : ℤ := (orb0_u_vecs.getD h []).getD i 0
def orb0_u0 (i : Nat) : ℤ := orb0_u 0 i
def orb0_Mt (i j : Nat) : ℤ := orb0_M0 i j * orb0_u0 i * orb0_u0 j

def orb0_R (i j : Nat) : ℤ :=
  (if i == j then 18 else 0) - 6 * orb0_M0 i j +
  orb0_u 0 i * orb0_u 0 j + orb0_u 1 i * orb0_u 1 j + orb0_u 2 i * orb0_u 2 j

/-- Induced `(perm, sgn)` on `B36` of `(g, us)` (`sOut(B36[i]) = sgn[i] * s(B36[perm[i]])`). -/
def orb0_A27 : List Nat := [2, 4, 6, 16, 19, 20, 23, 26, 27, 30, 31, 32, 34, 37, 39, 44, 45, 46, 47, 48, 51, 53, 54, 58, 59, 60, 61]
def orb0_B36 : List Nat := [1, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 33, 35, 36, 38, 40, 41, 42, 43, 49, 50, 52, 55, 56, 57, 62, 63]
def orb0_wlines : List (Nat × Nat × Nat × ℤ) := [(1, 2, 3, 1), (1, 4, 5, 1), (1, 6, 7, 1), (1, 16, 17, 1), (1, 18, 19, 1), (1, 20, 21, 1), (1, 22, 23, 1), (1, 32, 33, 1), (1, 34, 35, 1), (1, 36, 37, 1), (1, 38, 39, 1), (1, 48, 49, 1), (1, 50, 51, 1), (1, 52, 53, 1), (1, 54, 55, 1), (2, 4, 6, 1), (2, 5, 7, 1), (2, 8, 10, 1), (2, 9, 11, 1), (2, 12, 14, 1), (2, 13, 15, 1), (2, 32, 34, 1), (2, 33, 35, 1), (2, 36, 38, 1), (2, 37, 39, 1), (2, 40, 42, 1), (2, 41, 43, 1), (2, 44, 46, 1), (2, 45, 47, 1), (3, 4, 7, 1), (3, 5, 6, 1), (3, 24, 27, 1), (3, 25, 26, 1), (3, 28, 31, 1), (3, 29, 30, 1), (3, 32, 35, 1), (3, 33, 34, 1), (3, 36, 39, 1), (3, 37, 38, 1), (3, 56, 59, 1), (3, 57, 58, 1), (3, 60, 63, 1), (3, 61, 62, 1), (4, 8, 12, 1), (4, 9, 13, 1), (4, 10, 14, 1), (4, 11, 15, 1), (4, 16, 20, 1), (4, 17, 21, 1), (4, 18, 22, 1), (4, 19, 23, 1), (4, 24, 28, 1), (4, 25, 29, 1), (4, 26, 30, 1), (4, 27, 31, 1), (5, 16, 21, 1), (5, 17, 20, 1), (5, 18, 23, 1), (5, 19, 22, 1), (5, 40, 45, 1), (5, 41, 44, 1), (5, 42, 47, 1), (5, 43, 46, 1), (5, 56, 61, 1), (5, 57, 60, 1), (5, 58, 63, 1), (5, 59, 62, 1), (6, 8, 14, 1), (6, 9, 15, 1), (6, 10, 12, 1), (6, 11, 13, 1), (6, 48, 54, 1), (6, 49, 55, 1), (6, 50, 52, 1), (6, 51, 53, 1), (6, 56, 62, 1), (6, 57, 63, 1), (6, 58, 60, 1), (6, 59, 61, 1), (7, 24, 31, 1), (7, 25, 30, 1), (7, 26, 29, 1), (7, 27, 28, 1), (7, 40, 47, 1), (7, 41, 46, 1), (7, 42, 45, 1), (7, 43, 44, 1), (7, 48, 55, 1), (7, 49, 54, 1), (7, 50, 53, 1), (7, 51, 52, 1), (8, 16, 24, 1), (8, 18, 26, 1), (8, 20, 28, 1), (8, 22, 30, 1), (8, 32, 40, 1), (8, 34, 42, 1), (8, 36, 44, 1), (8, 38, 46, 1), (8, 48, 56, 1), (8, 50, 58, 1), (8, 52, 60, 1), (8, 54, 62, 1), (9, 16, 25, 1), (9, 18, 27, -1), (9, 20, 29, 1), (9, 22, 31, -1), (9, 32, 41, 1), (9, 34, 43, 1), (9, 36, 45, -1), (9, 38, 47, -1), (9, 48, 57, 1), (9, 50, 59, -1), (9, 52, 61, -1), (9, 54, 63, 1), (10, 17, 27, -1), (10, 19, 25, -1), (10, 21, 31, -1), (10, 23, 29, -1), (10, 32, 42, 1), (10, 34, 40, 1), (10, 36, 46, 1), (10, 38, 44, 1), (10, 49, 59, -1), (10, 51, 57, -1), (10, 53, 63, -1), (10, 55, 61, -1), (11, 17, 26, -1), (11, 19, 24, 1), (11, 21, 30, -1), (11, 23, 28, 1), (11, 32, 43, 1), (11, 34, 41, 1), (11, 36, 47, -1), (11, 38, 45, -1), (11, 49, 58, -1), (11, 51, 56, 1), (11, 53, 62, 1), (11, 55, 60, -1), (12, 16, 28, 1), (12, 18, 30, 1), (12, 20, 24, 1), (12, 22, 26, 1), (12, 33, 45, -1), (12, 35, 47, -1), (12, 37, 41, -1), (12, 39, 43, -1), (12, 49, 61, -1), (12, 51, 63, -1), (12, 53, 57, -1), (12, 55, 59, -1), (13, 16, 29, 1), (13, 18, 31, -1), (13, 20, 25, 1), (13, 22, 27, -1), (13, 33, 44, -1), (13, 35, 46, -1), (13, 37, 40, 1), (13, 39, 42, 1), (13, 49, 60, -1), (13, 51, 62, 1), (13, 53, 56, 1), (13, 55, 58, -1), (14, 17, 31, -1), (14, 19, 29, -1), (14, 21, 27, -1), (14, 23, 25, -1), (14, 33, 47, -1), (14, 35, 45, -1), (14, 37, 43, -1), (14, 39, 41, -1), (14, 48, 62, 1), (14, 50, 60, 1), (14, 52, 58, 1), (14, 54, 56, 1), (15, 17, 30, -1), (15, 19, 28, 1), (15, 21, 26, -1), (15, 23, 24, 1), (15, 33, 46, -1), (15, 35, 44, -1), (15, 37, 42, 1), (15, 39, 40, 1), (15, 48, 63, 1), (15, 50, 61, -1), (15, 52, 59, -1), (15, 54, 57, 1), (16, 32, 48, 1), (16, 33, 49, 1), (16, 36, 52, 1), (16, 37, 53, 1), (16, 40, 56, 1), (16, 41, 57, 1), (16, 44, 60, 1), (16, 45, 61, 1), (17, 32, 49, 1), (17, 33, 48, 1), (17, 36, 53, 1), (17, 37, 52, 1), (17, 42, 59, -1), (17, 43, 58, -1), (17, 46, 63, -1), (17, 47, 62, -1), (18, 32, 50, 1), (18, 33, 51, 1), (18, 36, 54, -1), (18, 37, 55, -1), (18, 40, 58, 1), (18, 41, 59, -1), (18, 44, 62, -1), (18, 45, 63, 1), (19, 32, 51, 1), (19, 33, 50, 1), (19, 36, 55, -1), (19, 37, 54, -1), (19, 42, 57, -1), (19, 43, 56, 1), (19, 46, 61, 1), (19, 47, 60, -1), (20, 34, 54, -1), (20, 35, 55, -1), (20, 38, 50, -1), (20, 39, 51, -1), (20, 42, 62, -1), (20, 43, 63, -1), (20, 46, 58, -1), (20, 47, 59, -1), (21, 34, 55, -1), (21, 35, 54, -1), (21, 38, 51, -1), (21, 39, 50, -1), (21, 40, 61, 1), (21, 41, 60, 1), (21, 44, 57, 1), (21, 45, 56, 1), (22, 34, 52, -1), (22, 35, 53, -1), (22, 38, 48, 1), (22, 39, 49, 1), (22, 42, 60, -1), (22, 43, 61, 1), (22, 46, 56, 1), (22, 47, 57, -1), (23, 34, 53, -1), (23, 35, 52, -1), (23, 38, 49, 1), (23, 39, 48, 1), (23, 40, 63, 1), (23, 41, 62, -1), (23, 44, 59, -1), (23, 45, 58, 1), (24, 32, 56, 1), (24, 35, 59, 1), (24, 36, 60, 1), (24, 39, 63, 1), (24, 40, 48, 1), (24, 43, 51, 1), (24, 44, 52, 1), (24, 47, 55, 1), (25, 32, 57, 1), (25, 35, 58, 1), (25, 36, 61, -1), (25, 39, 62, -1), (25, 41, 48, 1), (25, 42, 51, -1), (25, 45, 52, -1), (25, 46, 55, 1), (26, 32, 58, 1), (26, 35, 57, 1), (26, 36, 62, -1), (26, 39, 61, -1), (26, 40, 50, 1), (26, 43, 49, -1), (26, 44, 54, -1), (26, 47, 53, 1), (27, 32, 59, 1), (27, 35, 56, 1), (27, 36, 63, 1), (27, 39, 60, 1), (27, 41, 50, -1), (27, 42, 49, -1), (27, 45, 54, -1), (27, 46, 53, -1), (28, 33, 61, -1), (28, 34, 62, -1), (28, 37, 57, -1), (28, 38, 58, -1), (28, 41, 53, -1), (28, 42, 54, -1), (28, 45, 49, -1), (28, 46, 50, -1), (29, 33, 60, -1), (29, 34, 63, -1), (29, 37, 56, 1), (29, 38, 59, 1), (29, 40, 53, 1), (29, 43, 54, -1), (29, 44, 49, -1), (29, 47, 50, 1), (30, 33, 63, -1), (30, 34, 60, -1), (30, 37, 59, 1), (30, 38, 56, 1), (30, 41, 55, 1), (30, 42, 52, -1), (30, 45, 51, -1), (30, 46, 48, 1), (31, 33, 62, -1), (31, 34, 61, -1), (31, 37, 58, -1), (31, 38, 57, -1), (31, 40, 55, 1), (31, 43, 52, 1), (31, 44, 51, 1), (31, 47, 48, 1)]

set_option maxRecDepth 8192 in
lemma orb0_A27_eq : orb0_A27 = A27_list := by rfl
set_option maxRecDepth 8192 in
lemma orb0_B36_eq : orb0_B36 = B36_list := by rfl
set_option maxRecDepth 8192 in
lemma orb0_wlines_eq : orb0_wlines = wlines315 := by rfl

def orb0_actionB36Go (g : Nat) (revUs : List Nat) : Nat → List Nat → List ℤ → Option (List Nat × List ℤ)
  | 0, rP, rS => some (rP.reverse, rS.reverse)
  | rem + 1, rP, rS =>
    let i := Nat.sub 35 rem
    let p0 := orb0_B36.getD i 0
    let (cur, sg) := revUs.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p0, (1 : ℤ))
    match orb0_B36.idxOf? cur with
    | none => none
    | some j =>
      let sgTot := sg * (if symp3 g p0 == 0 then 1 else -1)
      orb0_actionB36Go g revUs rem (j :: rP) (sgTot :: rS)

def orb0_actionB36 (g : Nat) (us : List Nat) : Option (List Nat × List ℤ) :=
  if !(g < 64 && us.all fun u => u < 64 && Q3_form 9 u == 1) then none
  else
    let s27 := rep27_vecs.getD 0 []
    let sAInitArr : List ℤ := (List.range 64).map fun v => match orb0_A27.idxOf? v with | some i => s27.getD i 0 | none => 0
    let sAOut := applyGauge3Nat g (applyWord3Nat us (fun v => sAInitArr.getD v 0))
    if !((List.range 27).all fun i => sAOut (orb0_A27.getD i 0) == s27.getD i 0) then none
    else orb0_actionB36Go g us.reverse 36 [] []

def orb0_checkMapsU (h : Nat) (g : Nat) (us : List Nat) : Bool :=
  match orb0_actionB36 g us with
  | none => false
  | some (perm, sgn) =>
    let allPos := (List.range 36).all fun i => orb0_u h (perm.getD i 0) * sgn.getD i 0 == orb0_u0 i
    let allNeg := (List.range 36).all fun i => orb0_u h (perm.getD i 0) * sgn.getD i 0 == -orb0_u0 i
    allPos || allNeg

def orb0_checkStabU0 (target0 : Nat) (g : Nat) (us : List Nat) : Option (List Nat) :=
  match orb0_actionB36 g us with
  | none => none
  | some (perm, sgn) =>
    let allPos := (List.range 36).all fun i => orb0_u0 (perm.getD i 0) * sgn.getD i 0 == orb0_u0 i
    let allNeg := (List.range 36).all fun i => orb0_u0 (perm.getD i 0) * sgn.getD i 0 == -orb0_u0 i
    if (allPos || allNeg) && (perm.getD 0 99 == target0) then some perm else none

def orb0_checkHitsSp42 (mask : Nat) (spId : Nat) (us : List Nat) : Bool :=
  (spId < 42) && (us.all fun u => u < 64) &&
  let s27 := rep27_vecs.getD 0 []
  let sInitArr : List ℤ := (List.range 64).map fun v =>
    match orb0_A27.idxOf? v with
    | some idxA => s27.getD idxA 0
    | none =>
      match orb0_B36.idxOf? v with
      | some idxB =>
        let fl := if ((mask >>> idxB) &&& 1) == 1 then (-1 : ℤ) else 1
        orb0_u0 idxB * fl
      | none => 0
  let sOutArr : List ℤ := (List.range 64).map fun v => applyWord3Nat us (fun w => sInitArr.getD w 0) v
  let tgt := sp42S64List.getD spId []
  orb0_wlines.all fun (a, b, c, _) =>
    sOutArr.getD a 0 * sOutArr.getD b 0 * sOutArr.getD c 0 == getS64 tgt a * getS64 tgt b * getS64 tgt c

/-- Literal precomputed `Mt` table (`36 × 36`) for fast pure-kernel `by rfl` checks. -/
def orb0_Mt_rows : List (List ℤ) := [[0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0], [-1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1], [-1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1], [-1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, -1, 1, 1, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, -1, 0, 1, 0, 0, -1, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, -1, 0, 1, -1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 1], [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 1, 1, 0, 0, 1, 1, 0, -1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 1, 1, 0, 1, 0, -1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, -1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 1, 0, 1, 0, -1, 1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, -1, 0, 0, 1, 0, 1, 0, 0, 1, -1, 0, 0, 1, 0, 1], [1, 0, -1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 1, 1, 0, 1, 0, 0, 0, -1, 1], [1, 0, 1, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1], [1, 0, -1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, -1, 0, 0, 0, 1, 0, 1, 1, -1, 0, 0], [1, 0, 1, 0, 1, -1, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, -1], [0, 1, 0, 1, 0, 1, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, -1, 0, 0, 1, 1, 0, 0, 0, 1, -1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 0, 1, 1, 0, -1, 1, 0, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, -1, 1, 1, 0, 0, -1, 0, 0, 1], [1, 1, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 0, 0, 1, 1, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0], [1, -1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 1], [1, -1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, -1, 0, 0], [0, 0, 1, 1, -1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, -1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, -1, 1, 0, 1, 0, 0, 1, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 0, -1, 0, 0, 1, 0, 1, -1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, -1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, -1], [1, 0, 0, -1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 1, 1, 0, 0, 1, 0, 0, -1, 1, 0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, -1, 1, 0, 0, 0, 0, -1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, -1, 0, 0, 0, 0, 1, -1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0, 0, 0], [1, 0, 0, -1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, -1, 0, 0, 0, 1, 1, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0, 0, 1, 0, -1, 1, 0, 0, 0, 1, 1, 1, 0, 0, -1, 0, 1, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 1, -1, 0, 1, 0, 0, 1, 0, 0, -1, 1, 0, 1, 1, 0, 0, 1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 1, 0, 0, -1, 0, 1, 1, 0, -1, 1, 0, 0, 0, 1, 1, 0, 1, 0, -1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 1, 1, 0, 0, -1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma orb0_Mt_rows_eq : orb0_Mt_rows = (List.range 36).map (fun i => (List.range 36).map fun j => orb0_Mt i j) := by rfl

def orb0_Mt_fast (i j : Nat) : ℤ := (orb0_Mt_rows.getD i []).getD j 0

/-- 1. Exact spectral identity `R₃₆² = 36 R₃₆` + `M₀` / `Mt` degrees + `f₂₇ = 9`! -/
def checkOrb0Spectral : Bool :=
  let M0rows := (List.range 36).map fun i => (List.range 36).map fun j =>
    orb0_Mt_fast i j * orb0_u0 i * orb0_u0 j
  let getM0 := fun i j => (M0rows.getD i []).getD j 0
  let Rrows := (List.range 36).map fun i => (List.range 36).map fun j =>
    (if i == j then (18 : ℤ) else 0) - 6 * getM0 i j +
    orb0_u 0 i * orb0_u 0 j + orb0_u 1 i * orb0_u 1 j + orb0_u 2 i * orb0_u 2 j
  let getR := fun i j => (Rrows.getD i []).getD j 0
  -- Exact `R² = 36 R` and symmetry of `R` & `M₀`
  ((List.range 36).all fun i =>
    (List.range 36).all fun j =>
      let dot := (List.range 36).foldl (fun acc k => acc + getR i k * getR k j) (0 : ℤ)
      (dot == 36 * getR i j) && (getM0 i j == getM0 j i) &&
      ((getM0 i j != 0) == (i != j && symp3 (B36_val i) (B36_val j) == 0)) &&
      (getM0 i j == 0 || getM0 i j == 1 || getM0 i j == -1)) &&
  -- `u_h[i] ∈ {±1}`
  ((List.range 3).all fun h => (List.range 36).all fun i => orb0_u h i == 1 || orb0_u h i == -1) &&
  -- Every vertex in `Mt` has `deg_+ = 12`, `deg_- = 3` (hence `M₀` degree `15`!)
  ((List.range 36).all fun i =>
    let dp := ((List.range 36).filter fun j => orb0_Mt_fast i j == 1).length
    let dn := ((List.range 36).filter fun j => orb0_Mt_fast i j == -1).length
    dp == 12 && dn == 3) &&
  -- `f₂₇ = 9` for `rep27[0]` (`54` ordered frustrated pairs in `A27`)
  let s27 := rep27_vecs.getD 0 []
  let f27_ord := (List.range 27).foldl (fun acc i =>
    acc + ((List.range 27).filter fun j =>
      let ai := orb0_A27.getD i 0; let aj := orb0_A27.getD j 0
      if i == j || symp3 ai aj != 0 then false
      else match orb0_A27.idxOf? (ai ^^^ aj) with
        | some k => gamma3_sgn ai aj * s27.getD i 0 * s27.getD j 0 * s27.getD k 0 == -1
        | none => false).length) 0
  f27_ord == 54

/-- 2. Exact `4 × K_{3,3,3}` 3-coloring + `C₄`-free 3-regularity + `{0..9}^4` exhaustive bound! -/
def bipBnd (s t : Nat) : Nat :=
  min (min (3 * s) (3 * t))
    (min (min (s + t * (t - 1) / 2) (t + s * (s - 1) / 2))
         (min ((3 * s + t * (t - 1) / 2) / 2) ((3 * t + s * (s - 1) / 2) / 2)))

def checkOrb0Blocks : Bool :=
  -- `blk ∈ 0..3`, `col3 ∈ 0..2`, each block has size 9
  ((List.range 36).all fun i => orb0_blk.getD i 99 < 4 && orb0_col3.getD i 99 < 3) &&
  ((List.range 4).all fun b => ((List.range 36).filter fun i => orb0_blk.getD i 99 == b).length == 9) &&
  -- Intra-block: no monochromatic +1 edges; (0,1) and (2,3): zero +1 edges
  ((List.range 36).all fun i =>
    (List.range 36).all fun j =>
      let bi := orb0_blk.getD i 99; let bj := orb0_blk.getD j 99
      if orb0_Mt_fast i j == 1 then
        if bi == bj then orb0_col3.getD i 99 != orb0_col3.getD j 99
        else !((bi == 0 && bj == 1) || (bi == 1 && bj == 0) || (bi == 2 && bj == 3) || (bi == 3 && bj == 2))
      else true) &&
  -- Cross-block `(0,2), (0,3), (1,2), (1,3)`: every vertex has +1-degree ≤ 3 and any 2 distinct vertices in one block have ≤ 1 common +1-neighbor in the other!
  ([(0, 2), (0, 3), (1, 2), (1, 3)].all fun (a, b) =>
    let ptsA := (List.range 36).filter fun i => orb0_blk.getD i 99 == a
    let ptsB := (List.range 36).filter fun i => orb0_blk.getD i 99 == b
    (ptsA.all fun u => (ptsB.filter fun v => orb0_Mt_fast u v == 1).length ≤ 3) &&
    (ptsB.all fun v => (ptsA.filter fun u => orb0_Mt_fast u v == 1).length ≤ 3) &&
    (ptsA.all fun u1 => ptsA.all fun u2 =>
      if u1 < u2 then (ptsB.filter fun v => orb0_Mt_fast u1 v == 1 && orb0_Mt_fast u2 v == 1).length ≤ 1
      else true) &&
    (ptsB.all fun v1 => ptsB.all fun v2 =>
      if v1 < v2 then (ptsA.filter fun u => orb0_Mt_fast u v1 == 1 && orb0_Mt_fast u v2 == 1).length ≤ 1
      else true)) &&
  -- Exhaustive `{0..9}^4` check: for `6 ≤ s0+s1+s2+s3 ≤ 10`, `e_+_ub ≥ 9*k - 29` ONLY at the 4 whole 9-blocks!
  ((List.range 10).all fun s0 =>
    (List.range 10).all fun s1 =>
      (List.range 10).all fun s2 =>
        (List.range 10).all fun s3 =>
          let k := s0 + s1 + s2 + s3
          if 6 ≤ k && k ≤ 10 then
            let ub := (2 * s0 * s0) / 3 + (2 * s1 * s1) / 3 + (2 * s2 * s2) / 3 + (2 * s3 * s3) / 3 +
              2 * (bipBnd s0 s2 + bipBnd s0 s3 + bipBnd s1 s2 + bipBnd s1 s3)
            if 9 * k - 29 ≤ ub then
              (s0 == 9 && s1 == 0 && s2 == 0 && s3 == 0) ||
              (s0 == 0 && s1 == 9 && s2 == 0 && s3 == 0) ||
              (s0 == 0 && s1 == 0 && s2 == 9 && s3 == 0) ||
              (s0 == 0 && s1 == 0 && s2 == 0 && s3 == 9)
            else true
          else true)

/-- 3. Symmetries `U1_TO_U0`, `U2_TO_U0`, `36 V_TO_0`, `12 STAB_U0_0`, and `np0`. -/
def checkOrb0Syms : Bool :=
  (orb0_np0.length == 12) &&
  (orb0_np0.all fun v => 0 < v && v < 36 && orb0_Mt_fast 0 v == 1) &&
  ((List.range 36).all fun v => if 0 < v && orb0_Mt_fast 0 v == 1 then orb0_np0.contains v else true) &&
  orb0_checkMapsU 1 orb0_u1ToU0.1 orb0_u1ToU0.2 &&
  orb0_checkMapsU 2 orb0_u2ToU0.1 orb0_u2ToU0.2 &&
  ((List.range 36).all fun v =>
    let (g, us) := orb0_vTo0.getD v (0, [])
    (orb0_checkStabU0 v g us).isSome) &&
  (orb0_stabU00.all fun (g, us) => (orb0_checkStabU0 0 g us).isSome)

/-- 4. All 4 whole 9-blocks + all 134 canonical `k ≤ 5` subsets hit `sp42Certs`! -/
def checkOrb0Hits : Bool :=
  let blkMasks := (List.range 4).map fun b =>
    (List.range 36).foldl (fun m i => if orb0_blk.getD i 99 == b then m ||| (1 <<< i) else m) 0
  ((List.range 4).all fun b =>
    let (spId, us) := orb0_blocks9.getD b (0, [])
    orb0_checkHitsSp42 (blkMasks.getD b 0) spId us) &&
  (orb0_canonK5.all fun (m, spId, us) => orb0_checkHitsSp42 m spId us)

/-- 5. Fast `O(k + log 134)` exhaustive `k ≤ 5` coverage by `STAB_U0_0` into `orb0_canonK5`! -/
inductive NatBST where
  | leaf
  | node (val : Nat) (l r : NatBST)

def NatBST.mem (x : Nat) : NatBST → Bool
  | NatBST.leaf => false
  | NatBST.node v l r =>
    if Nat.beq x v then true
    else if Nat.ble x v then l.mem x
    else r.mem x

def NatBST.allIn (ms : List Nat) : NatBST → Bool
  | NatBST.leaf => true
  | NatBST.node v l r => ms.contains v && l.allIn ms && r.allIn ms

def orb0_stabPerms : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [0, 3, 2, 1, 9, 8, 7, 6, 5, 4, 11, 10, 12, 15, 14, 13, 19, 18, 17, 16, 30, 29, 28, 31, 32, 33, 34, 35, 22, 21, 20, 23, 24, 25, 26, 27], [0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 11, 10, 14, 15, 12, 13, 19, 18, 17, 16, 21, 20, 23, 22, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32], [0, 3, 2, 1, 8, 9, 6, 7, 4, 5, 10, 11, 14, 13, 12, 15, 16, 17, 18, 19, 29, 30, 31, 28, 35, 34, 33, 32, 23, 20, 21, 22, 27, 26, 25, 24], [0, 1, 3, 2, 4, 5, 6, 7, 10, 11, 8, 9, 28, 29, 31, 30, 32, 33, 34, 35, 20, 21, 23, 22, 24, 25, 26, 27, 12, 13, 15, 14, 16, 17, 18, 19], [0, 1, 3, 2, 5, 4, 7, 6, 11, 10, 9, 8, 31, 30, 28, 29, 35, 34, 33, 32, 21, 20, 22, 23, 27, 26, 25, 24, 14, 15, 13, 12, 19, 18, 17, 16], [0, 2, 3, 1, 10, 11, 6, 7, 4, 5, 8, 9, 31, 29, 28, 30, 32, 33, 34, 35, 13, 15, 14, 12, 19, 18, 17, 16, 22, 20, 21, 23, 27, 26, 25, 24], [0, 3, 1, 2, 8, 9, 6, 7, 10, 11, 4, 5, 23, 20, 22, 21, 27, 26, 25, 24, 29, 30, 28, 31, 35, 34, 33, 32, 14, 13, 15, 12, 16, 17, 18, 19], [0, 2, 1, 3, 11, 10, 7, 6, 9, 8, 5, 4, 23, 21, 22, 20, 24, 25, 26, 27, 15, 13, 14, 12, 16, 17, 18, 19, 28, 30, 29, 31, 35, 34, 33, 32], [0, 2, 1, 3, 10, 11, 6, 7, 8, 9, 4, 5, 22, 20, 23, 21, 27, 26, 25, 24, 13, 15, 12, 14, 19, 18, 17, 16, 31, 29, 30, 28, 32, 33, 34, 35], [0, 2, 3, 1, 11, 10, 7, 6, 5, 4, 9, 8, 28, 30, 31, 29, 35, 34, 33, 32, 15, 13, 12, 14, 16, 17, 18, 19, 23, 21, 20, 22, 24, 25, 26, 27], [0, 3, 1, 2, 9, 8, 7, 6, 11, 10, 5, 4, 22, 21, 23, 20, 24, 25, 26, 27, 30, 29, 31, 28, 32, 33, 34, 35, 12, 15, 13, 14, 19, 18, 17, 16]]
def orb0_stabInvPerms : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [0, 3, 2, 1, 9, 8, 7, 6, 5, 4, 11, 10, 12, 15, 14, 13, 19, 18, 17, 16, 30, 29, 28, 31, 32, 33, 34, 35, 22, 21, 20, 23, 24, 25, 26, 27], [0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 11, 10, 14, 15, 12, 13, 19, 18, 17, 16, 21, 20, 23, 22, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32], [0, 3, 2, 1, 8, 9, 6, 7, 4, 5, 10, 11, 14, 13, 12, 15, 16, 17, 18, 19, 29, 30, 31, 28, 35, 34, 33, 32, 23, 20, 21, 22, 27, 26, 25, 24], [0, 1, 3, 2, 4, 5, 6, 7, 10, 11, 8, 9, 28, 29, 31, 30, 32, 33, 34, 35, 20, 21, 23, 22, 24, 25, 26, 27, 12, 13, 15, 14, 16, 17, 18, 19], [0, 1, 3, 2, 5, 4, 7, 6, 11, 10, 9, 8, 31, 30, 28, 29, 35, 34, 33, 32, 21, 20, 22, 23, 27, 26, 25, 24, 14, 15, 13, 12, 19, 18, 17, 16], [0, 3, 1, 2, 8, 9, 6, 7, 10, 11, 4, 5, 23, 20, 22, 21, 27, 26, 25, 24, 29, 30, 28, 31, 35, 34, 33, 32, 14, 13, 15, 12, 16, 17, 18, 19], [0, 2, 3, 1, 10, 11, 6, 7, 4, 5, 8, 9, 31, 29, 28, 30, 32, 33, 34, 35, 13, 15, 14, 12, 19, 18, 17, 16, 22, 20, 21, 23, 27, 26, 25, 24], [0, 2, 1, 3, 11, 10, 7, 6, 9, 8, 5, 4, 23, 21, 22, 20, 24, 25, 26, 27, 15, 13, 14, 12, 16, 17, 18, 19, 28, 30, 29, 31, 35, 34, 33, 32], [0, 2, 1, 3, 10, 11, 6, 7, 8, 9, 4, 5, 22, 20, 23, 21, 27, 26, 25, 24, 13, 15, 12, 14, 19, 18, 17, 16, 31, 29, 30, 28, 32, 33, 34, 35], [0, 3, 1, 2, 9, 8, 7, 6, 11, 10, 5, 4, 22, 21, 23, 20, 24, 25, 26, 27, 30, 29, 31, 28, 32, 33, 34, 35, 12, 15, 13, 14, 19, 18, 17, 16], [0, 2, 3, 1, 11, 10, 7, 6, 5, 4, 9, 8, 28, 30, 31, 29, 35, 34, 33, 32, 15, 13, 12, 14, 16, 17, 18, 19, 23, 21, 20, 22, 24, 25, 26, 27]]
def orb0_canonBST : NatBST := (NatBST.node 1052801 (NatBST.node 20545 (NatBST.node 4099 (NatBST.node 65 (NatBST.node 17 (NatBST.node 3 (NatBST.node 1 (NatBST.node 0 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 7 NatBST.leaf NatBST.leaf)) (NatBST.node 21 (NatBST.node 19 NatBST.leaf NatBST.leaf) (NatBST.node 49 NatBST.leaf NatBST.leaf))) (NatBST.node 193 (NatBST.node 81 (NatBST.node 67 NatBST.leaf NatBST.leaf) (NatBST.node 97 NatBST.leaf NatBST.leaf)) (NatBST.node 289 (NatBST.node 273 NatBST.leaf NatBST.leaf) (NatBST.node 4097 NatBST.leaf NatBST.leaf)))) (NatBST.node 8209 (NatBST.node 5121 (NatBST.node 4129 (NatBST.node 4113 (NatBST.node 4101 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 4161 NatBST.leaf NatBST.leaf)) (NatBST.node 8195 (NatBST.node 8193 NatBST.leaf NatBST.leaf) (NatBST.node 8197 NatBST.leaf NatBST.leaf))) (NatBST.node 9217 (NatBST.node 8257 (NatBST.node 8225 NatBST.leaf NatBST.leaf) (NatBST.node 8321 NatBST.leaf NatBST.leaf)) (NatBST.node 12289 (NatBST.node 10241 NatBST.leaf NatBST.leaf) (NatBST.node 20481 NatBST.leaf NatBST.leaf))))) (NatBST.node 131075 (NatBST.node 65601 (NatBST.node 65539 (NatBST.node 40961 (NatBST.node 28673 (NatBST.node 21505 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 65537 NatBST.leaf NatBST.leaf)) (NatBST.node 65553 (NatBST.node 65541 NatBST.leaf NatBST.leaf) (NatBST.node 65569 NatBST.leaf NatBST.leaf))) (NatBST.node 69633 (NatBST.node 66561 (NatBST.node 65665 NatBST.leaf NatBST.leaf) (NatBST.node 67585 NatBST.leaf NatBST.leaf)) (NatBST.node 98305 (NatBST.node 73729 NatBST.leaf NatBST.leaf) (NatBST.node 131073 NatBST.leaf NatBST.leaf)))) (NatBST.node 139265 (NatBST.node 131201 (NatBST.node 131105 (NatBST.node 131089 (NatBST.node 131077 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 131137 NatBST.leaf NatBST.leaf)) (NatBST.node 133121 (NatBST.node 132097 NatBST.leaf NatBST.leaf) (NatBST.node 135169 NatBST.leaf NatBST.leaf))) (NatBST.node 393217 (NatBST.node 196609 (NatBST.node 163841 NatBST.leaf NatBST.leaf) (NatBST.node 327681 NatBST.leaf NatBST.leaf)) (NatBST.node 1052673 (NatBST.node 589825 NatBST.leaf NatBST.leaf) (NatBST.node 1052737 NatBST.leaf NatBST.leaf)))))) (NatBST.node 4268033 (NatBST.node 1318913 (NatBST.node 1069057 (NatBST.node 1057281 (NatBST.node 1056769 (NatBST.node 1054721 (NatBST.node 1053185 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 1056801 NatBST.leaf NatBST.leaf)) (NatBST.node 1064961 (NatBST.node 1060865 NatBST.leaf NatBST.leaf) (NatBST.node 1067009 NatBST.leaf NatBST.leaf))) (NatBST.node 1114113 (NatBST.node 1081345 (NatBST.node 1073153 NatBST.leaf NatBST.leaf) (NatBST.node 1085441 NatBST.leaf NatBST.leaf)) (NatBST.node 1310721 (NatBST.node 1179649 NatBST.leaf NatBST.leaf) (NatBST.node 1314817 NatBST.leaf NatBST.leaf)))) (NatBST.node 4206593 (NatBST.node 4198417 (NatBST.node 1581057 (NatBST.node 1576961 (NatBST.node 1572865 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 4198401 NatBST.leaf NatBST.leaf)) (NatBST.node 4198465 (NatBST.node 4198433 NatBST.leaf NatBST.leaf) (NatBST.node 4198529 NatBST.leaf NatBST.leaf))) (NatBST.node 4218881 (NatBST.node 4210753 (NatBST.node 4210689 NatBST.leaf NatBST.leaf) (NatBST.node 4214785 NatBST.leaf NatBST.leaf)) (NatBST.node 4259841 (NatBST.node 4231169 NatBST.leaf NatBST.leaf) (NatBST.node 4263937 NatBST.leaf NatBST.leaf))))) (NatBST.node 269500417 (NatBST.node 16908289 (NatBST.node 6356993 (NatBST.node 4718593 (NatBST.node 4456449 (NatBST.node 4325377 NatBST.leaf NatBST.leaf) NatBST.leaf) (NatBST.node 5255169 NatBST.leaf NatBST.leaf)) (NatBST.node 12648449 (NatBST.node 12603393 NatBST.leaf NatBST.leaf) (NatBST.node 16842753 NatBST.leaf NatBST.leaf))) (NatBST.node 33816577 (NatBST.node 17301505 (NatBST.node 17039361 NatBST.leaf NatBST.leaf) (NatBST.node 33685505 NatBST.leaf NatBST.leaf)) (NatBST.node 269492225 (NatBST.node 269488129 NatBST.leaf NatBST.leaf) (NatBST.node 269496321 NatBST.leaf NatBST.leaf)))) (NatBST.node 276844545 (NatBST.node 270008321 (NatBST.node 269516801 (NatBST.node 269504513 NatBST.leaf NatBST.leaf) (NatBST.node 269520897 NatBST.leaf NatBST.leaf)) (NatBST.node 272633857 (NatBST.node 270536705 NatBST.leaf NatBST.leaf) (NatBST.node 273682433 NatBST.leaf NatBST.leaf))) (NatBST.node 537939969 (NatBST.node 537927681 (NatBST.node 277348353 NatBST.leaf NatBST.leaf) (NatBST.node 537931777 NatBST.leaf NatBST.leaf)) (NatBST.node 538181633 (NatBST.node 537952257 NatBST.leaf NatBST.leaf) (NatBST.node 538443777 NatBST.leaf NatBST.leaf)))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma orb0_stabPerms_eq :
    (orb0_stabU00.filterMap fun (g, us) => orb0_checkStabU0 0 g us) = orb0_stabPerms := by rfl

set_option maxRecDepth 20000 in
lemma orb0_stabInvPerms_ok :
    (orb0_stabPerms.length == orb0_stabInvPerms.length &&
    (List.zip orb0_stabPerms orb0_stabInvPerms).all fun (p, invP) =>
      p.length == 36 && invP.length == 36 &&
      (List.range 36).all fun i =>
        p.getD i 0 < 36 && invP.getD i 0 < 36 &&
        p.getD (invP.getD i 0) 0 == i && invP.getD (p.getD i 0) 0 == i) = true := by rfl

set_option maxRecDepth 20000 in
lemma orb0_canonBST_ok :
    orb0_canonBST.allIn (orb0_canonK5.map fun (m, _, _) => m) = true := by rfl

def applyInvPerm36 (invP : List Nat) (vs : List Nat) : Nat :=
  vs.foldl (fun nm v => Nat.lor nm (Nat.shiftLeft 1 (invP.getD v 0))) 0

def orb0_isCovVs (vs : List Nat) : Bool :=
  orb0_stabInvPerms.any fun invP => orb0_canonBST.mem (applyInvPerm36 invP vs)

def checkOrb0K5Cover : Bool :=
  -- k = 0, 1
  orb0_isCovVs [] && orb0_isCovVs [0] &&
  -- k = 2: {0, a}
  ((List.range 35).all fun a' => orb0_isCovVs [0, a' + 1]) &&
  -- k = 3: {0, a, b}
  ((List.range 35).all fun a' =>
    let a := a' + 1
    (List.range (35 - a)).all fun db =>
      let b := a + 1 + db
      orb0_isCovVs [0, a, b]) &&
  -- k = 4: {0, a, b, c} with a < b in np0, c ≠ 0, a, b, w ≥ 4
  ((List.range 12).all fun i1 =>
    let a := orb0_np0.getD i1 0
    (List.range (11 - i1)).all fun di2 =>
      let b := orb0_np0.getD (i1 + 1 + di2) 0
      (List.range 35).all fun c' =>
        let c := c' + 1
        if c == a || c == b then true
        else
          let w3 := 2 + orb0_Mt_fast 0 c + orb0_Mt_fast a b + orb0_Mt_fast a c + orb0_Mt_fast b c
          if 4 ≤ w3 then orb0_isCovVs [0, a, b, c] else true) &&
  -- k = 5: {0, a, b, c, d} with a < b < c < d in np0, w ≥ 8
  ((List.range 12).all fun i1 =>
    let a := orb0_np0.getD i1 0
    (List.range (11 - i1)).all fun di2 =>
      let i2 := i1 + 1 + di2
      let b := orb0_np0.getD i2 0
      (List.range (11 - i2)).all fun di3 =>
        let i3 := i2 + 1 + di3
        let c := orb0_np0.getD i3 0
        (List.range (11 - i3)).all fun di4 =>
          let d := orb0_np0.getD (i3 + 1 + di4) 0
          let w4 := 4 + orb0_Mt_fast a b + orb0_Mt_fast a c + orb0_Mt_fast a d +
            orb0_Mt_fast b c + orb0_Mt_fast b d + orb0_Mt_fast c d
          if 8 ≤ w4 then orb0_isCovVs [0, a, b, c, d] else true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma checkOrb0Spectral_ok : checkOrb0Spectral = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma checkOrb0Blocks_ok : checkOrb0Blocks = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma checkOrb0Syms_ok : checkOrb0Syms = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
lemma checkOrb0Hits_ok : checkOrb0Hits = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
lemma checkOrb0K5Cover_ok : checkOrb0K5Cover = true := by rfl

end FourQubitCD

end MultiQubitMUB
