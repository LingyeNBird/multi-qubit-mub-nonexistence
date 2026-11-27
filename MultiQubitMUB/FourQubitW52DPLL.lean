import MultiQubitMUB.FourQubitQminus52
import MultiQubitMUB.FourQubitCDCerts

set_option linter.constructorNameAsVariable false

/-!
# Shared 36-Bit + 144-Bit SIMD-in-a-`Nat` DPLL Engine for Parts 2a & 2b (Orbits 2 and 1)

Provides the pure-kernel verifier (`checkStabCovers`, `checkPatList`, `checkTree36`) and its
complete soundness theorem for ruling out Orbit 2 (`f₂₇ = 13`) and classifying Orbit 1 (`f₂₇ = 12`)
into the 42 certified `Sp(6,2)` orbits `sp42Certs`.
-/

namespace MultiQubitMUB

namespace FourQubitCD

/-! ### Section 1: Pure-Computable 36-Bit + 144-Bit SIMD-in-a-`Nat` DPLL Verifier -/

def otherC27_list : List Nat :=
  (List.range 64).filter fun c => c != 0 && c != 9 && Q3_0 c == 1

def pop9 (n : Nat) : Nat :=
  let n := Nat.sub n (Nat.land (Nat.shiftRight n 1) 85)
  let n := Nat.add (Nat.land n 307) (Nat.land (Nat.shiftRight n 2) 51)
  Nat.add (Nat.add (Nat.land n 15) (Nat.land (Nat.shiftRight n 4) 15)) (Nat.shiftRight n 8)

def pop36 (m : Nat) : Nat :=
  Nat.add
    (Nat.add (pop9 (Nat.land m 511)) (pop9 (Nat.land (Nat.shiftRight m 9) 511)))
    (Nat.add (pop9 (Nat.land (Nat.shiftRight m 18) 511)) (pop9 (Nat.land (Nat.shiftRight m 27) 511)))

def M36_val (oid i j : Nat) : ℤ :=
  if i == j || symp3 (B36_val i) (B36_val j) != 0 then 0
  else
    let a := B36_val i ^^^ B36_val j
    match A27_list.idxOf? a with
    | some idxA => gamma3_sgn (B36_val i) (B36_val j) * (rep27_vecs.getD oid []).getD idxA 0
    | none => 0

def lines27_list : List (Nat × Nat × Nat × ℤ) :=
  ((List.range 27).flatMap fun i =>
    ((List.range 27).flatMap fun j =>
      if j ≤ i || symp3 (A27_val i) (A27_val j) != 0 then []
      else
        match A27_list.idxOf? (A27_val i ^^^ A27_val j) with
        | some k => if k ≤ j then [] else [(i, j, k, gamma3_sgn (A27_val i) (A27_val j))]
        | none => []))

structure Orb36Tables where
  oid : Nat
  f27 : Nat
  pAdj : List Nat
  nAdj : List Nat
  pInc : List Nat
  nInc : List Nat
  slVerts : List (List Nat)
  slMask : List Nat
  slCA : List Nat

def mkOrb36Tables (oid f27 : Nat) : Orb36Tables :=
  let s27 := rep27_vecs.getD oid []
  let pAdj := (List.range 36).map fun u =>
    (List.range 36).foldl (fun m v => if M36_val oid u v == 1 then m ||| (1 <<< v) else m) 0
  let nAdj := (List.range 36).map fun u =>
    (List.range 36).foldl (fun m v => if M36_val oid u v == -1 then m ||| (1 <<< v) else m) 0
  let pInc := (List.range 36).map fun u =>
    (List.range 36).foldl (fun acc v => if M36_val oid u v == 1 then acc + (1 <<< (4 * v)) else acc) 0
  let nInc := (List.range 36).map fun u =>
    (List.range 36).foldl (fun acc v => if M36_val oid u v == -1 then acc + (1 <<< (4 * v)) else acc) 0
  let slVerts := otherC27_list.map fun ck =>
    (List.range 36).filter fun i => Q3_form ck (B36_val i) == 0
  let slMask := slVerts.map fun vs =>
    vs.foldl (fun m v => m ||| (1 <<< v)) 0
  let slCA := otherC27_list.map fun ck =>
    lines27_list.foldl (fun acc (a, b, c, g) =>
      if Q3_form ck (A27_val a) == 0 && Q3_form ck (A27_val b) == 0 && Q3_form ck (A27_val c) == 0 &&
         g * s27.getD a 0 * s27.getD b 0 * s27.getD c 0 == -1
      then acc + 1 else acc) 0
  { oid, f27, pAdj, nAdj, pInc, nInc, slVerts, slMask, slCA }

def A27_lit : List Nat := [2, 4, 6, 16, 19, 20, 23, 26, 27, 30, 31, 32, 34, 37, 39, 44, 45, 46, 47, 48, 51, 53, 54, 58, 59, 60, 61]
def B36_lit : List Nat := [1, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 21, 22, 24, 25, 28, 29, 33, 35, 36, 38, 40, 41, 42, 43, 49, 50, 52, 55, 56, 57, 62, 63]
def wlines315_lit : List (Nat × Nat × Nat × ℤ) := [(1, 2, 3, 1), (1, 4, 5, 1), (1, 6, 7, 1), (1, 16, 17, 1), (1, 18, 19, 1), (1, 20, 21, 1), (1, 22, 23, 1), (1, 32, 33, 1), (1, 34, 35, 1), (1, 36, 37, 1), (1, 38, 39, 1), (1, 48, 49, 1), (1, 50, 51, 1), (1, 52, 53, 1), (1, 54, 55, 1), (2, 4, 6, 1), (2, 5, 7, 1), (2, 8, 10, 1), (2, 9, 11, 1), (2, 12, 14, 1), (2, 13, 15, 1), (2, 32, 34, 1), (2, 33, 35, 1), (2, 36, 38, 1), (2, 37, 39, 1), (2, 40, 42, 1), (2, 41, 43, 1), (2, 44, 46, 1), (2, 45, 47, 1), (3, 4, 7, 1), (3, 5, 6, 1), (3, 24, 27, 1), (3, 25, 26, 1), (3, 28, 31, 1), (3, 29, 30, 1), (3, 32, 35, 1), (3, 33, 34, 1), (3, 36, 39, 1), (3, 37, 38, 1), (3, 56, 59, 1), (3, 57, 58, 1), (3, 60, 63, 1), (3, 61, 62, 1), (4, 8, 12, 1), (4, 9, 13, 1), (4, 10, 14, 1), (4, 11, 15, 1), (4, 16, 20, 1), (4, 17, 21, 1), (4, 18, 22, 1), (4, 19, 23, 1), (4, 24, 28, 1), (4, 25, 29, 1), (4, 26, 30, 1), (4, 27, 31, 1), (5, 16, 21, 1), (5, 17, 20, 1), (5, 18, 23, 1), (5, 19, 22, 1), (5, 40, 45, 1), (5, 41, 44, 1), (5, 42, 47, 1), (5, 43, 46, 1), (5, 56, 61, 1), (5, 57, 60, 1), (5, 58, 63, 1), (5, 59, 62, 1), (6, 8, 14, 1), (6, 9, 15, 1), (6, 10, 12, 1), (6, 11, 13, 1), (6, 48, 54, 1), (6, 49, 55, 1), (6, 50, 52, 1), (6, 51, 53, 1), (6, 56, 62, 1), (6, 57, 63, 1), (6, 58, 60, 1), (6, 59, 61, 1), (7, 24, 31, 1), (7, 25, 30, 1), (7, 26, 29, 1), (7, 27, 28, 1), (7, 40, 47, 1), (7, 41, 46, 1), (7, 42, 45, 1), (7, 43, 44, 1), (7, 48, 55, 1), (7, 49, 54, 1), (7, 50, 53, 1), (7, 51, 52, 1), (8, 16, 24, 1), (8, 18, 26, 1), (8, 20, 28, 1), (8, 22, 30, 1), (8, 32, 40, 1), (8, 34, 42, 1), (8, 36, 44, 1), (8, 38, 46, 1), (8, 48, 56, 1), (8, 50, 58, 1), (8, 52, 60, 1), (8, 54, 62, 1), (9, 16, 25, 1), (9, 18, 27, -1), (9, 20, 29, 1), (9, 22, 31, -1), (9, 32, 41, 1), (9, 34, 43, 1), (9, 36, 45, -1), (9, 38, 47, -1), (9, 48, 57, 1), (9, 50, 59, -1), (9, 52, 61, -1), (9, 54, 63, 1), (10, 17, 27, -1), (10, 19, 25, -1), (10, 21, 31, -1), (10, 23, 29, -1), (10, 32, 42, 1), (10, 34, 40, 1), (10, 36, 46, 1), (10, 38, 44, 1), (10, 49, 59, -1), (10, 51, 57, -1), (10, 53, 63, -1), (10, 55, 61, -1), (11, 17, 26, -1), (11, 19, 24, 1), (11, 21, 30, -1), (11, 23, 28, 1), (11, 32, 43, 1), (11, 34, 41, 1), (11, 36, 47, -1), (11, 38, 45, -1), (11, 49, 58, -1), (11, 51, 56, 1), (11, 53, 62, 1), (11, 55, 60, -1), (12, 16, 28, 1), (12, 18, 30, 1), (12, 20, 24, 1), (12, 22, 26, 1), (12, 33, 45, -1), (12, 35, 47, -1), (12, 37, 41, -1), (12, 39, 43, -1), (12, 49, 61, -1), (12, 51, 63, -1), (12, 53, 57, -1), (12, 55, 59, -1), (13, 16, 29, 1), (13, 18, 31, -1), (13, 20, 25, 1), (13, 22, 27, -1), (13, 33, 44, -1), (13, 35, 46, -1), (13, 37, 40, 1), (13, 39, 42, 1), (13, 49, 60, -1), (13, 51, 62, 1), (13, 53, 56, 1), (13, 55, 58, -1), (14, 17, 31, -1), (14, 19, 29, -1), (14, 21, 27, -1), (14, 23, 25, -1), (14, 33, 47, -1), (14, 35, 45, -1), (14, 37, 43, -1), (14, 39, 41, -1), (14, 48, 62, 1), (14, 50, 60, 1), (14, 52, 58, 1), (14, 54, 56, 1), (15, 17, 30, -1), (15, 19, 28, 1), (15, 21, 26, -1), (15, 23, 24, 1), (15, 33, 46, -1), (15, 35, 44, -1), (15, 37, 42, 1), (15, 39, 40, 1), (15, 48, 63, 1), (15, 50, 61, -1), (15, 52, 59, -1), (15, 54, 57, 1), (16, 32, 48, 1), (16, 33, 49, 1), (16, 36, 52, 1), (16, 37, 53, 1), (16, 40, 56, 1), (16, 41, 57, 1), (16, 44, 60, 1), (16, 45, 61, 1), (17, 32, 49, 1), (17, 33, 48, 1), (17, 36, 53, 1), (17, 37, 52, 1), (17, 42, 59, -1), (17, 43, 58, -1), (17, 46, 63, -1), (17, 47, 62, -1), (18, 32, 50, 1), (18, 33, 51, 1), (18, 36, 54, -1), (18, 37, 55, -1), (18, 40, 58, 1), (18, 41, 59, -1), (18, 44, 62, -1), (18, 45, 63, 1), (19, 32, 51, 1), (19, 33, 50, 1), (19, 36, 55, -1), (19, 37, 54, -1), (19, 42, 57, -1), (19, 43, 56, 1), (19, 46, 61, 1), (19, 47, 60, -1), (20, 34, 54, -1), (20, 35, 55, -1), (20, 38, 50, -1), (20, 39, 51, -1), (20, 42, 62, -1), (20, 43, 63, -1), (20, 46, 58, -1), (20, 47, 59, -1), (21, 34, 55, -1), (21, 35, 54, -1), (21, 38, 51, -1), (21, 39, 50, -1), (21, 40, 61, 1), (21, 41, 60, 1), (21, 44, 57, 1), (21, 45, 56, 1), (22, 34, 52, -1), (22, 35, 53, -1), (22, 38, 48, 1), (22, 39, 49, 1), (22, 42, 60, -1), (22, 43, 61, 1), (22, 46, 56, 1), (22, 47, 57, -1), (23, 34, 53, -1), (23, 35, 52, -1), (23, 38, 49, 1), (23, 39, 48, 1), (23, 40, 63, 1), (23, 41, 62, -1), (23, 44, 59, -1), (23, 45, 58, 1), (24, 32, 56, 1), (24, 35, 59, 1), (24, 36, 60, 1), (24, 39, 63, 1), (24, 40, 48, 1), (24, 43, 51, 1), (24, 44, 52, 1), (24, 47, 55, 1), (25, 32, 57, 1), (25, 35, 58, 1), (25, 36, 61, -1), (25, 39, 62, -1), (25, 41, 48, 1), (25, 42, 51, -1), (25, 45, 52, -1), (25, 46, 55, 1), (26, 32, 58, 1), (26, 35, 57, 1), (26, 36, 62, -1), (26, 39, 61, -1), (26, 40, 50, 1), (26, 43, 49, -1), (26, 44, 54, -1), (26, 47, 53, 1), (27, 32, 59, 1), (27, 35, 56, 1), (27, 36, 63, 1), (27, 39, 60, 1), (27, 41, 50, -1), (27, 42, 49, -1), (27, 45, 54, -1), (27, 46, 53, -1), (28, 33, 61, -1), (28, 34, 62, -1), (28, 37, 57, -1), (28, 38, 58, -1), (28, 41, 53, -1), (28, 42, 54, -1), (28, 45, 49, -1), (28, 46, 50, -1), (29, 33, 60, -1), (29, 34, 63, -1), (29, 37, 56, 1), (29, 38, 59, 1), (29, 40, 53, 1), (29, 43, 54, -1), (29, 44, 49, -1), (29, 47, 50, 1), (30, 33, 63, -1), (30, 34, 60, -1), (30, 37, 59, 1), (30, 38, 56, 1), (30, 41, 55, 1), (30, 42, 52, -1), (30, 45, 51, -1), (30, 46, 48, 1), (31, 33, 62, -1), (31, 34, 61, -1), (31, 37, 58, -1), (31, 38, 57, -1), (31, 40, 55, 1), (31, 43, 52, 1), (31, 44, 51, 1), (31, 47, 48, 1)]

set_option maxRecDepth 8192 in
lemma A27_lit_eq : A27_lit = A27_list := by rfl
set_option maxRecDepth 8192 in
lemma B36_lit_eq : B36_lit = B36_list := by rfl
set_option maxRecDepth 8192 in
lemma wlines315_lit_eq : wlines315_lit = wlines315 := by rfl

def orb1_tables : Orb36Tables := {
  oid := 1
  f27 := 12
  pAdj := [4040208398, 64440172557, 64676225035, 4279173127, 23114917184, 42983361152, 79693072, 21609384480, 304208, 21559249056, 23085449552, 43033887392, 1347436545, 34914468117, 15082721284, 5779759381, 42033481882, 10773594154, 17179937162, 39216873994, 807415809, 15033630722, 35441938515, 5105025107, 41406786076, 10871783468, 17196649036, 39762100364, 2156957705, 1100489753, 675386393, 321077257, 17341990550, 34395539494, 4362339990, 8745723942]
  nAdj := [2113536, 1048576, 4096, 0, 67371008, 1757978624, 45383045120, 2462076928, 45536575488, 2419236864, 171593728, 1613778944, 51740937412, 19365102112, 547359937, 8659141152, 256, 18324915776, 9505341456, 403702880, 51540397826, 1073794817, 19327492256, 8590213280, 64, 17717011840, 9932541968, 268965152, 202113984, 33835040, 69339168, 4203456, 0, 75792704, 38940672, 1052992]
  pInc := [22685144980201116002989925839069516048, 1486693661077585427540057561427667463442689, 1486693661423727988896305780298287107018769, 22685491122780767323765542692912627985, 87453980603511195990903065779009610579968, 1399241092780166612361919763083768115494912, 20287670848818633291219379224576, 87452568623199738773254814137724712255488, 4723523909073407901696, 87452568319042822951811072615012004528128, 87453980603426706583202234404970290020352, 1399241092799260599532303133747984024469504, 1334420292954144636245354848546979841, 1393796657984992912274665685402195482181889, 5806067886935391295586323259869768974592, 341617111737087332747779752847917252865, 1394159454475611339032771424168326312562704, 5465785519935244087979661593350599872528, 87112285931760246646642346264203121135632, 1394136940351918801289654376899836842610704, 88269046614434882803637578996121601, 5806067885588513742083243503186782191632, 1393797904136164683022030884394231174070289, 340370635967843116101897618357036843025, 1394158208020049589699882341521649970516224, 5465785843186127728102401377802189279488, 87112285931839474809138163857787128385792, 1394138186504348320325566499522089930723584, 21267647937511623050575251672840278017, 1329228079966123027997510996057985025, 83401268599700698204564318817685505, 5193643756640696902810500471984129, 87112286256362999646112681428703795806480, 1393796574909431616289318955256451670475024, 340282387203348071837411515417164316944, 5444518195333106796941121175906428125456]
  nInc := [19342813185891660833226752, 1208925819614629174706176, 281474976710656, 0, 20282409608374036906816896499712, 1412629269336452267671095344447356928, 1399262365619207607188557823510647935074304, 21272841502329034189354050194853855232, 1399262365944914603760602811580314103578624, 21272840229437740829328222440371781632, 325786224886246973603511384670208, 1412304745542024853966082766532509696, 1480908861184725156254684688768850511003904, 87133553580960765385828411162131296157696, 83076754707660212311861799642202113, 5444517891017444361878777976991058493440, 4294967296, 87113615180038750651158295079777166426112, 5444606161336623680446539698518613884928, 5516815413402180174929381053956096, 1480908860839924193072886521770603937005584, 1329227995784915874128804923637235713, 87133553579692805300885512824276397326336, 5444517870735015420136432259372244008960, 16777216, 87112369008509983208588326978047277268992, 5445852291027658871133193647493482610688, 5192296858610385492538989436993536, 344800963342358627415960540151808, 1267650604950667959552573440000, 20282428946759932180785586503680, 309485009825848741651808256, 0, 20287361368532331349425411588096, 1267961294459023051448559599616, 1208925819896108463161344]
  slVerts := [[12, 13, 14, 15, 16, 17, 18, 19, 28, 29, 30, 31, 32, 33, 34, 35], [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], [0, 2, 4, 7, 8, 11, 17, 19, 20, 23, 24, 27, 30, 31, 33, 34], [0, 2, 5, 6, 9, 10, 16, 18, 20, 23, 25, 26, 30, 31, 32, 35], [0, 2, 4, 7, 8, 11, 17, 19, 21, 22, 25, 26, 28, 29, 32, 35], [0, 2, 5, 6, 9, 10, 16, 18, 21, 22, 24, 27, 28, 29, 33, 34], [1, 3, 6, 7, 10, 11, 13, 15, 21, 23, 26, 27, 29, 31, 34, 35], [1, 3, 4, 5, 8, 9, 12, 14, 21, 23, 24, 25, 28, 30, 34, 35], [1, 3, 6, 7, 10, 11, 13, 15, 20, 22, 24, 25, 28, 30, 32, 33], [1, 3, 4, 5, 8, 9, 12, 14, 20, 22, 26, 27, 29, 31, 32, 33], [0, 1, 4, 6, 9, 11, 12, 15, 16, 19, 25, 27, 29, 31, 33, 34], [0, 1, 5, 7, 8, 10, 12, 15, 17, 18, 24, 26, 29, 31, 32, 35], [0, 1, 4, 6, 9, 11, 13, 14, 17, 18, 25, 27, 28, 30, 32, 35], [0, 1, 5, 7, 8, 10, 13, 14, 16, 19, 24, 26, 28, 30, 33, 34], [2, 3, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 30, 31, 34, 35], [2, 3, 8, 9, 10, 11, 12, 13, 16, 17, 22, 23, 28, 29, 32, 33], [2, 3, 4, 5, 6, 7, 14, 15, 16, 17, 20, 21, 28, 29, 34, 35], [2, 3, 4, 5, 6, 7, 12, 13, 18, 19, 20, 21, 30, 31, 32, 33], [0, 3, 4, 7, 9, 10, 14, 15, 17, 18, 20, 22, 24, 27, 33, 35], [0, 3, 5, 6, 8, 11, 14, 15, 16, 19, 20, 22, 25, 26, 32, 34], [0, 3, 4, 7, 9, 10, 12, 13, 16, 19, 21, 23, 25, 26, 33, 35], [0, 3, 5, 6, 8, 11, 12, 13, 17, 18, 21, 23, 24, 27, 32, 34], [1, 2, 6, 7, 8, 9, 13, 14, 18, 19, 21, 22, 26, 27, 29, 30], [1, 2, 4, 5, 10, 11, 12, 15, 18, 19, 21, 22, 24, 25, 28, 31], [1, 2, 4, 5, 10, 11, 13, 14, 16, 17, 20, 23, 26, 27, 28, 31], [1, 2, 6, 7, 8, 9, 12, 15, 16, 17, 20, 23, 24, 25, 29, 30]]
  slMask := [68452085760, 68718428160, 268431360, 29152119189, 41986360933, 39567624597, 26732725861, 54435818698, 52942623546, 14282697930, 15775847226, 28622559827, 41423377827, 40165075539, 27196482979, 54774255372, 13703003916, 52348305660, 16110072060, 43106354841, 21581384041, 43061425817, 21636725097, 1819042758, 2473368630, 2626907190, 1670616006]
  slCA := [1, 1, 0, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 4]
}

def orb2_tables : Orb36Tables := {
  oid := 2
  f27 := 13
  pAdj := [4042305550, 64441221133, 64676225035, 4279173127, 23182026048, 43117578880, 96470288, 21642938912, 304208, 21559249056, 23085449552, 43033887392, 1347436545, 34914468117, 12935237636, 4706017557, 42033481882, 10773594154, 67978, 4857135626, 807415811, 15033630723, 35441938515, 5105025107, 41406786140, 10871783596, 17196649052, 39762100396, 2156957705, 1100489753, 675353625, 321060873, 17341990550, 34395539494, 4362077846, 8745199654]
  nAdj := [16384, 0, 4096, 0, 262144, 1623760896, 45366267904, 2428522496, 45536575488, 2419236864, 171593728, 1613778944, 51740937412, 19365102112, 2694843585, 9732882976, 256, 18324915776, 26685210640, 34763441248, 51540397824, 1073794816, 19327492256, 8590213280, 0, 17717011712, 9932541952, 268965120, 202113984, 33835040, 69371936, 4219840, 0, 75792704, 39202816, 1577280]
  pInc := [22685144980220458816103759905864814864, 1486693661077585428748983381042296638148865, 1486693661423727988896305780298287107018769, 22685491122780767323765542692912627985, 87453980623793605594554736202956861865984, 1399241093104685166020346489866924136071168, 20366899011332897628812923174912, 87452568624467389373483043539221415460864, 4723523909073407901696, 87452568319042822951811072615012004528128, 87453980603426706583202234404970290020352, 1399241092799260599532303133747984024469504, 1334420292954144636245354848546979841, 1393796657984992912274665685402195482181889, 5784800239002832641619862346905283461376, 340287883741302416874875945787636908289, 1394159454475611339032771424168326312562704, 5465785519935244087979661593350599872528, 18446761670459002896, 340365443754854943671984859314248486928, 88269046614434882803637578996121617, 5806067885588513742083243503186782191633, 1393797904136164683022030884394231174070289, 340370635967843116101897618357036843025, 1394158208020049589699882341521649987293440, 5465785843186127728102401377802457714944, 87112285931839474809138163857787128451328, 1394138186504348320325566499522089931772160, 21267647937511623050575251672840278017, 1329228079966123027997510996057985025, 83401268599700697051642814210838529, 5193643756640696830752906434056193, 87112286256362999646112681428703795806480, 1393796574909431616289318955256451670475024, 340282387203348067115045032547519103248, 5444518195333106721383257449992104706320]
  nInc := [72057594037927936, 0, 281474976710656, 0, 4722366482869645213696, 1412304750782793840944312188426780672, 1399262365619128379026043559173054391123968, 21272840234678433961124648698150649856, 1399262365944914603760602811580314103578624, 21272840229437740829328222440371781632, 325786224886246973603511384670208, 1412304745542024853966082766532509696, 1480908861184725156254684688768850511003904, 87133553580960765385828411162131296157696, 21350724687266314178772774764127715329, 5445847119013229277751681784051338838016, 4294967296, 87113615180038750651158295079777166426112, 92556892093096870327070439201051276017664, 1393796580424979359748162566969903648079872, 1480908860839924193072886521770603937005568, 1329227995784915874128804923637235712, 87133553579692805300885512824276397326336, 5444517870735015420136432259372244008960, 0, 87112369008509983208588326978047008833536, 5445852291027658871133193647493482545152, 5192296858610385492538989435944960, 344800963342358627415960540151808, 1267650604950667959552573440000, 20282428946761085102290193350656, 309485009897906335689736192, 0, 20287361368532331349425411588096, 1267961299181389534318204813312, 1284483683622022786580480]
  slVerts := [[12, 13, 14, 15, 16, 17, 18, 19, 28, 29, 30, 31, 32, 33, 34, 35], [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35], [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], [0, 2, 4, 7, 8, 11, 17, 19, 20, 23, 24, 27, 30, 31, 33, 34], [0, 2, 5, 6, 9, 10, 16, 18, 20, 23, 25, 26, 30, 31, 32, 35], [0, 2, 4, 7, 8, 11, 17, 19, 21, 22, 25, 26, 28, 29, 32, 35], [0, 2, 5, 6, 9, 10, 16, 18, 21, 22, 24, 27, 28, 29, 33, 34], [1, 3, 6, 7, 10, 11, 13, 15, 21, 23, 26, 27, 29, 31, 34, 35], [1, 3, 4, 5, 8, 9, 12, 14, 21, 23, 24, 25, 28, 30, 34, 35], [1, 3, 6, 7, 10, 11, 13, 15, 20, 22, 24, 25, 28, 30, 32, 33], [1, 3, 4, 5, 8, 9, 12, 14, 20, 22, 26, 27, 29, 31, 32, 33], [0, 1, 4, 6, 9, 11, 12, 15, 16, 19, 25, 27, 29, 31, 33, 34], [0, 1, 5, 7, 8, 10, 12, 15, 17, 18, 24, 26, 29, 31, 32, 35], [0, 1, 4, 6, 9, 11, 13, 14, 17, 18, 25, 27, 28, 30, 32, 35], [0, 1, 5, 7, 8, 10, 13, 14, 16, 19, 24, 26, 28, 30, 33, 34], [2, 3, 8, 9, 10, 11, 14, 15, 18, 19, 22, 23, 30, 31, 34, 35], [2, 3, 8, 9, 10, 11, 12, 13, 16, 17, 22, 23, 28, 29, 32, 33], [2, 3, 4, 5, 6, 7, 14, 15, 16, 17, 20, 21, 28, 29, 34, 35], [2, 3, 4, 5, 6, 7, 12, 13, 18, 19, 20, 21, 30, 31, 32, 33], [0, 3, 4, 7, 9, 10, 14, 15, 17, 18, 20, 22, 24, 27, 33, 35], [0, 3, 5, 6, 8, 11, 14, 15, 16, 19, 20, 22, 25, 26, 32, 34], [0, 3, 4, 7, 9, 10, 12, 13, 16, 19, 21, 23, 25, 26, 33, 35], [0, 3, 5, 6, 8, 11, 12, 13, 17, 18, 21, 23, 24, 27, 32, 34], [1, 2, 6, 7, 8, 9, 13, 14, 18, 19, 21, 22, 26, 27, 29, 30], [1, 2, 4, 5, 10, 11, 12, 15, 18, 19, 21, 22, 24, 25, 28, 31], [1, 2, 4, 5, 10, 11, 13, 14, 16, 17, 20, 23, 26, 27, 28, 31], [1, 2, 6, 7, 8, 9, 12, 15, 16, 17, 20, 23, 24, 25, 29, 30]]
  slMask := [68452085760, 68718428160, 268431360, 29152119189, 41986360933, 39567624597, 26732725861, 54435818698, 52942623546, 14282697930, 15775847226, 28622559827, 41423377827, 40165075539, 27196482979, 54774255372, 13703003916, 52348305660, 16110072060, 43106354841, 21581384041, 43061425817, 21636725097, 1819042758, 2473368630, 2626907190, 1670616006]
  slCA := [0, 1, 0, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 0, 3, 2, 1, 1, 1, 2, 2, 0, 1, 2, 3]
}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma orb1_tables_eq : orb1_tables = mkOrb36Tables 1 12 := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma orb2_tables_eq : orb2_tables = mkOrb36Tables 2 13 := by rfl

inductive Tree36 where
  | S (u : Nat) (l r : Tree36)
  | G (tris : List (Nat × Nat × Nat))
  | U (k : Nat)
  | M (items : List (Nat × List (Nat × Nat × Nat)))
  | O (spId : Nat) (us : List Nat)

/-- 144-bit SIMD star lower bound: sums `min(cP[u], cN[u])` over all unassigned `u < 36`. -/
def simdStarLB : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | n + 1, am, cp, cn, acc =>
    let add :=
      if Nat.beq (Nat.land am 1) 0 then
        let a := Nat.land cp 15
        let b := Nat.land cn 15
        if Nat.ble a b then a else b
      else 0
    simdStarLB n (Nat.shiftRight am 1) (Nat.shiftRight cp 4) (Nat.shiftRight cn 4) (Nat.add acc add)

def edgeSgnMask (pAdj nAdj : List Nat) (a b : Nat) : ℤ :=
  let pa := pAdj.getD a 0
  if Nat.beq (Nat.land (Nat.shiftRight pa b) 1) 1 then 1
  else
    let na := nAdj.getD a 0
    if Nat.beq (Nat.land (Nat.shiftRight na b) 1) 1 then -1
    else 0

def checkTris36 (pAdj nAdj : List Nat) (am maskOk : Nat) :
    List (Nat × Nat × Nat) → List (Nat × Nat) → Bool
  | [], _ => true
  | (a, b, c) :: rest, used =>
    let okV :=
      Nat.ble a 35 && Nat.ble b 35 && Nat.ble c 35 &&
      (a < b) && (b < c) &&
      Nat.beq (Nat.land (Nat.shiftRight am a) 1) 0 &&
      Nat.beq (Nat.land (Nat.shiftRight am b) 1) 0 &&
      Nat.beq (Nat.land (Nat.shiftRight am c) 1) 0 &&
      Nat.beq (Nat.land (Nat.shiftRight maskOk a) 1) 1 &&
      Nat.beq (Nat.land (Nat.shiftRight maskOk b) 1) 1 &&
      Nat.beq (Nat.land (Nat.shiftRight maskOk c) 1) 1
    let w1 := edgeSgnMask pAdj nAdj a b
    let w2 := edgeSgnMask pAdj nAdj b c
    let w3 := edgeSgnMask pAdj nAdj a c
    let okW := w1 * w2 * w3 == -1
    let e1 := (a, b); let e2 := (b, c); let e3 := (a, c)
    let okU := !used.contains e1 && !used.contains e2 && !used.contains e3
    okV && okW && okU && checkTris36 pAdj nAdj am maskOk rest (e1 :: e2 :: e3 :: used)

def sliceUBLoop (pAdj nAdj : List Nat) (am nm posK negK unK : Nat) :
    List Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | [], fc2, re2, st => (fc2, re2, st)
  | u :: us, fc2, re2, st =>
    let pm := pAdj.getD u 0
    let nmask := nAdj.getD u 0
    if Nat.beq (Nat.land (Nat.shiftRight am u) 1) 1 then
      let f :=
        if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
        then Nat.add (pop36 (Nat.land pm posK)) (pop36 (Nat.land nmask negK))
        else Nat.add (pop36 (Nat.land pm negK)) (pop36 (Nat.land nmask posK))
      sliceUBLoop pAdj nAdj am nm posK negK unK us (Nat.add fc2 f) re2 st
    else
      let cP := Nat.add (pop36 (Nat.land pm negK)) (pop36 (Nat.land nmask posK))
      let cN := Nat.add (pop36 (Nat.land pm posK)) (pop36 (Nat.land nmask negK))
      let mx := if Nat.ble cP cN then cN else cP
      let r := pop36 (Nat.land (Nat.lor pm nmask) unK)
      sliceUBLoop pAdj nAdj am nm posK negK unK us fc2 (Nat.add re2 r) (Nat.add st mx)

def sliceLBLoop (pAdj nAdj : List Nat) (am nm posK negK : Nat) :
    List Nat → Nat → Nat → Nat × Nat
  | [], fc2, st => (fc2, st)
  | u :: us, fc2, st =>
    let pm := pAdj.getD u 0
    let nmask := nAdj.getD u 0
    if Nat.beq (Nat.land (Nat.shiftRight am u) 1) 1 then
      let f :=
        if Nat.beq (Nat.land (Nat.shiftRight nm u) 1) 1
        then Nat.add (pop36 (Nat.land pm posK)) (pop36 (Nat.land nmask negK))
        else Nat.add (pop36 (Nat.land pm negK)) (pop36 (Nat.land nmask posK))
      sliceLBLoop pAdj nAdj am nm posK negK us (Nat.add fc2 f) st
    else
      let cP := Nat.add (pop36 (Nat.land pm negK)) (pop36 (Nat.land nmask posK))
      let cN := Nat.add (pop36 (Nat.land pm posK)) (pop36 (Nat.land nmask negK))
      let mn := if Nat.ble cP cN then cP else cN
      sliceLBLoop pAdj nAdj am nm posK negK us fc2 (Nat.add st mn)

def checkMItems (tbl : Orb36Tables) (am nm posA negA : Nat) :
    List (Nat × List (Nat × Nat × Nat)) → Nat → Nat → Option Nat
  | [], _, accEx => some accEx
  | (k, tris) :: rest, seenMask, accEx =>
    if Nat.ble k 26 && Nat.beq (Nat.land (Nat.shiftRight seenMask k) 1) 0 then
      let slm := tbl.slMask.getD k 0
      if checkTris36 tbl.pAdj tbl.nAdj am slm tris [] then
        let posK := Nat.land posA slm
        let negK := Nat.land negA slm
        let (fc2, st) := sliceLBLoop tbl.pAdj tbl.nAdj am nm posK negK (tbl.slVerts.getD k []) 0 0
        let lb := Nat.add (Nat.add (tbl.slCA.getD k 0) (Nat.div fc2 2)) (Nat.add st tris.length)
        let ex := Nat.sub lb tbl.f27
        checkMItems tbl am nm posA negA rest (Nat.lor seenMask (Nat.shiftLeft 1 k)) (Nat.add accEx ex)
      else none
    else none

def fullMask36 : Nat := 68719476735

def checkTree36 (tbl : Orb36Tables) : Nat → Nat → Nat → Nat → Nat → Tree36 → Bool
  | am, nm, fc, cpVec, cnVec, Tree36.S u l r =>
    Nat.ble u 35 && Nat.beq (Nat.land (Nat.shiftRight am u) 1) 0 &&
    let bit := Nat.shiftLeft 1 u
    let am' := Nat.lor am bit
    let sh := Nat.mul 4 u
    let pI := tbl.pInc.getD u 0
    let nI := tbl.nInc.getD u 0
    let fcP := Nat.add fc (Nat.land (Nat.shiftRight cpVec sh) 15)
    let fcN := Nat.add fc (Nat.land (Nat.shiftRight cnVec sh) 15)
    checkTree36 tbl am' nm fcP (Nat.add cpVec nI) (Nat.add cnVec pI) l &&
    checkTree36 tbl am' (Nat.lor nm bit) fcN (Nat.add cpVec pI) (Nat.add cnVec nI) r
  | am, _, fc, cpVec, cnVec, Tree36.G tris =>
    let st := simdStarLB 36 am cpVec cnVec 0
    checkTris36 tbl.pAdj tbl.nAdj am fullMask36 tris [] &&
    Nat.ble 93 (Nat.add (Nat.add tbl.f27 fc) (Nat.add st tris.length))
  | am, nm, _, _, _, Tree36.U k =>
    Nat.ble k 26 &&
    let slm := tbl.slMask.getD k 0
    let posA := Nat.land am (Nat.xor am nm)
    let negA := Nat.land am nm
    let posK := Nat.land posA slm
    let negK := Nat.land negA slm
    let unK := Nat.xor slm (Nat.land am slm)
    let (fc2, re2, st) := sliceUBLoop tbl.pAdj tbl.nAdj am nm posK negK unK (tbl.slVerts.getD k []) 0 0 0
    let ub := Nat.add (Nat.add (tbl.slCA.getD k 0) (Nat.div fc2 2)) (Nat.add (Nat.div re2 2) st)
    Nat.ble ub (Nat.sub tbl.f27 1)
  | am, nm, _, _, _, Tree36.M items =>
    let posA := Nat.land am (Nat.xor am nm)
    let negA := Nat.land am nm
    match checkMItems tbl am nm posA negA items 0 0 with
    | none => false
    | some totEx => Nat.ble (Nat.sub 369 (Nat.mul 28 tbl.f27)) totEx
  | am, nm, _, _, _, Tree36.O spId us =>
    Nat.beq am fullMask36 && (spId < 42) && (us.all fun u => u < 64) &&
    let s27 := rep27_vecs.getD tbl.oid []
    let sInitArr : List ℤ := (List.range 64).map fun v =>
      match A27_lit.idxOf? v with
      | some idxA => s27.getD idxA 0
      | none =>
        match B36_lit.idxOf? v with
        | some idxB => if Nat.beq (Nat.land (Nat.shiftRight nm idxB) 1) 1 then -1 else 1
        | none => 0
    let sOutArr : List ℤ := (List.range 64).map fun v => applyWord3Nat us (fun w => sInitArr.getD w 0) v
    let tgt := sp42S64List.getD spId []
    wlines315_lit.all fun (a, b, c, _) =>
      sOutArr.getD a 0 * sOutArr.getD b 0 * sOutArr.getD c 0 == getS64 tgt a * getS64 tgt b * getS64 tgt c

def initPatSimd (tbl : Orb36Tables) (o12 : List Nat) (pat : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Bool × (Nat × Nat × Nat × Nat × Nat)
  | 0, am, nm, fc, cp, cn => (true, (am, nm, fc, cp, cn))
  | rem + 1, am, nm, fc, cp, cn =>
    let i := Nat.sub 11 rem
    let u := o12.getD i 0
    if Nat.ble u 35 && Nat.beq (Nat.land (Nat.shiftRight am u) 1) 0 then
      let bit := Nat.shiftLeft 1 u
      let sh := Nat.mul 4 u
      let pI := tbl.pInc.getD u 0
      let nI := tbl.nInc.getD u 0
      if Nat.beq (Nat.land (Nat.shiftRight pat i) 1) 1 then
        let fc' := Nat.add fc (Nat.land (Nat.shiftRight cn sh) 15)
        initPatSimd tbl o12 pat rem (Nat.lor am bit) (Nat.lor nm bit) fc' (Nat.add cp pI) (Nat.add cn nI)
      else
        let fc' := Nat.add fc (Nat.land (Nat.shiftRight cp sh) 15)
        initPatSimd tbl o12 pat rem (Nat.lor am bit) nm fc' (Nat.add cp nI) (Nat.add cn pI)
    else (false, (0, 0, 0, 0, 0))

def checkPatList (tbl : Orb36Tables) (o12 : List Nat) : List (Nat × Tree36) → Bool
  | [] => true
  | (pat, tree) :: rest =>
    let (ok, (am, nm, fc, cp, cn)) := initPatSimd tbl o12 pat 12 0 0 0 0 0
    ok && checkTree36 tbl am nm fc cp cn tree && checkPatList tbl o12 rest

/-- Compute the induced signed permutation `(p12, s12)` of a stabilizer element `(neg, g, us)` on `o12`
    (verifying it fixes `rep27[oid]` on `A27`, uses only `O⁻(6,2)` transvections, and preserves `o12`). -/
def stabActionO12Build (o12 : List Nat) (neg : Bool) (g : Nat) (revUs : List Nat) :
    Nat → List Nat → Nat → Nat → Option (List Nat × Nat)
  | 0, revP, s12, seen =>
    if seen == 4095 then some (revP.reverse, s12) else none
  | rem + 1, revP, s12, seen =>
    let i := Nat.sub 11 rem
    let bi := o12.getD i 0
    let p0 := B36_lit.getD bi 0
    let (cur, sg) := revUs.foldl (fun (c, s) u => (transv3_pt u c, s * transv3_sgn u c)) (p0, (1 : ℤ))
    match B36_lit.idxOf? cur with
    | none => none
    | some bj =>
      match o12.idxOf? bj with
      | none => none
      | some src =>
        let sgnTot : ℤ := (if neg then -1 else 1) * sg * (if symp3 g p0 == 0 then 1 else -1)
        let s12' := if sgnTot == -1 then Nat.lor s12 (Nat.shiftLeft 1 i) else s12
        stabActionO12Build o12 neg g revUs rem (src :: revP) s12' (Nat.lor seen (Nat.shiftLeft 1 src))

def stabActionO12 (oid : Nat) (o12 : List Nat) (elem : Bool × Nat × List Nat) :
    Option (List Nat × Nat) :=
  let (neg, g, us) := elem
  if !(g < 64 && us.all fun u => u < 64 && Q3_form 9 u == 1) then none
  else
    let s27 := rep27_vecs.getD oid []
    let sAInitArr : List ℤ := (List.range 64).map fun v => match A27_lit.idxOf? v with | some i => s27.getD i 0 | none => 0
    let sAOut := applyGauge3Nat g (applyWord3Nat us (fun v => sAInitArr.getD v 0))
    if !((List.range 27).all fun i => sAOut (A27_lit.getD i 0) == s27.getD i 0) then none
    else stabActionO12Build o12 neg g us.reverse 12 [] 0 0

/-- Exact preimage mask `m < 4096` such that applying `(p12, s12)` to `m` produces `pat`. -/
def preimgO12 (p12 : List Nat) (s12 pat : Nat) : Nat :=
  (List.range 12).foldl (fun m i =>
    let bit := Nat.xor (Nat.land (Nat.shiftRight pat i) 1) (Nat.land (Nat.shiftRight s12 i) 1)
    if Nat.beq bit 1 then Nat.lor m (Nat.shiftLeft 1 (p12.getD i 0)) else m) 0

/-- Verify all `4096` 12-bit patterns on `o12` map via `stab` into `pats`! -/
def checkStabCovers (oid : Nat) (o12 : List Nat) (stab : List (Bool × Nat × List Nat))
    (pats : List Nat) : Bool :=
  (o12.length == 12) &&
  (o12.all fun v => v < 36) &&
  (pop36 (o12.foldl (fun m v => Nat.lor m (Nat.shiftLeft 1 v)) 0) == 12) &&
  let rec collectActs : List (Bool × Nat × List Nat) → List (List Nat × Nat) → Option (List (List Nat × Nat))
    | [], acc => some acc
    | e :: es, acc =>
      match stabActionO12 oid o12 e with
      | none => none
      | some act => collectActs es (act :: acc)
  match collectActs stab [] with
  | none => false
  | some acts =>
    let cov := pats.foldl (fun c pat =>
      acts.foldl (fun c' (p12, s12) => Nat.lor c' (Nat.shiftLeft 1 (preimgO12 p12 s12 pat))) c) 0
    Nat.beq cov (Nat.sub (Nat.shiftLeft 1 4096) 1)

/-- Pure-kernel structural checks for `otherC27_list`, `pop9`, and `M36` degree 15. -/
def checkDPLLCoreTables : Bool :=
  (otherC27_list.length == 27) &&
  (lines27_list.length == 45) &&
  ((List.range 512).all fun x =>
    pop9 x == (List.range 9).foldl (fun acc b => acc + ((x >>> b) &&& 1)) 0) &&
  ((List.range 27).all fun k =>
    let ck := otherC27_list.getD k 0
    ck != 0 && ck != 9 && ck < 64 && Q3_0 ck == 1 &&
    (orb1_tables.slVerts.getD k []).length == 16 &&
    (orb2_tables.slVerts.getD k []).length == 16) &&
  ((List.range 26).all fun k => otherC27_list.getD k 0 < otherC27_list.getD (k + 1) 0) &&
  ((List.range 64).all fun c => if c != 0 && c != 9 && Q3_0 c == 1 then otherC27_list.contains c else true) &&
  -- Degree of every vertex in B36 is 15 (so 4-bit SIMD nibbles 0..15 NEVER overflow!)
  ((List.range 36).all fun u =>
    pop36 (Nat.lor (orb1_tables.pAdj.getD u 0) (orb1_tables.nAdj.getD u 0)) == 15 &&
    Nat.land (orb1_tables.pAdj.getD u 0) (orb1_tables.nAdj.getD u 0) == 0 &&
    pop36 (Nat.lor (orb2_tables.pAdj.getD u 0) (orb2_tables.nAdj.getD u 0)) == 15 &&
    Nat.land (orb2_tables.pAdj.getD u 0) (orb2_tables.nAdj.getD u 0) == 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma checkDPLLCoreTables_ok : checkDPLLCoreTables = true := by rfl

end FourQubitCD

end MultiQubitMUB
