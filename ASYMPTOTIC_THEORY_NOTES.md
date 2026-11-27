# General-$n$ Asymptotic Magic, Pauli Contextuality, and Clifford-PPT Phase Transitions: Theory Notes & Insights (Stages 12–14)

> **Branch:** `explore/asymptotic-theory` (building on verified Lean 4 baseline `73bad0e`, zero edits to upstream `FourQubit*.lean`, `TwoQubitExactCert.lean`, or `main`).  
> **Scope:** Pure general-$n$ theoretical results, exact closed-form Clifford-PPT witness theorems, spectral/Kerdock structural dissections, sharp meta-obstructions, and concrete attack blueprints for the two remaining asymptotic conjectures:
> $$\liminf_{n \to \infty} \min_{|\psi\rangle \in \mathbb{CP}^{2^n-1}} F_n(|\psi\rangle) > 2 \qquad \text{and} \qquad \limsup_{n \to \infty} \max_{\sigma} (1 - 2\rho_n(\sigma))\sqrt{2^n} < 2.$$

---

## 1. Notation & Verified Lean 4 Baseline (`73bad0e`)

Let $n \ge 1$, $d = 2^n$, and let $P_p = i^{a\cdot b} Z^b X^a$ ($p = (a,b) \in \mathbb{F}_2^{2n}$) be the Hermitian involutive $n$-qubit Pauli operators with symplectic form $\omega((a,b),(c,d)) = a\cdot d + b\cdot c \in \mathbb{F}_2$ and multiplication cocycle $P_p P_q = \gamma(p,q) P_{p\oplus q}$ ($\gamma(p,q) \in \{\pm 1\}$ when $\omega(p,q) = 0$). For a unit state $|\psi\rangle \in (\mathbb{C}^2)^{\otimes n}$ with Pauli expectations $c_p(\psi) := \langle\psi|P_p|\psi\rangle \in [-1, 1]$ and any sign assignment $\sigma : \mathbb{F}_2^{2n} \setminus \{0\} \to \{\pm 1\}$:
- **Pauli 4th moment & order-2 Stabilizer Rényi Entropy:**
  $$F_n(|\psi\rangle) := \sum_{p \in \mathbb{F}_2^{2n}} c_p(\psi)^4 = 1 + \sum_{p \neq 0} c_p(\psi)^4, \qquad M_2(|\psi\rangle) = -\ln\frac{F_n(|\psi\rangle)}{d}.$$
  The Welch (SIC) lower bound is $\mathrm{Welch}_n = \frac{2d}{d+1} = 2 - \frac{2}{d+1}$; the hypothetical MUB fiducial benchmark is $\mathrm{MUB}_n = 2 - \frac{1}{d}$; the Haar expectation is $1 + \frac{3(d-1)}{d+3} \to 4$.
- **Pauli $L_1$ flatness ratio:**
  $$\alpha_n(\psi) := \frac{\sum_{p \neq 0} |c_p(\psi)|}{\sqrt{d(d^2 - 1)}} \in (0, 1].$$
- **Symplectic sign operator & contextuality scaling constant:**
  $$S(\sigma) := \sum_{p \neq 0} \sigma_p P_p, \qquad \mathrm{Tr}(S) = 0, \qquad \mathrm{Tr}(S^2) = T_2 := d(d^2 - 1),$$
  $$\mathrm{Tr}(S^3) = d\,(1 - 2\rho_n(\sigma))(d^2 - 1)\left(\frac{d^2}{2} - 2\right), \qquad c_n(\sigma) := \bigl(1 - 2\rho_n(\sigma)\bigr)\sqrt{d},$$
  where $\rho_n(\sigma) \in [0, 1]$ is the fraction of frustrated commuting (isotropic) lines $\{p, q, p\oplus q\}$ ($\omega(p, q) = 0$) in $W(2n-1, 2)$.

### Already Machine-Verified in Lean 4 ([`MultiQubitMUB/AsymptoticContextuality.lean`](MultiQubitMUB/AsymptoticContextuality.lean))
Zero `sorry`, zero `native_decide`, 53/53 audited theorems in [`Audit.lean`](Audit.lean) depending solely on `[propext, Classical.choice, Quot.sound]`:
1. **Exact Asymptotic Contextuality Law $1 - 2\rho_n = \Theta(2^{-n/2})$:**
   - Upper bound ($\forall n \ge 2$ on $W(2n-1, 2)$ and $\forall n \ge 3$ on every elliptic quadric $\mathcal{Q}^-(2n-1, 2)$):
     $$1 - 2\rho_n(\sigma) \le \frac{2\sqrt{d+1}}{d+2} < 2 \cdot 2^{-n/2}, \qquad \lim_{n \to \infty} \rho_n = \frac{1}{2}.$$
   - Lower bound ($\forall n \ge 4$, finite $\mathbb{Z}_4$-phase averaging with zero measure theory):
     $$\frac{1}{4^d}\sum_{f : \mathbb{F}_2^n \to \mathbb{Z}_4} \bigl|\langle \psi_f | P_{a,b} | \psi_f \rangle\bigr| = \frac{1}{2^d}\binom{d}{d/2} \implies \exists\,\sigma,\; 1 - 2\rho_n(\sigma) \ge \frac{1}{7}\cdot 2^{-n/2}.$$
2. **One-Way $c = 2$ Barrier Equivalence (Matrix-Free):**
   Any Hermitian $S$ and unit $|\psi\rangle$ with $\mu = \langle\psi|S|\psi\rangle \ge 0$ and $\mathrm{Tr}(S^2) \le 2\mu^2$ satisfy $\mu^3 - (\mathrm{Tr}(S^2) - \mu^2)^{3/2} \le \mathrm{Tr}(S^3)$. Consequently, any uniform $c < 2$ forces $\liminf \min F_n \ge 1 + x^{-2} > 2$ where $x^3 - (1-x^2)^{3/2} = c/2$.
3. **Exact All-$n$ `spike` Frustration Formula & Asymptotic Suboptimality:**
   $$1 - 2\rho_n(\mathrm{spike}_n) = \frac{9(d - 2)}{(d + 1)(d + 2)} = \Theta(2^{-n}),$$
   strictly suboptimal for all $n \ge 12$ (and already at $n = 5$ via the rank-3 minimizer `31479` on $W(9,2)$ / `7087` on $\mathcal{Q}^-(9,2)$).

---

## 2. Crystallized General-$n$ Pure-Theory Results & Meta-Obstructions (Ready for Formalization)

### 2.1 Three-Line Elementary Classification of Multi-Qubit Pauli-SICs & All-$n \ge 4$ Strict Welch Separation

**Theorem 2.1 (Strict Welch Separation for All $n \neq 1, 3$).**  
For every integer $n \ge 1$ with $n \neq 1, 3$ ($d = 2^n$), there is no $n$-qubit Pauli-covariant SIC fiducial state; equivalently,
$$\forall\,|\psi\rangle \in \mathbb{CP}^{d-1},\quad F_n(|\psi\rangle) > \frac{2d}{d+1}, \qquad\text{and}\qquad \forall\,\sigma,\quad 1 - 2\rho_n(\sigma) < \frac{2\sqrt{d+1}}{d+2}.$$

*Proof (3 lines, zero Galois theory).*  
Suppose $F_n(|\psi\rangle) = \frac{2d}{d+1}$. By Cauchy–Schwarz on $\sum_{p \neq 0} c_p^2 = d - 1$, equality forces $c_p(\psi)^2 = \frac{1}{d+1}$ for every $p \neq 0$. Setting $\sigma_p := \operatorname{sgn}(c_p(\psi)) \in \{\pm 1\}$, we have $c_p(\psi) = \frac{\sigma_p}{\sqrt{d+1}}$ and hence
$$S(\sigma) = \sum_{p \neq 0} \sigma_p P_p = \sqrt{d+1}\bigl(d\,|\psi\rangle\langle\psi| - I\bigr).$$
The eigenvalues of $S(\sigma)$ are $(d-1)\sqrt{d+1}$ (multiplicity $1$) and $-\sqrt{d+1}$ (multiplicity $d-1$), so
$$\mathrm{Tr}\bigl(S(\sigma)^3\bigr) = (d+1)^{3/2}\bigl((d-1)^3 - (d-1)\bigr) = d(d-1)(d-2)(d+1)\sqrt{d+1}.$$
On the other hand, expanding $S(\sigma)^3$ in the Pauli basis gives
$$\mathrm{Tr}\bigl(S(\sigma)^3\bigr) = d \sum_{\substack{p,q \neq 0,\, p \neq q \\ \omega(p,q)=0}} \gamma(p,q)\sigma_p\sigma_q\sigma_{p\oplus q} \in \mathbb{Z}.$$
Whenever $n \ge 2$ we have $d - 2 > 0$, forcing $\sqrt{2^n + 1} \in \mathbb{Q}$, i.e. $2^n + 1 = k^2 \iff 2^n = (k-1)(k+1)$ for an integer $k \ge 1$. Since $\gcd(k-1, k+1) \mid 2$, the only positive powers of $2$ differing by $2$ are $2$ and $4$, giving $k = 3$ and uniquely $n = 3$ (the Hoggar SIC). For $n = 1$ ($d = 2$), the factor $d - 2 = 0$ vanishes identically (the single-qubit tetrahedron SIC exists). For strict contextuality equality, saturation of $\mathrm{Tr}(r_t^3) = 1$ for $r_t = \frac{1}{d}I + \frac{1}{d\sqrt{d+1}} S(\sigma)$ forces $r_t$ to be rank-1, yielding the exact same $S(\sigma) = \sqrt{d+1}(d|\psi\rangle\langle\psi| - I)$ and contradiction. $\square$

*(Remark: This elementary cubic-trace integrality proof recovers the complete Godsil–Roy / Zhu classification of multi-qubit Weyl–Heisenberg SICs without requiring algebraic number theory or Galois conjugates, and directly upgrades our existing spectral bound to a strict inequality for all $n \neq 1, 3$.)*

---

### 2.2 Complete Double Equivalence & the Subtle Sparse-Spike Gap

**Theorem 2.2 (Exact Asymptotic Equivalence).**  
Let $F_n^* := \min_{|\psi\rangle} F_n(|\psi\rangle)$, $\alpha_n^* := \max_{|\psi\rangle} \alpha_n(\psi)$, and $c_n^* := \max_{\sigma} c_n(\sigma)$. Then:
$$\liminf_{n \to \infty} F_n^* = 2 \;\Longrightarrow\; \limsup_{n \to \infty} \alpha_n^* = 1 \;\Longleftrightarrow\; \limsup_{n \to \infty} c_n^* = 2.$$

*Proof sketch.*
1. **$(\alpha_n^* \to 1 \Rightarrow c_n^* \to 2)$:** Already formalized in `signCubeSum_ge_of_L1`: $c_n(\sigma_\psi) \ge 2\bigl(\alpha_n^3 - (1-\alpha_n^2)^{3/2}\bigr) \to 2$.
2. **$(c_n^* \to 2 \Rightarrow \alpha_n^* \to 1)$:** For $r_t = \frac{1}{d}I + \frac{1}{d\sqrt{d+1}}S(\sigma)$ ($\mathrm{Tr}(r_t) = 1$, $\mathrm{Tr}(r_t^2) = 1$), having $c_n(\sigma) = 2 - \varepsilon$ forces $\mathrm{Tr}(r_t^3) \ge 1 - O(\varepsilon)$. Letting $\lambda_1$ be the top eigenvalue of $r_t$ with eigenvector $|\psi_1\rangle$, $\lambda_1 \ge \mathrm{Tr}(r_t^3) / \mathrm{Tr}(r_t^2) = 1 - O(\varepsilon)$, so
   $$\bigl\|r_t - |\psi_1\rangle\langle\psi_1|\bigr\|_F^2 = 2(1 - \lambda_1) = O(\varepsilon).$$
   Expanding in the Pauli basis gives $\frac{1}{d}\sum_{p \neq 0}\bigl(\frac{\sigma_p}{\sqrt{d+1}} - c_p(\psi_1)\bigr)^2 = O(\varepsilon)$, hence $\frac{1}{d}\sum_{p \neq 0}\sigma_p c_p(\psi_1) = (1 - O(\varepsilon))\frac{d-1}{\sqrt{d+1}}$ and $\alpha_n(\psi_1) \ge 1 - O(\varepsilon)$.
3. **$(F_n^* \to 2 \Rightarrow \alpha_n^* \to 1)$:** Set $a = \frac{1}{\sqrt{d+1}}$. Since $(|c_p| - a)^2 \le (c_p^2 - a^2)^2 / a^2$ and $\sum_{p \neq 0}(c_p^2 - a^2)^2 = F_n(\psi) - \frac{2d}{d+1}$,
   $$\frac{1}{d-1}\sum_{p \neq 0}\left(|c_p(\psi)| - \frac{1}{\sqrt{d+1}}\right)^2 \le \frac{d+1}{d-1}\bigl(F_n(\psi) - \mathrm{Welch}_n\bigr) \to 0 \implies \alpha_n(\psi) \to 1. \quad \square$$

> **Strategic Insight (The Sparse-Spike Gap):** The reverse implication $\alpha_n^* \to 1 \not\Rightarrow F_n^* \to 2$ fails in general! Frobenius proximity $\|r_t - |\psi_1\rangle\langle\psi_1|\|_F^2 = o(1)$ only controls the $L_2$ perturbation $\sum_{p\neq 0} e_p^2 = o(d)$ (where $c_p = \sigma_p/\sqrt{d+1} + e_p$), which does **not** prevent a sparse subset of $O(d)$ Paulis of amplitude $\Omega(d^{-1/4})$ from contributing $\Omega(1)$ to $F_n = 1 + \sum c_p^4$. Empirically, our $n = 9$ ($3+6$) Kerdock state exhibits exactly this phenomenon: $\alpha_9 = 0.9267$ stays close to $1$, while $378$ sparse intra-block Paulis of size $1/6$ drive $F_9$ up to $4.159$. Thus **proving $\liminf F_n^* > 2$ directly is strictly weaker (and potentially strictly easier) than proving $\limsup c_n^* < 2$** (where $c_7 = 1.7967$ already leaves only a $0.20$ margin below $2$).

---

### 2.3 Sharp Meta-Obstruction: Any Pure-$c_p^2$ (Sign-Blind / Bell-Difference-Sampling) LP Cannot Beat Welch

For any pure state $|\psi\rangle$, the Bell-difference-sampling probability distribution $q(p) := c_p(\psi)^2 / d$ on $\mathbb{F}_2^{2n}$ satisfies:
$$q(p) \ge 0, \qquad \sum_{p} q(p) = 1, \qquad q(0) = \frac{1}{d}, \qquad \widehat{q}(r) := \sum_p (-1)^{\omega(r, p)} q(p) = d \cdot q(r).$$
Because $q$ is an exact eigenfunction of the symplectic Walsh–Hadamard transform, every entrywise power $q^k$ also has non-negative symplectic transform $\widehat{q^k} = d\,(q^{*k}) \ge 0$, and $F_n(\psi) = d^2 \|q\|_2^2$.

**Proposition 2.3 (Pure-$c_p^2$ LP Barrier).**  
The flat hypothetical SIC distribution $q_{\mathrm{SIC}}(0) = \frac{1}{d}$, $q_{\mathrm{SIC}}(p \neq 0) = \frac{1}{d(d+1)}$ satisfies $q_{\mathrm{SIC}} \ge 0$, $\sum q_{\mathrm{SIC}} = 1$, $\widehat{q_{\mathrm{SIC}}} = d\cdot q_{\mathrm{SIC}}$, and $\widehat{q_{\mathrm{SIC}}^k} \ge 0$ for every integer $k \ge 1$, while attaining $d^2 \|q_{\mathrm{SIC}}\|_2^2 = \frac{2d}{d+1} = \mathrm{Welch}_n$.

*Consequence:* No sign-blind / Delsarte / Bell-sampling linear program depending solely on $\{c_p^2\}$ can beat the Welch bound for any $n$. Every general-$n$ proof beating Welch **must** exploit the signed Pauli vector $c_p \in [-1, 1]$ and genuine rank-1 quantum coherence $\rho = \frac{1}{d}\sum c_p P_p \succeq 0$, $\rho^2 = \rho$.

---

### 2.4 Gaussian-Integer Congruence & the $I_2 \to 2$ Obstruction to Naive `Alltop` Stability

1. **Exact Gaussian-Integer Parity Congruence ($\forall n \ge 2, \forall \sigma$):**
   Every diagonal entry $S(\sigma)_{x,x} = \sum_{b\neq 0} \sigma_{0,b}(-1)^{b\cdot x}$ is an **odd integer**, while every off-diagonal entry $S(\sigma)_{x\oplus a, x} = \sum_b \sigma_{a,b} i^{a\cdot b} (-1)^{b\cdot x}$ ($a \neq 0$) has **even real part** (sum of $d/2$ terms $\pm 1$) and **even imaginary part** (sum of $d/2$ terms $\pm 1$). Hence
   $$\frac{S(\sigma) + I}{2} \in M_d(\mathbb{Z}[i])$$
   is an exact Hermitian Gaussian-integer matrix.
2. **Why Flat-Amplitude `Alltop.lean` Stability Does Not Directly Rule Out $c_n \to 2$:**
   For any unit state $|\psi\rangle$ and any stabilizer basis (Lagrangian subspace $L \subset \mathbb{F}_2^{2n}$) with Born distribution $p_L(x) = |\langle e_{L,x}|\psi\rangle|^2$ and inverse participation ratio $I_2(L; \psi) := d\sum_x p_L(x)^2 = \sum_{p \in L} c_p(\psi)^2$:
   - The off-diagonal kurtosis of the ideal rank-1 sign matrix $S_{\mathrm{ideal}} = \sqrt{d+1}(d|\psi\rangle\langle\psi| - I)$ is $\kappa_{\mathrm{off}}(S_{\mathrm{ideal}}) \approx I_2(L; \psi)^2$.
   - `Alltop.lean` (phase states) lives on the hyperplane **$I_2 = 1$** ($p_L(x) = 1/d$, forcing $c_p = 0$ on $L\setminus\{0\}$ and $F_n \ge 2 - 1/d$).
   - By contrast, a Welch-saturating / $c_n \to 2$ state ($c_p^2 \approx \frac{1}{d+1}$ for all $p \neq 0$) satisfies in **every** stabilizer basis $L$:
     $$I_2(L; \psi) = 1 + \frac{d-1}{d+1} = \frac{2d}{d+1} \xrightarrow{n \to \infty} 2 \implies \kappa_{\mathrm{off}}(S_{\mathrm{ideal}}) \to 4.$$
   - Writing $Y_L(x) := d\,p_L(x) = 1 + \frac{m_{L,x}}{\sqrt{d+1}} + \text{err} \ge 0$ (where $m_{L,x} = \sum_{p \in L\setminus\{0\}} \sigma_p (-1)^{\langle p, x\rangle}$ is the odd-integer Walsh–Hadamard transform of $\sigma|_{L\setminus\{0\}}$), the $c_n \to 2$ limit requires $Y_L \ge 0$ with Porter–Thomas-like moments $(\mathbb{E}[Y_L], \mathbb{E}[Y_L^2], \mathbb{E}[Y_L^3], \mathbb{E}[Y_L^4]) \to (1, 2, 6, \ge 18)$ rather than flat $(1, 1, 1, 1)$.

---

## 3. Hard Battle A: Exact Symbolic Solution of the GNW $t = 8$ PPT Phase Transition & the $R_{4m}$-Ideal Mechanism

In Stage 12–13, solving the full dimension-independent GNW $t = 8$ Clifford commutant PPT SDP (`Sym^8 ⪰ 0`, $\tau_1..\tau_4 \succeq 0$, closed commutant dimensions $13, 49, 149, 275, 381$) broke Welch at $n = 2, 4, 5, 6$ and broke MUB + $2.0$ at $n = 4$ with zero DPLL:

| $d$ ($n$) | Welch | MUB | $\tau_2$ only | $\tau_3$ only | $\tau_4$ only | **Full $\tau_{1..4}$ SDP** | Status |
|---:|---:|---:|---:|---:|---:|---:|---|
| 4 ($n=2$) | 1.600000 | 1.750000 | 1.746322 | **1.750000** | **1.750000** | **1.750000** | Exact $7/4$ (7 cuts) |
| 8 ($n=3$) | 1.777778 | 1.875000 | 1.777778 | 1.777778 | 1.777778 | **1.777778** | Hoggar SIC tight |
| **16 ($n=4$)** | 1.882353 | 1.937500 | 1.912823 | **1.966301** | **2.015367** | **2.019754** | **Beats MUB & $2.0$ (12 cuts!)** |
| **32 ($n=5$)** | 1.939394 | 1.968750 | 1.957228 | 1.939394 | **1.961807** | **1.961948** | Beats Welch (76.8% to MUB) |
| **64 ($n=6$)** | 1.969231 | 1.984375 | 1.969231 | 1.969231 | **1.976110** | **1.976110** | Beats Welch (45.4% to MUB) |
| $\ge 128$ ($n\ge 7$) | Welch | MUB | Welch | Welch | Welch | **Welch** | All 5 cones PSD on $y_H(d)$ |

### 3.1 Stage 14 Breakthrough: Exact Continuous Roots $d_0$ (Refuting the Dyadic $2^5, 2^6, 2^7$ Guess)

Sweeping continuous $d$ on the analytic Hoggar curve $y_H(d)$ (parametrized in the 13 `Sym^8` orbits `orb8[0..12]` below) and interpolating the single negative eigenvector witness revealed that the true phase-transition roots are **not** pure powers of $2$:

| $t$ | Cone | Dim | Min-Eig Multiplicity $m$ | **Exact Root $d_0$ on $y_H(d)$** | **$R_8$-Ideal Support** |
|---:|---|---:|---:|---|---|
| $t = 6$ | $\tau_2, \tau_3$ | 21, 25 | $m = 1, 2$ | **$d_0 = 8$** (exact integer) | — (no $R_6$) |
| $t = 8$ | $\tau_3$ ($5:3$) | 275 | $m = 5$ | **$d_0 \approx 27.930150$** (non-dyadic, $< 32$!) | `0 / 225` (parity-forbidden!) |
| $t = 8$ | $\tau_2$ ($6:2$) | 149 | **$m = 1$ (unique!)** | **$d_0 = 64$** (**exact integer!**) | **`14 / 14`** (100% inside $R_8$-ideal!) |
| $t = 8$ | $\tau_4$ ($4:4$) | 381 | **$m = 1$ (unique!)** | **$d_0 = 52 + 2\sqrt{574} \approx 99.916594$** (**quadratic irrational, $< 128$!**) | **`34 / 34`** (100% inside $R_8$-ideal!) |

### 3.2 Exact Closed-Form 13-Term Polynomial Witnesses for $\tau_2$ and $\tau_4$

In the 13-dimensional commutative algebra $\mathrm{End}_{\mathrm{Cl}_n}(\mathrm{Sym}^8(\mathbb{C}^d))$ (`orb8[0..12]` as indexed in `stage14_probe1_gnw8_witness.c`), the analytic Hoggar curve $y_H(d)$ is:
$$y_0 = 1,\quad y_1 = \frac{2}{d+1},\quad y_2 = \frac{1}{d}\left(1 + \frac{d^2-1}{(d+1)^4}\right),\quad y_3 = y_4 = y_5 = y_7 = y_9 = \frac{4}{(d+1)^2},$$
$$y_6 = y_{10} = \frac{8}{(d+1)^3},\quad y_8 = \frac{d+3}{(d+1)^2},\quad y_{11} = \frac{2(d+3)}{(d+1)^3},\quad y_{12} = \frac{3d+5}{(d+1)^3}.$$
*(Here $y_0 = 1$, $y_1 = F_4/d$ is the weight-4 code `0xF0`, $y_2 = \mathrm{Tr}(R_8 \rho^{\otimes 8}) = \frac{1}{d}\sum_p c_p^8$ is the weight-8 repetition code `0xFF`, $y_7$ is the $[8,4,4]$ extended Hamming code $e_8$, and $y_8$ is the sign-sensitive weight-6 anti-stochastic operator $T_{\text{anti6}}$.)*

Every quantum state $\rho$ (indeed every PPT state on $(\mathbb{C}^d)^{\otimes 8}$) satisfies $\sum_{a=0}^{12} \alpha_a(d)\,y_a(\rho) \ge 0$ for both exact single-vector witnesses below (verified identically in $\mathbb{Q}(d)$ and against 16-digit eigensolver outputs at $d = 16, 32, 48, 64, 80, 96$):

1. **Exact $\tau_2$ Single-Vector Witness ($d_0 = 64$):**
   $$\alpha^{(\tau_2)}_0 = \alpha^{(\tau_2)}_5 = \alpha^{(\tau_2)}_7 = 0, \qquad \alpha^{(\tau_2)}_2 = \frac{1}{20}, \qquad \alpha^{(\tau_2)}_{12} = 1,$$
   $$\alpha^{(\tau_2)}_1 = \alpha^{(\tau_2)}_4 = \frac{72}{(d+8)(d+16)}, \quad \alpha^{(\tau_2)}_6 = \frac{6}{(d+8)(d+16)}, \quad \alpha^{(\tau_2)}_{10} = -\frac{9d + 48}{2(d+8)(d+16)},$$
   $$\alpha^{(\tau_2)}_3 = -\frac{3}{2(d+16)}, \quad \alpha^{(\tau_2)}_8 = -\frac{48}{5(d+16)}, \quad \alpha^{(\tau_2)}_9 = -\frac{24}{d+16}, \quad \alpha^{(\tau_2)}_{11} = \frac{3(d+4)}{4(d+16)}.$$
   - **Exact evaluation on $y_H(d)$:**
     $$\sum_{a=0}^{12} \alpha^{(\tau_2)}_a(d)\,y_H(d)_a = \frac{(d - 2)(d - 1)(d - 8)(d - 64)}{20\,(d + 1)^3(d + 8)(d + 16)} < 0 \iff d \in (8, 64).$$
   - **Exact evaluation on every stabilizer state ($y_a = 1$):**
     $$\sum_{a=0}^{12} \alpha^{(\tau_2)}_a(d) = \frac{36\,(d - 1)(d - 2)}{20\,(d + 8)(d + 16)} = \frac{9\,(d - 1)(d - 2)}{5\,(d + 8)(d + 16)} \ge 0.$$

2. **Exact $\tau_4$ Single-Vector Witness ($d_0 = 52 + 2\sqrt{574} \approx 99.916594$):**  
   Setting $D(d) := (d + 4)(d^2 + 24d + 512)$ and normalizing by $\alpha^{(\tau_4)}_2 = 1$, the 13 exact numerators $P_a(d) = D(d)\,\alpha^{(\tau_4)}_a(d)$ are:
   $$\begin{aligned}
   P_0 &= -10752, & P_1 &= 6912 d + 22272, & P_2 &= D(d) = d^3 + 28 d^2 + 608 d + 2048, \\
   P_3 &= -73 d^2 - 876 d - 3008, & P_4 &= -256 d^2 - 1344 d - 1280, & P_5 &= -32(d+4)(d+8), \\
   P_6 &= d^3 + 28 d^2 + 332 d + 944, & P_7 &= -(d+4)(d+8), & P_8 &= -256(d+4)(d-10), \\
   P_9 &= -1184(d+4)(d+8), & P_{10} &= 16 d^3 + 376 d^2 + 2720 d + 5888, & P_{11} &= 36(d+4)(d^2+16d+80), \\
   P_{12} &= 16 d^3 + 160 d^2 + 512 d + 512.
   \end{aligned}$$
   - **Exact evaluation on $y_H(d)$:**
     $$\sum_{a=0}^{12} \alpha^{(\tau_4)}_a(d)\,y_H(d)_a = \frac{(d - 1)(d - 8)(d + 8)\,(d^2 - 104 d + 408)}{(d + 1)^3(d + 4)(d^2 + 24 d + 512)} < 0 \iff d \in (8,\; 52 + 2\sqrt{574}).$$
   - **Exact evaluation on every stabilizer state ($y_a = 1$):**
     $$\sum_{a=0}^{12} \alpha^{(\tau_4)}_a(d) = \frac{70\,(d - 1)(d - 2)(d - 4)}{(d + 4)(d^2 + 24 d + 512)} \ge 0 \qquad (\forall\, d = 2^n \ge 1).$$

### 3.3 The General-$t = 4m$ Algebraic Mechanism: $R_{4m}$-Ideal Binomial Projection

Dissecting the negative eigenvector $Q$ of $\tau_2$ and $\tau_4$ reveals **why** the witness is 1-dimensional ($m=1$) and **how** it generalizes directly to every $t = 4m$:
1. Define the Pauli-invariant `[t, 1]` repetition-code operator $R_t := \frac{1}{d}\sum_{p \in \mathbb{F}_2^{2n}} P_p^{\otimes t}$ ($t \equiv 0 \pmod 4$).
2. Under an **even** partial-transpose cut $k = 2r$ ($\tau_2, \tau_4$), $(1^8, 0)$ and $(0, 1^8)$ remain compatible with doubly-even parity, generating a tiny closed two-sided ideal $R_8 \cdot \mathrm{Alg}_k \cdot R_8$ of dimension **14** (out of 149) for $\tau_2$ and **34** (out of 381) for $\tau_4$. Under an **odd** cut ($\tau_3$, $5:3$), $(1^5 0^3, 0^5 1^3)$ has odd weights and the $R_8$-ideal has dimension **0**, forcing $\tau_3$ into a 5-dimensional weight-6 anti-stochastic subspace that dies early at $d_0 \approx 27.93$.
3. Inside $R_8 \cdot \mathrm{Alg}_k \cdot R_8$, the negative eigenvector $Q$ has **exact zero Hilbert–Schmidt overlap** with every basis subspace having $\dim(L) \ge 2$ (`11` elements in $\tau_2$, `29` elements in $\tau_4$), and its coefficients on the remaining $\dim(L) = 1$ double-coset orbits of $R_8$ are **exact combinatorial orbit sizes**:
   - $\tau_2$: 3 orbits with weights `1 : 15 : 20` (summing to `36`, matching the numerator coefficient $36$ of the stabilizer evaluation!).
   - $\tau_4$: 5 orbits with weights $1 : 16 : 36 : 16 : 1 = \binom{4}{j}^2$ ($j = 0, \dots, 4$, summing to $\binom{8}{4} = 70$, matching the numerator coefficient $70$ of the stabilizer evaluation!).
4. Thus, for arbitrary $t = 4m$ ($t = 8, 12, 16, \dots$), we obtain an **explicit single-operator candidate family** requiring zero full-commutant construction:
   $$Q_{4m} := \Pi_{\perp(\dim(L) \ge 2)}\!\Big(\tau_{2m}\big(P_{\mathrm{Sym}^{4m}} R_{4m} P_{\mathrm{Sym}^{4m}}\big)\Big).$$
   Its crossover $d_0(4m)$ comes from balancing the $+\frac{1}{d}$ identity term in $y_2 = \mathrm{Tr}(R_{4m} y_H)$ against the $-\frac{c_1(4m)}{d^2}$ anti-stochastic sign-sensitive contribution ($d_0(4) = 2 \to d_0(6) = 8 \to d_0(8) \approx 99.92$).

> **Honest Limitation:** While $Q_{4m}$ is a striking general-$t$ Clifford representation-theory theorem and may yield super-exponentially growing $d_0(4m)$ on $y_H(d)$, falsifying $y_H(2^n)$ alone is already proved in 3 lines by Theorem 2.1. Converting $Q_{4m}$ into a constant gap $\liminf F_n^* > 2$ remains blocked by the $O(d^{-2})$ margin and the need to eliminate higher moments ($y_2, y_8, \dots$) via `Sym^{4m} ⪰ 0`.

---

## 4. Hard Battle B: Full Spectral Quantization of $S(\sigma_n^*)$ ($n = 3..8$) & Exact Kerdock Dissection of $n = 8$ `seed 0`

### 4.1 Complete Eigenvalue Spectra of $S(\sigma_n^*)$ ($n = 3..8$)

Evaluating the exact Hermitian spectrum of $S(\sigma) = \sum_{p \neq 0} \sigma_p P_p$ via its $2d \times 2d$ real doubling (verified `bad_parity = 0`, `Tr(S^2)/T2 = 1.000000000000`) settles the bulk-quantization question decisively:

| State | $n$ | $d$ | $-\sqrt{d+1}$ | $F_n$ | $\alpha_n$ | $c_n$ | $\lambda_1(r_t)$ | $\mathrm{Tr}(S^4)/T_2^2$ | $\kappa_{\mathrm{off}}(S)$ / $\kappa_{\mathrm{off}}(S_{\mathrm{ideal}})$ | Clustered Bulk Eigenvalue Spectrum of $S(\sigma)$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| Hoggar SIC | 3 | 8 | `-3.000` | `1.7778` | `0.9354` | `1.6971` | `1.0000` | `0.7679` | `1.750 / 1.750` | `+21 (×1)`, **`-3 (×7)`** |
| spike | 4 | 16 | `-4.123` | `2.1505` | `0.9407` | `1.6471` | `0.9749` | `0.7952` | `5.900 / 5.283` | `+60.19 (×1)`, **`-3 (×14)`**, `-18.19 (×1)` |
| min-$F_5$ | 5 | 32 | `-5.745` | `2.5490` | `0.9293` | `1.5611` | `0.9501` | `0.7704` | `3.517 / 4.228` | `+168.90 (×1)`, **`-3 (×29)`**, `-23.73`, `-58.17` |
| min-$F_6$ | 6 | 64 | `-8.062` | `2.7237` | `0.8987` | `1.4717` | `0.9215` | `0.7031` | `3.863 / 4.216` | `+467.43 (×1)`, **`-3 (×36)`**, **`-11 (×6)`**, `+5 (×6)`, `-27 (×3)` + 11 others |
| **Kerdock $n=7$** | **7** | **128** | **`-11.358`** | **`2.3723`** | **`0.9662`** | **`1.7967`** | **`0.9711`** | **`0.8755`** | **`3.526 / 3.728`** | `+1400.45 (×1)`, **`-7 (×60)`**, **`-3 (×48)`**, `+45 (×3)`, `+13 (×4)`, `-51 (×6)`, `-83 (×1)`, `-135 (×3)`, `-9.51`, `-219.94` |
| **$n=8$ `seed 0`** | **8** | **256** | **`-16.031`** | **`2.7917`** | **`0.9092`** | **`1.6173`** | **`0.9386`** | **`0.7721`** | **`3.532 / 4.039`** | `+3836.11 (×1)`, **`-3 (×96)`**, **`-11 (×15)`**, **`-15 (×66)`**, + 31 pos / 33 neg outliers (`-920.38` min) |
| $n=8$ `seed 1` | 8 | 256 | `-16.031` | `3.1459` | `0.8402` | `1.1835` | `0.8433` | `0.5010` | `3.198 / 4.339` | `+3444.84 (×1)`, **0 integer eigenvalues** (continuous semicircle `[-284.7, +249.3]`) |

**Key Spectral Takeaways:**
1. **Bulk eigenvalues DO track $-\sqrt{d+1}$ in $\equiv 1 \pmod 4$ integer steps (`-3 -> -7 -> -15`, plus `-11`):** At $n=7$, `125/128` eigenvalues are exact integers $\equiv 1 \pmod 4$ (so $(S+I)/2$ has odd integer eigenvalues), and the remaining 3 irrational eigenvalues sum to the exact integer `1171`. At $n=8$ `seed 0`, `177/256` eigenvalues are exact $\equiv 1 \pmod 4$ integers with a large cluster at **`-15 (×66)`** right beside $-\sqrt{257} \approx -16.03$. Hence **bulk eigenvalue quantization at `-3` does NOT obstruct $c_n \to 2$**.
2. **Row-WHT kurtosis confirms the $I_2 \to 2$ regime:** Both $n=7$ and $n=8$ `seed 0` have $\kappa_{\mathrm{off}}(S(\sigma)) \approx 3.53$ closely matching $\kappa_{\mathrm{off}}(S_{\mathrm{ideal}}) \approx 3.73\text{–}4.04 \approx I_2^2$, confirming Section 2.4.

### 4.2 Exact Canonical Dissection of $n = 8$ `seed 0` ($F_8 = 2.79173$, $c_8 = 1.6173$)

Diagonalizing the maximal isotropic subspace of top Paulis (`k = 4`, splitting $8 = 4 + 4$ into 16 four-qubit blocks) completely identifies $n = 8$ `seed 0`:
- Out of 16 blocks, 9 main blocks are active (plus one residual `y=5`, $q_5 = 0.00315$):
  - **8 exact 4-qubit stabilizer states** (`F_4 = 16.000`, weights $q \approx 0.090$ on 6 blocks and $q \approx 0.149$ on 2 blocks) with **every pairwise overlap $|\langle\phi_y|\phi_z\rangle| = 0.250 = 1/\sqrt{16}$**;
  - After rotating `y=1` to $|0000\rangle$, all 7 quadratic stabilizer blocks share the **exact same diagonal `(1, 1, 0, 0)`** (`diag_ang` $= [\pm 90^\circ, \pm 90^\circ, 0/180^\circ, 0/180^\circ]$), i.e., **all pairwise differences are invertible alternating binary matrices = a CCKS Kerdock real-MUB set**;
  - Plus **1 non-stabilizer rotated block** `y=13` ($q_{13} = 0.1587$, $F_4 = 12.764$).
- **Verdict:** $n = 8$ `seed 0` is a **9-block Kerdock real-MUB superposition** (exhausting all $2^{4-1} + 1 = 9$ real MUBs of $m=4$ in a doubled `3+5` version of the $n=7$ 5-block architecture). Because increasing from 5 to 9 blocks raises the cross-slice interference multiplicity to $r = 4$, it immediately triggers **Horn 2** of the Stage 13 two-horned Kerdock obstruction ($F_8 = 2.792 > F_7 = 2.372$, $c_8 = 1.617 < c_7 = 1.797$).

---

## 5. Complete Verified Dead-End Ledger (Through Stage 14)

Do **not** re-investigate any of the following (all decisively settled with exact data or proofs):
1. Continuous spectral moment bounds on $S(\sigma)$ (`Tr(r_t^3) ≤ 1`, `Tr(M_n^4)` Cauchy–Schwarz): all collapse identically to $c \le 2$.
2. Classical single-MUB spread additive energy $E_{\mathrm{add}}(p)$: tight at Welch via 1-spike classical distributions.
3. Sign-blind / pure-$c_p^2$ / Bell-difference-sampling Delsarte LPs: $q_{\mathrm{SIC}}$ satisfies every $\widehat{q^k} \ge 0$ constraint (Proposition 2.3).
4. Fixed $t = 8$ Clifford-PPT hierarchy for $n \ge 7$: all 5 cones turn PSD on $y_H(d)$ for $d \ge 52 + 2\sqrt{574} \approx 99.92 < 128$.
5. Multi-block MUB superpositions (Desarguesian, Kerdock, Z-shifted, recursive Clifford-$F_m$) for driving $F_n \to 2$: locked by the two-horned obstruction (Horn 1: $k \le 3 \implies F_{\mathrm{intra}} \propto 2^m/5^3 \to \infty$; Horn 2: $k \ge 4 \implies \kappa_{\mathrm{cross}} \ge 2.0\text{–}2.8$).
6. Bulk `-3` eigenvalue quantization of $S(\sigma)$ and naive flat-amplitude `Alltop.lean` stability ($I_2 = 1$): refuted by Probe 2 (`-3 -> -7 -> -15` tracking and $I_2 \to 2$).
7. Heavy finite-$n$ certificate engineering (e.g., formalizing the 381-dim $t = 8$ SDP for $n=4,5,6$ or DPLL scaling).

---

## 6. Next-Stage Pure-Theory Attack Roadmap

1. **Route 1 (Immediate General-$n$ Lean 4 Formalization Package):**  
   Formalize the four clean, zero-search all-$n$ theorems from Section 2 into a new module (under the 8 GB single-module build discipline):
   - Theorem 2.1: 3-line classification of multi-qubit Pauli-SICs & strict Welch separation $F_n(|\psi\rangle) > \frac{2d}{d+1}$ ($\forall n \neq 1, 3$) and strict $1 - 2\rho_n(\sigma) < \frac{2\sqrt{d+1}}{d+2}$;
   - Theorem 2.2: complete quantitative double equivalence $\liminf F_n^* = 2 \Rightarrow \limsup \alpha_n^* = 1 \Longleftrightarrow \limsup c_n^* = 2$;
   - Proposition 2.3: pure-$c_p^2$ Bell-sampling LP meta-obstruction ($\widehat{q_{\mathrm{SIC}}^k} \ge 0$);
   - Exact Gaussian-integer parity congruence $\frac{1}{2}(S(\sigma)+I) \in M_d(\mathbb{Z}[i])$.
2. **Route 2 (Hard Battle A — General $t = 4m$ $R_{4m}$-Ideal Theory):**  
   Compute $Q_{4m}$ directly inside the tiny $R_{4m}$-ideal (bypassing the full commutant) at $t = 12$ ($6:6$ cut) and derive the general-$m$ asymptotic law for $d_0(4m)$ (testing $2^{\Theta(m^2)}$ vs $(2m)!$ vs $4^{2m}$), and evaluate whether the $R_{4m}$-ideal alone gives an explicit closed-form PPT theorem for all $t = 4m$.
3. **Route 3 (Hard Battle B — True Quantitative $\liminf F_n^* > 2$ or $\limsup c_n^* < 2$):**  
   Attack the coupled multi-MUB discrete constraint uncovered by Probe 2: across all $d+1$ MUBs $L_k$, the Born variables $Y_{L_k}(x) = 1 + \frac{m_{k,x}}{\sqrt{d+1}} \ge 0$ must simultaneously have odd-integer WHTs $m_{k,x}$ bounded below by $-\sqrt{d+1}$, average third moment $\mathbb{E}[Y^3] \to 6$ (Porter–Thomas), minimal 4th additive energy $d E_{\mathrm{add}}(p_k) - 1 \to 1/d$, and non-bilinear symplectic 2-cocycle consistency $\gamma(p,q) = Q_0(p)Q_0(q) + a_1 \cdot b_2$ across spreads. Targeting $\liminf F_n^* > 2$ directly (exploiting the sparse-spike gap over $c < 2$) or bounding $\mathrm{Tr}(S(\sigma)^4) \le (1-\delta)T_2^2$ remain the two sharpest paths to a true asymptotic constant gap.
