# General-$n$ Asymptotic Magic, Pauli Contextuality, and Clifford-PPT Phase Transitions: Theory Notes & Insights (Stages 12–17)

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

### Already Machine-Verified in Lean 4 ([`MultiQubitMUB/AsymptoticContextuality.lean`](MultiQubitMUB/AsymptoticContextuality.lean), [`MultiQubitMUB/AsymptoticBarriers.lean`](MultiQubitMUB/AsymptoticBarriers.lean), [`MultiQubitMUB/AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean) & [`MultiQubitMUB/AsymptoticPauliSlicing.lean`](MultiQubitMUB/AsymptoticPauliSlicing.lean))
Zero `sorry`, zero `native_decide`, zero `set_option`, **116/116 audited theorems** in [`Audit.lean`](Audit.lean) (53 baseline + 21 in `AsymptoticBarriers.lean` + 26 in `AsymptoticChar2Theory.lean` + 16 in `AsymptoticPauliSlicing.lean`, `peak_pgid_rss = 4854.8 MB`) depending solely on `[propext, Classical.choice, Quot.sound]` (115 standard + 1 zero-axiom `symIdxTables_valid`):
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
4. **General-$n$ Barriers, Complete Quantitative Double Equivalence, and Arithmetic Obstructions ([`MultiQubitMUB/AsymptoticBarriers.lean`](MultiQubitMUB/AsymptoticBarriers.lean), 1,298 lines, 21 audited theorems):**
   - Strict all-$n \ge 2, n \neq 3$ non-squareness, spectral contextuality, and 3-line cubic-trace no-Pauli-SIC (`pow_two_add_one_ne_sq`, `sqrt_pow_two_add_one_ne_rat`, `signCubeSum_lt_spectral`, `frustPairs_gt_spectral`, `no_pauli_sic_via_cubic_trace`);
   - Exact linear quantitative double equivalence (`pauliL1_ge_of_pauliMoment4`, `pauliAlpha_ge_of_pauliMoment4`, `exists_unit_state_rayleigh_ge_cube`, `exists_unit_state_pauliL1_ge_of_signCubeSum`, `exists_unit_state_pauliAlpha_ge_of_frustPairs`);
   - Pure-$c_p^2$ / Bell-sampling LP meta-obstruction (`qSIC_nonneg`, `sum_qSIC_eq_one`, `sympWHT_qSIC_eq`, `sympWHT_qSIC_pow_nonneg`, `qSIC_moment4_eq_welch`);
   - Gaussian-integer congruence $(S(\sigma)+I)/2 \in M_d(\mathbb{Z}[i])$ & quantitative stabilizer-basis IPR obstruction (`signMat_diag_odd_int`, `signMat_offdiag_even_re_im`, `signMat_add_id_half_gaussInt`, `compBasisIPR_eq_sum_Z_pauliSq`, `compBasisIPR_eq_welch_of_flat_pauli`, `compBasisIPR_sub_welch_sq_le`).
5. **Stages 15–16 Characteristic-2 Gowers-$U^3$, Complex-Symmetric Duality, 3B Quartic Sandwich & $O^\varepsilon(2s,2)$ Telescoping ([`MultiQubitMUB/AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean), 2,198 lines, 26 audited theorems):**
   - Exact characteristic-2 Gowers-$U^3(\mathbb{F}_2^n)$ box reality, $F_n = d\sum H(a,u)^2$, non-negative surplus decomposition $E_{\mathrm{amp}} + E_K + E_H$, and real-state floor $F_n \ge 3 - \frac{2}{d}$ (`gowersBox_im_zero`, `pauliMoment4_eq_gowersBox_sum`, `pauliMoment4_sub_welch_eq_gowers`, `pauliMoment4_real_state_ge`);
   - Theorem A exact individual-coset formulas $S_{\mathrm{indiv,Abs}}$, $S_{\mathrm{indiv,Re}}$ and Welch floor $\frac{2d(d-17)}{(d+1)^2}$ (`indivCosetAbsEnergy_eq`, `indivCosetReEnergy_eq`, `indivCosetReEnergy_ge`, `indivCosetReEnergy_ge_welch_floor`);
   - Theorem B complex-symmetric $\Sigma = |\psi\rangle\langle\psi^*|$ symplectic WHT Parseval duality, $\sum w_p = d$, $\sum (w_p - \frac{2}{d+1})^2 = F_n - \mathrm{Welch}_n$, $\sum \tilde{c}_p^2 = d\tilde{c}_0^2$, and Takagi flatness bound $\frac{4d}{d+1}(1 - \tilde{\alpha}_n) \le F_n - \mathrm{Welch}_n$ (`symPauliExpect_eq_zero_of_antisym`, `symPauliNormSq_eq_sympWHT`, `sum_symPauliNormSq_eq_dim`, `sum_symPauliNormSq_sub_ideal_sq`, `symPauliExpect_sq_sum_eq`, `pauliMoment4_sub_welch_ge_symPauliAlpha`);
   - Path 3B symplectic autocorrelation expansion $S(\sigma)^2$, cubic/quartic traces, Rayleigh quartic bound, and exact sandwich $(\alpha_n^*)^4 \le \max_\sigma \mathrm{Tr}(S(\sigma)^4)/T_2^2 \le (\alpha_n^*)^2$ (`signMat_sq_eq_pauliExpand`, `matTr_signMat_cube_eq_autocorr`, `matTr_signMat_fourth_eq_autocorr`, `rayleigh_pow_four_le_matTr_fourth`, `pauliAlpha_pow_four_le_signMat_fourth`, `signMat_fourth_le_sq_of_alpha_bound`);
   - Stage 15 universal $q=2$ Chu–Vandermonde telescoping, exact Witt bidiagonal recurrence, universal stabilizer evaluation ratio & non-negativity, permanent $C_2(4m, 2r) > 0$ sign flip for all $m \ge 4$ ($t \ge 16$), and Theorem C Fermat two-squares descent $R^2 + I^2 = 4^m$ (`qChuVandermonde_telescoping`, `orthProjCoeff_bidiagonal_recurrence`, `orthProjCoeff_sum_eq_stabilizer_ratio`, `orthProjCoeff_sum_nonneg`, `c2_cancellation_pos_ge_16`, `int_sq_add_sq_eq_pow_four`).
6. **Stage 17 New Tool 1 — Pauli-Slicing Renormalization ($n \to n - 1$), Two-State Disjointness Functional $\mathcal{J}_m$, Complex-Symmetric Self-Duality & Unconditional $\frac{17}{8} > 2$ Constant-Gap Theorems ([`MultiQubitMUB/AsymptoticPauliSlicing.lean`](MultiQubitMUB/AsymptoticPauliSlicing.lean), 1,712 lines, 16 audited theorems):**
   - Two-state overlap identities & complex-symmetric self-duality (`pauliCrossOverlap4_eq_pauliOverlap4`, `pauliOverlap4_eq_one_add_supportOverlap`, `twoStateJ_ge_two_sub_inv_add_overlap`, `pauliOverlap4_eq_sum_symPauliNormSq`, `twoStateJ_eq_dual_symPauli`);
   - Exact Pauli-slicing renormalization identity $F_{m+1}(\psi) = 2w_0^4 F_m(\phi_0) + 2w_1^4 F_m(\phi_1) + 20 w_0^2 w_1^2 G_m + 8 w_0^2 w_1^2 Q_{\mathrm{phase}}$, explicit elementary Clifford conjugation (`S_k, H_k`, swap, CNOT) of any $q \neq 0$ to $Z_0$, and unconditional universal reduction $(1 - (2^{m+1}+1)^{-1/2})^4 \mathcal{J}_m(\phi_0, \phi_1) \le F_{m+1}(\psi)$ (`pauliMoment4_slicing_identity`, `exists_clifford_to_Z0`, `pauliMoment4_ge_twoStateJ_universal`);
   - Exact hyperplane & hyperbolic-quadric mass splits (`sum_pauliSq_hyperplane`, `sum_pauliSq_quadric`), general two-state lower bounds (`twoStateJ_ge_of_hyperplane`, `twoStateJ_ge_of_quadric`), and unconditional $\frac{17}{8} = 2.125 > 2$ constant-gap theorems for real-sliced ($\forall m \ge 2$, $> 2$ for $m \ge 4$) and stabilizer-sliced ($\forall m \ge 2$, $> 2$ for $m \ge 4$) pairs (`twoStateJ_ge_seventeen_eighths_of_real`, `twoStateJ_gt_two_of_real`, `twoStateJ_ge_seventeen_eighths_of_stabilizer`, `twoStateJ_gt_two_of_stabilizer`).

---

## 2. General-$n$ Pure-Theory Results & Meta-Obstructions (Machine-Verified in [`AsymptoticBarriers.lean`](MultiQubitMUB/AsymptoticBarriers.lean))

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

### 3.3 Stage 14 Observation: The $R_8$-Ideal Support Structure

Dissecting the negative eigenvector $Q$ of $\tau_2$ and $\tau_4$ revealed **why** the $t = 8$ witness is 1-dimensional ($m=1$):
1. Define the Pauli-invariant `[t, 1]` repetition-code operator $R_t := \frac{1}{d}\sum_{p \in \mathbb{F}_2^{2n}} P_p^{\otimes t}$ ($t \equiv 0 \pmod 4$, satisfying $R_t^2 = d R_t$ so $P_{R_t} := \frac{1}{d} R_t$ is an orthogonal projector).
2. Under an **even** partial-transpose cut $k = 2r$ ($\tau_2, \tau_4$), $(1^8, 0)$ and $(0, 1^8)$ remain compatible with doubly-even parity, generating a tiny closed two-sided ideal $R_8 \cdot \mathrm{Alg}_k \cdot R_8$ of dimension **14** (out of 149) for $\tau_2$ and **34** (out of 381) for $\tau_4$. Under an **odd** cut ($\tau_3$, $5:3$), $(1^5 0^3, 0^5 1^3)$ has odd weights and the $R_8$-ideal has dimension **0**, forcing $\tau_3$ into a 5-dimensional weight-6 anti-stochastic subspace that dies early at $d_0 \approx 27.93$.
3. Inside $R_8 \cdot \mathrm{Alg}_k \cdot R_8$, the negative eigenvector $Q$ has **exact zero Hilbert–Schmidt overlap** with every basis subspace having $\dim(L) \ge 2$ (`11` elements in $\tau_2$, `29` elements in $\tau_4$), and its coefficients on the remaining $\dim(L) = 1$ double-coset orbits of $R_8$ are **exact combinatorial orbit sizes**:
   - $\tau_2$: 3 orbits with weights `1 : 15 : 20` (summing to `36`, matching the numerator coefficient $36$ of the stabilizer evaluation);
   - $\tau_4$: 5 orbits with weights `1 : 16 : 36 : 16 : 1` (summing to `70`, matching the numerator coefficient $70$ of the stabilizer evaluation).

### 3.4 Stage 15 Resolution: Exact General-$t = 4m$ $O^\varepsilon(4m-2,2)$ Projection, $C_2(4m,2r)$ Cancellation Theorem, $t = 12/16$ Phase Transitions, and the Linear-Copy Ceiling

Stage 15 completely solves the general-$t = 4m$ $R_{4m}$-ideal Clifford-PPT problem analytically and settles its asymptotic ceiling (`idea/stage15_check_t8_Mj.c`, `stage15_t12_asymptotics.c`, `stage15_t12_exact_k012_plus_mc.c`):

#### (1) True Underlying Symmetry Group $O^\varepsilon(4m - 2, 2)$ (Replacing the Binomial-Weight Guess)
For every $t = 4m \ge 4$ and every even partial-transpose cut $k = 2r \in \{0, 2, \dots, 4m\}$, let $s := 2m - 1$ (so $2s = 4m - 2$) and $G_k := S_{t-k} \times S_k$. On $\mathrm{Im}(P_{R_t}) \cong \mathbb{C}[V_t^n]$, the quotient space $V_t := E_t / \langle 1^t \rangle \cong \mathbb{F}_2^{2s}$ carries the non-degenerate partial-transposed quadratic form
$$q_{2r}(x) := \frac{|x_L| - |x_H|}{2} \pmod 2, \qquad \varepsilon := \mathrm{Arf}(q_{2r}) = (-1)^{m-r} \in \{+1, -1\},$$
with Witt index $\nu = s = 2m - 1$ when $\varepsilon = +1$ and $\nu = s - 1 = 2m - 2$ when $\varepsilon = -1$. The $\dim(L) = 1$ quotient of the $R_{4m}$-ideal is governed by the **full orthogonal group $O^\varepsilon(2s, 2)$** (not $S_{4m}$!):
- At $t = 8, \tau_4$: the weights `1 : 16 : 36 : 16 : 1` only coincided with $\binom{4}{j}^2$ because of the exceptional low-dimensional isomorphism **$O^+(6, 2) \cong S_8$** ($D_3 = A_3$);
- At $t = 8, \tau_2$: the weights `1 : 15 : 20` (sum `36`) are the $S_6 \times S_2$ double-coset sizes inside **$O^-(6, 2) \cong W(E_6)$** (order $51{,}840$, index $36$);
- By $t = 12, \tau_6$: $|O^+(10, 2)| = 46{,}998{,}591{,}897{,}600 \approx 4.70 \times 10^{13}$ is **$98{,}118\times$ larger than $|S_{12}| = 12!$**, with index $[O^+(10, 2) : S_6 \times S_6] \approx 9.066 \times 10^7$.

#### (2) Universal Closed-Form Orthogonal Projection & Stabilizer Identity ($\forall m \ge 1, \forall 0 \le r \le 2m, \forall d = 2^n$)
Inside the $R_{4m}$-ideal, the $\dim(L) \ge 2$ subspaces form a two-sided *-ideal $\mathcal{I}_{\ge 2}$. For each $j \in \{0, \dots, \nu\}$, let $M_j^{(4m, 2r)}$ be the uniform average of $A_{\bar{T}} := \frac{1}{d} r(T)^{\otimes n}$ over all Lagrangians $\bar{T} \subset V_t \oplus V_t$ of kernel dimension $j$ (so $M_0$ averages over the graphs of $O^\varepsilon(2s, 2)$). By Witt's theorem, the $(\nu + 1)$-dimensional $O^\varepsilon(2s, 2)$-bi-invariant commutative algebra $\mathcal{A}(s, \varepsilon) = \mathrm{span}\{M_0, \dots, M_\nu\}$ obeys the exact upper-bidiagonal multiplication law:
$$N_1 M_1 M_i = (2^i - 1)\bigl(d + 2^{2s - i - 1}\bigr) M_i + 2^i(2^{s-i} - \varepsilon)(2^{s-i-1} + \varepsilon) M_{i+1} \qquad (0 \le i \le \nu),$$
where $N_j(s, \varepsilon) := \prod_{i=1}^{j} \frac{(2^{s-i+1} - \varepsilon)(2^{s-i} + \varepsilon)}{2^i - 1}$ is the number of $j$-dimensional totally singular subspaces of $(V_t, q_{2r})$.

**Theorem 3.1 (Universal Closed-Form $R_{4m}$-Ideal PPT Projection).**  
Solving $M_1 Q = 0$ uniquely determines the exact orthogonal projector $Q_{\mathrm{orth}}^{(4m, 2r)}(d)$ onto $\mathcal{I}_{\ge 2}^\perp$ inside $\mathcal{A}(s, \varepsilon)$ ($Q^2 = Q = Q^\dagger \succeq 0$, $M_j Q = 0\;\forall j \ge 1$):
$$Q_{\mathrm{orth}}^{(4m, 2r)}(d) = \sum_{j=0}^{\nu} (-1)^j \frac{2^{\binom{j}{2}} N_j(2m - 1, \varepsilon)}{\prod_{i=1}^{j}\bigl(d + 2^{4m - 3 - i}\bigr)} M_j^{(4m, 2r)}.$$
Consequently, every $n$-qubit PPT state (in particular every pure state $|\psi\rangle^{\otimes 4m}$) satisfies $\mathrm{Tr}\bigl(\tau_{2r}(Q_{\mathrm{orth}}^{(4m,2r)}(d))\,\rho^{\otimes 4m}\bigr) \ge 0$, with exact universal stabilizer evaluation ($\forall d = 2^n \ge 1$):
$$\mathrm{Tr}\!\left(\tau_{2r}\bigl(Q_{\mathrm{orth}}^{(4m, 2r)}(d)\bigr)|0^n\rangle\langle 0^n|^{\otimes 4m}\right) = \frac{1}{d}\cdot\frac{\prod_{i=0}^{\nu - 1}(d - 2^i)}{\prod_{i=1}^{\nu}\bigl(d + 2^{4m - 3 - i}\bigr)} \ge 0.$$
- **Exact unification of $t = 4$ and $t = 8$:**
  - At $t = 4, \tau_2$ ($s = 1, \varepsilon = +1, \nu = 1, N_1 = 2$): $Q_{\mathrm{orth}}^{(4,2)}(d) = M_0 - \frac{2}{d+1}M_1$ evaluates on any pure $|\psi\rangle$ to $\frac{1}{d^2}\bigl(F_n(\psi) - \frac{2d}{d+1}\bigr) \ge 0$, recovering the **exact Welch bound**!
  - At $t = 8, \tau_2$ ($s = 3, \varepsilon = -1$) and $t = 8, \tau_4$ ($s = 3, \varepsilon = +1$): $Q_{\mathrm{orth}}^{(8,2)}$ and $Q_{\mathrm{orth}}^{(8,4)}$ reproduce **100% identically** both 13-term rational witnesses of Section 3.2 (in $\tau_4$, the unnormalized projection has denominator $(d+4)(d+8)(d+16)$ and simplifies on $y_H(d)$ via $(d+8)$ cancellation to $\frac{(d-1)(d-8)(d^2 - 104d + 408)}{70(d+1)^3(d+4)(d+16)}$; the factor $d^2 + 24d + 512$ in Section 3.2 arose solely from dividing by $\alpha_2^{(\tau_4)}$).

#### (3) Exact $d^{-2}$ Cancellation Theorem ($\forall t = 4m \ge 12, \forall k = 2r \in \{2, \dots, 4m-2\}$)
Evaluating $E_{\mathrm{orth}}(4m, 2r; d) := \mathrm{Tr}\bigl(\tau_{2r}(Q_{\mathrm{orth}}^{(4m,2r)}(d))\,y_H(d)\bigr)$ and normalizing by the $k_{\mathrm{Sym}} = 0$ weight $p_0 := \frac{(t-k)!k!}{|O^\varepsilon(t-2, 2)|}$ yields the exact large-$d$ expansion
$$\frac{E_{\mathrm{orth}}(4m, 2r; d)}{p_0} = \frac{1}{d} + \frac{C_2(4m, 2r)}{d^2} + O\!\left(\frac{1}{d^3}\right),$$
governed by three exact $k_{\mathrm{Sym}} \le 2$ contributions:
1. $(j = 1, k_{\mathrm{Sym}} = 1)$ ($T_{\text{anti}, t-2}$): $-2^{t-4}(t-k)k$;
2. $(j = 0, k_{\mathrm{Sym}} = 2, r_{\mathrm{cross}} = 1)$: $+\bigl(2^{t-4} - 1 - \frac{1}{2}\binom{t-2}{2}\bigr)(t-k)k$ — **the exponential $2^{t-4}$ cancels identically** with term 1, leaving only the polynomial negative residue $-(t-k)k\bigl(1 + \frac{1}{2}\binom{t-2}{2}\bigr) = -O(t^4)$;
3. $(j = 0, k_{\mathrm{Sym}} = 2, r_{\mathrm{cross}} = 0)$ (non-singular vectors in $V_t$): $+A_0(r=0) = +\Theta(2^{t-3})$, where
   $$A_0(r = 0) = \bigl(2^{t-3} - \varepsilon 2^{t/2 - 1}\bigr) - \binom{t-k}{2} - \binom{k}{2} - \frac{1}{2}\!\left[\binom{t-k}{3}\binom{k}{1} + \binom{t-k}{1}\binom{k}{3}\right].$$
Hence the exact universal $d^{-2}$ coefficient is
$$C_2(4m, 2r) = A_0(r = 0) - (t - k)k\!\left(1 + \frac{1}{2}\binom{t-2}{2}\right).$$
- At $t = 8$: $C_2(8, 2) = -102$, $C_2(8, 4) = -136$.
- At $t = 12$: $C_2(12, 2) = -140$, $C_2(12, 4) = -386$, $C_2(12, 6) = -500$.
- At $t = 16$: $C_2(16, 2) = +6498$, $C_2(16, 4) = +5360$, $C_2(16, 6) = +4946$, $C_2(16, 8) = +4648$ — **$C_2(4m, 2r) > 0$ permanently for every $t = 4m \ge 16$**, because $+2^{t-3}$ permanently overwhelms $-O(t^4)$!

#### (4) Exact $k_{\mathrm{Sym}} \le 2$ + Stratified MC Phase Transitions ($t = 12, 16$) & Growth-Law Verdict
Evaluating ALL $k_{\mathrm{Sym}} \in \{0, 1, 2\}$ across every $j = 0..\nu$ **100% exactly** (zero MC variance; verified to the single integer on all $7 \times 3$ strata at $t = 8$) and running OpenMP stratified MC strictly on the smooth $k_{\mathrm{Sym}} \ge 3$ bulk (`stage15_t12_exact_k012_plus_mc.c`) gives the complete phase-transition ladder:

| $t$ | Cut $\tau_{2r}$ | Group $O^\varepsilon(2s,2)$ | Exact $C_2(t, 2r)$ | **Root $d_0(t, 2r)$ on $y_H(d)$** | Key Evidence / Status |
|---:|---|---|---:|---|---|
| $4$ | $\tau_2$ ($2:2$) | $O^+(2, 2)$ | $-1$ | **$d_0 = 2$** | Exact Welch bound |
| $6$ | $\tau_2, \tau_3$ | — (no $R_6$) | — | **$d_0 = 8$** | Exact integer |
| $8$ | $\tau_2$ ($6:2$) | $O^-(6, 2) \cong W(E_6)$ | $-102$ | **$d_0 = 64$** | Exact rational witness |
| $8$ | $\tau_4$ ($4:4$) | $O^+(6, 2) \cong S_8$ | $-136$ | **$d_0 = 52 + 2\sqrt{574} \approx 99.92$** | Exact rational witness |
| **$12$** | $\tau_2$ ($10:2$) | $O^+(10, 2)$ | $-140$ | **$d_0 < 64$** | Strictly $> 0$ for all $d \ge 64$ ($+8.89\sigma$ at $512$, $+48.59\sigma$ at $1024$) |
| **$12$** | $\tau_4$ ($8:4$) | $O^-(10, 2)$ | $-386$ | **$d_0 \approx 220\text{–}250$** | Negative at $d = 64\,(-2.56\sigma), 128\,(-1.34\sigma)$; $+2.19\sigma$ at $512$, $+9.64\sigma$ at $1024$ |
| **$12$** | **$\tau_6$ ($6:6$)** | **$O^+(10, 2)$** | **$-500$** | **$d_0 \approx 550\text{–}650 \in (512, 1024)$** | **Breaks $t=8$ ceiling ($n=7,8$):** $-4.20\sigma$ ($d=64$), $-4.16\sigma$ ($d=128$), $-2.92\sigma$ ($d=256$), $-0.67\sigma$ ($d=512$), **$+5.63\sigma$ ($d=1024$)**, **$+33.66\sigma$ ($d=2048$)** |
| **$16$** | $\tau_8$ ($8:8$) | $O^+(14, 2)$ | **$+4648$** | **$d_0 \lesssim 2 \times 10^4$** | Even `EXACT(k<=2)` alone crosses zero at $d \approx 7.5 \times 10^4$ ($-3.42\times 10^{-25}$ at $65536$ vs $+2.23\times 10^{-24}$ at $131072$); positive $k \ge 3$ bulk shifts $d_0$ down by $\sim 4\times$ |

> **Definitive Verdict on Hard Battle A (Double Obstruction):**
> 1. **Single-Exponential Growth Law & Linear-Copy Barrier:** $d_0(4m, 2m) = \Theta(2^{4m})$ — governed by the leading pole scale $d + 2^{4m - 4}$ — refuting super-exponential $2^{\Theta(m^2)}$ or $(2m)!$ growth. Breaking $y_H(2^n)$ via the $R_{4m}$-ideal therefore requires **linear copies $t(n) = \Omega(n)$** (impossible at $t(n) \ll n$).
> 2. **Super-Exponentially Vanishing Violation Margin:** Because $p_0 = \frac{(2m)!^2}{|O^+(4m-2,2)|} \sim 2^{-4m^2}$ (already $|E_{\mathrm{orth}}| / E_{\mathrm{stab}} \sim 10^{-5}$ at $t = 12, d = 128$), the $R_{4m}$-ideal Clifford-PPT hierarchy cannot produce a uniform $O(1)$ asymptotic gap $\liminf F_n^* > 2$. Hard Battle A is now **theoretically closed**.

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

### 4.3 Stage 16 Breakthrough: Characteristic-2 Gowers-$U^3(\mathbb{F}_2^n)$ Anatomy, Complex-Symmetric Duality, and 3B Boundary Calibration

#### (1) Strategic Sandwich Equivalence for 3B ($\forall n \ge 1$)
For every $n \ge 1$ and $T_2 := d(d^2 - 1)$, every $\pm 1$ sign assignment $\sigma$ and unit state $|\psi\rangle$ satisfy the exact quartic-trace sandwich:
$$\bigl(\alpha_n^*\bigr)^4 \;\le\; \max_{\sigma \in \{\pm 1\}^{d^2 - 1}} \frac{\mathrm{Tr}\bigl(S(\sigma)^4\bigr)}{T_2^2} \;\le\; \bigl(\alpha_n^*\bigr)^2, \qquad \mathrm{Tr}\!\left(S(\sigma)^4\right) = d(d^2 - 1)^2 + d \sum_{r \neq 0} A_r(\sigma)^2.$$
Hence Path 3B is strictly equivalent to $\limsup \alpha_n^* < 1 \iff \limsup c_n^* < 2$ (strictly stronger than $\liminf F_n^* > 2$ due to the sparse-spike gap).

#### (2) 3A Clifford-Orbit Flow, 2-Plane Coset Distribution & $\mathbb{Z}_d$ Golden Litmus Test Contrast (`stage16_probe1`, `probe2`, `probe4`)
Decomposing $F_n(\psi) - \frac{2d}{d+1} = E_{\mathrm{amp}} + E_K + E_H$ across $n = 3..8$ extremal states and Haar controls under 1,000–2,000 random Clifford bases + greedy Clifford optimization yields:

| State | $n$ | $d$ | Surplus | Cliff avg $E_{\mathrm{amp}}$ | Cliff avg $E_K$ | **Cliff avg $E_H$** | Greedy $\min E_H$ | $S_{\mathrm{indiv,Re}}$ | $\eta_H = E_H / S_{\mathrm{indiv,Re}}$ | $H^2$ `PR_frac` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Hoggar SIC | 3 | 8 | `0.0000` | `0.0000` | `0.0000` | **`0.0000`** | `0.0000` | `0.000–0.519` | **`0.0000`** | — |
| spike min-$F$ | 4 | 16 | `0.2682` | `0.0308` | `0.0321` | **`0.2053`** (76.5%) | `0.0713` | `0.525–0.827` | `0.136–0.303` | `0.200` |
| min-$F_5$ | 5 | 32 | `0.6096` | `0.0372` | `0.0350` | **`0.5374`** (88.2%) | `0.1140` | `1.373–1.460` | `0.244–0.403` | `0.154` |
| min-$F_6$ | 6 | 64 | `0.7545` | `0.0230` | `0.0233` | **`0.7082`** (93.9%) | `0.5420` | `1.618–1.727` | `0.426–0.456` | `0.177` |
| **Kerdock $n=7$** | **7** | **128** | **`0.3879`** | `0.0064` | `0.0061` | **`0.3754`** (96.8%) | **`0.2480`** | **`1.799–1.814`** | **`0.150–0.212`** | **`0.259`** |
| **$n=8$ seed 0** | **8** | **256** | **`0.7995`** | `0.0064` | `0.0065` | **`0.7866`** (98.4%) | **`0.7164`** | **`1.900–1.918`** | **`0.374–0.415`** | **`0.161`** |
| Haar $n=8$ | 8 | 256 | `2.0881` | `0.0161` | `0.0162` | **`2.0558`** (98.5%) | `2.0228` | `1.928–1.944` | `1.065` | `0.316` |

Key structural findings:
1. **Clifford concentration:** On every state, $\mathbb{E}_{\mathrm{Cl}}[E_{\mathrm{amp}}] = \mathbb{E}_{\mathrm{Cl}}[E_K] = \frac{2}{d+1}(F_n - \mathrm{Welch}_n) + O(d^{-2})$, placing **96.8%–98.5%** of the surplus in $E_H$; and `PR_frac = 0.16–0.26` proves $E_H$ is a **diffuse bulk floor** across all $\frac{(d-1)(d-2)}{2}$ pairs rather than sparse outliers.
2. **$\mathbb{Z}_d$ Litmus Test 2 contrast:** Exact $\mathbb{Z}_4, \mathbb{Z}_8$ Zauner SICs attain $F_{\mathbb{Z}_d} = \mathrm{Welch}_d$ to $10^{-15}$, yet have strictly positive squared-amplitude autocorrelation $d\sum_{a\neq 0}|\langle\psi^{\circ 2}|T^a|\psi^{\circ 2}\rangle|^2$ (`0.0800` at $d=4$, `0.0772` at $d=8$), confirming $K(a) \equiv 0$ and complex-symmetric flatness are characteristic-2 exclusive.
3. **Constant-amplitude phase-state floor (`stage16_probe4`):** On $\psi_x = \frac{1}{\sqrt{d}}e^{i\theta_x}$ ($F_n = 2 - \frac{1}{d} + E_K + E_H$, where odd-prime $\mathbb{Z}_p$ Alltop hits $E_K = E_H = 0$), $\mathbb{F}_2^n$ satisfies `min F_phase = 1.75 (n=2), 2.25 (n=3), 2.8125 (n=4; E_K=0 exact, E_H=7/8!), 2.625 (n=5), 2.648 (n=6), 3.134 (n=7)`.

#### (3) Three New Unconditional Characteristic-2 General-$n$ Theorems (All Pass Both Golden Litmus Tests & Machine-Verified in [`AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean))
1. **Theorem A (Exact Individual-Coset Floor & $+4$ vs $+3$ 3-Cube Shift):**  
   For every $n$-qubit unit state $|\psi\rangle$ in every stabilizer basis,
   $$S_{\mathrm{indiv,Abs}} = 4\,d\!\left(\sum_{a} r_a^2 - 3 r_0^2 + 2\sum_x p_x^4\right),$$
   $$S_{\mathrm{indiv,Re}} = 2\,d\sum_{a} r_a^2 + 2 E_K - 8 d r_0^2 + 8 d\sum_x p_x^4 - 2 d\left|\sum_x \psi_x^4\right|^2 \;\ge\; 2\,d\!\left(\frac{(1 - r_0)^2}{d - 1} - 4 r_0^2\right).$$
   At Welch IPR ($r_0 = \frac{2}{d+1}$), $S_{\mathrm{indiv,Re}} \ge \frac{2d(d - 17)}{(d+1)^2} \to 2$. At $n=3$ ($d=8$), $d - 17 = -9 < 0$ allows Hoggar's canonical basis $\frac{1}{\sqrt{6}}(1+i,0,-1,1,-1,-i,0,0)$ to attain `S_indiv_Re = 0.0000` (coset-by-coset annihilation); for all $n \ge 5$, coset-by-coset cancellation is impossible in every Clifford basis. Equivalently, in the Gowers $U^3$ 3-cube expansion, characteristic 2's extra degenerate locus $a \oplus u \oplus v = 0$ shifts the non-independent cube floor from $+3$ (on $\mathbb{Z}_d$) to $+4 - O(1/d)$, forcing the linearly independent 3-cube sum $X_H = E_H - S_{\mathrm{indiv,Re}} = 192\,d \sum_A \sum_{\lambda \in V(A)^*\setminus\{0\}} \mathrm{Re}\,P_\lambda(A)$ to cancel down to $-2$ instead of $-1$.
2. **Theorem B (Complex-Symmetric $\Sigma = |\psi\rangle\langle\psi^*|$ Parseval Duality & Takagi Flatness Lower Bound):**  
   For $\tilde{c}_p := \langle\psi^*|P_p|\psi\rangle$ (vanishing identically on $Q_0(p) = 1$) and $w_p := |\tilde{c}_p|^2$,
   $$w_p = \frac{1}{d}\sum_{q \in \mathbb{F}_2^{2n}} (-1)^{Q_0(q) + \omega(p, q)} c_q^2, \qquad \sum_{Q_0(p)=0}\left(w_p - \frac{2}{d+1}\right)^2 = F_n(|\psi\rangle) - \frac{2d}{d+1}, \qquad \sum_{Q_0(p)=0}\tilde{c}_p^2 = d\,\tilde{c}_0^2,$$
   and with $\tilde{\alpha}_n(\psi) := \frac{1}{d}\sqrt{\frac{2}{d+1}}\sum_{Q_0(p)=0}|\tilde{c}_p| \in (0, 1]$,
   $$\frac{4d}{d+1}\bigl(1 - \tilde{\alpha}_n(\psi)\bigr) \;\le\; F_n(|\psi\rangle) - \frac{2d}{d+1}, \qquad \tilde{\alpha}_n^* = \frac{1}{d\sqrt{(d+1)/2}}\max_\theta \left\|\sum_{Q_0(p)=0} e^{i\theta_p} P_p\right\|_{\mathrm{op}}.$$
3. **Theorem C (Fermat Two-Squares $\mathbb{Z}_4$-Rigidity for Even-$n$ Pauli-MUB Fiducials):**  
   Every integer solution to $R^2 + I^2 = 4^m$ satisfies $(R, I) \in \{(\pm 2^m, 0), (0, \pm 2^m)\}$. Combined with `signMat_offdiag_even_re_im`, every even-$n = 2m$ Pauli-MUB fiducial must be a $\mathbb{Z}_4$-phase state $\frac{1}{\sqrt{d}}i^{h(x) + 2q(x)}$ with $h$ bent ($E_K = 0$), and $U^2 + V^2 = 2\cdot 4^m$ forces both $D_a q$ and $D_a q \oplus h$ to be bent on $H_a/\langle a\rangle$ (giving a 5-line zero-case-split proof of no MUB fiducial at $n = 4$ and explaining `E_K = 0, E_H = 7/8` on $n=4$ phase states).

#### (4) 3B Reverse-Boundary Reconnaissance (`stage16_probe3`, `probe3b`): Peak at $n = 7$ Followed by Drop at $n = 8, 9$
Directly maximizing $\alpha_n(\psi)$ and $c_n(\sigma)$ (ignoring $F_n$) via smoothed-$L_1$ BB ascent + exact Hermitian alternating projection + hypercube discrete `sgn(A_r)` polish across Haar, MUB-block, `Hoggar ⊗ psi`, and analytic CCKS Kerdock seeds:

| $n$ | $d$ | Min $F_n$ | **Max $\alpha_n$** | **Max $c_n$** | $F_n$ at max-$c_n$ | Max $\tilde{\alpha}_n$ | $\mathrm{Tr}(S^4)/T_2^2$ | Extremal Structure |
|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 3 | 8 | `1.7778` | `0.93541` | `1.69706` | `1.7778` | `1.00000` | `0.7679` | Hoggar SIC |
| 4 | 16 | `2.1505` | `0.94234` | `1.64706` | `2.1612` | `0.98962` | `0.7952` | spike |
| 5 | 32 | `2.5490` | `0.93352` | `1.56112` | `2.6032` | `0.97178` | `0.7704` | min-$F_5$ |
| 6 | 64 | `2.7237` | `0.94348` | `1.66208` | `3.1605` | `0.96598` | `0.7932` | `Hoggar ⊗ Hoggar` (explicit sparse-spike gap: $c_6$ +0.19 over min-$F_6$ while $F_6 = 256/81$) |
| **7** | **128** | **`2.3723`** | **`0.96709`** | **`1.79675`** | **`2.3837`** | **`0.98419`** | **`0.8755`** | 5-block Kerdock (global attractor across all initializations) |
| **8** | **256** | **`2.7917`** | **`0.93866`** | **`1.62881`** | **`2.8794`** | **`0.97072`** | **`0.7790`** | 9-block Kerdock `seed 0` refined (**drops back below $n=7$**) |
| **9** | **512** | `4.1489` | **`0.93554`** | **`1.59078`** | **`4.1489`** | **`0.95356`** | **`0.7711`** | 5-block `(3+6)` Kerdock refined (**continues dropping**) |

**Calibration Verdict:** $n = 7$ (`c_7 = 1.7967`) is a finite-$n$ low-dimensional Kerdock sweet spot ($k=3, m=4$ threading both horns), not a climb toward $2$. Both $\liminf F_n^* > 2$ and $\limsup c_n^* < 2$ remain strongly supported empirically.

---

### 4.4 Stage 17 Invention — New Tool 1: Pauli-Slicing Renormalization ($n \to n - 1$) & the Two-State Support-Disjointness Uncertainty Functional $\mathcal{J}_m$

#### (1) Motivation: Diagnosing the Structural Mismatch of Existing Tools
Stages 12–16 revealed why every off-the-shelf toolkit stalls before an $O(1)$ gap:
- **Spectral / SDP / Clifford-PPT moments** only see low-degree continuous moments, are blind to $\mathbb{F}_2^n$ vs $\mathbb{Z}_d$ until $t = \Omega(n)$ (Dead End #8), and suffer super-exponentially vanishing margins;
- **Additive combinatorics ($U^3$ inverse theorems)** are built for *large* $U^3$ norms of $L_\infty$-bounded functions, whereas we need an *anti-pseudorandomness lower bound* on unbounded $L_2$-normalized quantum amplitudes;
- **Integrality / Galois / Fermat rigidity** sees characteristic 2 sharply but yields only $\mathrm{poly}(1/d)$ continuous stability (Dead End #10).

A bespoke tool for $\liminf F_n^* > 2$ must (i) explicitly exploit characteristic-2 real Pauli expectations $c_p \in \mathbb{R}$, (ii) fail sharply on both Golden Litmus Tests ($n=3$ Hoggar and $\mathbb{Z}_d$ Zauner), and (iii) output a direct $O(1)$ macroscopic obstruction without modular arithmetic.

#### (2) Exact Pauli-Slicing Renormalization Identity & Unconditional 2-Line Reduction Theorem
For any $n$-qubit pure state $|\psi\rangle$ ($d = 2^n$, $D = d/2 = 2^{n-1}$) and any non-zero Pauli $P_q$ (conjugated by Clifford to $Z_1$), write
$$|\psi\rangle = \sqrt{w_+}\,|0\rangle|\psi_+\rangle + \sqrt{w_-}\,|1\rangle|\psi_-\rangle, \qquad w_\pm = \frac{1 \pm c_{Z_1}(\psi)}{2}, \quad \|\psi_\pm\| = 1.$$
Define the $(n-1)$-qubit cross-Pauli overlaps $z_r := \langle \psi_+ | P_r | \psi_- \rangle \in \mathbb{C}$, the support-overlap functional
$$G_{n-1}(\psi_+, \psi_-) := \sum_{r \in \mathbb{F}_2^{2(n-1)}} c_r(\psi_+)^2 c_r(\psi_-)^2 = \sum_{r \in \mathbb{F}_2^{2(n-1)}} |z_r|^4 = 1 + C(\psi_+, \psi_-),$$
and the relative-phase term $Q_{\mathrm{phase}}(\psi_+, \psi_-) := \sum_r \bigl((\mathrm{Re}\,z_r)^2 - (\mathrm{Im}\,z_r)^2\bigr)^2 \ge 0$. Expanding all $4^n$ Paulis $\{I, Z, X, Y\} \otimes P_r$ using real expectations $(x+y)^4 + (x-y)^4 = 2x^4 + 2y^4 + \mathbf{12}x^2 y^2$, $a^4 + b^4 = \frac{1}{2}(a^2+b^2)^2 + \frac{1}{2}(a^2-b^2)^2$, and symplectic Parseval $\sum_r |z_r|^4 = G_{n-1}(\psi_+, \psi_-)$ yields:

- **Theorem 4.4A (Exact Pauli-Slicing Identity, verified to `0.00e+00`–`1.51e-14` on $n = 3..6$):**
  $$F_n(\psi) = 2 w_+^4 F_{n-1}(\psi_+) + 2 w_-^4 F_{n-1}(\psi_-) + \mathbf{20}\, w_+^2 w_-^2 G_{n-1}(\psi_+, \psi_-) + 8 w_+^2 w_-^2 Q_{\mathrm{phase}}(\psi_+, \psi_-).$$
- **Theorem 4.4B (Unconditional Universal Reduction to Two-State Functional $\mathcal{J}_{n-1}^*$, $\forall n \ge 1$):**
  Since $\sum_{q \neq 0} c_q(\psi)^2 = d - 1$, every pure state admits a non-zero Pauli $P_q$ with $|c_q(\psi)| \le \frac{1}{\sqrt{d+1}}$, hence $w_\pm \ge \frac{1 - (d+1)^{-1/2}}{2}$. Dropping $Q_{\mathrm{phase}} \ge 0$ and decoupling $|\psi_\pm\rangle$ immediately yields:
  $$F_n^* \;\ge\; \left(1 - \frac{1}{\sqrt{2^n + 1}}\right)^4 \mathcal{J}_{n-1}^*, \qquad \mathcal{J}_m(\phi_+, \phi_-) := \frac{F_m(\phi_+) + F_m(\phi_-)}{8} + \frac{5}{4} G_m(\phi_+, \phi_-).$$
  Furthermore, writing $F_m(\phi_+) = 1 + A$, $F_m(\phi_-) = 1 + B$, $G_m = 1 + C$, Cauchy–Schwarz $A + B + 2C \ge \frac{4(D-1)}{D+1}$ gives
  $$\mathcal{J}_m(\phi_+, \phi_-) = \frac{3}{2} + \frac{A + B + 2C}{8} + C \;\ge\; 2 - \frac{1}{2^m + 1} + C(\phi_+, \phi_-).$$
  Thus **$\liminf_{m\to\infty} \mathcal{J}_m^* > 2 \implies \liminf_{n\to\infty} F_n^* > 2$** unconditionally, with zero near-Welch hypothesis and zero sparse-spike loophole!

#### (3) Why New Tool 1 Passes Both Golden Litmus Tests & Exposes Quantum Coherence
1. **Litmus Test 2 ($\mathbb{Z}_d$ Zauner SIC fails cleanly):** On $\mathbb{Z}_d$, substate expectations $c_r(\psi_\pm) \in \mathbb{C}$ can differ by a $90^\circ$ phase, dropping the commuting cross-term coefficient in $|u+v|^4 + |u-v|^4$ from **$12$ down to $4$** and destroying the support-disjointness penalty $+C$. Only characteristic-2 real Pauli expectations $c_r \in \mathbb{R}$ force the $+20 w_+^2 w_-^2 G_{n-1}$ disjointness barrier.
2. **Litmus Test 1 ($n = 3$ Hoggar SIC exact saturation):** At $n = 3$ ($w_+ = 2/3, w_- = 1/3$), $|\psi_-\rangle$ is a 2-qubit stabilizer state ($F_2 = 4$, supported on 3 Paulis) and $|\psi_+\rangle$ is a 2-qubit Alltop state ($F_2 = 7/4$, supported on the complementary 12 Paulis), giving $G_2 = 1$, $Q_{\mathrm{phase}} = 0$, and $2(2/3)^4(7/4) + 2(1/3)^4(4) + 20(4/81)(1) = \mathbf{16/9}$ with zero slack. For large $m$, stabilizer states explode ($F_m = 2^m \to \infty$), permanently closing Hoggar's asymmetric escape hatch.
3. **Abstract Polytope vs Pure-State Coherence Contrast:**
   - Inside the Bell+Theorem-B convex polytope $\mathcal{P}_m$ of non-negative vectors of squares ($x \ge 0, x_0 = 1, \widehat{x} = D x, \sum_r (-1)^{Q_p(r)} x_r \ge 0$), an elliptic quadric $Q_0 = 1$ is cut off by Theorem B, **but** taking $x = \frac{2}{D}\sum_{k < D/2} \mathbf{1}_{L_k}$ and $y = \frac{2}{D}\sum_{k \ge D/2} \mathbf{1}_{L_k}$ (averaging disjoint halves of a complete MUB spread) achieves $C = 0$ and $\mathcal{J}_m(x, y) = 2 - \frac{1}{2D} < 2$.
   - For **actual quantum states**, linear mixing destroys purity ($\mathrm{Tr}(\rho^2) = O(1/D) \ll 1$), while coherent pure-state superpositions of disjoint MUB halves produce cross-MUB interference that **destroys support disjointness ($C \ge 0.13\text{–}0.56$)**.
   - Moreover, $C \to 0$ forces **simultaneous Pauli unbiasedness of $|\phi_-\rangle$ against BOTH $|\phi_+\rangle$ and $|\phi_+^*\rangle$**: $|\langle\phi_+|P_s|\phi_-\rangle|^2 \approx 1/D$ AND $|\langle\phi_+^*|P_s|\phi_-\rangle|^2 \approx 1/D$ for all $s \in \mathbb{F}_2^{2m}$, while $F_m(\phi_\pm) \approx 3$.

#### (4) First Empirical Stress-Test (`stage17_probe1`, `stage17_probe2`, $m = 1..7$)
Unconstrained Riemannian Barzilai–Borwein minimization of $\mathcal{J}_m(\phi_+, \phi_-)$ (completely dropping $Q_{\mathrm{phase}}$ and decoupling $|\phi_\pm\rangle$), including adversarial coherent superpositions of disjoint Desarguesian MUB halves:

| $m$ | $D = 2^m$ | $n = m+1$ | **Free equal-$w$ $\mathcal{J}_m^*$** | Free weighted $\mathcal{J}_m^{\mathrm{wt}*}$ | $F_+$ / $F_-$ | **$C = G_m - 1$** | MUB-half raw $\to$ opt | Real pair $\mathcal{J}_m^{\text{real}}$ | Actual $F_{m+1}^*$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 2 | `1.687500` | `1.630669` | `1.500 / 2.000` | `0.00000` | — | `1.750` | `1.7500` |
| **2** | **4** | **3** | **`1.968750`** | **`1.777778` (`16/9`)** | `1.750 / 4.000` | **`0.00000`** | — | `2.250` | `1.7778` |
| **3** | **8** | **4** | **`2.102293`** | **`2.008220` (`> 2`)** | `2.705 / 2.813` | **`0.13009`** | `2.553 -> 2.102` | `2.594` | `2.1505` |
| **4** | **16** | **5** | **`2.335287`** | **`2.321481`** | `2.756 / 3.260` | **`0.26658`** | `2.926 -> 2.335` | `2.897` | `2.5490` |
| **5** | **32** | **6** | **`2.395299`** | **`2.413045`** | `3.077 / 3.077` | **`0.30081`** | `3.179 -> 2.415` | `3.440` | `2.6016`* |
| **6** | **64** | **7** | **`2.269891`** | **`2.261085`** | `2.882 / 3.382` | **`0.18959`** | `3.397 -> 2.270` | `3.458` | `2.3723` |
| **7** | **128** | **8** | **`2.816018`** | — | `3.445 / 3.491` | **`0.55920`** | `3.439 -> 2.816` | — | `2.7917` |

*(Bonus: `stage17_probe1` Part 3 also improved the empirical 6-qubit minimum to `F_6 = 2.601601` vs prior `2.7237`.)*  
**Key Anatomical Signals:** (i) $\mathcal{J}_m^*$ tracks $F_{m+1}^*$ within `0.05–0.21` across $m=3..6$ and bounces strongly back up at $m=7$ (`2.816`), showing almost the entire $> 2$ obstruction survives after dropping $Q_{\mathrm{phase}}$ and decoupling $|\phi_\pm\rangle$; (ii) at $m=3$, $|\phi_-\rangle$ is a real state (`28` exact zeros, `max w_p = 1.0`) colliding directly with Theorem B; (iii) at $m=5, 6$, neither state is real (`max w_p ≈ 0.20`), yet both slam onto the **boundary of the Theorem B cone (`min w_p = 0.0000`)** while still suffering $C \ge 0.19$.

#### (5) Four Unconditional Stage 17 Theorems (Machine-Verified in [`AsymptoticPauliSlicing.lean`](MultiQubitMUB/AsymptoticPauliSlicing.lean), 16 Audited Theorems) & $k = 1$ Uniqueness
1. **Uniqueness of $k = 1$ Positive-Definite Slicing:** Slicing along a $k$-qubit commuting subgroup splits $|\psi\rangle$ into $K = 2^k$ substates. For every $k \ge 2$ ($K \ge 4$), the 4th-moment expansion contains $\binom{K}{4}$ sign-canceling 4-body cross terms $v_{x_1}v_{x_2}v_{x_3}v_{x_4}$ ($k = n$ recovers Gowers $U^3$). **Only $k = 1$ ($K = 2 < 4$)** has identically zero 4-body cancellation, making Theorem 17.1 (`pauliMoment4_slicing_identity`) 100% positive-definite in $(F_+, F_-, G, Q_{\mathrm{phase}})$.
2. **Theorem 17.1 & 17.2 (Exact Slicing & Universal Reduction, ALL $m$):** Formalized via explicit elementary Clifford generators ($S_k$, $H_k$, qubit swap, involutive CNOT) conjugating any $q \neq 0$ to $Z_0$ (`exists_clifford_to_Z0`, `pauliMoment4_ge_twoStateJ_universal`), proving $(1 - (2^{m+1}+1)^{-1/2})^4 \mathcal{J}_m(\phi_0, \phi_1) \le F_{m+1}(\psi)$ for every pure state with zero near-Welch hypothesis.
3. **Theorem 17.3 (Exact Complex-Symmetric Self-Duality of $G_m$ and $\mathcal{J}_m$, ALL $m$):**
   Because $w_p(\phi) = \frac{1}{D}\sum_r (-1)^{Q_p(r)} c_r(\phi)^2$ (Theorem B) is an orthogonal involution on $Q_0(p) = 0$ up to $\sqrt{D}$, Parseval gives (`pauliOverlap4_eq_sum_symPauliNormSq`, `twoStateJ_eq_dual_symPauli`):
   $$G_m(\phi_1, \phi_2) = \sum_{Q_0(p)=0} w_p(\phi_1) w_p(\phi_2), \qquad \mathcal{J}_m(\phi_1, \phi_2) = \frac{1}{8}\sum_{Q_0(p)=0}\bigl(w_p(\phi_1) + w_p(\phi_2)\bigr)^2 + \sum_{Q_0(p)=0} w_p(\phi_1) w_p(\phi_2).$$
4. **Theorem 17.4 (Hyperplane / Quadric Mass Concentration & Unconditional $\frac{17}{8} = 2.125 > 2$ Constant-Gap Theorems, ALL $m$):**
   For every unit state $\phi$, every $q \neq 0$ splits Pauli mass across $q^\perp$ (`sum_pauliSq_hyperplane`) with $\sum_{r \neq 0,\, \omega(q,r)=0} c_r^2 = \frac{D - 2 + D c_q^2}{2}$, and every $p \in \{Q_0 = 0\}$ splits mass across the hyperbolic quadric $Q_p = 0$ (`sum_pauliSq_quadric`) with $\sum_{r \neq 0,\, Q_p(r)=0} c_r^2 = \frac{D - 2 + D w_p}{2}$. Two-bin Cauchy–Schwarz (`twoStateJ_ge_of_hyperplane`, `twoStateJ_ge_of_quadric`) yields, for every $m \ge 2$ ($D = 2^m$):
   - **Real-sliced pair** ($\exists p,\, w_p(\phi_1) = 1 \lor w_p(\phi_2) = 1$, i.e. at least one slice is Clifford-real):
     $$\mathcal{J}_m(\phi_1, \phi_2) \;\ge\; \frac{17}{8} - \frac{16 D - 18}{8(D - 1)(D + 2)} \;\xrightarrow{m \to \infty}\; \frac{17}{8} = 2.125, \qquad \text{strictly } > 2 \text{ for all } m \ge 4$$
     (`twoStateJ_ge_seventeen_eighths_of_real`, `twoStateJ_gt_two_of_real`).
   - **Stabilizer-sliced pair** ($\exists q \neq 0,\, c_q(\phi_1)^2 = 1 \lor c_q(\phi_2)^2 = 1$, i.e. at least one slice has any non-trivial Pauli stabilizer):
     $$\mathcal{J}_m(\phi_1, \phi_2) \;\ge\; \frac{17}{8} - \frac{12 D - 17}{8(D^2 - 2)} \;\xrightarrow{m \to \infty}\; \frac{17}{8} = 2.125, \qquad \text{strictly } > 2 \text{ for all } m \ge 4$$
     (`twoStateJ_ge_seventeen_eighths_of_stabilizer`, `twoStateJ_gt_two_of_stabilizer`).
   - *Immediate general-$n$ consequence:* Combined with Theorem 17.2, **every $n$-qubit complex state** admitting even one balanced slice ($|c_q| \le (d+1)^{-1/2}$) whose branch is Clifford-real or stabilizer-invariant unconditionally obeys $F_n(\psi) \ge \frac{17}{8} - O(2^{-n/2}) \to 2.125 > 2$! (In fact, Theorem 17.4 gives a strictly $> 2$ constant gap whenever *either* slice has $\max_{q\neq 0} c_q^2 \ge \varepsilon_0 > 0$ or $\max_{Q_0(p)=0} w_p \ge \varepsilon_0 > 0$ with fixed $\varepsilon_0 > 0$: the asymptotic floor is $2 + \frac{\varepsilon_0^2}{8}$!)

#### (6) Deep Anatomy (`stage17_probe3`, `stage17_probe4`): Pareto Frontier, $C = 0$ Stabilizer Collapse & Flat-Pauli Rank-1 Operator $T = |\phi_+\rangle\langle\phi_-|$
1. **$m = 7$ Convergence & Phase-Only Check (`probe3`, `probe4`):** Multi-start verification confirms $\mathcal{J}_7^* = 2.8160\text{–}2.8168$ ($C = 0.559$); slicing the adversarial 9-block Kerdock state on $m = 7$ gives `5.805 -> 4.406` (far above `2.816`). Phase-only pairs give $\mathcal{J}_m^{\text{phase}*} \in [2.344, 2.948]$ across $m = 3..6$.
2. **Exact $C = 0$ Disjoint-Support Explosion & Spontaneous Stabilizer Collapse:** Tracing the Pareto frontier $\min(\lambda(F_+ + F_-) + C)$ across $m = 1..6$ reveals that pushing $C \to 0$ drives $F_+ + F_-$ **monotonically upward** far past the Welch threshold $6$, and **every single unconstrained $C = 0$ minimizer collapses onto states with exact stabilizer symmetries (`stab >= 1`)**:

   | $m$ | $D$ | $\min_{C=0} (F_+ + F_-)$ | $\mathcal{J}_m$ at $C=0$ | Exact $C = 0$ Minimizer Anatomy (`probe4`) |
   |---:|---:|---:|---:|---|
   | 1 | 2 | `3.50` | `1.6875` | `1.50 + 2.00` (1-qubit stabilizer + magic) |
   | 2 | 4 | `5.75` (`< 6`) | `1.96875` | `|00⟩` ($F=4$) + `Alltop_2` ($F=7/4$), `stab >= 1` (Hoggar slices!) |
   | **3** | **8** | **`8.25`** (`> 6`) | `2.28125` | `|00⟩⊗|H⟩` + `F = 2.25` state, **`stab >= 1`** |
   | **4** | **16** | **`9.00`** | `2.37500` | `4.50 + 4.50` with **commuting stabilizers $Z_1, Z_2$** (`stab >= 1`) |
   | **5** | **32** | **`11.25`** | `2.65625` | `|0⟩⊗χ_-` ($5.25$) + `(|0⟩|0^4⟩ + e^{iπ/4}|1⟩|+^4⟩)/√2` ($6.10$), **`stab >= 1`** |
   | **6** | **64** | **`11.36`** | `2.670` | Strong stabilizer structure (`F_+ + F_- >> 6`) |

3. **Unimodular Phase Reformulation of $C = 0$ (Flat-Pauli Rank-1 Operator Rigidity):**
   Since $\sum_r |z_r|^2 = 1$ and $\sum_r |z_r|^4 = G_m = 1 + C$, exact support disjointness holds **if and only if** $|z_r| = |\langle\phi_+|P_r|\phi_-\rangle| = \frac{1}{\sqrt{D}}$ for all $r \in \mathbb{F}_2^{2m}$, i.e., the rank-1 operator $T := |\phi_+\rangle\langle\phi_-|$ has a **completely flat Pauli spectrum**:
   $$T = |\phi_+\rangle\langle\phi_-| = \frac{1}{D\sqrt{D}}\sum_{p \in \mathbb{F}_2^{2m}} \overline{f(p)}\,P_p, \qquad |f(p)| \equiv 1 \;\; (\forall p \in \mathbb{F}_2^{2m}).$$
   Evaluating $T T^\dagger = |\phi_+\rangle\langle\phi_+|$ and $T^\dagger T = |\phi_-\rangle\langle\phi_-|$ in the Pauli basis immediately gives the exact **twisted symplectic autocorrelation equations** on the unimodular phase function $f : \mathbb{F}_2^{2m} \to S^1$:
   $$c_r(\phi_+) + c_r(\phi_-) = \frac{2}{D^2}\sum_{\omega(p, r) = 0} \gamma(p, p\oplus r)\,\overline{f(p)}\,f(p\oplus r), \qquad c_r(\phi_+) - c_r(\phi_-) = \frac{2}{D^2}\sum_{\omega(p, r) = 1} \gamma(p, p\oplus r)\,\overline{f(p)}\,f(p\oplus r),$$
   coupled with exact rank-1 idempotence $T^\dagger T T^\dagger = T^\dagger$ and disjointness $c_r(\phi_+) c_r(\phi_-) = 0$ ($\forall r \neq 0$). Crucially, **if any unimodular flat-Pauli rank-1 rigidity theorem forces even one large Pauli expectation $\max_{q\neq 0} \max(|c_q^+|, |c_q^-|) \ge \varepsilon_0 > 0$ (or directly $F_+ + F_- \ge 6 + \delta_0$) stably for $C \ll 1$, then Theorem 17.4 immediately closes $\liminf \mathcal{J}_m^* > 2 \implies \liminf F_n^* > 2$!**

---

## 5. Complete Verified Dead-End Ledger (Through Stage 17)

Do **not** re-investigate any of the following (all decisively settled with exact data or proofs):
1. Continuous spectral moment bounds on $S(\sigma)$ (`Tr(r_t^3) ≤ 1`, `Tr(M_n^4)` Cauchy–Schwarz): all collapse identically to $c \le 2$.
2. Classical single-MUB spread additive energy $E_{\mathrm{add}}(p)$: tight at Welch via 1-spike classical distributions.
3. Sign-blind / pure-$c_p^2$ / Bell-difference-sampling Delsarte LPs: $q_{\mathrm{SIC}}$ satisfies every $\widehat{q^k} \ge 0$ constraint (Proposition 2.3).
4. Fixed $t = 8$ Clifford-PPT hierarchy for $n \ge 7$: all 5 cones turn PSD on $y_H(d)$ for $d \ge 52 + 2\sqrt{574} \approx 99.92 < 128$.
5. Multi-block MUB superpositions (Desarguesian, Kerdock, Z-shifted, recursive Clifford-$F_m$) for driving $F_n \to 2$: locked by the two-horned obstruction (Horn 1: $k \le 3 \implies F_{\mathrm{intra}} \propto 2^m/5^3 \to \infty$; Horn 2: $k \ge 4 \implies \kappa_{\mathrm{cross}} \ge 2.0\text{–}2.8$).
6. Bulk `-3` eigenvalue quantization of $S(\sigma)$ and naive flat-amplitude `Alltop.lean` stability ($I_2 = 1$): refuted by Probe 2 (`-3 -> -7 -> -15` tracking and $I_2 \to 2$).
7. Heavy finite-$n$ certificate engineering (e.g., formalizing the 381-dim $t = 8$ SDP for $n=4,5,6$ or DPLL scaling).
8. **General $t = 4m$ $R_{4m}$-ideal Clifford-PPT for sublinear $t(n) \ll n$ or constant asymptotic gap $\liminf F_n^* > 2$ (Stage 15):** exact $O^\varepsilon(4m-2,2)$ projection proves $d_0(4m, 2m) = \Theta(2^{4m})$ (single-exponential, requiring linear $t(n) = \Omega(n)$), permanent $C_2(4m, 2r) > 0$ sign flip for all $t \ge 16$, and super-exponentially vanishing margin $p_0 \sim 2^{-4m^2}$.
9. **Single-MUB Boolean WHT one-sided cubic/quartic obstruction & single-stabilizer 4th overlap moment (Stage 15 pre-checks):**
   - *Single-MUB WHT:* refuted directly at $n = 7$ ($d = 128$), where a single Boolean function $f : \mathbb{F}_2^7 \setminus \{0\} \to \{\pm 1\}$ attains $Y(x) = 1 + \frac{\widehat{f}(x)}{\sqrt{129}} \ge +0.0277 > 0$ everywhere with $\mathbb{E}[Y^2] = 2$, $\mathbb{E}[Y^3] = 5.9197$, $\mathbb{E}[Y^4] = 24.0693$ (Porter–Thomas moments are feasible inside a single MUB!).
   - *Single-stabilizer 4th overlap moment:* exact identity $\mathbb{E}_{|\phi\rangle \in \mathrm{Stab}_n}[d^4 |\langle\phi|\psi\rangle|^8] = A(d) + B(d)\,F_n(\psi)$ has $A(d) \to 24$, $B(d) = O(1/d) \to 0$; at Welch, $m_4(\mathrm{Welch}) \to 24$ stays strictly above the Hamburger lower bound $20$ for moments $(1, 2, 6)$, yielding zero $O(1)$ gap.
10. **Four Naive Characteristic-2 / 3A Shortcuts (Stage 16 Meta-Obstructions):**
    - *Naive $\sim d^2/2$ quartic equations vs $2d - 2$ real DOFs overconstraint counting:* fails Golden Litmus Test 2 ($\mathbb{Z}_d$ Zauner SICs satisfy the exact same quartic equation count yet exist for all tested $d \le 193$).
    - *Naive $L_1$ / Cauchy–Schwarz amplitude budget on linearly independent 3-cubes:* although Theorem A forces $S_{\mathrm{indiv,Re}} \to 2$ ($X_H \to -2$), the $\Theta(d^4)$ affine 3-cubes carry total $L_1$ budget $\Theta(d)$, easily accommodating $X_H = -2$ without sign-coherence obstruction.
    - *Proving $\limsup \tilde{\alpha}_n^* < 1$ via $F_n$-independent sparse spikes:* spikes of amplitude $d^{-1/4}$ supported on a self-dual Lagrangian $K = K'$ of size $d$ simultaneously allow $\alpha_n \to 1$ AND $\tilde{\alpha}_n \to 1$ while keeping $F_n - \mathrm{Welch}_n = \Omega(1)$; thus $\tilde{\alpha}_n^*$ shares the sparse-spike loophole (confirmed empirically: $\tilde{\alpha}_n^* \in [0.954, 0.990]$ for $n=4..9$).
    - *Pure integrality / Galois / Fermat two-squares rigidity alone:* exact arithmetic contradictions (Theorem 2.1, Theorem C) yield only $\mathrm{poly}(1/d)$ continuous stability, not an $O(1)$ macroscopic gap.
11. **Bell + Theorem-B Polytope Barrier for $\mathcal{J}_m$ & Two Related Stage 17 Non-Shortcuts:**
    - *Convex Bell + Theorem-B polytope $\mathcal{P}_m$ for $\mathcal{J}_m$:* partitioning a complete MUB spread into two disjoint halves of size $D/2$ gives $x = \frac{2}{D}\sum_{k<D/2}\mathbf{1}_{L_k}$, $y = \frac{2}{D}\sum_{k\ge D/2}\mathbf{1}_{L_k} \in \mathcal{P}_m$ satisfying $x, y \ge 0$, $x_0 = y_0 = 1$, $\widehat{x} = Dx$, $\widehat{y} = Dy$, $w_p(x), w_p(y) \ge 0$, and every $\widehat{x^k}, \widehat{y^k} \ge 0$, yet achieving $C(x, y) = 0$ and $\mathcal{J}_m(x, y) = 2 - \frac{1}{2D} < 2$. Hence once $\max c_q^2, \max w_p = o(1)$ (outside Theorem 17.4), proving $\mathcal{J}_m^* \ge 2 + \delta_0$ **must** use genuine rank-1 quantum purity ($\rho_\pm^2 = \rho_\pm$ or $T = |\phi_+\rangle\langle\phi_-|$ rank 1).
    - *Two-state $L_1$ difference ratio $\beta_m^* := \frac{1}{\sqrt{2T_2}}\max \sum_{r\neq 0}|c_r^+ - c_r^-|$ and 1-line $\det S(\tau) \neq 0$:* $\beta_m^*$ tracks $\alpha_{m+1}^*$ (same hardness as $\limsup \alpha_n^* < 1$); and $S(\tau) \equiv I \pmod 2 \implies |\det S(\tau)| \ge 1$ kills exact bimodal disjoint $|c_r^+ - c_r^-| = \sqrt{2/D}$ for all $m \ge 2$ in 1 line, but again yields only $\mathrm{poly}(1/D)$ continuous stability.

---

## 6. Next-Stage Pure-Theory Attack Roadmap

1. **Route 1 (COMPLETED & Machine-Verified in [`MultiQubitMUB/AsymptoticBarriers.lean`](MultiQubitMUB/AsymptoticBarriers.lean)):**  
   All four general-$n$ pure-theory theorem groups from Section 2 are formalized (1,298 lines, 21 audited theorems, `peak_pgid_rss = 4800.5 MB`, standard three Lean axioms only).
2. **Route 2 (COMPLETED — Stage 15 General-$t = 4m$ $R_{4m}$-Ideal Mechanism & Ceiling Settled & Machine-Verified):**  
   The complete $O^\varepsilon(4m-2,2)$ bidiagonal projection $Q_{\mathrm{orth}}^{(4m,2r)}(d)$, universal stabilizer identity, exact $C_2(4m,2r) > 0$ ($t \ge 16$) sign-flip theorem, $t=12/16$ phase transitions ($d_0(12,6) \approx 550\text{–}650$, $d_0(4m,2m) = \Theta(2^{4m})$), and double obstruction are resolved (Section 3.4) and their general-$m, s, \varepsilon, d$ algebraic core is machine-verified in [`AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean).
3. **Option C — Stage 15–16 General-$n$ / General-$m$ Pure-Theory Package (COMPLETED & Machine-Verified in [`MultiQubitMUB/AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean)):**  
   2,198 lines, 26 audited theorems across all 5 unconditional theorem groups; brought [`Audit.lean`](Audit.lean) to 100/100 (`peak_pgid_rss = 4936.2 MB`).
4. **Stage 17 New Tool 1 — Pauli-Slicing Renormalization & Unconditional $\frac{17}{8}$ Constant-Gap Package (COMPLETED & Machine-Verified in [`MultiQubitMUB/AsymptoticPauliSlicing.lean`](MultiQubitMUB/AsymptoticPauliSlicing.lean)):**  
   1,712 lines, 16 audited theorems across all 4 theorem groups (Theorems 17.1–17.4: exact slicing identity, explicit elementary Clifford conjugation & universal reduction to $\mathcal{J}_m^*$, complex-symmetric self-duality, hyperplane/quadric mass splits, and unconditional $\frac{17}{8} > 2$ constant-gap bounds for real-sliced and stabilizer-sliced pairs); **116 / 116 audited theorems** in [`Audit.lean`](Audit.lean) (`peak_pgid_rss = 4854.8 MB`, standard three Lean axioms only).
5. **Immediate Next Pure-Theory Frontier (Post-Commit Deep Excavation):**  
   - **Laser Target — Flat-Pauli Rank-1 Operator Rigidity ($C = 0$ and $C \ll 1$ stability):** On $T = |\phi_+\rangle\langle\phi_-| = \frac{1}{D\sqrt{D}}\sum_p \overline{f(p)} P_p$ ($|f(p)| \equiv 1$), investigate (i) whether stabilizer-free $C = 0$ pairs exist at all on $m = 3, 4, 5$ and what $f(p)$'s exact Gowers/bent/$\mathbb{Z}_4$ structure is; (ii) how the rank-1 equation $T^\dagger T T^\dagger = T^\dagger$ and twisted symplectic autocorrelations of unimodular $f : \mathbb{F}_2^{2m} \to S^1$ force either $F_+ + F_- \ge 6 + \delta_0$ or $\max(|c_q^\pm|, w_p^\pm) = \Omega(1)$ (which feeds directly into Theorem 17.4 to close $\liminf \mathcal{J}_m^* > 2 \implies \liminf F_n^* > 2$!).
   - **Companion Option A (Characteristic-2 Phase-State Gowers-$U^3$ Lower Bound):** prove an unconditional constant lower bound on constant-amplitude phase states $\psi_x = \frac{1}{\sqrt{d}}e^{i\theta_x}$ on $\mathbb{F}_2^n$ (empirically `min F_phase = 2.25..3.134` for $n=3..7$).
   - **Companion Option B (Discrete Real-Sign Macroscopic Rank-1 Obstruction on $S(\sigma)$):** exploit $\sigma_p \in \{\pm 1\}$ hypercube discreteness and non-bilinear symplectic 2-cocycle coupling $\gamma(p, p\oplus r)$ across $r$.
