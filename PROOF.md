# Complete Human-Readable Mathematical Proof

This document gives a complete, self-contained, human-readable proof of every theorem formalized in the Lean 4 library `MultiQubitMUB`. Every step mirrors the machine-checked proof in [`MultiQubitMUB/`](MultiQubitMUB/), with direct theorem-name cross-references.

---

## 1. Setup, Definitions, and Main Theorems

Let $n \ge 1$ be an integer, $d = 2^n$, and $\mathbb{F}_2^n = (\mathbb{Z}/2\mathbb{Z})^n$ with standard dot product $x \cdot y = \sum_{i=1}^n x_i y_i \in \mathbb{F}_2$ and sign character $\chi(x, y) := (-1)^{x \cdot y} \in \{\pm 1\}$.

### 1.1 Quantum States and Hermitian Involutive Pauli Operators

An $n$-qubit pure state is a vector $|\psi\rangle \in \mathbb{C}^{\mathbb{F}_2^n} \cong (\mathbb{C}^2)^{\otimes n}$ with Hermitian inner product $\langle \phi | \psi \rangle = \sum_{x \in \mathbb{F}_2^n} \overline{\phi(x)}\,\psi(x)$ and unit norm $\langle \psi | \psi \rangle = 1$.

For phase-space index $p = (a, b) \in \mathbb{F}_2^n \times \mathbb{F}_2^n$, define the phase $\eta(p) := i^{a \cdot b} \in \{1, i\}$ (identifying $0 \mapsto 1$, $1 \mapsto i$) and the operator $P_p$ on $\mathbb{C}^{\mathbb{F}_2^n}$ by
$$(P_{(a,b)}\psi)(x) := \eta(a,b)\,(-1)^{b \cdot x}\,\psi(x \oplus a).$$
On $\mathbb{F}_2^{2n}$, equip phase space with the non-degenerate symplectic bilinear form
$$\omega\bigl((a,b),(c,d)\bigr) := a \cdot d + b \cdot c \in \mathbb{F}_2.$$
A direct calculation verifies:
1. **Involution (`pauliApply_invol`):** $P_p^2 = I$, since $\eta(a,b)^2 (-1)^{b\cdot a} = (-1)^{a\cdot b}(-1)^{b\cdot a} = 1$.
2. **Hermiticity & Unitarity (`innerProd_pauliApply_right`, `innerProd_pauliApply_both`):** $\langle \phi | P_p \psi \rangle = \langle P_p \phi | \psi \rangle$, since $\eta(a,b)(-1)^{b\cdot a} = \overline{\eta(a,b)}$. Hence $\langle\psi|P_p|\psi\rangle \in \mathbb{R}$ for all $\psi, p$.
3. **Composition & Commutation (`pauliApply_comp`, `pauliApply_comm`, `pauliPhase_re_cases`):**
   $$P_p P_q = \gamma(p, q)\, P_{p \oplus q}, \qquad \gamma(p, q) := \eta(p)\eta(q)(-1)^{q_2 \cdot p_1}\overline{\eta(p \oplus q)} \in \{\pm 1, \pm i\}.$$
   Moreover:
   - $\gamma(p, q) = (-1)^{\omega(p, q)}\gamma(q, p)$, so $P_p P_q = (-1)^{\omega(p, q)} P_q P_p$;
   - $\omega(p, q) = 0 \implies \gamma(p, q) \in \{+1, -1\}$ (purely real);
   - $\omega(p, q) = 1 \implies \gamma(p, q) \in \{+i, -i\}$ (purely imaginary, $\operatorname{Re}\gamma(p,q) = 0$).

### 1.2 Core Definitions

- **Alltop function on $\mathbb{F}_2^n$ (`IsAlltop`):** A function $\phi : \mathbb{F}_2^n \to \mathbb{C}$ satisfying $|\phi(x)| = 1$ for all $x \in \mathbb{F}_2^n$ and
  $$\left|\sum_{x \in \mathbb{F}_2^n} (-1)^{b \cdot x}\,\overline{\phi(x)}\,\phi(x \oplus a)\right|^2 = 2^n \qquad \forall\, a \in \mathbb{F}_2^n \setminus \{0\},\; \forall\, b \in \mathbb{F}_2^n.$$
- **Pauli-covariant MUB fiducial state (`IsPauliMubFiducial`):** A unit vector $|\psi\rangle \in (\mathbb{C}^2)^{\otimes n}$ for which there exists a partition map $\pi : \mathbb{F}_2^{2n} \to \{0, \dots, 2^n - 1\}$ such that for all $p, q \in \mathbb{F}_2^{2n}$:
  - $\pi(p) = \pi(q)$ and $p \neq q \implies \langle P_p\psi | P_q\psi \rangle = 0$;
  - $\pi(p) \neq \pi(q) \implies |\langle P_p\psi | P_q\psi \rangle|^2 = 2^{-n}$.
  *(Note: This captures a fiducial generating a complete set of $2^n$ pairwise MUBs under $\mathcal{P}_n$—yielding $2^n + 1$ MUBs with the computational basis when $|\psi\rangle$ is equatorial—and does not assume a priori that the fibers of $\pi$ have equal size $2^n$; as shown in Lemma 3.1, the fibers are automatically the $2^n$ cosets of $H$, each of cardinality $2^n$. Smaller partial sets of $< 2^n$ covariant MUBs are outside the scope of this definition.)*
- **Pauli 4th moment (`pauliMoment4`, `phasePauliMoment4`):**
  $$F_n(|\psi\rangle) := \sum_{p \in \mathbb{F}_2^{2n}} |\langle\psi|P_p|\psi\rangle|^4,$$
  which relates to the order-2 Stabilizer Rényi Entropy by $M_2(|\psi\rangle) = -\ln\bigl(F_n(|\psi\rangle)/2^n\bigr)$. For a phase state $\psi(x) = 2^{-n/2}\phi(x)$ ($|\phi(x)| = 1$), $F_n(|\psi\rangle) = 2^n \|\phi\|_{U^3(\mathbb{F}_2^n)}^8$.

### 1.3 Statement of Main Theorems

- **Theorem 1 (`no_alltop_f2`):** For every $n \ge 3$, no Alltop function exists on $\mathbb{F}_2^n$. For $n = 2$, $\phi_2 = (1, 1, 1, i)$ IS an Alltop function (`exists_alltop_two`).
- **Corollary 1 (`phasePauliMoment4_gt_mub`):** For every $n \ge 3$ and every $\phi : \mathbb{F}_2^n \to U(1)$, $2^n \|\phi\|_{U^3(\mathbb{F}_2^n)}^8 > 2 - 2^{-n}$ strictly.
- **Theorem 2 (`no_pauli_mub_fiducial`):** For every $n \ge 3$, no unit vector $|\psi\rangle \in (\mathbb{C}^2)^{\otimes n}$ is a Pauli-covariant MUB fiducial state (generating $2^n$ pairwise MUBs under $\mathcal{P}_n$). In particular, this proves the $\omega_8$-phase non-existence statement (`damski_conjecture_1`, corresponding to Conjecture 1 of Damski–Bistroń–Ponterio–Czartowski–Życzkowski, `arXiv:2603.15550`) as well as the unrestricted non-existence of $2^n$ product-WH covariant MUBs from a fiducial for all $n \ge 3$, and rules out the conjectured WH-MUB maximal magic states of Liu–Low–Yin (`arXiv:2502.17550`, originally conjectured for $n \neq 1, 3$) for all $n \ge 4$. For $n = 2$, $|\psi_2\rangle = \frac{1}{2}(1, 1, 1, i)$ IS a Pauli-covariant MUB fiducial (`exists_pauli_mub_fiducial_two`).
- **Theorem 3 (`no_pauli_two_valued_odd`):** For every odd $n = 2k + 1 \ge 3$, no unit vector $|\psi\rangle \in (\mathbb{C}^2)^{\otimes n}$ even satisfies $|\langle\psi|P_p|\psi\rangle|^2 \in \{0, 2^{-n}\}$ for all $p \neq 0$ (no basis-partition hypothesis needed).
- **Theorem 4 (`pauliMoment4_spikeState`, `hoggar_sic_three`, `four_qubit_spike_bound`):** Exact closed-form formula for $F_n$ on the $\mathrm{GL}(n,\mathbb{F}_2)$-invariant, antiunitarily $(H^{\otimes n} \circ K)$-symmetric family $|\psi_n(s)\rangle$ (where $K$ is entrywise complex conjugation in the computational basis), recovering the 3-qubit Hoggar SIC ($F_3 = 16/9$) and certifying a 4-qubit unit state with $F_4 < 2.150521$.

---

## 2. Pauli Completeness and Direct Proof of Theorem 3 (All Odd $n \ge 3$)

### Lemma 2.1 (Pauli Completeness, Parseval, Symplectic Self-Duality, Purity)
For any $\psi, \phi \in \mathbb{C}^{\mathbb{F}_2^n}$:
1. **Completeness (`pauli_completeness`):**
   $$\sum_{p \in \mathbb{F}_2^{2n}} \langle\psi|P_p|\psi\rangle\, P_p \phi = 2^n \langle\psi|\phi\rangle\,\psi.$$
2. **Parseval (`pauli_parseval`):**
   $$\sum_{p \in \mathbb{F}_2^{2n}} \langle\psi|P_p|\psi\rangle \langle\phi|P_p|\phi\rangle = 2^n |\langle\psi|\phi\rangle|^2.$$
   In particular, for unit $\psi$, $\sum_p \langle\psi|P_p|\psi\rangle^2 = 2^n$ (`sum_normSq_pauliExpect`).
3. **Symplectic WHT Self-Duality (`pauli_symp_self_dual`):** For every $q \in \mathbb{F}_2^{2n}$,
   $$\sum_{p \in \mathbb{F}_2^{2n}} (-1)^{\omega(p, q)} \langle\psi|P_p|\psi\rangle^2 = 2^n \langle\psi|P_q|\psi\rangle^2.$$
4. **Purity Identity (`pauli_purity_identity`):** For every unit $\psi$ and $q \in \mathbb{F}_2^{2n}$,
   $$\sum_{p \in \mathbb{F}_2^{2n}} \langle\psi|P_p|\psi\rangle\,\gamma(q, p)\,\langle\psi|P_{q\oplus p}|\psi\rangle = 2^n \langle\psi|P_q|\psi\rangle.$$

*Proof.*
For (1), evaluate the LHS at $x \in \mathbb{F}_2^n$:
$$\sum_{a, b \in \mathbb{F}_2^n} \left(\sum_{y \in \mathbb{F}_2^n} \overline{\psi(y)}\,\eta(a,b)(-1)^{b\cdot y}\psi(y\oplus a)\right) \eta(a,b)(-1)^{b\cdot x}\phi(x\oplus a).$$
Since $\eta(a,b)^2 = (-1)^{a\cdot b}$, the inner sum over $b$ is $\sum_{b} (-1)^{b\cdot(x \oplus y \oplus a)} = 2^n \mathbf{1}_{y = x \oplus a}$. Substituting $y = x \oplus a$ (hence $y \oplus a = x$) and re-indexing $z = x \oplus a$ gives $2^n \bigl(\sum_z \overline{\psi(z)}\phi(z)\bigr)\psi(x) = 2^n \langle\psi|\phi\rangle\psi(x)$.

For (2), take $\langle\phi|\cdot\rangle$ of both sides of (1).
For (3), substitute $\phi = P_q \psi$ into (2) and use $\langle P_q\psi | P_p P_q\psi\rangle = (-1)^{\omega(p,q)}\langle\psi|P_p|\psi\rangle$.
For (4), set $\phi = \psi$ in (1) (so $\langle\psi|\psi\rangle = 1$) and take $\langle P_q\psi | \cdot \rangle$, using Hermiticity and $P_q P_p = \gamma(q,p)P_{q\oplus p}$. $\square$

### Proof of Theorem 3 (`no_pauli_two_valued_odd`)
Let $n = 2k + 1 \ge 3$ ($k \ge 1$) and suppose a unit vector $\psi$ satisfies $c_p := \langle\psi|P_p|\psi\rangle \in \mathbb{R}$ with $c_p^2 \in \{0, 2^{-n}\}$ for all $p \neq 0$.
1. Since $c_0 = 1$ and $\sum_p c_p^2 = 2^n \ge 8 > 1$, there exists $q \neq 0$ with $c_q \neq 0$, hence $c_q^2 = 2^{-n}$.
2. Take the real part of Lemma 2.1(4) at $q$ and peel off $p = 0$ and $p = q$ (both contribute $\gamma(q,0) = \gamma(q,q) = 1$, hence $c_q$ each):
   $$\sum_{p \notin \{0, q\}} \operatorname{Re}\bigl(\gamma(q, p)\bigr)\, c_p\, c_{q\oplus p} = (2^n - 2)\, c_q.$$
3. Multiply by $2^n$. For every $p \notin \{0, q\}$, both $p \neq 0$ and $q \oplus p \neq 0$, so $(2^n c_p c_{q\oplus p})^2 \in \{0, 1\}$, hence $2^n c_p c_{q\oplus p} \in \{-1, 0, +1\} \subset \mathbb{Z}$. Moreover $\operatorname{Re}\gamma(q, p) \in \{-1, 0, +1\}$ by the real/imaginary classification of $\gamma(q,p)$. Thus the LHS is an integer $M \in \mathbb{Z}$:
   $$M = 2^n (2^n - 2)\, c_q.$$
4. Squaring and substituting $c_q^2 = 2^{-n}$ and $n = 2k + 1$ gives
   $$M^2 = 2^n (2^n - 2)^2 = 2\bigl(2^k (2^n - 2)\bigr)^2.$$
5. Since $n \ge 3$, $b := 2^k(2^n - 2) > 0$. By elementary infinite descent (`int_sq_ne_two_mul_sq`: $a^2 = 2 b^2 \implies 2 \mid a \implies 2 \mid b \implies (a/2)^2 = 2(b/2)^2$), $M^2 = 2 b^2$ forces $b = 0$, contradiction. *(Notice why $n = 1$ escapes: $2^1 - 2 = 0$, allowing $|T\rangle$!)* $\blacksquare$

*Structural remark.* Since any Pauli-covariant MUB fiducial is two-valued on $\mathcal{P}_n \setminus \{I\}$ (Lemma 3.1), Theorem 3 already implies Theorem 2 directly for all odd $n \ge 3$. The odd-$n$ Alltop argument in Section 4 (`no_alltop_odd`) is still required to prove Theorem 1 (Alltop non-existence) and Corollary 1 (strict Gowers $U^3$ lower bound) for odd $n \ge 3$.

---

## 3. Matrix-Free Reduction: Pauli-MUB Fiducial $\implies$ Alltop Function (Theorem 2 $\Leftarrow$ Theorem 1)

Suppose $\psi$ is an $n$-qubit Pauli-covariant MUB fiducial with partition map $\pi : \mathbb{F}_2^{2n} \to \{0, \dots, 2^n - 1\}$.

### Lemma 3.1 (Lagrangian Zero Subgroup, `mub_zero_lagrangian`)
Define $H := \{p \in \mathbb{F}_2^{2n} : \pi(p) = \pi(0)\}$. Then $H$ is an $n$-dimensional Lagrangian subspace of $(\mathbb{F}_2^{2n}, \omega)$, i.e., $\dim_{\mathbb{F}_2} H = n$ and $H^\perp = H$, with $\langle\psi|P_p|\psi\rangle = 0$ for all $p \in H \setminus \{0\}$ and $|\langle\psi|P_p|\psi\rangle|^2 = 2^{-n}$ for all $p \notin H$.

*Proof.*
1. For any $p \in \mathbb{F}_2^{2n}$, $\pi(p) = \pi(0) \iff (p = 0 \text{ or } \langle\psi|P_p|\psi\rangle = 0)$, since $\pi(p) \neq \pi(0) \implies |\langle\psi|P_p|\psi\rangle|^2 = 2^{-n} > 0$.
2. Clearly $0 \in H$. If $p, q \in H$: if $p = q$ then $p \oplus q = 0 \in H$; if $p \neq q$ then $0 = \langle P_p\psi | P_q\psi\rangle = \gamma(p,q)\langle\psi|P_{p\oplus q}|\psi\rangle$, and since $|\gamma(p,q)| = 1$ we get $\langle\psi|P_{p\oplus q}|\psi\rangle = 0$, so $p \oplus q \in H$. Hence $H \le \mathbb{F}_2^{2n}$ is a linear subspace.
3. By Parseval (Lemma 2.1(2)), $2^n = \sum_p |\langle\psi|P_p|\psi\rangle|^2 = 1 + (4^n - |H|)\cdot 2^{-n}$, giving $|H| = 2^n$, hence $\dim_{\mathbb{F}_2} H = n$.
4. Summing Lemma 2.1(3) over $q \in H$ and using character orthogonality $\sum_{q \in H} (-1)^{\omega(p, q)} = |H|\mathbf{1}_{p \in H^\perp} = 2^n \mathbf{1}_{p \in H^\perp}$ (`sum_sympSign_submodule`) gives:
   $$2^n \sum_{p \in H^\perp} \langle\psi|P_p|\psi\rangle^2 = 2^n \sum_{q \in H} \langle\psi|P_q|\psi\rangle^2 = 2^n \cdot 1.$$
   Dividing by $2^n$ and peeling off $p = 0$ yields $\sum_{p \in H^\perp \setminus \{0\}} \langle\psi|P_p|\psi\rangle^2 = 0$. Since each summand is $\ge 0$, every $p \in H^\perp \setminus \{0\}$ has $\langle\psi|P_p|\psi\rangle = 0$, so $H^\perp \subseteq H$.
5. By rank-nullity on $p \mapsto (h \mapsto \omega(p, h)) \in H^*$ (`finrank_sympOrth_ge`), $\dim H^\perp \ge 2n - \dim H = n = \dim H$. Combined with $H^\perp \subseteq H$, this forces $H^\perp = H$.

*Remark on all fibers of $\pi$.* Although the rest of the proof only uses $|H| = 2^n$, one also has $\pi(p) = \pi(q) \iff p \oplus q \in H$ for all $p, q \in \mathbb{F}_2^{2n}$: if $\pi(p) = \pi(q)$ and $p \neq q$, then $0 = \langle P_p\psi | P_q\psi\rangle = \gamma(p,q)\langle\psi|P_{p\oplus q}|\psi\rangle$, so $p \oplus q \in H$; conversely, if $p \oplus q \in H \setminus \{0\}$, then $|\langle P_p\psi|P_q\psi\rangle|^2 = |\langle\psi|P_{p\oplus q}|\psi\rangle|^2 = 0 \neq 2^{-n}$, forcing $\pi(p) = \pi(q)$. Thus the fibers of $\pi$ are precisely the $2^n$ cosets $p \oplus H$, each of size $|H| = 2^n$. $\square$

### Lemma 3.2 (Explicit Symplectic Basis, `exists_symplectic_basis`)
Let $f_1, \dots, f_n$ be an $\mathbb{F}_2$-basis of the Lagrangian subspace $H$. Then there exist $e_1, \dots, e_n \in \mathbb{F}_2^{2n}$ such that $\omega(f_i, f_j) = 0$, $\omega(e_i, e_j) = 0$, and $\omega(e_i, f_j) = \delta_{ij}$ for all $i, j$.

*Proof.*
Consider $L : \mathbb{F}_2^{2n} \to \mathbb{F}_2^n$, $L(v)_j := \omega(v, f_j)$. Its kernel is $H^\perp = H$ (dimension $n$), so $\dim(\operatorname{im} L) = 2n - n = n$, hence $L$ is surjective. Pick $e_{0, i}$ with $L(e_{0,i}) = \delta_i$, i.e., $\omega(e_{0,i}, f_j) = \delta_{ij}$. Define explicitly (without induction):
$$e_i := e_{0, i} + \sum_{j < i} \omega(e_{0, i}, e_{0, j})\, f_j.$$
Since $\omega(f_j, f_k) = 0$, we immediately have $\omega(e_i, f_k) = \omega(e_{0,i}, f_k) = \delta_{ik}$. For $k < i$:
$$\omega(e_i, e_k) = \omega(e_{0,i}, e_{0,k}) + \sum_{j < i} \omega(e_{0,i}, e_{0,j})\,\underbrace{\omega(f_j, e_{0,k})}_{\delta_{jk}} + \sum_{\ell < k} \omega(e_{0,k}, e_{0,\ell})\,\underbrace{\omega(e_{0,i}, f_\ell)}_{0 \text{ since } \ell < k < i} = \omega(e_{0,i}, e_{0,k}) + \omega(e_{0,i}, e_{0,k}) = 0.$$
Symmetry and $\omega(e_i, e_i) = 0$ give $\omega(e_i, e_k) = 0$ for all $i, k$. $\square$

### Lemma 3.3 (Joint $+1$ Eigenstate and Orthonormal Basis, `exists_joint_eigenstate`, `no_pauli_mub_fiducial`)
Let $F_j := P_{f_j}$ and $E_i := P_{e_i}$.
1. Define the iterated projector $\Pi := \prod_{j=1}^n \frac{I + F_j}{2} = 2^{-n} \sum_{u \in \mathbb{F}_2^n} F^u$, where $F^u := \prod_{j: u_j = 1} F_j$. Since the $F_j$ are commuting involutions, $F_j \Pi = \Pi$ for every $j$.
2. Each $F^u$ is a unit phase times $P_{\sum_j u_j f_j}$. The computational-basis trace of $P_p$ is $\sum_{x \in \mathbb{F}_2^n} \langle \delta_x | P_p \delta_x \rangle = 2^n \mathbf{1}_{p = 0}$ (`trace_pauliApply`). Because $f_1, \dots, f_n$ are linearly independent, $\sum_j u_j f_j = 0 \iff u = 0$, so
   $$\sum_{x \in \mathbb{F}_2^n} \langle \delta_x | \Pi \delta_x \rangle = 2^{-n} \cdot 2^n = 1 \neq 0.$$
   Hence $\Pi \delta_{x_0} \neq 0$ for some $x_0$. Normalizing $v_0 := \Pi \delta_{x_0} / \|\Pi \delta_{x_0}\|$ yields a unit vector with $F_j v_0 = v_0$ for all $j$.
3. For each $x \in \mathbb{F}_2^n$, define $E^x := \prod_{i: x_i = 1} E_i$ and $v_x := E^x v_0$.
   - Since $\omega(f_j, e_i) = \delta_{ij}$, $F_j E_i = (-1)^{\delta_{ij}} E_i F_j$, so $F_j v_x = (-1)^{x_j} v_x$, hence $F^b v_x = (-1)^{b\cdot x} v_x$ for all $b \in \mathbb{F}_2^n$.
   - Since all $E_i$ pairwise commute and satisfy $E_i^2 = I$, $E^a E^x = E^{x \oplus a}$ with **no phase factor at all** (`applyProd_applyProd`), so $E^a v_x = v_{x \oplus a}$.
   - Each $E^x$ is unitary, so $\|v_x\| = \|v_0\| = 1$; for $x \neq y$, picking $j$ with $x_j \neq y_j$ gives $\langle v_x | v_y \rangle = \langle F_j v_x | F_j v_y \rangle = -\langle v_x | v_y \rangle \implies \langle v_x | v_y \rangle = 0$. Thus $\{v_x\}_{x \in \mathbb{F}_2^n}$ is an orthonormal basis of $\mathbb{C}^{\mathbb{F}_2^n}$.
4. Set $\alpha(x) := \langle v_x | \psi \rangle$, so $\psi = \sum_{x \in \mathbb{F}_2^n} \alpha(x)\, v_x$. Applying $F^b E^a$ term by term and re-indexing $y = x \oplus a$ gives
   $$F^b E^a \psi = \sum_{x \in \mathbb{F}_2^n} \alpha(x)\, F^b v_{x\oplus a} = \sum_{x \in \mathbb{F}_2^n} (-1)^{b\cdot(x\oplus a)}\,\alpha(x)\, v_{x\oplus a} = \sum_{y \in \mathbb{F}_2^n} (-1)^{b\cdot y}\,\alpha(y\oplus a)\, v_y.$$
   Taking the inner product with $\psi = \sum_y \alpha(y) v_y$ (by orthonormality of $\{v_y\}$) yields
   $$c_{a,b}\,\langle \psi | P_{p(a,b)} | \psi \rangle = \langle \psi | F^b E^a \psi \rangle = \sum_{y \in \mathbb{F}_2^n} (-1)^{b\cdot y}\,\overline{\alpha(y)}\,\alpha(y \oplus a),$$
   where $|c_{a,b}| = 1$ and $p(a,b) := \sum_i a_i e_i + \sum_j b_j f_j$.
5. Notice $\omega(p(a,b), f_k) = a_k$, so $p(a,b) \in H = H^\perp \iff a = 0$.
   - Setting $a = 0$: for $b = 0$ the sum is $\sum_x |\alpha(x)|^2 = 1$; for $b \neq 0$, $p(0, b) \in H \setminus \{0\}$ gives $0$. By WHT inversion, $|\alpha(x)|^2 = 2^{-n}$ for all $x$.
   - Define $\phi(x) := 2^{n/2}\alpha(x)$. Then $|\phi(x)| = 1$ for all $x$. For any $a \neq 0$ and any $b \in \mathbb{F}_2^n$, $p(a,b) \notin H$, so $|\langle\psi|P_{p(a,b)}|\psi\rangle|^2 = 2^{-n}$, whence
     $$\left|\sum_{x \in \mathbb{F}_2^n} (-1)^{b\cdot x}\,\overline{\phi(x)}\,\phi(x \oplus a)\right|^2 = (2^n)^2 \cdot |c_{a,b}|^2 \cdot 2^{-n} = 2^n.$$
   Thus $\phi$ is an Alltop function on $\mathbb{F}_2^n$. Applying Theorem 1 (`no_alltop_f2`) for $n \ge 3$ gives a contradiction, proving Theorem 2. $\blacksquare$

---

## 4. Quantization of Alltop Functions and Odd-$n$ Non-Existence

### Lemma 4.1 (Elementary Norm-Power-of-Two Descent, `GaussianInt.lean`)
For $m, \ell \in \mathbb{Z}$ and $j \ge 0$:
1. (`sq_add_sq_eq_pow_two_even`) $m^2 + \ell^2 = 2^{2j} \implies (m, \ell) \in \{(\pm 2^j, 0), (0, \pm 2^j)\}$.
2. (`sq_add_sq_eq_pow_two_odd`) $m^2 + \ell^2 = 2^{2j+1} \implies m \in \{\pm 2^j\}$ and $\ell \in \{\pm 2^j\}$.

*Proof.* Both follow immediately by induction on $j$, since $m^2 + \ell^2 \equiv 0 \pmod 4 \implies 2 \mid m$ and $2 \mid \ell$ (`even_of_four_dvd_sq_add_sq`), dividing out $4$ to reduce $j \to j - 1$, with base cases $m^2 + \ell^2 = 1$ and $m^2 + \ell^2 = 2$. $\square$

### Lemma 4.2 (Alltop Quantization, `alltop_quantization`)
Let $n \ge 2$ and let $\phi : \mathbb{F}_2^n \to U(1)$ be an Alltop function. For $a \neq 0$, define $g_a(x) := \overline{\phi(x)}\phi(x \oplus a) = r_a(x) + i t_a(x) \in U(1)$. Then for all $a \neq 0$ and $x \in \mathbb{F}_2^n$, there exist $m, \ell \in \mathbb{Z}$ with
$$2^n r_a(x) = 2 m \sqrt{2^n}, \qquad 2^n t_a(x) = 2 \ell \sqrt{2^n}, \qquad m^2 + \ell^2 = 2^{n-2}.$$

*Proof.*
Since $g_a(x \oplus a) = \overline{g_a(x)}$, we have $r_a(x \oplus a) = r_a(x)$ and $t_a(x \oplus a) = -t_a(x)$. Re-indexing $x \mapsto x \oplus a$ in the WHT $\widehat{g_a}(b) = \sum_x (-1)^{b\cdot x} g_a(x)$ (`alltop_wht_re_im`):
- When $a \cdot b = 0$: $\widehat{t_a}(b) = -\widehat{t_a}(b) = 0$, so $\widehat{r_a}(b)^2 = 2^n$, i.e., $\widehat{r_a}(b) = \sigma_r(a, b)\sqrt{2^n}$ with $\sigma_r(a,b) \in \{\pm 1\}$.
- When $a \cdot b = 1$: $\widehat{r_a}(b) = -\widehat{r_a}(b) = 0$, so $\widehat{t_a}(b)^2 = 2^n$, i.e., $\widehat{t_a}(b) = \sigma_t(a, b)\sqrt{2^n}$ with $\sigma_t(a,b) \in \{\pm 1\}$.

By WHT inversion (`wht_inversion`):
$$2^n r_a(x) = \left(\sum_{b : a\cdot b = 0} (-1)^{b\cdot x}\sigma_r(a,b)\right)\sqrt{2^n}, \qquad 2^n t_a(x) = \left(\sum_{b : a\cdot b = 1} (-1)^{b\cdot x}\sigma_t(a,b)\right)\sqrt{2^n}.$$
Because $n \ge 2$ and $a \neq 0$, both sets $\{b : a\cdot b = 0\}$ and $\{b : a\cdot b = 1\}$ have even cardinality $2^{n-1}$. A sum of an even number of $\pm 1$'s is even (`sum_signs_parity`), so the parenthesized sums equal $2m$ and $2\ell$ for integers $m, \ell \in \mathbb{Z}$. Finally, $r_a(x)^2 + t_a(x)^2 = |g_a(x)|^2 = 1$ gives $4(m^2 + \ell^2)\cdot 2^n = 4^n \implies m^2 + \ell^2 = 2^{n-2}$. $\square$

### Proof of Theorem 1 for Odd $n = 2k + 1 \ge 3$ (`no_alltop_odd`)
By Lemmas 4.1(2) and 4.2, $m^2 + \ell^2 = 2^{2(k-1)+1}$ forces $m, \ell \in \{\pm 2^{k-1}\}$, hence $r_a(x)^2 = t_a(x)^2 = 1/2$ for every $a \neq 0$ and every $x$. Pick $a = e_1$, $b = e_2$ (distinct nonzero basis vectors, since $n \ge 3$). They satisfy the triangle identity $g_a(0)\, g_{a\oplus b}(a) = g_b(0)$. Writing $g_a(0) = x_1 + i y_1$ and $g_{a\oplus b}(a) = x_2 + i y_2$, we have
$$\operatorname{Re}(g_b(0))\,\operatorname{Im}(g_b(0)) = (x_1 x_2 - y_1 y_2)(x_1 y_2 + y_1 x_2) = x_1 y_1 (x_2^2 - y_2^2) + x_2 y_2 (x_1^2 - y_1^2) = 0,$$
since $x_1^2 = y_1^2 = x_2^2 = y_2^2 = 1/2$. Yet $\operatorname{Re}(g_b(0))^2 \operatorname{Im}(g_b(0))^2 = 1/4 \neq 0$, contradiction. $\blacksquare$

---

## 5. Universal 2-Adic Subspace Induction in $\mathbb{Z}[i]$ (All Even $n = 2k \ge 4$)

Let $n = 2k$ with $k \ge 2$, and suppose $\phi : \mathbb{F}_2^{2k} \to U(1)$ is an Alltop function.

### Step 1: Reduction to $\mathbb{Z}[i]$ and Parity Alignment (`no_alltop_even`)
1. Replacing $\phi$ by $\phi_0(x) := \overline{\phi(0)}\phi(x)$ preserves `IsAlltop` (`isAlltop_smul`) and normalizes $\phi_0(0) = 1$.
2. By Lemmas 4.1(1) and 4.2, $m^2 + \ell^2 = 2^{2(k-1)}$ forces $g_a(x) \in \{+1, -1, +i, -i\}$ for all $a \neq 0, x$. Since $\phi_0(x) = g_x(0)$ for $x \neq 0$, $\phi_0$ lifts to a function $\psi : \mathbb{F}_2^{2k} \to \{+1, -1, +i, -i\} \subset \mathbb{Z}[i]$.
3. For $\hat{g}_a(b) := \sum_x (-1)^{b\cdot x}\overline{\psi(x)}\psi(x\oplus a) \in \mathbb{Z}[i]$, we have $\hat{g}_0(b) = 2^{2k}\mathbf{1}_{b=0}$, while for $a \neq 0$:
   $$\hat{g}_a(b) = \begin{cases} \sigma_r(a,b)\, 2^k & (a\cdot b = 0), \\ \sigma_t(a,b)\, 2^k i & (a\cdot b = 1), \end{cases} \qquad \sigma_r(a,b), \sigma_t(a,b) \in \{\pm 1\}.$$
4. Let $z_u := \sum_{x \in \mathbb{F}_2^{2k}} (-1)^{u\cdot x}\psi(x) \in \mathbb{Z}[i]$. Direct expansion gives the **convolution identity**
   $$\overline{z_{u\oplus b}}\, z_u = \sum_{a \in \mathbb{F}_2^{2k}} (-1)^{u\cdot a} \hat{g}_a(b).$$
   At $b = 0$, $|z_u|^2 = 2^k \bigl(2^k + \sum_{a \neq 0} (-1)^{u\cdot a}\sigma_r(a,0)\bigr)$ is divisible by $2^k$. By elementary $(1+i)$-descent (`pow_giPi_dvd_of_pow_two_dvd_norm`: $2 \mid a^2 + b^2 \implies a \equiv b \pmod 2 \implies (1+i) \mid a + bi$ in $\mathbb{Z}[i]$, iterated $k$ times), there exists $w_u \in \mathbb{Z}[i]$ with $z_u = (1+i)^k w_u$. Canceling $|(1+i)^k|^2 = 2^k$ gives:
   - $|w_u|^2 = 2^k + \sum_{a \neq 0}(-1)^{u\cdot a}\sigma_r(a,0)$, which is **odd** (as $2^k$ is even and $2^{2k} - 1$ is odd).
   - For $b \neq 0$:
     $$\overline{w_{u\oplus b}}\, w_u = \sum_{\substack{a\neq 0 \\ a\cdot b = 0}} (-1)^{u\cdot a}\sigma_r(a,b) \;+\; i \sum_{a\cdot b = 1} (-1)^{u\cdot a}\sigma_t(a,b).$$
5. For any $u \neq v$, setting $b = u \oplus v \neq 0$ shows $\operatorname{Re}(\overline{w_v} w_u) = \operatorname{Re}(w_v)\operatorname{Re}(w_u) + \operatorname{Im}(w_v)\operatorname{Im}(w_u)$ is a sum of $2^{2k-1} - 1$ (odd) signs, hence odd. Together with odd $|w_u|^2$ and odd $|w_v|^2$, mod-2 arithmetic forces $\operatorname{Re}(w_u) \equiv \operatorname{Re}(w_v) \pmod 2$ for all $u, v$.
6. Choose $u_{\mathrm{rot}} \in \{1, -i\}$ (`1` if $\operatorname{Re}(w_0)$ is odd, `-i` if even) and set $\psi' := u_{\mathrm{rot}}\psi$, $w' := u_{\mathrm{rot}} w$. Then $\psi'(x) \in \{\pm 1, \pm i\}$ and every $w'_u$ has odd real part and even imaginary part, so
   $$w'_u = 1 + 2\eta_u, \qquad \eta_u \in \mathbb{Z}[i].$$

### Step 2: Subspace Correlation Congruences $(\star_r)$ for $1 \le r \le 2k - 2$
Let $1 \le r \le 2k - 2$, let $U \le \mathbb{F}_2^{2k}$ be an $r$-dimensional linear subspace, $v_0 \in \mathbb{F}_2^{2k}$, and $b \in \mathbb{F}_2^{2k}$. Since $\dim U^\perp \ge 2k - r \ge 2$ (`finrank_orth_ge`):
- For $b = 0$: $|U^\perp \setminus \{0\}| = 2^{\dim U^\perp} - 1$ is odd, and $k \ge 1$.
- For $b \neq 0$: $\dim(U^\perp \cap b^\perp) \ge \dim U^\perp - 1 \ge 1$, so $|(U^\perp \cap b^\perp) \setminus \{0\}| = 2^{\dim(U^\perp \cap b^\perp)} - 1$ is **odd** (`odd_card_nonzero_dot_zero`), while $|\{a \in U^\perp : a \cdot b = 1\}| \in \{0, 2^{\dim U^\perp - 1}\}$ is **even** (`even_card_dot_one`).

Summing $\overline{w_{v_0 + u + b}}\, w_{v_0 + u}$ over $u \in U$ and applying affine character orthogonality $\sum_{u \in U} (-1)^{(v_0 + u)\cdot a} = 2^r (-1)^{v_0 \cdot a}\mathbf{1}_{a \in U^\perp}$ (`sum_chi_affine`) shows that $\sum_{u \in U} \overline{w_{v_0 + u + b}}\, w_{v_0 + u}$ has the form $2^r(\text{odd} + i\cdot\text{even}) \equiv 2^r \pmod{2^{r+1}}$ in $\mathbb{Z}[i]$. Taking complex conjugates preserves this congruence (since $\overline{2^r(\text{odd} + i\cdot\text{even})} = 2^r(\text{odd} - i\cdot\text{even}) \equiv 2^r \pmod{2^{r+1}}$), and multiplying by $\overline{u_{\mathrm{rot}}} u_{\mathrm{rot}} = 1$ gives $\overline{w'_x}\, w'_y = \overline{w_x}\, w_y$, hence
$$\sum_{u \in U} \overline{w'_{v_0 + u}}\, w'_{v_0 + u + b} \equiv 2^r \pmod{2^{r+1}} \quad \text{in } \mathbb{Z}[i].$$
Substituting $w'_u = 1 + 2\eta_u$, subtracting $2^r$, and dividing by $2$ gives the **subspace correlation congruence** (`CorrCongr η r`):
$$(\star_r): \qquad 2^r \;\Big|\; \sum_{u \in U} \Bigl(\overline{\eta_{v_0+u}} + \eta_{v_0+u+b} + 2\,\overline{\eta_{v_0+u}}\,\eta_{v_0+u+b}\Bigr) \quad \text{in } \mathbb{Z}[i].$$

### Step 3: 2-Adic Subspace Induction Theorem (`SubspaceInduction.lean`)

Define the inductive predicate `SubspaceVal η m`: for every $1 \le r \le m$, every $r$-dimensional subspace $U \le \mathbb{F}_2^n$, and every $v_0 \in \mathbb{F}_2^n$,
$$(IH_m): \qquad 2^{r-1} \;\Big|\; \sum_{u \in U} \eta(v_0 + u) \quad \text{in } \mathbb{Z}[i].$$

**Theorem 5.1 (`subspaceVal_of_corrCongr`):** If $\eta : \mathbb{F}_2^n \to \mathbb{Z}[i]$ satisfies $(\star_r)$ for all $1 \le r \le M$, then `SubspaceVal η (M + 1)` holds.

*Proof by induction on $m = 1, \dots, M$:*
- **Base ($m = 1$):** $2^{1-1} = 1$ divides every element of $\mathbb{Z}[i]$.
- **Step ($m \to m + 1$, $1 \le m \le M$, `subspaceVal_step`):** Let $W \le \mathbb{F}_2^n$ have dimension $m + 1$ and $w_0 \in \mathbb{F}_2^n$. Pick a basis $b_0, \dots, b_m$ of $W$, pull back $\eta$ along $h(x) := \eta\bigl(w_0 + \sum_{i=0}^m x_i b_i\bigr)$ to $\mathbb{F}_2^{m+1}$ (`subspaceVal_pullback`), and split $\mathbb{F}_2^{m+1}$ into the two $m$-dimensional halves $f(u) := h(u, 0)$ and $h(u, 1) = f(u) + \delta(u)$ for $u \in \mathbb{F}_2^m$, where $\delta(u) := h(u, 1) - h(u, 0)$.

  1. **Exact $\mathbb{Z}[i]$-Möbius expansion (`mobius_inversion`):** Any $g : \mathbb{F}_2^m \to \mathbb{Z}[i]$ expands uniquely as
     $$g(u) = \sum_{S \subseteq [m]} c_S(g)\, u^S, \qquad c_S(g) := \sum_{\operatorname{supp}(v) \subseteq S} (-1)^{|S| - |v|}\, g(v),$$
     where $u^S := \prod_{i \in S} u_i \in \{0, 1\}$.
  2. **2-Adic valuation of $c_S(f)$ (`pow_two_dvd_mobiusCoeff`):** For $|S| = r \ge 1$: if $r = 1$ then $2^0 = 1 \mid c_S(f)$; if $r \ge 2$ then writing $C_S := \{v : \operatorname{supp}(v) \subseteq S\}$ (dim $r \le m$) and $H_S := \{v \in C_S : \sum_{i \in S} v_i = 0\}$ (dim $r - 1$), we have the exact identity (`mobiusCoeff_eq_subspaces`):
     $$c_S(f) = (-1)^r \left(2 \sum_{v \in H_S} f(v) - \sum_{v \in C_S} f(v)\right).$$
     By $(IH_m)$, $2^{r-2} \mid \sum_{H_S} f$ and $2^{r-1} \mid \sum_{C_S} f$, hence **$2^{r-1} \mid c_S(f)$ for all $|S| \ge 1$**.
  3. **Sharper 2-adic valuation of $c_T(\delta)$ (`pow_two_dvd_mobiusCoeff_diff`):** For $|T| = r \ge 1$:
     - If $r = m$: because $(IH_m)$ holds for *every* affine subspace of dimension $\le m$, the pullback of $h(\cdot, 1)$ onto $\mathbb{F}_2^m$ also satisfies $(IH_m)$, so (2) applies equally to both $h(\cdot, 1)$ and $f = h(\cdot, 0)$. Hence $c_T(\delta) = c_T(h(\cdot, 1)) - c_T(h(\cdot, 0))$ is divisible by $2^{m-1}$.
     - If $1 \le r \le m - 1$: let $\widetilde{C}_T := \{w \in \mathbb{F}_2^{m+1} : \forall i \notin T,\, w_i = 0\}$ (dim $r + 1 \le m$) and $D_T := \{w \in \widetilde{C}_T : \sum_{i \in T} w_i + w_m = 0\}$ (dim $r \le m - 1$). Then (`mobiusCoeff_diff_eq_subspaces`):
       $$c_T(\delta) = (-1)^r \left(\sum_{w \in \widetilde{C}_T} h(w) - 2 \sum_{w \in D_T} h(w)\right).$$
       By $(IH_m)$ on $h$, $2^r \mid \sum_{\widetilde{C}_T} h$ and $2^{r-1} \mid \sum_{D_T} h$, hence **$2^r \mid c_T(\delta)$** (an extra factor of $2$!).
  4. **Product-difference valuation (`pow_two_dvd_product_diff`):** Expanding $f$ and $\delta$ in the Möbius basis and summing $u^S u^T = u^{S \cup T}$ over $u \in \mathbb{F}_2^m$:
     $$\sum_{u \in \mathbb{F}_2^m} \overline{f(u)}\,\delta(u) = \sum_{S, T \subseteq [m]} \overline{c_S(f)}\, c_T(\delta)\, 2^{m - |S \cup T|}.$$
     Every term has $2$-adic valuation at least $m - 1$:
     - If $T = \emptyset$ and $S = \emptyset$: the factor $2^{m - 0} = 2^m$ already has valuation $m \ge m - 1$.
     - If $T = \emptyset$ and $|S| \ge 1$: $v_2(c_S(f)) + (m - |S|) \ge (|S| - 1) + (m - |S|) = m - 1$.
     - If $1 \le |T| \le m - 1$: $v_2(c_T(\delta)) \ge |T|$; if $S = \emptyset$ then $|T| + (m - |T|) = m$; if $|S| \ge 1$ then $(|S| - 1) + |T| + (m - |S \cup T|) \ge m - 1$ since $|S| + |T| \ge |S \cup T|$.
     - If $|T| = m$: $|S \cup T| = m$ and $v_2(c_T(\delta)) \ge m - 1$.

     Thus **$2^{m-1} \mid \sum_{u \in \mathbb{F}_2^m} \overline{f(u)}\,\delta(u)$**.
  5. **Cancellation of $|f|^2$ and conclusion:**
     Applying $(\star_m)$ on the $m$-dimensional subspace $V = \operatorname{span}(b_0, \dots, b_{m-1})$ with shift $b = 0$ gives $2^m \mid \sum_V (\overline{\eta} + \eta + 2|\eta|^2)$. Since $2^{m-1} \mid \sum_V \eta$ by $(IH_m)$, $2^m \mid \sum_V (\overline{\eta} + \eta) = 2\operatorname{Re}\sum_V \eta$, whence $2^m \mid 2\sum_V |\eta|^2$, i.e., **$2^{m-1} \mid \sum_{u \in \mathbb{F}_2^m} |f(u)|^2$**.
     Adding (4) gives $2^{m-1} \mid \sum_u \overline{f(u)} h(u, 1)$, so $2^m \mid 2 \sum_u \overline{f(u)} h(u, 1)$.
     Now apply $(\star_m)$ on $V$ with shift $b = b_m$:
     $$2^m \;\Big|\; \sum_{u \in \mathbb{F}_2^m} \bigl(\overline{f(u)} + h(u, 1)\bigr).$$
     - Taking the **real part**: $\operatorname{Re}(\overline{f} + h(\cdot, 1)) = \operatorname{Re}(f) + \operatorname{Re}(h(\cdot, 1))$, so $2^m \mid \sum_{w \in \mathbb{F}_2^{m+1}} \operatorname{Re}(h(w))$.
     - Taking the **imaginary part**: $\operatorname{Im}(\overline{f} + h(\cdot, 1)) = \operatorname{Im}(h(\cdot, 1)) - \operatorname{Im}(f)$, so adding $2\sum_u \operatorname{Im}(f(u))$ (divisible by $2 \cdot 2^{m-1} = 2^m$ by $(IH_m)$) gives $2^m \mid \sum_{w \in \mathbb{F}_2^{m+1}} \operatorname{Im}(h(w))$.

     Hence $2^m \mid \sum_{w \in W} \eta(w_0 + w)$ in $\mathbb{Z}[i]$, completing the induction! $\square$

### Step 4: Final Contradiction for All $k \ge 2$ (`pow_two_dvd_wht_sub_of_subspaceVal`, `no_alltop_even`)
Applying Theorem 5.1 with $M = 2k - 2$ gives `SubspaceVal η (2k - 1)`.
1. **Exact WHT-to-subcube identity (`wht_eq_subcube_sum`):** Using $(-1)^{u\cdot x} = \prod_{i=1}^{2k} (1 - 2 u_i x_i) = \sum_{T \subseteq [2k]} (-2)^{|T|} x^T u^T$, for any $g : \mathbb{F}_2^{2k} \to \mathbb{Z}[i]$:
   $$\sum_{u \in \mathbb{F}_2^{2k}} (-1)^{u\cdot x} g(u) = \sum_{T \subseteq [2k]} (-2)^{|T|} x^T \sum_{u : T \subseteq \operatorname{supp}(u)} g(u).$$
2. Apply this to $1 + 2\eta$: the $T = \emptyset$ term is independent of $x$, so in the difference between $x$ and $y$, only $T \neq \emptyset$ remains:
   - For $1 \le |T| \le 2k - 1$: the subcube $V_T = \{u : T \subseteq \operatorname{supp}(u)\}$ is a $(2k - |T|)$-dimensional affine subspace, so by $(IH_{2k-1})$, $2^{2k - |T| - 1} \mid \sum_{V_T} \eta$. Multiplying by $2 \cdot (-2)^{|T|}$ gives divisibility by $2 \cdot 2^{|T|} \cdot 2^{2k - |T| - 1} = 2^{2k}$!
   - For $|T| = 2k$: $2 \cdot (-2)^{2k}$ is trivially divisible by $2^{2k}$!
   - Meanwhile $\sum_u (-1)^{u\cdot x} \cdot 1 = 2^{2k}\mathbf{1}_{x=0} \equiv 0 \pmod{2^{2k}}$.

   Therefore, for all $x, y \in \mathbb{F}_2^{2k}$:
   $$2^{2k} \;\Big|\; \sum_{u \in \mathbb{F}_2^{2k}} (-1)^{u\cdot x}(1 + 2\eta_u) - \sum_{u \in \mathbb{F}_2^{2k}} (-1)^{u\cdot y}(1 + 2\eta_u).$$
3. By WHT inversion on $\psi$ and the exact identity $2^{2k} = (-1)^k (1+i)^{4k}$ (`gi_two_pow_even`), dividing $(1+i)^k \sum_u (-1)^{u\cdot x} w'_u = 2^{2k}\psi'(x)$ by $(1+i)^k$ yields
   $$\sum_{u \in \mathbb{F}_2^{2k}} (-1)^{u\cdot x}(1 + 2\eta_u) = (-1)^k (1+i)^{3k} \psi'(x).$$
   Hence $2^{2k} \mid (-1)^k (1+i)^{3k}\bigl(\psi'(x) - \psi'(y)\bigr)$ in $\mathbb{Z}[i]$.
4. Taking $\mathbb{Z}[i]$-norms gives $2^{4k} \mid 2^{3k}|\psi'(x) - \psi'(y)|^2$, i.e., **$2^k \mid |\psi'(x) - \psi'(y)|^2$**.
5. Since $k \ge 2$, $4 \mid |\psi'(x) - \psi'(y)|^2$. Yet $\psi'(x), \psi'(0) \in \{+1, -1, +i, -i\}$, whose pairwise squared distances lie in $\{0, 2, 4\}$, with distance $2$ occurring precisely when one is in $\{\pm 1\}$ and the other in $\{\pm i\}$. Thus $4 \mid |\psi'(x) - \psi'(0)|^2$ forces $\psi'(x) = \pm \psi'(0)$ for **all** $x \in \mathbb{F}_2^{2k}$!
6. Consequently, for $a_0 := e_1 \neq 0$, every product $\overline{\psi(x)}\psi(x \oplus a_0) = \overline{\psi'(x)}\psi'(x \oplus a_0) \in \{+1, -1\}$ is purely real, so $\operatorname{Im}(\hat{g}_{a_0}(a_0)) = 0$. Yet $a_0 \cdot a_0 = 1$ requires $\operatorname{Im}(\hat{g}_{a_0}(a_0)) = \pm 2^k \neq 0$, **contradiction!** $\blacksquare$

*(Remark on $n = 2$, $k = 1$: Here $2k - 2 = 0$, so there are zero $(\star_r)$ steps, and $2^k = 2$ does divide $|\psi'(x) - \psi'(0)|^2 = 2$, allowing $\phi_2 = (1, 1, 1, i)$ to exist!)*

---

## 6. Strict Gowers $U^3$ Bound, $n = 2$ Sharpness, and the $\mathrm{GL}(n,\mathbb{F}_2)$ Spike Family

### Proof of Corollary 1 (`phasePauliMoment4_gt_mub`)
For any unimodular $\phi : \mathbb{F}_2^n \to U(1)$, let $c_a(b) := |\widehat{g_a}(b)|^2$.
- At $a = 0$, $g_0 \equiv 1$, so $c_0(b) = 4^n \mathbf{1}_{b=0}$, contributing $1$ to `phasePauliMoment4 n φ`.
- For every $a \in \mathbb{F}_2^n$, Parseval (`sum_normSq_wht_multDeriv`) gives $\sum_b c_a(b) = 4^n$, hence the exact sum-of-squares identity
  $$\sum_{b \in \mathbb{F}_2^n} \left(\frac{c_a(b)}{4^n}\right)^2 = \frac{1}{2^n} + \frac{1}{4^{2n}}\sum_{b \in \mathbb{F}_2^n} \bigl(c_a(b) - 2^n\bigr)^2.$$
- Summing over all $2^n - 1$ nonzero $a$ yields
  $$F_n(\phi) = 2 - \frac{1}{2^n} + \frac{1}{4^{2n}}\sum_{a \neq 0}\sum_{b} \bigl(c_a(b) - 2^n\bigr)^2.$$
- By Theorem 1 (`no_alltop_f2`), for $n \ge 3$ there exists $(a_0, b_0)$ with $a_0 \neq 0$ and $c_{a_0}(b_0) \neq 2^n$, making the sum of squares strictly positive. $\blacksquare$

### The $\mathrm{GL}(n, \mathbb{F}_2)$-Invariant, $(H^{\otimes n} \circ K)$-Symmetric Spike Family (`SpikeFamily.lean`)
For $n \ge 1$ ($d = 2^n$) and real $s$ satisfying $p := 1 - \frac{d-1}{d}s > 0$ and $v^2 := -1 + 4s - \frac{4(d-1)}{d} s^2 \ge 0$, set $\alpha := \sqrt{p}$, $u := 2p - 1$, $v := \sqrt{v^2}$, $\beta := \frac{u + iv}{2\alpha}$, and $|\psi_n(s)\rangle := \alpha|0\rangle + \beta\sum_{x \neq 0}|x\rangle$. Under computational-basis permutations in $\mathrm{GL}(n, \mathbb{F}_2)$ the state is strictly invariant; under $H^{\otimes n}$, direct calculation gives $H^{\otimes n}|\psi_n(s)\rangle = e^{i\theta}|\overline{\psi_n(s)}\rangle$ (i.e., $|\psi_n(s)\rangle$ is invariant up to global phase under the **antiunitary** involution $H^{\otimes n} \circ K$, where $K$ is entrywise complex conjugation, so its Pauli expectation spectrum is symmetric under $(a, b) \leftrightarrow (b, a)$ up to signs on $a \cdot b = 1$). Direct evaluation over the 5 Pauli orbits yields:
- $(a,b) = (0,0)$: $\langle P \rangle = 1$ (count $1$);
- $a = 0, b \neq 0$ or $a \neq 0, b = 0$: $\langle P \rangle = 1 - s$ (count $2(d - 1)$);
- $a \neq 0, b \neq 0, a \cdot b = 0$: $\langle P \rangle = 1 - 2s$ (count $(d - 1)(d/2 - 1)$);
- $a \neq 0, a \cdot b = 1$: $\langle P \rangle = -v$ (count $(d - 1)(d/2)$).

Hence (`pauliMoment4_spikeState`):
$$F_n(|\psi_n(s)\rangle) = 1 + (d - 1)\!\left[2(1 - s)^4 + \left(\frac{d}{2} - 1\right)(1 - 2s)^4 + \frac{d}{2}\left(-1 + 4s - \frac{4(d-1)}{d} s^2\right)^2\right].$$
- At $n = 3, s = 2/3$: $|\langle P\rangle| = 1/3$ for all 63 non-identity Paulis, recovering the **Hoggar SIC** $F_3 = 16/9$ (`hoggar_sic_three`).
- At $n = 4$: the stationarity equation $dF_4/ds = 0$ reduces to the irreducible cubic $453 s^3 - 708 s^2 + 368 s - 64 = 0$ ($s^* \approx 0.6225432$, $F_4 \approx 2.1505201547$). Evaluating at the nearby rational witness $s = 622543/1000000$ formally certifies $F_4(|\psi_4(s)\rangle) < 2.150521$ (`four_qubit_spike_bound`). *(Whether $F_4(s^*)$ is the true global minimum on all of $\mathbb{CP}^{15}$ remains an open numerical observation supported by 2,936/3,000 multi-start Riemannian optimizations.)*
