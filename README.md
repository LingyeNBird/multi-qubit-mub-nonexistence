# Non-Existence of Multi-Qubit Pauli-Covariant MUB Fiducial States and Alltop Phase Functions on $\mathbb{F}_2^n$ ($n \ge 3$)

A self-contained, pure-kernel **Lean 4** formalization (zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only) resolving the multi-qubit Pauli-covariant MUB fiducial problem and the Alltop phase function problem over $\mathbb{F}_2^n$ for **all** $n \ge 3$ (both odd and even).

For the full publication-ready manuscript (compiled PDF + LaTeX source), see **[`paper/main.pdf`](paper/main.pdf)** ([`paper/main.tex`](paper/main.tex)). For a concise Markdown proof mirroring every Lean module and lemma, see **[`PROOF.md`](PROOF.md)**.

---

## Main Results (Machine-Verified in Lean 4)

| Module | Lean Theorem | Result |
|---|---|---|
| [`MultiQubitMUB/Alltop.lean`](MultiQubitMUB/Alltop.lean) | `no_alltop_f2` | **Theorem 1 (All $n \ge 3$):** No unimodular function $\phi : \mathbb{F}_2^n \to U(1)$ has flat Walsh–Hadamard spectra on all nontrivial multiplicative derivatives $g_a(x) = \overline{\phi(x)}\phi(x \oplus a)$. |
| [`MultiQubitMUB/Alltop.lean`](MultiQubitMUB/Alltop.lean) | `exists_alltop_two` | **Sharpness ($n = 2$):** $\phi_2 = (1, 1, 1, i)$ IS an Alltop function on $\mathbb{F}_2^2$. |
| [`MultiQubitMUB/Alltop.lean`](MultiQubitMUB/Alltop.lean) | `phasePauliMoment4_gt_mub` | **Strict Gowers $U^3$ / Phase-State Bound:** For all $n \ge 3$ and every $\phi : \mathbb{F}_2^n \to U(1)$, $2^n \|\phi\|_{U^3(\mathbb{F}_2^n)}^8 > 2 - 2^{-n}$ strictly. |
| [`MultiQubitMUB/PauliGroup.lean`](MultiQubitMUB/PauliGroup.lean) | `no_pauli_two_valued_odd` | **Strong Odd-$n$ Theorem (no basis partition assumed):** For every odd $n = 2k + 1 \ge 3$, no $n$-qubit pure state even satisfies $|\langle\psi|P|\psi\rangle|^2 \in \{0, 2^{-n}\}$ for all $P \neq I$. |
| [`MultiQubitMUB/PauliGroup.lean`](MultiQubitMUB/PauliGroup.lean) | `no_pauli_mub_fiducial` | **Theorem 2 (All $n \ge 3$, unrestricted):** No unit vector $|\psi\rangle \in (\mathbb{C}^2)^{\otimes n}$ generates $2^n$ pairwise mutually unbiased orthonormal bases under the $n$-qubit Pauli group $\mathcal{P}_n$. |
| [`MultiQubitMUB/PauliGroup.lean`](MultiQubitMUB/PauliGroup.lean) | `damski_conjecture_1` | **$\omega_8$-Phase Corollary:** No $\omega_8$-phase state $\psi_x = 2^{-n/2}\omega_8^{m_x}$ generates $2^n$ pairwise MUBs under $\mathcal{P}_n$ for $n \ge 3$ (resolving Conjecture 1 of Damski, Bistroń, Ponterio, Czartowski, and Życzkowski, [arXiv:2603.15550](https://arxiv.org/abs/2603.15550), 2026; `no_pauli_mub_fiducial` removes both the $\omega_8$ and equimodularity assumptions). |
| [`MultiQubitMUB/PauliGroup.lean`](MultiQubitMUB/PauliGroup.lean) | `exists_pauli_mub_fiducial_two` | **Sharpness ($n = 2$):** $|\psi_2\rangle = \frac{1}{2}(1, 1, 1, i)$ generates 4 pairwise MUBs under $\mathcal{P}_2$. |
| [`MultiQubitMUB/SpikeFamily.lean`](MultiQubitMUB/SpikeFamily.lean) | `pauliMoment4_spikeState`, `hoggar_sic_three`, `four_qubit_spike_bound` | Exact closed-form Pauli 4th moment for the $\mathrm{GL}(n,\mathbb{F}_2)$-invariant, antiunitarily $(H^{\otimes n} \circ K)$-symmetric spike+uniform family, recovering the 3-qubit Hoggar SIC ($F_3 = 16/9$) and certifying a 4-qubit unit state with $F_4 < 2.150521$. |

### Physics & Literature Context

1. **Product Weyl–Heisenberg MUBs ([arXiv:2603.15550](https://arxiv.org/abs/2603.15550)):** Damski, Bistroń, Ponterio, Czartowski, and Życzkowski conjectured (Conjecture 1) that no product-WH MUB fiducial vector of the form $\psi_x = 2^{-n/2}\omega_8^{m_x}$ exists for $n > 2$, and further proposed the stronger conjecture that no multi-qubit product-WH MUB fiducial exists at all for $n > 2$ (analogous to Godsil–Roy's theorem for product-WH SICs). Our `IsPauliMubFiducial` characterizes a fiducial generating a complete set of $2^n$ pairwise MUBs under $\mathcal{P}_n$ (adding the computational basis gives $2^n + 1$ MUBs for equatorial states; partial sets of $< 2^n$ bases are not ruled out). `no_pauli_mub_fiducial` proves non-existence in full unrestricted generality for **all** $n \ge 3$.
2. **Multi-Qubit Maximal Magic ([arXiv:2502.17550](https://arxiv.org/abs/2502.17550) / Problem E28):** Liu, Low, and Yin found 480 two-qubit WH-MUB fiducials attaining $F_2 = 7/4$ ($M_2 = \ln(16/7)$) and conjectured that WH-MUB fiducials act as maximal magic states for $n$-qubit systems with $n \neq 1, 3$ (excluding $n = 1, 3$, where product WH-SICs exist). Theorem 2 proves that no product WH-MUB fiducial exists for any $n \ge 3$, ruling out their conjectured WH-MUB maximizers for all $n \ge 4$.
3. **Reproducible Companion Numerical Search ($n = 4$):** In 12,000 independent Haar-random multi-start Riemannian L-BFGS optimizations on $\mathbb{CP}^{15}$ across four independent seeds (separate from the Lean formalization; reproducible via [`scripts/cp15_riemannian_lbfgs.c`](scripts/cp15_riemannian_lbfgs.c), primary seed `20260401` giving 2,935 / 65), 11,754 runs (97.95%) converged to the isolated strict local minimum of the `spikeState` family ($453 s^3 - 708 s^2 + 368 s - 64 = 0$, projected Hessian $\lambda_{\min} \approx 5.96$), giving $F_4 \approx 2.1505201547 > 31/16 = 1.9375$ — equivalently $M_2 \approx 2.006879 < \ln(256/31) \approx 2.111190$ relative to the unreachable WH-MUB value — with identical Pauli spectra matching Table 2 to $< 6.2\times 10^{-8}$. The remaining 246 runs (2.05%) all (`246/246`, verified under Clifford equivalence and projected Hessian) converged to the minority local-minimum sub-region (~11.9% local-min-like vs. ~88.1% saddles across 1,000 random locus samples) of a smooth 3-dimensional bent-support $(16,6,2)$-difference-set family at $F_4 = 20/9 \approx 2.222222$ ($\sum_{x\in S} e^{4i\theta_x} = 0$, 3 zero and 27 positive Hessian eigenvalues), and 200 basin-hopping chains all converged to $F_4(s^*)$ with no run below $F_4(s^*)$. (Note that Corollary 1 proves $F_4 > 31/16$ strictly for phase and Lagrangian-annihilated states, whereas for general states on $\mathbb{CP}^{15}$ the only known analytic lower bound is the Welch/SIC bound $2d/(d+1) = 32/17 \approx 1.882353$; proving global optimality of $F_2 = 7/4$ at $n=2$ and $F_4 \approx 2.150520$ at $n=4$ remains open.)

---

## Repository Structure

```text
.
├── paper/
│   ├── main.tex                    # Complete LaTeX manuscript (AMS style, TikZ/pgfplots)
│   ├── references.bib              # Curated BibTeX bibliography
│   └── main.pdf                    # Compiled publication-ready PDF
├── PROOF.md                        # Concise Markdown proof mirroring Lean modules
├── README.md                       # Project overview and verification guide
├── Audit.lean                      # #print axioms audit on all 10 main theorems
├── MultiQubitMUB.lean              # Root Lean library aggregator
├── MultiQubitMUB/
│   ├── GaussianInt.lean            # Elementary Z[i] norm & (1+i)-divisibility descent (zero UFD)
│   ├── Basic.lean                  # F_2^n, Walsh–Hadamard inversion, subspace character sums
│   ├── SubspaceInduction.lean      # 2-adic affine subspace induction in Z[i] via Mobius inversion
│   ├── Alltop.lean                 # Theorem 1 (all n >= 3), sharpness (n = 2), strict U^3 bound
│   ├── PauliGroup.lean             # Theorem 2 (all n >= 3), strong odd-n Theorem 3, Conjecture 1
│   └── SpikeFamily.lean            # GL(n, F_2)-invariant spike family (Hoggar SIC & n=4 bound)
├── scripts/
│   ├── verify_claims.py            # Independent Python numerical & exact sanity checks
│   └── cp15_riemannian_lbfgs.c     # Reproducible 3,000-start Riemannian L-BFGS on CP^15
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain                  # leanprover/lean4:v4.36.0
└── LICENSE                         # MIT
```

---

## Verification

Requires Lean 4 (`v4.36.0`, managed automatically by `elan` via [`lean-toolchain`](lean-toolchain)) and Mathlib `v4.36.0`.

```bash
# 1. Build the entire Lean 4 library
lake build

# 2. Run the axiom audit (every theorem must use only [propext, Classical.choice, Quot.sound])
lake env lean Audit.lean

# 3. Verify zero sorry, zero native_decide, zero custom axioms
grep -rn "sorry\|native_decide\|axiom " MultiQubitMUB/ MultiQubitMUB.lean

# 4. Run independent Python sanity checks (n=2 witness, n=1..4 spike family)
python3 scripts/verify_claims.py
```
