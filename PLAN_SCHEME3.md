# 方案 3 执行计划：先固化一般 $n$ 基础理论包（路线 1），再新开会话双线攻坚硬仗 A & B（路线 2 + 路线 3）

> **分支：** `explore/asymptotic-theory`（阶段一已入库 `4ff8c18`，当前更新至 Stage 15 战线 2 结题与战线 3 精化方案，对应理论综述 [ASYMPTOTIC_THEORY_NOTES.md](ASYMPTOTIC_THEORY_NOTES.md)）  
> **总原则：** 严格遵守 `idea/12` 五条研究宪章与 15 GB WSL2 低内存编译铁律；绝不退回有限 $n$ 刷分/造证书；绝不修改任何上游 `FourQubit*.lean`、`TwoQubitExactCert.lean`、`AsymptoticContextuality.lean` 已过审定理、`main` 分支或隔壁目录 `/home/admin/projects/e28_multiqubit_magic_main`。

---

## 阶段一（已完成并入库）：路线 1 — 一般 $n$ 基础理论包 Lean 4 形式化

**状态：** ✅ **已完成全量形式化、安全构建与公理审计**
- **新增模块：** [`MultiQubitMUB/AsymptoticBarriers.lean`](MultiQubitMUB/AsymptoticBarriers.lean)（1,298 行，21 条公开定理，零 `sorry`、零 `native_decide`、零 `set_option`、零改动上游任何已过审模块）
- **低内存安全构建：**
  - `lake env lean -M 8192 -j 1 MultiQubitMUB/AsymptoticBarriers.lean`：exit 0，13.2s，0 错误 0 警告；
  - `python3 idea/safe_lake_build.py MultiQubitMUB.AsymptoticBarriers`：exit 0，7.0s，`peak_pgid_rss = 4800.5 MB`（< 8000 MB 上限）；
  - `python3 idea/safe_lake_build.py MultiQubitMUB`：exit 0，3.0s，`peak_pgid_rss = 4506.9 MB`；
  - `lake env lean -M 8192 -j 1 Audit.lean`：**74 / 74** 条定理（53 条既有 + 21 条新增）100% 仅依赖 `[propext, Classical.choice, Quot.sound]`。

**已形式化的 4 组面向一般 $n$ 的无条件定理：**

1. **定理组 1 — 3 行初等全 $n \neq 1, 3$ 多比特 Pauli-SIC 非存在性与严格破 Welch 定理**
   - `pow_two_add_one_ne_sq`、`sqrt_pow_two_add_one_ne_rat`：$\forall n \neq 3,\; 2^n + 1 \neq k^2$ 与 $\sqrt{2^n + 1} \notin \mathbb{Q}$；
   - `signCubeSum_lt_spectral`、`frustPairs_gt_spectral`：$\forall n \ge 2, n \neq 3$，无条件严格不等式 $1 - 2\rho_n(s) < \frac{2\sqrt{2^n + 1}}{2^n + 2}$；
   - `no_pauli_sic_via_cubic_trace`：$\forall n \ge 2, n \neq 3$，经 $\mathrm{Tr}(r_t^3) = 1$ 与 `signCubeSum_lt_spectral` 直接推出 $F_n(|\psi\rangle) > \frac{2\cdot 2^n}{2^n + 1}$。

2. **定理组 2 — 完整定量双向等价定理（补全 `AsymptoticContextuality.lean` 的另一半）**
   - `pauliL1_ge_of_pauliMoment4`、`pauliAlpha_ge_of_pauliMoment4`（$\forall n \ge 1$）：精确线性下界 $\sqrt{\frac{d-1}{d}} - \frac{d+1}{2\sqrt{d(d-1)}}\bigl(F_n(\psi) - \frac{2d}{d+1}\bigr) \le \alpha_n(\psi)$（在 Welch 等式处取到精确等号）；
   - `exists_unit_state_rayleigh_ge_cube`（$\forall n$）：经 Mathlib `Matrix.IsHermitian.spectral_theorem` 证明任意 Hermitian 矩阵存在单位特征态满足 $\mathrm{Re}\,\mathrm{Tr}(A^3) \le \langle\psi|A|\psi\rangle\cdot\|A\|_F^2$；
   - `exists_unit_state_pauliL1_ge_of_signCubeSum`、`exists_unit_state_pauliAlpha_ge_of_frustPairs`（$\forall n \ge 2$）：对 $r_t(\sigma)$ 最高特征态 $|\psi_1\rangle$ 同时给出 Frobenius 逼近 $\|r_t - |\psi_1\rangle\langle\psi_1|\|_F^2 \le 2(1 - \mathrm{Tr}(r_t^3))$ 与**无平方根损失的精确线性下界** $\sqrt{\frac{d-1}{d}}\cdot\frac{d+2}{2\sqrt{d+1}}(1 - 2\rho_n(s)) \le \alpha_n(\psi_1)$（在 $n=3$ Hoggar SIC 处取到精确等号 $\sqrt{7/8}$），与既有 `signCubeSum_ge_of_L1` 组成精确双向等价 $\limsup \alpha_n^* = 1 \Longleftrightarrow \limsup c_n^* = 2$。

3. **定理组 3 — 纯 $c_p^2$（Bell 差分采样 / Delsarte LP）元障碍定理**
   - `qSIC_nonneg`、`sum_qSIC_eq_one`、`sympWHT_qSIC_eq`、`sympWHT_qSIC_pow_nonneg`（$\forall n, k \in \mathbb{N}$）、`qSIC_moment4_eq_welch`：无条件证明假想平坦分布 $q_{\mathrm{SIC}}$ 满足一切高次辛 WHT 非负性与自对偶性并精确达到 Welch 界 $\frac{2d}{d+1}$，锁死所有无符号 / 纯 $c_p^2$ 线性规划路线。

4. **定理组 4 — 高斯整数奇偶同余与稳定子基 IPR 障碍定理**
   - `signMat_diag_odd_int`、`signMat_offdiag_even_re_im`、`signMat_add_id_half_gaussInt`（$\forall n \ge 2$）：无条件证明 $\frac{1}{2}(S(\sigma) + I) \in M_d(\mathbb{Z}[i])$；
   - `compBasisIPR_eq_sum_Z_pauliSq`、`compBasisIPR_eq_welch_of_flat_pauli`、`compBasisIPR_sub_welch_sq_le`（$\forall n$）：证明 $I_2(\psi) = \sum_b c_{0,b}(\psi)^2$ 以及定量分离界 $\bigl(I_2(\psi) - \frac{2d}{d+1}\bigr)^2 \le (d - 1)\bigl(F_n(\psi) - \frac{2d}{d+1}\bigr)$（严格分离 Welch 逼近态 $I_2 \to 2$ 与 `Alltop.lean` 平坦振幅相态 $I_2 = 1$）。

---

## 阶段二：路线 2（已结题）+ 路线 3（主攻中）双线纯理论攻坚

### 战线 2（硬仗 A — 一般 $t = 4m$ 的 $R_{4m}$-理想 Clifford-PPT 理论）
**状态：** ✅ **纯理论攻坚与天花板机理已彻底查明（Stage 15，详见 [`ASYMPTOTIC_THEORY_NOTES.md`](ASYMPTOTIC_THEORY_NOTES.md) Section 3.4）**
- **真实对称群与万能闭式投影（$\forall m \ge 1, \forall 0 \le r \le 2m, \forall d = 2^n$）**：
  - $\dim(L)=1$ 商空间的真实对称群为正交群 $O^\varepsilon(4m - 2, 2)$（二次型 $q_{2r}(x) = \frac{|x_L|-|x_H|}{2} \pmod 2$，$\varepsilon = \mathrm{Arf}(q_{2r}) = (-1)^{m-r}$），打破 Stage 14 的二项分布猜想（$t=8$ 只是 $O^+(6,2)\cong S_8$ 与 $O^-(6,2)\cong W(E_6)$ 的低维巧合；到 $t=12,\tau_6$ 时 $|O^+(10,2)| \approx 98{,}118 \times 12!$）。
  - 由 Witt 定理导出精确上双对角乘法律，直接解出一般 $(4m, 2r)$ 的精确正交投影算子 $Q_{\mathrm{orth}}^{(4m,2r)}(d)$ 与普适稳定子恒等式 $\mathrm{Tr}\bigl(\tau_{2r}(Q_{\mathrm{orth}})|0^n\rangle\langle 0^n|^{\otimes 4m}\bigr) = \frac{1}{d}\frac{\prod_{i=0}^{\nu-1}(d-2^i)}{\prod_{i=1}^\nu(d+2^{4m-3-i})} \ge 0$，一举统一 $t=4$（精确 Welch 界）与 $t=8$ 两条 13 项精确多项式见证。
- **精确 $d^{-2}$ 抵消定理与 $t=12/16$ 相变测量**：
  - 证明 $E_{\mathrm{orth}}/p_0 = d^{-1} + C_2(4m, 2r)\,d^{-2} + O(d^{-3})$，其中指数项 $-2^{t-4}(t-k)k$ 与 $+2^{t-4}(t-k)k$ 精确抵消，留下 $C_2(4m, 2r) = A_0(r=0) - (t-k)k(1 + \frac{1}{2}\binom{t-2}{2})$；在 $t=12$ 为负（$-140, -386, -500$），自 **$t = 4m \ge 16$ 起永久严格为正**（$t=16$ 为 $+6498 \sim +4648$）。
  - $k_{\mathrm{Sym}} \le 2$ 全精确 + $k_{\mathrm{Sym}} \ge 3$ 分层 MC 测得：$t=12, \tau_6$ 击穿 $t=8$ 的 $99.92$ 天花板（排除 $n=7, 8$ 的 $y_H(2^n)$）并在 **$d_0(12, 6) \approx 550\text{–}650 \in (512, 1024)$** 过零（$d=1024$ 处 $+5.63\sigma$，$d=2048$ 处 $+33.66\sigma$）；$d_0(12, 4) \approx 220\text{–}250$；$t=12, \tau_2$ 在 $d \ge 64$ 全正；$t=16, \tau_8$ 连 `EXACT(k<=2)` 也在 $d \approx 7.5 \times 10^4$ 过零（全量 $d_0(16,8) \lesssim 2\times 10^4$）。
- **最终结论（双重本质障碍，已列入死胡同 #8）**：
  1. 增长律为**单指数 $d_0(4m, 2m) = \Theta(2^{4m})$**（由极点尺度 $d + 2^{4m-4}$ 主导，非 $2^{\Theta(m^2)}$ 或 $(2m)!$），击穿 $y_H(2^n)$ 需线性副本数 $t(n) = \Omega(n)$（无法在 $t(n) \ll n$ 完成）；
  2. 裕度按 $p_0 \sim 2^{-4m^2}$ 超指数衰减（$t=12, d=128$ 时已仅 $\sim 10^{-5}$），无法导出常数渐近间隙 $\liminf F_n^* > 2$。

### 战线 3（硬仗 B — 直接攻坚 $\liminf F_n^* > 2$ 或 $\limsup c_n^* < 2$）
**状态：** ⏳ **Stage 15 前置排雷已完成，两条精化纯理论主攻路线就绪（待拍板下一步选择）**
- **Stage 15 新排除的两条子路线（死胡同 #9，切勿重踩）**：
  1. 单 MUB 布尔 WHT 单侧三次/四次矩障碍：$n=7$ ($d=128$) 已直接构造出满足 $Y \ge +0.0277 > 0$ 且 $(\mathbb{E}[Y^2], \mathbb{E}[Y^3], \mathbb{E}[Y^4]) = (2, 5.9197, 24.0693)$ 的单 MUB 布尔函数；
  2. 单稳定子重叠四次矩：$\mathbb{E}_{\mathrm{Stab}}[d^4 |\langle\phi|\psi\rangle|^8] = A(d) + B(d)\,F_n(\psi)$ 中 $B(d) = O(1/d) \to 0$，Welch 处 $m_4 \to 24 > 20$（Hamburger 下界），无 $O(1)$ 间隙。
- **精化后的两条纯理论主攻方向（必须利用多 MUB 耦合 / 全局相位相干）**：
  - **方向 3A（直接攻 $\liminf F_n^* > 2$ — Gowers $U^3$ 相位方盒精确正定分解）**：
    在任意稳定子基下（$p_x = |\psi_x|^2, r_a = (p*p)(a), K(a) = \langle \psi^{\circ 2}|X^a|\psi^{\circ 2}\rangle \in \mathbb{R}, H(a,u) = \sum_x \psi_x \psi_{x\oplus a}^* \psi_{x\oplus u}^* \psi_{x\oplus a\oplus u} \in \mathbb{R}$），精确恒等式
    $$F_n(|\psi\rangle) = d \sum_{a, u} H(a, u)^2 = d^5 \|\psi\|_{U^3(\mathbb{F}_2^n)}^8,$$
    $$F_n(|\psi\rangle) - \frac{2d}{d+1} = \frac{d(d+1)}{d-1}\!\left(r_0 - \frac{2}{d+1}\right)^2 + 2d \sum_{a \neq 0}\!\left(r_a - \frac{1-r_0}{d-1}\right)^2 + d \sum_{a \neq 0} K(a)^2 + d \sum_{\substack{a,u \neq 0 \\ a \neq u}} H(a,u)^2$$
    已验证至 $10^{-15}$ 精度（$n=3$ Hoggar SIC 处 $K \equiv 0, H_{\text{off}} \equiv 0$；实态强迫 $K(a)=r_a \implies F_n \ge 3$）。目标：利用 $\sim d^2$ 个四次相位方程在 $2d-2$ 实自由度上的过约束、导数态 $D_a \psi$ 与全 Clifford 基下 $(U\psi)^{\circ 2}$ 的近 Bent 性，证明 $\forall n \ge 4$ 有 $d\sum_{a\neq 0}K(a)^2 + d\sum_{a\neq u\neq 0}H(a,u)^2 \ge \delta_0 > 0$。
  - **方向 3B（同时攻 $\limsup c_n^* < 2$ 与 $\liminf F_n^* > 2$ — 纯布尔辛自相关四次迹界）**：
    由 $S(\sigma)^2 = (d^2-1)I + \sum_{r\neq 0} A_r(\sigma) P_r$（其中 $A_r(\sigma) := \sum_{p \in r^\perp \setminus \{0, r\}} \gamma(p, p\oplus r)\sigma_p\sigma_{p\oplus r} \equiv 2 \pmod 4$，且 $A_{Z_1}(\sigma) = \sum_{p \in Z_1^\perp \setminus \{0, Z_1\}} \sigma_p\sigma_{p\oplus Z_1}$）得精确恒等式
    $$\mathrm{Tr}\!\left(S(\sigma)^4\right) = d(d^2-1)^2 + d \sum_{r \neq 0} A_r(\sigma)^2, \qquad \mathrm{Tr}\!\left(S(\sigma)^3\right) = d \sum_{r \neq 0} \sigma_r A_r(\sigma).$$
    任何一致界 $\sum_{r \neq 0} A_r(\sigma)^2 \le (1 - \delta)\,d(d^2-1)^2$（$\delta > 0$）即可一步同时证明 $\limsup c_n^* \le 2\sqrt{1-\delta} < 2$ 与 $\liminf F_n^* > 2$。
- **待决策下一步选项**：
  1. 直接进入**方向 3A**（Gowers $U^3$ 相位方盒 / 过约束 $K(a), H(a,u)$ 纯理论攻坚）；
  2. 直接进入**方向 3B**（纯布尔辛自相关 $\sum A_r(\sigma)^2$ 四次迹界纯理论攻坚）；
  3. 同步或先行将 Stage 15 中干净的一般 $n$ / 一般 $m$ 纯代数定理（如 $F_n = d^5\|\psi\|_{U^3}^8$ 精确分解、`Tr(S^4)` 自相关恒等式、或 $O^\varepsilon(2s,2)$ 上双对角正交投影与稳定子恒等式）形式化入 Lean 4。
