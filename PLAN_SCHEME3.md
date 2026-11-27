# 方案 3 执行计划：先固化一般 $n$ 基础理论包（路线 1），再新开会话双线攻坚硬仗 A & B（路线 2 + 路线 3）

> **分支：** `explore/asymptotic-theory`（基线 `0bdb5ff`，对应理论综述 [ASYMPTOTIC_THEORY_NOTES.md](ASYMPTOTIC_THEORY_NOTES.md)）  
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

## 阶段二（新开干净会话）：路线 2 + 路线 3 双线纯理论攻坚

完成阶段一并推送后，开启全新会话（仅需先读 `ASYMPTOTIC_THEORY_NOTES.md` + 本文件即可 1 轮热启动），分两条正交战线推进真正的开放性一般 $n$ 硬仗：

### 战线 2（硬仗 A — 一般 $t = 4m$ 的 $R_{4m}$-理想 Clifford-PPT 理论）
- **开局精准探针**：绕开完整交换子代数，**只在 $R_{12}$ 重复码理想内部**构造 $t = 12$（$6:6$ 切分）的显式单算子 $Q_{12} = \Pi_{\perp(\dim(L)\ge 2)}(\tau_6(P_{\mathrm{Sym}^{12}} R_{12} P_{\mathrm{Sym}^{12}}))$，测定其在 $y_H(d)$ 上的精确零点 $d_0(12)$；
- **纯理论目标**：
  1. 判定 $d_0(4m)$ 的增长律（$2^{\Theta(m^2)}$ vs $(2m)!$ vs $4^{2m}$），明确回答需要多大的 $t(n)$ 才能在 $y_H(2^n)$ 上产生负特征值；
  2. 尝试对一般 $t = 4m$ 给出 $Q_{4m}$ 作用在 $y_H(d)$ 上的解析闭式（或证明其 $O(d^{-2})$ 裕度在 `Sym^{4m}` 下能否/为何不能推出常数间隙 $\liminf F_n^* > 2$）；
  3. 视结论决定是否把 $t=8$ 的 $\tau_2$（$d_0 = 64$）与 $\tau_4$（$d_0 = 52 + 2\sqrt{574}$）精确闭式相变定理形式化。

### 战线 3（硬仗 B — 直接攻坚 $\liminf F_n^* > 2$ 或 $\limsup c_n^* < 2$）
*(可与战线 2 同会话先后推进，或按需单开 `/boost` 会话专注攻坚)*
- **核心切入点（探针 2 筛出的唯一活口）**：
  在 $F_n \to 2$（或 $c_n \to 2$）极限下，对全部 $d+1$ 个完整 MUB 展布 $L_k$，Born 分布 $Y_k(x) = d p_{L_k}(x) = 1 + \frac{m_{k,x}}{\sqrt{d+1}} + e_k(x) \ge 0$ 同时受到四重耦合约束：
  1. 离散奇整数 WHT 约束与单侧下界 $m_{k,x} \ge -\sqrt{d+1}$；
  2. Porter–Thomas 型三次矩 $\mathbb{E}[Y_k^3] \to 6$（与 $c_n \to 2$ 等价）；
  3. 极小四次加法能量 $d E_{\mathrm{add}}(p_k) - 1 \to 1/d$；
  4. 跨 MUB 的非双线性辛 2-上链耦合 $\gamma(p, q) = Q_0(p)Q_0(q) + a_1 \cdot b_2$。
- **两条并进主攻方向**：
  - **方向 3a（直接攻 $\liminf F_n^* > 2$）**：利用“稀疏尖峰缝隙”，绕过接近 $2$ 的 $c_n$（如 $c_7 = 1.797$），直接寻求非固定 $t$ 的四次矩 / 稳定子 Rényi 熵 $M_2$ 相干下界或跨 MUB 加法能量耦合下界；
  - **方向 3b（攻 $\mathrm{Tr}(S(\sigma)^4) \le (1-\delta)T_2^2$ 或多 MUB 熵/离散障碍）**：从 $(S(\sigma)+I)/2 \in M_d(\mathbb{Z}[i])$ 和 $d+1$ 个 MUB 的同步离散相容性出发，寻找迫使 $S(\sigma)$ 偏离秩 1（即 $\|r_t - |\psi_1\rangle\langle\psi_1|\|_F \ge \delta_0 > 0$ 或 $\mathrm{Tr}(S^4) \le (1-\delta)T_2^2$）的定量障碍。
