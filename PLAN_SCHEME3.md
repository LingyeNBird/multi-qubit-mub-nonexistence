# 方案 3 执行计划：先固化一般 $n$ 基础理论包（路线 1），再新开会话双线攻坚硬仗 A & B（路线 2 + 路线 3）

> **分支：** `explore/asymptotic-theory`（阶段一 `4ff8c18`、Stage 15 战线 2 `a6625d7`、Stage 16 + 选项 C 100/100 审计 `038aae3` 均已入库；本次记录 **Stage 17 新工具 1：Pauli 切片重整化与双态支集互斥测不准泛函 $\mathcal{J}_m$** 并随即转入纯理论深挖，对应综述 [ASYMPTOTIC_THEORY_NOTES.md](ASYMPTOTIC_THEORY_NOTES.md)）  
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

### 战线 3（硬仗 B — 直接攻坚 $\liminf F_n^* > 2$ 或 $\limsup c_n^* < 2$）与选项 C 形式化
**状态：** ✅ **Stage 16 3A+3B 理论剖析、3B 边界标定与选项 C 26 条一般 $n$/一般 $m$ 纯理论定理 Lean 4 形式化全部完成**（详见 [`ASYMPTOTIC_THEORY_NOTES.md`](ASYMPTOTIC_THEORY_NOTES.md) Section 4.3 与 Section 5 #10）

1. **Stage 16 核心理论与侦察进展（3A 主攻 + 3B 边界标定）**：
   - **3A Clifford 流转与 $\mathbb{Z}_d$ 双黄金试金石**：在 $n=3..8$ 极值态与 Haar 对照上验证 $\mathbb{E}_{\mathrm{Cl}}[E_{\mathrm{amp}}] = \mathbb{E}_{\mathrm{Cl}}[E_K] = \frac{2}{d+1}(F_n - \mathrm{Welch}_n) + O(d^{-2})$，**96.8%–98.5%** 的超 Welch 盈余集中在弥散主体 $E_H$（`PR_frac = 0.16–0.26`）；精确 $\mathbb{Z}_4, \mathbb{Z}_8$ Zauner SIC 达到 $F_{\mathbb{Z}_d} = \mathrm{Welch}_d$ 却有严格正的 $K$ 能量（`0.0800 / 0.0772`），确认 $K(a)\equiv 0$ 与复对称平坦度为特征 2 专属；常振幅相态满足 `min F_phase = 1.75 (n=2), 2.25 (n=3), 2.8125 (n=4; E_K=0, E_H=7/8), 2.625 (n=5), 2.648 (n=6), 3.134 (n=7)`。
   - **三条通过双试金石的特征 2 无条件一般 $n$ 定理**：
     - **Theorem A（单陪集精确下界与 3-立方 $+4$ 偏移）**：$S_{\mathrm{indiv,Re}} \ge 2d\bigl(\frac{(1-r_0)^2}{d-1} - 4r_0^2\bigr)$，Welch 处 $\ge \frac{2d(d-17)}{(d+1)^2} \to 2$（$n=3$ 处 $d-17=-9<0$ 允许 Hoggar 达到 `S_indiv_Re = 0`，$\forall n \ge 5$ 在一切 Clifford 基下禁止逐陪集抵消）；
     - **Theorem B（复对称 $\Sigma = |\psi\rangle\langle\psi^*|$ 辛 Parseval 对偶与 Takagi 下界）**：$w_p = \frac{1}{d}\sum_q (-1)^{Q_p(q)} c_q^2$、$\sum_{Q_0=0}(w_p - \frac{2}{d+1})^2 = F_n - \mathrm{Welch}_n$、$\sum_{Q_0=0}\tilde{c}_p^2 = d\tilde{c}_0^2$ 与 $\frac{4d}{d+1}(1-\tilde{\alpha}_n(\psi)) \le F_n - \mathrm{Welch}_n$；
     - **Theorem C（费马双平方降阶与偶数 $n$ Pauli-MUB $\mathbb{Z}_4$-刚性）**：$R^2+I^2=4^m \implies (R,I) \in \{(\pm 2^m,0),(0,\pm 2^m)\}$。
   - **3B 反向边界标定（$n=4..9$）**：直接最大化 $\alpha_n, c_n$ 发现在 $n=7$ 达到局部峰值（`c_7 = 1.79675, α_7 = 0.96709`）后于 **$n=8$（`c_8 = 1.62881`）与 $n=9$（`c_9 = 1.59078`）回落**；$n=6$ `Hoggar ⊗ Hoggar`（`c_6 = 1.66208, F_6 = 256/81 = 3.1605`）显式实现稀疏尖峰缝隙。两条渐近猜想均获强实证支撑。
   - **诚实记录 4 条新排雷障碍（死胡同 #10）**：朴素 $\sim d^2/2$ vs $2d-2$ 过约束计数（败于 $\mathbb{Z}_d$ Zauner 试金石 2）；3-立方 $\Theta(d)$ 振幅 $L_1$ 预算；自对偶拉格朗日稀疏尖峰对 $\tilde{\alpha}_n^*$ 的同样绕过漏洞；纯整性/费马刚性仅给 $\mathrm{poly}(1/d)$ 连续稳定性。

2. **选项 C — Stage 15–16 纯理论包 Lean 4 形式化（✅ 已完成全量验证与公理审计）**：
   - **新增模块：** [`MultiQubitMUB/AsymptoticChar2Theory.lean`](MultiQubitMUB/AsymptoticChar2Theory.lean)（**2,198 行，26 条公开定理**，零 `sorry`、零 `native_decide`、零 `set_option`、零改动任何上游已过审模块）
   - **低内存安全构建与全量审计：**
     - `lake env lean -M 8192 -j 1 MultiQubitMUB/AsymptoticChar2Theory.lean`：exit 0，42.5s，0 错误 0 警告；
     - `python3 idea/safe_lake_build.py MultiQubitMUB.AsymptoticChar2Theory`：exit 0，19.0s，`peak_pgid_rss = 4936.2 MB`（< 8000 MB 上限）；
     - `python3 idea/safe_lake_build.py MultiQubitMUB`：exit 0，3.0s，`peak_pgid_rss = 4495.9 MB`；
     - `lake env lean -M 8192 -j 1 Audit.lean`：**100 / 100** 条定理（74 条既有 + 26 条新增）100% 仅依赖 `[propext, Classical.choice, Quot.sound]`。
   - **已形式化的 5 组无条件一般 $n$ / 一般 $m$ 定理**：
     1. 特征 2 Gowers-$U^3(\mathbb{F}_2^n)$ 方盒实性、$F_n = d\sum H^2$、非负超 Welch 分解与实态下界 $F_n \ge 3 - 2/d$（4 条）；
     2. Theorem A 单陪集精确公式 $S_{\mathrm{indiv,Abs}}, S_{\mathrm{indiv,Re}}$ 与 Welch 下界 $\frac{2d(d-17)}{(d+1)^2}$（4 条）；
     3. Theorem B 复对称 $\Sigma = |\psi\rangle\langle\psi^*|$ 辛 Parseval 对偶与 Takagi 下界（6 条）；
     4. 3B 辛自相关展开 $S(\sigma)^2$、三次/四次迹与精确夹逼 $(\alpha_n^*)^4 \le \max_\sigma \mathrm{Tr}(S^4)/T_2^2 \le (\alpha_n^*)^2$（6 条）；
     5. Stage 15 普适 $q=2$ Chu–Vandermonde 望远镜恒等式、$O^\varepsilon(2s,2)$ 上双对角递推、普适稳定子比值与非负性、$C_2(4m,2r) > 0$（$\forall m \ge 4$）与 Theorem C 费马双平方降阶（6 条）。

3. **Stage 17 专研新工具 1（当前主攻 — Pauli 切片重整化与双态支集互斥测不准泛函 $\mathcal{J}_m$，详见 [`ASYMPTOTIC_THEORY_NOTES.md`](ASYMPTOTIC_THEORY_NOTES.md) Section 4.4）**：
   - **发明动机**：打破现有三大工具（谱矩/SDP/Clifford-PPT、大 $U^3$ 逆定理、$\mathrm{poly}(1/d)$ 整性刚性）与问题本质的错配，构造一条显式利用特征 2 实期望 $c_p \in \mathbb{R}$、精确过双试金石、且直接输出 $O(1)$ 宏观量的专用工具。
   - **精确切片重整化恒等式与无条件 2 行普适归约**：对任意 $n$-比特纯态按最小 $|c_q(\psi)| \le (d+1)^{-1/2}$ 的 Pauli $P_q$ 切片，扔掉相位项 $Q_{\mathrm{phase}} \ge 0$ 并解耦两子态，无条件得
     $$F_n^* \;\ge\; \left(1 - \frac{1}{\sqrt{2^n + 1}}\right)^4 \mathcal{J}_{n-1}^*, \qquad \mathcal{J}_m(\phi_+, \phi_-) := \frac{F_m(\phi_+) + F_m(\phi_-)}{8} + \frac{5}{4} G_m(\phi_+, \phi_-) \;\ge\; 2 - \frac{1}{2^m + 1} + C(\phi_+, \phi_-).$$
   - **双试金石与首轮验金硬数据（`stage17_probe1`, `probe2`）**：$\mathbb{Z}_d$ 上因复相位 $90^\circ$ 抵消使系数 $12 \to 4$（无支集互斥惩罚）；$n=3$ Hoggar 处加权 $\mathcal{J}_2^{\mathrm{wt}*}$ 精确命中 **`16/9 = 1.777778`**（$C=0$）；自 $m=3$（$n=4$）起自由双态极小值全线卡在 **`2.102 (m=3), 2.335 (m=4), 2.395 (m=5), 2.270 (m=6), 2.816 (m=7)`**（$C \in [0.130, 0.559]$），对抗性 MUB 半数相干叠加攻击全部失败，且 $m=5, 6$ 极值双态同时撞在 Theorem B 锥边界（`min w_p = 0.0000`）。
   - **即时深挖主线**：(a) 复核 $m=7$ 收敛度（含 9-block Kerdock 切片）并深度解剖 $m=3..6$ 极值双态的零点集/群结构；(b) 先证一般 $m$ 实态双态下界 $\mathcal{J}_m(\phi_{\text{real}}, \phi_-)$；(c) 结合“同时对 $|\phi_+\rangle, |\phi_+^*\rangle$ Pauli-无偏”、秩-1 乘法律 $\rho_\pm^2 = \rho_\pm$ 及二级切片重整化（$n \to n-1 \to n-2$）冲击一般纯态对的 $\mathcal{J}_m^* \ge 2 + \delta_0$。
   - **并行储备方向**：选项 A（特征 2 常振幅相态 Gowers-$U^3$ 下界）与选项 B（离散实符号 $S(\sigma)$ 宏观秩-1 偏离障碍）。
