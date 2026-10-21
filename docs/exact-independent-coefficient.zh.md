# 独立模型的精确系数公式

这一有限计数入口已经完成 Lean 验证。固定一个 \(d\) 阶基锦标赛，每个内部块独立取均匀的 \(m\) 阶锦标赛。令 \(N=dm\ge3\)，令 \(B\) 的对角元为 \(1/2\)，其余矩阵元为基图的弧指标。对变量 \(X_1,\ldots,X_d\)，记

\[
M_B(X)=B\operatorname{diag}(X_1,\ldots,X_d),
\qquad [X^m]=[X_1^m\cdots X_d^m].
\]

原模型的真实期望满足精确恒等式

\[
\boxed{\displaystyle
\mathbb E\,HC(T\circ R_m)
=\frac{(m!)^d}{N}[X^m]\operatorname{tr}(M_B(X)^N).}
\tag{1}
\]

这里没有渐近误差，也没有把原模型换成任意定义的函数。

证明按四个有限对应完成。

1. **平均真正的内部无序边。** 对一个单轨后继置换 \(\sigma\)，当 \(N\ge3\) 时，不可能同时出现 \(\sigma(u)=v\)、\(\sigma(v)=u\)。因此一个 Hamilton 圈至多使用一条内部无序边的一种方向。该圈权重对这一公平布尔坐标是仿射函数，端点平均恰好等于中点值。逐条平均后，圈的期望权重恰为 \(\prod_v B_{b(v),b(\sigma(v))}\)，其中 \(b(v)\) 为顶点所属的基块。

2. **选择循环起点。** 一个单轨后继置换加一个起点，与一个双射顶点顺序 \(e:\operatorname{Fin}(N)\simeq V\) 严格一一对应：\(e(k)=\sigma^k(e(0))\)。Lean 同时证明了轨道周期为 \(N\)、循环后继对应以及两个方向互逆。因此对所有双射顺序求和，恰好把每个圈计算 \(N\) 次。

3. **忘掉内部顶点标签。** 记循环基词 \(f(k)=b(e(k))\)。每个字母出现 \(m\) 次的词恰好有 \((m!)^d\) 个双射标签分配；不满足这一平衡条件的词没有标签分配。形式化证明实际构造了一个标签分配，再将整个标签纤维与保块置换群建立等价。

4. **展开矩阵迹并提取系数。** 对 \(N>0\)，

   \[
   \operatorname{tr}(M_B(X)^N)
   =\sum_{f:\operatorname{Fin}(N)\to\operatorname{Fin}(d)}
     \left(\prod_k B_{f(k),f(k+1)}\right)
     \prod_k X_{f(k)},
   \]

   下标 \(k+1\) 按模 \(N\) 理解。提取 \(X_1^m\cdots X_d^m\) 恰好筛出平衡循环词，得到 (1)。

\(N\ge3\) 的条件有实际作用：二圈会同时使用同一无序边的相反方向；在真实锦标赛中其权重为零，而两个边际均值的乘积为 \(1/4\)。证明没有忽略这一相关性。

## 适合极限分析的归一化

令 \(P=2B/d\)，令

\[
R(d,m)=\frac{(m!)^d d^{dm}}{(dm)!},
\qquad \nu_N=\frac{(N-1)!}{2^N}.
\]

由齐次性及 \(N!=N(N-1)!\)，(1) 等价于

\[
\boxed{\displaystyle
\frac{\mathbb E\,HC(T\circ R_m)}{\nu_{dm}}
=R(d,m)[X^m]\operatorname{tr}((P\operatorname{diag}X)^{dm}).}
\tag{2}
\]

这个代数恒等式对所有基图成立。若基图正则，则 \(P\ge0\)、每行及每列之和均为 \(1\)，且 \(P_{ii}=1/d\)，因此右端确实可以解释为有限状态 Markov 循环的平衡占用权重。

Stirling 部分也已独立验证。写 \(d=k+1\)，则

\[
\frac{R(k+1,m)}{(\sqrt m)^k}
\longrightarrow\frac{(\sqrt{2\pi})^k}{\sqrt{k+1}}.
\tag{3}
\]

(2)、(3) 把正则基图渐近问题集中到这个**具体矩阵迹系数**的局部极限估计。该估计现已在 `ActualRegularCyclesLimit` 中由实际 Fourier 积分证明，见[分析证明](local-counting-analysis.zh.md)。均匀正则内部块属于另一种有相关性的概率律，不能直接套用本页的独立边平均步骤。

## 对应的 Lean 声明

| 步骤 | 声明 |
|---|---|
| 单轨后继没有二圈 | `singleOrbit_no_twoCycle` |
| 真实期望恰等于加权单轨和 | `expectedCycles_eq_weightedHamiltonianCycleSum` |
| 选择起点与顶点顺序的等价 | `rootedCycleEquivOrder` |
| 精确的循环起点因子 | `rootedOrder_sum_eq_card_mul_weightedSum` |
| 平衡词的标签纤维大小 | `labelingFiber_card_eq_ite` |
| 原模型到平衡词的精确公式 | `expectedCycles_eq_balancedCycleWordSum` |
| 矩阵迹的有限闭路词展开 | `trace_variableMatrix_pow_eq` |
| 系数恰好筛出平衡词 | `coeff_trace_variableMatrix_pow` |
| 完整的精确公式 (1) | `expectedCycles_eq_traceCoefficient` |
| 完整的归一化公式 (2) | `normalizedExpectedCycles_eq_markovTraceCoefficient` |
| 正则时 \(P\) 双随机 | `markovBase_rowSum`、`markovBase_colSum` |
| 精确的 Stirling 极限 (3) | `tendsto_factorialPrefactor_div_sqrt` |
