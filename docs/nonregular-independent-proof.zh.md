# 非正则基图：从真实随机模型到零极限

这一分支已经完成 Lean 验证。它针对原猜想 1 的**独立随机内部块**：每条内部无序边独立、公平地定向。固定基锦标赛 \(T\)，记其阶为 \(d>0\)、顶点 \(i\) 的出度为 \(a_i\)，每个内部块有 \(m\) 个顶点，总阶为 \(N=dm\)。有向 Hamilton 圈按后继置换计数，循环起点已经取商。

若 \(T\) 非正则，则

\[
\frac{\mathbb E\,HC(T\circ R_m)}{\nu_{dm}}\longrightarrow0,
\qquad \nu_N=\frac{(N-1)!}{2^N}.
\]

不需要对正则基图的渐近式作任何假设。证明只有以下三个步骤。

## 1. 先平均真正独立的无序边

每个样本的 Hamilton 圈只是所有置换覆盖中的一部分，因此其圈数不超过邻接矩阵的永久积。

对一条内部无序边，把两个相反方向的矩阵元同时写为 \(x\) 与 \(1-x\)。永久积的每个单项式各使用这两个位置至多一次，因此具有

\[
\alpha+\beta x+\gamma(1-x)+\delta x(1-x),
\qquad \delta\ge0
\]

的形式。于是公平定向的平均不超过同时置为 \(1/2\) 的值：

\[
\frac{F(0)+F(1)}2\le F(1/2).
\]

逐条平均所有内部无序边，即得到全体内部非对角元均为 \(1/2\) 的矩阵。再把真正的零对角元增大到 \(1/2\)，永久积继续不减。令

\[
B_{ij}=\begin{cases}
\frac12,&i=j,\\
1,&i\to j\text{ 是基图的弧},\\
0,&\text{其余情况},
\end{cases}
\]

并将 \(B_{ij}\) 替换为常值的 \(m\times m\) 块，得到 \(B^{[m]}\)。上面的结论是

\[
\mathbb E\,HC(T\circ R_m)\le\operatorname{per}(B^{[m]}).
\tag{1}
\]

这里没有把相反方向的两个指标误当作独立变量：它们始终一起平均。其依赖关系正是使 \(x(1-x)\) 在端点为零、在中点非负的原因。

## 2. 用块结构得到阶乘上界

对每个顶点先指定其置换像所在的目标块。一个固定的目标块指定方式至多对应 \((m!)^d\) 个置换，因为每个目标块内至多有 \(m!\) 种匹配。

删去“每个目标块恰好接收 \(m\) 个顶点”的限制，只会增加非负权重之和。剩下的自由指定逐顶点分解，得到

\[
\operatorname{per}(B^{[m]})
\le (m!)^d\prod_i\left(\sum_j B_{ij}\right)^m
=(m!)^d\prod_i(a_i+\tfrac12)^m.
\tag{2}
\]

这一计数论证适用于任意非负基矩阵；不需要 Brégman 不等式。

定义归一化度数和度数乘积

\[
b_i=\frac{2a_i+1}{d}>0,
\qquad P=\prod_i b_i.
\]

每条基图边恰贡献一个出度，故 \(\sum_i b_i=d\)。如果基图非正则，\(b_i\) 不全为 \(1\)，严格 AM–GM 给出 \(0<P<1\)。结合 (1)、(2)，有

\[
\mathbb E\,HC(T\circ R_m)
\le(m!)^d(d/2)^{dm}P^m.
\tag{3}
\]

## 3. 正确归一化后让指数损失吸收阶乘因子

令

\[
R(d,m)=\frac{(m!)^d d^{dm}}{(dm)!}.
\]

将 (3) 除以 \(\nu_{dm}\)，使用 \((dm)!=dm\,(dm-1)!\)，对于 \(m>0\) 得到

\[
0\le\frac{\mathbb E\,HC(T\circ R_m)}{\nu_{dm}}
\le dm\,R(d,m)P^m.
\tag{4}
\]

固定 \(d>0\)，Stirling 公式给出某个仅依赖 \(d\) 的常数 \(C_d>0\)，使 \(R(d,m)\le C_dm^d\)。因为 \(P<1\)，右边不超过 \(dC_dm^{d+1}P^m\)，趋于零。夹逼即证。

## 证明与 Lean 的逐步对应

| 数学步骤 | 已验证声明 |
|---|---|
| 单样本圈数不超过永久积 | `blowup_hamiltonCycleCount_le_permanent` |
| 一条无序边的端点平均不超过中点 | `permanent_oppositePair_average_le` |
| 逐条独立平均 | `boolCube_average_le_midpoint` |
| 真正的样本空间与布尔坐标一一对应 | `independentSampleEquiv` |
| 原模型的期望上界 (1) | `expectedPermanent_le_blockConstant`、`expectedCycles_le_blockConstant` |
| 块矩阵永久积上界 (2) | `blockConstantMatrix_permanent_le` |
| 正确的出度归一化与 (3) | `weightedBase_rowSum_eq_degreeFactor`、`expectedCycles_le_factorial_degreeProduct` |
| 非正则时严格 \(P<1\) | `Tournament.degreeProduct_lt_one` |
| 阶乘因子的多项式上界 | `factorialPrefactor_polynomial_bound` |
| 真实归一化期望的有限上界 (4) | `factorialDegree_bound_normalized` |
| 完整的原模型零极限 | `tendsto_normalizedExpectedCycles_nonregular` |

最后一个定理的假设只有 \(d>0\) 和基图非正则。它直接使用 `FiniteModel.expectedCycles`，没有以任意函数代替期望，也没有把尚待证明的渐近式放进假设。相关主要声明的公理依赖均仅为 Lean/mathlib 的 `propext`、`Classical.choice`、`Quot.sound`。

这个独立边平均论证不能直接用于原猜想 2 的均匀正则内部块：后者的不同无序边存在额外依赖，必须另行处理。
