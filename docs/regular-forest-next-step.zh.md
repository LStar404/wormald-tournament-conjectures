# 正则内部块：真实概率的一致渐近

本说明中的条件化、有限系数与积分恒等式、增长维一致估计及最终循环计数连接均已完成。`UniformRegularTorusProof.lean` 证明实际积分的一致主项，`ConjectureTwoProof.lean` 将它用于真实正则块期望，从而完成原编号猜想 2。文件名保留了早期工作阶段的名称，内容不再是待证明问题清单。

原模型把每个内部块限制为均匀正则锦标赛。它与独立公平边模型之间的关系是**条件化**，不是逐边替换成均值。

`RegularConditioning.lean` 已证明有限恒等式

\[
\mathbb E_{\mathcal R} f
=\frac{\mathbb E_{\mathcal T}[f\,\mathbf1_{\mathrm{AllRegular}}]}
{\Pr_{\mathcal T}(\mathrm{AllRegular})}.
\]

这个公式已经代入真实 `expectedRegularCycles` 和 `expectedRegularPaths`。奇数块阶存在 carousel 正则锦标赛，因而分母严格为正；正则事件也已经严格改写为各块符号矩阵的每一行之和为零。对任意指定有向边集的正则包含概率，文件同样给出精确的条件比式。

`RegularDegreePolynomial.lean` 和 `RegularForestFourier.lean` 又把这个真实概率接到了有限生成函数及 Fourier 积分。令 \(k=(m-1)/2\)，令

\[
G_m(X)=\prod_{i<j}(X_i+X_j).
\]

每条无向边选择其源端的变量，所以单个锦标赛贡献的单项式恰为 \(\prod_iX_i^{\deg^+(i)}\)。因此 \([X_1^k\cdots X_m^k]G_m\) 是**实际正则锦标赛数**，且已证明严格为正。给定无自环有向边集 \(D\)，把强制边 \(i\to j\) 的因子替换为 \(X_i\)，得到 \(G_{m,D}\)；若同时强制两个反向，因子为零。已经验证

\[
\Pr_{\mathrm{reg}}(D\subseteq T_m)
=\frac{[X_1^k\cdots X_m^k]G_{m,D}}
{[X_1^k\cdots X_m^k]G_m}.
\]

两个系数随后都严格转换为归一化 torus 积分，或任意单位边长实立方体上的 Fourier 积分。这里没有假定目标包含概率或其渐近值；实际增长维积分估计因而与原有限概率准确对应。

`RegularForestCosine.lean` 进一步完成公共相位的抵消。每条自由边贡献 \(2\cos(\pi(x_i-x_j))\)，每条强制边 \(i\to j\) 贡献 \(\exp(i\pi(x_i-x_j))\)。实际概率正是强制边产品积分除以自由边产品积分；双向矛盾约束贡献零。`GaussianMatrixFourier.lean` 则独立证明了后续主峰计算需要的正定矩阵 Gaussian Fourier 积分

\[
\int_{\mathbb R^r}e^{-x^TSx/2+i b^Tx}\,dx
=\frac{(\sqrt{2\pi})^r}{\sqrt{\det S}}
e^{-b^TS^{-1}b/2}.
\]

该公式来自真实矩阵平方根换元及一维 Gaussian 积分，并已证明可积性。后续另外证明了与真实 torus 积分之间的一致误差；二者在最终装配中准确连接。

## 与原文准确对应的目标

[Wormald 固定版本的 §2、Lemma 3](https://arxiv.org/html/2610.16245v1#S2) 的相关目标为：奇数 \(m\to\infty\) 时，对于路径森林或 Hamilton 圈 \(F_m\)，

\[
\Pr_{\mathrm{reg}}(F_m\subseteq T_m)
\sim 2^{-a(F_m)}\exp\!\left(\frac{a(F_m)-s(F_m)}m\right),
\tag{1}
\]

其中 \(a\) 是边数，\(s\) 只计算含至少一条边的路径分量。原文 Theorem 1 证明的中间显示式有 \(e^{m/d}\)；依其前面的参数计算应为 \(e^{1/d}\)，也与定理陈述及下一句一致。

Lean 使用下面更直接的二步边统计表述，并对全部合法部分置换弧集证明统一相对误差。这覆盖原圈计数需要的路径森林与有向圈。

## 避免连通分量计数的表述

令 \(b(F)\) 为连续两条有向边组成的有向二步路径数。一个含 \(\ell\ge1\) 条边的路径贡献 \(\ell-1\)，所以路径森林满足

\[
b(F)=a(F)-s(F).
\]

Hamilton 圈满足 \(b(F)=a(F)=m\)。因此所需修正统一为 \(\exp(b(F)/m)\)。这使 Lean 可以只处理有限边和相邻边对，避免引入图连通分量的商类型。

形式化直接把 \(D\) 表示为有限有向边集，并要求没有自环、没有反向弧对、每个顶点入度与出度至多一。无需先把森林重标号为标准路径的子集。已证明的**一致相对误差**为：

\[
\sup_{D\text{ 为合法部分置换}}
\left|
2^{a(D)}\Pr_{\mathrm{reg}}(D\subseteq T_m)
e^{-b(D)/m}-1
\right|\longrightarrow0.
\tag{2}
\]

仅对某个固定的有限边集证明包含概率趋于 \(2^{-a}\)，不足以替代 (2)：实际森林有 \(O(m)\) 条边，\(O(1/m)\) 的逐边修正会累积为非平凡常数。

## 如何接到已经验证的循环基词公式

固定 \(d\ge3\)，一个 Hamilton 圈在每个内部块中的边构成路径森林。将圈投影成循环基词 \(f\)，则

\[
\sum_i b(F_i)
=\#\{t:f_t=f_{t+1}=f_{t+2}\}.
\tag{3}
\]

`RegularCycleTransfer.lean` 将真实 `expectedRegularCycles` 改写成单轨后继排列的有限加权和，每项是各内部边集真实正则包含概率的乘积。`InternalTripleStatistic.lean` 证明 (3) 与这个内部边集定义准确对应。已证明的一致概率估计逐项作用于这个有限和，固定 \(d\) 后给出 \((1\pm\varepsilon_m)^d\) 的整体夹逼。

对于已定义的正则基图转移矩阵 \(P\)，Lean 已证明其双随机性和 \(P_{ii}=1/d\)。均匀稳态下，同字母三连字的概率为

\[
\sum_i\frac1d P_{ii}^2=\frac1{d^2}.
\]

总词长为 \(dm\)，因此集中点是
\(\sum_i b(F_i)/m\to1/d\)，从而得到 \(e^{1/d}\)。短证明利用 \(P_{ii}=1/d\)：开放路径的“下一步仍停在同块”标志，其真实联合权重恰为独立 Bernoulli 乘积。三连字是相邻两个标志的乘积，按起点奇偶拆开即可应用 Hoeffding。`HoldingFlags.lean` 至 `BalancedTripleConcentration.lean` 接到实际循环词及平衡坏词分子，给出指数尾界；首尾闭合只影响两个统计项。`BalancedTripleConditional.lean` 用已证独立块渐近提供的实际平衡总权重下界完成条件化，`BalancedTripleExponential.lean` 再证明正指数均值趋于 \(e^{1/d}\)。

## 已完成的增长维解析连接

估计 (2) 属于维数随 \(m\) 增长的正则度约束枚举。证明单独处理了实际主峰的一致 Taylor 误差、公共四次项集中与消去，以及完整周期域上的非中心尾界；没有拿固定维局部极限定理代替增长维估计。

`RegularCentralMainTerm.lean` 给出主峰误差，`RegularNoncentralTail.lean` 给出完整补集的一致范数积分误差，`UniformRegularTorusProof.lean` 将两者装配成 `uniformRegularTorusMainTerm`。`UniformRegularFourierReduction.lean` 的精确分子、分母比随后推出 `uniformRegularContainmentAsymptotic`。这两个曾保留在条件归约中的输入现已无条件证明。

实际正则块的内层极限为独立块谱常数乘 \(e^{1/d}\)，`ConjectureTwoProof.lean` 把它与 carousel 闭式及外层极限相接。最终定理全名为 `Wormald.FiniteModel.conjectureTwo_proof`。详见 [主峰高斯计算](regular-local-gaussian.zh.md)、[圆上主簇尾界](regular-tail-cluster-proof.zh.md)、[最终有限计数连接](regular-cycle-limit-reduction.zh.md) 和 [原命题对应审阅记录](verification-c2-correspondence.zh.md)。路径版本仍不列为当前端到端结论。
