# 临界转移的收缩、唯一性和远域衰减

这条有限维证明直接使用原问题的正则锦标赛，不需要先证明图的不可约性或调用 Perron–Frobenius 定理，也不把待证谱隙当作假设。它为 Fourier 积分的远离临界点部分提供统一指数界；局部高斯渐近及二者的完整合并已在 `ActualRegularCyclesLimit` 中另行证明。

设 \(T\) 是非空的正则锦标赛，符号矩阵为 \(S\)，令

\[
 C=S/d,\qquad P=J/d+C,\qquad E(x)=\sum_i|x_i|^2.
\]

## 1. 先证明唯一的无损方向

已知 \(\|C\|_F^2=(d-1)/d<1\)。对复向量分别应用实部和虚部的 Cauchy–Schwarz 不等式，得到

\[
 E(Cx)\le\frac{d-1}{d}E(x).
\]

因此 \(x\ne0\) 时 \(E(Cx)<E(x)\)。若 \(\sum_i x_i=0\)，则 \(Px=Cx\)，所以 \(P\) 在常数正交补上严格收缩。

对于一般 \(x\)，写成 \(x=\mu\mathbf1+y\)，其中 \(\mu=d^{-1}\sum_i x_i\)、\(\sum_i y_i=0\)。正则性给出 \(C\mathbf1=0\) 和 \(\mathbf1^TC=0\)，故

\[
 Px=\mu\mathbf1+Cy,\qquad
 E(x)=d|\mu|^2+E(y),\qquad
 E(Px)=d|\mu|^2+E(Cy).
\]

于是 \(E(Px)\le E(x)\)，并且取等当且仅当 \(y=0\)，即 \(x\) 为常数向量。

Lean 对应：`CriticalTransitionContraction` 和 `CriticalTransitionEquality`。平方能量的定义明确使用复数模平方，没有混用函数空间的最大范数。

## 2. 两步已经足以排除所有非平凡相位

令 \(|u_i|=1\)，固定一个指标 \(a\) 并要求 \(u_a=1\)，记 \(A(u)=P\operatorname{diag}(u)\)。相位乘法保持 \(E\)，所以

\[
 E(A(u)^2x)\le E(A(u)x)\le E(x).
\]

假设 \(x\ne0\) 且最后取等。第一次取等强制

\[
 \operatorname{diag}(u)x=\alpha\mathbf1,
 \qquad A(u)x=\alpha\mathbf1.
\]

这里 \(\alpha\ne0\)，否则 \(x=0\)。第二次取等又强制 \(u_i\alpha=\beta\) 对所有 \(i\) 成立。代入锚点 \(u_a=1\) 得 \(\beta=\alpha\)，从而所有 \(u_i=1\)。因此，除全一相位外，每个非零向量经过两步都严格损失能量。

同样，若 \(A(u)x=\lambda x\)、\(|\lambda|=1\)、\(x\ne0\)，则能量取等，故相位全为一且 \(\lambda=1\)。于是

\[
 \det(I-A(u))=0\quad\Longleftrightarrow\quad u=\mathbf1.
\]

Lean 对应：`CriticalTransitionPhase`、`CriticalTransitionSpectralGap`、`CriticalTransitionTwoStep`。锚点可以直接选最后一个坐标。

## 3. 紧致性只用于选取共同的严格常数

设 \(K\) 是锚定相位环面中避开全一相位的任意紧集。集合

\[
 K\times\{x:E(x)=1\}
\]

紧致，且 \((u,x)\mapsto E(A(u)^2x)\) 连续。它在每一点都小于 \(1\)，所以其最大值 \(r\) 满足 \(0\le r<1\)。齐次性把单位能量球上的界延伸到所有向量：

\[
 E(A(u)^2x)\le rE(x)\qquad(u\in K).
\]

每一步不增加能量，故归纳得到

\[
 E(A(u)^m x)\le r^{\lfloor m/2\rfloor}E(x).
\]

对基向量应用此式，控制每个对角元，再用迹的三角不等式，得到对所有 \(u\in K\)、所有自然数 \(m\) 共同成立的指数界

\[
 \bigl|\operatorname{tr}A(u)^m\bigr|
 \le d\,(\sqrt r)^{\lfloor m/2\rfloor},\qquad 0\le\sqrt r<1.
\]

Lean 对应：`CriticalTransitionCompactGap` 和 `CriticalTransitionTraceDecay`。这里已经证明单位能量球紧致、能量函数连续、共同最大值存在和任意向量的显式归一化；共同收缩率不是额外假设。以上正是 Fourier 积分远域指数衰减所需的有限部分。

## 4. 积分中的远域与局部余项

固定最后一个相位为零，将其余相位写成 \(e^{2\pi i t_j}\)，其中 \(t\in(-1/2,1/2]^{d-1}\)。记 \(N=dm\)。原模型的归一化期望已经精确写成一个显式阶乘前因子乘以下面的积分：

\[
 \int_{(-1/2,1/2]^{d-1}}
 e^{-2\pi i m\sum_jt_j}\,
 \operatorname{tr}\!\left(P\operatorname{diag}
 (e^{2\pi i t_1},\ldots,e^{2\pi i t_{d-1}},1)\right)^N\,dt.
\]

这是有限闭路词展开和 Fourier 正交性给出的恒等式：前 \(d-1\) 个颜色都出现 \(m\) 次，而总长度为 \(dm\)，所以最后一个颜色也恰好出现 \(m\) 次。这里没有先假设概率局部极限定理。Lean 对应：`AnchoredCycleFourier`、`MarkovCriticalBridge`、`AnchoredRealFourier`。

在小球之外，锚定相位不会全为一，前一节的紧致统一界直接适用。Fourier 字符的模恒为一，所以该部分积分的绝对值至多是有限体积乘 \(d q^{\lfloor dm/2\rfloor}\)，其中 \(0\le q<1\)。任意固定的 \((\sqrt m)^k\) 都不能抵消这一指数衰减。Lean 对应：`AnchoredPhaseGeometry`、`AnchoredFarField`。

在零点附近，实际主特征值和秩一投影给出精确分解

\[
 \operatorname{tr}A(t)^N=\lambda(t)^N+\operatorname{tr}R(t)^N,
 \qquad R(0)=C.
\]

由于 \(R\) 在零点连续且 \(\|C\|_F^2<1\)，可选一个共同的小球和 \(r<1\)，使整个小球内 \(\|R(t)\|_F^2\le r\)。同一个 Cauchy–Schwarz 估计给出

\[
 E(R(t)x)\le rE(x),\qquad
 |\operatorname{tr}R(t)^N|\le d(\sqrt r)^N.
\]

因此局部余项的 Fourier 积分乘任意固定 \((\sqrt m)^k\) 后也趋于零。Lean 中 `ResidualPowerDecay` 先证明这条通用有限维估计，再由 `ActualResidualDecay` 接到原锦标赛的实际余项 \(R(2\pi t)\)；中心值、连续性和严格能量界均已证明。局部主项 \(\lambda(t)^{dm}\) 的高斯渐近现也已完成，见[完整分析证明](local-counting-analysis.zh.md)；`ActualRegularCyclesLimit` 将这些环节接成真实期望极限。
