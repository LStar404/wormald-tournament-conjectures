# 真实独立块计数渐近：完整分析证明

这一节记录猜想 1 的完整计数分析链。最终 `ActualRegularCyclesLimit` 已从原随机样本推导出真实期望极限，没有将计数渐近、局部特征值或期望的 Hessian 作为假设。与有限谱极值及非正则分支合并后，`ConjectureOneProof` 无条件证明原猜想 1。

固定正则基图阶数 \(d\ge3\)，令内部块阶数为 \(m\)，\(N=dm\)，并设

\[
B=A+\tfrac12I,\quad P=\frac2dB=\frac Jd+C,
\qquad R_{d,m}=\frac{(m!)^d d^{dm}}{(dm)!}.
\]

## 1. 从样本到真实 Fourier 积分

每个 Hamilton 圈使用的内部无序边各不相同；独立公平边平均后，每条这样的有向边贡献 \(1/2\)。把一个圈选定起点，再按基块记录顶点，得到平衡循环词。每个词有恰好 \((m!)^d\) 种顶点标号，而每个圈有 \(N\) 个起点。

因此有精确公式

\[
\frac{\mathbb EC}{\nu_N}
=R_{d,m}\,[X_1^m\cdots X_d^m]
\operatorname{tr}((P\operatorname{diag}X)^N).
\]

把最后一个相位固定为 1，总次数 \(N=dm\) 使最后一个占用数也被迫等于 \(m\)。于是可用 \(d-1\) 维归一化环面的 Fourier 正交性精确提取系数。标号、旋转及维数减少都由有限双射或有限和恒等式证明，没有使用计数渐近。见 `ExactCycleCoefficient`、`ExactCycleFourier`、`AnchoredCycleFourier`、`MarkovCriticalBridge`。

## 2. 远离唯一临界相位的部分

\(P\) 保持常数向量，并在零和向量上严格收缩。对单位相位 \(u\)，令 \(A_u=P\operatorname{diag}u\)。由平方范数取等条件可得：若最后一个相位为 1，且 \(A_u\) 有单位模特征值，则全部相位都为 1，特征值也为 1。

更直接的估计是：非临界相位下，每个非零向量都满足 \(\|A_u^2x\|_2<\|x\|_2\)。在任意避开临界相位的紧集上取最大值，便得到统一收缩率以及矩阵幂迹的指数衰减。它不需要调用谱半径连续性。见 [两步收缩简明证明](concise-critical-gap.zh.md) 和 `CriticalTransitionTraceDecay`。

## 3. 从原多项式构造局部特征值

对原 \(K\) 使用复隐函数定理，构造真正的局部函数 \(s(\theta)\)，使 \(s(0)=0\)、\(\lambda(\theta)=e^{s(\theta)}\)，并且

\[
\det\bigl(\lambda(\theta)I-P\operatorname{diag}(e^{i\theta_1},\ldots,e^{i\theta_{d-1}},1)\bigr)=0.
\]

一、二阶导数来自原 \(K\) 的实际链式求导。对中心化相位

\[
\Phi(\theta)=d\,s(\theta)-i\sum_j\theta_j
\]

已经证明 \(\Phi(0)=0\)、\(D\Phi(0)=0\) 以及

\[
-\partial_j\partial_k\Phi(0)=Q_{jk}-\frac1d,
\qquad Q=(I+C^2)(I-C^2)^{-1}.
\]

实锚定矩阵 \(R=(Q_{jk}-1/d)_{j,k<d}\) 正定，且 \(\det R=\det Q/d\)。对应 `LocalSpectralBranch`、`ExponentialJetCalculus`、`CenteredSpectralJet`、`SpectralBranchJets`、`SpectralPhase`、`CovarianceAnchor`。

## 4. 局部高斯积分与常数

通用局部 Laplace 定理已独立证明：若实际复相位在零点附近有正定二次项 \(-x^TSx/2\)，余项是 \(o(\|x\|^2)\)，则足够小的球上

\[
m^{(d-1)/2}\int e^{m\Phi(x)}\,dx
\longrightarrow\frac{(\sqrt{2\pi})^{d-1}}{\sqrt{\det S}}.
\]

证明先用正定性给出统一正下界，再以 \(x/\sqrt m\) 缩放。二次余项给出点态极限，并受可积高斯函数控制，所以可应用控制收敛定理。高斯行列式常数来自真实 Lebesgue 换元及正矩阵平方根。对应 `QuadraticScaling`、`QuadraticRemainderBound`、`QuadraticPeakIntegral`、`GaussianMatrixIntegral`、`GaussianNormBound`、`MatrixLaplaceIntegral`。

此外，阶乘因子已证明

\[
\frac{R_{d,m}}{(\sqrt m)^{d-1}}
\longrightarrow\frac{(\sqrt{2\pi})^{d-1}}{\sqrt d}.
\]

单位周期 Fourier 坐标是 \(t=\theta/(2\pi)\)；因此实际局部二次矩阵是 \((2\pi)^2R\)。不能省略这个变量替换及其行列式因子。

## 5. 合并三部分，得到原计数极限

实际局部矩阵幂迹满足精确分解

\[
\operatorname{tr}A(t)^N=\lambda(t)^N+\operatorname{tr}R(t)^N,
\qquad R(0)=C.
\]

秩一投影由实际左右特征向量构造；其存在、连续性及这条恒等式均已证明。由于 \(\|C\|_F<1\)，余项在共同小球中一致指数衰减。实际相位的二阶微分经小凸球上的均值不等式给出真正的 \(o(\|t\|^2)\) 余项，从而可直接使用第 4 步。拆分积分所需的实际可积性也已证明，没有利用非可积函数积分默认取零的约定。

因此在 \((\sqrt m)^{d-1}\) 尺度上，局部主项趋于高斯常数，局部余项及远域部分均趋零。再乘精确 Stirling 比例，所有 \(2\pi\) 和维数因子相消，得到

\[
\frac{\mathbb EC}{\nu_{dm}}\longrightarrow
\frac{1}{\sqrt d\sqrt{\det R}}
=\frac1{\sqrt{\det Q}}=\rho(T).
\]

对应 `LocalSpectralProjector`、`SpectralPhaseTaylor`、`ScaledSpectralLaplace`、`ActualResidualDecay`、`LocalFourierDecomposition`、`LocalFourierIntegral`、`GaussianSpectralConstant`、`ActualRegularCyclesLimit`。`RegularCycleAsymptotics` 已由 `regularCycleAsymptotics` 证明，原归约不再保留未证明输入。

均匀正则内部块使用单独证明的相关边概率渐近；第 1 步的独立边平均等式不适用于该模型。所需一致估计及最终原猜想 2 现均已完成，见 [正则内部块的完整概率与计数连接](regular-forest-next-step.zh.md)。
