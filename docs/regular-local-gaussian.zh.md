# 正则块主峰的高斯计算

这里说明原正则块 Fourier 积分的主峰计算及其完整一致误差。主峰与全部非中心部分现已在 `UniformRegularTorusProof.lean` 装配，实际条件概率及最终两层极限由 `ConjectureTwoProof.lean` 接通，原编号猜想 2 已端到端完成。

## 两个有限统计量

指定边集 $D$ 没有自环和反向弧对，每个顶点入度、出度至多一。令 $a=|D|$，令 $b$ 为同时有指定入边、出边的顶点数。路径森林满足 $b=a-s$，其中 $s$ 只计非平凡路径分量；有向圈满足 $b=a$。取

\[
L=\sum_{(i,j)\in D}(e_i-e_j)(e_i-e_j)^T,
\qquad z=\sum_{(i,j)\in D}(e_i-e_j).
\]

矩阵证明只用五条信息：

\[
0\preceq L\preceq4I,\quad \operatorname{tr}L=2a,\quad
\|z\|^2=2(a-b),\quad \sum_i z_i=0,\quad a\le m.
\]

`GaussianGraphData` 明确封装这些条件。标准路径、一般部分排列及实际循环内部边集的实例均已完成，见 [部分排列短证明](concise-partial-permutation-gaussian.zh.md)。真实余弦积分的有向相位、删边能量及高斯尺度也已在 `RegularLocalPhase` 至 `RegularScaledExpansion` 中精确对应。

## 精确高斯修正

对真实独立标准正态向量 $X\in\mathbb R^m$，令

\[
W_D(X)=\exp\!\left(\frac{X^TLX}{2m}+\frac{i z^TX}{\sqrt m}\right).
\]

`GaussianGraphFourierIntegral.lean` 已验证

\[
\mathbb EW_D=e^{\ell_D}
=\det(I-L/m)^{-1/2}
\exp\!\left(-\frac{z^T(I-L/m)^{-1}z}{2m}\right).
\]

期望使用实际 `Measure.pi (fun _ => gaussianReal 0 1)`。`GaussianProductDensity.lean` 证明了它与 Lebesgue 高斯密度积分的精确转换。对于 $m\ge16$，还已证明

\[
|\ell_D-b/m|\le16a/m^2,\qquad
|e^{\ell_D-b/m}-1|\le32/m,\qquad
\mathbb E|W_D|^2\le e^4.
\]

证明对特征值逐项使用 $\log(1-u)=-u+O(u^2)$，并通过完成平方控制逆矩阵二次型。常数不随维数、边数、路径分量数变化。一阶项分别为 $+a/m$ 和 $-(a-b)/m$，因此修正为 $+b/m$。

## 公共四次项

令

\[
Q_m(X)=\frac1{12m^2}\sum_{i<j}(X_i-X_j)^4.
\]

有限恒等式

\[
\sum_{i<j}(x_i-x_j)^4
=m\sum_i x_i^4-4\left(\sum_i x_i^3\right)\left(\sum_i x_i\right)
 +3\left(\sum_i x_i^2\right)^2
\]

把问题化为经验矩。真实标准正态的矩值及强大数定律给出 $Q_m\to1/2$ 几乎处处；因 $Q_m\ge0$，有界收敛进一步给出

\[
\mathbb E(e^{-Q_m}-e^{-1/2})^2\longrightarrow0.
\]

`GaussianQuarticConcentration.lean` 先在公共可数乘积空间证明，再通过精确有限前缀推前测度回到每个 $m$ 维高斯乘积。这是增长维数的真实结论。

`GaussianQuarticCancellation.lean` 用 Cauchy–Schwarz 合成

\[
\left|\mathbb E\bigl[W_D(e^{-Q_m}-e^{-1/2})\bigr]\right|
\le e^2\sqrt{\mathbb E(e^{-Q_m}-e^{-1/2})^2}\longrightarrow0,
\]

对所有允许的边集一致。这说明公共四次因子可在分子、分母间抵消。四次项本身并不趋于零。

## 余弦乘积与完整主峰误差

`DeletedCosineApproximation.lean` 由真实标量 Taylor 界证明：若所有边差至多 $r\le1$，删除 $a$ 条边的总对数误差至多 $|E|r^6+2ar^4$。取 $r=m^{-3/8}$，两项分别为 $O(m^{-1/4})$、$O(m^{-1/2})$。

`RegularCentralMainTerm.lean` 将这条误差与精确高斯修正、公共四次项消去及高斯窗口尾界组合，证明实际局部被积函数的主项为 $e^{-1/2}e^{b/m}$，误差对全部合法 $D$ 一致趋零。`RegularCentralGaussianTransport.lean` 与 `AnchoredRegularWindow.lean` 则证明主峰真实 torus 积分、物理角积分和有限高斯乘积期望的精确对应；其中 $\pi^{-(m-1)}$ Jacobian 与 Gaussian 商体积均保留。

完整周期域的补集已由 `RegularNoncentralTail.lean` 统一控制，见 [圆上主簇尾界](regular-tail-cluster-proof.zh.md)。因此 `UniformRegularTorusProof.lean` 给出实际完整积分 $I_D$ 的一致估计

\[
\left|\frac{I_D}{V_m/\pi^{m-1}}-e^{-1/2}e^{b/m}\right|\le\eta_m,
\qquad\eta_m\to0.
\]

空弧集使用同一估计，公共因子 $e^{-1/2}$ 随后在精确条件概率比中抵消，得到 $\Pr_{\rm reg}(D)=2^{-a}e^{b/m}(1+o(1))$ 的一致形式。最终定理不再保留这个积分估计作为假设；它直接服务于原猜想 2 的实际内层计数极限。
