# 中央分析独立复核记录

本次对已冻结 Lean 源作独立数学语义与可积性复核，未修改证明源。未发现下列范围内的常数、相位、维数或积分使用错误。本记录不代替整个项目的编译及公理审计，也不单独宣称完整 C2 已证明。

## 覆盖范围

- 四次项：`GaussianQuarticIdentity`、`QuarticLawOfLargeNumbers`、`StandardNormalMoments`、`GaussianQuarticConcentration`、`GaussianQuarticCancellation`、`WeightedL2Cancellation`、`GaussianProductDensity`。
- 真实规定弧集：`PrescribedEdgeStatistics`、`RegularLocalPhase`、`RegularLocalExpansion`、`RegularScaledExpansion`；同时检查它们使用的 `DeletedCosineApproximation`、`CosineTaylorBounds`、`RegularCentralWindow` 与实际部分置换 Laplacian 接口。
- 中央积分：`GaussianCentralWindow`、`LocalGaussianIntegralError`、`GaussianQuarticMean`、`GaussianGraphMainTerm`、`RegularCentralMainTerm`、`RegularCentralGaussianTransport`；同时核对 Gaussian Fourier、密度和 quotient transport 的归一化。

## 核验结论

**四次系数正确。** `completeQuarticEnergy` 定义为有序对四次差总和的一半，精确等于无序边总和。标准 Gaussian 尺度下的指数为

\[
Q_m=\frac{\sum_{i<j}(Z_i-Z_j)^4}{12m^2}
=\frac{M_4-4M_3M_1+3M_2^2}{12}
\longrightarrow\frac{3+3}{12}=\frac12.
\]

这里只需要三阶经验矩具有有限极限，因为一阶极限为零。公共四次因子确为 \(e^{-1/2}\)，没有遗漏有序对的一半。

**维数确实增长。** 先在同一个可数独立标准 Gaussian 产品空间上使用强大数定律，再以精确前缀推前测度转回每个 \(\mathbb R^m\)。有界支配收敛给出四次因子的 \(L^2\) 误差趋零；未将固定维 Laplace 定理用于增长的 \(m\)。

**有向相位与修正符号正确。** 规定弧 \(a\to b\) 保留 \(e^{i(\theta_a-\theta_b)}\)。正反标号均经 canonical-edge 对应证明，最终相位是 \(+i\beta_D\cdot\theta\)。局部精确展开为

\[
N_D(\theta/\pi)=e^{i\beta_D\cdot\theta}
 \exp\!\left(-\frac{Q_2(\theta)}2-rac{Q_4(\theta)}{12}
             +\frac{\theta^TL_D\theta}2+e_D\right).
\]

Gaussian Fourier 产生负的 imbalance 二次项；与 determinant 项结合，利用
\(\operatorname{tr}L_D=2a_D\)、\(\|\beta_D\|^2=2(a_D-j_D)\)，主项为 **正号** \(\exp(j_D/m)\)。这里 \(j_D=\texttt{internalInOutCount D}\)。

**误差对全部合法弧集一致。** 使用的结构界只有 \(L_D\succeq0\)、\(L_D\preceq4I\)、\(a_D\le m\) 及上述 trace、imbalance 恒等式。对于 \(m\ge16\)，Gaussian 权重满足 \(\mathbb E|w_D|^2\le e^4\)，常数不依赖 \(D\) 的形状或随 \(m\) 的选择。局部余项满足

\[
|e_D|\le E_m=m^2r_m^6+2mr_m^4
=m^{-1/4}+2m^{-1/2},\qquad r_m=m^{-3/8}.
\]

**窗口与尾常数一致。** Gaussian 窗口为
\(|Z_i-Z_{\rm anchor}|/\sqrt m\le r_m/2\)，所以任意两点的物理角差至多 \(r_m\)。窗口外概率界是
\(\tau_m=2m\exp(-mr_m^2/32)\)：差变量使用有效但保守的 subgaussian 参数 \(4\)，再代入阈值 \(\sqrt m\,r_m/2\)，恰得到分母 \(32\)。

## 可积性与适用范围

- 局部误差先以 \(L^2\) Gaussian 权重支配，明确证明截断函数可积，再比较积分。
- 四次平均中的积分减法使用已证明的 `MemLp`、`hqi` 与 `hwi.mul_const`；没有直接对未证可积的表达式使用线性。
- `RegularCentralMainTerm` 在 `integral_sub` 前建立真实 `scaledRegularFactor` 的窗口可积性，在 `integral_add_compl` 前建立整个四次权重的可积性。
- `RegularCentralGaussianTransport` 的截断 anchored factor 在物理闭球上连续有界，因此其拉回在 Gaussian 概率测度下可积；随后通过实际密度等价与 Fubini 接到 quotient Gaussian。物理 Gaussian 指数与 factor 指数精确抵消，体积为 \(V_m\)。
- 含 \(1/m\) 的谱界与积分估计使用 \(m\ge16\)；`E_m\le1` 也是明确前提，最后由 \(E_m\to0\) 在充分大维数获得。定义在 \(m=0,1\) 的全域化值未被当作渐近证据。

最终中央误差上界为

\[
e^2\!\left(2E_m+\sqrt{q_m}+\sqrt{\tau_m}\right)
+e^{-1/2}e\,\frac{32}{m},
\]

其中 \(q_m\) 是公共四次因子的 Gaussian 平方误差。每项都只依赖 \(m\) 且趋零，与 `centralMainError` 的实际定义及主项 \(e^{-1/2}e^{j_D/m}\) 一致。
