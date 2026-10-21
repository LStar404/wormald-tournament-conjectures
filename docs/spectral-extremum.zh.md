# 谱常数的最大值与唯一取等：完整有限证明

本节已由 Lean 完整验证，证明猜想 1 所需的有限极值结论。真实随机吹胀的 Hamilton 圈计数渐近也已在后续分析模块证明，最终共同给出原猜想 1 的端到端证明。

设锦标赛有奇数个顶点 \(d\ge3\)，符号矩阵为 \(S=2A+I-J\)，令 \(C=S/d\)。记

\[
\rho(T)=\frac{\det(I+C)}{\det(I+iC)}.
\]

这里的行列式比是正实数；符号配对还说明它是正有理数。以下证明对每个锦标赛都有 \(\rho(T)\le\rho(R_d)\)，其中 \(R_d\) 是实际圆环锦标赛；若 \(T\) 正则，取等当且仅当 \(T\cong R_d\)，同构采用普通有向图同构。

## 1. 用一个收敛级数表达原谱常数

令 \(D=-C^2=C^TC\)。它半正定，且 \(I-D\) 正定；后者由 \(C\) 的 Frobenius 范数严格小于 1 得到。于是 \(D\) 的每个特征值 \(t_j\) 都在 \([0,1)\) 内。标量恒等式

\[
\frac12\bigl(\log(1+t)-\log(1-t)\bigr)
=\sum_{r=0}^{\infty}\frac{t^{2r+1}}{2r+1}
\]

可对有限个特征值求和。结合实际行列式公式，得到

\[
\log\rho(T)
=\frac12\log\frac{\det(I+D)}{\det(I-D)}
=\sum_{r=0}^{\infty}\frac{\|C^{2r+1}\|_F^2}{2r+1}.
\]

Lean 先证明标量级数，再用实对称矩阵谱分解把迹、行列式和全部幂矩逐项连接；没有把这个级数表示当作额外前提。对应 `MomentSeries`、`MatrixMomentSeries`、`SkewMomentSeries`。

## 2. 逐项比较，取等下降到四阶迹

[任意幂矩的短证明](concise-moment-proof.zh.md) 给出每个 \(p\ge0\) 的实际矩阵不等式

\[
\|C_T^p\|_F^2\le\|C_{R_d}^p\|_F^2.
\]

因此上面收敛级数逐项比较即可得到 \(\log\rho(T)\le\log\rho(R_d)\)，再用对数的严格递增性得到谱常数比较。

若谱常数取等，任何一个级数项严格小都会使总和严格小。因此所有奇次幂矩都取等，特别可取 \(p=3\)。幂矩的等号下降定理进一步给出

\[
\operatorname{tr}(S_T^4)=\operatorname{tr}(S_{R_d}^4)
=\operatorname{tr}(S_{\mathrm{tr}}^4),
\]

其中 \(S_{\mathrm{tr}}\) 是传递锦标赛的符号矩阵。对应 `SpectralExtremum`、`NormalizedMoments`、`MomentEquality`。

## 3. 四点恒等式把取等变成具体图结构

对四个不同顶点定义

\[
\operatorname{pf}(a,b,c,e)
=S_{ab}S_{ce}-S_{ac}S_{be}+S_{ae}S_{bc}.
\]

它的平方只能为 1 或 9；重复顶点时为 0。反对称矩阵的有限展开给出

\[
\sum_{a,b,c,e}\operatorname{pf}(a,b,c,e)^2
=3\Bigl(\sum_{a,b}S_{ab}^2\Bigr)^2-6\operatorname{tr}(S^4).
\]

传递锦标赛每个不同四元组的平方都为 1。因此四阶迹取等强制所有不同四元组的平方为 1。

选择一个顶点，把其余各顶点的符号按需切换，使它成为源点。若剩余顶点中存在有向三角形，与源点组成的四元组就会有平方 9，矛盾。故余下锦标赛无有向三角形，顶点可按传递全序排列。这证明原符号矩阵是传递符号矩阵的带符号置换共轭。对应 `FourthMomentIdentity`、`FourthMomentEquality`、`SignClassification`。

最后使用原锦标赛的正则性：在这个传递排列下，相邻位置的切换符号必须交替。按明确给出的奇偶指标排列，得到与实际 \(R_d\) 的普通有向图同构。对应 `RegularSignClassification`，最终接口为 `isomorphic_carousel_of_fourth_trace_eq`。

## 4. 接回原猜想 1

`StrictSpectralGap` 由此证明：正则 \(T\not\cong R_d\) 时，\(\rho(T)<\rho(R_d)\)。非正则基图的实际归一化期望趋零也已独立证明。有限多个基图的共同阈值与同构不变性均已完成。

`ConjectureOneSpectralReduction` 将原命题归约到实际正则基图计数渐近。该极限现在由 `ActualRegularCyclesLimit` 从真实 Fourier 积分完整证明，见 [分析连接](local-counting-analysis.zh.md)。最终 `ConjectureOneProof` 消去这条归约的全部输入，证明原猜想及唯一普通同构类加强版；没有新增计数公理。
