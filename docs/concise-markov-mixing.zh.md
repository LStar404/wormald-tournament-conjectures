# 正则模型的有限 Markov 混合基础

本说明的有限恒等式、循环三连浓度、平衡条件化和正指数均值极限均已完成，并已用于 `ConjectureTwoProof.lean` 的实际正则块计数。原编号猜想 2 的端到端结论不再以这些集中或混合性质为未证输入。

这里的转移矩阵就是原问题的计数转移矩阵。若正则锦标赛的邻接矩阵为 \(A\)，符号矩阵为 \(S=2A+I-J\)，阶数为 \(d\)，则

\[
 P=\frac{I+2A}{d}=\frac{J+S}{d}.
\]

Lean 的 `realCriticalTransition` 映入复数后精确等于 `criticalTransition`，也精确等于有限计数模型的 `markovBase`。矩阵的每个元素非负，每行、每列之和都是一。

## 两步转移的正下界

正则性使 \(JS=SJ=0\)，所以

\[
 (P^2)_{ij}=\frac{d+(S^2)_{ij}}{d^2}.
\]

当 \(i=j\) 时，反对称性给出 \((S^2)_{ii}=-(d-1)\)，故对角元恰为 \(1/d^2\)。当 \(i\ne j\) 时，和式中的第 \(i,j\) 项都是零，其余每项至少为 \(-1\)，故

\[
 (P^2)_{ij}\ge\frac{2}{d^2}.
\]

因此所有元素都至少为 \(1/d^2\)。令 \(U=J/d\)、\(\varepsilon=1/d\)，对于 \(d>1\) 定义

\[
 Q=\frac{P^2-\varepsilon U}{1-\varepsilon}.
\]

上述逐项下界直接说明 \(Q\ge0\)，行、列和的计算说明 \(Q\) 也是双随机矩阵。因此得到实际的 Doeblin 分解

\[
 P^2=\varepsilon U+(1-\varepsilon)Q.
\]

这些都是 `PositiveTransitionSquare.lean` 中已核验的有限恒等式与不等式；没有另行假设图的不可约性或混合性。

## 明确的收缩率

令 \(q=1-1/d\)。若实行向量 \(x\) 满足 \(\sum_i x_i=0\)，则 \(xU=0\)。随机矩阵在行向量的 \(\ell^1\) 范数下不扩张，因而

\[
 \|xP^2\|_1=q\|xQ\|_1\le q\|x\|_1,
 \qquad
 \|xP^N\|_1\le q^{\lfloor N/2\rfloor}\|x\|_1.
\]

这给出任意两个初始分布的总变差收缩；从两个单点初始分布出发，得到

\[
 \sum_k |(P^N)_{ik}-(P^N)_{jk}|\le2q^{\lfloor N/2\rfloor}.
\]

对取值落在 \([a,b]\) 的观测量 \(f\)，还有

\[
 |(P^2f)_i-(P^2f)_j|\le q(b-a).
\]

Lean 对应 `DoeblinMixing.lean`。这些混合界可复用，不过本问题的三连计数还有下面这条更短的证明。

## 三连计数直接化为独立停留指示量

实际矩阵满足 \(P_{ii}=1/d\)。令 \(H_t=\mathbf1_{X_{t+1}=X_t}\)。每给定一段过去，下一步停留的概率仍是同一个数 \(p=1/d\)，所以各 \(H_t\) 独立同分布。这里不只写了条件概率说明：`HoldingFlags.lean` 精确计算了每个有限模式的质量，得到

\[
 \sum_{\text{path}:H=b}\operatorname{weight}(\text{path})
 =\prod_t p^{b_t}(1-p)^{1-b_t}.
\]

任意只依赖停留模式的函数，包括尾事件和指数矩，都已经证明可以用此恒等式换成有限 Bernoulli 乘积加权和。

三连同标号的指标恰为 \(H_tH_{t+1}\)。偶数起点与奇数起点分别由不相交的停留指示量对组成。Lean 用每次剥离两位的有限求和直接证明每组的中心化矩母函数等于 Bernoulli\((p^2)\) 矩母函数的幂，再使用 Mathlib 的单变量 Hoeffding 引理和有限 Chernoff 界，避免另建无限 Markov 过程。

将一个长度 \(L\ge3\) 的闭路词切开只删去两个跨切口的三连。中心也只删去 \(2p^2\)，故中心化统计的误差至多为 \(2\)。闭合边的权重至多为 \(2/d\)；对起点求和后，闭路坏质量至多是均匀初始开放路径坏质量的两倍。因此，当 \(\varepsilon\ge0\) 且 \(\varepsilon L\ge4\) 时，已核验

\[
 \sum_f\mathbf1_{|b(f)-L/d^2|\ge\varepsilon L}
       \operatorname{weight}(f)
 \le 8\exp\!\left(-\frac{\varepsilon^2(L-2)}8\right).
\]

这里 \(b(f)\) 的定义就是沿循环后继求和的三连计数；`InternalTripleStatistic.lean` 又把它精确对应到实际内部规定弧集的“同时有入弧和出弧的顶点数”。`BalancedTripleConcentration.lean` 证明限制到平衡词后的坏质量仍满足同一个上界。

## 平衡条件化和正指数修正

设 \(W_m\) 为平衡闭路词的总权重，\(B_m\) 为坏词权重，\(R_{d,m}\) 为实际计数公式中的阶乘前因子。精确转移公式与第一猜想所用的已证渐近给出

\[
 R_{d,m}W_m=\frac{\mathbb E H(T\circ T_m)}{\nu_{dm}}
 \longrightarrow a(T)>0.
\]

因此无需另建一个条件概率下界：直接写

\[
 \frac{B_m}{W_m}=\frac{R_{d,m}B_m}{R_{d,m}W_m}.
\]

分子中的 \(R_{d,m}\) 至多多项式增长，指数坏质量将它吸收；分母趋于严格正数。于是 \(B_m/W_m\to0\)，这条实际条件集中已在 `BalancedTripleConditional.lean` 中闭合。

由于 \(L=dm\)，中心 \(L/d^2\) 对应 \(b/m\to1/d\)。同时 \(0\le b/m\le d\)，所以正指数 \(e^{b/m}\) 在整个样本空间都有共同上界 \(e^d\)。有限加权和的“好集用连续性、坏集用共同上界”估计于是给出

\[
 \frac{\sum_{f\text{ balanced}}\operatorname{weight}(f)e^{b(f)/m}}
      {\sum_{f\text{ balanced}}\operatorname{weight}(f)}
 \longrightarrow e^{1/d}.
\]

Lean 对应 `FiniteWeightedAverages.lean` 与 `BalancedTripleExponential.lean`。后者使用的是原问题需要的正指数修正；样本空间随 \(m\) 增大变化，论证仍是明确的有限加权求和，没有把所求极限列为假设。

最后，`TiltedCycleTransfer.lean` 通过真实根标号和纤维重数把这个均值接回 Hamilton 圈有限和。`UniformRegularTorusProof.lean` 证明的相关边包含概率估计再给出真实正则块内层极限 $e^{1/d}\rho(T)$。先固定 $d$ 完成这一步，随后才沿奇数 $d$ 求外层极限；路径伴随命题和闭式单调性不属于这里的结论。
