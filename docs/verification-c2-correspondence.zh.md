# 猜想 2：原命题与 Lean 形式化的独立对应复核

本记录核对的是源码中实际定义的含义、渐近量词和证明链，并非以“能够编译”代替数学对应检查。复核对象是 `ConjectureTwoProof.lean` 及其实际有限概率模型、计数、Fourier、Gaussian 和浓度依赖。当前结论：未发现导致形式化偏离原猜想 2 的实质缺口。

## 原命题和两个极限

[原论文](https://arxiv.org/html/2610.16245v1#S1) 的猜想 2 是：沿奇数阶 \(d\)，\(\rho_{\mathcal R}(R_d)\) 的极限存在。这里 \(\mathcal R\) 表示把各内部块独立地取为均匀正则竞赛图，\(\rho_{\mathcal R}\) 已经包含固定底图、再令内部奇数阶趋于无穷的内层极限。

Lean 中使用

\[
d_j=2j+3,\qquad m_k=2k+1,\qquad
\nu_N=\frac{(N-1)!}{2^N}.
\]

最终 `conjectureTwo` 明确要求存在实数序列 \(r_j\)，使得

\[
\forall j,\quad
\lim_{k\to\infty}
\frac{\mathbb E[H(\mathcal R(R_{d_j},m_k))]}{\nu_{d_jm_k}}
=r_j,
\qquad
\lim_{j\to\infty}r_j=\frac{\cosh 1}{\cos 1}.
\]

因此它既证明了原命题的极限存在，还给出确切值。内层始终固定 \(d_j\)；没有把两个极限交换，没有以同时增长的对角序列代替迭代极限。外层略去 \(d=1\) 只是略去有限前缀，不改变奇数阶无穷远极限。

## 实际概率律和计数约定

`FiniteModel.Orientation m` 给每个无序顶点对分配一个 Boolean；每个有标号竞赛图恰好出现一次。`RegularBlock` 使用实际邻接矩阵的正则度数条件。`RegularSample d m` 是各块均匀正则竞赛图子类型的乘积，`expectedRegularCycles` 对这个有限乘积空间做精确有理数平均。奇数阶 carousel 提供非空见证；平均分母不会为零。

`RegularConditioning.expectedRegularCycles_eq_conditional` 另外验证：这个乘积平均等于独立公平边模型在“每一块均正则”事件上的条件期望。因此这里没有把正则块内部仍当作独立公平边，也没有使用一个任意测试函数替代真实 Hamilton 圈数。

`hamiltonCycleCount` 数的是只有一个轨道、且每一步均沿实际弧的 successor permutation。一个有向圈对应一个 successor，旋转起点已经识别；不再额外除以顶点数。对 \(N\ge3\)，共有 \((N-1)!\) 个可能的有向 successor 圈，每个圈在独立公平竞赛图中出现的概率为 \(2^{-N}\)。这与 `cycleNormalizer N` 完全一致。反向圈是另一个有向对象，不应再除以二。

`regularCarouselNormalized d k` 的分母确为 \(\nu_{d(2k+1)}\)，而不是 \(\nu_d\)、\(\nu_{2k+1}\) 或路径正规化常数。

## 统一指定边估计的合法性

`LegalPartialPermutationArcs D` 同时要求无自环、源点映射在 \(D\) 上单射、终点映射在 \(D\) 上单射、没有相反方向的边对。真实 Hamilton successor 在每个内部块诱导的 `internalCycleArcSet` 满足这些条件；`internalCycleArcSet_legal` 已从 successor 双射和总阶至少三证明它们。

这些条件允许若干有向路径及长度至少三的有向圈。解析估计因此比只处理路径森林更强，足够覆盖真正出现的全部内部限制；没有把“能嵌入指定森林”作为未证前提。

`UniformRegularContainmentAsymptotic` 给出同一个 \(\varepsilon_k\to0\)，同时控制 \(m_k\) 阶的所有合法 \(D\)：

\[
\left|
2^{|D|}\,\Pr_{\rm reg}(D)\,
e^{-b(D)/m_k}-1
\right|\le\varepsilon_k,
\]

其中 \(b(D)\) 是同时具有内部入边和出边的顶点数。误差独立于 \(D\)，边数可以随 \(m_k\) 线性增长。后续先固定底图阶 \(d\)，再相乘得到 \((1\pm\varepsilon_k)^d\)；没有误用只对固定有限边集成立的点态估计。

## 正号和修正常数的独立核算

令 \(a=|D|\)，\(L\) 为实际边关联向量构成的 Laplacian，\(b=b(D)\)，\(u\) 为实际出入不平衡向量。有限恒等式是

\[
\operatorname{tr}L=2a,\qquad
\|u\|^2=2(a-b).
\]

Gaussian 行列式修正的一阶项为 \(+a/m\)，虚指数线性相位的 Fourier 积分贡献 \(-(a-b)/m\)。两者相加恰为 \(+b/m\)。共同四次项贡献 \(e^{-1/2}\)，在指定边分子和空边集分母中相消。因此条件概率的主项是

\[
2^{-a}e^{+b/m},
\]

符号为正，也没有遗留额外 \(e^{-1/2}\)。这与已证明的真实 Fourier 比和 `independentTiltedBlockWeight` 一致。

有限组合桥把 \(\sum_i b(D_i)\) 精确对应到循环底图词中连续三个相同字母的位置数。实际临界 Markov 转移的自环概率恒为 \(1/d\)，相邻两次自环的概率为 \(1/d^2\)。长度 \(dm\) 的词中，该统计量除以 \(m\) 的极限为 \(1/d\)，所以正则块修正是 \(e^{+1/d}\)。形式化还处理了平衡占用条件和循环首尾位置，并通过浓度及有界性证明指数期望的收敛；没有直接把指数的期望替换为期望的指数。

## 周期峰和体积常数

真实度数系数首先写为完整 \((\mathbb R/\mathbb Z)^m\) 上的归一化 Haar 积分。奇数 \(m\) 时，中心化被积函数逐坐标以一为周期，且在同时平移全部坐标时不变。`RegularFourierAnchoring` 用 Haar 平移和 Fubini 精确去掉共同平移方向；物理角 \(\theta=\pi x\) 的 Jacobian 是 \(\pi^{-(m-1)}\)。

主峰窗口是每个坐标到最后锚点的圆距离不超过 \(m^{-3/8}/(2\pi)\)。十六个圆中心的有限覆盖、非空离群点分支和全部好点但仍在主峰之外的分支覆盖了整个补集。`RegularNoncentralTail` 控制的是这个实际补集的范数积分，误差对所有合法 \(D\) 一致。因而没有只取某个实角立方体中的单一代表峰而漏算周期峰，也没有额外乘或漏乘 \(2^{m-1}\)、\(m\) 或平移方向的体积。

完整积分的归一化使用

\[
\frac{V_m}{\pi^{m-1}},\qquad
V_m=\frac{(\sqrt{2\pi})^{m-1}}{(\sqrt m)^{m-2}},
\]

它是实际锚定完整图 Gaussian 精度矩阵的积分，而非仅保留指数阶的近似量。

## 最终无条件证明链及范围

当前链条为：实际有限正则期望 → 精确内部指定边概率乘积 → 已证明的一致 Fourier/Gaussian 概率估计 → 真实循环三连统计的正指数倾斜 → 固定正则底图的内层极限 → carousel 的确切行列式常数 → 外层 \(\cosh 1/\cos 1\)。

`ConjectureTwoProof.uniformRegularContainmentAsymptotic`、`tendsto_regularCarouselNormalized` 和 `conjectureTwo_proof` 均没有模型极限、主峰公式或尾界假设。中间的条件归约定理仍然保留，便于说明证明结构；最终定理已经用实际证明消除了这些输入。

未发现需要留作 C2 前提的数学缺口。应区分的是：本结论是原猜想 2 的 Hamilton **圈**版本；论文另外提出的路径版本，以及猜想 3、4、5，并不由本定理自动得到。阅读一般条件归约时，也应将其明示接口与最终无条件应用区分：这些输入已经由实际模型的证明消除，而不是新增的公理。
