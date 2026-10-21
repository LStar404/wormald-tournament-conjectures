# 所有点同属好圆弧时的窗口外积分

固定奇数阶 \(m\)，令 \(D\) 是无环、无反向弧对、每点入出度至多一的真实规定弧集。将所有点限制在同一个半径 \(3/16\) 的好圆弧中，并用圆心的中心提升写成 \(x_i\in[-3/16,3/16]\)。两点提升之差的绝对值至多 \(3/8<1/2\)，所以圆距离恰等于提升之差的绝对值。

自由弧上的余弦因此满足

\[
\left|\prod_{\text{自由边}}\cos\pi(x_i-x_j)\right|
\le\exp\!\left(-\frac{\pi^2}{2}
                 \sum_{\text{自由边}}(x_i-x_j)^2\right).
\]

右侧是删去 \(D\) 对应无向边后的实际 Gaussian 核。它的精确矩阵为 complete-graph quotient precision 减去 \(D\) 的 Laplacian，没有以任意图替代真实内部弧集。

取末点为锚，主峰窗口为

\[
\operatorname{dist}(x_i,x_{\rm last})\le r/(2\pi)
\quad\text{对全部 }i.
\]

在好圆弧提升中，其补集精确对应
\(\|\pi(x_i-x_{\rm last})\|_\infty>r/2\)。公共平移变量只遍历长度 \(3/8\) 的区间，因此积分至多增加因子 \(3/8\)。这一步允许窗口外指示函数；证明明确检查了拉回函数的可积性，不假设指示函数连续。

将锚定 Gaussian 核精确运输到 \(m\) 个独立标准正态变量后，规定弧集只留下权重 \(w_D\)，且已证明

\[
\mathbb E|w_D|^2\le e^4.
\]

窗口外事件的 Gaussian 概率至多

\[
\tau_m(r)=2m\exp(-mr^2/32).
\]

Cauchy–Schwarz 直接给出加权窗口外质量至多 \(e^2\sqrt{\tau_m(r)}\)。所以一个好圆弧窗口的实际原积分满足

\[
\frac{\int_{\text{好圆弧}\setminus\text{主峰窗口}}|N_D|}
 {V_m/\pi^{m-1}}
\le\frac38e^2\sqrt{\tau_m(r)}.
\]

对十六个圆心求并集，固定重叠代价给出

\[
\frac{\int_{\text{所有好圆弧内、主峰外}}|N_D|}
 {V_m/\pi^{m-1}}
\le6e^2\sqrt{\tau_m(r)}.
\]

最后取 \(r=m^{-3/8}\)，则 \(mr^2=m^{1/4}\)，故右侧趋零。这个界对全部合法 \(D\) 一致。

Lean 对应模块为 `MeasurableGaussianBoxAnchor`、`GaussianOutsideAnchor`、`AllGoodClusterTail` 和 `AllGoodRegionTail`。最后一个模块给出实际可测区域的积分界及对全部合法弧集一致的小量接口，负责全局尾部证明中的零 outlier 情形。
