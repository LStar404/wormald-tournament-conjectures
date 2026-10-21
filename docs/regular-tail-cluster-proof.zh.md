# 正则 Fourier 积分的非中心部分：有限圆覆盖路线

这条路线已在 Lean 中完成：`RegularNoncentralTail.lean` 证明了原正则度数 Fourier 被积函数的全部非中心部分，在正确 Gaussian 体积归一化下，一致趋于零。误差不依赖指定边集，适用于每个顶点至多一条入边、一条出边、没有环和反向边对的任意指定边集；边数可以随顶点数线性增长。它是原 Lemma 3 的非中心估计，主峰展开和最后条件概率比由其他模块处理。

把角度除以 \(\pi\)，在 \(\mathbb R/\mathbb Z\) 上工作。指定边集 \(D\) 的每个顶点至多关联两条无向边；固定边的复指数模为一，所以只需控制

\[
\prod_{\{i,j\}\notin D}|\cos(\pi(x_i-x_j))|.
\]

这里先除去了所有常数 \(2\) 因子。这个绝对值产品在每个坐标中都以一为周期。

## 有限覆盖及边界

取十六个中心 \(c_j=j/16\)。半径 \(1/16\) 的闭圆球覆盖整圆：对代表 \(y\in[0,1)\)，选 \(j=\lfloor16y\rfloor\) 即可。因而至少一个核心球含有 \(c\ge m/16\) 个顶点。

围绕同一个中心，取半径 \(3/16\) 的扩大球。设其中有 \(g\) 个好顶点，其余 \(r=m-g\) 个是离群点。对每个核心点 \(v\) 和离群点 \(u\)，三角不等式给出

\[
\operatorname{dist}(x_u,x_v)>3/16-1/16=1/8.
\]

闭球使边界点属于好集合；圆上没有漏掉的半开端点。好点可统一提升到中心左右 \(3/16\) 的实区间，任意两个实代表之差至多 \(3/8<1/2\)。因此好点之间的余弦为正，可以使用真正的实 Gaussian 比较。

取 \(q=\cos(\pi/8)\in(0,1)\)。每个离群点至少有 \(c-2\) 条没有被指定的核心边，所以核心与离群点之间的不同无向边提供因子

\[
q^{r(c-2)}\le\left(q^{\lfloor m/16\rfloor-2}\right)^r.
\]

核心和离群集合不相交，因此这些边不会重复计算，也与好点内部的边不相交。

## 保留正确量级的 Gaussian 体积

对好点内部使用 \(\cos t\le e^{-t^2/2}\)。删去的边最大度至多二，故

\[
\sum_{\{i,j\}\subseteq G,\,\{i,j\}\notin D}(y_i-y_j)^2
\ge (g-4)\sum_{i\in G}(y_i-\bar y)^2.
\]

这里没有把好点的体积粗估为一。按实际好点集的递增顺序重标号，删边图仍然是同一类有向部分置换。它的 Laplacian 正半定、消灭常向量、迹为两倍边数，且二次型至多为四倍平方范数。精确 Gaussian 换元与二阶矩估计给出：当 \(g\ge16\) 时，好点窗口的积分至多为

\[
\frac38 e^2 V_g,
\]

其中归一化圆坐标使用的体积是

\[
V_g=\sqrt g\left(\frac{2}{\pi g}\right)^{(g-1)/2}.
\]

因子 \(3/8\) 是共同平移坐标的区间长度；\(e^2\) 是指定边造成的一致 Gaussian 修正上界。令 \(r=m-g\)，则

\[
\frac{V_g}{V_m}
\le \left(\sqrt{\frac{\pi e}{2}}\sqrt m\right)^r,
\]

这个体积比较保留了每删去一个坐标的 \(\sqrt{2\pi}\) 因子。关键是每个离群点只损失 \(O(\sqrt m)\)，没有额外 \(C^m\) 体积损失。

按离群点的精确子集求和，至多有 \(\binom mr\le m^r\) 种；圆覆盖至多再乘十六。因此所有 \(r\ge1\) 的部分，相对主 Gaussian 量级至多为常数倍的

\[
16\cdot\frac38e^2\sum_{r=1}^m\binom mr
\left(\sqrt{\frac{\pi e}{2}}\,\sqrt m\,
q^{\lfloor m/16\rfloor-2}\right)^r=o(1).
\]

例如以 \(\binom mr\le m^r\) 放大后，这是首项趋零的几何级数。圆球可重叠，上式用并集上界，不要求唯一分区。全程保留原来的全部 Haar 概率坐标；投影到好点坐标保持概率测度，所以离群点坐标的积分恰为一。不必要求原来的锚点是好点，也不产生额外的锚点选择因子。当 \(m\ge256\) 时，每个非空覆盖单元自动有 \(g\ge16\)，故上述 Gaussian 估计始终适用。

## 没有离群点但仍不在主峰

当 \(r=0\) 时，所有点已在一个小实区间内，预先固定的锚点也在其中。取物理角尺度 \(R_m=m^{-3/8}\)，主峰要求每个点到最后锚点的圆距离至多 \(R_m/(2\pi)\)。Gaussian 尾界和 Cauchy–Schwarz 不等式给出这一分支的归一化误差至多

\[
6e^2\sqrt{2m\exp(-mR_m^2/32)}=o(1).
\]

对任何主峰以外的配置，有限圆覆盖必定给出两种情况之一：存在非空离群点覆盖单元，或全部坐标都落在某个好窗口但仍不属于主峰。两支相加即得到实际全部非中心部分的一致误差；复积分的范数也由同一个误差控制。

## 与 Lean 定理对应

- `RegularFourierAnchoring.lean`：真实完整 Haar 积分去掉共同平移，物理角换元的 Jacobian 精确为 \(\pi^{-(m-1)}\)。
- `GoodClusterRestriction.lean`、`GoodClusterCoordinates.lean`：实际好点删边图、能量重标号和概率 Haar 投影。
- `CircleLiftIntegration.lean`、`GoodClusterKernelVolume.lean`：圆窗口与实立方体的精确积分对应，以及上述好点 Gaussian 体积界。
- `GoodClusterCellBound.lean`：每个实际覆盖单元的范数积分上界。
- `OutlierClusterTail.lean`、`OutlierClusterRegion.lean`：全部非空离群点分支的一致尾界。
- `AllGoodClusterTail.lean`、`AllGoodRegionTail.lean`：全部好点、但仍在主峰以外的分支。
- `RegularNoncentralTail.regularNoncentral_uniform_small`：完整实际非中心范数积分一致趋零；`norm_regularNoncentralIntegral_div_volume_le` 给出可直接代入主峰证明的显式误差上界。
