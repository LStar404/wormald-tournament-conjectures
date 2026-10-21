# 内部规定弧集的高斯修正：不必重标号成路径森林

设 \(D\subseteq[m]\times[m]\) 无自环，每个顶点至多是一条弧的起点、至多是一条弧的终点。对弧 \(e=(a,b)\) 令

\[
 v_e=e_a-e_b,\qquad L_D=\sum_{e\in D}v_ev_e^T,
 \qquad h_D=\sum_{e\in D}v_e.
\]

令 \(s_i,t_i\in\{0,1\}\) 分别表示顶点 \(i\) 是否有规定出弧、入弧，\(j(D)=\#\{i:s_i=t_i=1\}\)。只需下面四行有限恒等式：

\[
\begin{aligned}
 x^TL_Dx&=\sum_{(a,b)\in D}(x_a-x_b)^2
 \le2\sum_D(x_a^2+x_b^2)\le4\sum_i x_i^2,\\
 \operatorname{tr}L_D&=2|D|,\\
 h_D&=s-t,\qquad \sum_i(h_D)_i=0,\\
 \|h_D\|^2&=\sum_i(s_i-t_i)^2=2|D|-2j(D).
\end{aligned}
\]

第一行也直接给出半正定性；最后一步使用起点、终点在弧集上的单射性。没有必要先把弧集分解、重标号成路径森林。即使存在有向环组件，这些式子仍成立。

`PartialPermutationLaplacian.lean` 从实际 \(D\) 构造 `GaussianGraphData`，逐项证明全部字段，包括 \(|D|\le m\)。`PartialPermutationShift.lean` 另证明

\[
 L_D\mathbf1=0,\qquad h_D^T\mathbf1=0,
 \qquad (x+c\mathbf1)^TL_D(x+c\mathbf1)=x^TL_Dx,
\]

因此完整高斯积分和锚定坐标积分之间所需的平移不变性也有实际对象的证明。

对于原模型的 Hamilton 后继置换 \(\sigma\)，第 \(i\) 块的规定弧集精确定义为

\[
 D_i=\{(a,b):\sigma(i,a)=(i,b)\}.
\]

置换的函数性、单射性分别给出起点与终点唯一性；总阶至少三的单轨置换没有不动点，故无自环。于是 `internalCycleGaussianGraphData` 无条件实例化上述有限数据。沿实际循环顶点顺序 \(e\) 求和时，`InternalTripleStatistic.lean` 证明

\[
 \sum_i j(D_i)
 =\#\{t: (e_t)_1=(e_{t+1})_1=(e_{t+2})_1\}.
\]

右边就是已经证明平衡条件集中和正指数均值极限的循环三连计数。

通用高斯计算把行列式因子和不平衡相位因子合并为

\[
 g_D(r)=-\frac12\log\det(I-rL_D)
 -\frac r2 h_D^T(I-rL_D)^{-1}h_D.
\]

`GaussianGraphCorrection.lean` 的统一误差为

\[
 |g_D(r)-rj(D)|\le16r^2|D|\qquad(0\le r\le1/8).
\]

取 \(r=1/m\) 后，主项是正号 \(j(D)/m\)，误差至多 \(16/m\)。这解释了正则模型修正中 \(e^{+b/m}\) 的来源，并准确连接到 \(e^{1/d}\) 的平衡词均值极限。
