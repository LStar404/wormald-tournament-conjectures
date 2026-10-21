# 任意幂矩比较：一条可直接核对 Lean 的短证明

本节证明论文第二部分所需的矩比较与等号下降。它不把 Fang–Huang 的比较定理当作额外假设，也不靠检验有限阶矩阵代替一般证明。记 \(T_n\) 为上三角全为 \(1\)、下三角全为 \(-1\)、对角为 \(0\) 的矩阵。

**定理。** 若实矩阵 \(A\) 满足 \(A^T=-A\) 且 \(|a_{ij}|\le1\)，则对每个自然数 \(p\)，

\[
 \|A^p\|_F^2\le\|T_n^p\|_F^2.
\]

奇数阶 carousel 的符号矩阵与 \(T_n\) 有相同的全部幂矩。因此，对原论文的归一化矩阵 \(C=S/n\)，全部幂矩同样由实际 carousel 的相应矩控制。这里不要求 \(A\) 正则；正则性只在后续极值同构分类中使用。

## 1. 一步比较只需两两差值和重排

令 \(x^*\) 为 \((|x_i|)\) 的递减排列。给定 \(r\) 个位置组成的集合 \(E\) 和符号 \(\varepsilon_i\in\{\pm1\}\)，先设 \(x\ge0\)。反对称性和 \(|a_{ij}|\le1\) 给出

\[
 \sum_{i\in E}\varepsilon_i(Ax)_i
 \le r\sum_{j\notin E}x_j+
 \frac12\sum_{i,j\in E}|\varepsilon_i x_j-\varepsilon_jx_i|.
\]

令 \(z_i=\varepsilon_i x_i\)，内部绝对值等于 \(|z_i-z_j|\)。把 \(z\) 递减排列后，

\[
 \frac12\sum_{i,j}|z_i-z_j|
 =\sum_{i=0}^{r-1}(r-1-2i)z_i
 \le\sum_{i=0}^{r-1}c_{r,i}(x|_E)^*_i,
\]

其中 \(c_r=(r-1,r-1,r-3,r-3,\ldots)\)。将这些权重与外部的 \(n-r\) 个权重 \(r\) 合并，再作一次重排，得到

\[
 \sum_{i\in E}|(Ax)_i|\le\sum_j w_{r,j}x_j^*,\qquad
 w_r=(\underbrace{r,\ldots,r}_{n-r},r-1,r-1,r-3,r-3,\ldots).
\]

任意实输入可先用对角符号矩阵把它变成非负输入；同时对 \(A\) 作同一符号切换，反对称性和元素界仍成立。取 \(E\) 为输出绝对值最大的 \(r\) 个位置，便得到一般一步弱主序。

Lean 对应：`MomentComparison`、`PairDistance`、`ComparisonWeights`、`MergeWeights`、`OneStepComparison`。所有集合、排序、符号切换与重索引均已逐项证明。

## 2. 比较矩阵与平方范数不需要积分论证

定义 \(K_{ij}=w_{i+1,j}-w_{i,j}\)，采用从 \(0\) 开始的指标。它正是关于反对角线分为“全 \(1\)、零、交替符号”的对称矩阵。其前 \(r\) 行之和为 \(w_r\)，所以刚才的一步界就是

\[
 (Ax)^*\prec_w Kx^*.
\]

每个 \(w_r\) 非负且递减。Abel 求和因此证明：若 \(u\prec_w v\)，则对任意非负递减权重 \(b\)，

\[
 \sum_i b_i u_i\le\sum_i b_i v_i.
\]

由对称性，\(K\) 的行前缀也等于 \(w_r\)。对行前缀应用同一个加权不等式，立即得到：\(K\) 把非负递减向量送到非负递减向量，并保持弱主序。

现在设 \(u,v\) 非负递减且 \(u\prec_w v\)。取权重 \(b=u+v\)，交叉项直接消去，得到

\[
 \sum_i u_i^2\le\sum_i v_i^2.
\]

若两边相等，再取权重 \(b=u\)，则 \(\sum_i u_i v_i\ge\sum_i u_i^2\)，从而

\[
 0\le\sum_i(v_i-u_i)^2
 =2\sum_i u_i^2-2\sum_i u_iv_i\le0.
\]

故取等当且仅当 \(u=v\)。这给出本证明需要的严格平方范数比较，省去了额外的凸函数定理和积分等号分析。

Lean 对应：`PrefixDominated`、`ComparisonMatrix`、`ComparisonMatrixEntries`、`ComparisonCone`。

## 3. 迭代与等号下降

反复应用一步界和 \(K\) 的保序性，得到

\[
 (A_0A_1\cdots A_{m-1}x)^*\prec_w K^m x^*.
\]

当 \(n\ge2\) 时，还可证明：\(u\prec_w v\) 且 \(Ku=Kv\) 蕴含 \(u=v\)。证明只用前缀差非负、\(K\) 的前两行和从右到左消元；没有误用奇数阶矩阵的可逆性。因此完整乘积取等会强制每个后缀取等。

特别地，若 \(\|A^p x\|_2^2=\|K^p x^*\|_2^2\)，则排序向量取等，并且所有 \(q\le p\) 均有

\[
 (A^q x)^*=K^q x^*.
\]

Lean 对应：`ComparisonPowers`、`ComparisonStrictness`、`ComparisonEquality`、`ComparisonProducts`。原始 [Fang–Huang 第 3 节](https://arxiv.org/html/2608.06238v1#S3) 的一般乘积与后缀结论在这里已被独立重证。来源 Lemma 3.2 的最后一句在 \(n=1\) 有边界问题：\(K_1=0\) 不具有所声称的可比向量单射性；形式化明确使用 \(n\ge2\)，论文目标 \(d\ge3\) 不受影响。

## 4. 把比较界准确换回传递矩阵与 carousel

设 \(R\) 反转指标，\(D\) 的对角符号交替为 \(1,-1,\ldots\)，并按“偶指标递增、奇指标递减”重新排列。逐项计算给出 \(DKR\) 在此排列下恰为 \(T_n\)。由 \(K^T=K\) 得到 \(T_nT_n^T\) 与 \(K^2\) 的带符号置换共轭，因此它们的任意次幂也共轭，首个基向量保持不动。

此外，传递矩阵在一个带符号循环移位下不变，所以其每个次幂的对角元相同。故对每个基向量 \(e_j\)，

\[
 \|A^p e_j\|_2^2\le\|K^p e_0\|_2^2
 =\|T_n^p e_0\|_2^2
 =\|T_n^p e_j\|_2^2.
\]

对列求和即得开头的全部幂矩比较。奇数阶 carousel 的实际符号矩阵又是 \(T_n\) 的带符号置换共轭，所以可精确换成 carousel 参照。最后乘以正的归一化因子 \(n^{-2p}\)，得到原论文矩阵 \(C=S/n\) 的相应结论。

若全矩在某个 \(p\ge2\) 取等，每列的非负亏损都为零；由等号下降可取 \(q=2\)，因而

\[
 \operatorname{tr}(S^4)=\|S^2\|_F^2
 =\|T_n^2\|_F^2=\operatorname{tr}(T_n^4).
\]

Lean 对应：`ComparisonTransitive`、`ComparisonGram`、`TransitiveMoments`、`MomentBound`、`MomentEquality`、`SwitchingMoments`、`NormalizedMoments`。最后一个模块直接陈述真实 `Tournament.realNormalizedSign` 的全部矩比较及等号归约；不需要把待证矩界作为参数。

这些结果完成矩比较这一环。非正则实际期望衰减、普通同构意义下的谱极值分类及实际独立块计数渐近现均已证明，见[谱常数极值](spectral-extremum.zh.md)和[分析连接](local-counting-analysis.zh.md)。`ConjectureOneProof` 已将这些环节接成原猜想 1 的无条件证明；有限矩比较本身不承担计数渐近的替代作用。
