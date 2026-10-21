# 猜想 6：与 Lean 步骤对应的简洁证明

设正则竞赛图有 $d\ge3$ 个顶点，邻接矩阵为 $A$。记

$$S=2A+I-J,\quad C=S/d,\quad z=2/d,\quad U=(I-C)^{-1},\quad q=\det(I-C).$$

原问题使用的函数是

$$K(y)=\det\bigl(I-(A+\tfrac12I)\operatorname{diag}y\bigr),\qquad
h(y')=-K_0(y')/K_1(y'),$$

其中 $K(y',t)=K_0(y')+tK_1(y')$。角函数和 Hessian 为

$$f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}}),\qquad H=\nabla^2 f(0).$$

这里保留原始行列式、实际消元函数、主值复对数和实角变量求导，不能用一个候选矩阵重新定义 $H$。下面只需要一次有限行列式展开，再使用通常的链式法则；无需对矩阵逆函数求两次导数。

## 1. 先保证原定义在临界点附近合法

竞赛图和正则性给出

$$C^T=-C,\qquad C\mathbf1=0,\qquad \mathbf1^TC=0,\qquad
\|C\|_F^2=(d-1)/d<1.$$

特别地，$I\pm C$ 可逆，$U\mathbf1=\mathbf1$、$\mathbf1^TU=\mathbf1^T$，且 $q\ne0$。这些结论都由实际邻接矩阵推导。

令 $v_j=(A+\tfrac12 I)e_j$。在临界点只改变一个坐标时，行列式的精确公式为

$$\boxed{K(z\mathbf1+a e_j)=-qa/2.}$$

因此 $K(z\mathbf1)=0$，所有一阶偏导均为

$$\boxed{K_j(z\mathbf1)=-q/2=:r\ne0.}$$

由于行列式对每一列分别线性，$K$ 对最后一个变量仿射，且 $K_1(z,\ldots,z)=r\ne0$。在这个系数不为零的邻域，$h=-K_0/K_1$ 是解析函数，满足原方程 $K(y',h(y'))=0$，并且 $h(z,\ldots,z)=z>0$。连续性保证再缩小邻域后，$h$ 的值落在复对数的解析分支域中；因此原角函数可合法求两次导数。

## 2. 两个坐标的精确展开给出全部二阶数据

对任意 $j,k$，包括 $j=k$，有

$$\boxed{
K(z\mathbf1+a e_j+b e_k)
=q\left[-\frac{a+b}{2}+\frac{ab}{2}
\big((Uv_j)_j+(Uv_k)_k-(Uv_k)_j-(Uv_j)_k\big)\right].}$$

这个公式只是一个三阶行列式计算：把原矩阵写成

$$I-C-J/d-av_je_j^T-bv_ke_k^T,$$

以 $I-C$ 为可逆部分，对后面三个秩一项应用
$\det(D+FG)=\det D\det(I+GD^{-1}F)$。利用 $U\mathbf1=\mathbf1$ 和
$\mathbf1^TUv_j=d/2$，右侧成为一个明确的 $3\times3$ 行列式。展开即可得到上式。$j=k$ 时交叉系数为零，与每个坐标分别仿射一致。

所以

$$K_{jk}(z\mathbf1)=\frac q2
\big((Uv_j)_j+(Uv_k)_k-(Uv_k)_j-(Uv_j)_k\big).$$

令 $P=C+J/d$。因为 $v_j=(d/2)Pe_j$，且

$$UP=U-I+J/d,$$

引入对数坐标的代数导数

$$F_j=zK_j=-q/d,\qquad F_{jk}=z^2K_{jk}+\delta_{jk}zK_j,$$

即可整理成

$$\boxed{F_{jk}=\frac qd\big(U_{jj}+U_{kk}-U_{jk}-U_{kj}-2+\delta_{jk}\big).}$$

Lean 通过多项式代入、偏导与取系数证明这些等式。随后再证明多项式偏导确实等于其复求值函数的实际 Fréchet 导数，避免把代数符号直接当作解析导数。

## 3. 对原隐式方程求导，识别实际 Hessian

记 $p=d$ 为被消去的坐标，$w(\theta)=h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})$。对

$$K(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}},w(\theta))=0$$

在原点求导。所有 $K_j=r$，所以

$$r(iz+w_j)=0,\qquad w_j=-iz.$$

再求一次导数。令

$$\Delta K_{jk}=K_{jk}-K_{jp}-K_{pk}+K_{pp}.$$

角坐标的一阶导数为 $iz$，二阶导数为 $-z$，因而

$$0=-z^2\Delta K_{jk}+r(w_{jk}-z\delta_{jk}),\qquad
w_{jk}=z\delta_{jk}+\frac{z^2}{r}\Delta K_{jk}.$$

由于 $w(0)=z>0$，实际主值复对数的链式法则给出

$$H_{jk}=\frac{w_{jk}}z-\frac{w_jw_k}{z^2}
=1+\delta_{jk}+\frac zr\Delta K_{jk}
=\frac{F_{jk}-F_{jp}-F_{pk}+F_{pp}}{F_p}.$$

这里的 $+1$ 来自 $(-iz)^2=-z^2$，不能漏掉。将第 2 节的有限公式代入，令

$$Q=U+U^T-I=(I+C^2)(I-C^2)^{-1},\qquad
E=(e_1-e_d,\ldots,e_{d-1}-e_d),$$

便得到

$$\boxed{H_{jk}=Q_{jk}-Q_{jp}-Q_{pk}+Q_{pp},\qquad H=E^TQE.}$$

这一连接是证明的核心：左侧是原函数的实际二阶导数，右侧才是可以用有限线性代数处理的矩阵。

## 4. 正定性、行列式及有理平方

反对称性给出 $x^TC^2x=-\|Cx\|_2^2$。Cauchy–Schwarz 与第 1 节的 Frobenius 界保证 $I+C^2\succ0$。又

$$Q=U^T(I+C^2)U\succ0.$$

$E$ 的列线性无关，因此 $H\succ0$，特别地 $\det H>0$。

由于 $Q\mathbf1=\mathbf1$，将常数方向与其正交补分开，并使用
$E^TE=I+J$、$\det(E^TE)=d$，得到

$$\boxed{\mathcal H:=\det H=d\det Q
=d\frac{\det(I+C^2)}{\det(I-C^2)}.}$$

最后由转置不改变行列式，

$$\det(I-C^2)=\det(I+C)^2,\qquad
\det(I+C^2)=\det(I+iC)^2.$$

有理多项式 $p(t)=\det(I+tC)$ 满足 $p(t)=p(-t)$，所以 $p(i)$ 仍是有理数。因此

$$\boxed{\frac d{\mathcal H}
=\left(\frac{\det(I+C)}{\det(I+iC)}\right)^2\in\{a^2:a\in\mathbb Q\}.}$$

结合 $\mathcal H\ne0$，这就是原猜想 6。若还需要明确的正根公式，反对称标准块上的因子分别为 $1+\lambda^2$ 和 $1-\lambda^2$，而 $|\lambda|<1$；两个行列式均为正，所以该比值就是正平方根。

三顶点例子给出 $H=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}$、$\mathcal H=3/4$、$d/\mathcal H=4$，可用于核对归一化与符号。

## 对应的形式化模块

| 数学步骤 | Lean 模块 |
|---|---|
| 实际竞赛图、正则性、符号矩阵与平方和 | `Definitions`、`TournamentPositivity` |
| 原始行列式等于多项式求值、最后坐标严格仿射 | `AnalyticTarget`、`Elimination` |
| 临界点、共同非零偏导、实际消元系数非零 | `CriticalPoint`、`CriticalGradient` |
| 三阶行列式展开、取系数与实际一二阶偏导数据 | `TwoColumnDeterminant`、`AlgebraicJets`、`CriticalJets` |
| $U+U^T-I=Q$ 与代数 Hessian 矩阵 | `CriticalResolvent`、`JetToCandidate` |
| 真正的多项式、角坐标、复对数一二阶链式法则 | `AnalyticImplicit`、`AngleCalculus`、`ImplicitAlgebra` |
| 正定性、压缩行列式因子 $d$、有理平方 | `Positivity`、`Compression`、`CompressionDeterminant`、`RegularCandidate`、`RationalSquare` |

模块的存在不替代最终定理通过编译；原解析 Hessian 的最终组装与完整验收状态，以 [范围说明](../lean/README.zh.md) 和 `verification/lean-verification.json` 为准。这个证明不包含 Wormald 随机模型计数渐近，不能单独推出猜想 1 或猜想 2。
