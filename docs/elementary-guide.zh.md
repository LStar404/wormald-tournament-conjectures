# 从微积分和线性代数理解Wormald竞赛图模型

刘星辰。2026年10月21日，公开研究稿的配套基础讲解。

本篇从基本微积分和线性代数出发，解释主文的Hessian计算、行列式比值和随机块模型。主文讨论的是模型期望，其一般推导仍待独立数学审阅。

## 1. 必须先分清两个大小

全文以奇数$d\ge3$为基图阶数，$m$为正整数块阶数。这里，竞赛图在任意两个不同顶点之间恰有一条有向边；出度是从该顶点发出的边数，入度是指向它的边数。

::: {.definition title="基图、块和总阶数"}

先取一个$d$顶点的基图。把每个基图顶点替换成$m$个顶点，得到

$$
N=dm.
$$

在独立内部块模型$\mathcal T$中，每一块的每一条边独立公平定向；在正则内部块模型$\mathcal R$中，每块在全部有标号正则竞赛图中均匀选取，各块之间独立，块内各条边不要求独立，块阶数必须为奇数。

块间所有边依照基图；块内部随机选择竞赛图。这里有两个不同参数：

- $d$是基图大小；
- $m$是每块大小，$N$是最后图的大小。

:::

原模型先固定$d$，再令$m\to\infty$。得到每个$d$对应的一个极限常数后，我们才研究$d\to\infty$。不能把这两个步骤直接交换。

## 2. 所研究的常数不是基图本身的路径数

下文$H(G)$表示图$G$的哈密顿路数；$\mathbb EX$表示随机量$X$的平均值。

$C(G)$表示图的圈数。

哈密顿路按有向顶点排列计数；哈密顿圈旋转起点仍是同一圈，不把反向排列再识别为同一有向圈。

$0!=1$；$n!=1\cdot2\cdots n$。

随机竞赛图在$N$阶的平均哈密顿圈数与路径数为

$$
\nu_N=\frac{(N-1)!}{2^N},\qquad
\mu_N=\frac{N!}{2^{N-1}}.
$$

我们考虑随机块模型的

$$
\frac{\mathbb E C}{\nu_N},\qquad \frac{\mathbb E H}{\mu_N}.
$$

主文第一部分第8节明确引用Wormald的计数定理，将我们随后算出的Hessian接到这些模型期望的极限；这里把这条概率渐近定理作为外部输入。后续的有限矩阵计算会验证该输入所要求的正则性及Hessian非退化条件。

例如三角形基图$d=3$本身有1个哈密顿圈，$\nu_3=1/4$，所以它的有限圈数比为4。但将它吹胀成大随机块后，圈期望比的极限为2。这两个量不同。

## 3. 正则基图的矩阵

上标$T$表示转置。

下文$I_r$是$r$阶单位矩阵，$J_r$是$r$阶全一矩阵，$\mathbf1_r$是全一列向量；省略下标时看乘法维数。

::: {.definition title="邻接矩阵与符号矩阵"}

正则表示每个顶点的出度、入度都为$(d-1)/2$。令$A$为邻接矩阵：当$i\to j$时$A_{ij}=1$，没有这条方向的边时$A_{ij}=0$，并且$A_{ii}=0$。定义

$$
S=2A+I-J,\qquad C=S/d.
$$

:::

单独写的$C=S/d$则是矩阵，二者按是否带图参数区分。

于是

$$
S^T=-S,\qquad S\mathbf1=0.
$$

把$2A+I$除以$d$，得到

$$
P=\frac{2A+I}{d}=\frac Jd+C.
$$

记$\mathbf1=(1,\ldots,1)^T$，令$u=\mathbf1/\sqrt d$。则$Pu=u$；若$v$与$\mathbf1$垂直，$Pv=Cv$。

因此把空间分成常数方向与零和方向：前者由全一向量张成，后者的坐标之和为0。

## 4. Hessian是什么

::: {.definition title="Hessian"}

先设$f(x_1,\ldots,x_r)$为二阶偏导连续的实值函数，$x$为实列向量。Hessian是二阶偏导数组成的矩阵：

$$
\nabla^2f=
\left(\frac{\partial^2f}{\partial x_j\partial x_k}\right)_{j,k=1}^r.
$$

:::

一阶导数列向量记为$\nabla f=(\partial f/\partial x_1,\ldots,\partial f/\partial x_r)^T$。多元Taylor公式写为

$$
f(x)=f(0)+\nabla f(0)^Tx+\frac12x^T\nabla^2f(0)x+\cdots.
$$

因此Hessian描述二次变化。在实值函数的驻点，一阶项为0；若此时Hessian正定，二次项沿每个非零实方向都为正。原文的角函数可能是复值函数，不能把上述实函数极小值直觉直接套用；我们将逐式算出它在原点的Hessian恰为实对称正定矩阵。

Wormald的模型常数写成$\sqrt{d/\mathcal H}$，其中$\mathcal H$是一个特定Hessian的行列式。关键任务就是把这个$\mathcal H$算清楚。

## 5. 为什么会出现一个由行列式决定的函数

$\operatorname{diag}(a_1,\ldots,a_r)$是所列元素组成的对角矩阵。

::: {.definition title="行列式函数与末变量"}

原文定义

$$
B(y)=I-(A+\tfrac12I)\operatorname{diag}(y_1,\ldots,y_d),
\qquad K(y)=\det B(y).
$$

在每个$y_j=2/d$时，

$$
B=I-\frac{2A+I}{d}=I-P.
$$

因为$P\mathbf1=\mathbf1$，$I-P$有常数零方向，所以$K=0$。我们在这个点附近，由$K=0$把最后一个变量写成

$$
y_d=h(y_1,\ldots,y_{d-1}).
$$

:::

::: {.lemma title="仿射行列式的显式消元"}

这里并不需要抽象地假定这个函数存在。行列式对每一列线性，所以

$y'=(y_1,\ldots,y_{d-1})$和$t'=(t_1,\ldots,t_{d-1})$表示删去最后一个坐标；这里的撇号不是求导。

$$
K(y)=K_0(y')+y_dK_1(y').
$$

这里$y'=(y_1,\ldots,y_{d-1})$，两个系数具体为

$$
K_0(y')=K(y',0),\qquad
K_1(y')=K(y',1)-K(y',0).
$$

只要$K_1$不为零，

$$
h(y')=-K_0(y')/K_1(y').
$$

记$q=\det(I-C)>0$。第8节将完整算出关键点的$K_1=-q/2\ne0$，因此$h$是一个明确的有理函数。

:::

## 6. 先改成对数变量，计算更容易

对数变量$t_j$允许取原点附近的复数，角变量$\theta_j$为原点附近的实数。

函数下标$F_j,F_{jk}$表示对第$j$个变量求一次偏导、对第$j,k$个变量求两次偏导。写出$K_{y_j}$时则明确按$y_j$求导。矩阵的导数逐元计算。

虚数单位满足$i^2=-1$。

$e_j$为只有第$j$个坐标是1的标准基列向量。

令$z=2/d$，写

$$
y_j=ze^{t_j}.
$$

原点$t=0$对应原关键点。于是矩阵变为

$$
\mathscr B(t)=I-P\operatorname{diag}(e^{t_j}).
$$

每求一次$t_j$导数，就只改变第$j$列：

$$
\mathscr B_j(0)=-Pe_je_j^T.
$$

这里$\delta_{jk}$在$j=k$时为1，否则为0。

二次导数为

$$
\mathscr B_{jk}(0)=-\delta_{jk}Pe_je_j^T.
$$

## 7. 把分块消元的矩阵乘法写出来

实向量的长度为$\|v\|_2=(\sum_jv_j^2)^{1/2}$。

全一向量记为$\mathbf1=(1,\ldots,1)^T$。令

$$
u=\mathbf1/\sqrt d,\qquad \Pi=I-uu^T.
$$

直接乘法给

$$
u^Tu=1,\qquad \Pi^2=\Pi,\qquad \Pi u=0.
$$

$u^\perp$为满足$u^Tv=0$的向量$v$组成的空间。

$\Pi v=v-u(u^Tv)$去掉了$v$的常数方向分量。选取$u^\perp$的一组正交单位基作为$V$的列，则

$$
V^TV=I_{d-1},\quad V^Tu=0,\quad VV^T=\Pi.
$$

分块式中的$a$为标量、$b$为$1\times(d-1)$行、$c$为$(d-1)\times1$列、$D$为$(d-1)$阶矩阵；这些局部块记号随$t$变化。

在正交基矩阵$(u,V)$中，原矩阵写成

$$
\begin{pmatrix}a&b\\c&D\end{pmatrix},
\qquad
a=u^T\mathscr Bu,\quad b=u^T\mathscr BV,\quad
c=V^T\mathscr Bu,\quad D=V^T\mathscr BV.
$$

::: {.lemma title="Schur消元恒等式"}

若$D$可逆，左乘下面的行消元矩阵：

$$
\begin{pmatrix}1&-bD^{-1}\\0&I\end{pmatrix}
\begin{pmatrix}a&b\\c&D\end{pmatrix}
=
\begin{pmatrix}a-bD^{-1}c&0\\c&D\end{pmatrix}.
$$

左边第一个矩阵的行列式为1。右边为分块三角矩阵，所以

$$
\det\mathscr B=\det D\,(a-bD^{-1}c).
$$

:::

::: {.proof title="可逆性与行列式的符号"}

记$\psi=a-bD^{-1}c$。在$t=0$时，

$$
\mathscr B(0)=\Pi-C,\quad a(0)=0,\quad b(0)=0,\quad c(0)=0,
$$

$$
D(0)=V^T(I-C)V.
$$

由于$C$反对称，若$(I-C)x=0$且$x$实，则

$$
0=x^T(I-C)x=\|x\|_2^2-x^TCx=\|x\|_2^2.
$$

这里$x^TCx=(x^TCx)^T=x^TC^Tx=-x^TCx$，故它为0。因此$I-C$无非零实零向量，可逆；其在零和空间上的限制也可逆。$\det D(0)\ne0$，邻域内$\det\mathscr B=0$等价于$\psi=0$。

第5节还用到了$q>0$，其符号可按实反对称矩阵的二维块核对。对任意实频率$\lambda$，

$$
J_\lambda=\begin{pmatrix}0&\lambda\\-\lambda&0\end{pmatrix},
\qquad
\det(I-J_\lambda)
=\det\begin{pmatrix}1&-\lambda\\\lambda&1\end{pmatrix}
=1+\lambda^2>0.
$$

正交基变换保持行列式，零块的因子为1，所有二维块的因子均正，故$q=\det(I-C)>0$。又$Cu=0$，常数方向的$I-C$因子恰为1；剩余块正是$D(0)$。因此$\det D(0)=q$，这也说明第8节的两个$q$来源相同。

:::

## 8. 一次与二次导数不省项

记$F_j=e_je_j^T$，$R=D^{-1}$。由

$$
\mathscr B_j(0)=-PF_j,\qquad
\mathscr B_{jk}(0)=-\delta_{jk}PF_j
$$

以及$u^TP=u^T$，有

$$
a_j(0)=u^T(-PF_j)u=-u_j^2=-1/d,
$$

$$
a_{jk}(0)=-\delta_{jk}/d.
$$

现在对乘积$bRc$求导，先列一次导数：

$$
\partial_j(bRc)=b_jRc+bR_jc+bRc_j.
$$

再对$t_k$求导，九项全部为

$$
\begin{aligned}
\partial_k\partial_j(bRc)
={}&b_{jk}Rc+b_jR_kc+b_jRc_k\\
&+b_kR_jc+bR_{jk}c+bR_jc_k\\
&+b_kRc_j+bR_kc_j+bRc_{jk}.
\end{aligned}
$$

因为原点$b=c=0$，第一、二、四、五、六、八、九项都为0，只剩

$$
\partial_k\partial_j(bRc)(0)
=b_j(0)R(0)c_k(0)+b_k(0)R(0)c_j(0).
$$

这也说明逆矩阵的导数项确实全部消失，没有被忽略。

把剩余两项逐个算出。由$P=uu^T+C$、$V^Tu=0$，

$$
b_j(0)=u^T(-Pe_je_j^T)V
=-\frac1{\sqrt d}e_j^TV,
$$

$$
c_k(0)=V^T(-Pe_ke_k^T)u
=-\frac1{\sqrt d}V^TCe_k.
$$

令$U=(I-C)^{-1}$。$C$保持零和空间，故$(I-C)V=VD(0)$。把这条等式左乘$U$再右乘$R(0)$：

$$
V=UVD(0),\qquad VR(0)=UV.
$$

由于$VV^T=\Pi$及$\Pi C=C$，接着有

$$
UC=U\Pi C=UVV^TC=VR(0)V^TC.
$$

这样，限制空间上的逆与完整空间中的逆之间的连接也已逐项列出。

于是

$$
b_j(0)R(0)c_k(0)
=\frac1d e_j^TVR(0)V^TCe_k
=\frac1d(UC)_{jk}.
$$

第二个保留下来的乘积也明确写为

$$
b_k(0)R(0)c_j(0)
=\frac1d e_k^TVR(0)V^TCe_j
=\frac1d(UC)_{kj}.
$$

把这两项从$a_{jk}$中减去，得到

$$
\psi_j(0)=-1/d,
$$

$$
\psi_{jk}(0)
=-\frac1d\bigl[\delta_{jk}+(UC)_{jk}+(UC)_{kj}\bigr].
$$

最后化简矩阵。因为$C$与$I-C$交换，也与其逆交换，

$$
UC=C(I-C)^{-1}.
$$

转置为

$$
(UC)^T=C^TU^T=-C(I+C)^{-1}.
$$

而

$$
\begin{aligned}
(I-C)^{-1}-(I+C)^{-1}
&=(I-C)^{-1}\bigl[(I+C)-(I-C)\bigr](I+C)^{-1}\\
&=2C(I-C)^{-1}(I+C)^{-1}\\
&=2C(I-C^2)^{-1}.
\end{aligned}
$$

因此

$$
UC+(UC)^T=2C^2(I-C^2)^{-1},
$$

$$
I+UC+(UC)^T
=(I-C^2+2C^2)(I-C^2)^{-1}
=(I+C^2)(I-C^2)^{-1}=Q.
$$

完整结果是

$$
\boxed{\psi_j(0)=-1/d,\qquad \psi_{jk}(0)=-Q_{jk}/d.}
$$

还要把第5节的$q$与偏导数算清楚。由于$I-C$在常数方向上是1，

$$
q:=\det(I-C)=1\cdot\det D(0)=\det D(0).
$$

第7节已经逐块计算：每个二维块对$\det(I-C)$贡献$1+\lambda^2>0$，零块贡献1，所以它为正。现在对$K(ze^{t_1},\ldots,ze^{t_d})=\det D(t)\psi(t)$求一次导数。在原点$\psi(0)=0$，故

$$
\partial_{t_j}K
=\partial_{t_j}(\det D)\,\psi+\det D\,\psi_j
=0+q(-1/d)=-q/d.
$$

另一方面，$y_j=ze^{t_j}$给

$$
\partial_{t_j}K(ze^{t_1},\ldots,ze^{t_d})\big|_{t=0}
=zK_{y_j}(z\mathbf1),
\qquad K_{y_j}(z\mathbf1)=-\frac{q}{dz}=-\frac q2\ne0.
$$

因此第5节的有理函数$h=-K_0/K_1$确实在关键点附近有定义。

## 9. 把最后一个变量消去后，导数怎样变化

::: {.definition title="消元后的对数函数"}

令$t'=(t_1,\ldots,t_{d-1})$。第8节已验证$K_1$在关键点非零，所以第5节的有理函数$h$在邻域内有定义，且$h(z,\ldots,z)=z$。缩小邻域，取在1处值为0的对数分支，定义

$$
g(t')=\log\left[\frac{h(ze^{t_1},\ldots,ze^{t_{d-1}})}z\right],
\qquad g(0)=0.
$$

这里不要求先学过复分析。“在1附近取值为0的对数”可以直接用基本幂级数定义：

$$
\log(1+w)=\sum_{n=1}^{\infty}\frac{(-1)^{n+1}}n w^n,\qquad |w|<1.
$$

本题$h/z$在原点等于1，连续性允许取足够小的邻域，使$w=h/z-1$落在$|w|<1/2$内。上面的级数在该闭圆盘上一致收敛，导数级数也在更小的圆盘上一致收敛，因此这里所用导数由逐项求导得到，并与实数附近的自然对数一致。

:::

::: {.proof title="完整链式求导"}

令$t_d=g(t')$。本节下列未写求值点的一、二阶导数，代入常数时都在$t'=0,\ t_d=0$求值；例如$g_j=-1$只表示原点处的值，不表示整个邻域中恒等于$-1$。指标满足$1\le j,k\le d-1$。对

$$
\psi(t_1,\ldots,t_{d-1},g(t'))=0
$$

求一次导数：

$$
0=\psi_j+\psi_dg_j,\qquad
g_j=-\frac{\psi_j}{\psi_d}=-1.
$$

再求一次，必须保留全部链式法则项：

$$
0=\psi_{jk}+\psi_{jd}g_k+\psi_{dk}g_j
+\psi_{dd}g_jg_k+\psi_dg_{jk}.
$$

代入$g_j=g_k=-1$，逐项整理为

$$
0=-\frac{Q_{jk}-Q_{jd}-Q_{dk}+Q_{dd}}d-\frac{g_{jk}}d.
$$

两边乘$d$并移项：

$$
g_{jk}=-Q_{jk}+Q_{jd}+Q_{dk}-Q_{dd}=-(e_j-e_d)^TQ(e_k-e_d).
$$

:::

::: {.theorem title="原点处的Hessian"}

原文的角函数为$\widetilde f(\theta)=\log z+g(i\theta_1,\ldots,i\theta_{d-1})$。两次求导带来$i^2=-1$，故其原点Hessian为：

$$
\mathbf H=E^TQE,\qquad E=(e_1-e_d,\ldots,e_{d-1}-e_d).
$$

:::

## 10. 为什么Hessian一定正定

$M\succ0$表示$M$实对称且$v^TMv>0$对每个非零实$v$成立。

::: {.proof title="正定性"}

$C$反对称，它的非零特征值成对为$\pm i\lambda$，这里的$\lambda$是归一化矩阵$C$的频率。本题有$|\lambda|<1$；A.2给出这个界的逐块证明，只用到第3节的矩阵定义，不依赖本节的Hessian正定结论。因此$Q$对应的实特征值为

$$
\frac{1-\lambda^2}{1+\lambda^2}>0.
$$

上式讨论的是非零频率；若$C$还有零特征值，相应$Q$特征值是$(1-0)/(1+0)=1$，也为正。实反对称矩阵的正交分块使$Q$成为实对称矩阵；所有块的系数均正，所以$Q$正定。对任意非零$v$，

$$
v^T\mathbf Hv=(Ev)^TQ(Ev)>0,
$$

因为$E$的列独立，所以$Ev\ne0$。这就证明原文担心的Hessian退化不会发生。

:::

## 11. 因子d从哪里来

::: {.corollary title="行列式中的因子d"}

$E$的列不是正交单位向量，其Gram矩阵为$E^TE=I_{d-1}+J_{d-1}$。把它换成零和空间的正交单位基时，行列式会多出因子$d$。完整计算见A.3；因此

$$
\mathcal H=d\det Q
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}.
$$

:::

## 12. 为什么是有理数的平方

::: {.proof title="正有理平方"}

矩阵乘法给

$$
(I+iC)(I-iC)=I+C^2,\qquad
(I+C)(I-C)=I-C^2.
$$

分别转置并用$C^T=-C$，有

$$
\det(I-iC)=\det((I-iC)^T)=\det(I+iC),
$$

$$
\det(I-C)=\det((I-C)^T)=\det(I+C).
$$

将这两组相等关系代入乘积行列式，得到

$$
\frac d{\mathcal H}
=\left[\frac{\det(I+C)}{\det(I+iC)}\right]^2.
$$

写$[d]=\{1,\ldots,d\}$。

$\lfloor r\rfloor$把它向下取到最近整数。

有限求和的空和为0、空乘积为1。

还要解释“矩阵含虚数单位，行列式为什么仍为有理数”，不能只由$C$的元素有理就直接断言。令$U$是同时选取的行列指标集，$C[U]$为对应主子矩阵，空集行列式约定为1。按每一列选单位列或矩阵列展开：

$$
\det(I+tC)=\sum_{U\subseteq[d]}t^{|U|}\det C[U].
$$

若$|U|$为奇数，反对称性给

$$
\det C[U]=\det(C[U]^T)=\det(-C[U])
=-\det C[U],\qquad \det C[U]=0.
$$

只剩偶数阶主子式。代入$t=i$，每个幂$i^{2k}=(-1)^k$是实整数，因此

$$
\det(I+iC)=
\sum_{k=0}^{\lfloor d/2\rfloor}(-1)^k
\sum_{\substack{U\subseteq[d]\\|U|=2k}}\det C[U]\in\mathbb Q.
$$

代入$t=1$时每项也有理，故$\det(I+C)\in\mathbb Q$。在每个二维块上，两个行列式因子分别是$1+\lambda^2$和$1-\lambda^2$，都为正；零块贡献1。因此分子、分母均正。

把这个正的行列式比值记为$\rho_d(S)$，上式说明$d/\mathcal H$是它的平方，因而所取正平方根为正有理数。

这给出所引用版本猜想6的完整一般计算，而不只是在表中的几个例子上发现有理数。

:::

## 13. 三角形例子可以完全手算

::: {.example title="三顶点逐项验算"}

取

$$
S=\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},\qquad C=S/3.
$$

把每行与每列相乘：

$$
S^2=\begin{pmatrix}-2&1&1\\1&-2&1\\1&1&-2\end{pmatrix}=J-3I,
\qquad C^2=(J-3I)/9.
$$

令$P_0=J/3$、$\Pi=I-P_0$。因为$P_0\Pi=\Pi P_0=0$、$P_0^2=P_0$、$\Pi^2=\Pi$，

$$
C^2=-\Pi/3,\quad
I+C^2=P_0+\frac23\Pi,\quad
I-C^2=P_0+\frac43\Pi.
$$

直接检查逆：

$$
\left(P_0+\frac43\Pi\right)
\left(P_0+\frac34\Pi\right)=P_0+\Pi=I.
$$

因此

$$
\begin{aligned}
Q&=\left(P_0+\frac23\Pi\right)
\left(P_0+\frac34\Pi\right)\\
&=P_0+\frac12\Pi
=\frac12I+\frac12P_0
=\frac12I+\frac16J.
\end{aligned}
$$

取

$$
E=\begin{pmatrix}1&0\\0&1\\-1&-1\end{pmatrix}.
$$

每列的和都是0，故$JE=0$。再直接相乘：

$$
E^TE=
\begin{pmatrix}1&0&-1\\0&1&-1\end{pmatrix}
\begin{pmatrix}1&0\\0&1\\-1&-1\end{pmatrix}
=\begin{pmatrix}2&1\\1&2\end{pmatrix}.
$$

所以

$$
\mathbf H=E^TQE
=\frac12E^TE+\frac16E^TJE
=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}.
$$

从而

$$
\mathcal H=1-\frac14=\frac34,\qquad
\sqrt{d/\mathcal H}=\sqrt{\frac3{3/4}}=2.
$$

还可以用行列式比值独立核对。按第一行展开：

$$
\begin{aligned}
\det(I+tS)
&=\det\begin{pmatrix}1&t&-t\\-t&1&t\\t&-t&1\end{pmatrix}\\
&=(1+t^2)-t(-t-t^2)-t(t^2-t)\\
&=1+3t^2.
\end{aligned}
$$

分别代入$t=1/3$与$t=i/3$：

$$
\det(I+C)=1+\frac39=\frac43,
$$

$$
\det(I+iC)=1+\frac{3i^2}{9}=1-\frac13=\frac23.
$$

所以$\rho_3=(4/3)/(2/3)=2$，与直接算Hessian完全相同。

:::

## 14. 圆环模型常数的极限与误差

奇阶圆环图$\mathrm{Car}_d$的顶点是模$d$的余数。其边方向为

$$
i\to j\quad\Longleftrightarrow\quad
(j-i)\bmod d\in\{1,\ldots,(d-1)/2\}.
$$

::: {.definition title="双曲函数与反函数"}

本节会用到双曲函数；它们可直接由指数函数定义：

$$
\cosh y=\frac{e^y+e^{-y}}2,\qquad
\sinh y=\frac{e^y-e^{-y}}2,\qquad
\tanh y=\frac{\sinh y}{\cosh y}.
$$

后面的$\operatorname{artanh}x=\tfrac12\log((1+x)/(1-x))$在$|x|<1$时为实数；$\arctan$是反正切函数。另外，$\sec y=1/\cos y$（余弦非零时）、$\operatorname{sech}y=1/\cosh y$。这些定义足以配合基本求导公式阅读A.4的展开。

:::

::: {.theorem title="圆环常数及展开"}

对圆环基图，

$$
\rho_d=
\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}.
$$

当每块内部也限制为正则时，原文的计数定理另给一个$e^{1/d}$因子。定义

$$
\mathfrak r_d=e^{1/d}\rho_d.
$$

本次证明$\mathfrak r_d$随奇数$d\ge3$严格增加，且趋于

$$
L=\frac{\cosh1}{\cos1}.
$$

误差记号$R(x)=O(x^k)$的意思是：当$x$足够接近0时，存在一个与$x$无关的常数$M$，使$|R(x)|\le M|x|^k$。因此若$R_1=O(x^a)$、$R_2=O(x^b)$，则$|R_1R_2|\le M_1M_2|x|^{a+b}$，即$R_1R_2=O(x^{a+b})$；加法与除以非零$x$也按此不等式计算。$O(d^{-k})$指$d$趋于无穷，$O_d$允许常数依赖固定的$d$。

令$b=\tanh1,h=\tan1$，进一步有

$$
\mathfrak r_d
=L\left[1+\frac{b-h}{3d^2}+\frac{a_4}{d^4}
-\frac1{3d^5}+O(d^{-6})\right],
$$

$$
a_4=\frac{b+h}{5}+\frac{2+h^2-b^2}{18}+\frac{(b-h)^2}{18}.
$$

所以$d^{-1}$和$d^{-3}$系数精确为零，第一项非零奇次是$d^{-5}$。主文以求导证明单调性，再用Taylor公式计算系数。

这里的误差是基图参数$d$的误差，不是最终图大小$N$的误差。

:::

## 15. 为什么非正则基图会有指数损失

::: {.lemma title="非正则时的严格损失因子"}

设基图出度为$d_i$，令

$$
a_i=(2d_i+1)/d,\qquad
\kappa=(a_1\cdots a_d)^{1/d}.
$$

因为平均出度是$(d-1)/2$，

$$
\frac1d\sum_i a_i=1.
$$

算术—几何平均给$\kappa\le1$；只有全部出度相同才取等号。因此非正则时$\kappa<1$。

:::

随机吹胀的第$i$类行和约为$m(d_i+1/2)$。对行和舍入后使用Brégman界，再与$N!/2^N$比较，主要对数差为

$$
m\sum_i\log a_i=N\log\kappa.
$$

所以归一化圈、路径期望均有

$$
\text{某个多项式因子}\times\kappa^N
$$

这样的上界。当$\kappa<1$，指数衰减快于任何固定多项式增长，因此它们都趋于0。

还可直接用基图比分$s_i=2d_i-(d-1)$量化：

$$
\log\kappa\le-\frac{\sum_i s_i^2}{8d^3}.
$$

奇阶非正则基图至少有一个非零正比分与一个非零负比分，各自绝对值至少2，所以$\sum_i s_i^2\ge8$。于是指数因子至多$e^{-N/d^3}$。

这一步很重要：正则基图的Hessian公式不能直接套在非正则基图上，必须另作估计。

## 16. 为什么圆环成为固定基图模型的唯一最优者

“普通同构”就是保持所有边方向的顶点重编号。

::: {.theorem title="固定基图模型的唯一期望最优者"}

对正则基图，极限常数就是$\rho_d(S)$，正则内部块时另乘共同正因子$e^{1/d}$。

已有并在主文第二部分明确展开的矩比较给

$$
\rho_d(S)\le\rho_d(\mathrm{Car}_d),
$$

且正则图中只有普通同构于圆环的图取等号。不普通同构于圆环的正则图还有严格的常数间隙；非正则图的归一化期望趋于0。

固定$d$时只有有限多个基图，所以可以对它们各自“块足够大”的阈值取最大值。这样就得到：对充分大的$m$，随机块模型的圈期望和路径期望都由圆环基图唯一最大。

它不表示每一个随机样本都最大，也不表示任意$N$阶竞赛图的最大者都已确定。

:::

# 进一步展开：期望、谱隙和Taylor系数

## A.1 期望为什么可以逐条圈相加

$\mathbb P(\mathcal E)$表示事件$\mathcal E$的概率。

::: {.definition title="候选圈的指示量"}

只有有限多个等可能随机实现时，$\mathbb EX$就是这些实现中$X$值的算术平均。对每条候选有向哈密顿圈$\gamma$，定义指示量

$$
I_\gamma=\begin{cases}1,&\gamma\text{出现},\\0,&\gamma\text{不出现}.\end{cases}
$$

:::

圈数就是$C=\sum_\gamma I_\gamma$。把有限平均与有限求和交换，得到

$$
\mathbb EC=\sum_\gamma\mathbb EI_\gamma
=\sum_\gamma\mathbb P(\gamma\text{出现}).
$$

全体$N$个顶点的顺序有$N!$种。圈的每个起点给同一圈的$N$种表示，故候选有向圈有$(N-1)!$条。每条需要$N$个独立方向成立，概率$2^{-N}$；路径有$N!$个候选，需要$N-1$个方向。因此

$$
\mathbb EC=(N-1)!2^{-N}=\nu_N,\qquad
\mathbb EH=N!2^{-(N-1)}=\mu_N.
$$

这一步用于$N\ge3$的圈。在独立内部块模型$\mathcal T$中，块间边概率为0或1，块内边概率为$1/2$。一条圈使用不同的无序点对，所需随机边彼此独立，故其概率为各边概率的乘积。

置换就是顶点集合到自身的双射，$\mathfrak S_N$为所有这样的置换。

除非模型已作具体指定，$W$表示任意$N$阶非负矩阵，即$W_{ij}\ge0$。

::: {.definition title="永久式与加权圈数"}

永久式则不同。它定义为

$$
\operatorname{per}W
=\sum_{\pi\in\mathfrak S_N}\prod_{i=1}^N W_{i,\pi(i)}.
$$

记$\mathcal C_N\subseteq\mathfrak S_N$为恰有一个长度$N$循环的置换。加权圈数具体为

$$
C(W)=\sum_{\pi\in\mathcal C_N}\prod_{i=1}^N W_{i,\pi(i)}.
$$

:::

该置换表示已识别循环起点，不再额外除以$N$。哈密顿圈只占其中一部分置换，所有项非负，所以$C(W)\le\operatorname{per}W$。永久式还包含二圈；随机竞赛图不允许同一对顶点的两个方向同时存在，所以不能把$\mathbb E\operatorname{per}A$错误地等同于$\operatorname{per}(\mathbb EA)$。

## A.2 不靠猜测得到Hessian中的谱隙

::: {.proof title="实反对称分块与谱隙"}

这里先证明为什么存在所用的二维分块，避免把它留作读者额外掌握的结论。设$C^T=-C$，则$B=C^TC=-C^2$为实对称矩阵，对实向量$x$有$x^TBx=\|Cx\|_2^2\ge0$。

若$C\ne0$，存在某个标准基向量$e_j$满足$\|Ce_j\|_2^2>0$。在单位球面上使连续函数$x^TBx$达到最大，取最大点$v$并记$\mu=v^TBv$。单位球面在有限维空间中闭且有界，所以最大点存在，并有$\mu\ge\|Ce_j\|_2^2>0$。

对任意$x\perp v$，曲线$(v+tx)/\|v+tx\|_2$仍在单位球面上；最大点处的一元导数必须为0。因此

$$
0=\left.\frac{d}{dt}
\frac{(v+tx)^TB(v+tx)}{1+t^2\|x\|_2^2}\right|_{t=0}
=2x^TBv.
$$

这表示$Bv$没有垂直于$v$的分量，故$Bv=\mu v$。令$\lambda=\sqrt\mu>0$、$w=-Cv/\lambda$。逐项计算：

$$
v^Tw=-v^TCv/\lambda=0,\qquad
w^Tw=\frac{v^TC^TCv}{\lambda^2}=\frac{\mu}{\lambda^2}=1,
$$

$$
Cv=-\lambda w,\qquad
Cw=-C^2v/\lambda=Bv/\lambda=\lambda v.
$$

所以$v,w$为正交单位向量，且这两个向量张成的平面在$C$作用下不变。在有序基$(v,w)$上，$Cv$的坐标为$(0,-\lambda)^T$、$Cw$的坐标为$(\lambda,0)^T$，故矩阵恰为下面的$J_\lambda$。若$x$垂直于$v,w$，则

$$
v^TCx=-(Cv)^Tx=\lambda w^Tx=0,\qquad
w^TCx=-(Cw)^Tx=-\lambda v^Tx=0.
$$

因而剩余正交补空间也不变。对这个更小的空间重复上述步骤，每次去掉两个维数；若剩余矩阵为0便停止，有限步后得到若干二维块与零块。这证明实反对称矩阵可在正交基中分成若干个二维块

$$
J_\lambda=\begin{pmatrix}0&\lambda\\-\lambda&0\end{pmatrix}
$$

以及零块。这是实反对称矩阵的标准分块形式。该块满足

$$
J_\lambda^2=-\lambda^2I_2.
$$

$\|M\|_F=(\sum_{j,k}M_{jk}^2)^{1/2}$是矩阵所有元素平方和的平方根。

$s_{ij}$也表示$S$的第$i,j$元。

另有$\|M\|_{\rm op}=\sup_{v\ne0}\|Mv\|_2/\|v\|_2$，表示矩阵把向量长度放大的最大比例。$\sup$表示上确界，即所有这些比例的最小上界。

本题$C=S/d$有$d(d-1)$个大小为$1/d$的非对角元，故

$$
\|C\|_F^2=\frac{d(d-1)}{d^2}=\frac{d-1}{d}.
$$

每个二维块对这个平方和贡献$2\lambda^2$，因此对每一个块，

$$
2\lambda^2\le\|C\|_F^2=\frac{d-1}{d},
$$

$$
\lambda^2\le\frac{d-1}{2d}<\frac12<1.
$$

这给出了第10节所需的$|\lambda|<1$；零频率对应$Q$的单位块。

:::

## A.3 基变换中的因子d再算一遍

::: {.proof title="基变换的体积因子"}

令$V$为零和空间的正交单位基，$E=VL$。因为$E$列独立，$L$为可逆$(d-1)$阶方阵。于是

$$
E^TQE=L^T(V^TQV)L,
$$

$$
\det(E^TQE)=\det(L)^2\det(V^TQV).
$$

又

$$
E^TE=L^TV^TVL=L^TL,\qquad
\det(L)^2=\det(E^TE)=d.
$$

$Qu=u$，且$Q$保持零和空间，所以在正交基$(u,V)$中，

$$
\det Q=\det\begin{pmatrix}1&0\\0&V^TQV\end{pmatrix}
=\det(V^TQV).
$$

把这两个值乘回，恰得$\det(E^TQE)=d\det Q$。这一步同时解释了每个矩阵的维数。

:::

## A.4 模型常数的Taylor系数逐项相乘

令$x=1/d$，并定义

$$
\alpha(x)=\frac{\arctan x}{x},\qquad
\beta(x)=\frac{\operatorname{artanh}x}{x},\qquad
\operatorname{artanh}x=\frac12\log\frac{1+x}{1-x}.
$$

对$0<|x|<1$，几何级数积分给

$$
\frac{\arctan x}{x}=1-\frac{x^2}{3}+\frac{x^4}{5}+O(x^6),
$$

$$
\frac{\operatorname{artanh}x}{x}=1+\frac{x^2}{3}+\frac{x^4}{5}+O(x^6).
$$

从圆环闭式拆出共同实因子：

$$
(1+x)^{1/x}+(1-x)^{1/x}
=2(1-x^2)^{1/(2x)}\cosh\beta(x),
$$

$$
(1+ix)^{1/x}+(1-ix)^{1/x}
=2(1+x^2)^{1/(2x)}\cos\alpha(x).
$$

在这里选取原点附近的解析分支；当$x=1/d$时指数$1/x=d$为整数，直接等于原多项式幂。故

$$
\mathfrak r(x)=e^{p(x)}\frac{\cosh\beta(x)}{\cos\alpha(x)},
$$

$$
p(x)=x+\frac{\log(1-x^2)-\log(1+x^2)}{2x}.
$$

分别展开两个对数：

$$
\log(1-x^2)=-x^2-\frac{x^4}{2}-\frac{x^6}{3}-\frac{x^8}{4}+O(x^{10}),
$$

$$
\log(1+x^2)=x^2-\frac{x^4}{2}+\frac{x^6}{3}-\frac{x^8}{4}+O(x^{10}).
$$

将上面两行逐项相减，第四次项和第八次项分别抵消：

$$
\begin{aligned}
\log(1-x^2)-\log(1+x^2)
&=(-x^2-x^2)+(-x^4/2+x^4/2)\\
&\quad+(-x^6/3-x^6/3)+(-x^8/4+x^8/4)+O(x^{10})\\
&=-2x^2-\frac{2x^6}{3}+O(x^{10}),\\
p(x)&=x+\frac{-2x^2-2x^6/3+O(x^{10})}{2x}\\
&=x-x-\frac{x^5}{3}+O(x^9).
\end{aligned}
$$

余项除以$x$后阶数从10变为9；这里不是把任意八阶余项直接提高到九阶。于是

$$
p(x)=-\frac{x^5}{3}+O(x^9).
$$

令$b=\tanh1$、$h=\tan1$、$\delta_\beta=\beta-1$、$\delta_\alpha=\alpha-1$。设$F(y)=\log\cosh y$、$G(y)=-\log\cos y$，先求三次导数：

$$
F'(y)=\tanh y,\quad F''(y)=1-\tanh^2y,\quad
F'''(y)=-2\tanh y\,\operatorname{sech}^2y,
$$

$$
G'(y)=\tan y,\quad G''(y)=1+\tan^2y,\quad
G'''(y)=2\tan y\,\sec^2y.
$$

对本题$0<x\le1/3$，$\alpha$位于$[0,1]$，而$\beta$是实数。故$|F'''|\le2$，在$\alpha$与1之间有$|G'''|\le2\tan1\,\sec^21$。积分余项的绝对值分别满足

$$
|R_F|\le\frac{2}{2}\int_0^{|\delta_\beta|}
(|\delta_\beta|-t)^2dt
=\frac{|\delta_\beta|^3}{3},
$$

$$
|R_G|\le\frac{2\tan1\,\sec^21}{2}
\int_0^{|\delta_\alpha|}(|\delta_\alpha|-t)^2dt
=\frac{\tan1\,\sec^21}{3}|\delta_\alpha|^3.
$$

由此前幂级数，两个$\delta$均为$O(x^2)$，所以上述余项均为$O(x^6)$。在点1处代入已列的一、二阶导数，得到

$$
\log\cosh(1+\delta_\beta)-\log\cosh1
=b\delta_\beta+\frac{1-b^2}{2}\delta_\beta^2+O(\delta_\beta^3),
$$

$$
-\log\cos(1+\delta_\alpha)+\log\cos1
=h\delta_\alpha+\frac{1+h^2}{2}\delta_\alpha^2+O(\delta_\alpha^3).
$$

逐项代入$\delta_\beta=x^2/3+x^4/5+O(x^6)$：

$$
\log\cosh\beta-\log\cosh1
=\frac b3x^2+\left[\frac b5+\frac{1-b^2}{18}\right]x^4+O(x^6).
$$

再代入$\delta_\alpha=-x^2/3+x^4/5+O(x^6)$：

$$
-\log\cos\alpha+\log\cos1
=-\frac h3x^2+\left[\frac h5+\frac{1+h^2}{18}\right]x^4+O(x^6).
$$

加上$p(x)$，并记$L=\cosh1/\cos1$：

$$
\log\frac{\mathfrak r(x)}L
=a_2x^2+\ell_4x^4-\frac{x^5}{3}+O(x^6),
$$

$$
a_2=\frac{b-h}{3},\qquad
\ell_4=\frac{b+h}{5}+\frac{2+h^2-b^2}{18}.
$$

最后用$e^z=1+z+z^2/2+O(z^3)$。此处$z=O(x^2)$，所以

$$
\frac{z^2}{2}=\frac{a_2^2}{2}x^4+O(x^6),\qquad
z^3=O(x^6).
$$

得到

$$
\mathfrak r(x)
=L\left[1+a_2x^2+
\left(\ell_4+\frac{a_2^2}{2}\right)x^4-\frac{x^5}{3}+O(x^6)\right].
$$

这逐项给出二次、四次、五次系数，也说明一次和三次项为何精确为零。

# 补充演算

## B.1 传递符号矩阵的行列式多项式

令$T_n$上三角为1、下三角为$-1$、对角为0，记$F_n(t)=\det(I+tT_n)$。下面直接用行变换证明主文第一部分第9节的闭式，不把偶阶主子式的值作为未说明的输入。

当$n=1$时，$F_1(t)=1=((1+t)+(1-t))/2$，闭式成立。以下$n\ge2$。对前$n-1$行同时作$R_i\leftarrow R_i-R_{i+1}$。该行变换由一个对角为1的上三角矩阵实施，行列式不变。所得矩阵的前$n-1$行只有

$$
M_{ii}=1+t,\qquad M_{i,i+1}=t-1
$$

可能非零，最后一行是$(-t,\ldots,-t,1)$。假设暂时$t\ne-1,0$，置

$$
r=\frac{1-t}{1+t}.
$$

左上$(n-1)$阶块记为$B$，其行列式为$(1+t)^{n-1}$。右上列$b$仅最后一元是$t-1$。解$Bx=b$，从最后一行向上：

$$
x_{n-1}=\frac{t-1}{1+t}=-r,
$$

$$
(1+t)x_i+(t-1)x_{i+1}=0
\quad\Longrightarrow\quad x_i=rx_{i+1}=-r^{n-i}.
$$

Schur补于是给

$$
F_n(t)=(1+t)^{n-1}\left(1-t\sum_{k=1}^{n-1}r^k\right).
$$

有限几何和先乘$1-r$，相邻项抵消：

$$
(1-r)\sum_{k=1}^{n-1}r^k
=(r+r^2+\cdots+r^{n-1})-(r^2+\cdots+r^n)
=r-r^n.
$$

因此$\sum_{k=1}^{n-1}r^k=r(1-r^{n-1})/(1-r)$。再利用$1-r=2t/(1+t)$，括号化为

$$
\begin{aligned}
1-t\sum_{k=1}^{n-1}r^k
&=1-\frac{tr(1-r^{n-1})}{1-r}\\
&=1-\frac{1-t}{2}(1-r^{n-1})\\
&=\frac{1+t}{2}+\frac{1-t}{2}r^{n-1}.
\end{aligned}
$$

把括号乘回$(1+t)^{n-1}$，并代入$r=(1-t)/(1+t)$：

$$
\begin{aligned}
F_n(t)
&=\frac{(1+t)^n}{2}
+\frac{(1+t)^{n-1}(1-t)}2
\left(\frac{1-t}{1+t}\right)^{n-1}\\
&=\frac{(1+t)^n}{2}+\frac{(1-t)^n}{2}.
\end{aligned}
$$

两端都是多项式，已在除两个点以外的所有$t$相等，故在$t=-1,0$也相等。代入$t=1/d$与$t=i/d$，得到圆环模型的行列式比值。

为补明主文第一部分第9节关于每个主子式的陈述，取非空$U$，记$k=|U|$。按原顶点升序排列后，$T_d[U]$就是$T_k$。行列式多项式$F_k(t)=\det(I+tT_k)$中$t^k$的系数为$\det T_k$；记$[t^k]$为提取这一系数的符号，因此

$$
\det T_d[U]=\det T_k=[t^k]F_k(t)
=\frac{1+(-1)^k}{2}
=\begin{cases}1,&k\ \text{even},\\0,&k\ \text{odd}.\end{cases}
$$

空集的主子式由约定等于1。这就从已证闭式推出了每一个主子式的取值。

## B.2 交替切换与圆环的普通同构

设$d=2q+1$。对传递矩阵作交替切换，$\varepsilon_i=(-1)^{i-1}$、$D_{\varepsilon}=\operatorname{diag}(\varepsilon_i)$。当$i<j$、$\Delta=j-i$时，

$$
(D_{\varepsilon}T_dD_{\varepsilon})_{ij}=(-1)^\Delta.
$$

定义圆环标签映射

$$
\phi(i)=(q+1)i\pmod d.
$$

因为$2(q+1)=d+1$，$q+1$与$d$互素，故$\phi$是置换。

若$\Delta=2r$，则$1\le r\le q$且

$$
\phi(j)-\phi(i)\equiv(q+1)2r\equiv r\pmod d.
$$

该差在$\{1,\ldots,q\}$，正是圆环中$\phi(i)\to\phi(j)$的条件；切换矩阵此时也为1。

若$\Delta=2r+1$，则$0\le r\le q-1$，且

$$
\phi(j)-\phi(i)\equiv q+1+r\pmod d.
$$

该差在$\{q+1,\ldots,2q\}$，方向相反；切换矩阵此时为$-1$。反对称性处理$i>j$，对角均为0，所以这是逐条边的普通同构。

主文第二部分还用到传递矩阵的幂有相同对角元。令$Ze_j=e_{j+1}$（$j<d$）、$Ze_d=-e_1$。当$i,j<d$时，

$$
(Z^TT_dZ)_{ij}=(T_d)_{i+1,j+1}=(T_d)_{ij}.
$$

当$i<d,j=d$时，

$$
(Z^TT_dZ)_{i,d}=-(T_d)_{i+1,1}=1=(T_d)_{i,d}.
$$

当$i=d,j<d$时，

$$
(Z^TT_dZ)_{d,j}=-(T_d)_{1,j+1}=-1=(T_d)_{d,j}.
$$

最后对角元均为0。因此$Z^TT_dZ=T_d$，从而对每个整数$p\ge0$，

$$
Z^TT_d^{2p}Z=T_d^{2p}.
$$

取对角元便得到相邻对角相等，绕回时的两个负号抵消。

## B.3 四阶主子式与四次矩等号

$\binom nk=n!/(k!(n-k)!)$，$k>n$时为0。

本节$S$可为任意$d$阶竞赛符号矩阵，反对称且非对角元为$\pm1$；不要求正则。它帮助解释第16节所说的矩比较等号分类。令$a,b,c,g,e,f$为六个局部实标量，其中$g$不是图或矩阵阶数，设

$$
M=\begin{pmatrix}
0&a&b&c\\
-a&0&g&e\\
-b&-g&0&f\\
-c&-e&-f&0
\end{pmatrix}.
$$

记$M_{1j}$为删去第1行、第$j$列后的三阶行列式（不含代数余子式符号）。沿第一行展开，分别计算：

$$
\begin{aligned}
M_{12}
&=\det\begin{pmatrix}-a&g&e\\-b&0&f\\-c&-f&0\end{pmatrix}\\
&=(-a)(0-f(-f))-g((-b)0-f(-c))+e((-b)(-f)-0(-c))\\
&=-af^2-cgf+bef,\\
M_{13}
&=\det\begin{pmatrix}-a&0&e\\-b&-g&f\\-c&-e&0\end{pmatrix}\\
&=(-a)((-g)0-f(-e))-0+e((-b)(-e)-(-g)(-c))\\
&=-aef+be^2-cge,\\
M_{14}
&=\det\begin{pmatrix}-a&0&g\\-b&-g&0\\-c&-e&-f\end{pmatrix}\\
&=(-a)((-g)(-f)-0(-e))-0+g((-b)(-e)-(-g)(-c))\\
&=-agf+bge-cg^2.
\end{aligned}
$$

将每个三阶行列式按其第一行再展开，三项分别来自第一行的三个元素；上式中第一行的0贡献为0。再乘四阶展开的系数：

$$
\begin{aligned}
\det M
&=-aM_{12}+bM_{13}-cM_{14}\\
&=(a^2f^2+acgf-abef)
+(-abef+b^2e^2-bcge)
+(acgf-bcge+c^2g^2)\\
&=a^2f^2+b^2e^2+c^2g^2-2abef+2acgf-2bcge\\
&=(af-be+cg)^2.
\end{aligned}
$$

六个变量均为$\pm1$时，$af-be+cg$是三个$\pm1$之和，其值为$\pm1$或$\pm3$，故行列式为1或9。设$D_4(S)$为四顶点主子式等于9的个数。由行列式的列多线性展开，在每列选择单位列或$tS$的列，得到

$$
\det(I+tS)=\sum_{U\subseteq[d]}t^{|U|}\det S[U].
$$

奇阶反对称矩阵$B$满足$\det B=\det B^T=\det(-B)=-\det B$，所以其行列式为0。二阶主子式均为1，四阶中有$D_4$个9，其余为1。因此

$$
\det(I+tS)=1+e_2t^2+e_4t^4+O(t^6),
$$

$$
e_2=\binom d2,\qquad
e_4=(\binom d4-D_4)+9D_4=\binom d4+8D_4.
$$

$\operatorname{tr}M=\sum_jM_{jj}$是矩阵的迹。

下列展开只在$t=0$附近使用。取$|t|\,\|S\|_{\rm op}<1/2$，则每个特征值$\mu$都满足$|t\mu|<1/2$，并用在1处为0的对数级数定义$\log(1+t\mu)$。有限个特征值求和与幂级数交换合法，且

$$
\det(I+tS)=\prod_\mu(1+t\mu),\qquad
\operatorname{tr}S^k=\sum_\mu\mu^k.
$$

这里特征值按重数计入；实反对称标准形保证可在复数域对角化，零特征值也包括在内。

每个特征值的对数级数给

$$
\log\det(I+tS)
=\sum_{k\ge1}\frac{(-1)^{k+1}t^k}{k}\operatorname{tr}S^k
=-\frac{t^2}{2}\operatorname{tr}S^2
-\frac{t^4}{4}\operatorname{tr}S^4+O(t^6).
$$

奇次迹为0，因为$\operatorname{tr}S^{2j+1}=\operatorname{tr}(S^{2j+1})^T=-\operatorname{tr}S^{2j+1}$。另一方面，将$z=e_2t^2+e_4t^4+O(t^6)$代入$\log(1+z)=z-z^2/2+O(z^3)$，其中$z^2=e_2^2t^4+O(t^6)$、$z^3=O(t^6)$，得到

$$
\log\det(I+tS)=e_2t^2+(e_4-e_2^2/2)t^4+O(t^6).
$$

四次系数相等，逐步移项：

$$
-\operatorname{tr}S^4/4=e_4-e_2^2/2,\qquad
\operatorname{tr}S^4=2e_2^2-4e_4
=2\left(\binom d2\right)^2-4\binom d4-32D_4(S).
$$

传递矩阵任取四个升序顶点都有$a=b=c=g=e=f=1$，其行列式为$(1-1+1)^2=1$，所以$D_4(T_d)=0$。相减给

$$
\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S).
$$

若四次矩取等，则$D_4(S)=0$。取$\varepsilon_1=1,\varepsilon_j=s_{1j}$（$j>1$），定义$D_{\varepsilon}=\operatorname{diag}(\varepsilon_1,\ldots,\varepsilon_d)$和$S'=D_{\varepsilon} S D_{\varepsilon}$。于是$s'_{1j}=\varepsilon_1s_{1j}\varepsilon_j=s_{1j}^2=1$。各主子式乘以$(\det D_{\varepsilon}[U])^2=1$，故$D_4$不变。任取$i<j<k$且都不为1，

$$
\det S'[\{1,i,j,k\}]
=(s'_{jk}-s'_{ik}+s'_{ij})^2.
$$

若这三点形成有向三圈，则$s'_{ij}=s'_{jk}=-s'_{ik}$，括号为$3s'_{ij}$，平方为9，矛盾。因此剩余顶点无有向三圈。如果$i\to j$、$j\to k$而$i\not\to k$，则$k\to i$，会形成三圈；所以方向关系是严格全序，可按该全序排列。第一顶点指向所有剩余点，整个切换图于是为传递图。反过来带符号置换相似保持迹，故四次矩取等。$d=3$时切换后剩下两点，按其唯一边方向排列即可。

## B.4 逐行补齐与整数化的全部计算

符号$\lceil r\rceil$把实数向上取到最近整数。

::: {.proof title="行补齐、整数化及Brégman界"}

本节的$W$在独立内部块模型中是邻接矩阵的逐元期望：对角为0，同块异点之间为$1/2$，不同块之间为基图所定的0或1。记基图出度为$d_i$、$b_i=d_i+1/2$。本节应用于$m\ge2$；$\mathcal R$还要求奇$m$，故实际从$m\ge3$开始。这足以处理块阶数趋于无穷的结论。第$i$类的每一行在$W$中的和为

$$
r_i=md_i+\frac{m-1}{2}=mb_i-\frac12,\qquad
R_i=\lceil r_i\rceil.
$$

先讨论任意$L$元行$w$，其中$0\le w_j\le1$，当前行和记为$r=\sum_{j=1}^Lw_j$，目标整数行和$R$满足$r\le R\le L$。需要补入$s_0=R-r$，可用容量为$\sum_j(1-w_j)=L-r\ge s_0$。从$j=1$开始依次取

$$
\delta_j=\min(1-w_j,s_{j-1}),\qquad
s_j=s_{j-1}-\delta_j,\qquad w'_j=w_j+\delta_j.
$$

递推的每一步满足

$$
s_j=\max(0,s_{j-1}-(1-w_j))
=\max\left(0,s_0-\sum_{h=1}^j(1-w_h)\right).
$$

第一等式由减去两数的最小值得到；第二等式从$j=1$开始逐步代入。

递推得到$s_L=\max(0,s_0-\sum_j(1-w_j))=0$，所以$0\le w'_j\le1$且$\sum_jw'_j=R$。永久式各系数非负，这种逐元增加不使其减少。

固定其他行，将永久式写作$\sum_jw_jc_j$，其中$c_j$是删去当前行和第$j$列后的永久式，故$c_j\ge0$。若两个元素$w_a,w_b$严格介于0与1，重标这两个坐标使$c_a\ge c_b$，取

$$
\eta=\min(1-w_a,w_b)>0,\qquad
w_a'=w_a+\eta,\qquad w_b'=w_b-\eta.
$$

行和保持不变，且

$$
\sum_jw_j'c_j-\sum_jw_jc_j=\eta(c_a-c_b)\ge0.
$$

至少一个坐标变成0或1，非整数坐标数减少。至多$L-1$次后至多剩一个非整数坐标；若其余坐标均为整数且总和$R$为整数，最后一个坐标也是整数。对各行执行此过程，得到0、1矩阵$W^\sharp$，每个第$i$类行有$R_i$个1，而且$\operatorname{per}W\le\operatorname{per}W^\sharp$。

这里的$W^\sharp$是用于上界的辅助矩阵；所需条件是各元为0或1及指定行和，允许其对角为1。下面所引定理适用于这种一般0、1矩阵。

现在引用[Brégman不等式（Alon论文Lemma 2.1）](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)：0、1矩阵的行和为$q_1,\ldots,q_L>0$时，

$$
\operatorname{per}W^\sharp\le\prod_{\ell=1}^L(q_\ell!)^{1/q_\ell}.
$$

由于$r_i\ge(m-1)/2>0$，整数上界$R_i$至少为1，满足所引用Brégman界的正行和假设。本题每类恰有$m$行，因此

$$
\operatorname{per}W\le\prod_{i=1}^d(R_i!)^{m/R_i}.
$$

使用的是原0、1定理；加权情形的适用性已由上面的具体行操作证明。

上面已列出逐坐标补齐量$\delta_j$、剩余量$s_j$、两坐标移动量$\eta$及永久式改变量。这里记录终止性所需的两个整数。

$\#U=|U|$表示集合元素数。

行记号$W_{\ell,\cdot}=(W_{\ell1},\ldots,W_{\ell N})$表示第$\ell$行。

$$
q(w)=\#\{j:0<w_j<1\},\qquad
q(W)=\sum_{\ell=1}^L q(W_{\ell,\cdot}).
$$

每次两坐标移动不改变整数行和，使至少一个非整数坐标变成整数，且不改变其他整数坐标，所以$q(w)$至少减少1。最初$q(w)\le L$，不可能无限下降。若停止时$q(w)=1$，唯一非整数坐标为

$$
w_a=R-\sum_{j\ne a}w_j\in\mathbb Z,
$$

与其非整数性矛盾。因此停止时$q(w)=0$。逐行处理不会修改其他行；每行最多$L-1$次两坐标移动后已经整数化，总移动次数至多$L(L-1)$。每次永久式改变量均为上面算出的$\eta(c_a-c_b)\ge0$。

:::

## B.5 圈与路径的归一化逐项计算

令$d_i$为基图第$i$个顶点的出度，$b_i=d_i+1/2$，$a_i=2b_i/d$，$\kappa=(\prod_{i=1}^d a_i)^{1/d}$，$N=dm$。B.4得到整数行和$R_i=\lceil mb_i-1/2\rceil$及对应的永久式上界。本节先把这个圈上界的余项常数写明，再计算增点路径上界；不再用尚未指定的常数或多项式代替计算。

如果待估计的永久式等于0，被它控制的非负圈计数也等于0，所需上界已经成立，不对0取对数。本节以下的全部永久式对数计算只在相应永久式为正时进行；正的上界最后也覆盖零值情形。以下$m\ge2$，$N=dm$。写$R_i=mb_i+\xi_i$，则$|\xi_i|\le1/2$，并有

$$
R_i\ge m/2-1/2\ge m/4,\qquad R_i\le N.
$$

舍入误差来自目标定义，而不是额外假设：

$$
0\le R_i-r_i<1,\qquad
\xi_i=R_i-mb_i=(R_i-r_i)-\frac12
\in[-1/2,1/2).
$$

使用整数$R\ge1$的带余项Stirling界

$$
\log(R!)=R\log R-R+\frac12\log(2\pi R)
+\frac{\theta_R}{12R},\qquad 0<\theta_R<1.
$$

因此

$$
\begin{aligned}
m\sum_{i=1}^d\frac{\log(R_i!)}{R_i}
&\le m\sum_i\log R_i-N
+m\sum_i\frac{\log(2\pi R_i)}{2R_i}
+m\sum_i\frac1{12R_i^2}\\
&\le m\sum_i\log R_i-N
+2d\log(2\pi N)+\frac{4d}{3m}.
\end{aligned}
$$

最后两项分别使用$m/(2R_i)\le2$和$m/(12R_i^2)\le4/(3m)$。Stirling下界也给

$$
\log(N!/2^N)\ge N\log(N/2)-N.
$$

相减后，

$$
\log\frac{\operatorname{per}W}{N!/2^N}
\le m\sum_i\log\frac{2R_i}{N}
+2d\log(2\pi N)+\frac{4d}{3m}.
$$

令$y_i=\xi_i/(mb_i)$。由于$b_i\ge1/2$，$|y_i|\le1/m\le1/2$，且

$$
\frac{2R_i}{N}=a_i(1+y_i),\qquad
|\log(1+y_i)|
=\left|\int_0^{y_i}\frac{dt}{1+t}\right|
\le\frac{|y_i|}{1-|y_i|}\le\frac2m.
$$

所以

$$
m\sum_i\log\frac{2R_i}{N}
\le m\sum_i\log a_i+2d=N\log\kappa+2d.
$$

再使用$4d/(3m)\le2d/3$以及$N!/2^N=N\nu_N$，得到明确上界

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N}
\le e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N.
$$

若内部是正则块，每个样本的实际旧行和就是$mb_i-1/2$，为正整数。若该样本为$G$、邻接矩阵为$A_G$，则每个圈是永久式和中的一个非负单循环项，故$C(G)\le\operatorname{per}A_G$。直接对$A_G$应用Brégman及上面逐项估计，再对所有样本取平均，得到

$$
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
\le e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N.
$$

正则模型仅取合法奇$m$。非正则基图有$\kappa<1$；将右端取对数并除以$N$，

$$
\frac{\log(e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N)}{N}
=\log\kappa+
\frac{8d/3+2d\log(2\pi)+(2d+1)\log N}{N}
\longrightarrow\log\kappa<0,
$$

为写清最后一步，对$N\ge1$有

$$
0\le\frac{\log N}{N}
=\frac1N\int_1^N\frac{dt}{t}
\le\frac1N\int_1^N\frac{dt}{\sqrt t}
=\frac{2(\sqrt N-1)}N\longrightarrow0.
$$

记上界为$B_N$，取$c=-\tfrac12\log\kappa>0$。由$\log B_N/N\to\log\kappa=-2c$，存在阈值使其后$\log B_N/N<-c$，于是$0\le B_N<e^{-cN}\to0$。路径界的多项式次数虽然不同，但同样可将其对数除以$N$，按上面的积分界逐项令常数项及$\log(N+1)/N$趋于0。

故两个归一化圈期望都趋于0。

有限模型中的条件期望$\mathbb E[X\mid G]$先固定$G$，只对尚未固定的随机边取平均，再对$G$平均可恢复$\mathbb EX$。

固定旧竞赛图$G$，加入新顶点$v$，与旧顶点的边独立公平定向。每条路径$x_1\to\cdots\to x_N$对应唯一候选圈$v\to x_1\to\cdots\to x_N\to v$，两条新增边的联合概率为$(1/2)^2=1/4$。删除$v$是逆操作。因此

$$
\mathbb E[C_{\rm aug}\mid G]=H(G)/4,\qquad
4\nu_{N+1}=\frac{4N!}{2^{N+1}}=\frac{N!}{2^{N-1}}=\mu_N,
$$

$$
\frac{\mathbb EH}{\mu_N}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

这里$G_{\rm aug}$为加入$v$后的随机竞赛图，$C_{\rm aug}:=C(G_{\rm aug})$；条件期望先固定$G$，只对新增边平均。对独立内部块模型令$W_{\rm aug}$为增广邻接矩阵的逐元期望；对正则内部块模型，固定一个实际增广样本并记其邻接矩阵为$A_{\rm aug}$。将B.4的行补齐与整数化操作分别作用于这两种输入，所得$(N+1)$阶0、1辅助矩阵统一记为$W^\sharp_{\rm aug}$。它不是随机竞赛图的邻接矩阵。

$$
\mathbb EC_{{\rm aug},\mathcal T}
=C(W_{\rm aug})\le\operatorname{per}W_{\rm aug}
\le\operatorname{per}W^\sharp_{\rm aug},
$$

$$
C(G_{\rm aug})\le\operatorname{per}A_{\rm aug}
\le\operatorname{per}W^\sharp_{\rm aug}
\qquad(\mathcal R\text{ 的每个样本}).
$$

第一个等号只对独立内部块模型使用。第二行对每个样本逐个成立，不要求正则块内部边独立。

对于$\mathcal T$的增广期望矩阵，旧行和为$mb_i$；对于$\mathcal R$的每个实际增广样本，旧行和不超过$mb_i+1/2$。统一选择

$$
R_i'=\lceil mb_i+1/2\rceil=mb_i+\xi_i',
\qquad \frac12\le\xi_i'<\frac32.
$$

新行补到$R_0=N$。因为$b_i\le d-1/2$且$m\ge2$，$mb_i+1/2\le N-1/2$，所以$R_i'\le N$；同时$R_i'\ge m/2$。这些补齐目标都不超过增广矩阵的列数$N+1$，B.4的行操作适用。Brégman给出

$$
\log\operatorname{per}W^\sharp_{\rm aug}
\le m\sum_i\frac{\log(R_i'!)}{R_i'}
+\frac{\log(N!)}N.
$$

沿用$R_i'\ge m/4$、$R_i'\le N+1$计算旧行余项，并单列新行，

$$
\begin{aligned}
\log\operatorname{per}W^\sharp_{\rm aug}
&\le m\sum_i\log R_i'-N+\log N-1\\
&\quad+2d\log(2\pi(N+1))+\frac{4d}{3m}
+\frac{\log(2\pi N)}{2N}+\frac1{12N^2}\\
&\le m\sum_i\log R_i'-N+\log N-1\\
&\quad+(2d+1)\log(2\pi(N+1))+\frac{4d}{3m}+\frac1{12}.
\end{aligned}
$$

减去$\log((N+1)!/2^{N+1})\ge(N+1)\log((N+1)/2)-(N+1)$。主项逐项重组为

$$
\begin{aligned}
&m\sum_i\log R_i'+\log N-(N+1)\log((N+1)/2)\\
&=m\sum_i\log(2R_i'/N)
+N\log(N/(N+1))+\log(2N/(N+1)).
\end{aligned}
$$

第二项不大于0，第三项不大于$\log2$。而$\log(1+y)\le y$对于$y\ge0$由积分$\int_0^y(1+t)^{-1}dt\le y$得出，故

$$
\begin{aligned}
m\sum_i\log(2R_i'/N)
&=N\log\kappa+
m\sum_i\log(1+\xi_i'/(mb_i))\\
&\le N\log\kappa+\sum_i\frac{\xi_i'}{b_i}
\le N\log\kappa+3d.
\end{aligned}
$$

于是，使用$4d/(3m)\le2d/3$，

$$
\begin{aligned}
\log\frac{\operatorname{per}W^\sharp_{\rm aug}}{(N+1)!/2^{N+1}}
&\le N\log\kappa+\frac{11d}{3}+\frac1{12}+\log2\\
&\quad +(2d+1)\log(2\pi(N+1)).
\end{aligned}
$$

取指数，再将$(N+1)!/2^{N+1}=(N+1)\nu_{N+1}$代入，两个模型分别满足

$$
\frac{\mathbb EH_{\mathcal T}}{\mu_N}
\le 2e^{11d/3+1/12}(2\pi)^{2d+1}(N+1)^{2d+2}\kappa^N,
$$

$$
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
\le 2e^{11d/3+1/12}(2\pi)^{2d+1}(N+1)^{2d+2}\kappa^N.
$$

第二个界逐样本约束增广圈数，然后取期望；没有假定正则块内部的边独立。固定非正则基图时，右端对数除以$N$趋于$\log\kappa<0$，所以两者趋于0。

## B.6 有限多个基图如何给同一个阈值

::: {.proof title="有限多个基图的共同阈值"}

固定一个模型和一种计数，$T$表示一个基图普通同构类。令$f_T(m)$为该类随机吹胀模型的归一化期望，圈除以$\nu_N$、路径除以$\mu_N$；其极限记$\ell_T$。圆环对应$f_*(m)$和$\ell_*>0$，其余类满足$\ell_T<\ell_*$。有标号基图仅有$2^{\binom d2}$个，所以普通同构类也有限。圆环正则而传递基图不正则，故非圆环类集合非空。普通同构$\pi$给出样本双射$(i,a)\mapsto(\pi(i),a)$，保持各样本概率及圈、路径数，因此同类中归一化期望相同。于是

$$
\delta=\min_{T\not\cong\mathrm{Car}_d}(\ell_*-\ell_T)>0.
$$

非正则类的极限是0；正则非圆环类由严格谱间隙处理。对每个类取$M_T$，使$m\ge M_T$时归一化计数$f_T(m)$满足

$$
|f_T(m)-\ell_T|<\delta/3.
$$

圆环也取相同误差要求。令$M$为这些有限阈值的最大值，则

$$
f_*(m)-f_T(m)
>(\ell_*-\delta/3)-(\ell_T+\delta/3)
\ge\delta/3>0.
$$

最后对两种模型、两种计数的四个阈值再取最大值。正则内部模型始终只沿奇$m$。这证明存在性，但没有从非有效渐近定理中虚构一个数值阈值。

:::

## B.7 单调性中三角函数不等式的微积分证明

主文第一部分使用$\tan y\ge y+y^3/3$（$0\le y<\pi/2$）。令$f(y)=\tan y-y$，则

$$
f'(y)=\tan^2y\ge0,\qquad f(0)=0,
$$

所以$\tan y\ge y$。再令$g(y)=\tan y-y-y^3/3$，有

$$
g'(y)=\tan^2y-y^2\ge0,\qquad g(0)=0.
$$

所需不等式成立。又

$$
\alpha(x)=\int_0^1\frac{dt}{1+x^2t^2}
\ge\int_0^1(1-x^2t^2)\,dt=1-x^2/3,
$$

其中$(1+z)^{-1}-(1-z)=z^2/(1+z)\ge0$。这补全了单调性计算中的两个初等估计。

## 参考文献

1. N. C. Wormald. *Tournaments with many Hamilton cycles*. arXiv:2610.16245v1. [固定版本全文](https://arxiv.org/html/2610.16245v1)，[历史说明](https://arxiv.org/abs/2610.16245)。本文使用其模型定义、Theorem 1、4、5，并讨论Conjecture 1、2、6。
2. Yijia Fang and Hao Huang. *Maximizing directed cycles in tournaments*. arXiv:2608.06238v1. [固定版本第3节](https://arxiv.org/html/2608.06238v1#S3)。本文使用Corollary 3.4；四次矩等号另在附录B.3复算。
3. Noga Alon. *The maximum number of Hamiltonian paths in tournaments*. Combinatorica 10 (1990), 319-324. [作者提供全文](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)。本文使用第2节所列Brégman永久式界。
