# Wormald竞赛图猜想1、2、6：Hessian恒等式与随机块模型

刘星辰、叶祥宇

2026年10月19日。公开研究稿，版本1。

# 摘要

本文研究Wormald随机吹胀模型中的三个具体问题。我们把原文定义的对数角Hessian写成有限矩阵的压缩，证明其正定，并把模型渐近常数精确化为行列式比值。对圆环基图，这个比值有闭式；乘回正则内部块因子后，所得常数严格递增至$\cosh(1)/\cos(1)$，且可以计算其倒幂展开。结合明确引用的Fang–Huang矩比较和Wormald模型计数定理，再单独估计非正则基图，可推出固定奇基图阶数、块充分大时的唯一期望最大者。

本文提供针对[Wormald公开版本](https://arxiv.org/html/2610.16245v1)猜想1、2、6的证明稿。推导与程序由AI辅助完成，已经过本次逐式自检及精确有限计算，尚待作者和同行独立数学审阅，未获形式化认证。不据此主张历史优先权。模型结论不等于全体竞赛图的Hamilton精确极值定理。

# 原猜想、记号和本稿结论的对应

原猜想归属于N. C. Wormald。本文核对的固定版本是arXiv:2610.16245v1，上传于2026年10月12日；作者说明该文来自早期研究，并非2026年才提出这些问题。下面是统一本文记号后的转述。

固定奇数$d\ge3$，基图$T^*$有$d$个顶点；每个顶点替换成$m$个顶点，总阶数$N=dm$。块间方向由$T^*$决定。$\mathcal T(T^*,m)$的内部块独立均匀随机；$\mathcal R(T^*,m)$进一步要求每个内部块正则，因而$m$必须为奇数。用$C(G)$和$H(G)$分别表示Hamilton圈和路径数。

- 猜想1：固定$d$，当$m$充分大时，圆环基图在所有$d$阶基图中最大化$\mathbb E C(\mathcal T(T^*,m))$。本稿第二部分证明这一陈述，并得到唯一性、路径类比及正则内部块类比。
- 猜想2：圆环基图的正则内部块极限常数，在奇$d\to\infty$时收敛。第一部分给出极限值、严格单调性和误差展开。
- 猜想6：每个至少三阶的正则基图，原文Hessian行列式$\mathcal H$非零，且$d/\mathcal H$是有理数的平方。第一部分给出精确公式。

原文猜想3涉及全体充分大奇阶竞赛图的精确圈极值，不在本稿证明范围内。我们也不借本稿宣布原文猜想4、5的全局陈述得到证明。

# 阅读路线与外部输入

第一部分第1至7节只使用有限维线性代数和求导。第8节引用Wormald的Theorem 1、4、5，将有限Hessian接到随机模型的期望渐近。第9至11节计算圆环闭式及展开。

第二部分第3节使用Fang–Huang的Corollary 3.4；四次矩等号分类也可由附录A.3的四顶点计算直接核对。第二部分第8节使用Brégman的0、1永久式界。非正则基图单独处理，因此没有将正则Hessian公式用于不满足假设的图。

第三部分补齐本次发表前复核时展开的计算，包括行列式多项式、圆环同构、四次矩等号、路径增点的全部归一化项，以及有限阈值的选取。配套基础讲解另成一册。

本文所有$m\to\infty$均先固定$d$。随后讨论$d\to\infty$的模型常数时，没有交换极限，也没有获得最终阶数$N$的统一二阶误差。


# 第一部分：精确Hessian与模型常数

## 1. 对象、主公式与范围

令$d\ge3$为奇数，$A$为$d$阶正则竞赛图的邻接矩阵，

$$
S=2A+I-J,\quad S^T=-S,\quad S1=0,\qquad
C=S/d,\quad P_0=J/d.
$$

设

$$
B(y)=I-(A+\tfrac12I)\operatorname{diag}(y_1,\ldots,y_d),
\quad K(y)=\det B(y),\quad z=2/d.
$$

Wormald在$y=z1$附近由$K(y)=0$解出$y_d=h(y_1,\ldots,y_{d-1})$，并对

$$
\widetilde f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})
$$

取Hessian。记其矩阵为$\mathbf H$、行列式为$\mathcal H$。本文证明

$$
\boxed{
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,\qquad
E=(e_1-e_d,\ldots,e_{d-1}-e_d).}
$$

因此

$$
\boxed{
\mathcal H
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,\qquad
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}=:\rho_d(S).}
$$

右边正且有理。这给出了所读版本Conjecture 6的一般证明稿，而非只核对若干基图。该有限矩阵证明不使用此前研究中的永久式渐近展开、局部平衡、全局极值先验。

## 2. 固定谱隙与唯一的常数零方向

反对称奇异值成对且$\|S\|_F^2=d(d-1)$，所以

$$
\|C\|_{\rm op}^2\le\frac{d-1}{2d}<\frac12.
$$

令$u=1/\sqrt d$、$\Pi=I-uu^T$。因为$C1=0$，

$$
P_0C=CP_0=0,\qquad
P:=\frac{2A+I}{d}=P_0+C.
$$

在常数方向，$P$作用为1；在$u^\perp$上，$P$作用为$C$。因此

$$
B(z1)=I-P=\Pi-C
$$

恰有一维零空间，且在$u^\perp$上的限制$I-C$可逆。其限制行列式为

$$
\det_{u^\perp}(I-C)=\det(I-C)=\det(I+C)=:q>0.
$$

最后一个等式来自转置；正性来自成对纯虚谱。

## 3. 将奇异行列式化成一个标量隐函数

换用对数变量

$$
y_j=ze^{t_j},\qquad
\mathscr B(t)=I-P\operatorname{diag}(e^{t_j}).
$$

在分解$\mathbb C u\oplus u^\perp$下，定义

$$
D(t)=\Pi\mathscr B(t)\Pi\big|_{u^\perp}.
$$

$D(0)=I-C$在$u^\perp$可逆，因此小邻域内$D(t)^{-1}$解析。Schur补精确给

$$
\det\mathscr B(t)=\det D(t)\,\psi(t),
$$

$$
\psi(t)=u^T\mathscr B(t)u
-u^T\mathscr B(t)\Pi D(t)^{-1}\Pi\mathscr B(t)u.
$$

原点的两个交叉块都为零：

$$
u^T\mathscr B(0)\Pi=0,\qquad
\Pi\mathscr B(0)u=0,\qquad \psi(0)=0.
$$

所以求$\psi$的前两次导数时，二次乘积仅保留两个交叉块各被求导一次的项，不会出现未列出的逆矩阵导数项。

## 4. 一次导数与隐函数存在性

记$D_j=e_je_j^T$。在$t=0$处，

$$
\mathscr B_j=-PD_j,\qquad
\mathscr B_{jk}=-\delta_{jk}PD_j.
$$

因$u^TP=u^T$，第3节的零交叉块给

$$
\psi_j(0)=u^T\mathscr B_ju
=-u^TD_ju=-1/d.
$$

行列式的一次导数也完全明确：

$$
\partial_{t_j}\det\mathscr B(0)=q\psi_j(0)=-q/d,
$$

$$
K_{y_j}(z1)=z^{-1}(-q/d)=-q/2\ne0.
$$

这同时证明原文所需非零偏导条件，对任意消去坐标都成立。

还可避免把隐函数存在性作为额外黑盒。因为行列式对第$d$列线性，

$$
K(y)=K_0(y_1,\ldots,y_{d-1})+y_dK_1(y_1,\ldots,y_{d-1}),
$$

$$
K_1(z,\ldots,z)=-q/2\ne0,\qquad
h(y')=-K_0(y')/K_1(y').
$$

所以$h$是所需邻域内明确的有理函数，且$h(z,\ldots,z)=z$。定义

$$
g(t')=\log[h(ze^{t_1},\ldots,ze^{t_{d-1}})/z].
$$

对数取原点值0的分支，则$t_d=g(t')$、$g(0)=0$。后面只对这个明确函数作两次求导。

## 5. 二次导数逐项计算

令$U=(I-C)^{-1}$，在$u^\perp$上与$D(0)^{-1}$相同。两个交叉导数为

$$
u^T\mathscr B_j\Pi=-\frac1{\sqrt d}e_j^T\Pi,\qquad
\Pi\mathscr B_ku=-\frac1{\sqrt d}Ce_k.
$$

所以

$$
u^T\mathscr B_j\Pi D(0)^{-1}\Pi\mathscr B_ku
=\frac1d e_j^TUC e_k.
$$

对$j,k$交换再加一次，得到

$$
\psi_{jk}(0)
=-\frac{\delta_{jk}}d-\frac{(UC)_{jk}+(UC)_{kj}}d.
$$

因为$U$与$C$交换，$C^T=-C$，

$$
\begin{aligned}
UC+(UC)^T
&=C(I-C)^{-1}-C(I+C)^{-1}\\
&=C[(I-C)^{-1}-(I+C)^{-1}]\\
&=2C^2(I-C^2)^{-1}.
\end{aligned}
$$

因此令

$$
Q=(I+C^2)(I-C^2)^{-1}
=I+2C^2(I-C^2)^{-1},
$$

便有完整Hessian

$$
\boxed{\nabla_t^2\psi(0)=-Q/d.}
$$

## 6. 从标量曲面到原文的对数角Hessian

对$\psi(t',g(t'))=0$求一次导数：

$$
0=\psi_j+\psi_dg_j,\qquad g_j(0)=-1.
$$

再求一次：

$$
0=\psi_{jk}+\psi_{jd}g_k+\psi_{dk}g_j+\psi_{dd}g_jg_k+\psi_dg_{jk}.
$$

代入$g_j=g_k=-1$与$\psi_d=-1/d$：

$$
g_{jk}(0)=-(e_j-e_d)^TQ(e_k-e_d).
$$

原文的$\log h$满足

$$
\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})
=\log z+g(i\theta_1,\ldots,i\theta_{d-1}).
$$

每求一次$\theta$导数产生$i$，两次产生$i^2=-1$。于是

$$
\mathbf H_{jk}=-g_{jk}(0)
=(e_j-e_d)^TQ(e_k-e_d).
$$

这一步解释了符号为什么为正，不能将$t$变量的Hessian直接当作$\theta$变量的Hessian。

## 7. 正定性、行列式和有理平方

$C$的频率平方为$\lambda^2<1$时，$Q$对应的特征值是

$$
\frac{1-\lambda^2}{1+\lambda^2}>0.
$$

所以$Q\succ0$，而$E$满列秩，故$\mathbf H=E^TQE\succ0$。又$Qu=u$。在$u^\perp$取任意正交基矩阵$V$，写$E=VL$，则

$$
\det(E^TQE)=\det(L)^2\det(V^TQV).
$$

一方面，

$$
E^TE=I_{d-1}+J_{d-1},\qquad \det(E^TE)=d,
$$

因此$\det(L)^2=d$。另一方面$Q$的常数特征值为1，故$\det(V^TQV)=\det Q$。得到

$$
\mathcal H=d\det Q=d\,\frac{\det(I+C^2)}{\det(I-C^2)}.
$$

对称成对谱及矩阵乘法给

$$
\det(I+C^2)=\det(I+iC)^2,\qquad
\det(I-C^2)=\det(I+C)^2.
$$

两个右侧根均取正值，所以

$$
\frac d{\mathcal H}
=\left[\frac{\det(I+C)}{\det(I+iC)}\right]^2.
$$

$C$有理，$\det(I+C)$有理；$\det(I+iC)$的奇次主子式为零，偶次项为实有理。因此括号中的数为正有理数。

## 8. 与Wormald随机块模型的常数连接

以下渐近结论使用Wormald原文Theorem 1、4、5，不是重新证明其全部随机计数论证。固定基图$T^*$阶数$d$，每个顶点替换成$m$阶块，总顶点数是$N=dm$。

内部为独立均匀随机竞赛图的模型记$\mathcal T(T^*,m)$；内部条件为正则图的模型记$\mathcal R(T^*,m)$。由第7节消去Theorem 4中的Hessian非退化条件，并代入其常数，得到

$$
\frac{\mathbb EC_{\mathcal T}}{(N-1)!/2^N}
\longrightarrow\rho_d(S),\qquad
\frac{\mathbb EH_{\mathcal T}}{N!/2^{N-1}}
\longrightarrow\rho_d(S),
$$

$$
\frac{\mathbb EC_{\mathcal R}}{(N-1)!/2^N}
\longrightarrow e^{1/d}\rho_d(S),\qquad
\frac{\mathbb EH_{\mathcal R}}{N!/2^{N-1}}
\longrightarrow e^{1/d}\rho_d(S).
$$

这里$m\to\infty$且$d$固定；$\mathcal R$沿合法的奇$m$。这些是随机模型的期望常数，不是某个固定图的Hamilton计数恒等式。

## 9. 圆环基图给出完整闭式

奇阶圆环符号矩阵与传递符号矩阵$T_d$带符号置换相似。$T_d$的偶阶主子式为1，奇阶主子式为0，所以

$$
\det(I+tT_d)=\frac{(1+t)^d+(1-t)^d}{2}.
$$

于是

$$
\boxed{
\rho_d(\mathrm{Car}_d)
=\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}.}
$$

它直接恢复原文表中$2,44/19,3032/1231,\ldots$，不需要逐项求多元Hessian。正则块模型的常数为

$$
\mathfrak r_d=e^{1/d}\rho_d(\mathrm{Car}_d).
$$

## 10. 严格单调逼近共同常数

令$x=1/d$，在$0<x\le1/3$上定义

$$
\alpha(x)=\frac{\arctan x}{x},\qquad
\beta(x)=\frac{\operatorname{artanh}x}{x}.
$$

闭式化为

$$
\mathfrak r(x)=
\exp(p(x))\frac{\cosh\beta(x)}{\cos\alpha(x)},\qquad
p(x)=x+\frac{\log(1-x^2)-\log(1+x^2)}{2x}.
$$

逐项展开对数的奇幂：

$$
p(x)=-\sum_{j\ge1}\frac{x^{4j+1}}{2j+1},\qquad p'(x)<0.
$$

置$v=1-\alpha$。积分式给

$$
\beta'(x)=\int_0^1\frac{2xt^2}{(1-x^2t^2)^2}\,dt,\quad
v'(x)=\int_0^1\frac{2xt^2}{(1+x^2t^2)^2}\,dt>0.
$$

对每个$t$比较被积函数：

$$
\beta'(x)\le
\left(\frac{1+x^2}{1-x^2}\right)^2v'(x)\le\frac{25}{16}v'(x).
$$

又$\beta(x)\le\beta(1/3)=\frac32\log2$，故

$$
\tanh\beta(x)\le\tanh(\tfrac32\log2)=\frac79.
$$

由$\alpha(x)\ge1-x^2/3\ge26/27$及$\tan y\ge y+y^3/3$，

$$
\tan\alpha(x)\ge\frac{26}{27}+\frac13\left(\frac{26}{27}\right)^3
>\frac79\frac{25}{16}.
$$

最后一个差精确为$42833/944784>0$。所以

$$
\begin{aligned}
\frac d{dx}\log\mathfrak r(x)
&=p'(x)+\tanh\beta\,\beta'(x)-\tan\alpha\,v'(x)\\
&\le p'(x)-\frac{42833}{944784}v'(x)<0.
\end{aligned}
$$

因此$\mathfrak r_d$随奇数$d\ge3$严格增加，且

$$
\boxed{\mathfrak r_d\uparrow L=\cosh1/\cos1.}
$$

这证明所读版本Conjecture 2的极限存在，并给出极限值与严格单调性；不依赖对有限数值表的外推。

## 11. 显式误差与原文奇次系数现象

令$b=\tanh1$、$h=\tan1$。有

$$
\beta=1+x^2/3+x^4/5+O(x^6),\qquad
\alpha=1-x^2/3+x^4/5+O(x^6),
$$

$$
\log(\mathfrak r(x)/L)
=a_2x^2+\ell_4x^4-\frac13x^5+O(x^6),
$$

$$
a_2=(b-h)/3,\qquad
\ell_4=(b+h)/5+(2+h^2-b^2)/18.
$$

指数恢复时，四次项还包括$a_2^2/2$。令$a_4=\ell_4+a_2^2/2$，则

$$
\boxed{
\mathfrak r_d
=L\left[1+\frac{a_2}{d^2}+\frac{a_4}{d^4}
-\frac1{3d^5}+O(d^{-6})\right].}
$$

特别地，$d^{-1},d^{-3}$系数精确为零，$d^{-5}$系数为$-L/3$。数值上，

$$
La_2\approx-0.757603347512237,\qquad La_4\approx2.035222101370122.
$$


更完整地，$\cosh\beta/\cos\alpha$是$x$的偶解析函数，所有奇次来自$\exp[-\sum_{j\ge1}x^{4j+1}/(2j+1)]$。这说明奇次消失的具体来源，不是数值拟合。

这里$d$是先固定再取块极限的基图阶数，$N=dm$才是最终图阶数。上述$d^{-2}$不能改写成全体竞赛图极值的$O(N^{-2})$余项，也没有交换两个极限。

## 12. 独立核查与结论边界

配套Hessian核查程序实际退出0：73组正则基图，包括三、五阶全部有标号正则图；11,724个Hessian元素、345个不同消去坐标的Hessian行列式用精确分数一致。

独立路径是先展开$\det(I-P\operatorname{diag}(e^t))$的全部主子式，直接取一、二次导数，再按隐函数公式求Hessian；没有用本稿闭式生成待比较的左端。原文圆环表及九阶三角形吹胀表的有理数也恢复一致。单调性的有理余量精确检查；大$d$展开误差仅作高精度诊断。

本稿给出所引用版本猜想6和2的证明稿及显式模型常数，但仍需独立数学审阅，也未穷尽历史文献的新颖性调查。它不证明原文Conjecture 3的全体竞赛图精确圈极值。

# 第二部分：固定基图的唯一期望极值

## 1. 准确的极值对象

固定奇数$d\ge3$。对任意$d$阶竞赛图$T^*$，将每个顶点替换成一个$m$阶随机竞赛图，块间全部边依照$T^*$。总阶数$N=dm$。

内部独立均匀随机的模型记$\mathcal T(T^*,m)$；内部独立均匀正则的模型记$\mathcal R(T^*,m)$，后一模型要求$m$奇。圈、路径期望分别记$\mathbb EC,\mathbb EH$，归一化为

$$
\nu_N=(N-1)!/2^N,\qquad \mu_N=N!/2^{N-1}.
$$

本稿证明：对每个固定$d$，存在$M_d$，使全部$m\ge M_d$时，这两个模型的圈期望与路径期望，均由普通同构于$\mathrm{Car}_d$的基图达到最大，且只有这些基图取等号。$\mathcal R$沿合法$m$。

这给出了所读Wormald版本Conjecture 1及路径类比的证明稿。它比较的是随机吹胀模型的期望，不是说每个样本都最优，也不证明全体$N$阶竞赛图的精确Hamilton极值。

## 2. 正则基图常数已经是谱比值

对正则基图，第一部分给出

$$
\lim_{m\to\infty}\frac{\mathbb EC_{\mathcal T}}{\nu_N}
=\lim_{m\to\infty}\frac{\mathbb EH_{\mathcal T}}{\mu_N}
=\rho_d(S),
$$

$$
\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
=e^{1/d}\rho_d(S),
$$

$$
\rho_d(S)=\frac{\det(I+S/d)}{\det(I+iS/d)}.
$$

因此正则基图间的比较变成一个有限矩阵问题。非正则基图不能直接套这条公式；第7—10节另证其指数损失。

## 3. 正确使用Fang–Huang的全部乘积比较

以下$K_d$专指Fang–Huang的对称比较矩阵，不能与删集包含核混用。准确元素为

$$
(K_d)_{ij}=\begin{cases}
1,&i+j\le d,\\
0,&i+j=d+1,\\
(-1)^{i+j-d-2},&i+j\ge d+2.
\end{cases}
$$

外部输入为

$$
(S_1\cdots S_p x)^*\prec_w K_d^p x^*,
$$

右端为非负降序向量；等号时全部后缀比较也为向量等号。另用其定理1.4在四次迹的等号分类。没有把其$4k$迹定理直接换成$4k+2$。

对非负降序$u\prec_w v$，

$$
\sum_i(u_i-t)_+
=\max_r\left(\sum_{i\le r}u_i-rt\right)
\le\max_r\left(\sum_{i\le r}v_i-rt\right).
$$

积分得

$$
\|u\|_2^2
=2\int_0^\infty\sum_i(u_i-t)_+\,dt\le\|v\|_2^2.
$$

若平方和相等，连续非负的被积差处处为零；其折点、斜率确定全部坐标，故$u=v$。

对标准基$e_j$，

$$
\|S^pe_j\|_2^2\le\|K_d^pe_1\|_2^2.
$$

## 4. 比较矩阵右端与传递矩阵精确相同

令$T_d$上三角为1、下三角为$-1$。设$R_0$为反序矩阵，$D_0=\operatorname{diag}(1,-1,\ldots)$。逐元素先算

$$
(D_0K_dR_0)_{ij}=(-1)^{i-1}(K_d)_{i,d+1-j}
=\begin{cases}(-1)^{i-1},&i<j,\\0,&i=j,\\(-1)^j,&i>j.\end{cases}
$$

该矩阵反对称。在“奇数指标升序、偶数指标降序”的顺序中，较早点到较晚点的元素均为1：两个奇指标使用上三角的$(-1)^{i-1}$；两个偶指标使用下三角的$(-1)^j$；奇点到偶点则按$i<j$或$i>j$分别使用同样的两个式子。令$\Lambda$为此同一行列置换，得到

$$
\Lambda^TD_0K_dR_0\Lambda=T_d.
$$

置$U=D_0\Lambda$。利用$K_d^T=K_d$，

$$
T_dT_d^T=U^TK_d^2U,\qquad Ue_1=e_1.
$$

所以

$$
(-1)^p(T_d^{2p})_{11}=(K_d^{2p})_{11}
=\|K_d^pe_1\|_2^2.
$$

带负绕回循环移位$Ce_j=e_{j+1}$、$Ce_d=-e_1$与$T_d$交换，故$T_d^{2p}$全部对角元相同。因此

$$
d\|K_d^pe_1\|_2^2
=(-1)^p\operatorname{tr}T_d^{2p}=\|T_d^p\|_F^2.
$$

对第3节的列比较求和，得到每个整数$p\ge1$的有限不等式

$$
\boxed{\|S^p\|_F^2\le\|T_d^p\|_F^2.}
$$

带负移位的逐元素验证另见附录A.2；上述矩阵关系明确了奇次幂Frobenius比较的来源。

## 5. 谱比值上界及等号

若$S$的频率为$\pm i\lambda_j$，置$x_j=\lambda_j^2/d^2<1/2$。积分几何级数给

$$
\log\frac{1+x}{1-x}=2\sum_{r\ge0}\frac{x^{2r+1}}{2r+1}.
$$

于是

$$
\log\rho_d(S)
=\sum_{r\ge0}\frac{\|S^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}
\le\log\rho_d(T_d).
$$

级数绝对收敛，每个矩亏损非负。若取等号，则$p=3$的Frobenius比较取等号，每列亦取等号：

$$
(S^3e_j)^*=K_d^3e_1.
$$

Fang–Huang的后缀等号给

$$
(S^2e_j)^*=K_d^2e_1.
$$

求平方和并按列求和，得$\operatorname{tr}S^4=\operatorname{tr}T_d^4$。由其四次等号分类（亦见附录A.3的独立计算），

$$
S=Q^TT_dQ
$$

其中$Q$为带符号置换。反之该关系显然保持谱比值。因此

$$
\boxed{\rho_d(S)\le r_d:=\rho_d(T_d),}
$$

全部等号恰为带符号置换传递矩阵。

如果$S$还正则，普通重编号后可写$S=D_eT_dD_e$，$e_i=\pm1$。正则性给$T_de=0$；相邻行相减给

$$
0=(T_de)_i-(T_de)_{i+1}=e_i+e_{i+1}.
$$

故$e$必须交替。该奇阶切换图普通同构于$\mathrm{Car}_d$，例如用$\phi(i)=((d+1)/2)i\bmod d$直接检查边方向。因此正则基图中的等号恰为圆环普通同构类。

## 6. 正则非参考基图还有明确的常数间隙

若正则$S$不普通同构于圆环，第5节的$p=3$亏损必为正。对任意竞赛符号矩阵，模2有$S\equiv J+I$，且

$$
(J+I)^3\equiv I+(1+d+d^2)J\equiv I+J\pmod2.
$$

故$S^3$的非对角元均为奇数，对角为0。奇数平方模8为1，而反对称位置成对，所以

$$
\|S^3\|_F^2
=2\sum_{i<j}(S^3_{ij})^2\equiv d(d-1)\pmod{16}.
$$

正亏损因而至少16。保留对数级数的$p=3$项：

$$
\log(r_d/\rho_d(S))\ge16/(3d^6),
$$

$$
\boxed{r_d-\rho_d(S)\ge r_d(1-e^{-16/(3d^6)})>0.}
$$

该间隙只针对固定基图的极限常数，不给有限块大小$m$的显式收敛阈值。

## 7. 非正则基图必须单独处理

令基图出度为$d_i$。定义

$$
a_i=\frac{2d_i+1}{d}>0,\qquad
\kappa=\left(\prod_{i=1}^d a_i\right)^{1/d}.
$$

因为$\sum_i d_i=d(d-1)/2$，

$$
\frac1d\sum_i a_i=1.
$$

算术—几何平均给$\kappa\le1$，且取等号当且仅当全部$d_i=(d-1)/2$。所以非正则基图满足$\kappa<1$。

还可保留比分的明确损失。令$s_i=2d_i-(d-1)$，则$a_i=1+s_i/d\in(0,2)$。对$0<a<2$，Taylor积分式给

$$
\log a=(a-1)+(a-1)^2\int_0^1(1-t)
\frac{-1}{[1+t(a-1)]^2}\,dt
\le(a-1)-\frac18(a-1)^2.
$$

所以

$$
\boxed{\log\kappa\le-\frac{\|s\|^2}{8d^3}.}
$$

奇$d$的比分为偶数，非正则时因$\sum_i s_i=0$有$\|s\|^2\ge8$，故$\kappa^N\le e^{-N/d^3}$。这使第9—10节的指数衰减率有一个统一、明确的下界。

对于$\mathcal T$，令$W$为邻接矩阵的逐元期望：块间为0或1，块内不同顶点为$1/2$，对角为0。每个Hamilton圈使用不同无序顶点对，相关内部随机边独立，故

$$
\mathbb EC_{\mathcal T}=C(W)\le\operatorname{per}W.
$$

不需要错误地声称$\mathbb E\operatorname{per}A=\operatorname{per}W$；后者的二圈项不符合竞赛图互斥方向。

## 8. 加权矩阵的整数行和舍入与Brégman界

第$i$类顶点在$W$中的行和为

$$
r_i=md_i+(m-1)/2=m(d_i+\tfrac12)-\tfrac12.
$$

先把行和补到$R_i=\lceil r_i\rceil$，每元仍保持在$[0,1]$。固定其余行，永久式是该行元素的线性函数；在$[0,1]^N$且整数行和$R_i$的多面体上，线性最大值可在一个0、1行达到。逐行替换得到0、1矩阵$V$，满足

$$
\operatorname{per}W\le\operatorname{per}V,\qquad
\text{第$i$类每行有$R_i$个1}.
$$

使用[Brégman不等式（Alon论文第2节Lemma 2.1所列版本）](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)，

$$
\operatorname{per}W\le\prod_{i=1}^d(R_i!)^{m/R_i}.
$$

这是对加权矩阵的行舍入后应用原0、1定理，不是未经说明引用一个加权版本。

## 9. 计算指数损失，不丢掉归一化尺度

固定$d$、$m\to\infty$。有

$$
R_i=m(d_i+\tfrac12)+O(1),\qquad R_i\ge m/4
$$

最终一致成立。Stirling带余项给

$$
\frac{\log(R_i!)}{R_i}
=\log R_i-1+O\left(\frac{\log m}{m}\right).
$$

所以

$$
\log\operatorname{per}W
\le m\sum_i\log R_i-N+O_d(\log N).
$$

又

$$
\log(N!/2^N)=N\log(N/2)-N+O(\log N).
$$

两式相减，并使用$2R_i/N=a_i+O_d(m^{-1})$：

$$
\begin{aligned}
\log\frac{\operatorname{per}W}{N!/2^N}
&\le m\sum_i\log(2R_i/N)+O_d(\log N)\\
&=m\sum_i\log a_i+O_d(\log N)\\
&=N\log\kappa+O_d(\log N).
\end{aligned}
$$

因此存在仅依赖$d$的常数$c_d,C_d$，使

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N}
\le C_dN^{c_d}\kappa^N\longrightarrow0.
$$

从$N!/2^N$换到$\nu_N$多出的$N$已计入多项式因子。

与第7节合并，右边还可写为

$$
C_dN^{c_d}\exp[-N\|s\|^2/(8d^3)]
\le C_dN^{c_d}e^{-N/d^3}.
$$

## 10. 路径与正则内部块的相同结论

对路径，添加一个新顶点，其与旧顶点的方向独立均匀。每条旧Hamilton路径以概率$1/4$闭合成经过新顶点的圈，故

$$
\mathbb EC_{\rm aug}=\tfrac14\mathbb EH,\qquad
4\nu_{N+1}=\mu_N.
$$

在$\mathcal T$中，对增广期望矩阵应用第8—9节。旧行和变为$m(d_i+1/2)$，新行和为$N/2$；仅多一行，旧行的$O(1)$改变及新行对数项不改变$N\log\kappa$主项。因此

$$
\frac{\mathbb EH_{\mathcal T}}{\mu_N}
\le C'_d(N+1)^{c'_d}\kappa^N\longrightarrow0.
$$

在$\mathcal R$中，每个实际样本的旧行和都准确为$md_i+(m-1)/2$。所以圈的Brégman界可以直接逐样本使用。增广后旧行最多增加1，新行最多为$N$；这一个额外行与旧行$O(1)$变化同样只改变多项式因子。故

$$
\frac{\mathbb EC_{\mathcal R}}{\nu_N}\longrightarrow0,\qquad
\frac{\mathbb EH_{\mathcal R}}{\mu_N}\longrightarrow0
$$

且均有多项式乘$\kappa^N$的指数上界。内部若使用原文的三角分解正则模型，在其定义成立的阶数上，逐样本行和相同，结论亦成立。

## 11. 从极限常数推出充分大块阶数的精确期望极值

固定$d$后，只有有限多个有标号基图。正则基图中，圆环的极限常数为$r_d$（或$e^{1/d}r_d$），其余正则基图有第6节的正间隙。非正则基图的归一化期望趋于0。

对每个非参考基图分别取足够大的$m$，使其实际归一化期望严格小于圆环；再对有限个阈值取最大值，即得第1节的$M_d$及唯一普通同构类。这一步合法地利用$d$固定，不声称该阈值对增长$d$统一。

## 12. 完成了什么，尚未完成什么

第一部分给出所读Wormald版本猜想6的有限代数证明及猜想2的极限、单调性；本稿在明确引用其原计数定理和Fang–Huang比较后，得到猜想1及路径类比的固定基图期望结论。

这些结果将本文的谱比值与原随机模型常数准确等同，摆脱逐个基图计算Hessian。没有由此证明Wormald猜想3的全体竞赛图圈极值，也没有给出全体竞赛图路径数新的统一误差、有效$M_d$，或对增长基图与块阶数同时极限的结论。一般论证仍待独立数学审阅，历史文献归属尚未穷尽，不主张优先权。

# 第三部分：发表前复核补充计算

## A.1 传递符号矩阵的行列式多项式

令$T_n$上三角为1、下三角为$-1$，记$F_n(t)=\det(I+tT_n)$。下面直接用行变换证明第一部分第9节的闭式，不把偶阶主子式的值作为未说明的输入。

对前$n-1$行同时作$R_i\leftarrow R_i-R_{i+1}$。该行变换由一个对角为1的上三角矩阵实施，行列式不变。所得矩阵的前$n-1$行只有

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

利用$1-r=2t/(1+t)$，括号化为

$$
\begin{aligned}
1-t\sum_{k=1}^{n-1}r^k
&=1-\frac{tr(1-r^{n-1})}{1-r}\\
&=1-\frac{1-t}{2}(1-r^{n-1})\\
&=\frac{1+t}{2}+\frac{1-t}{2}r^{n-1}.
\end{aligned}
$$

所以

$$
F_n(t)=\frac{(1+t)^n+(1-t)^n}{2}.
$$

两端都是多项式，已在除两个点以外的所有$t$相等，故在$t=-1,0$也相等。代入$t=1/d$与$t=i/d$，得到圆环模型的行列式比值。

## A.2 交替切换与圆环的普通同构

设$d=2q+1$。对传递矩阵作交替切换，$e_i=(-1)^{i-1}$、$D_e=\operatorname{diag}(e_i)$。当$i<j$、$\Delta=j-i$时，

$$
(D_eT_dD_e)_{ij}=(-1)^\Delta.
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

第二部分还用到传递矩阵的幂有相同对角元。令$Ze_j=e_{j+1}$（$j<d$）、$Ze_d=-e_1$。当$i,j<d$时，

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

## A.3 四次矩等号分类的独立四顶点证明

这里给出与所引Fang–Huang四次等号结论一致的有限计算，方便独立检查第二部分的等号链。

四阶反对称矩阵写为

$$
M=\begin{pmatrix}
0&a&b&c\\
-a&0&d&e\\
-b&-d&0&f\\
-c&-e&-f&0
\end{pmatrix}.
$$

按行展开并合并同类项，

$$
\begin{aligned}
\det M
&=a^2f^2+b^2e^2+c^2d^2
-2abef+2acdf-2bcde\\
&=(af-be+cd)^2.
\end{aligned}
$$

若六个变量均为$\pm1$，括号是三个$\pm1$的和，故行列式为1或9。设$D_4(S)$是四顶点主子式等于9的个数。行列式系数展开给

$$
\det(I+tS)=1+e_2t^2+e_4t^4+O(t^6),
$$

$$
e_2=\binom d2,\qquad e_4=\binom d4+8D_4(S).
$$

对特征值逐个使用$\log(1+t\lambda)$的幂级数：

$$
\log\det(I+tS)
=-\frac{t^2}{2}\operatorname{tr}S^2
-\frac{t^4}{4}\operatorname{tr}S^4+O(t^6).
$$

另一方面，

$$
\log(1+e_2t^2+e_4t^4+O(t^6))
=e_2t^2+(e_4-e_2^2/2)t^4+O(t^6).
$$

比较四次系数：

$$
\operatorname{tr}S^4=2\binom d2^2-4\binom d4-32D_4(S).
$$

传递矩阵每个四顶点主子式都是1，因此

$$
\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S).
$$

若取等号，$D_4(S)=0$。作对角符号切换使第一行非对角元全为1。任取另外三个顶点$i<j<k$，四顶点行列式为

$$
\det S[\{1,i,j,k\}]=(s_{jk}-s_{ik}+s_{ij})^2.
$$

如果$i,j,k$形成有向三圈，则$s_{ij}=s_{jk}=-s_{ik}$，右端为9，矛盾。因此剩余顶点无有向三圈。若$i\to j$且$j\to k$，必有$i\to k$，否则就是三圈；这证明其方向关系传递，故可按全序重编号。第一顶点指向所有其余顶点，整个切换图是传递图。

由此，四次矩取等当且仅当$S$与$T_d$带符号置换相似。$d=3$时其余两点自动传递，同一论证仍成立。

## A.4 逐行整数化为什么合法

第二部分第8节先补齐行和，再逐行使永久式不减。补齐是可行的：若一行当前和为$r$，目标为$R=\lceil r\rceil\le L$，则该行剩余容量为

$$
\sum_{j=1}^L(1-w_j)=L-r\ge R-r.
$$

保持其他行不动，永久式对当前行是

$$
\operatorname{per}W=\sum_{j=1}^L w_jc_j,\qquad c_j\ge0.
$$

若一行有至少两个严格介于0和1的元素$w_a,w_b$，在保持$w_a+w_b$不变时，向系数较大的坐标移动质量，直到至少一元变为0或1；线性目标不减，非整数元素数下降。重复后至多剩一个非整数元素；但总和$R$为整数，最后一个也必须为整数。所以每一行都能替换成0、1行，且永久式不减。按行完成此过程即可使用Brégman界。

## A.5 路径增点后全部对数项的计算

先固定一个$N$顶点竞赛图，并加一个新顶点$v$，与旧顶点的边独立公平定向。每条旧Hamilton路径$x_1\to\cdots\to x_N$对应唯一的候选圈

$$
v\to x_1\to\cdots\to x_N\to v.
$$

需要的两条新边相互独立，概率为$1/4$。删除$v$又把每个增广Hamilton圈唯一还原成旧路径，因此

$$
\mathbb E[C_{\rm aug}\mid G]=H(G)/4.
$$

再对$G$平均，并用

$$
4\nu_{N+1}=\frac{4N!}{2^{N+1}}
=\frac{N!}{2^{N-1}}=\mu_N,
$$

便有完全相同的归一化期望：

$$
\frac{\mathbb EH(G)}{\mu_N}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

写$b_i=d_i+1/2$，$a_i=2b_i/d$。旧行整数上界统一写作$R_i'=mb_i+O(1)$。独立内部模型的新行整数上界为$R_0=\lceil N/2\rceil$；正则内部块的逐样本证明可把新行补至$R_0=N$。两种情况下$R_0$都与$N$同阶。

Brégman与Stirling给

$$
\begin{aligned}
\log\operatorname{per}V_{\rm aug}
&\le m\sum_{i=1}^d\frac{\log(R_i'!)}{R_i'}
+\frac{\log(R_0!)}{R_0}\\
&=m\sum_{i=1}^d\log R_i'-N+\log R_0-1
+O_d(\log N).
\end{aligned}
$$

减去$\log((N+1)!/2^{N+1})$，得到

$$
\begin{aligned}
\log\frac{\operatorname{per}V_{\rm aug}}
{(N+1)!/2^{N+1}}
&\le m\sum_i\log\frac{2R_i'}N
+N\log\frac N{N+1}\\
&\quad+\log\frac{2R_0}{N+1}+O_d(\log N).
\end{aligned}
$$

逐项估计：

$$
\frac{2R_i'}N=a_i+O_d(m^{-1}),
$$

$$
m\sum_i\log\frac{2R_i'}N
=m\sum_i\log a_i+O_d(1)=N\log\kappa+O_d(1),
$$

$$
N\log\frac N{N+1}=-1+O(N^{-1}),\qquad
\log\frac{2R_0}{N+1}=O(1).
$$

因此主项仍为$N\log\kappa$。从$(N+1)!/2^{N+1}$换成$\nu_{N+1}$只多一个$N+1$因子，计入多项式即可：

$$
\frac{\mathbb EH}{\mu_N}
\le C_d(N+1)^{c_d}\kappa^N.
$$

这补全了“只改变多项式因子”的每个归一化步骤。

## A.6 有限多个基图如何给同一个阈值

固定一个模型和一种计数，其圆环极限为$\ell_*>0$，其他普通同构类的极限为$\ell_T<\ell_*$。因为基图有限，

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

## A.7 单调性中三角不等式的微积分证明

第一部分使用$\tan y\ge y+y^3/3$（$0\le y<\pi/2$）。令$f(y)=\tan y-y$，则

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

## A.8 本次复核结论与证明责任

本轮核对了原文三个猜想的量词、模型及Hessian定义；对Schur补的二阶导数、角变量的负号、基变换行列式中的$d$、弱主序的等号传递、非正则分支、路径归一化和两重极限的先后分别复算。未发现推翻上述主公式或固定基图结论的错误。本附录补齐原稿略写的计算，不改变结论范围。

配套程序检查的是精确有限恒等式和有限枚举，并记录高精度渐近诊断。它们不能替代任意阶证明，也不能认证所引用外部定理的全部分析细节。本稿没有声称已经获得同行认可、形式化认证或历史优先权。

## 参考文献

1. N. C. Wormald. *Tournaments with many Hamilton cycles*. arXiv:2610.16245v1. [固定版本全文](https://arxiv.org/html/2610.16245v1)，[历史说明](https://arxiv.org/abs/2610.16245)。本文使用其模型定义、Theorem 1、4、5，并讨论Conjecture 1、2、6。
2. Yijia Fang and Hao Huang. *Maximizing directed cycles in tournaments*. arXiv:2608.06238v1. [固定版本第3节](https://arxiv.org/html/2608.06238v1#S3)。本文使用Corollary 3.4；四次矩等号另在附录A.3复算。
3. Noga Alon. *The maximum number of Hamiltonian paths in tournaments*. Combinatorica 10 (1990), 319-324. [作者提供全文](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)。本文使用第2节所列Brégman永久式界。

