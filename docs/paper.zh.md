# Wormald竞赛图猜想1、2、6：Hessian恒等式与随机块模型

刘星辰

2026年10月19日。公开研究稿，版本0.2.2。

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


# 术语与记号约定

竞赛图是在每一对不同顶点之间恰选一个方向的完全图定向。邻接矩阵的第$i,j$元为1当且仅当$i\to j$，对角为0。正则竞赛图的每个顶点出度、入度均为$(d-1)/2$。

Hamilton路径按顶点的有向排列计数；Hamilton圈按循环起点识别，即旋转起点不产生新圈，也不把反向排列另作同一个有向圈。普通同构指保持边方向的顶点双射；本文的唯一性始终在这种同构意义下理解。

奇阶圆环图记为$\mathrm{Car}_d$，其定义为

$$
V(\mathrm{Car}_d)=\mathbb Z/d\mathbb Z,\qquad
i\to j\ \Longleftrightarrow\
(j-i)\bmod d\in\{1,\ldots,(d-1)/2\}.
$$

记$I_r$为$r$阶单位矩阵，$J_r$为$r$阶全一矩阵，$\mathbf1_r$为全一列向量，$e_j$为第$j$个标准基列向量，$\delta_{jk}$在$j=k$时为1、否则为0。省略矩阵下标时，阶数由乘法维数确定。转置记为上标$T$，虚数单位满足$i^2=-1$；$\log$在正实数上为自然对数，在复邻域使用文中说明的解析分支。

对实矩阵$M$，两种范数分别为

$$
\|M\|_F^2=\sum_{j,k}M_{jk}^2,\qquad
\|M\|_{\rm op}=\sup_{v\ne0}\frac{\|Mv\|_2}{\|v\|_2}.
$$

记$[d]=\{1,\ldots,d\}$。$M[U]$是行列都取自$U$的主子矩阵，约定$\det M[\varnothing]=1$。$u^\perp$是与实向量$u$正交的子空间，$\det_{u^\perp}$表示限制到该不变子空间后、在正交单位基中计算的行列式。

图上的$C(G),H(G)$分别是圈数、路径数；单独出现的$C=S/d$是矩阵，粗体$\mathbf H$是Hessian矩阵，花体$\mathcal H$是它的行列式。不同节中的局部符号按该节重新给出的定义解释。

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

取在$\theta=0$处的Hessian。记其矩阵为$\mathbf H$、行列式为$\mathcal H$。第4—6节将验证用于定义$h$和对数分支的条件，因而这里的定义不预先假定尚未证明的存在性。本文证明

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

## 2. 谱隙、常数方向与限制行列式

本文的$\mathbf1$为全一列向量；式子中不加粗的$1$若与矩阵相乘，也表示这个向量。由竞赛图的定义及正则性，

$$
A+A^T=J-I,\qquad
A\mathbf1=\frac{d-1}{2}\mathbf1,
$$

$$
S^T=2A^T+I-J
=2(J-I-A)+I-J=-S,
$$

$$
S\mathbf1
=2\frac{d-1}{2}\mathbf1+\mathbf1-d\mathbf1=0.
$$

$S$的$d(d-1)$个非对角元均为$\pm1$，因此

$$
\|S\|_F^2=\sum_{i\ne j}s_{ij}^2=d(d-1),
\qquad \|C\|_F^2=\frac{d-1}{d}.
$$

对归一化的实反对称矩阵$C$作正交基变换。其标准形由零块及二维块

$$
J_\lambda=\begin{pmatrix}0&\lambda\\-\lambda&0\end{pmatrix}
$$

组成。每个二维块对Frobenius范数平方贡献$2\lambda^2$。于是每个频率都满足

$$
2\lambda^2\le\sum_{\text{全部二维块}}2\lambda_j^2
=\|C\|_F^2=\frac{d-1}{d},
$$

$$
\|C\|_{\rm op}^2=\max_j\lambda_j^2
\le\frac{d-1}{2d}<\frac12.
$$

令$u=\mathbf1/\sqrt d$、$P_0=uu^T=J/d$、$\Pi=I-P_0$。逐式计算：

$$
u^Tu=1,\quad P_0^2=P_0,\quad
\Pi^2=I-2P_0+P_0^2=\Pi,
$$

$$
Cu=0,\qquad u^TC=-(Cu)^T=0,
\qquad CP_0=(Cu)u^T=0,\quad P_0C=u(u^TC)=0.
$$

又有

$$
P:=\frac{2A+I}{d}=P_0+C,\qquad
Pu=P_0u+Cu=u.
$$

若$u^Tv=0$，则$P_0v=u(u^Tv)=0$，所以$Pv=Cv$。在关键点，

$$
B(z\mathbf1)=I-P=\Pi-C,\qquad
B(z\mathbf1)u=0.
$$

在$u^\perp$上，该矩阵是$I-C$。若$x\in u^\perp$满足$(I-C)x=0$，则

$$
0=x^T(I-C)x=\|x\|_2^2-x^TCx=\|x\|_2^2,
$$

其中$x^TCx=-x^TCx$给出$x^TCx=0$。故$x=0$，限制矩阵可逆。

在二维块上，

$$
\det(I-J_\lambda)
=\det\begin{pmatrix}1&-\lambda\\\lambda&1\end{pmatrix}
=1+\lambda^2>0.
$$

$I-C$在常数方向上的特征值为1，所以

$$
q:=\det_{u^\perp}(I-C)
=\det(I-C)
=\prod_j(1+\lambda_j^2)>0.
$$

转置给出

$$
\det(I+C)=\det((I+C)^T)=\det(I-C)=q.
$$

## 3. 对数变量、分块矩阵与Schur消元

令$y_j=ze^{t_j}$，则

$$
\mathscr B(t)=B(ze^{t_1},\ldots,ze^{t_d})
=I-P\operatorname{diag}(e^{t_1},\ldots,e^{t_d}).
$$

取$u^\perp$的一组正交单位基作为$V$的列。矩阵$O=(u,V)$满足

$$
V^TV=I_{d-1},\quad V^Tu=0,\quad VV^T=\Pi,
\quad O^TO=OO^T=I_d.
$$

在这个基中写成

$$
O^T\mathscr B(t)O=
\begin{pmatrix}a(t)&b(t)\\c(t)&D(t)\end{pmatrix},
$$

$$
a=u^T\mathscr Bu,\quad b=u^T\mathscr BV,\quad
c=V^T\mathscr Bu,\quad D=V^T\mathscr BV.
$$

因为$\det(O)^2=1$，这次基变换不改变行列式。在$t=0$时，

$$
a(0)=0,\quad b(0)=0,\quad c(0)=0,
\qquad D(0)=V^T(I-C)V.
$$

第2节已经证明$D(0)$可逆，且$\det D(0)=q>0$。行列式连续，所以原点某个邻域内$\det D(t)\ne0$。逆矩阵公式

$$
D(t)^{-1}=\frac{\operatorname{adj}D(t)}{\det D(t)}
$$

说明逆的每个元素在这个邻域内解析。

实际实施分块行消元：

$$
\begin{pmatrix}1&-bD^{-1}\\0&I\end{pmatrix}
\begin{pmatrix}a&b\\c&D\end{pmatrix}
=
\begin{pmatrix}a-bD^{-1}c&0\\c&D\end{pmatrix}.
$$

左乘矩阵的行列式为1，右端为分块三角矩阵。因此，定义

$$
\psi(t)=a(t)-b(t)D(t)^{-1}c(t)
$$

后，得到精确恒等式

$$
\det\mathscr B(t)=\det D(t)\,\psi(t).
$$

在上述邻域内，$\det\mathscr B(t)=0$与$\psi(t)=0$等价，因为因子$\det D(t)$不为零。

## 4. 一阶、二阶导数及九个乘积项

记$F_j=e_je_j^T$，$R(t)=D(t)^{-1}$。指数矩阵只在第$j$列依赖$t_j$，故在原点

$$
\mathscr B_j=-PF_j,\qquad
\mathscr B_{jk}=-\delta_{jk}PF_j.
$$

由$u^TP=u^T$及$e_j^Tu=1/\sqrt d$，

$$
a_j(0)=-u^TPF_ju=-u_j^2=-1/d,
\qquad a_{jk}(0)=-\delta_{jk}/d.
$$

先列出乘积的一次导数：

$$
\partial_j(bRc)=b_jRc+bR_jc+bRc_j.
$$

再对$t_k$求导，全部九项为

$$
\begin{aligned}
\partial_k\partial_j(bRc)
={}&b_{jk}Rc+b_jR_kc+b_jRc_k\\
&+b_kR_jc+bR_{jk}c+bR_jc_k\\
&+b_kRc_j+bR_kc_j+bRc_{jk}.
\end{aligned}
$$

在原点$b=c=0$。上式第1、2、4、5、6、8、9项各含因子$b$或$c$，因此它们在原点均等于0。留下的两项是

$$
\partial_k\partial_j(bRc)(0)=b_j(0)R(0)c_k(0)+b_k(0)R(0)c_j(0).
$$

现在计算这些因子：

$$
b_j(0)=-u^TPe_je_j^TV
=-\frac1{\sqrt d}e_j^TV,
$$

$$
c_k(0)=-V^TPe_ke_k^Tu
=-\frac1{\sqrt d}V^TCe_k,
$$

其中$V^TP=V^TC$使用了$V^Tu=0$。令$U=(I-C)^{-1}$。由$C$保持$u^\perp$和$D(0)=V^T(I-C)V$，先得到以下等式；第二个等式对第一个等式左乘$U$、右乘$R(0)$，第三行使用$\Pi C=C$：

$$
(I-C)V=VD(0),\qquad UV=VR(0),
$$

$$
UC=U\Pi C=UVV^TC=VR(0)V^TC.
$$

因此，

$$
VR(0)V^TC=UC.
$$

于是两个二次乘积分别为

$$
b_jR(0)c_k=\frac1d e_j^TUC e_k=\frac{(UC)_{jk}}d,
$$

$$
b_kR(0)c_j=\frac1d e_k^TUC e_j=\frac{(UC)_{kj}}d.
$$

一次乘积导数在原点为0，因此

$$
\psi_j(0)=-1/d,\qquad
\psi_{jk}(0)=-\frac{\delta_{jk}+(UC)_{jk}+(UC)_{kj}}d.
$$

$C(I-C)=(I-C)C$，左右乘逆矩阵可得$CU=UC$。又

$$
(UC)^T=C^TU^T=-C(I+C)^{-1}.
$$

两个逆的差逐步化为

$$
\begin{aligned}
(I-C)^{-1}-(I+C)^{-1}
&=(I-C)^{-1}[(I+C)-(I-C)](I+C)^{-1}\\
&=2C(I-C)^{-1}(I+C)^{-1}\\
&=2C(I-C^2)^{-1}.
\end{aligned}
$$

所以

$$
\begin{aligned}
I+UC+(UC)^T
&=I+C[(I-C)^{-1}-(I+C)^{-1}]\\
&=I+2C^2(I-C^2)^{-1}\\
&=(I+C^2)(I-C^2)^{-1}=:Q.
\end{aligned}
$$

我们得到完整导数

$$
\boxed{\psi_j(0)=-1/d,\qquad
\nabla^2\psi(0)=-Q/d.}
$$

对行列式乘积求导。由于$\psi(0)=0$、$\det D(0)=q$，

$$
\begin{aligned}
\partial_{t_j}\det\mathscr B(0)
&=\partial_{t_j}(\det D)(0)\,\psi(0)+\det D(0)\psi_j(0)\\
&=0+q(-1/d)=-q/d.
\end{aligned}
$$

在原点$\partial y_j/\partial t_j=z$，因此

$$
zK_{y_j}(z\mathbf1)=-q/d,\qquad
K_{y_j}(z\mathbf1)=-\frac{q}{dz}=-q/2\ne0.
$$

这给出了每一个消去坐标所需的非零偏导。

## 5. 用明确的有理函数消去最后一个变量

行列式对第$d$列线性，而这一列关于$y_d$仿射，所以

$$
K(y)=K_0(y_1,\ldots,y_{d-1})
+y_dK_1(y_1,\ldots,y_{d-1}).
$$

由第4节的偏导计算，

$$
K_1(z,\ldots,z)=K_{y_d}(z\mathbf1)=-q/2\ne0.
$$

缩小邻域，使$K_1(y')\ne0$，即可明确写出

$$
h(y')=-\frac{K_0(y')}{K_1(y')}.
$$

因为$K(z\mathbf1)=0$，

$$
K_0(z,\ldots,z)+zK_1(z,\ldots,z)=0,
\qquad h(z,\ldots,z)=z.
$$

定义

$$
g(t')=\log\!\left[
\frac{h(ze^{t_1},\ldots,ze^{t_{d-1}})}z\right].
$$

原点处对数的自变量为1。由$h$连续且$h(z,\ldots,z)=z>0$，可进一步缩小邻域，使$|h(ze^{t'})/z-1|<1/2$，其中$ze^{t'}$表示逐坐标取指数。这个圆盘不含0，选取在1处值为0的解析对数分支后，

$$
g(0)=\log1=0,\qquad
t_d=g(t'),\qquad \psi(t',g(t'))=0.
$$

下面只对这个有理函数与解析对数的组合求导，不额外假定隐函数存在。

## 6. 完整链式法则与角变量的符号

这里$j,k\in\{1,\ldots,d-1\}$。链式法则先在曲面邻域内成立；将导数替换为第4节算出的常数时，只在$t'=0,\ t_d=g(0)=0$求值。特别地，$g_j(0)=-1$不是邻域内的恒等式。对$j\le d-1$，求一次导数：

$$
0=\psi_j+\psi_dg_j,\qquad
g_j(0)=-\frac{\psi_j(0)}{\psi_d(0)}
=-\frac{-1/d}{-1/d}=-1.
$$

对$t_k$再次求导，五项为

$$
0=\psi_{jk}+\psi_{jd}g_k+\psi_{dk}g_j
+\psi_{dd}g_jg_k+\psi_dg_{jk}.
$$

逐项代入第4节的导数与$g_j=g_k=-1$：

$$
0=-\frac{Q_{jk}}d+\frac{Q_{jd}}d
+\frac{Q_{dk}}d-\frac{Q_{dd}}d-\frac{g_{jk}}d.
$$

两边乘$d$，再移项：

$$
\begin{aligned}
g_{jk}(0)
&=-Q_{jk}+Q_{jd}+Q_{dk}-Q_{dd}\\
&=-(e_j-e_d)^TQ(e_k-e_d).
\end{aligned}
$$

对原文的$\log h$也选择同一个局部分支，使$h=z$时其值为实数$\log z$。由第5节对$g$的定义，原文的角函数满足

$$
\widetilde f(\theta)=\log z+g(i\theta_1,\ldots,i\theta_{d-1}).
$$

一次角导数为$i g_j(i\theta)$，二次角导数为$i^2g_{jk}(i\theta)$。因此

$$
\mathbf H_{jk}
=i^2g_{jk}(0)=-g_{jk}(0)
=(e_j-e_d)^TQ(e_k-e_d),
$$

$$
\boxed{\mathbf H=E^TQE.}
$$

## 7. 正定性、基变换因子与有理平方

在第2节的每个二维块上，$J_\lambda^2=-\lambda^2I_2$，因此

$$
(I+J_\lambda^2)(I-J_\lambda^2)^{-1}
=\frac{1-\lambda^2}{1+\lambda^2}I_2.
$$

由$\lambda^2<1/2$，这个系数为正。零块上的$Q$为单位矩阵，所以$Q\succ0$。
对$v\in\mathbb R^{d-1}$，

$$
Ev=(v_1,\ldots,v_{d-1},-\textstyle\sum_{j=1}^{d-1}v_j)^T.
$$

若$v\ne0$，前$d-1$个分量不全为0，故$Ev\ne0$，从而

$$
v^T\mathbf Hv=(Ev)^TQ(Ev)>0.
$$

接着保留基变换的体积因子。$E$的第$j,k$列内积为

$$
(e_j-e_d)^T(e_k-e_d)=\delta_{jk}+1.
$$

故$E^TE=I_{d-1}+J_{d-1}$。在全一方向该矩阵的特征值为$1+(d-1)=d$，
在与全一向量垂直的方向上特征值为1。因此

$$
\det(E^TE)=d\cdot1^{d-2}=d.
$$

写$E=VL$，其中$V$是$u^\perp$的正交基、$L$为可逆方阵：

$$
E^TQE=L^T(V^TQV)L,\qquad
E^TE=L^TL.
$$

取行列式分别得到

$$
\det(E^TQE)=\det(L)^2\det(V^TQV),\qquad
\det(L)^2=d.
$$

由$Cu=0$，

$$
Qu=(I+C^2)(I-C^2)^{-1}u=u.
$$

$Q$在第2节的实正交基中每个块都是实数乘单位矩阵，因此$Q$为实对称矩阵。于是$u^TQV=(Qu)^TV=u^TV=0$。故

$$
(u,V)^TQ(u,V)=
\begin{pmatrix}1&0\\0&V^TQV\end{pmatrix},
\qquad \det Q=\det(V^TQV).
$$

把两个行列式因子乘回：

$$
\mathcal H=d\det Q
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0.
$$

矩阵乘法及转置给出

$$
(I+iC)(I-iC)=I+C^2,\qquad
\det(I-iC)=\det((I-iC)^T)=\det(I+iC),
$$

$$
(I+C)(I-C)=I-C^2,\qquad \det(I-C)=\det(I+C).
$$

因此

$$
\det(I+C^2)=\det(I+iC)^2,\qquad
\det(I-C^2)=\det(I+C)^2.
$$

根的符号也逐块确定：

$$
\det(I+J_\lambda)=1+\lambda^2>0,\qquad
\det(I+iJ_\lambda)=1-\lambda^2>0.
$$

所以

$$
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}>0.
$$

最后证明有理性。行列式按单位列与$C$的列多线性展开：

$$
\det(I+tC)=\sum_{U\subseteq[d]}t^{|U|}\det C[U].
$$

对奇数阶$r=|U|$，

$$
\det C[U]=\det(C[U]^T)=\det(-C[U])
=(-1)^r\det C[U]=-\det C[U],
$$

所以该主子式为0。$C$有理，故

$$
\det(I+iC)
=\sum_{k=0}^{\lfloor d/2\rfloor}\sum_{\substack{U\subseteq[d]\\|U|=2k}}
(-1)^k\det C[U]\in\mathbb Q.
$$

$\det(I+C)$也为有理数。已经证明分子、分母均正，所以所得比值为正有理数。

## 8. 外部计数定理的输入与四个极限

本节明确引用Wormald的Theorem 1、4、5，不将其随机计数证明当作本稿已经重证的内容。
固定正则基图阶数$d$，内部块阶数$m$，最终阶数$N=dm$。下标$\mathcal T,\mathcal R$指定随机模型；例如$\mathbb EC_{\mathcal T}$是从$\mathcal T(T^*,m)$取随机图后圈数的期望，路径记号的含义一致。各块独立，在各自有标号的全部允许内部竞赛图中均匀选择。定义

$$
\nu_N=\frac{(N-1)!}{2^N},\qquad
\mu_N=\frac{N!}{2^{N-1}}.
$$

Wormald的Theorem 4在$\mathcal H\ne0$时给出

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N}
\longrightarrow\sqrt{d/\mathcal H}.
$$

第7节给出$\mathcal H>0$及其根式的正分支，因此这次代入为

$$
\lim_{m\to\infty}\frac{\mathbb EC_{\mathcal T}}{\nu_N}
=\sqrt{\frac d{d\det(I+C^2)/\det(I-C^2)}}
=\rho_d(S).
$$

Theorem 5把Theorem 4的圈计数换成路径计数，故

$$
\lim_{m\to\infty}\frac{\mathbb EH_{\mathcal T}}{\mu_N}
=\sqrt{d/\mathcal H}=\rho_d(S).
$$

Theorem 1给出正则内部块与独立随机内部块的期望之比：

$$
\frac{\mathbb EC_{\mathcal R}}{\mathbb EC_{\mathcal T}}
\longrightarrow e^{1/d}.
$$

对足够大的$m$，分母为正，因为其归一化极限$\rho_d(S)>0$。相乘得到

$$
\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\left(\frac{\mathbb EC_{\mathcal R}}{\mathbb EC_{\mathcal T}}
\frac{\mathbb EC_{\mathcal T}}{\nu_N}\right)
=e^{1/d}\rho_d(S).
$$

Theorem 5还把Theorem 1的计数换成路径，给出

$$
\frac{\mathbb EH_{\mathcal R}}{\mathbb EH_{\mathcal T}}
\longrightarrow e^{1/d}.
$$

于是第四个极限为

$$
\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm 奇}}}
\left(\frac{\mathbb EH_{\mathcal R}}{\mathbb EH_{\mathcal T}}
\frac{\mathbb EH_{\mathcal T}}{\mu_N}\right)
=e^{1/d}\rho_d(S).
$$

四次取极限都固定$d$。后两个只沿合法的奇$m$，不涉及$d$与$m$同时增长。

## 9. 圆环基图给出完整闭式

令$T_d$上三角为1、下三角为$-1$、对角为0。附录A.2给出圆环符号矩阵与$T_d$的带符号置换相似关系；附录A.1先证行列式闭式，再由最高次系数说明每个偶阶主子式为1、奇阶主子式为0。由此，

$$
\det(I+tT_d)=\frac{(1+t)^d+(1-t)^d}{2}.
$$

下式把图名放入$\rho_d$的括号时，指代该图的符号矩阵；普通重编号不改变行列式，因而取值与标签无关。于是

$$
\boxed{
\rho_d(\mathrm{Car}_d)
=\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}.}
$$

它直接恢复原文表中$2,44/19,3032/1231,\ldots$，不需要逐项求多元Hessian。正则块模型的常数为

$$
\mathfrak r_d=e^{1/d}r_d,\qquad r_d:=\rho_d(\mathrm{Car}_d).
$$

## 10. 闭式的实函数形式与严格单调性

令$x=1/d$，在$0<x\le1/3$上定义

$$
\alpha(x)=\frac{\arctan x}{x},\qquad
\beta(x)=\frac{\operatorname{artanh}x}{x},\qquad
\operatorname{artanh}x=\frac12\log\frac{1+x}{1-x}.
$$

先把分子与分母分别写成实函数。实对数的和与差给出

$$
\log(1\pm x)=\frac12\log(1-x^2)
\ \pm\operatorname{artanh}x.
$$

指数化并相加：

$$
(1+x)^{1/x}+(1-x)^{1/x}
=2(1-x^2)^{1/(2x)}\cosh\beta(x).
$$

当$0\le x\le1/3$时，$1\pm ix$的实部均为1，整段曲线都位于右半平面。在这个半平面选取与正实轴实对数一致的解析对数分支，得到

$$
\log(1\pm ix)=\frac12\log(1+x^2)\pm i\arctan x,
$$

$$
(1+ix)^{1/x}+(1-ix)^{1/x}
=2(1+x^2)^{1/(2x)}\cos\alpha(x).
$$

因此

$$
\mathfrak r(x)
=e^{p(x)}\frac{\cosh\beta(x)}{\cos\alpha(x)},\qquad
p(x)=x+\frac{\log(1-x^2)-\log(1+x^2)}{2x}.
$$

当$x=1/d$时，$1/x=d$是整数，上述复幂就是原来的多项式幂。
又$0<\alpha(x)\le1<\pi/2$，所以分母的余弦严格为正。

把两个对数的级数相减：

$$
\begin{aligned}
\log(1-x^2)-\log(1+x^2)
&=-2\sum_{j=0}^\infty\frac{x^{4j+2}}{2j+1},\\
p(x)&=x-\sum_{j=0}^\infty\frac{x^{4j+1}}{2j+1}
=-\sum_{j=1}^\infty\frac{x^{4j+1}}{2j+1},\\
p'(x)&=-\sum_{j=1}^\infty
\frac{4j+1}{2j+1}x^{4j}<0.
\end{aligned}
$$

对反正切与反双曲正切的积分作变量代换，得到

$$
\alpha(x)=\int_0^1\frac{dt}{1+x^2t^2},\qquad
\beta(x)=\int_0^1\frac{dt}{1-x^2t^2}.
$$

令$v=1-\alpha$，在积分内求导：

$$
\beta'(x)=\int_0^1\frac{2xt^2}{(1-x^2t^2)^2}\,dt,
\qquad
v'(x)=\int_0^1\frac{2xt^2}{(1+x^2t^2)^2}\,dt>0.
$$

对每个$t\in[0,1]$，

$$
\frac{2xt^2}{(1-x^2t^2)^2}
\le\left(\frac{1+x^2}{1-x^2}\right)^2
\frac{2xt^2}{(1+x^2t^2)^2},
$$

$$
\left(\frac{1+x^2}{1-x^2}\right)^2
\le\left(\frac{1+1/9}{1-1/9}\right)^2
=\left(\frac54\right)^2=\frac{25}{16}.
$$

故$\beta'(x)\le(25/16)v'(x)$。因为$\beta'(x)>0$，

$$
\beta(x)\le\beta(1/3)
=3\cdot\frac12\log\frac{1+1/3}{1-1/3}
=\frac32\log2,
$$

$$
\tanh\beta(x)
\le\frac{e^{3\log2}-1}{e^{3\log2}+1}
=\frac{8-1}{8+1}=\frac79.
$$

用$(1+z)^{-1}\ge1-z$并积分，

$$
\alpha(x)\ge\int_0^1(1-x^2t^2)\,dt
=1-\frac{x^2}{3}\ge\frac{26}{27}.
$$

附录A.7以微积分证明$\tan y\ge y+y^3/3$。由于$y+y^3/3$在非负实数上严格递增，把$\alpha(x)\ge26/27$这个下界代入，得到

$$
\tan\alpha(x)
\ge\frac{26}{27}+\frac13\left(\frac{26}{27}\right)^3.
$$

需要的严格余量逐项通分为

$$
\frac{26}{27}+\frac{26^3}{3\cdot27^3}
-\frac79\frac{25}{16}
=\frac{1191008-1148175}{944784}
=\frac{42833}{944784}>0.
$$

最后对$\log\mathfrak r$求导并代入以上每一个界：

$$
\begin{aligned}
\frac d{dx}\log\mathfrak r(x)
&=p'(x)+\tanh\beta(x)\,\beta'(x)
-\tan\alpha(x)\,v'(x)\\
&\le p'(x)
+\left(\frac79\frac{25}{16}
-\frac{26}{27}-\frac{26^3}{3\cdot27^3}\right)v'(x)\\
&=p'(x)-\frac{42833}{944784}v'(x)<0.
\end{aligned}
$$

$d_1<d_2$给$1/d_1>1/d_2$，所以
$\mathfrak r_{d_1}<\mathfrak r_{d_2}$。在$x\downarrow0$时，

$$
\alpha(x)\to1,\qquad \beta(x)\to1,\qquad p(x)\to0,
$$

$$
\lim_{d\to\infty,\ d\ {\rm 奇}}\mathfrak r_d
=e^0\frac{\cosh1}{\cos1}
=L.
$$

## 11. Taylor系数及余项的逐项恢复

对$|x|<1$，积分几何级数：

$$
\frac{\arctan x}{x}
=1-\frac{x^2}{3}+\frac{x^4}{5}+O(x^6),
\qquad
\frac{\operatorname{artanh}x}{x}
=1+\frac{x^2}{3}+\frac{x^4}{5}+O(x^6).
$$

例如第二个式子的余项满足

$$
\left|\sum_{k=3}^\infty\frac{x^{2k}}{2k+1}\right|
\le\frac{|x|^6}{7}\sum_{j=0}^\infty|x|^{2j}
=\frac{|x|^6}{7(1-x^2)}.
$$

第一个交错级数的绝对余项也被这同一个正级数控制。
第10节的$p$级数给出

$$
p(x)=-x^5/3+R_p(x),\qquad
|R_p(x)|\le\frac{|x|^9}{5(1-|x|^4)}.
$$

令$b=\tanh1$、$h=\tan1$、$\delta_\beta=\beta-1$、
$\delta_\alpha=\alpha-1$。所用的一、二阶导数为

$$
(\log\cosh y)'=\tanh y,\quad
(\log\cosh y)''=1-\tanh^2y,
$$

$$
(-\log\cos y)'=\tan y,\quad
(-\log\cos y)''=1+\tan^2y.
$$

再求一次导数，

$$
(\log\cosh y)'''=-2\tanh y\,\operatorname{sech}^2y,\qquad
(-\log\cos y)'''=2\tan y\,\sec^2y.
$$

前者的绝对值不超过2。后者只需在$\alpha$和1之间估计；由于$0\le\alpha\le1$，其绝对值不超过$2\tan1\,\sec^21$。Taylor积分余项满足

$$
|R_f|\le\frac{2}{6}|\delta_\beta|^3,\qquad
|R_g|\le\frac{2\tan1\,\sec^21}{6}|\delta_\alpha|^3.
$$

这里系数$1/6$来自$\frac12\int_0^{|\delta|}(|\delta|-t)^2dt=|\delta|^3/6$。展开为

$$
\log\cosh(1+\delta_\beta)-\log\cosh1
=b\delta_\beta+\frac{1-b^2}{2}\delta_\beta^2
+O(\delta_\beta^3),
$$

$$
-\log\cos(1+\delta_\alpha)+\log\cos1
=h\delta_\alpha+\frac{1+h^2}{2}\delta_\alpha^2
+O(\delta_\alpha^3).
$$

因为

$$
\delta_\beta=x^2/3+x^4/5+O(x^6),\quad
\delta_\alpha=-x^2/3+x^4/5+O(x^6),
$$

$$
\delta_\beta^2=x^4/9+O(x^6),\quad
\delta_\alpha^2=x^4/9+O(x^6),\quad
\delta_\beta^3=O(x^6),\quad\delta_\alpha^3=O(x^6),
$$

代回得到

$$
\log\cosh\beta-\log\cosh1
=\frac b3x^2+
\left(\frac b5+\frac{1-b^2}{18}\right)x^4+O(x^6),
$$

$$
-\log\cos\alpha+\log\cos1
=-\frac h3x^2+
\left(\frac h5+\frac{1+h^2}{18}\right)x^4+O(x^6).
$$

再加上$p(x)$，并记$L=\cosh1/\cos1$：

$$
\log\frac{\mathfrak r(x)}L
=a_2x^2+\ell_4x^4-\frac{x^5}{3}+O(x^6),
$$

$$
a_2=\frac{b-h}{3},\qquad
\ell_4=\frac{b+h}{5}+\frac{2+h^2-b^2}{18}.
$$

令上式右边为$z(x)$。由于$z=O(x^2)$，

$$
e^z=1+z+\frac{z^2}{2}+O(z^3),\qquad
\frac{z^2}{2}=\frac{a_2^2}{2}x^4+O(x^6),\quad z^3=O(x^6).
$$

所以

$$
\mathfrak r(x)
=L\left[1+a_2x^2+
\left(\ell_4+\frac{a_2^2}{2}\right)x^4
-\frac{x^5}{3}+O(x^6)\right].
$$

定义$a_4=\ell_4+a_2^2/2$，再代入$x=1/d$：

$$
\boxed{\mathfrak r_d
=L\left[1+\frac{a_2}{d^2}+\frac{a_4}{d^4}
-\frac1{3d^5}+O(d^{-6})\right].}
$$

这里一次、三次项的系数为0；五次项的系数为$-L/3$。用于核对的数值是

$$
La_2\approx-0.757603347512237,\qquad
La_4\approx2.035222101370122.
$$

这个展开的变量是基图阶数$d$。固定$d$取过块极限以后才令$d$增长，
所以它不是最终阶数$N=dm$的统一$O(N^{-2})$极值误差。

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

因此正则基图间的比较变成一个有限矩阵问题。需要区分代数定义与概率结论：后文的行列式比值可以对非正则符号矩阵定义，但本节“模型期望极限等于该比值”的结论只对正则基图引用。非正则基图的期望不能套用这条极限公式；第7—10节另证其归一化期望趋于0。

## 3. 乘积比较、积分与全部等号条件

本节引用[Fang–Huang的Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3)。这条外部定理不是本文重新证明的结论。其比较矩阵为

$$
(K_d)_{ij}=\begin{cases}
1,&i+j\le d,\\
0,&i+j=d+1,\\
(-1)^{i+j-d-2},&i+j\ge d+2.
\end{cases}
$$

本节$x\in\mathbb R^d$，$S_1,\ldots,S_p$均为$d$阶实反对称矩阵，非对角元为$\pm1$。向量$x^*$表示将$x$的各坐标绝对值按降序排列。对于这些同阶竞赛符号矩阵的任意乘积，所引定理给出

$$
(S_1\cdots S_p x)^*\prec_w K_d^p x^*.
$$

右端是非负降序向量。弱主序$u\prec_w v$的含义是

$$
\sum_{i=1}^r u_i\le\sum_{i=1}^r v_i
\quad(1\le r\le d).
$$

所引定理还给出：若最外层比较是向量等号，则对每个后缀乘积的比较都是向量等号。下面证明本文需要的平方和及其等号转换。

记$(a-t)_+=\max(a-t,0)$。对于降序非负向量及$t\ge0$，

$$
\sum_{i=1}^d(u_i-t)_+
=\max_{0\le r\le d}\left(\sum_{i=1}^r u_i-rt\right)
\le\max_{0\le r\le d}\left(\sum_{i=1}^r v_i-rt\right)
=\sum_{i=1}^d(v_i-t)_+.
$$

第一个等号中，取$r$等于严格大于$t$的坐标个数；加入更小坐标只会减少和，去掉更大坐标也只会减少和。对任意$a\ge0$，

$$
2\int_0^\infty(a-t)_+\,dt
=2\int_0^a(a-t)\,dt
=2[at-t^2/2]_0^a=a^2.
$$

逐坐标积分得到

$$
\|u\|_2^2
=2\int_0^\infty\sum_i(u_i-t)_+\,dt
\le2\int_0^\infty\sum_i(v_i-t)_+\,dt
=\|v\|_2^2.
$$

若平方和相等，令$g(t)=\sum_i(v_i-t)_+-\sum_i(u_i-t)_+$。它连续、非负且积分为0。如果$g(t_0)>0$，连续性给一个正长度区间，使其上$g(t)>g(t_0)/2$，积分便大于0。因此$g(t)=0$对每个$t\ge0$成立。分段线性函数的右导数给

$$
\#\{i:u_i>t\}=\#\{i:v_i>t\}=:N(t).
$$

对第$j$个坐标，

$$
u_j=\int_0^\infty
\mathbf1_{\{\#\{i:u_i>t\}\ge j\}}\,dt
=\int_0^\infty\mathbf1_{\{N(t)\ge j\}}\,dt=v_j.
$$

因而平方和取等强制$u=v$。取$x=e_j$，由于$e_j^*=e_1$，得到

$$
\|S^pe_j\|_2^2\le\|K_d^pe_1\|_2^2,
$$

并且取等时$(S^pe_j)^*=K_d^pe_1$。

## 4. 比较矩阵与传递矩阵的每个矩相同

令$T_d$的上三角元为1、下三角元为$-1$。令$R_0$为反序置换矩阵，$D_0=\operatorname{diag}(1,-1,\ldots)$。从$K_d$的定义逐项代入，

$$
(D_0K_dR_0)_{ij}
=(-1)^{i-1}(K_d)_{i,d+1-j}
=\begin{cases}
(-1)^{i-1},&i<j,\\
0,&i=j,\\
(-1)^j,&i>j.
\end{cases}
$$

按“奇指标升序、偶指标降序”同时排列行列。两个奇指标中，较早者$i<j$，上式为$(-1)^{i-1}=1$；两个偶指标中，较早者$i>j$，上式为$(-1)^j=1$。奇指标排在每个偶指标之前：若原指标$i<j$，上式为$(-1)^{i-1}=1$；若$i>j$，上式为$(-1)^j=1$。所以该顺序下所有上三角元都为1。令$\Lambda$实现这个排列，则

$$
T_d=\Lambda^TD_0K_dR_0\Lambda.
$$

置$U=D_0\Lambda$。由于$R_0R_0^T=I$、$\Lambda\Lambda^T=I$、$K_d^T=K_d$，矩阵乘积给

$$
\begin{aligned}
T_dT_d^T
&=\Lambda^TD_0K_dR_0\Lambda
\Lambda^TR_0^TK_dD_0\Lambda\\
&=\Lambda^TD_0K_d^2D_0\Lambda=U^TK_d^2U.
\end{aligned}
$$

第一项指标是1，故$Ue_1=e_1$。又$T_d^T=-T_d$，所以

$$
T_d^2=-U^TK_d^2U,\qquad
T_d^{2p}=(-1)^pU^TK_d^{2p}U
$$

（相乘时每两个邻接的$UU^T$都等于$I$）。于是

$$
(-1)^p(T_d^{2p})_{11}
=e_1^TK_d^{2p}e_1
=(K_d^pe_1)^T(K_d^pe_1)
=\|K_d^pe_1\|_2^2.
$$

附录A.2逐元素证明带负绕回移位$Z$满足$Z^TT_dZ=T_d$。插入$ZZ^T=I$得到$Z^TT_d^{2p}Z=T_d^{2p}$。取第$j<d$个对角元给$(T_d^{2p})_{j+1,j+1}=(T_d^{2p})_{jj}$；取第$d$个对角元，两个绕回负号相乘为1，给$(T_d^{2p})_{11}=(T_d^{2p})_{dd}$。因此

$$
\begin{aligned}
\|T_d^p\|_F^2
&=\operatorname{tr}((T_d^p)^TT_d^p)
=(-1)^p\operatorname{tr}T_d^{2p}\\
&=d(-1)^p(T_d^{2p})_{11}
=d\|K_d^pe_1\|_2^2.
\end{aligned}
$$

现在对上一节的$d$个列不等式求和：

$$
\|S^p\|_F^2
=\sum_{j=1}^d\|S^pe_j\|_2^2
\le d\|K_d^pe_1\|_2^2
=\|T_d^p\|_F^2\qquad(p\ge1).
$$

这里包括全部奇$p$，没有将一个仅关于$4k$次迹的结论直接替换成$4k+2$次迹结论。

## 5. 谱比值的上界与等号的完整推演

本节的$S$可为任意$d$阶竞赛符号矩阵，不假定正则。$\lambda_j$在本节表示未归一化矩阵$S$的频率，与第一部分矩阵$C=S/d$的频率相差因子$d$。非零特征值成对为$\pm i\lambda_j$，其中$\lambda_j>0$。第一部分的Frobenius估计只使用反对称性和非对角元为$\pm1$，并未使用正则性，因此每个$x_j=\lambda_j^2/d^2<1/2$。零特征值对下列行列式贡献为1；每个非零二维块的贡献分别为$1+x_j$和$1-x_j$，因此

$$
\det(I+S/d)=\prod_j(1+x_j),\qquad
\det(I+iS/d)=\prod_j(1-x_j)>0.
$$

在$0\le x<1$上，将几何级数积分，

$$
\begin{aligned}
\log\frac{1+x}{1-x}
&=\int_0^x\left(\frac1{1+t}+\frac1{1-t}\right)\,dt\\
&=2\int_0^x\frac{dt}{1-t^2}
=2\sum_{r=0}^\infty\int_0^x t^{2r}\,dt
=2\sum_{r=0}^\infty\frac{x^{2r+1}}{2r+1}.
\end{aligned}
$$

积分交换可由$[0,x]$上几何级数的一致收敛保证。反对称标准形还给$\|S^p\|_F^2=2\sum_j\lambda_j^{2p}$。逐项代入，

$$
\begin{aligned}
\log\rho_d(S)
&=2\sum_j\sum_{r=0}^\infty
\frac{\lambda_j^{4r+2}}{(2r+1)d^{4r+2}}\\
&=\sum_{r=0}^\infty
\frac{\|S^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}
\le\sum_{r=0}^\infty
\frac{\|T_d^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}
=\log\rho_d(T_d).
\end{aligned}
$$

定义$r_d=\rho_d(T_d)$。每个亏损非负；若总和为0，则$r=1$这一项也为0，即$\|S^3\|_F^2=\|T_d^3\|_F^2$。该亏损是$d$个非负列亏损的和，所以每一列取等。本部分第3节的平方和等号结论及Fang–Huang的后缀等号依次给

$$
(S^3e_j)^*=K_d^3e_1,\qquad
(S^2e_j)^*=K_d^2e_1.
$$

对后一式求平方和并按$j$求和，

$$
\operatorname{tr}S^4=\|S^2\|_F^2
=d\|K_d^2e_1\|_2^2
=\|T_d^2\|_F^2=\operatorname{tr}T_d^4.
$$

附录A.3独立证明这一等号强制$S=Q^TT_dQ$，其中$Q$为带符号置换矩阵。反向也要检查：$Q^TQ=I$，故

$$
I+tS=Q^T(I+tT_d)Q,\qquad
\det(I+tS)=(\det Q)^2\det(I+tT_d)=\det(I+tT_d).
$$

分别取$t=1/d$和$t=i/d$，得到$\rho_d(S)=r_d$。因此

$$
\rho_d(S)\le r_d,
\quad\text{等号当且仅当 }S=Q^TT_dQ.
$$

这里的带符号置换矩阵$Q$每行、每列恰有一个$\pm1$，满足$Q^TQ=I$；它是本节局部记号，与第一部分的对称矩阵$Q$不同。写$Q=D_eP$，其中$P$为普通置换矩阵，$D_e=\operatorname{diag}(e_1,\ldots,e_d)$，本段的$e_i=\pm1$是标量符号。于是

$$
S=P^TD_eT_dD_eP,\qquad PSP^T=D_eT_dD_e.
$$

这里只把$P$吸收到普通重编号中，以下仍将重编号后的矩阵记为$S$；对角符号切换本身不是普通同构。若$S$正则，在这个重编号后仍有$S\mathbf1=0$。由$D_e^2=I$，

$$
D_eT_de=0,\qquad T_de=0.
$$

第$i$行与第$i+1$行的差只有第$i,i+1$列各为1，因此

$$
0=(T_de)_i-(T_de)_{i+1}=e_i+e_{i+1}.
$$

递推给$e_i=(-1)^{i-1}e_1$。整体符号$e_1$在$D_eT_dD_e$中出现两次而抵消；附录A.2给出该交替切换与$\mathrm{Car}_d$的逐边普通同构。因此正则基图的等号恰为圆环普通同构类。

## 6. 六次矩给出的明确严格间隙

若正则$S$不普通同构于圆环，上一节的等号推演给

$$
\Delta_3:=\|T_d^3\|_F^2-\|S^3\|_F^2>0.
$$

在模2意义下$S\equiv J+I$，并且$J^2=dJ$、$J^3=d^2J$，所以

$$
S^3\equiv(J+I)^3
=I+3J+3dJ+d^2J
\equiv I+(1+d+d^2)J\equiv I+J\pmod2.
$$

最后一步使用$d(d+1)$为偶数。又$(S^3)^T=-S^3$，故其对角为0、非对角为奇数。若$z=2k+1$，

$$
z^2=4k(k+1)+1\equiv1\pmod8.
$$

将反对称位置成对求和，

$$
\|S^3\|_F^2=2\sum_{i<j}(S^3_{ij})^2
\equiv2\binom d2=d(d-1)\pmod{16}.
$$

此式也适用于$T_d$。因此$\Delta_3$是正的16的整数倍，$\Delta_3\ge16$。在对数级数中只保留$r=1$项，

$$
\log\frac{r_d}{\rho_d(S)}
\ge\frac{\Delta_3}{3d^6}\ge\frac{16}{3d^6}.
$$

两边取指数，再移项，

$$
\rho_d(S)\le r_de^{-16/(3d^6)},\qquad
r_d-\rho_d(S)\ge r_d(1-e^{-16/(3d^6)})>0.
$$

这是固定基图的极限常数间隙，不是有限块阶数的有效阈值。

## 7. 非正则比分与指数损失

令$d_i$为基图出度，$b_i=d_i+1/2$，并定义

$$
a_i=\frac{2b_i}{d},\qquad
\kappa=\left(\prod_{i=1}^d a_i\right)^{1/d},\qquad
s_i=2d_i-(d-1).
$$

每条边恰贡献一个出度，因此

$$
\sum_i d_i=\binom d2,\qquad
\sum_i a_i=\frac{2\binom d2+d}{d}=d,\qquad
a_i=1+\frac{s_i}{d}\in(0,2),\qquad \sum_i s_i=0.
$$

函数$f(a)=a-1-\log a$满足$f'(a)=(a-1)/a$，所以在$a=1$达到唯一最小值$f(1)=0$。于是

$$
\log\kappa=\frac1d\sum_i\log a_i
\le\frac1d\sum_i(a_i-1)=0.
$$

取等要求全部$a_i=1$，即全部$d_i=(d-1)/2$。非正则时$\kappa<1$。为了计算损失，使用带积分余项的二阶展开：

$$
\log a=(a-1)-(a-1)^2\int_0^1
\frac{1-t}{[1+t(a-1)]^2}\,dt.
$$

由于$0<1+t(a-1)<2$，

$$
\int_0^1\frac{1-t}{[1+t(a-1)]^2}\,dt
\ge\frac14\int_0^1(1-t)\,dt=\frac18.
$$

代入$a_i$并求和，

$$
\begin{aligned}
\log\kappa
&\le\frac1d\sum_i\left(\frac{s_i}{d}-\frac{s_i^2}{8d^2}\right)
=-\frac{\|s\|^2}{8d^3}.
\end{aligned}
$$

奇$d$时每个$s_i$为偶数。非正则意味着至少一个$s_i\ne0$；零和条件还要求存在相反符号的非零项，各自绝对值至少2。因此$\|s\|^2\ge2^2+2^2=8$，并有

$$
\kappa^N\le\exp[-N\|s\|^2/(8d^3)]\le e^{-N/d^3}.
$$

在$\mathcal T$模型中，令$W$为邻接矩阵的逐元期望。对任意非负$N$阶矩阵，$\operatorname{Sym}(N)$为全部顶点置换，$\mathcal C_N$为其中恰有一个长度$N$循环的置换，定义加权永久式和加权Hamilton圈数如下：

$$
\operatorname{per}W=\sum_{\sigma\in\operatorname{Sym}(N)}
\prod_{v=1}^N W_{v,\sigma(v)},\qquad
C(W)=\sum_{\sigma\in\mathcal C_N}\prod_{v=1}^N W_{v,\sigma(v)}.
$$

对有向圈使用单循环置换表示，已经将循环起点识别，因此不再额外除以顶点数。对一个固定有向Hamilton圈，其$N$条边使用不同无序顶点对，内部随机边相互独立；故该圈出现概率等于对应$W$元素的乘积。对所有按循环起点识别的圈求和，

$$
\mathbb EC_{\mathcal T}=C(W)\le\operatorname{per}W.
$$

永久式包含所有置换；一个Hamilton圈对应其中一个单圈置换，其权重非负，因此末尾不等式成立。这里没有将一般置换的随机边乘积当作独立：置换可能含二圈，而竞赛图不可能同时包含相反的两条边。

## 8. 加权行的补齐、整数化及Brégman界

本节应用于$m\ge2$；$\mathcal R$还要求奇$m$，故实际从$m\ge3$开始。这足以处理块阶数趋于无穷的结论。第$i$类的每一行在$W$中的和为

$$
r_i=md_i+\frac{m-1}{2}=mb_i-\frac12,\qquad
R_i=\lceil r_i\rceil.
$$

先讨论任意$L$元行$w$，其中$0\le w_j\le1$，当前行和记为$r=\sum_{j=1}^Lw_j$，目标整数行和$R$满足$r\le R\le L$。需要补入$s_0=R-r$，可用容量为$\sum_j(1-w_j)=L-r\ge s_0$。从$j=1$开始依次取

$$
\delta_j=\min(1-w_j,s_{j-1}),\qquad
s_j=s_{j-1}-\delta_j,\qquad w'_j=w_j+\delta_j.
$$

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

至少一个坐标变成0或1，非整数坐标数减少。至多$L-1$次后至多剩一个非整数坐标；若其余坐标均为整数且总和$R$为整数，最后一个坐标也是整数。对各行执行此过程，得到0、1矩阵$V$，每个第$i$类行有$R_i$个1，而且$\operatorname{per}W\le\operatorname{per}V$。

这里的$V$是用于上界的辅助矩阵；所需条件是各元为0或1及指定行和，允许其对角为1。下面所引定理适用于这种一般0、1矩阵。

现在引用[Brégman不等式（Alon论文Lemma 2.1）](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)：0、1矩阵的行和为$q_1,\ldots,q_L>0$时，

$$
\operatorname{per}V\le\prod_{\ell=1}^L(q_\ell!)^{1/q_\ell}.
$$

由于$r_i\ge(m-1)/2>0$，整数上界$R_i$至少为1，满足所引用Brégman界的正行和假设。本题每类恰有$m$行，因此

$$
\operatorname{per}W\le\prod_{i=1}^d(R_i!)^{m/R_i}.
$$

使用的是原0、1定理；加权情形的适用性已由上面的具体行操作证明。

## 9. 带明确常数的归一化计算

如果待估计的永久式等于0，被它控制的非负圈计数也等于0，所需上界已经成立，不对0取对数。以下以及第10节的全部永久式对数计算只在相应永久式为正时进行；正的上界最后也覆盖零值情形。以下$m\ge2$，$N=dm$。写$R_i=mb_i+\varepsilon_i$，则$|\varepsilon_i|\le1/2$，并有

$$
R_i\ge m/2-1/2\ge m/4,\qquad R_i\le N.
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

令$y_i=\varepsilon_i/(mb_i)$。由于$b_i\ge1/2$，$|y_i|\le1/m\le1/2$，且

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

若内部是正则块，每个样本的实际旧行和就是$mb_i-1/2$，为正整数。直接对该样本邻接矩阵应用Brégman及上面逐项估计，得到

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

故两个归一化圈期望都趋于0。

## 10. 增点后的路径界：逐项保留所有归一化项

固定旧竞赛图$G$，加入新顶点$v$，与旧顶点的边独立公平定向。每条路径$x_1\to\cdots\to x_N$对应唯一候选圈$v\to x_1\to\cdots\to x_N\to v$，两条新增边的联合概率为$(1/2)^2=1/4$。删除$v$是逆操作。因此

$$
\mathbb E[C_{\rm aug}\mid G]=H(G)/4,\qquad
4\nu_{N+1}=\frac{4N!}{2^{N+1}}=\frac{N!}{2^{N-1}}=\mu_N,
$$

$$
\frac{\mathbb EH}{\mu_N}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

对于$\mathcal T$的增广期望矩阵，旧行和为$mb_i$；对于$\mathcal R$的每个实际增广样本，旧行和不超过$mb_i+1/2$。统一选择

$$
R_i'=\lceil mb_i+1/2\rceil=mb_i+\varepsilon_i',
\qquad \frac12\le\varepsilon_i'<\frac32.
$$

新行补到$R_0=N$。因为$b_i\le d-1/2$且$m\ge2$，$mb_i+1/2\le N-1/2$，所以$R_i'\le N$；同时$R_i'\ge m/2$。这些补齐目标都不超过增广矩阵的列数$N+1$，第8节的行操作适用。Brégman给出

$$
\log\operatorname{per}V_{\rm aug}
\le m\sum_i\frac{\log(R_i'!)}{R_i'}
+\frac{\log(N!)}N.
$$

沿用$R_i'\ge m/4$、$R_i'\le N+1$计算旧行余项，并单列新行，

$$
\begin{aligned}
\log\operatorname{per}V_{\rm aug}
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
m\sum_i\log(1+\varepsilon_i'/(mb_i))\\
&\le N\log\kappa+\sum_i\frac{\varepsilon_i'}{b_i}
\le N\log\kappa+3d.
\end{aligned}
$$

于是，使用$4d/(3m)\le2d/3$，

$$
\begin{aligned}
\log\frac{\operatorname{per}V_{\rm aug}}{(N+1)!/2^{N+1}}
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

第二个界逐样本约束增广圈数，然后取期望；没有假定正则块内部的边独立。固定非正则基图时，右端对数除以$N$趋于$\log\kappa<0$，所以两者趋于0。若采用三角分解正则内部模型，在定义成立的阶数上每个旧顶点内部出度仍是$(m-1)/2$，旧行和仍是$mb_i-1/2$，增点后上界仍是$mb_i+1/2$；上述两个行和界逐样本成立，因此也得到所列$\mathcal R$上界。

## 11. 从极限常数推出充分大块阶数的精确期望极值

固定$d$后，每一对顶点的方向有两种选择，所以有标号基图的总数为$2^{\binom d2}$，普通同构类数不超过这个有限数。正则基图中，圆环的极限常数为$r_d$（或$e^{1/d}r_d$），其余正则基图有第6节的正间隙。非正则基图的归一化期望趋于0。

对每个非参考基图分别取足够大的$m$，使其实际归一化期望严格小于圆环；再对有限个阈值取最大值，即得第1节的$M_d$及唯一普通同构类。这一步合法地利用$d$固定，不声称该阈值对增长$d$统一。

还需说明为什么圆环的每个普通同构副本都达到相同的最大值。若基图的普通同构为$\pi$，吹胀顶点写成$(i,a)$，则

$$
(i,a)\longmapsto(\pi(i),a)
$$

给出两个吹胀模型样本之间的双射。块间方向由基图同构保持；内部块只是重新排列，独立且同分布的选取概率保持不变。每条路径、每个圈都经这个双射唯一对应，故两种计数的期望相等。结合非同构基图的严格不等式，等号类恰为整个圆环普通同构类。

## 12. 完成了什么，尚未完成什么

第一部分给出所读Wormald版本猜想6的有限代数证明及猜想2的极限、单调性；本稿在明确引用其原计数定理和Fang–Huang比较后，得到猜想1及路径类比的固定基图期望结论。

这些结果将本文的谱比值与原随机模型常数准确等同，摆脱逐个基图计算Hessian。没有由此证明Wormald猜想3的全体竞赛图圈极值，也没有给出全体竞赛图路径数新的统一误差、有效$M_d$，或对增长基图与块阶数同时极限的结论。一般论证仍待独立数学审阅，历史文献归属尚未穷尽，不主张优先权。

# 第三部分：发表前复核补充计算

## A.1 传递符号矩阵的行列式多项式

令$T_n$上三角为1、下三角为$-1$，记$F_n(t)=\det(I+tT_n)$。下面直接用行变换证明第一部分第9节的闭式，不把偶阶主子式的值作为未说明的输入。

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

所以

$$
F_n(t)=\frac{(1+t)^n+(1-t)^n}{2}.
$$

两端都是多项式，已在除两个点以外的所有$t$相等，故在$t=-1,0$也相等。代入$t=1/d$与$t=i/d$，得到圆环模型的行列式比值。

为补明第一部分第9节关于每个主子式的陈述，取非空$U$，记$k=|U|$。按原顶点升序排列后，$T_d[U]$就是$T_k$。行列式多项式$F_k(t)=\det(I+tT_k)$的最高次系数为$\det T_k$；记$[t^k]$为提取这一系数的符号，因此

$$
\det T_d[U]=\det T_k=[t^k]F_k(t)
=\frac{1+(-1)^k}{2}
=\begin{cases}1,&k\ \text{even},\\0,&k\ \text{odd}.\end{cases}
$$

空集的主子式由约定等于1。这就从已证闭式推出了每一个主子式的取值。

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

## A.3 四阶行列式及四次矩等号的完整展开

令

$$
M=\begin{pmatrix}
0&a&b&c\\
-a&0&d&e\\
-b&-d&0&f\\
-c&-e&-f&0
\end{pmatrix}.
$$

记$M_{1j}$为删去第1行、第$j$列后的三阶行列式（不含代数余子式符号）。沿第一行展开，分别计算：

$$
\begin{aligned}
M_{12}
&=\det\begin{pmatrix}-a&d&e\\-b&0&f\\-c&-f&0\end{pmatrix}\\
&=(-a)(0-f(-f))-d((-b)0-f(-c))+e((-b)(-f)-0(-c))\\
&=-af^2-cdf+bef,\\
M_{13}
&=\det\begin{pmatrix}-a&0&e\\-b&-d&f\\-c&-e&0\end{pmatrix}\\
&=(-a)((-d)0-f(-e))-0+e((-b)(-e)-(-d)(-c))\\
&=-aef+be^2-cde,\\
M_{14}
&=\det\begin{pmatrix}-a&0&d\\-b&-d&0\\-c&-e&-f\end{pmatrix}\\
&=(-a)((-d)(-f)-0(-e))-0+d((-b)(-e)-(-d)(-c))\\
&=-adf+bde-cd^2.
\end{aligned}
$$

将每个三阶行列式按其第一行再展开，三项分别来自第一行的三个元素；上式中第一行的0贡献为0。再乘四阶展开的系数：

$$
\begin{aligned}
\det M
&=-aM_{12}+bM_{13}-cM_{14}\\
&=(a^2f^2+acdf-abef)
+(-abef+b^2e^2-bcde)
+(acdf-bcde+c^2d^2)\\
&=a^2f^2+b^2e^2+c^2d^2-2abef+2acdf-2bcde\\
&=(af-be+cd)^2.
\end{aligned}
$$

六个变量均为$\pm1$时，$af-be+cd$是三个$\pm1$之和，其值为$\pm1$或$\pm3$，故行列式为1或9。设$D_4(S)$为四顶点主子式等于9的个数。由行列式的列多线性展开，在每列选择单位列或$tS$的列，得到

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
=2\binom d2^2-4\binom d4-32D_4(S).
$$

传递矩阵任取四个升序顶点都有$a=b=c=d=e=f=1$，其行列式为$(1-1+1)^2=1$，所以$D_4(T_d)=0$。相减给

$$
\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S).
$$

若四次矩取等，则$D_4(S)=0$。取对角符号$e_1=1,e_j=s_{1j}$（$j>1$），切换后$s'_{1j}=e_1s_{1j}e_j=s_{1j}^2=1$。任意主子式在切换下乘以$(\det D_e[U])^2=1$，故$D_4$不变。任取$i<j<k$且都不为1，

$$
\det S'[\{1,i,j,k\}]
=(s'_{jk}-s'_{ik}+s'_{ij})^2.
$$

若这三点形成有向三圈，则$s'_{ij}=s'_{jk}=-s'_{ik}$，括号为$3s'_{ij}$，平方为9，矛盾。因此剩余顶点无有向三圈。如果$i\to j$、$j\to k$而$i\not\to k$，则$k\to i$，会形成三圈；所以方向关系是严格全序，可按该全序排列。第一顶点指向所有剩余点，整个切换图于是为传递图。反过来带符号置换相似保持迹，故四次矩取等。$d=3$时切换后剩下两点，按其唯一边方向排列即可。

## A.4 逐行整数化的可复现步骤

第二部分第8节已列出逐坐标补齐量$\delta_j$、剩余量$s_j$、两坐标移动量$\eta$及永久式改变量。这里记录终止性所需的两个整数。

$$
q(w)=\#\{j:0<w_j<1\},\qquad
q(W)=\sum_{\ell=1}^L q(W_{\ell,\cdot}).
$$

每次两坐标移动不改变整数行和，使至少一个非整数坐标变成整数，且不改变其他整数坐标，所以$q(w)$至少减少1。最初$q(w)\le L$，不可能无限下降。若停止时$q(w)=1$，唯一非整数坐标为

$$
w_a=R-\sum_{j\ne a}w_j\in\mathbb Z,
$$

与其非整数性矛盾。因此停止时$q(w)=0$。逐行处理不会修改其他行；每行最多$L-1$次两坐标移动后已经整数化，总移动次数至多$L(L-1)$。每次永久式改变量均为第8节算出的$\eta(c_a-c_b)\ge0$。

## A.5 增点界中主项重组的逐项核对

第二部分第10节已经给出带明确常数的路径上界。本节把其中唯一一次对数重组分别拆开，避免隐藏一个额外的$N$因子。由于$md=N$，

$$
m\sum_i\log R_i'
=m\sum_i\log(2R_i'/N)+N\log(N/2).
$$

于是

$$
\begin{aligned}
&N\log(N/2)+\log N-(N+1)\log((N+1)/2)\\
&=N\log N-N\log2+\log N
-(N+1)\log(N+1)+(N+1)\log2\\
&=N[\log N-\log(N+1)]
+[\log N+\log2-\log(N+1)]\\
&=N\log(N/(N+1))+\log(2N/(N+1)).
\end{aligned}
$$

在此后的指数界里，分母先是$(N+1)!/2^{N+1}$。改成圈期望的分母时，

$$
\frac{(N+1)!/2^{N+1}}{\nu_{N+1}}
=\frac{(N+1)!}{N!}=N+1.
$$

因此多项式次数从$2d+1$变成$2d+2$。增点恒等式又给

$$
\frac{\mathbb EH}{\mu_N}
=\frac{4\mathbb EC_{\rm aug}}{4\nu_{N+1}}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

这两个因子一个来自阶数变更，一个来自增点概率，均已显式保留。

## A.6 有限多个基图如何给同一个阈值

固定一个模型和一种计数，其圆环极限为$\ell_*>0$，其他普通同构类的极限为$\ell_T<\ell_*$。由于$d\ge3$，传递基图非正则而圆环正则，因此非圆环同构类集合非空。有限性及同构不变性见第二部分第11节；各非圆环类的极限严格较小，因此有限个正差值有正的最小值：

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

