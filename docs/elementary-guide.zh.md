# 从大一基础理解这次的新连接：Hessian、有理平方与随机块模型

刘星辰。2026年10月19日，公开研究稿的配套基础讲解。

本篇解释主文的第一、第二部分。我们把Wormald原稿中的一个多元Hessian，算成了矩阵分析中出现的谱比值。它给出该引用版本猜想6的一般证明稿，并进一步得到模型常数的极限、单调性及固定基图的期望极值。一般推导仍待独立数学审阅，不把它说成全体竞赛图的Hamilton极值已经解决。

## 1. 必须先分清两个大小

先取一个$d$顶点的基图。把每个基图顶点替换成$m$个顶点，得到

$$
N=dm.
$$

块间所有边依照基图；块内部随机选择竞赛图。这里有两个不同参数：

- $d$是基图大小；
- $m$是每块大小，$N$是最后图的大小。

原模型先固定$d$，再令$m\to\infty$。得到每个$d$对应的一个极限常数后，我们才研究$d\to\infty$。不能把这两个步骤直接交换。

## 2. 所研究的常数不是基图本身的路径数

随机竞赛图在$N$阶的平均Hamilton圈数与路径数为

$$
\nu_N=\frac{(N-1)!}{2^N},\qquad
\mu_N=\frac{N!}{2^{N-1}}.
$$

我们考虑随机块模型的

$$
\frac{\mathbb E C}{\nu_N},\qquad \frac{\mathbb E H}{\mu_N}.
$$

例如三角形基图$d=3$本身有1个Hamilton圈，$\nu_3=1/4$，所以它的有限圈数比为4。但将它吹胀成大随机块后，圈期望比的极限为2。这两个量不同。

## 3. 正则基图的矩阵

正则表示每个顶点的出度、入度都为$(d-1)/2$。令$A$为邻接矩阵，定义

$$
S=2A+I-J,\qquad C=S/d.
$$

于是

$$
S^T=-S,\qquad S1=0.
$$

把$2A+I$除以$d$，得到

$$
P=\frac{2A+I}{d}=\frac Jd+C.
$$

记$\mathbf1=(1,\ldots,1)^T$，令$u=\mathbf1/\sqrt d$。则$Pu=u$；若$v$与$1$垂直，$Pv=Cv$。

所以常数方向与零和方向可以分别处理。这和我们此前平衡矩阵时区分常数方向的做法一致。

## 4. Hessian是什么

对多元函数$f(x_1,\ldots,x_r)$，Hessian是二阶偏导数组成的矩阵：

$$
\nabla^2f=
\left(\frac{\partial^2f}{\partial x_j\partial x_k}\right)_{j,k=1}^r.
$$

普通Taylor公式在多元情形写为

$$
f(x)=f(0)+\nabla f(0)^Tx+\frac12x^T\nabla^2f(0)x+\cdots.
$$

因此Hessian控制函数在驻点附近的二次变化。如果Hessian正定，每个非零方向的二次变化都为正，其行列式也严格为正。

Wormald的模型常数写成$\sqrt{d/\mathcal H}$，其中$\mathcal H$是一个特定Hessian的行列式。关键任务就是把这个$\mathcal H$算清楚。

## 5. 为什么会出现一个由行列式决定的函数

原文定义

$$
B(y)=I-(A+\tfrac12I)\operatorname{diag}(y_1,\ldots,y_d),
\qquad K(y)=\det B(y).
$$

在每个$y_j=2/d$时，

$$
B=I-\frac{2A+I}{d}=I-P.
$$

因为$P1=1$，$I-P$有常数零方向，所以$K=0$。我们在这个点附近，由$K=0$把最后一个变量写成

$$
y_d=h(y_1,\ldots,y_{d-1}).
$$

这里并不需要抽象地假定这个函数存在。行列式对每一列线性，所以

$$
K(y)=K_0(y')+y_dK_1(y').
$$

只要$K_1$不为零，

$$
h(y')=-K_0(y')/K_1(y').
$$

记$q=\det(I-C)>0$。第8节将完整算出关键点的$K_1=-q/2\ne0$，因此$h$是一个明确的有理函数。

## 6. 先改成对数变量，计算更容易

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

二次导数为

$$
\mathscr B_{jk}(0)=-\delta_{jk}Pe_je_j^T.
$$

这里$\delta_{jk}$在$j=k$时为1，否则为0。

## 7. 把分块消元的矩阵乘法写出来

全一向量记为$\mathbf1=(1,\ldots,1)^T$。令

$$
u=\mathbf1/\sqrt d,\qquad \Pi=I-uu^T.
$$

直接乘法给

$$
u^Tu=1,\qquad \Pi^2=\Pi,\qquad \Pi u=0.
$$

$\Pi v=v-u(u^Tv)$去掉了$v$的常数方向分量。选取$u^\perp$的一组正交单位基作为$V$的列，则

$$
V^TV=I_{d-1},\quad V^Tu=0,\quad VV^T=\Pi.
$$

在正交基矩阵$(u,V)$中，原矩阵写成

$$
\begin{pmatrix}a&b\\c&D\end{pmatrix},
\qquad
a=u^T\mathscr Bu,\quad b=u^T\mathscr BV,\quad
c=V^T\mathscr Bu,\quad D=V^T\mathscr BV.
$$

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

令$U=(I-C)^{-1}$。$C$保持零和空间，故

$$
VR(0)V^TC=UC.
$$

于是

$$
b_j(0)R(0)c_k(0)
=\frac1d e_j^TVR(0)V^TCe_k
=\frac1d(UC)_{jk}.
$$

再交换$j,k$，得到

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

它为正：第B.2节的每个二维块对$\det(I-C)$贡献$1+\lambda^2>0$，零块贡献1。现在对$K(ze^{t_1},\ldots,ze^{t_d})=\det D(t)\psi(t)$求一次导数。在原点$\psi(0)=0$，故

$$
\partial_{t_j}K
=\partial_{t_j}(\det D)\,\psi+\det D\,\psi_j
=0+q(-1/d)=-q/d.
$$

另一方面，$y_j=ze^{t_j}$给

$$
\partial_{t_j}K=zK_{y_j},
\qquad K_{y_j}=-\frac{q}{dz}=-\frac q2\ne0.
$$

因此第5节的有理函数$h=-K_0/K_1$确实在关键点附近有定义。



## 9. 把最后一个变量消去后，导数怎样变化

设$t_d=g(t_1,\ldots,t_{d-1})$。对

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

原文使用角变量$t_j=i\theta_j$。两次求导多出$i^2=-1$，所以原Hessian变成正号：

$$
\mathbf H=E^TQE,\qquad E=(e_1-e_d,\ldots,e_{d-1}-e_d).
$$

## 10. 为什么Hessian一定正定

$C$反对称，它的非零特征值成对为$\pm i\lambda$。本题有$|\lambda|<1$。因此$Q$对应的实特征值为

$$
\frac{1-\lambda^2}{1+\lambda^2}>0.
$$

所以$Q$正定。对任意非零$v$，

$$
v^T\mathbf Hv=(Ev)^TQ(Ev)>0,
$$

因为$E$的列独立，所以$Ev\ne0$。这就证明原文担心的Hessian退化不会发生。

## 11. 因子d从哪里来

$E$的列不是正交单位向量。直接计算：

$$
E^TE=I_{d-1}+J_{d-1}.
$$

这个矩阵在全一方向的特征值为$d$，其余特征值为1，所以

$$
\det(E^TE)=d.
$$

而$Q$在常数方向的特征值是1。因此

$$
\mathcal H=\det(E^TQE)=d\det Q
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}.
$$

若忘了$E$不是正交基，就会漏掉这个$d$。

## 12. 为什么是有理数的平方

矩阵乘法给

$$
(I+iC)(I-iC)=I+C^2,\qquad
(I+C)(I-C)=I-C^2.
$$

反对称性使两支行列式分别相等。因此

$$
\frac d{\mathcal H}
=\left[\frac{\det(I+C)}{\det(I+iC)}\right]^2.
$$

这正是以前研究的谱比值$\rho_d(S)$的平方。$C$的元素有理，两个行列式均为实有理；分母、分子均为正，故平方根就是正有理数$\rho_d(S)$。

这给出所引用版本猜想6的完整一般计算，而不只是在表中的几个例子上发现有理数。

## 13. 三角形例子可以完全手算

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


## 14. 圆环模型常数的极限与误差

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

令$b=\tanh1,h=\tan1$，进一步有

$$
\mathfrak r_d
=L\left[1+\frac{b-h}{3d^2}+\frac{a_4}{d^4}
-\frac1{3d^5}+O(d^{-6})\right],
$$

$$
a_4=\frac{b+h}{5}+\frac{2+h^2-b^2}{18}+\frac{(b-h)^2}{18}.
$$

所以$d^{-1}$和$d^{-3}$系数精确为零，第一项非零奇次是$d^{-5}$。技术稿通过明确函数求导证明单调性，再用Taylor公式算系数，没有用数值拟合代替证明。

这里的误差是基图参数$d$的误差，不是最终图大小$N$的误差。

## 15. 为什么非正则基图会有指数损失

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

奇阶非正则基图至少有一个非零正比分与一个非零负比分，各自绝对值至少2，所以$\sum_i s_i^2\ge8$。于是指数因子至多$e^{-N/d^3}$。这将正则性要求与我们此前使用的比分能量罚项直接联系起来。

这一步很重要：正则基图的Hessian公式不能直接套在非正则基图上，必须另作估计。

## 16. 为什么圆环成为固定基图模型的唯一最优者

对正则基图，极限常数就是$\rho_d(S)$，正则内部块时另乘共同正因子$e^{1/d}$。

已有并在主文第二部分明确展开的矩比较给

$$
\rho_d(S)\le\rho_d(\mathrm{Car}_d),
$$

且正则图中只有普通同构于圆环的图取等号。非参考正则图还有严格的常数间隙；非正则图的归一化期望趋于0。

固定$d$时只有有限多个基图，所以可以对它们各自“块足够大”的阈值取最大值。这样就得到：对充分大的$m$，随机块模型的圈期望和路径期望都由圆环基图唯一最大。

它不表示每一个随机样本都最大，也不表示任意$N$阶竞赛图的最大者都已确定。

## 17. 验证与后续范围

73组正则基图的Hessian通过独立主子式展开直接求导，11,724个元素与345个Hessian行列式精确一致。另穷举三、五、七阶全部2,666个正则图，核对谱极值和等号；七阶有720个圆环标号图取等号，其余1,920个严格小。

576个随机块实现的精确平均，与加权路径、圈计算一致。它们检查有限恒等式；一般定理依靠主文第一部分、主文第二部分的逐式证明和标明来源的外部定理。

这次得到的是针对所引用版本猜想1、2、6的公开证明稿及模型常数闭式，仍需独立数学审阅和进一步核对历史文献。没有将这些模型结论冒充为全体竞赛图Hamilton极值的新证明。

# 进一步展开：期望、谱隙和Taylor系数

## B.1 期望为什么可以逐条圈相加

只有有限多个等可能随机实现时，$\mathbb EX$就是这些实现中$X$值的算术平均。对每条候选有向Hamilton圈$\gamma$，定义指示量

$$
I_\gamma=\begin{cases}1,&\gamma\text{出现},\\0,&\gamma\text{不出现}.\end{cases}
$$

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

这一步用于$N\ge3$的圈。块模型中，块间指定边的概率是0或1，块内独立边是$1/2$。Hamilton圈不会同时使用同一个无序点对的两个方向，因此单条圈的概率确实是各条所需边概率的乘积。

永久式则不同。它定义为

$$
\operatorname{per}W
=\sum_{\pi\in\mathfrak S_N}\prod_{i=1}^N W_{i,\pi(i)}.
$$

Hamilton圈只占其中一部分置换，所有项非负，所以$C(W)\le\operatorname{per}W$。永久式还包含二圈；随机竞赛图不允许同一对顶点的两个方向同时存在，所以不能把$\mathbb E\operatorname{per}A$错误地等同于$\operatorname{per}(\mathbb EA)$。

## B.2 不靠猜测得到Hessian中的谱隙

实反对称矩阵可在正交基中分成若干个二维块

$$
J_\lambda=\begin{pmatrix}0&\lambda\\-\lambda&0\end{pmatrix}
$$

以及零块。这是实反对称矩阵的标准分块形式。该块满足

$$
J_\lambda^2=-\lambda^2I_2.
$$

所以在该块上，

$$
(I+J_\lambda^2)(I-J_\lambda^2)^{-1}
=\frac{1-\lambda^2}{1+\lambda^2}I_2.
$$

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

所以所有上述比值为正。零块上$Q=I$，也正。这是第10节所需$|\lambda|<1$的完整来源。

## B.3 基变换中的因子d再算一遍

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

## B.4 模型常数的Taylor系数逐项相乘

令$x=1/d$，并定义

$$
\alpha(x)=\frac{\arctan x}{x},\qquad
\beta(x)=\frac{\operatorname{artanh}x}{x},\qquad
\operatorname{artanh}x=\frac12\log\frac{1+x}{1-x}.
$$

对$|x|<1$，几何级数积分给

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
\log(1-x^2)=-x^2-\frac{x^4}{2}-\frac{x^6}{3}+O(x^8),
$$

$$
\log(1+x^2)=x^2-\frac{x^4}{2}+\frac{x^6}{3}+O(x^8).
$$

相减时偶数次幂$x^4,x^8,\ldots$相消，因而

$$
p(x)=-\frac{x^5}{3}+O(x^9).
$$

令$b=\tanh1$、$h=\tan1$、$\delta_\beta=\beta-1$、
$\delta_\alpha=\alpha-1$。普通二阶Taylor公式给

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


# 补充演算：把原来略写的步骤展开

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


## 参考文献

1. N. C. Wormald. *Tournaments with many Hamilton cycles*. arXiv:2610.16245v1. [固定版本全文](https://arxiv.org/html/2610.16245v1)，[历史说明](https://arxiv.org/abs/2610.16245)。本文使用其模型定义、Theorem 1、4、5，并讨论Conjecture 1、2、6。
2. Yijia Fang and Hao Huang. *Maximizing directed cycles in tournaments*. arXiv:2608.06238v1. [固定版本第3节](https://arxiv.org/html/2608.06238v1#S3)。本文使用Corollary 3.4；四次矩等号另在附录A.3复算。
3. Noga Alon. *The maximum number of Hamiltonian paths in tournaments*. Combinatorica 10 (1990), 319-324. [作者提供全文](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)。本文使用第2节所列Brégman永久式界。


