# 论文梳理：三个猜想、三条证明链

基线：LStar404/wormald-tournament-conjectures，提交 `59eb6ebcaa16c6b176ebd96023b4060a51274982`，论文 v0.2.6。原问题以 [Wormald v1](https://arxiv.org/html/2610.16245v1) 为准。Lean 的实际对象、最终定理与验证方法见 [形式化说明](../lean/README.zh.md)。

当前机器验证状态：原编号猜想 1、2、6 均已端到端完成。最终定理为 `Wormald.FiniteModel.conjectureOne_proof`、`Wormald.FiniteModel.conjectureTwo_proof` 和 `Wormald.conjectureSix`；猜想 1 另有 `uniqueClassConjectureOne_proof` 的唯一普通同构类加强版。下面的独立块渐近、正则块相关边渐近及实际解析 Hessian 均有对应证明，最终结果不依赖未证明的桥接假设。

## 先固定比较对象

基图有奇数 $d\ge3$ 个顶点，每个顶点换成 $m$ 个内部顶点，总阶数是 $N=dm$。块间方向由基图决定。独立块模型的每个内部竞赛图独立均匀选择；正则块模型的每个内部块独立均匀取自正则竞赛图，只考虑奇数 $m$。

用 $C(G)$ 表示按循环起点识别的有向 Hamilton 圈数，$H(G)$ 表示按有向顶点排列计数的 Hamilton 路数。归一化分别为

$$\nu_N=(N-1)!/2^N,\qquad \mu_N=N!/2^{N-1}.$$

猜想 1 比较固定 $d$、$m$ 充分大时的**随机模型期望**；猜想 2 讨论圆环模型常数的后续 $d\to\infty$ 极限；猜想 6 讨论 Wormald 原始角函数的 Hessian。它们不等于全体 $N$ 阶竞赛图的精确 Hamilton 极值，也不允许交换两个极限。

## 猜想 6：先计算原始 Hessian

这是其他计算的入口。设 $A$ 为正则基图邻接矩阵，

$$S=2A+I-J,\quad C=S/d,\quad z=2/d,\quad E=(e_1-e_d,\ldots,e_{d-1}-e_d).$$

原始对象是

$$K(y)=\det\bigl(I-(A+\tfrac12I)\operatorname{diag}(y)\bigr),\qquad
\widetilde f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}}),$$

其中 $h$ 在临界点附近由 $K(y',h(y'))=0$ 定义。不能直接把一个候选矩阵命名为 Hessian，然后省略这条连接。

最短的计算分成四步：

1. 竞赛图给出 $C^T=-C$ 和 $\|C\|_F^2=(d-1)/d<1$；正则性另给出 $C\mathbf1=0$。只为正定性，无须使用更强的配对谱界。
2. 令 $U=(I-C)^{-1}$、$q=\det(I-C)$。只改变两个坐标时，对三个秩一更新使用行列式公式，把 $K(z\mathbf1+ae_j+be_k)$ 化为明确的三阶行列式。取系数得到实际 $K_j=-q/2$ 及 $K_{jk}$。这一步完全是有限多项式运算，避免了对逆矩阵函数求两次导数。
3. $K$ 对最后一个变量仿射，而且 $K_{y_d}(z\mathbf1)=-q/2\ne0$，所以 $h=-K_0/K_1$ 在该点附近解析，且 $h(z,\ldots,z)=z>0$。对实际恒等式 $K(ze^{i\theta},h(ze^{i\theta}))=0$ 求两次导数，再使用实际复对数的链式法则，得到 $\mathbf H=E^TQE$，其中 $Q=U+U^T-I=(I+C^2)(I-C^2)^{-1}$。
4. $I+C^2\succ0$ 且 $Q=(I-C)^{-T}(I+C^2)(I-C)^{-1}\succ0$，故 $\mathbf H\succ0$。常数方向上 $Q\mathbf1=\mathbf1$，$E^TE=I+J$ 且其行列式为 $d$，所以

   $$\mathcal H=\det\mathbf H=d\frac{\det(I+C^2)}{\det(I-C^2)}.$$

转置与乘法给出

$$\det(I-C^2)=\det(I+C)^2,\qquad \det(I+C^2)=\det(I+iC)^2.$$

有理多项式 $p(t)=\det(I+tC)$ 满足 $p(t)=p(-t)$，故只有偶次幂，$p(i)$ 是有理数。逐个反对称二维块可知两个相关行列式都为正。因此

$$\sqrt{d/\mathcal H}=\frac{\det(I+C)}{\det(I+iC)}\in\mathbb Q_{>0}.$$

完整的短证明见 [Hessian 简明稿](concise-hessian-proof.zh.md)。三顶点例子应得到 $\mathbf H=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}$、$\mathcal H=3/4$、$\sqrt{3/\mathcal H}=2$，这也是形式化中的回归证书。

## 猜想 2：真实内层极限、闭式与外层极限

先固定正则底图阶数 $d$。正则内部块是独立公平块在“每块正则”事件上的真实条件律。有限生成函数把指定内部弧集的包含概率精确写成 Fourier 系数比，再写成完整周期域上的积分比。已证明的一致主峰与全部非中心估计给出

$$\Pr_{\rm reg}(D)=2^{-|D|}e^{b(D)/m}(1+o(1)),$$

其中误差对所有合法内部部分置换 $D$ 一致，$b(D)$ 为同时有内部入弧和出弧的顶点数。真实圈的内部弧集自动满足这些条件。把概率乘积逐项求和后，循环基词的三连统计给出 $\sum_i b(D_i)/m\to1/d$；指数集中与平衡条件化又保证正指数均值趋于 $e^{1/d}$。因此实际正则块期望的内层极限是 $e^{1/d}\rho_d(S)$。这个步骤已正式证明，不能只用闭式序列的极限替代。

圆环符号矩阵与传递符号矩阵 $T_d$ 带符号置换相似。传递矩阵满足

$$\det(I+tT_d)=\frac{(1+t)^d+(1-t)^d}{2}.$$

所以，Wormald 计数定理所识别的圆环正则块常数为

$$\mathfrak r_d=e^{1/d}
\frac{(1+1/d)^d+(1-1/d)^d}{(1+i/d)^d+(1-i/d)^d}.$$

**只证明极限时，不需要 Taylor 展开或单调性。** 对 $a=1,-1,i,-i$ 分别使用 $(1+a/d)^d\to e^a$，再用 $e^{1/d}\to1$ 和 $\cos1>0$，直接得到

$$\mathfrak r_d\longrightarrow\frac{e+e^{-1}}{e^i+e^{-i}}=\frac{\cosh1}{\cos1}.$$

Lean 已把任意奇阶实际圆环、一般行列式闭式与实际正则块内层期望极限接通，再取 $d=2j+3\to\infty$。`ConjectureTwoProof` 同时保证每个内层极限存在以及外层精确值；没有交换极限。细节见 [正则块一致概率估计](regular-forest-next-step.zh.md)、[主峰计算](regular-local-gaussian.zh.md)、[三连统计短证明](concise-markov-mixing.zh.md) 和 [对应审阅记录](verification-c2-correspondence.zh.md)。

如果需要原稿的加强结论，再独立阅读严格单调性和 $d^{-5}$ 展开。原稿以 $x=1/d$ 证明 $d\log\mathfrak r(x)/dx<0$，关键有理余量为 $42833/944784>0$；其余项估计在第一部分第 11 节。这个展开是基图阶数 $d$ 的展开，不是 $N$ 的统一误差。

## 猜想 1：谱比较、排除非正则、有限性

原论文用 [Wormald Theorem 1、4、5](https://arxiv.org/html/2610.16245v1) 将正则基图的四个归一化期望极限，分别识别为 $\rho_d(S)$ 或 $e^{1/d}\rho_d(S)$。本次 Lean 已从实际样本、精确 Fourier 积分及局部高斯分析独立证明编号猜想 1 所需的独立块 Hamilton 圈极限，无须将外部计数定理作为假设。其中

$$\rho_d(S)=\det(I+S/d)/\det(I+iS/d).$$

之后只需三步。

**正则基图的严格比较。** [Fang–Huang Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3) 的乘积弱主序及后缀取等结论，给出所有正整数 $p$ 的

$$\|S^p\|_F^2\le\|T_d^p\|_F^2.$$

把行列式比值写成绝对收敛、系数为正的级数，便可逐项比较：

$$\log\rho_d(S)=\sum_{r\ge0}\frac{\|S^{2r+1}\|_F^2}{(2r+1)d^{4r+2}}\le\log\rho_d(T_d).$$

若取等，六次矩取等经后缀取等强制四次矩取等。四阶行列式公式及 $\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S)$，说明 $S$ 是传递矩阵的带符号置换。再用正则性得到切换符号只能交替，从而恰为圆环的普通同构类。这里必须保留“正则性排除其他切换”的一步。

**非正则基图的归一化期望趋零。** 这条实际独立块模型的极限现在已由 Lean 完整证明。若基图出度为 $d_i$，令 $a_i=(2d_i+1)/d$。公平独立边逐对平均给出期望永久式不超过中点权重矩阵的永久式。按源顶点的目标基块分类置换，直接得到

$$\mathbb EC\le(m!)^d\prod_i(d_i+1/2)^m.$$

Stirling 给出 $R_{d,m}=(m!)^dd^{dm}/(dm)!=O_d(m^d)$，于是

$$0\le\frac{\mathbb EC}{\nu_{dm}}\le dm\,R_{d,m}\left(\prod_i a_i\right)^m\longrightarrow0,$$

因为非正则时严格算术几何平均给 $\prod_i a_i<1$。完整对应见 [非正则独立块简明证明](nonregular-independent-proof.zh.md)。这条直接界省去了独立块分支中的 Brégman 定理，并且严格只用于独立块；猜想 2 的正则块相关性由前述真实条件概率估计处理。路径类比可通过增加一个公平随机顶点和 $\mathbb E[C_{\rm aug}\mid G]=H(G)/4$ 处理，但尚未完成相应端到端形式化。

**有限多个基图给一个阈值。** 固定 $d$ 只有有限多个基图。每个非圆环基图的归一化极限都严格小于圆环；对每个基图分别取误差阈值，再取最大值。普通同构保持精确期望，因此得到唯一普通同构类。这个最后步骤、独立块非正则极限、正则实际计数渐近、完整谱比较及普通同构取等分类现均已形式化。`ConjectureOneProof` 已无额外假设地证明原编号猜想 1。短证明见 [幂矩比较](concise-moment-proof.zh.md)、[谱极值及唯一取等](spectral-extremum.zh.md) 和 [计数渐近的分析证明](local-counting-analysis.zh.md)。

这一渐近从原随机样本推导精确恒等式：Hamilton 圈期望等于 $(m!)^d/(dm)$ 倍的平衡循环词权重和，也等于对应矩阵幂迹的系数。所有标号与旋转因子均为实际双射所得，见 [精确计数系数简明证明](exact-independent-coefficient.zh.md)。随后分别证明局部主项、高斯余项控制和远域衰减，再乘精确 Stirling 常数；不是仅凭有限恒等式宣称得到了极限。

## 阅读与验证顺序

先读本说明和 Hessian 简明稿；需要单调性或误差项时再读原稿第一部分第 10–11 节；需要极值的严格等号或非正则上界时读第二部分及 A.2、A.3、A.6。

书面证明、有限精确核查、Lean 一般引理、原猜想端到端形式化是不同层次。原编号 1、2、6 的最终定理已消去全部计数与解析归约输入；保留的条件归约用于说明结构。路径伴随命题、严格单调性、高阶展开及原编号 3、4、5 不列入本轮端到端覆盖范围。
