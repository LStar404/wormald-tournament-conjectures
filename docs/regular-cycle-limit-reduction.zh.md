# 正则块模型的最后有限计数连接

本文说明原猜想 2 中，真实正则块期望怎样与平衡块字统计极限相接。这里保留便于阅读的条件归约结构；其中单块统一概率估计现已由 `UniformRegularTorusProof.lean` 完整证明，并在 `ConjectureTwoProof.lean` 中消去。最终原命题没有未证明的计数或解析输入。

固定一个 $d\ge3$ 的正则基础锦标赛，块大小为奇数 $m$。记

\[
\nu_{dm}=\frac{(dm-1)!}{2^{dm}},\qquad
\rho(T)=\frac{\det(I+C)}{\det(I+iC)},\qquad C=S(T)/d.
\]

Lean 中原独立块与正则块模型都由全部标号锦标赛的有限均匀样本定义。本文中的概率不是独立弧的替代模型。

## 1. 真实圈与内部弧集

一条 Hamilton 圈由具有单一轨道的后继置换 \(\sigma\) 表示，因而起点已经商去。在块 \(i\) 内，它使用的弧集为

\[
D_{\sigma,i}=\{(a,b):\sigma(i,a)=(i,b)\}.
\]

这些弧集没有环和反向弧对；每个顶点至多有一条出弧和一条入弧。设 \(a(D)=|D|\)，\(b(D)\) 是入弧与出弧同时存在的顶点数。真实正则模型恰有有限恒等式

\[
\mathbb E H_{\rm reg}
=\sum_{\sigma\text{ 为圈且块间相容}}
  \prod_i\Pr_{\rm reg}(D_{\sigma,i}).
\]

这是 `RegularCycleTransfer.lean` 已证明的准确样本平均。

## 2. 指数倾斜的独立圈和

定义

\[
Z_m=\sum_{\sigma\text{ 为圈且块间相容}}
 \prod_i\left(2^{-a(D_{\sigma,i})}
       e^{b(D_{\sigma,i})/m}\right).
\]

每条圈的独立模型权重就是 \(\prod_i2^{-a(D_{\sigma,i})}\)。给圈指定起点有 \(dm\) 种选择；给一个平衡块字恢复全部顶点标号有 \((m!)^d\) 种选择。此外，严格的统计恒等式为

\[
\sum_i b(D_{\sigma,i})
=\#\{t:f_t=f_{t+1}=f_{t+2}\},
\]

其中 \(f\) 是任意起点读出的循环块字。于是这两个有限重数恰好给出

\[
\frac{Z_m}{\nu_{dm}}
=\frac{\mathbb EH_{\rm ind}}{\nu_{dm}}
   \mathbb E_{\rm balanced}\!\left[e^{b(f)/m}\right].
\]

此式在平衡权重总和非零时成立；已证明对充分大 \(m\) 它严格为正。`TiltedCycleTransfer.lean` 的证明通过真实根标号纤维，而非重新假设独立性。

已有完整定理分别给出

\[
\frac{\mathbb EH_{\rm ind}}{\nu_{dm}}\longrightarrow\rho(T),
\qquad
\mathbb E_{\rm balanced}\!\left[e^{b(f)/m}\right]
\longrightarrow e^{1/d}.
\]

第二式来自保持旗标的有限 IID 恒等式、相邻旗标对的指数集中，以及对平衡占用的条件化。因此，无须正则弧集渐近估计，已经可以证明

\[
Z_m/\nu_{dm}\longrightarrow e^{1/d}\rho(T).
\]

## 3. 已经证明的一致概率估计

对所有合法内部部分置换弧集 \(D\)，已证明存在同一个 \(\varepsilon_m\ge0\)、\(\varepsilon_m\to0\)，使

\[
\left|2^{a(D)}\Pr_{\rm reg}(D)e^{-b(D)/m}-1\right|
\le\varepsilon_m.
\]

“合法”明确包括没有反向弧对：若允许同时指定 \(a\to b\) 与 \(b\to a\)，真实包含概率为零，上述统一估计不可能成立。Lean 的 `LegalPartialPermutationArcs` 精确列出全部条件，且真实圈的内部弧集自动满足它们。

从这个单块估计逐项相乘并求和，直接得到

\[
(1-\varepsilon_m)^dZ_m
\le \mathbb EH_{\rm reg}
\le(1+\varepsilon_m)^dZ_m
\]

（只须充分大 \(m\) 时 \(\varepsilon_m\le1\)）。夹逼定理因而给出真实模型的内层极限

\[
\frac{\mathbb EH_{\rm reg}}{\nu_{dm}}
\longrightarrow e^{1/d}\rho(T).
\]

对奇数阶 carousel，这个值等于已证明的闭式常数；其外层极限为 \(\cosh(1)/\cos(1)\)。`RegularCycleLimitReduction.lean` 将这一步接到准确的双层模型极限目标；其中保留的 `UniformRegularContainmentAsymptotic` 归约输入已由最终 `uniformRegularContainmentAsymptotic` 无条件证明。固定底图的内层极限和后续奇底图阶数的外层极限严格分开。

## 4. 真实 Fourier 积分如何证明这一估计

记 \(I_D\) 为 `normalizedRegularTorusIntegrand D` 在概率 Haar 测度下的积分，

\[
v_m=V_m/\pi^{m-1},\qquad c=e^{-1/2}.
\]

已证明的有限恒等式精确为

\[
\Pr_{\rm reg}(D)=2^{-a(D)}\frac{I_D}{I_\varnothing}.
\]

解析部分证明了

\[
\left|I_D/v_m-c e^{b(D)/m}\right|\le\eta_m,
\qquad\eta_m\ge0,\quad\eta_m\to0.
\]

空弧集也合法，所以同一估计给出 \(|I_\varnothing/v_m-c|\le\eta_m\)。充分大时 \(\eta_m\le c/2\)，从而分母的模长至少为 \(c/2\)。又因 \(b(D)\ge0\)，有 \(e^{-b(D)/m}\le1\)。三角不等式遂给出

\[
\left|2^{a(D)}\Pr_{\rm reg}(D)e^{-b(D)/m}-1\right|
\le4\eta_m/c.
\]

这些比值、非零分母和实复数转换在 `UniformRegularFourierReduction.lean` 中全部证明。原先保留的 `UniformRegularTorusMainTerm` 真实积分输入现由 `UniformRegularTorusProof.lean` 中的 `uniformRegularTorusMainTerm` 消去：实际主峰误差由 `RegularCentralMainTerm` 控制，完整周期域的补集由 `RegularNoncentralTail` 控制。精确物理角桥保证 \(I_D/v_m\) 等于锚定物理角积分除以 \(V_m\)，所有 \(\pi^{m-1}\) 因子严格抵消。

最终 `Wormald.FiniteModel.conjectureTwo_proof` 因而证明真实正则块模型的每个内层极限存在，并证明这些常数的外层极限是 \(\cosh(1)/\cos(1)\)。原编号猜想 1、2、6 的圈版本均已完成；路径伴随版本、严格单调性及高阶展开不列入这些最终定理的覆盖范围。
