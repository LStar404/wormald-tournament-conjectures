# Lean 形式化：原编号猜想 1、2、6 已完成

本项目补充于论文 v0.2.6，基线提交 `59eb6ebcaa16c6b176ebd96023b4060a51274982`。**原编号猜想 1、2、6 已完成端到端 Lean 形式化。** 最终定理分别为 `Wormald.FiniteModel.conjectureOne_proof : Wormald.FiniteModel.conjectureOne`、`Wormald.FiniteModel.conjectureTwo_proof : Wormald.FiniteModel.conjectureTwo` 和 `Wormald.conjectureSix : Wormald.ConjectureSix`。猜想 1 还证明唯一普通同构类加强版，保留实际独立块样本、所有基图及固定阶数后充分大块阶数的量词。猜想 2 使用实际均匀正则块，先取奇块阶数的内层极限，再取奇底图阶数的外层极限，得到 $\cosh(1)/\cos(1)$。猜想 6 保留原行列式、实际消元函数、主值复对数及实角二阶 Fréchet 导数，另有正有理谱平方根加强结论。

独立验收入口为 `python tools/check_conjecture_one.py`、`python tools/check_conjecture_two.py`、`python tools/check_conjecture_six.py`，相应记录位于 `verification/conjecture-one-verification.json`、`verification/conjecture-two-verification.json`、`verification/conjecture-six-verification.json`。检查覆盖最终定理的完整本地依赖闭包，并直接核对原命题及实际期望对象，无需额外计数或解析假设。整体入口与检查程序分别为 `Wormald.lean`、`python tools/check_lean.py`；未接入入口的文件会在记录中明确列出。模块数和定理数以对应检查记录为准。

## 可复现构建

固定 Lean `4.34.1`，Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。所有依赖版本记录于 `lake-manifest.json`。

在此目录运行：

```text
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Windows 可用 `./run-lean.ps1 build` 和 `./run-lean.ps1 env lean AxiomAudit.lean`，以便选择已经安装的相应工具链。首次使用须先安装 `lean-toolchain` 所指定的工具链。缓存只加速依赖获取；项目的证明仍交给 Lean 内核检查。交付源码不包含依赖缓存或机器专用的路径联接。

## 哪些已经证明

| 模块 | 内容与论文对应 | 限制 |
|---|---|---|
| `Definitions` | 真实 0/1 竞赛图、正则性、$S^T=-S$、零行和、归一化元素平方和 $(d-1)/d$；原始行列式多项式及其二阶代数公式 | 解析对应由后续模块证明 |
| `Elimination`、`CriticalPoint`、`CriticalGradient` | 原始复行列式等于有理多项式求值；最后坐标仿射；实际临界点、共同非零偏导及实际消元系数非零；$h$ 精确解原方程 | 不依赖计数渐近 |
| `ImplicitJet` | 一次及二次隐式求导方程推出正确的消元公式和角变量符号 | 一般代数引理保留求导方程前提；实际方程已在 `AnalyticJetBridge` 中从原函数证明 |
| `MatrixCore` | 逆矩阵代数、Hessian 候选核恒等式、两个行列式平方恒等式 | 逆方程在相应一般引理中明示 |
| `RationalSquare` | 任意有理反对称 $C$ 的 $\det(I+C^2)$ 是有理平方；相应行列式比也是有理平方 | 正根及原 $\mathcal H$ 对应由后续 `SpectralConstant`、`ConjectureSixProof` 完成，非零性单独证明 |
| `TwoColumnDeterminant`、`AlgebraicJets`、`CriticalJets` | 任意两个坐标的精确行列式展开；多项式代入与偏导相容；原始 $K$ 的全部所需一、二阶导数数据 | 适用于任意阶数，包含相同坐标的情形 |
| `CriticalResolvent`、`JetToCandidate` | 真正代数隐式二阶公式等于 $E^TQE$；复、实、有理矩阵及求值间的精确转换 | 对应仍从实际原多项式推导 |
| `AnalyticImplicit`、`AngleCalculus`、`ImplicitAlgebra`、`AnalyticJetBridge` | 实际多项式 Fréchet 求导、实际角坐标导数、局部光滑性、原隐式恒等式两次求导、实际主值复对数链式法则 | 不将导数方程或期望的 Hessian 等式作假设 |
| `ConjectureSixReduction`、`ConjectureSixProof` | 证明原解析 Hessian 等于候选矩阵，进而无条件证明原猜想 6 | 原问题的全部假设仅为正则竞赛图及相应阶数范围 |
| `Positivity`、`TournamentPositivity` | Cauchy–Schwarz、反对称二次型、实际竞赛图 $C$ 的 $(I+C^2)(I-C^2)^{-1}\succ0$ | 不需要加强的配对谱界 |
| `Compression` | $E$ 的列独立；实际竞赛图的候选矩阵 $E^TQE$ 正定且行列式为正 | 不将候选矩阵直接定义成原解析 Hessian |
| `CompressionDeterminant`、`RegularCandidate` | 一般压缩行列式因子 $d$；真实正则竞赛图的候选 Hessian 完整行列式公式 | 这里仍是候选有限矩阵，不是省略解析证明后重命名的 Hessian |
| `ThreeVertex` | 从三圈原始 $K$ 算到二阶代数矩阵 $\bigl(\begin{smallmatrix}1&1/2\\1/2&1\end{smallmatrix}\bigr)$、行列式 $3/4$、有理平方 $4$ | 有限例子；没有宣称覆盖任意阶数或原解析导数 |
| `SpectralConstant` | 实际谱行列式分子、分母及比值为正有理数；其平方和正平方根与 Hessian 行列式的准确对应 | 无正则性也可证明谱比值的正有理性，但这不自动给出非正则模型渐近 |
| `CarouselDeterminant`、`CarouselSwitching`、`CarouselConstantBridge`、`CarouselLimit` | 任意奇阶实际圆环的带符号置换对应、一般行列式闭式、谱常数及其 $\cosh1/\cos1$ 极限 | 实际内层模型极限现由 `ConjectureTwoProof` 完整识别；单调性和高阶余项不在本轮范围 |
| `FiniteModel`、`CarouselRegular` | 所有有标号竞赛图的布尔编码、与有理邻接矩阵对象的双射、真实圈和路计数、两种吹胀模型的精确均匀期望、普通同构、圆环逐边定义；任意奇阶圆环正则，因此合法正则块样本非空 | 定义真实期望不等于证明其渐近 |
| `CountIsomorphism` | 普通同构保持真实 Hamilton 圈、路计数，以及两种模型的四种期望 | 使用真实顶点与内部样本的双射，不使用符号切换 |
| `Eventual` | 有限族严格极限间隙推出共同阈值，保留奇块阶数等合法指标限制 | 是明示假设的逻辑归约，不是计数渐近证明 |
| `ConjectureOneReduction` | 将最终阈值归约专门用于真实 Hamilton 圈期望的正确归一化，再取消正分母回到原始计数；同构期望相等已证明 | 最简接口仅将实际归一化极限与严格间隙列为明示输入 |
| `ConjectureTwoReduction` | 先固定 $d$ 取正则块模型的真实归一化期望极限，再取奇 $d$ 极限；不以默认值代替不存在的极限 | 条件归约保留供阅读；其中内层输入已由 `UniformRegularTorusProof` 至 `ConjectureTwoProof` 消去 |
| `NonregularDegree`、`FactorialPrefactor`、`MeanPermanentDegree`、`NonregularCycles` | 非正则实际度数乘积严格小于 1；阶乘归一化仅有多项式增长；真实独立块归一化 Hamilton 圈期望趋于零 | 这条非正则分支已完整证明，不替代正则基图的渐近常数识别 |
| `PermanentBound`、`BlockPermanent`、`BoolCubeAverage`、`MeanPermanent` | 每个样本的实际圈数受永久式控制；真实独立边均匀平均受中点权重矩阵控制；非负重复块永久式直接上界 | 均值矩阵上界严格保留独立边假设，不能套给正则内部块 |
| `MomentComparison` 至 `NormalizedMoments` 的比较模块 | 一步及任意乘积弱主序、后缀取等、平方和比较、实际传递矩阵及圆环的全部幂矩对应 | 这是一般有限证明，无需外加矩比较假设 |
| `MomentSeries`、`MatrixMomentSeries`、`SkewMomentSeries`、`SpectralExtremum` | 实际谱比值的收敛对数矩级数；全部锦标赛的圆环谱常数上界；取等下降至四阶迹 | 无须计数渐近，非正则基图也适用谱比较 |
| `FourthMomentIdentity`、`FourthMomentEquality`、`SignClassification`、`RegularSignClassification`、`StrictSpectralGap` | 四点 Pfaffian 平方恒等式、传递矩阵的切换分类、正则性迫使交替符号、实际圆环的普通同构唯一取等 | 正则性用于最后一步普通同构分类 |
| `ConjectureOneSpectralReduction` | 保留方便阅读的条件归约：由实际正则计数渐近推出最终极值与唯一同构类 | 输入现已在 `ActualRegularCyclesLimit` 中完整证明，由 `ConjectureOneProof` 消去 |
| `ExactCycleTransfer`、`RootedCycleOrder`、`CycleLabelingFiber`、`CycleWordTransfer`、`TraceWordExpansion`、`MarkovCycleTransfer`、`ExactCycleCoefficient` | 原独立样本期望精确等于平衡循环词权重；标号数恰为 $(m!)^d$；真实计数等于有限矩阵幂迹系数 | 内部正则块不满足这里的独立边恒等式 |
| `FactorialPrefactorLimit`、`PolynomialFourierCoefficient` | 阶乘因子的精确 Stirling 比例极限；任意多元多项式系数等于归一化环面 Fourier 积分 | 局部积分渐近由后续真实谱分支、Gaussian 分析和远域控制另行证明 |
| `CriticalTransitionContraction` 至 `CriticalTransitionTwoStep` | 实际正则转移矩阵严格收缩零和向量；固定锚定相位后唯一单位圆特征值；非临界相位的两步严格收缩 | 只是计数渐近所需的分析基础，不能替代最终积分极限 |
| `ActualRegularCyclesLimit`、`ConjectureOneProof` | 实际 Fourier 积分的局部主项、真实可积余项与远域合并；精确 Stirling 因子识别原谱常数；无条件证明原猜想 1 及唯一普通同构类加强版 | 覆盖原编号猜想的独立块 Hamilton 圈版本，未声称同时覆盖路径或正则块伴随极值 |
| `RegularConditioning` | 正则内部块真实期望与公平独立样本的精确条件化关系；正则事件概率严格为正及各块乘积公式；度数零约束与边包含概率条件式 | 后续一致渐近对真实条件律证明，未套用独立边平均 |
| `RegularDegreePolynomial`、`RegularForestFourier`、`RegularForestCosine`、`RegularCycleTransfer` | 实际正则包含概率的系数比、Fourier 比、余弦比；真实 Hamilton 圈期望的内部边集有限和 | 增长维一致估计已由主峰和完整非中心尾界接通 |
| `CosineTaylorBounds`、`DeletedCosineApproximation`、`GaussianGraphCorrection`、`GaussianGraphFourierIntegral` | 真实余弦 Taylor 误差、删边修正、一般度二矩阵的精确高斯积分、统一相对误差 $32/m$ 及 $L^2$ 界 | 实际 torus 到 Gaussian 的统一替换已在 `RegularCentralMainTerm`、`UniformRegularTorusProof` 完成 |
| `GaussianQuarticIdentity` 至 `GaussianQuarticCancellation` | 公共四次项有限恒等式、真实标准正态矩值、增长维高斯乘积上的集中、复权重下一致消去 | 维数可以变化；该结果不代替 torus 非中心尾界 |
| `CircleClusterCover` 至 `RegularNoncentralTail` 的圆簇与积分模块 | 有限覆盖、真实远边、好点图重标号、Haar 投影、精确实代表积分、Gaussian 商体积、两支尾界及全部主峰外区域 | 已控制实际完整 torus 的非中心范数积分，误差对全部合法内部部分置换一致 |
| `HoldingFlags` 至 `BalancedTripleExponential`、`InternalTripleStatistic`、`TiltedCycleTransfer` | 实际停留标志的 Bernoulli 乘积律、循环三连指数尾界、平衡条件化、正指数均值及真实内部边集统计对应 | 已证明修正为 $e^{+1/d}$，没有把指数期望替换为期望的指数 |
| `RegularCentralMainTerm`、`UniformRegularTorusProof`、`ConjectureTwoProof` | 实际主峰及补集的完整统一误差；真实正则包含概率渐近；固定正则底图内层极限与 carousel 外层极限 | 无条件证明原编号猜想 2；未覆盖路径伴随命题或闭式单调性 |

`ConjectureSix`、`AnalyticJetBridge`、`AnalyticCandidateCorrespondence` 分别由 `conjectureSix`、`Tournament.analyticJetBridge`、`analyticCandidateCorrespondence` 证明。`FiniteModel.conjectureOne`、`uniqueClassConjectureOne`、`RegularCycleAsymptotics` 分别由 `conjectureOne_proof`、`uniqueClassConjectureOne_proof`、`regularCycleAsymptotics` 证明。`FiniteModel.conjectureTwo` 由 `conjectureTwo_proof` 证明；其中 `UniformRegularTorusMainTerm` 已由 `UniformRegularTorusProof.lean` 内的 `FiniteModel.uniformRegularTorusMainTerm` 实际构造消去。原条件归约保留用于阅读结构；最终定理不保留未证明的计数与解析输入。

## 已完成的原命题与覆盖边界

猜想 6：原命题已完成，且正定性、完整行列式公式和实际正有理谱平方根均有形式化证明。

猜想 2：实际正则块主峰替换、完整周期域统一尾界、平衡条件化、正指数加权极限、固定底图内层极限及奇底图阶数外层极限均已完成。见 [正则块一致概率估计](../docs/regular-forest-next-step.zh.md)、[主峰高斯计算](../docs/regular-local-gaussian.zh.md)、[三连计数短证明](../docs/concise-markov-mixing.zh.md) 和 [原命题对应独立复核](../docs/verification-c2-correspondence.zh.md)。

猜想 1：原编号命题已完整证明，包括所有基图、实际独立块计数渐近、非正则分支、唯一普通同构类与共同阈值。

当前范围不包括 Hamilton 路的伴随猜想、正则块伴随极值、carousel 常数的严格单调性或高阶展开加强，也不证明原编号猜想 3、4、5。圈版本中的最终结果不能自动当作这些加强命题的证明。

## 信任与检查

项目没有 `sorry`、`admit`、自定义 `axiom` 或 `native_decide` 证明。`AxiomAudit.lean` 枚举导出定理的实际公理依赖；标准库允许 `propext`、`Classical.choice`、`Quot.sound`，不能将此误说为“完全没有公理”。最终构建和检查记录保存在交付包的 `verification` 中。

书面简化见 [Hessian 简明稿](../docs/concise-hessian-proof.zh.md)、[幂矩比较](../docs/concise-moment-proof.zh.md)、[谱极值与唯一取等](../docs/spectral-extremum.zh.md)、[精确计数系数](../docs/exact-independent-coefficient.zh.md) 和 [论文梳理](../docs/proof-map.zh.md)。原稿与原 Python 检查记录作为基线保存，不把旧版排版、翻译审阅记录改写成此次 Lean 的认证。

## 本轮进一步探索的取舍

得到几项直接用于主线的简化：二坐标有限行列式展开替代逆矩阵的二次解析求导；较弱的 Frobenius 界已足够证明正定；Abel 加权比较给出平方和及其等号条件，无需正部积分。独立块非正则部分也有利用重复块结构绕开 Brégman 的直接永久式上界。最后一条仅用于独立边模型，不用于均匀正则块。这里没有对历史优先权作判断，也没有据此宣称更广泛的 Hamilton 极值突破。
