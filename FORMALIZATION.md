# 本次论文梳理与 Lean 扩展

本目录保留原仓库 v0.2.6 的论文和公开包记录，并新增简明证明、实际数学对象的 Lean 定义及通过内核检查的一般引理。

**原编号猜想 1、2、6 的端到端 Lean 证明已完成。** `Wormald.FiniteModel.conjectureOne_proof` 证明原独立块模型的最终极值，另有唯一普通同构类加强版；`Wormald.FiniteModel.conjectureTwo_proof` 证明实际正则块模型的两层极限存在，并给出确切值 $\cosh(1)/\cos(1)$；`Wormald.conjectureSix` 从原解析 Hessian 的实际定义出发。最终定理没有 `sorry`、自定义公理或未证明的计数、解析输入。

建议依次阅读：

1. [三个猜想的证明路线](docs/proof-map.zh.md)
2. [从原始 Hessian 出发的简洁证明](docs/concise-hessian-proof.zh.md)
3. [Lean 覆盖范围、缺口和构建方法](lean/README.zh.md)
4. [猜想 6 完整依赖核查记录](verification/conjecture-six-verification.json)
5. [谱常数极值及普通同构唯一取等](docs/spectral-extremum.zh.md)
6. [真实计数渐近的分析连接](docs/local-counting-analysis.zh.md)
7. [正则块主峰的高斯计算及完整连接](docs/regular-local-gaussian.zh.md)
8. [三连统计的有限 Bernoulli 短证明](docs/concise-markov-mixing.zh.md)

Lean 源码入口是 [Wormald.lean](lean/Wormald.lean)，最终证明分别在 [ConjectureOneProof.lean](lean/Wormald/ConjectureOneProof.lean)、[ConjectureTwoProof.lean](lean/Wormald/ConjectureTwoProof.lean) 和 [ConjectureSixProof.lean](lean/Wormald/ConjectureSixProof.lean)。独立复核用 `python tools/check_conjecture_one.py`、`python tools/check_conjecture_two.py`、`python tools/check_conjecture_six.py`，全入口复核用 `python tools/check_lean.py`；后者也列出未接入入口的文件。原仓库的六个核查程序仍单独保留。根目录 `README.md` 已列明叶祥宇完成的新增工作；原 `AUDIT.md`、`MANIFEST.json` 和旧 PDF 审阅记录主要描述上游 v0.2.6，新增 Lean 部分以专门的验收记录为准。

原猜想 1 包括真实样本计数、实际计数渐近、非正则衰减、谱比较、普通同构唯一取等及有限共同阈值。猜想 2 包括实际均匀正则内部块、增长维数的一致包含概率估计、全部周期峰、平衡循环三连统计、固定底图的内层极限及后续奇底图阶数的外层极限；两个极限没有交换。猜想 6 保留实际隐函数、主值复对数和实角二阶导数。路径伴随猜想、单调性和高阶展开等加强结论不列作当前端到端覆盖范围。猜想 2 的独立语义复核见 [对应审阅记录](docs/verification-c2-correspondence.zh.md)。
