# Wormald tournament conjectures: Hessians and random blow-ups

[English](#english) · [中文](#中文)

## English

This repository contains a Chinese/English research manuscript, a Chinese elementary guide, a concise proof guide, exact computational checks, and Lean formalizations concerning Conjectures **1, 2 and 6** in N. C. Wormald's [*Tournaments with many Hamilton cycles*](https://arxiv.org/html/2610.16245v1).

The original research manuscript is by **Xingchen Liu (刘星辰)**, independent researcher. **Xiangyu Ye (叶祥宇)** contributed the subsequent proof exposition, simplification and Lean formalization. The conjectures are Wormald's. Contact: [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com).

### Read the documents

| Document | PDF | Editable source |
| --- | --- | --- |
| English research paper | [34 pages](output/pdf/wormald-conjectures-proof.en.pdf) | [Markdown](docs/paper.en.md) |
| Chinese research paper | [32 pages](output/pdf/wormald-conjectures-proof.zh.pdf) | [Markdown](docs/paper.zh.md) |
| Chinese elementary guide | [27 pages](output/pdf/wormald-conjectures-guide.zh.pdf) | [Markdown](docs/elementary-guide.zh.md) |
| Concise complete proof guide, Chinese | [3 pages](output/pdf/wormald-conjectures-complete-proof.zh.pdf) | [Markdown](docs/concise-complete-proof.zh.md) |

The manuscript's mathematical revision remains **0.2.6, 21 October 2026**. The **24 October 2026 layout revision** structures definitions, theorems, lemmas, quoted results and proofs; distributes notation explanations through the relevant arguments; and improves headings, spacing and pagination. The computational formulas and derivation steps are retained. The papers keep their previous page counts; the elementary guide gains one page. All four PDFs, totaling **96 pages**, were rendered and visually checked.

The two papers each retain **963 mathematical expressions**; the elementary guide retains **815**, and the concise guide **68**. [The layout check](tools/check_layout.py) reverses the recorded notation moves and editorial adjustments and checks the recovered original source hashes. [The bilingual check](tools/check_translation.py) preserves the original formula-sequence and prose/display checks after that verified reversal, and also compares the formulas in the published papers. These are document checks, separate from Lean proof checking.

### Mathematical scope and Lean coverage

Here $d$ is the base order, $m$ is the block order, and $N=dm$ is the final tournament order. Limits in $m$ fix $d$ first. The later odd-$d$ limit does not interchange these limits.

| Original conjecture | End-to-end Lean statement | Final proof |
| --- | --- | --- |
| 1 | Actual independent-block Hamilton-cycle expectations: eventual maximum over bases of fixed odd order, with uniqueness up to ordinary isomorphism | [`conjectureOne_proof`](lean/Wormald/ConjectureOneProof.lean) |
| 2 | Actual uniform regular-block expectations: first the odd block-order limit, then the odd base-order limit, with outer constant $\cosh(1)/\cos(1)$ | [`conjectureTwo_proof`](lean/Wormald/ConjectureTwoProof.lean) |
| 6 | The Hessian defined from the actual implicit function and angular derivatives: nonzero determinant and the required positive rational square | [`conjectureSix`](lean/Wormald/ConjectureSixProof.lean) |

The manuscript also discusses path counterparts, monotonicity and higher-order expansions. Those additions are **outside the current end-to-end Lean coverage**. This repository does not claim proofs of the original global Conjectures 3, 4 or 5. The research manuscript remains available for independent mathematical review.

For the proof route, start with the [concise guide](docs/concise-complete-proof.zh.md), [proof map](docs/proof-map.zh.md) and [formalization overview](FORMALIZATION.md). The [Lean guide](lean/README.zh.md) states the exact definitions, dependencies and coverage boundaries.

### Reproduce the checks

The project pins **Lean 4.34.1** and the mathlib revision in [the dependency manifest](lean/lake-manifest.json). From the repository root, run:

```text
python tools/check_lean.py
python tools/check_conjecture_one.py
python tools/check_conjecture_two.py
python tools/check_conjecture_six.py
```

**Verification rerun, 24 October 2026:** all four original Lean gates passed. The full entry-point audit covers 211 local modules and 1286 exported theorems. Lean sources, toolchain, dependency lock and the four original gates are unchanged from the layout baseline.

The original gates build the Lean targets, elaborate the stated conjectures and audit exported declarations and their axiom dependencies. The permitted standard axioms are `propext`, `Classical.choice` and `Quot.sound`; the checks reject `sorry`, `admit`, custom axioms and the other forbidden proof shortcuts listed in the checker. Records: [full entry point](verification/lean-verification.json), [Conjecture 1](verification/conjecture-one-verification.json), [Conjecture 2](verification/conjecture-two-verification.json), [Conjecture 6](verification/conjecture-six-verification.json). Logs are in [verification/lean-logs/](verification/lean-logs/).

Document and package checks:

```text
python tools/check_layout.py
python tools/check_translation.py
python tools/check_package.py
```

The earlier exact finite checks remain in [verification/](verification/). Their recorded counts and mathematical scope are documented in [AUDIT.md](AUDIT.md). The layout revision does not present those earlier checks as newly rerun mathematical proofs.

To build the PDFs, install Python with `pypdf`, Pandoc, Tectonic or XeLaTeX, and the fonts selected in [the template](tools/template.tex). Windows defaults use SimSun/SimHei for Chinese and Times New Roman/Arial for English.

```text
python tools/build_pdf.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
```

An existing Tectonic cache can be supplied with `--cache`. The builder uses the [structure filter](tools/structure.lua) to render the semantic Markdown containers. [PDF review records](verification/qa/pdf_review.json) bind the reviewed pages to the published PDF hashes.

### Attribution and references

Please cite the original manuscript as: **Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*. Research manuscript, version 0.2.6, 2026.** Machine-readable metadata is in [CITATION.cff](CITATION.cff). Please also acknowledge Xiangyu Ye's separately described exposition and Lean formalization when using that extension.

- N. C. Wormald, [*Tournaments with many Hamilton cycles*, arXiv:2610.16245v1](https://arxiv.org/html/2610.16245v1): source of the conjectures and random models.
- Yijia Fang and Hao Huang, [*Maximizing directed cycles in tournaments*, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3): the comparison result cited by the original manuscript.
- Noga Alon, [*The maximum number of Hamiltonian paths in tournaments*](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf), Combinatorica 10 (1990), 319–324: the permanent bound cited in the manuscript.

The earlier [Hamiltonian-path repository](https://github.com/LStar404/tournament-hamiltonian-paths) is related work with its own authorship and verification records.

## 中文

本仓库包含中英文研究论文、中文基础讲解、中文完整证明导读、精确计算核查程序，以及针对 N. C. Wormald [《Tournaments with many Hamilton cycles》](https://arxiv.org/html/2610.16245v1)中原编号**猜想1、2、6**的 Lean 形式化证明。

原研究论文作者为独立研究者**刘星辰（Xingchen Liu）**。**叶祥宇（Xiangyu Ye）**完成了后续的证明梳理、简化与 Lean 形式化扩展。猜想本身属于 Wormald。联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)。

### 阅读文件

| 文件 | PDF | 可编辑源稿 |
| --- | --- | --- |
| 中文研究论文 | [32页](output/pdf/wormald-conjectures-proof.zh.pdf) | [Markdown](docs/paper.zh.md) |
| 英文研究论文 | [34页](output/pdf/wormald-conjectures-proof.en.pdf) | [Markdown](docs/paper.en.md) |
| 中文基础讲解 | [27页](output/pdf/wormald-conjectures-guide.zh.pdf) | [Markdown](docs/elementary-guide.zh.md) |
| 中文完整证明导读 | [3页](output/pdf/wormald-conjectures-complete-proof.zh.pdf) | [Markdown](docs/concise-complete-proof.zh.md) |

论文的数学内容版本仍为**0.2.6，2026年10月21日**。**2026年10月24日排版修订**将定义、定理、引理、引用定理和证明按类型呈现，将原先集中在开头的符号说明移到相关推导处，并调整标题层次、行距及分页。原有计算公式与推导步骤保留。中英文论文页数不变，基础讲解增加1页。四份 PDF 共**96页**，均已渲染并逐页检查。

中英文论文各保留**963处数学表达式**，基础讲解保留**815处**，完整证明导读保留**68处**。[排版核对程序](tools/check_layout.py)会撤回已记录的符号迁移和文字调整，验证能否恢复原稿的哈希；[中英文核对程序](tools/check_translation.py)在完成该还原检查后，继续检查原稿的公式顺序与文字、公式段落结构，并比较发表版的全部数学表达式。这些属于文稿核对，与 Lean 的证明核查分别记录。

### 数学范围与 Lean 覆盖

$d$ 是基图阶数，$m$ 是块阶数，最终竞赛图阶数为 $N=dm$。取 $m$ 的极限时先固定 $d$；其后讨论奇数 $d$ 的极限，没有交换这两重极限。

| 原猜想编号 | 端到端 Lean 证明的对象 | 最终证明入口 |
| --- | --- | --- |
| 1 | 实际独立内部块模型的 Hamilton 圈期望：固定奇基图阶数、块充分大时的最大者，以及普通同构意义下的唯一性 | [`conjectureOne_proof`](lean/Wormald/ConjectureOneProof.lean) |
| 2 | 实际均匀正则内部块模型的期望：先取奇块阶数的内层极限，再取奇基图阶数的外层极限，外层常数为 $\cosh(1)/\cos(1)$ | [`conjectureTwo_proof`](lean/Wormald/ConjectureTwoProof.lean) |
| 6 | 从实际隐函数和角变量导数定义的 Hessian 出发，证明行列式非零及所要求的正有理平方性质 | [`conjectureSix`](lean/Wormald/ConjectureSixProof.lean) |

论文还讨论路径类比、严格单调性与高阶展开；这些加强内容**不在当前端到端 Lean 覆盖范围内**。本仓库不宣称证明了原编号猜想3、4、5。研究论文仍开放供外部专家独立审阅。

建议先读[完整证明导读](docs/concise-complete-proof.zh.md)、[证明路线](docs/proof-map.zh.md)和[形式化说明](FORMALIZATION.md)。[Lean 说明](lean/README.zh.md)列出实际定义、依赖和覆盖边界。[中文基础讲解](docs/elementary-guide.zh.md)从基本微积分和线性代数出发，展开矩阵消元、链式求导、行列式比值、随机期望及极限比较。

### 重现核查

项目固定使用 **Lean 4.34.1**；mathlib 版本见[依赖锁定文件](lean/lake-manifest.json)。在仓库根目录依次运行：

```text
python tools/check_lean.py
python tools/check_conjecture_one.py
python tools/check_conjecture_two.py
python tools/check_conjecture_six.py
```

**2026年10月24日重新核查：**原有四个 Lean 验收程序全部通过。完整入口审计覆盖211个本地模块、1286个导出定理。Lean 源码、工具链、依赖锁定和四个原有检查程序与排版底稿保持一致。

原有核查程序会构建 Lean 目标，检查所列原命题的证明，并审计导出声明的公理依赖。允许的标准公理为 `propext`、`Classical.choice`、`Quot.sound`；程序拒绝 `sorry`、`admit`、自定义公理及检查器列出的其他禁用捷径。验收记录分别为[完整入口](verification/lean-verification.json)、[猜想1](verification/conjecture-one-verification.json)、[猜想2](verification/conjecture-two-verification.json)、[猜想6](verification/conjecture-six-verification.json)，日志在 [verification/lean-logs/](verification/lean-logs/) 中。

文稿与公开文件检查：

```text
python tools/check_layout.py
python tools/check_translation.py
python tools/check_package.py
```

此前的精确有限核查程序保存在 [verification/](verification/)；[AUDIT.md](AUDIT.md)说明其计数和适用范围。本次排版修订不会将早先记录改称为新完成的数学证明。

构建 PDF 需要 Python 与 `pypdf`、Pandoc、Tectonic 或 XeLaTeX，以及[模板](tools/template.tex)中选用的字体。Windows 默认中文字体为宋体/黑体，英文字体为 Times New Roman/Arial。

```text
python tools/build_pdf.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
```

已有 Tectonic 缓存可用 `--cache` 指定。[结构过滤器](tools/structure.lua)负责将 Markdown 中的定义、定理和证明容器排入 PDF。[PDF审阅记录](verification/qa/pdf_review.json)将逐页检查结果与实际文件哈希绑定。

### 引用与来源

原研究稿建议引用为：**Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*. Research manuscript, version 0.2.6, 2026.** 机器可读信息见 [CITATION.cff](CITATION.cff)。使用后续证明梳理与形式化扩展时，也请按该扩展的实际贡献说明致谢叶祥宇。

- N. C. Wormald，[原论文固定版本](https://arxiv.org/html/2610.16245v1)：原猜想和随机模型的来源。
- Yijia Fang、Hao Huang，[原论文推论3.4](https://arxiv.org/html/2608.06238v1#S3)：原研究稿引用的矩比较结果。
- Noga Alon，[Hamilton 路论文](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)，Combinatorica 10 (1990)，319–324：文稿所引永久式界的来源。

[此前的哈密顿路仓库](https://github.com/LStar404/tournament-hamiltonian-paths)属于相关工作，其作者信息与验证记录适用于原项目。
