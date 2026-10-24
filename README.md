# Wormald tournament conjectures: Hessians and random blow-ups

[English](#english) · [中文](#中文)

## English

This repository holds our work on three of the conjectures in N. C. Wormald's [*Tournaments with many Hamilton cycles*](https://arxiv.org/html/2610.16245v1), namely Conjectures 1, 2 and 6. Besides the research paper, which exists in English and in Chinese, there is a Chinese guide written for readers who know only first-year calculus and linear algebra, a three-page map of the complete proof, exact computational checks, and a Lean 4 formalization.

The conjectures are Wormald's. The original research manuscript is by **Xingchen Liu** (刘星辰), an independent researcher; **Xiangyu Ye** (叶祥宇) is responsible for the later proof exposition, the simplifications and the Lean formalization. We are happy to be contacted at [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com).

### Read the documents

| Document | PDF | Editable source |
| --- | --- | --- |
| English research paper | [34 pages](output/pdf/wormald-conjectures-proof.en.pdf) | [Markdown](docs/paper.en.md) |
| Chinese research paper | [32 pages](output/pdf/wormald-conjectures-proof.zh.pdf) | [Markdown](docs/paper.zh.md) |
| Chinese elementary guide | [27 pages](output/pdf/wormald-conjectures-guide.zh.pdf) | [Markdown](docs/elementary-guide.zh.md) |
| Concise guide to the full proof, Chinese | [3 pages](output/pdf/wormald-conjectures-complete-proof.zh.pdf) | [Markdown](docs/concise-complete-proof.zh.md) |

The mathematics has not moved since version **0.2.6** of 21 October 2026. What the 24 October 2026 revision changed is the layout: definitions, theorems, lemmas, quoted results and proofs are now set apart by kind, notation is explained where it is first needed instead of in a block at the front, and headings, spacing and pagination were reworked. The formulas and derivations are still those of 0.2.6. Page counts are unchanged, except that the elementary guide gained one page; the four PDFs come to **96 pages**, and all of them were rendered and checked page by page.

A small bookkeeping effort keeps the record honest. The two papers each contain 963 mathematical expressions, the elementary guide 815, and the concise guide 68. [check_layout.py](tools/check_layout.py) reverses the recorded notation moves and editorial adjustments and checks that the recovered source hashes match the originals, and [check_translation.py](tools/check_translation.py) then compares the two languages — formula order, prose and display structure — after that same verified reversal, and compares the formulas as published. These are checks on documents. They are not part of the Lean verification.

### Mathematical scope and Lean coverage

Write $d$ for the order of the base graph and $m$ for the order of the blocks, so that the final tournament has order $N=dm$. The limit in $m$ is taken with $d$ held fixed; the later limit in odd $d$ does not commute with it.

| Original conjecture | What the end-to-end Lean statement covers | Proof |
| --- | --- | --- |
| 1 | Expectations of Hamilton cycles in the actual independent-block model: the eventual maximum over bases of fixed odd order, and uniqueness up to ordinary isomorphism | [`conjectureOne_proof`](lean/Wormald/ConjectureOneProof.lean) |
| 2 | Expectations in the actual uniform regular-block model: first the limit in odd block order, then the outer limit in odd base order, with outer constant $\cosh(1)/\cos(1)$ | [`conjectureTwo_proof`](lean/Wormald/ConjectureTwoProof.lean) |
| 6 | The Hessian built from the actual implicit function and the angular derivatives: nonzero determinant, and the required positive rational square | [`conjectureSix`](lean/Wormald/ConjectureSixProof.lean) |

The manuscript goes further than the formalization does. It also treats path analogues, monotonicity and higher-order expansions, and none of that is **covered end to end in Lean**. We do not claim a proof of the original global Conjectures 3, 4 or 5 either. The research manuscript itself is offered for independent mathematical review.

If you want the proof rather than the whole paper, start from the [concise guide](docs/concise-complete-proof.zh.md), the [proof map](docs/proof-map.zh.md) and the [formalization overview](FORMALIZATION.md). The [Lean guide](lean/README.zh.md) sets out the actual definitions, their dependencies, and exactly where coverage stops.

### Reproducing the checks

The project pins Lean 4.34.1 and the mathlib revision recorded in the [dependency manifest](lean/lake-manifest.json). From the repository root, run:

```text
python tools/check_lean.py
python tools/check_conjecture_one.py
python tools/check_conjecture_two.py
python tools/check_conjecture_six.py
```

All four original Lean gates were rerun on 24 October 2026 and all four passed. The full entry-point audit covers 211 local modules and 1286 exported theorems, and the Lean sources, the toolchain, the dependency lock and the four gates are unchanged from the layout baseline.

Each gate builds the Lean targets, elaborates the conjectures as stated, and audits the exported declarations together with the axioms they rest on. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`; `sorry`, `admit`, custom axioms and the other shortcuts listed in the checker are rejected. Records: [full entry point](verification/lean-verification.json), [Conjecture 1](verification/conjecture-one-verification.json), [Conjecture 2](verification/conjecture-two-verification.json), [Conjecture 6](verification/conjecture-six-verification.json). The logs are in [verification/lean-logs/](verification/lean-logs/).

The documents and the public package are checked separately:

```text
python tools/check_layout.py
python tools/check_translation.py
python tools/check_package.py
```

The exact finite checks from earlier versions are still in [verification/](verification/); [AUDIT.md](AUDIT.md) records what they count and how far their scope reaches. The layout revision does not present them as newly rerun mathematical proofs.

To build the PDFs you need Python with `pypdf`, Pandoc, Tectonic or XeLaTeX, and the fonts chosen in [the template](tools/template.tex). The Windows defaults are SimSun/SimHei for Chinese and Times New Roman/Arial for English.

```text
python tools/build_pdf.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
```

If you already have a Tectonic cache, point `--cache` at it. The builder relies on the [structure filter](tools/structure.lua) to lay out the semantic containers in the Markdown, and [PDF review records](verification/qa/pdf_review.json) tie every reviewed page to the hash of the published PDF.

### Citation and references

Please cite the original manuscript as: **Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*. Research manuscript, version 0.2.6, 2026.** Machine-readable metadata is in [CITATION.cff](CITATION.cff). If you use the later exposition or the Lean formalization, please credit Xiangyu Ye for those parts as well.

- N. C. Wormald, [*Tournaments with many Hamilton cycles*, arXiv:2610.16245v1](https://arxiv.org/html/2610.16245v1): where the conjectures and the random models come from.
- Yijia Fang and Hao Huang, [*Maximizing directed cycles in tournaments*, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3): the comparison result the original manuscript cites.
- Noga Alon, [*The maximum number of Hamiltonian paths in tournaments*](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf), Combinatorica 10 (1990), 319–324: the source of the permanent bound used in the manuscript.

The earlier [Hamiltonian-path repository](https://github.com/LStar404/tournament-hamiltonian-paths) is related work, with its own authorship and its own verification records.

## 中文

本仓库收录了我们对 N. C. Wormald [《Tournaments with many Hamilton cycles》](https://arxiv.org/html/2610.16245v1)中猜想 1、2、6 的工作：中英文双版研究论文、一份只要求基础微积分和线性代数的中文讲解、一份三页的完整证明导读、精确计算核查程序，以及 Lean 4 形式化。

猜想由 Wormald 提出。原研究论文的作者是独立研究者**刘星辰**（Xingchen Liu），**叶祥宇**（Xiangyu Ye）负责其后的证明梳理、简化和 Lean 形式化。联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)。

### 阅读文件

| 文件 | PDF | 可编辑源稿 |
| --- | --- | --- |
| 中文研究论文 | [32 页](output/pdf/wormald-conjectures-proof.zh.pdf) | [Markdown](docs/paper.zh.md) |
| 英文研究论文 | [34 页](output/pdf/wormald-conjectures-proof.en.pdf) | [Markdown](docs/paper.en.md) |
| 中文基础讲解 | [27 页](output/pdf/wormald-conjectures-guide.zh.pdf) | [Markdown](docs/elementary-guide.zh.md) |
| 中文完整证明导读 | [3 页](output/pdf/wormald-conjectures-complete-proof.zh.pdf) | [Markdown](docs/concise-complete-proof.zh.md) |

数学内容自 0.2.6 版（2026 年 10 月 21 日）以来没有改动。2026 年 10 月 24 日改的是排版：定义、定理、引理、引述结果和证明按类型分开呈现，符号说明移到首次用到它的地方，标题层次、行距和分页也重新调整过。公式与推导沿用 0.2.6 版。页数基本没变，只有基础讲解多了 1 页；四份 PDF 合计 **96 页**，已全部渲染并逐页看过。

中英文论文各含 963 处数学表达式，基础讲解 815 处，完整证明导读 68 处。核对用的是两个脚本：[排版核对程序](tools/check_layout.py)撤回已记录的符号迁移和文字调整，核对还原后的源稿哈希是否与原件一致；[中英文核对程序](tools/check_translation.py)在完成同样的还原之后，逐项比较两版的公式顺序与文字、公式段落结构，并比较发表版里的全部表达式。它们核对的是文稿，与 Lean 的证明核查各记各的账。

### 数学范围与 Lean 覆盖

记基图阶数为 $d$，块阶数为 $m$，最终竞赛图阶数为 $N=dm$。取 $m$ 的极限时 $d$ 固定；之后讨论奇数 $d$ 的极限，这两个极限不能交换。

| 原猜想编号 | 端到端 Lean 证明的对象 | 最终证明入口 |
| --- | --- | --- |
| 1 | 实际独立内部块模型下的 Hamilton 圈期望：固定奇基图阶数、块充分大时的最终最大者，以及普通同构意义下的唯一性 | [`conjectureOne_proof`](lean/Wormald/ConjectureOneProof.lean) |
| 2 | 实际均匀正则内部块模型下的期望：先取奇块阶数的内层极限，再取奇基图阶数的外层极限，外层常数为 $\cosh(1)/\cos(1)$ | [`conjectureTwo_proof`](lean/Wormald/ConjectureTwoProof.lean) |
| 6 | 从实际隐函数和角变量导数出发定义的 Hessian：行列式非零，且满足所要求的正有理平方性质 | [`conjectureSix`](lean/Wormald/ConjectureSixProof.lean) |

论文比形式化走得更远。路径类比、严格单调性和高阶展开这些加强内容**不在当前端到端 Lean 覆盖范围内**；我们也没有宣称证明原编号猜想 3、4、5。论文本身开放给外部专家独立审阅。

想直接看证明，可以先读[完整证明导读](docs/concise-complete-proof.zh.md)、[证明路线](docs/proof-map.zh.md)和[形式化说明](FORMALIZATION.md)。[Lean 说明](lean/README.zh.md)列出实际定义、依赖关系，以及覆盖到哪里为止。想从最基础的地方开始，[中文基础讲解](docs/elementary-guide.zh.md)从基本微积分和线性代数讲起，依次展开矩阵消元、链式求导、行列式比值、随机期望和极限比较。

### 重现核查

项目固定使用 Lean 4.34.1，mathlib 版本见[依赖锁定文件](lean/lake-manifest.json)。在仓库根目录依次运行：

```text
python tools/check_lean.py
python tools/check_conjecture_one.py
python tools/check_conjecture_two.py
python tools/check_conjecture_six.py
```

2026 年 10 月 24 日重新跑了原有四个 Lean 验收程序，全部通过。完整入口审计覆盖 211 个本地模块、1286 个导出定理。Lean 源码、工具链、依赖锁定和四个验收程序都与排版底稿保持一致。

每个验收程序都会构建 Lean 目标、核查所列原命题的证明，并审计导出声明及其依赖的公理。只接受 `propext`、`Classical.choice`、`Quot.sound` 三条标准公理；`sorry`、`admit`、自定义公理，以及检查器里列出的其他禁用捷径，一律拒绝。验收记录见[完整入口](verification/lean-verification.json)、[猜想 1](verification/conjecture-one-verification.json)、[猜想 2](verification/conjecture-two-verification.json)、[猜想 6](verification/conjecture-six-verification.json)，日志在 [verification/lean-logs/](verification/lean-logs/)。

文稿与公开文件另有检查：

```text
python tools/check_layout.py
python tools/check_translation.py
python tools/check_package.py
```

此前的精确有限核查程序仍保存在 [verification/](verification/) 中，[AUDIT.md](AUDIT.md)说明了它们的计数和适用范围。本次排版修订不会把早先的记录说成新完成的数学证明。

构建 PDF 需要 Python 与 `pypdf`、Pandoc、Tectonic 或 XeLaTeX，以及[模板](tools/template.tex)中选用的字体。Windows 下默认中文用宋体和黑体，英文用 Times New Roman 和 Arial。

```text
python tools/build_pdf.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
```

已经有 Tectonic 缓存的话，用 `--cache` 指过去。[结构过滤器](tools/structure.lua)负责把 Markdown 里的定义、定理、证明容器排进 PDF；[PDF 审阅记录](verification/qa/pdf_review.json)则把逐页检查的结果绑定到发布文件的哈希上。

### 引用与来源

引用原研究稿时请写：**Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*. Research manuscript, version 0.2.6, 2026.** 机器可读信息见 [CITATION.cff](CITATION.cff)。如果用到后续的证明梳理或形式化扩展，请按实际贡献一并署名叶祥宇。

- N. C. Wormald，[《Tournaments with many Hamilton cycles》固定版本](https://arxiv.org/html/2610.16245v1)：原猜想与随机模型的来源。
- Yijia Fang、Hao Huang，[《Maximizing directed cycles in tournaments》推论 3.4](https://arxiv.org/html/2608.06238v1#S3)：原研究稿引用的矩比较结果。
- Noga Alon，[《The maximum number of Hamiltonian paths in tournaments》](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)，Combinatorica 10 (1990), 319–324：文稿中永久式界的来源。

此前的[哈密顿路仓库](https://github.com/LStar404/tournament-hamiltonian-paths)属于相关工作，其作者信息与验证记录适用于原项目。
