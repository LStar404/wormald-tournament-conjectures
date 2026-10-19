# Wormald tournament conjectures: Hessians and random blow-ups

[English](#english) · [中文](#中文)

## English

**Wormald tournament conjectures: Hessians and random blow-ups**  
Xingchen Liu · Independent Researcher  
Contact: [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)

This repository contains a research manuscript, an elementary companion guide,
and exact computational checks addressing Conjectures **1, 2 and 6** in
N. C. Wormald's [*Tournaments with many Hamilton cycles*](https://arxiv.org/html/2610.16245v1).
The conjectures are Wormald's. This research draft is authored by **Xingchen Liu**.

**Read the paper:** [Chinese proof PDF](output/pdf/wormald-conjectures-proof.zh.pdf)
(22 pages) · [Chinese elementary guide PDF](output/pdf/wormald-conjectures-guide.zh.pdf)
(20 pages)  
**Editable sources:** [Proof manuscript](docs/paper.zh.md) ·
[Elementary guide](docs/elementary-guide.zh.md)  
Current repository revision: **0.1.1**, 19 October 2026.
The manuscripts are currently in Chinese; this README is bilingual.

### Main results

Let $d\ge3$ be odd, let $A$ be the adjacency matrix of a regular
$d$-vertex tournament, and put

$$
S=2A+I-J,\qquad C=S/d,\qquad
E=(e_1-e_d,\ldots,e_{d-1}-e_d).
$$

The manuscript derives the following formula for Wormald's logarithmic-angle
Hessian $\mathbf H$, with $\mathcal H=\det\mathbf H$:

$$
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,
\qquad
\mathcal H=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,
$$

$$
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}
=:\rho_d(S)\in\mathbb Q_{>0}.
$$

For the carousel base, the limiting constant for regular internal blocks is

$$
\mathfrak r_d=e^{1/d}
\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}
\ \uparrow\ \frac{\cosh1}{\cos1}
$$

along odd $d\ge3$. The paper proves strict monotonicity and gives an explicit
expansion through $d^{-5}$.

Combining the Hessian identity with the cited counting and matrix-comparison
theorems gives the fixed-base extremum: for each fixed odd $d$, there is
$M_d$ such that, for every block order $m\ge M_d$, the carousel is the unique
base tournament up to ordinary isomorphism maximizing expected Hamilton
cycle and path counts. This holds for independent random internal blocks
and for uniform regular internal blocks, with odd $m$ in the latter model.

| Wormald conjecture | Result presented in this draft |
| --- | --- |
| 1 | Eventual unique maximum of the fixed-base blow-up expectation; also path and regular-block analogues |
| 2 | Closed form, strict monotonicity, exact limit and explicit expansion of the carousel model constant |
| 6 | Positive-definite Hessian and a positive rational formula for its associated square root |

Here $d$ is the base order, $m$ is the block order, and $N=dm$ is the final
tournament order. The block limit is taken with $d$ fixed. These statements
concern random-model expectations; they do not establish the global exact
Hamilton extremum in Conjecture 3 or interchange the two limits.

### Guide for reviewers

Start with the conjecture correspondence and reading roadmap in
[the manuscript](docs/paper.zh.md). Part I, Sections 1–7, derives the finite
Hessian identity by linear algebra and differentiation. Part I, Section 8,
uses Wormald's Theorems 1, 4 and 5 to identify the model constants.
Part II uses Fang–Huang's Corollary 3.4 for the moment comparison, and treats
nonregular bases separately using the Brégman permanent bound.
Part III expands the determinant calculation, equality classification,
path augmentation, normalization and finite-threshold argument.

The [companion guide](docs/elementary-guide.zh.md) starts from basic calculus
and linear algebra, including the full product-rule calculation and a worked
three-vertex example.

The manuscript is an AI-assisted preprint awaiting independent expert review.
The [review record](AUDIT.md) distinguishes exact finite checks from
high-precision diagnostics. This repository contains no Lean formalization
of these results and makes no claim of historical priority.

### Reproduce the checks

Use Python 3.10 or newer. The mathematical checks use only the standard library.
From the repository root:

    python verification/verify_wormald_hessian_spectral_bridge.py
    python verification/verify_wormald_fixed_base_extremum.py
    python verification/audit_publication_identities.py
    python tools/check_package.py

The mathematical checks cover 11,724 exact Hessian entries, 345
coordinate-elimination determinants, all 2,666 labelled regular tournaments
of orders 3, 5 and 7, finite blow-up expectations, and weighted permanent
bounds. The [saved records](verification/qa/) describe the individual checks.
Finite checks support error detection; the general statements depend on
the written proofs and the explicitly cited external theorems.

The PDFs are generated from Markdown through Pandoc and Tectonic or XeLaTeX.
Build instructions are in [the PDF builder](tools/build_pdf.py).
All 42 pages were rendered and visually inspected; [the layout record](verification/qa/pdf_review.json)
records that review separately from mathematical verification.

### Repository contents

| Location | Contents |
| --- | --- |
| [docs/](docs/) | Proof manuscript and elementary guide in Markdown |
| [output/pdf/](output/pdf/) | Reading PDFs |
| [verification/](verification/) | Exact-arithmetic checks and helper routines |
| [verification/qa/](verification/qa/) | Mathematical check records and PDF layout record |
| [tools/](tools/) | PDF build and package-verification tools |
| [AUDIT.md](AUDIT.md) | Review scope, dependencies and revision record |
| [MANIFEST.json](MANIFEST.json) | File hashes for the current publication package |

### Citation and sources

For this research draft, cite:

> Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*.
> Research draft, version 0.1.1, 2026.
> https://github.com/LStar404/wormald-tournament-conjectures.

Machine-readable citation metadata is in [CITATION.cff](CITATION.cff).
The [earlier Hamiltonian-path repository](https://github.com/LStar404/tournament-hamiltonian-paths)
is related work; its authorship and formal-verification records belong to that project.

1. N. C. Wormald,
   [*Tournaments with many Hamilton cycles*, arXiv:2610.16245v1](https://arxiv.org/html/2610.16245v1):
   model definitions, counting theorems and the conjectures discussed here.
2. Yijia Fang and Hao Huang,
   [*Maximizing directed cycles in tournaments*, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3):
   weak-majorization input for the moment comparison.
3. Noga Alon,
   [*The maximum number of Hamiltonian paths in tournaments*](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf),
   Combinatorica 10 (1990), 319–324: the stated Brégman bound.

## 中文

**Wormald竞赛图猜想：Hessian恒等式与随机吹胀模型**  
刘星辰 · 个人研究者  
联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)

本仓库收录研究论文、基础讲解和精确计算核查程序，讨论N. C. Wormald的
[*Tournaments with many Hamilton cycles*](https://arxiv.org/html/2610.16245v1)
中猜想 **1、2、6**。原猜想归属于Wormald，**本研究稿由刘星辰独立署名**。

**阅读论文：**[完整证明PDF](output/pdf/wormald-conjectures-proof.zh.pdf)（22页）·
[大一基础讲解PDF](output/pdf/wormald-conjectures-guide.zh.pdf)（20页）  
**可编辑稿：**[论文Markdown](docs/paper.zh.md) ·
[基础讲解Markdown](docs/elementary-guide.zh.md)  
当前仓库修订版本：**0.1.1**，2026年10月19日。
现有论文和讲解为中文，README提供完整中英双语内容。

### 主要结果

设$d\ge3$为奇数，$A$为$d$阶正则竞赛图的邻接矩阵，令

$$
S=2A+I-J,\qquad C=S/d,\qquad
E=(e_1-e_d,\ldots,e_{d-1}-e_d).
$$

论文从Wormald的原始定义出发，推导其对数角Hessian矩阵$\mathbf H$及
行列式$\mathcal H=\det\mathbf H$：

$$
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,
\qquad
\mathcal H=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,
$$

$$
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}
=:\rho_d(S)\in\mathbb Q_{>0}.
$$

圆环基图、正则内部块模型的极限常数有闭式

$$
\mathfrak r_d=e^{1/d}
\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}
\ \uparrow\ \frac{\cosh1}{\cos1}
$$

其中$d$沿奇数$d\ge3$增长。论文证明其严格单调性，
并计算了直到$d^{-5}$项的显式展开。

结合文中注明来源的计数与矩阵比较定理，可得到固定基图的极值结论：
对每个固定奇数$d$，存在$M_d$，使得所有$m\ge M_d$时，
圆环基图在普通同构意义下唯一最大化Hamilton圈及路径的期望。
结论适用于独立随机内部块和均匀正则内部块；后一模型只沿奇数$m$考虑。

| Wormald猜想编号 | 本稿给出的结果 |
| --- | --- |
| 1 | 固定基图随机吹胀期望的最终唯一最大者，以及路径和正则内部块类比 |
| 2 | 圆环模型常数的闭式、严格单调性、精确极限及显式展开 |
| 6 | Hessian正定性，以及相应平方根的正有理数公式 |

这里$d$是基图阶数，$m$是块阶数，$N=dm$才是最终竞赛图阶数。
取内部块极限时始终固定$d$。这些结论针对随机模型的期望，
未由此证明猜想3的全体竞赛图精确Hamilton极值，也没有交换两重极限。

### 专家阅读入口

建议从[论文](docs/paper.zh.md)开头的原猜想对应和阅读路线开始。
第一部分第1–7节使用有限维线性代数和求导计算Hessian；
第8节引用Wormald的Theorem 1、4、5，将有限恒等式连接到模型常数。
第二部分使用Fang–Huang推论3.4进行矩比较，并用Brégman永久式界
单独处理非正则基图。第三部分展开行列式闭式、等号分类、路径增点、
归一化及共同阈值的计算。

[基础讲解](docs/elementary-guide.zh.md)以基本微积分和线性代数为起点，
保留完整乘积求导，并提供三顶点例子的逐项手算。

论文目前为AI辅助完成的预印本，等待外部专家独立审阅。
[复核记录](AUDIT.md)区分精确有限核查与高精度数值诊断。
本仓库尚无这些结果的Lean形式化证明，也不主张历史优先权。

### 复现核验

使用Python 3.10或更新版本。数学核查仅依赖Python标准库。
从仓库根目录运行：

    python verification/verify_wormald_hessian_spectral_bridge.py
    python verification/verify_wormald_fixed_base_extremum.py
    python verification/audit_publication_identities.py
    python tools/check_package.py

数学核查覆盖11,724个精确Hessian元素、345个不同消去坐标的Hessian行列式、
三、五、七阶全部2,666个有标号正则竞赛图，以及有限随机吹胀期望和
加权永久式界。[保存的记录](verification/qa/)列出各项范围。
有限检查用于发现错误；一般结论依靠逐式证明及文中明确引用的外部定理。

PDF由Markdown主稿经Pandoc和Tectonic或XeLaTeX生成，
可复现方法见[PDF构建程序](tools/build_pdf.py)。
共42页已全部渲染并逐页检查；[版面记录](verification/qa/pdf_review.json)
将排版审查与数学核验分别记录。

### 仓库结构

| 位置 | 内容 |
| --- | --- |
| [docs/](docs/) | Markdown论文与基础讲解 |
| [output/pdf/](output/pdf/) | PDF阅读稿 |
| [verification/](verification/) | 精确算术核查与辅助程序 |
| [verification/qa/](verification/qa/) | 数学核查记录及PDF版面记录 |
| [tools/](tools/) | PDF构建与公开包校验工具 |
| [AUDIT.md](AUDIT.md) | 审阅范围、证明依赖和修订记录 |
| [MANIFEST.json](MANIFEST.json) | 当前公开文件的内容哈希 |

### 引用与文献

引用本研究稿时，请使用：

> Liu, Xingchen. *Wormald tournament conjectures: Hessians and random blow-ups*.
> Research draft, version 0.1.1, 2026.
> https://github.com/LStar404/wormald-tournament-conjectures.

机器可读引用信息见[CITATION.cff](CITATION.cff)。
[此前的哈密顿路仓库](https://github.com/LStar404/tournament-hamiltonian-paths)
属于相关工作；其作者信息与形式化核验记录适用于原项目。

1. N. C. Wormald，
   [*Tournaments with many Hamilton cycles*，arXiv:2610.16245v1](https://arxiv.org/html/2610.16245v1)：
   本稿讨论的模型、计数定理及原猜想来源。
2. Yijia Fang、Hao Huang，
   [*Maximizing directed cycles in tournaments*，推论3.4](https://arxiv.org/html/2608.06238v1#S3)：
   矩比较所用的弱主序输入。
3. Noga Alon，
   [*The maximum number of Hamiltonian paths in tournaments*](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf)，
   Combinatorica 10 (1990)，319–324：文中列出的Brégman界。

