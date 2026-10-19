# Wormald tournament conjectures: Hessians and random blow-ups

Research notes by **刘星辰、叶祥宇**, 19 October 2026.

This repository presents proof drafts addressing Conjectures **1, 2 and 6**
in N. C. Wormald's *Tournaments with many Hamilton cycles*,
[arXiv:2610.16245v1](https://arxiv.org/html/2610.16245v1).
The conjectures are Wormald's; this repository is not an official edition of his paper.

The manuscript derives an exact Hessian identity, a closed form and monotone
limit for the carousel model constants, and the eventual unique maximizer of
expected Hamilton counts among blow-ups of a **fixed odd-order base tournament**.
The model conclusions use Wormald's counting theorems and the explicitly cited
Fang–Huang matrix comparison.

**Status:** AI-assisted research draft, reviewed within the project and checked by
exact finite computations. Independent mathematical review is still needed.
No historical priority claim or formal certification is made.
This does **not** establish the global exact Hamilton extremum in Conjecture 3.
The base order and the block order are different parameters; their limits are
not interchanged.

## Read / 阅读

- [完整证明 PDF，22页](output/pdf/wormald-conjectures-proof.zh.pdf)
- [大一基础讲解 PDF，20页](output/pdf/wormald-conjectures-guide.zh.pdf)
- [完整证明 Markdown](docs/paper.zh.md)
- [基础讲解 Markdown](docs/elementary-guide.zh.md)
- [复核报告及适用范围](AUDIT.md)

原文对应关系已重新核对：猜想1是固定基图阶数下的随机吹胀期望极值，
猜想2是正则内部块圆环模型常数的极限，猜想6是Hessian非退化及有理平方性质。
稿件保留逐步推导，并补充四顶点等号分类、行列式闭式及增点归一化的计算。

## Reproduce the finite checks

Python 3.10 or newer; the checks use only the standard library.

    python verification/verify_wormald_hessian_spectral_bridge.py
    python verification/verify_wormald_fixed_base_extremum.py
    python verification/audit_publication_identities.py

Results are written to verification/qa/. The first two scripts check exact
Hessian entries and determinants, all labelled regular bases of orders 3, 5, 7,
finite random blow-up expectations, and weighted permanent bounds.
The additional audit checks the expanded elementary calculations.
High-precision asymptotic diagnostics are distinguished from exact checks.
Finite checks do not prove the general asymptotic statements.

## Build the PDFs

The Markdown sources and a LaTeX template are included. Install Pandoc,
Tectonic or XeLaTeX, and suitable Chinese fonts; see tools/build_pdf.py.
The supplied PDFs were rendered and visually inspected before publication.

## Sources and attribution

1. N. C. Wormald,
   [*Tournaments with many Hamilton cycles*](https://arxiv.org/html/2610.16245v1).
   Definitions, Theorems 1/4/5, and Conjectures 1/2/6.
   The [author's historical note](https://arxiv.org/abs/2610.16245)
   identifies this as older research uploaded in 2026.
2. Yijia Fang and Hao Huang,
   [*Maximizing directed cycles in tournaments*, Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3).
3. Noga Alon,
   [*The maximum number of Hamiltonian paths in tournaments*](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf),
   Combinatorica 10 (1990), 319-324; the stated Brégman bound.

The upstream papers are linked, not redistributed. New claims are restricted to
the scope stated in the manuscript and remain open to correction.

