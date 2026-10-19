# Wormald's Tournament Conjectures 1, 2 and 6: Hessian Identities and Random Block Models

Xingchen Liu

19 October 2026. Public research manuscript, version 0.2.3.

# Abstract

We study three specific questions in Wormald's random blow-up models. We express the logarithmic angular Hessian defined in that paper as a compression of a finite matrix, prove its positive definiteness, and identify the model's asymptotic constant with a determinant ratio. For a carousel base tournament, this ratio has a closed form. After multiplication by the factor for regular internal blocks, the resulting constant increases strictly to $\cosh(1)/\cos(1)$ and admits an explicit expansion in inverse powers of the base order. Combining the explicitly cited moment comparison of Fang and Huang with Wormald's model counting theorems, and treating nonregular bases separately, yields the unique maximizer of the expectations when the odd base order is fixed and the blocks are sufficiently large.

This is a proof manuscript addressing Conjectures 1, 2 and 6 in [Wormald's public version](https://arxiv.org/html/2610.16245v1). The derivations and programs were developed with AI assistance and checked equation by equation and by exact finite computations. Independent mathematical review by the author and other researchers remains necessary; no formal certification is claimed. We make no claim of historical priority. Statements about these models do not establish exact Hamiltonian extremal theorems for all tournaments.

# Correspondence with the original conjectures and notation

The original conjectures are due to N. C. Wormald. We use the fixed version arXiv:2610.16245v1, uploaded on 12 October 2026. Its author explains that the paper comes from earlier research; these questions were not first proposed in 2026. The following restatements use the notation of this manuscript.

Fix an odd integer $d\ge3$. The base tournament $T^*$ has $d$ vertices, each replaced by $m$ vertices, giving total order $N=dm$. Directions between blocks are determined by $T^*$. In $\mathcal T(T^*,m)$ the internal blocks are independent uniform random tournaments. In $\mathcal R(T^*,m)$ each internal block is additionally regular, requiring $m$ to be odd. Let $C(G)$ and $H(G)$ denote the numbers of Hamiltonian cycles and paths, respectively.

- Conjecture 1: for fixed $d$ and sufficiently large $m$, among bases of order $d$ the carousel maximizes $\mathbb E C(\mathcal T(T^*,m))$. Part II proves this assertion and gives uniqueness, a path counterpart, and a counterpart with regular internal blocks.
- Conjecture 2: the limiting constant for a carousel base with regular internal blocks converges as odd $d\to\infty$. Part I identifies the limit and proves strict monotonicity and an error expansion.
- Conjecture 6: for each regular base of order at least three, the original Hessian determinant $\mathcal H$ is nonzero and $d/\mathcal H$ is a rational square. Part I gives exact formulas.

The original Conjecture 3 concerns the exact cycle extremum among all tournaments of sufficiently large odd order. It lies outside this manuscript. We also do not claim to prove the global statements of the original Conjectures 4 and 5.

# Reading route and external inputs

Sections 1–7 of Part I use finite dimensional linear algebra and differentiation. Section 8 invokes Wormald's Theorems 1, 4 and 5 to connect the finite Hessian with asymptotic expectations in the random models. Sections 9–11 compute the carousel closed form and its expansion.

Section 3 of Part II uses Fang–Huang's Corollary 3.4. The equality classification for the fourth moment can also be checked directly through the four-vertex calculation in Appendix A.3. Section 8 of Part II uses Brégman's permanent bound for zero–one matrices. Nonregular bases are treated separately, so the regular Hessian formula is never applied outside its hypotheses.

Part III supplies the calculations expanded during the prepublication review: the determinant polynomial, the carousel isomorphism, fourth-moment equality, every normalization term in the added-vertex argument for paths, and the choice of a common finite threshold. A separate elementary guide is provided in Chinese.

Every limit $m\to\infty$ in this manuscript fixes $d$ first. The subsequent discussion of model constants as $d\to\infty$ does not interchange limits and does not give a uniform second-order error in the final order $N$.

# Terminology and notation

A tournament orients every pair of distinct vertices in exactly one direction. Its adjacency entry in position $i,j$ is 1 exactly when $i\to j$, and the diagonal is zero. In a regular tournament each vertex has outdegree and indegree $(d-1)/2$.

Hamiltonian paths are counted as directed vertex orderings. Hamiltonian cycles are identified up to cyclic starting point: rotating the starting point does not produce another cycle, and reversal is not an additional identification of directed orderings. An ordinary isomorphism is a vertex bijection preserving all edge directions. Every uniqueness assertion in this manuscript uses this notion.

For odd order, the carousel tournament $\mathrm{Car}_d$ is defined by

$$
V(\mathrm{Car}_d)=\mathbb Z/d\mathbb Z,\qquad
i\to j\ \Longleftrightarrow\
(j-i)\bmod d\in\{1,\ldots,(d-1)/2\}.
$$

Write $I_r$ for the identity matrix of order $r$, $J_r$ for the all-one matrix of order $r$, $\mathbf1_r$ for the all-one column vector, and $e_j$ for the $j$th standard basis column vector. The symbol $\delta_{jk}$ is 1 when $j=k$ and 0 otherwise. Matrix subscripts may be omitted when multiplication determines their dimensions. Superscript $T$ denotes transpose, and the imaginary unit satisfies $i^2=-1$. On positive real numbers, $\log$ is the natural logarithm; in complex neighborhoods we use the analytic branches specified below.

For a real matrix $M$, the two norms are

$$
\|M\|_F^2=\sum_{j,k}M_{jk}^2,\qquad
\|M\|_{\rm op}=\sup_{v\ne0}\frac{\|Mv\|_2}{\|v\|_2}.
$$

Write $[d]=\{1,\ldots,d\}$. The principal submatrix $M[U]$ uses the rows and columns in $U$, with convention $\det M[\varnothing]=1$. The space $u^\perp$ is orthogonal to the real vector $u$. The notation $\det_{u^\perp}$ means the determinant of the restriction to this invariant subspace, computed in an orthonormal basis.

On a graph, $C(G),H(G)$ count cycles and paths. In contrast, the standalone $C=S/d$ is a matrix, bold $\mathbf H$ is the Hessian matrix, and $\mathcal H$ is its determinant. Local symbols in different sections are interpreted according to the definitions given in those sections.

We also fix the conventions for operations and differentiation. For a real vector $v=(v_1,\ldots,v_r)^T$, its Euclidean norm is $\|v\|_2=(\sum_{j=1}^r v_j^2)^{1/2}$; an unsubscripted vector norm $\|s\|$ has this meaning too. Write $\operatorname{tr}M=\sum_jM_{jj}$. The matrix $\operatorname{diag}(a_1,\ldots,a_r)$ has the listed scalars on the diagonal and zero elsewhere. The notation $M\succ0$ means that $M$ is real symmetric and, for every nonzero real vector $v$, we have $v^TMv>0$. Lowercase letters may denote entries, for example $s_{ij}=S_{ij}$.

For a scalar function $F(t_1,\ldots,t_d)$, subscripts $F_j,F_{jk}$ denote $\partial F/\partial t_j$ and $\partial^2F/(\partial t_j\partial t_k)$; matrix, row and column derivatives are taken entry by entry. When differentiating in the original variables $y$, we write $K_{y_j}$. The matrix $\nabla^2F$ consists of the entries $F_{jk}$. A prime on a function of one variable denotes differentiation in its argument. The notations $y'=(y_1,\ldots,y_{d-1})$ and $t'=(t_1,\ldots,t_{d-1})$ delete the last coordinate; those primes do not denote derivatives. A vertex of type $j$ belongs to the block replacing base vertex $j$, which contains $m$ vertices.

Write $\lfloor a\rfloor$ for the largest integer at most $a$ and $\lceil a\rceil$ for the smallest integer at least $a$. For a finite set, $\#U=|U|$ is its cardinality. The scalar indicator $\mathbf1_{\mathcal E}$ is 1 when condition $\mathcal E$ holds and 0 otherwise; it differs from the all-one vector $\mathbf1$ without a condition subscript. Set $0!=1$ and $n!=1\cdot2\cdots n$; also $\binom nk=n!/(k!(n-k)!)$, with value 0 for $k>n$.

In the expansions here, $R(x)=O(x^k)$ means that constants $M,\eta>0$ exist such that, whenever $0<|x|<\eta$, we have $|R(x)|\le M|x|^k$. The notation $O(d^{-k})$ concerns $d\to\infty$, with other parameters fixed. A subscript in $O_d$ permits dependence on the fixed parameter $d$. Finite sums or uniformly convergent power series control the remainders below; a numerical fit is not a proof of this definition.

For a square matrix $D$, the adjugate $\operatorname{adj}D$ is the transpose of the cofactor matrix: $(\operatorname{adj}D)_{ij}=(-1)^{i+j}\det D^{(j|i)}$, where $D^{(j|i)}$ deletes row $j$ and column $i$. Determinant expansion gives $D\operatorname{adj}D=(\det D)I$. When $\det D\ne0$, division by this determinant gives the inverse formula used below.

# Part I: The exact Hessian and the model constants

## 1. Objects, main formulas and scope

Let $d\ge3$ be odd and let $A$ be the adjacency matrix of a regular tournament of order $d$.

$$
S=2A+I-J,\quad S^T=-S,\quad S1=0,\qquad
C=S/d,\quad P_0=J/d.
$$

Set

$$
B(y)=I-(A+\tfrac12I)\operatorname{diag}(y_1,\ldots,y_d),
\quad K(y)=\det B(y),\quad z=2/d.
$$

Near $y=z1$, Wormald solves $K(y)=0$ for $y_d=h(y_1,\ldots,y_{d-1})$ and takes the Hessian of

$$
\widetilde f(\theta)=\log h(ze^{i\theta_1},\ldots,ze^{i\theta_{d-1}})
$$

Evaluate the Hessian at $\theta=0$. Denote its matrix by $\mathbf H$ and its determinant by $\mathcal H$. Sections 4–6 verify the conditions needed to define $h$ and the logarithm branch, so this definition does not assume an existence statement still to be proved. We prove

$$
\boxed{
\mathbf H=E^T(I+C^2)(I-C^2)^{-1}E,\qquad
E=(e_1-e_d,\ldots,e_{d-1}-e_d).}
$$

Consequently,

$$
\boxed{
\mathcal H
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0,\qquad
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}=:\rho_d(S).}
$$

The right-hand side is positive and rational. This gives a general proof manuscript for Conjecture 6 in the cited version, rather than a check of selected bases. This finite matrix argument does not use permanent asymptotics, local balancing, or prior global extremal assertions from the earlier research.

## 2. Spectral gap, the constant direction and restricted determinants

Throughout, $\mathbf1$ is the all-one column vector; a nonbold $1$ multiplied by a matrix also means this vector. The tournament definition and regularity give

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

The matrix $S$ has $d(d-1)$ off-diagonal entries, all equal to $\pm1$. Thus

$$
\|S\|_F^2=\sum_{i\ne j}s_{ij}^2=d(d-1),
\qquad \|C\|_F^2=\frac{d-1}{d}.
$$

Apply a real orthogonal basis change to the normalized skew-symmetric matrix $C$. Its canonical form consists of zero blocks and two-dimensional blocks

$$
J_\lambda=\begin{pmatrix}0&\lambda\\-\lambda&0\end{pmatrix}
$$

Each two-dimensional block contributes $2\lambda^2$ to the squared Frobenius norm. Therefore every frequency satisfies

$$
2\lambda^2\le\sum_{\text{all two-dimensional blocks}}2\lambda_j^2
=\|C\|_F^2=\frac{d-1}{d},
$$

$$
\|C\|_{\rm op}^2=\max_j\lambda_j^2
\le\frac{d-1}{2d}<\frac12.
$$

Put $u=\mathbf1/\sqrt d$, $P_0=uu^T=J/d$ and $\Pi=I-P_0$. Direct multiplication gives

$$
u^Tu=1,\quad P_0^2=P_0,\quad
\Pi^2=I-2P_0+P_0^2=\Pi,
$$

$$
Cu=0,\qquad u^TC=-(Cu)^T=0,
\qquad CP_0=(Cu)u^T=0,\quad P_0C=u(u^TC)=0.
$$

We also have

$$
P:=\frac{2A+I}{d}=P_0+C,\qquad
Pu=P_0u+Cu=u.
$$

If $u^Tv=0$, then $P_0v=u(u^Tv)=0$, and hence $Pv=Cv$. At the critical point,

$$
B(z\mathbf1)=I-P=\Pi-C,\qquad
B(z\mathbf1)u=0.
$$

On $u^\perp$ this matrix is $I-C$. If $x\in u^\perp$ satisfies $(I-C)x=0$, then

$$
0=x^T(I-C)x=\|x\|_2^2-x^TCx=\|x\|_2^2,
$$

Here $x^TCx=-x^TCx$ implies $x^TCx=0$. Thus $x=0$, and the restricted matrix is invertible.

On a two-dimensional block,

$$
\det(I-J_\lambda)
=\det\begin{pmatrix}1&-\lambda\\\lambda&1\end{pmatrix}
=1+\lambda^2>0.
$$

The eigenvalue of $I-C$ in the constant direction is 1. Therefore

$$
q:=\det_{u^\perp}(I-C)
=\det(I-C)
=\prod_j(1+\lambda_j^2)>0.
$$

Taking transposes gives

$$
\det(I+C)=\det((I+C)^T)=\det(I-C)=q.
$$

## 3. Logarithmic variables, block matrices and Schur elimination

In this part $1\le j,k\le d$ until Section 6 eliminates the last coordinate and restricts them to $1\le j,k\le d-1$. Take $t=(t_1,\ldots,t_d)\in\mathbb C^d$ near the origin and write $y=(y_1,\ldots,y_d)$. The angular variables are $\theta=(\theta_1,\ldots,\theta_{d-1})\in\mathbb R^{d-1}$. Set $y_j=ze^{t_j}$. Then

$$
\mathscr B(t)=B(ze^{t_1},\ldots,ze^{t_d})
=I-P\operatorname{diag}(e^{t_1},\ldots,e^{t_d}).
$$

Choose an orthonormal basis of $u^\perp$ as the columns of $V$. The matrix $O=(u,V)$ satisfies

$$
V^TV=I_{d-1},\quad V^Tu=0,\quad VV^T=\Pi,
\quad O^TO=OO^T=I_d.
$$

In this basis write

$$
O^T\mathscr B(t)O=
\begin{pmatrix}a(t)&b(t)\\c(t)&D(t)\end{pmatrix},
$$

$$
a=u^T\mathscr Bu,\quad b=u^T\mathscr BV,\quad
c=V^T\mathscr Bu,\quad D=V^T\mathscr BV.
$$

Here $a$ is a scalar, $b$ is a row of size $1\times(d-1)$, $c$ is a column of size $(d-1)\times1$, and $D$ is square of order $(d-1)$. The derivatives below also use the left constant-vector relation, which follows from skew symmetry as

$$
u^TP=u^T(P_0+C)=u^Tuu^T+u^TC=u^T+0=u^T.
$$

Since $\det(O)^2=1$, this basis change preserves the determinant. At $t=0$,

$$
a(0)=0,\quad b(0)=0,\quad c(0)=0,
\qquad D(0)=V^T(I-C)V.
$$

Section 2 proves that $D(0)$ is invertible and that $\det D(0)=q>0$. Continuity of the determinant gives a neighborhood of the origin in which $\det D(t)\ne0$. The inverse formula

$$
D(t)^{-1}=\frac{\operatorname{adj}D(t)}{\det D(t)}
$$

shows that every entry of the inverse is analytic on this neighborhood.

The actual block elimination is

$$
\begin{pmatrix}1&-bD^{-1}\\0&I\end{pmatrix}
\begin{pmatrix}a&b\\c&D\end{pmatrix}
=
\begin{pmatrix}a-bD^{-1}c&0\\c&D\end{pmatrix}.
$$

The left multiplier has determinant 1, and the resulting matrix is block triangular. Defining

$$
\psi(t)=a(t)-b(t)D(t)^{-1}c(t)
$$

therefore gives the exact identity

$$
\det\mathscr B(t)=\det D(t)\,\psi(t).
$$

On this neighborhood, $\det\mathscr B(t)=0$ and $\psi(t)=0$ are equivalent because the factor $\det D(t)$ is nonzero.

## 4. First and second derivatives: all nine product terms

Write $F_j=e_je_j^T$ and $R(t)=D(t)^{-1}$. Only column $j$ of the exponential matrix depends on $t_j$, so at the origin

$$
\mathscr B_j=-PF_j,\qquad
\mathscr B_{jk}=-\delta_{jk}PF_j.
$$

To make the inverse derivatives explicit, differentiate $DR=I$ once and then again:

$$
D_jR+DR_j=0,\qquad R_j=-RD_jR,
$$

$$
R_{jk}=RD_kRD_jR-RD_{jk}R+RD_jRD_kR.
$$

These identities hold in the neighborhood where $\det D\ne0$. The symbols $R_j,R_{jk}$ in the nine terms below denote these derivatives.

Using $u^TP=u^T$ and $e_j^Tu=1/\sqrt d$,

$$
a_j(0)=-u^TPF_ju=-u_j^2=-1/d,
\qquad a_{jk}(0)=-\delta_{jk}/d.
$$

First list every term of the first product derivative:

$$
\partial_j(bRc)=b_jRc+bR_jc+bRc_j.
$$

Differentiating with respect to $t_k$ gives all nine terms:

$$
\begin{aligned}
\partial_k\partial_j(bRc)
={}&b_{jk}Rc+b_jR_kc+b_jRc_k\\
&+b_kR_jc+bR_{jk}c+bR_jc_k\\
&+b_kRc_j+bR_kc_j+bRc_{jk}.
\end{aligned}
$$

At the origin $b=c=0$. Terms 1, 2, 4, 5, 6, 8 and 9 contain a factor $b$ or $c$ and hence vanish there. The two surviving terms are

$$
\partial_k\partial_j(bRc)(0)=b_j(0)R(0)c_k(0)+b_k(0)R(0)c_j(0).
$$

We now calculate these factors:

$$
b_j(0)=-u^TPe_je_j^TV
=-\frac1{\sqrt d}e_j^TV,
$$

$$
c_k(0)=-V^TPe_ke_k^Tu
=-\frac1{\sqrt d}V^TCe_k,
$$

Here $V^TP=V^TC$ follows from $V^Tu=0$. Set $U=(I-C)^{-1}$. The matrix $C$ preserves $u^\perp$, and $D(0)=V^T(I-C)V$ gives the identities below. Multiply the first on the left by $U$ and on the right by $R(0)$ to obtain the second; the next line uses $\Pi C=C$:

$$
(I-C)V=VD(0),\qquad UV=VR(0),
$$

$$
UC=U\Pi C=UVV^TC=VR(0)V^TC.
$$

Consequently,

$$
VR(0)V^TC=UC.
$$

The two second-order products are therefore

$$
b_jR(0)c_k=\frac1d e_j^TUC e_k=\frac{(UC)_{jk}}d,
$$

$$
b_kR(0)c_j=\frac1d e_k^TUC e_j=\frac{(UC)_{kj}}d.
$$

The first derivative of the product vanishes at the origin. Thus

$$
\psi_j(0)=-1/d,\qquad
\psi_{jk}(0)=-\frac{\delta_{jk}+(UC)_{jk}+(UC)_{kj}}d.
$$

From $C(I-C)=(I-C)C$, multiplying on the left and right by the inverse gives $CU=UC$. Also,

$$
(UC)^T=C^TU^T=-C(I+C)^{-1}.
$$

The difference of the two inverses expands as

$$
\begin{aligned}
(I-C)^{-1}-(I+C)^{-1}
&=(I-C)^{-1}[(I+C)-(I-C)](I+C)^{-1}\\
&=2C(I-C)^{-1}(I+C)^{-1}\\
&=2C(I-C^2)^{-1}.
\end{aligned}
$$

It follows that

$$
\begin{aligned}
I+UC+(UC)^T
&=I+C[(I-C)^{-1}-(I+C)^{-1}]\\
&=I+2C^2(I-C^2)^{-1}\\
&=(I+C^2)(I-C^2)^{-1}=:Q.
\end{aligned}
$$

We have obtained the full derivative formulas

$$
\boxed{\psi_j(0)=-1/d,\qquad
\nabla^2\psi(0)=-Q/d.}
$$

Differentiate the determinant product. Since $\psi(0)=0$ and $\det D(0)=q$,

$$
\begin{aligned}
\partial_{t_j}\det\mathscr B(0)
&=\partial_{t_j}(\det D)(0)\,\psi(0)+\det D(0)\psi_j(0)\\
&=0+q(-1/d)=-q/d.
\end{aligned}
$$

At the origin $\partial y_j/\partial t_j=z$, so

$$
zK_{y_j}(z\mathbf1)=-q/d,\qquad
K_{y_j}(z\mathbf1)=-\frac{q}{dz}=-q/2\ne0.
$$

This supplies the nonzero partial derivative needed for every choice of eliminated coordinate.

## 5. Eliminating the last variable by an explicit rational function

The determinant is linear in column $d$, and this column is affine in $y_d$. Hence

$$
K(y)=K_0(y_1,\ldots,y_{d-1})
+y_dK_1(y_1,\ldots,y_{d-1}).
$$

The two coefficients have the explicit definitions

$$
K_0(y')=K(y',0),\qquad
K_1(y')=K(y',1)-K(y',0)=K_{y_d}(y',y_d).
$$

The last partial derivative does not depend on $y_d$, because the displayed expression is affine in $y_d$.

The derivative calculation in Section 4 gives

$$
K_1(z,\ldots,z)=K_{y_d}(z\mathbf1)=-q/2\ne0.
$$

Shrink the neighborhood so that $K_1(y')\ne0$. We can then write explicitly

$$
h(y')=-\frac{K_0(y')}{K_1(y')}.
$$

Since $K(z\mathbf1)=0$,

$$
K_0(z,\ldots,z)+zK_1(z,\ldots,z)=0,
\qquad h(z,\ldots,z)=z.
$$

Define

$$
g(t')=\log\!\left[
\frac{h(ze^{t_1},\ldots,ze^{t_{d-1}})}z\right].
$$

At the origin the logarithm's argument is 1. Continuity of $h$, together with $h(z,\ldots,z)=z>0$, lets us shrink the neighborhood so that $|h(ze^{t'})/z-1|<1/2$, where $ze^{t'}$ means coordinatewise exponentiation. This disk excludes 0. Choose its analytic logarithm branch with value 0 at 1. Then

$$
g(0)=\log1=0,\qquad
t_d=g(t'),\qquad \psi(t',g(t'))=0.
$$

We differentiate only this composition of an explicit rational function and an analytic logarithm; existence of an implicit function is not an additional assumption.

## 6. The complete chain rule and the angular sign

Here $j,k\in\{1,\ldots,d-1\}$. The chain rule holds first in the surface neighborhood. The derivative values calculated in Section 4 are substituted only at $t'=0,\ t_d=g(0)=0$. In particular, $g_j(0)=-1$ is not an identity throughout that neighborhood. For $j\le d-1$, take one derivative:

$$
0=\psi_j+\psi_dg_j,\qquad
g_j(0)=-\frac{\psi_j(0)}{\psi_d(0)}
=-\frac{-1/d}{-1/d}=-1.
$$

Differentiating again with respect to $t_k$ gives five terms:

$$
0=\psi_{jk}+\psi_{jd}g_k+\psi_{dk}g_j
+\psi_{dd}g_jg_k+\psi_dg_{jk}.
$$

Substitute the derivatives from Section 4 and $g_j=g_k=-1$ term by term:

$$
0=-\frac{Q_{jk}}d+\frac{Q_{jd}}d
+\frac{Q_{dk}}d-\frac{Q_{dd}}d-\frac{g_{jk}}d.
$$

Multiply by $d$ and isolate the last derivative:

$$
\begin{aligned}
g_{jk}(0)
&=-Q_{jk}+Q_{jd}+Q_{dk}-Q_{dd}\\
&=-(e_j-e_d)^TQ(e_k-e_d).
\end{aligned}
$$

Choose the same local branch for the original $\log h$; when $h=z$, take the real value $\log z$. By the definition of $g$ in Section 5, the original angular function satisfies

$$
\widetilde f(\theta)=\log z+g(i\theta_1,\ldots,i\theta_{d-1}).
$$

Its first angular derivative is $i g_j(i\theta)$ and its second angular derivative is $i^2g_{jk}(i\theta)$. Therefore

$$
\mathbf H_{jk}
=i^2g_{jk}(0)=-g_{jk}(0)
=(e_j-e_d)^TQ(e_k-e_d),
$$

$$
\boxed{\mathbf H=E^TQE.}
$$

## 7. Positive definiteness, the basis-change factor and the rational square

On each two-dimensional block from Section 2, $J_\lambda^2=-\lambda^2I_2$. Therefore

$$
(I+J_\lambda^2)(I-J_\lambda^2)^{-1}
=\frac{1-\lambda^2}{1+\lambda^2}I_2.
$$

The coefficient is positive because $\lambda^2<1/2$. On zero blocks, $Q$ is the identity, so $Q\succ0$. For $v\in\mathbb R^{d-1}$,

$$
Ev=(v_1,\ldots,v_{d-1},-\textstyle\sum_{j=1}^{d-1}v_j)^T.
$$

If $v\ne0$, its first $d-1$ components are not all zero, so $Ev\ne0$. Consequently,

$$
v^T\mathbf Hv=(Ev)^TQ(Ev)>0.
$$

We next retain the volume factor of the basis change. For $E$, the inner product of columns $j,k$ is

$$
(e_j-e_d)^T(e_k-e_d)=\delta_{jk}+1.
$$

Thus $E^TE=I_{d-1}+J_{d-1}$. Its eigenvalue in the all-one direction is $1+(d-1)=d$; each direction orthogonal to the all-one vector has eigenvalue 1. Therefore

$$
\det(E^TE)=d\cdot1^{d-2}=d.
$$

Write $E=VL$, where $V$ is an orthonormal basis of $u^\perp$ and $L$ is invertible:

$$
E^TQE=L^T(V^TQV)L,\qquad
E^TE=L^TL.
$$

Taking determinants gives, respectively,

$$
\det(E^TQE)=\det(L)^2\det(V^TQV),\qquad
\det(L)^2=d.
$$

Using $Cu=0$,

$$
Qu=(I+C^2)(I-C^2)^{-1}u=u.
$$

In the real orthogonal basis of Section 2, every block of $Q$ is a real scalar multiple of the identity. Thus $Q$ is real symmetric, and $u^TQV=(Qu)^TV=u^TV=0$. Hence

$$
(u,V)^TQ(u,V)=
\begin{pmatrix}1&0\\0&V^TQV\end{pmatrix},
\qquad \det Q=\det(V^TQV).
$$

Restore the two determinant factors:

$$
\mathcal H=d\det Q
=d\,\frac{\det(I+C^2)}{\det(I-C^2)}>0.
$$

Matrix multiplication and transposition give

$$
(I+iC)(I-iC)=I+C^2,\qquad
\det(I-iC)=\det((I-iC)^T)=\det(I+iC),
$$

$$
(I+C)(I-C)=I-C^2,\qquad \det(I-C)=\det(I+C).
$$

Therefore

$$
\det(I+C^2)=\det(I+iC)^2,\qquad
\det(I-C^2)=\det(I+C)^2.
$$

The sign of the square root is also fixed block by block:

$$
\det(I+J_\lambda)=1+\lambda^2>0,\qquad
\det(I+iJ_\lambda)=1-\lambda^2>0.
$$

Thus

$$
\sqrt{\frac d{\mathcal H}}
=\frac{\det(I+C)}{\det(I+iC)}>0.
$$

Finally, prove rationality. Expand the determinant multilinearly, choosing either an identity column or a column of $C$:

$$
\det(I+tC)=\sum_{U\subseteq[d]}t^{|U|}\det C[U].
$$

For an odd-order matrix $r=|U|$,

$$
\det C[U]=\det(C[U]^T)=\det(-C[U])
=(-1)^r\det C[U]=-\det C[U],
$$

Thus this principal determinant is zero. Since $C$ has rational entries,

$$
\det(I+iC)
=\sum_{k=0}^{\lfloor d/2\rfloor}\sum_{\substack{U\subseteq[d]\\|U|=2k}}
(-1)^k\det C[U]\in\mathbb Q.
$$

The number $\det(I+C)$ is rational as well. We have already shown that numerator and denominator are positive, so their ratio is a positive rational number.

## 8. External counting theorems and the four limits

This section explicitly invokes Wormald's Theorems 1, 4 and 5; it does not claim to reprove their random counting arguments. Fix a regular base of order $d$, internal block order $m$ and total order $N=dm$. Subscripts $\mathcal T,\mathcal R$ specify the random model; for example, $\mathbb EC_{\mathcal T}$ is the expected cycle count of a random graph drawn from $\mathcal T(T^*,m)$. The path notation has the corresponding meaning. Blocks are independent and uniform over all admissible labeled internal tournaments. Define

$$
\nu_N=\frac{(N-1)!}{2^N},\qquad
\mu_N=\frac{N!}{2^{N-1}}.
$$

When $\mathcal H\ne0$, Wormald's Theorem 4 gives

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N}
\longrightarrow\sqrt{d/\mathcal H}.
$$

Section 7 establishes $\mathcal H>0$ and the positive branch of its square root. Substitution gives

$$
\lim_{m\to\infty}\frac{\mathbb EC_{\mathcal T}}{\nu_N}
=\sqrt{\frac d{d\det(I+C^2)/\det(I-C^2)}}
=\rho_d(S).
$$

Theorem 5 replaces cycle counts in Theorem 4 by path counts. Thus

$$
\lim_{m\to\infty}\frac{\mathbb EH_{\mathcal T}}{\mu_N}
=\sqrt{d/\mathcal H}=\rho_d(S).
$$

Theorem 1 gives the expectation ratio between regular internal blocks and independent random internal blocks:

$$
\frac{\mathbb EC_{\mathcal R}}{\mathbb EC_{\mathcal T}}
\longrightarrow e^{1/d}.
$$

For sufficiently large $m$ the denominator is positive, because its normalized limit is $\rho_d(S)>0$. Multiplication gives

$$
\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\left(\frac{\mathbb EC_{\mathcal R}}{\mathbb EC_{\mathcal T}}
\frac{\mathbb EC_{\mathcal T}}{\nu_N}\right)
=e^{1/d}\rho_d(S).
$$

Theorem 5 also replaces the counts in Theorem 1 by path counts, giving

$$
\frac{\mathbb EH_{\mathcal R}}{\mathbb EH_{\mathcal T}}
\longrightarrow e^{1/d}.
$$

The fourth limit is therefore

$$
\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\left(\frac{\mathbb EH_{\mathcal R}}{\mathbb EH_{\mathcal T}}
\frac{\mathbb EH_{\mathcal T}}{\mu_N}\right)
=e^{1/d}\rho_d(S).
$$

All four limits fix $d$. The last two take only admissible odd $m$ and do not involve simultaneous growth of $d$ and $m$.

## 9. A complete closed form for the carousel base

Let $T_d$ have entries 1 above the diagonal, $-1$ below it and 0 on it. Appendix A.2 gives the signed permutation similarity between a carousel sign matrix and $T_d$. Appendix A.1 proves the determinant closed form and then uses its highest-degree coefficient to show that every even principal determinant is 1 and every odd principal determinant is 0. Hence

$$
\det(I+tT_d)=\frac{(1+t)^d+(1-t)^d}{2}.
$$

When a graph name is used as the argument of $\rho_d$ below, it denotes that graph's sign matrix. Ordinary relabeling preserves the determinants, so the value does not depend on vertex labels. Consequently,

$$
\boxed{
\rho_d(\mathrm{Car}_d)
=\frac{(1+1/d)^d+(1-1/d)^d}
{(1+i/d)^d+(1-i/d)^d}.}
$$

This directly recovers $2,44/19,3032/1231,\ldots$ in the original table, without calculating a multivariate Hessian separately for each example. The constant for regular internal blocks is

$$
\mathfrak r_d=e^{1/d}r_d,\qquad r_d:=\rho_d(\mathrm{Car}_d).
$$

## 10. Real-function form and strict monotonicity

The functions used here and in the Taylor calculation are defined by the following formulas; $\sec$ is used only where the cosine is nonzero.

$$
\cosh y=\frac{e^y+e^{-y}}2,\quad
\sinh y=\frac{e^y-e^{-y}}2,\quad
\tanh y=\frac{\sinh y}{\cosh y},\quad
\operatorname{sech}y=\frac1{\cosh y},\quad
\sec y=\frac1{\cos y}.
$$

Set $x=1/d$ and define on $0<x\le1/3$

$$
\alpha(x)=\frac{\arctan x}{x},\qquad
\beta(x)=\frac{\operatorname{artanh}x}{x},\qquad
\operatorname{artanh}x=\frac12\log\frac{1+x}{1-x}.
$$

First express the numerator and denominator as real functions. The sum and difference of the real logarithms give

$$
\log(1\pm x)=\frac12\log(1-x^2)
\ \pm\operatorname{artanh}x.
$$

Exponentiating and adding gives

$$
(1+x)^{1/x}+(1-x)^{1/x}
=2(1-x^2)^{1/(2x)}\cosh\beta(x).
$$

For $0\le x\le1/3$, both $1\pm ix$ have real part 1, so their entire curves lie in the right half-plane. Choose on that half-plane the analytic logarithm agreeing with the real logarithm on the positive axis. Then

$$
\log(1\pm ix)=\frac12\log(1+x^2)\pm i\arctan x,
$$

$$
(1+ix)^{1/x}+(1-ix)^{1/x}
=2(1+x^2)^{1/(2x)}\cos\alpha(x).
$$

Therefore

$$
\mathfrak r(x)
=e^{p(x)}\frac{\cosh\beta(x)}{\cos\alpha(x)},\qquad
p(x)=x+\frac{\log(1-x^2)-\log(1+x^2)}{2x}.
$$

When $x=1/d$, the exponent $1/x=d$ is an integer, so these complex powers equal the original polynomial powers. Also $0<\alpha(x)\le1<\pi/2$, so the cosine in the denominator is strictly positive.

Subtract the two logarithmic series:

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

Changing variables in the integrals for the arctangent and inverse hyperbolic tangent gives

$$
\alpha(x)=\int_0^1\frac{dt}{1+x^2t^2},\qquad
\beta(x)=\int_0^1\frac{dt}{1-x^2t^2}.
$$

Set $v=1-\alpha$ and differentiate under the integral:

$$
\beta'(x)=\int_0^1\frac{2xt^2}{(1-x^2t^2)^2}\,dt,
\qquad
v'(x)=\int_0^1\frac{2xt^2}{(1+x^2t^2)^2}\,dt>0.
$$

For each $t\in[0,1]$,

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

Hence $\beta'(x)\le(25/16)v'(x)$. Since $\beta'(x)>0$,

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

Use $(1+z)^{-1}\ge1-z$ and integrate:

$$
\alpha(x)\ge\int_0^1(1-x^2t^2)\,dt
=1-\frac{x^2}{3}\ge\frac{26}{27}.
$$

Appendix A.7 proves $\tan y\ge y+y^3/3$ by elementary calculus. Since $y+y^3/3$ is strictly increasing on nonnegative real numbers, substitute the lower bound $\alpha(x)\ge26/27$ to obtain

$$
\tan\alpha(x)
\ge\frac{26}{27}+\frac13\left(\frac{26}{27}\right)^3.
$$

Putting the terms over a common denominator gives the following strict margin:

$$
\frac{26}{27}+\frac{26^3}{3\cdot27^3}
-\frac79\frac{25}{16}
=\frac{1191008-1148175}{944784}
=\frac{42833}{944784}>0.
$$

Finally differentiate $\log\mathfrak r$ and substitute each of the bounds above:

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

The inequality $d_1<d_2$ implies $1/d_1>1/d_2$, hence $\mathfrak r_{d_1}<\mathfrak r_{d_2}$. Define $L:=\cosh1/\cos1$. As $x\downarrow0$,

$$
\alpha(x)\to1,\qquad \beta(x)\to1,\qquad p(x)\to0,
$$

$$
\lim_{d\to\infty,\ d\ {\rm odd}}\mathfrak r_d
=e^0\frac{\cosh1}{\cos1}
=L.
$$

## 11. Recovering every Taylor coefficient and remainder

For $|x|<1$, integrate the geometric series:

$$
\frac{\arctan x}{x}
=1-\frac{x^2}{3}+\frac{x^4}{5}+O(x^6),
\qquad
\frac{\operatorname{artanh}x}{x}
=1+\frac{x^2}{3}+\frac{x^4}{5}+O(x^6).
$$

For example, the remainder in the second identity satisfies

$$
\left|\sum_{k=3}^\infty\frac{x^{2k}}{2k+1}\right|
\le\frac{|x|^6}{7}\sum_{j=0}^\infty|x|^{2j}
=\frac{|x|^6}{7(1-x^2)}.
$$

The absolute remainder of the first, alternating series is bounded by the same positive series. The series for $p$ in Section 10 gives

$$
p(x)=-x^5/3+R_p(x),\qquad
|R_p(x)|\le\frac{|x|^9}{5(1-|x|^4)}.
$$

Put $b=\tanh1$, $h=\tan1$, $\delta_\beta=\beta-1$ and $\delta_\alpha=\alpha-1$. The first and second derivatives used below are

$$
(\log\cosh y)'=\tanh y,\quad
(\log\cosh y)''=1-\tanh^2y,
$$

$$
(-\log\cos y)'=\tan y,\quad
(-\log\cos y)''=1+\tan^2y.
$$

Differentiating once more,

$$
(\log\cosh y)'''=-2\tanh y\,\operatorname{sech}^2y,\qquad
(-\log\cos y)'''=2\tan y\,\sec^2y.
$$

The absolute value of the first expression is at most 2. The second needs to be bounded only between $\alpha$ and 1. Since $0\le\alpha\le1$, its absolute value is at most $2\tan1\,\sec^21$. Taylor's integral remainders satisfy

$$
|R_f|\le\frac{2}{6}|\delta_\beta|^3,\qquad
|R_g|\le\frac{2\tan1\,\sec^21}{6}|\delta_\alpha|^3.
$$

Here the factor $1/6$ comes from $\frac12\int_0^{|\delta|}(|\delta|-t)^2dt=|\delta|^3/6$. The expansions are

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

Since

$$
\delta_\beta=x^2/3+x^4/5+O(x^6),\quad
\delta_\alpha=-x^2/3+x^4/5+O(x^6),
$$

$$
\delta_\beta^2=x^4/9+O(x^6),\quad
\delta_\alpha^2=x^4/9+O(x^6),\quad
\delta_\beta^3=O(x^6),\quad\delta_\alpha^3=O(x^6),
$$

substitution gives

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

Add $p(x)$ and put $L=\cosh1/\cos1$:

$$
\log\frac{\mathfrak r(x)}L
=a_2x^2+\ell_4x^4-\frac{x^5}{3}+O(x^6),
$$

$$
a_2=\frac{b-h}{3},\qquad
\ell_4=\frac{b+h}{5}+\frac{2+h^2-b^2}{18}.
$$

Denote the right-hand side by $z(x)$. Since $z=O(x^2)$,

$$
e^z=1+z+\frac{z^2}{2}+O(z^3),\qquad
\frac{z^2}{2}=\frac{a_2^2}{2}x^4+O(x^6),\quad z^3=O(x^6).
$$

Therefore

$$
\mathfrak r(x)
=L\left[1+a_2x^2+
\left(\ell_4+\frac{a_2^2}{2}\right)x^4
-\frac{x^5}{3}+O(x^6)\right].
$$

Define $a_4=\ell_4+a_2^2/2$ and substitute $x=1/d$:

$$
\boxed{\mathfrak r_d
=L\left[1+\frac{a_2}{d^2}+\frac{a_4}{d^4}
-\frac1{3d^5}+O(d^{-6})\right].}
$$

The coefficients of the first and third powers are zero; the fifth-power coefficient is $-L/3$. Numerical values for comparison are

$$
La_2\approx-0.757603347512237,\qquad
La_4\approx2.035222101370122.
$$

The variable in this expansion is the base order $d$. We fix $d$ and take the block limit before letting $d$ grow. In total order $N=dm$, this does not provide a uniform $O(N^{-2})$ extremal error.

## 12. Independent checks and the limits of the conclusions

The accompanying Hessian verification program exits successfully. Exact fractions agree for 73 regular bases, including all labeled regular tournaments of orders three and five: 11,724 Hessian entries and 345 Hessian determinants with different eliminated coordinates.

The independent calculation first expands all principal determinants of $\det(I-P\operatorname{diag}(e^t))$, takes first and second derivatives directly, and then applies the implicit differentiation formula. It does not generate the left-hand side being compared from our closed form. The rational numbers in the original carousel table and the order-nine triangle blow-up table are recovered. The rational margin for monotonicity is checked exactly; the large-$d$ expansion remainder is examined only as a high-precision diagnostic.

This manuscript provides proofs for Conjectures 6 and 2 in the cited version and explicit model constants. Independent mathematical review and a fuller historical novelty investigation remain necessary. It does not prove the exact cycle extremum for all tournaments in the original Conjecture 3.

# Part II: The unique maximizer of fixed-base expectations

## 1. The precise extremal object

Fix an odd integer $d\ge3$. For any order-$d$ tournament $T^*$, replace each vertex by a random tournament of order $m$. All edges between blocks follow $T^*$. The total order is $N=dm$.

Write $\mathcal T(T^*,m)$ for independent uniform random internal blocks, and $\mathcal R(T^*,m)$ for independent uniform regular internal blocks; the latter requires odd $m$. The expected cycle and path counts are denoted by $\mathbb EC,\mathbb EH$ and normalized by

$$
\nu_N=(N-1)!/2^N,\qquad \mu_N=N!/2^{N-1}.
$$

We prove that for each fixed $d$ there is $M_d$ such that whenever $m\ge M_d$, both models' cycle and path expectations are maximized exactly by bases ordinarily isomorphic to $\mathrm{Car}_d$. In $\mathcal R$ only admissible $m$ are considered.

This gives a proof manuscript for Conjecture 1 in the cited Wormald version and its path counterpart. The objects compared are expectations of random blow-up models, not individual samples, and no exact Hamiltonian extremum for all tournaments of order $N$ is asserted.

## 2. The regular-base constants are already spectral ratios

For a regular base, Part I gives

$$
\lim_{m\to\infty}\frac{\mathbb EC_{\mathcal T}}{\nu_N}
=\lim_{m\to\infty}\frac{\mathbb EH_{\mathcal T}}{\mu_N}
=\rho_d(S),
$$

$$
\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
=\lim_{\substack{m\to\infty\\m\ {\rm odd}}}
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
=e^{1/d}\rho_d(S),
$$

$$
\rho_d(S)=\frac{\det(I+S/d)}{\det(I+iS/d)}.
$$

Comparing regular bases is thus a finite matrix problem. Distinguish the algebraic definition from the probabilistic conclusion: the determinant ratio below can be defined for nonregular sign matrices, but this section invokes the equality between that ratio and a model expectation limit only for regular bases. The expectation for a nonregular base cannot use that limit formula; Sections 7–10 prove separately that its normalized expectation tends to zero.

## 3. Product comparison, integration and all equality conditions

We invoke [Fang–Huang's Corollary 3.4](https://arxiv.org/html/2608.06238v1#S3). This is an external theorem, not a result reproved here. Its comparison matrix is

$$
(K_d)_{ij}=\begin{cases}
1,&i+j\le d,\\
0,&i+j=d+1,\\
(-1)^{i+j-d-2},&i+j\ge d+2.
\end{cases}
$$

Here $p$ is any positive integer, $x\in\mathbb R^d$, and $S_1,\ldots,S_p$ are real skew-symmetric matrices of order $d$ with off-diagonal entries in $\pm1$. The vector $x^*$ lists the absolute values of the coordinates of $x$ in decreasing order. For any product of these tournament sign matrices of the same order, the cited theorem gives

$$
(S_1\cdots S_p x)^*\prec_w K_d^p x^*.
$$

The right-hand side is a nonnegative decreasing vector. Weak majorization $u\prec_w v$ means

$$
\sum_{i=1}^r u_i\le\sum_{i=1}^r v_i
\quad(1\le r\le d).
$$

The cited theorem also states that vector equality in the outermost comparison implies vector equality for every suffix product. We now prove the squared-norm comparison and the equality conversion needed here.

Write $(a-t)_+=\max(a-t,0)$. For nonnegative decreasing vectors and $t\ge0$,

$$
\sum_{i=1}^d(u_i-t)_+
=\max_{0\le r\le d}\left(\sum_{i=1}^r u_i-rt\right)
\le\max_{0\le r\le d}\left(\sum_{i=1}^r v_i-rt\right)
=\sum_{i=1}^d(v_i-t)_+.
$$

For the first equality, take $r$ equal to the number of coordinates strictly greater than $t$. Adding smaller coordinates can only decrease the sum, and removing larger coordinates can only decrease it. For any $a\ge0$,

$$
2\int_0^\infty(a-t)_+\,dt
=2\int_0^a(a-t)\,dt
=2[at-t^2/2]_0^a=a^2.
$$

Integrating coordinate by coordinate gives

$$
\|u\|_2^2
=2\int_0^\infty\sum_i(u_i-t)_+\,dt
\le2\int_0^\infty\sum_i(v_i-t)_+\,dt
=\|v\|_2^2.
$$

If the squared norms agree, set $g(t)=\sum_i(v_i-t)_+-\sum_i(u_i-t)_+$. This function is continuous and nonnegative, with integral zero. If $g(t_0)>0$, continuity supplies an interval of positive length on which $g(t)>g(t_0)/2$, making the integral positive. Thus $g(t)=0$ for every $t\ge0$. Right derivatives of these piecewise linear functions give

$$
\#\{i:u_i>t\}=\#\{i:v_i>t\}=:N(t).
$$

For coordinate $j$,

$$
u_j=\int_0^\infty
\mathbf1_{\{\#\{i:u_i>t\}\ge j\}}\,dt
=\int_0^\infty\mathbf1_{\{N(t)\ge j\}}\,dt=v_j.
$$

Equality of squared norms therefore forces $u=v$. Taking $x=e_j$ and using $e_j^*=e_1$ yields

$$
\|S^pe_j\|_2^2\le\|K_d^pe_1\|_2^2,
$$

Equality also forces $(S^pe_j)^*=K_d^pe_1$.

## 4. Every moment of the comparison matrix matches the transitive matrix

Let $T_d$ have upper-triangular entries 1, lower-triangular entries $-1$ and diagonal entries 0. Let $R_0$ be the reversal permutation matrix and $D_0=\operatorname{diag}(1,-1,\ldots)$. Substituting the definition of $K_d$ entry by entry gives

$$
(D_0K_dR_0)_{ij}
=(-1)^{i-1}(K_d)_{i,d+1-j}
=\begin{cases}
(-1)^{i-1},&i<j,\\
0,&i=j,\\
(-1)^j,&i>j.
\end{cases}
$$

More explicitly, $R_0e_j=e_{d+1-j}$ and $(D_0)_{jj}=(-1)^{j-1}$. Every entry of $K_d$ depends only on $i+j$, so $(K_d)_{ij}=(K_d)_{ji}$ and $K_d^T=K_d$.

Write the sequence of increasing odd indices followed by decreasing even indices as

$$
(\ell_1,\ldots,\ell_d)=(1,3,\ldots,d,d-1,d-3,\ldots,2),
\qquad \Lambda e_j=e_{\ell_j}.
$$

Each index occurs once. Hence $\Lambda^T\Lambda=\Lambda\Lambda^T=I$, and $\ell_1=1$.

Order both rows and columns by increasing odd indices followed by decreasing even indices. For two odd indices, the earlier one satisfies $i<j$, giving $(-1)^{i-1}=1$. For two even indices, the earlier one satisfies $i>j$, giving $(-1)^j=1$. Every odd index precedes every even index: if their original indices satisfy $i<j$, the entry is $(-1)^{i-1}=1$; if $i>j$, it is $(-1)^j=1$. All upper-triangular entries in this order are therefore 1. Let $\Lambda$ perform this permutation. Then

$$
T_d=\Lambda^TD_0K_dR_0\Lambda.
$$

Set $U=D_0\Lambda$. Since $R_0R_0^T=I$, $\Lambda\Lambda^T=I$ and $K_d^T=K_d$, multiplication gives

$$
\begin{aligned}
T_dT_d^T
&=\Lambda^TD_0K_dR_0\Lambda
\Lambda^TR_0^TK_dD_0\Lambda\\
&=\Lambda^TD_0K_d^2D_0\Lambda=U^TK_d^2U.
\end{aligned}
$$

The first index in this ordering is 1, so $Ue_1=e_1$. Also $T_d^T=-T_d$, hence

$$
T_d^2=-U^TK_d^2U,\qquad
T_d^{2p}=(-1)^pU^TK_d^{2p}U
$$

because each adjacent pair $UU^T$ in the product equals $I$. Consequently,

$$
(-1)^p(T_d^{2p})_{11}
=e_1^TK_d^{2p}e_1
=(K_d^pe_1)^T(K_d^pe_1)
=\|K_d^pe_1\|_2^2.
$$

Appendix A.2 proves entry by entry that the shift $Z$ with negative wraparound satisfies $Z^TT_dZ=T_d$. Inserting $ZZ^T=I$ gives $Z^TT_d^{2p}Z=T_d^{2p}$. Its diagonal entry at $j<d$ gives $(T_d^{2p})_{j+1,j+1}=(T_d^{2p})_{jj}$. At $d$, the two wraparound minus signs multiply to 1, giving $(T_d^{2p})_{11}=(T_d^{2p})_{dd}$. Thus

$$
\begin{aligned}
\|T_d^p\|_F^2
&=\operatorname{tr}((T_d^p)^TT_d^p)
=(-1)^p\operatorname{tr}T_d^{2p}\\
&=d(-1)^p(T_d^{2p})_{11}
=d\|K_d^pe_1\|_2^2.
\end{aligned}
$$

Sum the $d$ column inequalities from the preceding section:

$$
\|S^p\|_F^2
=\sum_{j=1}^d\|S^pe_j\|_2^2
\le d\|K_d^pe_1\|_2^2
=\|T_d^p\|_F^2\qquad(p\ge1).
$$

This includes every odd $p$. We have not replaced a theorem solely about traces of degree $4k$ by one about degree $4k+2$.

## 5. The spectral-ratio bound and the full equality argument

Here $S$ is any tournament sign matrix of order $d$, with no regularity assumption. In this section $\lambda_j$ denotes a frequency of the unnormalized matrix $S$; to compare with the frequencies of $C=S/d$ in Part I, multiply those frequencies by $d$. Nonzero eigenvalues occur in pairs $\pm i\lambda_j$, with $\lambda_j>0$. The Frobenius estimate in Part I uses only skew symmetry and off-diagonal entries in $\pm1$, not regularity, so each $x_j=\lambda_j^2/d^2<1/2$. Zero eigenvalues contribute 1 to the following determinants, while a nonzero two-dimensional block contributes $1+x_j$ and $1-x_j$, respectively. Therefore

$$
\det(I+S/d)=\prod_j(1+x_j),\qquad
\det(I+iS/d)=\prod_j(1-x_j)>0.
$$

For $0\le x<1$, integrate the geometric series:

$$
\begin{aligned}
\log\frac{1+x}{1-x}
&=\int_0^x\left(\frac1{1+t}+\frac1{1-t}\right)\,dt\\
&=2\int_0^x\frac{dt}{1-t^2}
=2\sum_{r=0}^\infty\int_0^x t^{2r}\,dt
=2\sum_{r=0}^\infty\frac{x^{2r+1}}{2r+1}.
\end{aligned}
$$

The interchange follows from uniform convergence of the geometric series on $[0,x]$. The skew-symmetric canonical form also gives $\|S^p\|_F^2=2\sum_j\lambda_j^{2p}$. Substituting term by term yields

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

Define $r_d=\rho_d(T_d)$. Every deficit is nonnegative. If their sum vanishes, the term $r=1$ vanishes, giving $\|S^3\|_F^2=\|T_d^3\|_F^2$. This deficit is a sum of $d$ nonnegative column deficits, so each column attains equality. The squared-norm equality criterion in Section 3 of this part and Fang–Huang's suffix equality give, in sequence,

$$
(S^3e_j)^*=K_d^3e_1,\qquad
(S^2e_j)^*=K_d^2e_1.
$$

Take squared norms in the second identity and sum over $j$:

$$
\operatorname{tr}S^4=\|S^2\|_F^2
=d\|K_d^2e_1\|_2^2
=\|T_d^2\|_F^2=\operatorname{tr}T_d^4.
$$

Appendix A.3 independently proves that this equality forces $S=Q^TT_dQ$, where $Q$ is a signed permutation matrix. Check the converse as well: $Q^TQ=I$, so

$$
I+tS=Q^T(I+tT_d)Q,\qquad
\det(I+tS)=(\det Q)^2\det(I+tT_d)=\det(I+tT_d).
$$

Take $t=1/d$ and $t=i/d$ separately to obtain $\rho_d(S)=r_d$. Thus

$$
\rho_d(S)\le r_d,
\quad\text{with equality if and only if }S=Q^TT_dQ.
$$

The signed permutation matrix $Q$ here has exactly one entry $\pm1$ in each row and column and satisfies $Q^TQ=I$. This is a local symbol, different from the symmetric $Q$ in Part I. Write $Q=D_eP$, where $P$ is an ordinary permutation matrix and $D_e=\operatorname{diag}(e_1,\ldots,e_d)$; in this paragraph $e_i=\pm1$ are scalar signs. Put $e=(e_1,\ldots,e_d)^T$; these scalars are not standard basis vectors. Then

$$
S=P^TD_eT_dD_eP,\qquad PSP^T=D_eT_dD_e.
$$

Only $P$ is absorbed into ordinary relabeling; continue to denote the relabeled matrix by $S$. Diagonal sign switching itself is not an ordinary isomorphism. If $S$ is regular, then after this relabeling $S\mathbf1=0$ still holds. Using $D_e^2=I$,

$$
D_eT_de=0,\qquad T_de=0.
$$

The difference between rows $i$ and $i+1$ has entry 1 in each of columns $i,i+1$ and zero elsewhere. Therefore

$$
0=(T_de)_i-(T_de)_{i+1}=e_i+e_{i+1}.
$$

Recursion gives $e_i=(-1)^{i-1}e_1$. The overall sign $e_1$ occurs twice in $D_eT_dD_e$ and cancels. Appendix A.2 supplies an ordinary isomorphism, checked on every edge, between this alternating switching and $\mathrm{Car}_d$. Among regular bases, equality therefore holds exactly for the ordinary carousel isomorphism class.

## 6. An explicit strict gap from the sixth moment

If regular $S$ is not ordinarily isomorphic to the carousel, the preceding equality argument gives

$$
\Delta_3:=\|T_d^3\|_F^2-\|S^3\|_F^2>0.
$$

Modulo 2, $S\equiv J+I$. Since $J^2=dJ$ and $J^3=d^2J$,

$$
S^3\equiv(J+I)^3
=I+3J+3dJ+d^2J
\equiv I+(1+d+d^2)J\equiv I+J\pmod2.
$$

The last step uses that $d(d+1)$ is even. Also $(S^3)^T=-S^3$, so its diagonal entries vanish and its off-diagonal entries are odd. If $z=2k+1$,

$$
z^2=4k(k+1)+1\equiv1\pmod8.
$$

Pair the skew-symmetric positions in the squared norm:

$$
\|S^3\|_F^2=2\sum_{i<j}(S^3_{ij})^2
\equiv2\binom d2=d(d-1)\pmod{16}.
$$

This also applies to $T_d$. Thus $\Delta_3$ is a positive multiple of 16, and $\Delta_3\ge16$. Retaining just term $r=1$ in the logarithmic series gives

$$
\log\frac{r_d}{\rho_d(S)}
\ge\frac{\Delta_3}{3d^6}\ge\frac{16}{3d^6}.
$$

Exponentiate and rearrange:

$$
\rho_d(S)\le r_de^{-16/(3d^6)},\qquad
r_d-\rho_d(S)\ge r_d(1-e^{-16/(3d^6)})>0.
$$

This is a gap between limiting constants for fixed bases, not an effective threshold for finite block order.

## 7. Nonregular scores and exponential loss

Let $d_i$ be the base outdegrees, put $b_i=d_i+1/2$, and define

$$
a_i=\frac{2b_i}{d},\qquad
\kappa=\left(\prod_{i=1}^d a_i\right)^{1/d},\qquad
s_i=2d_i-(d-1).
$$

Put $s=(s_1,\ldots,s_d)^T$, so that $\|s\|^2=\sum_{i=1}^d s_i^2$. Each edge contributes exactly one outdegree. Therefore

$$
\sum_i d_i=\binom d2,\qquad
\sum_i a_i=\frac{2\binom d2+d}{d}=d,\qquad
a_i=1+\frac{s_i}{d}\in(0,2),\qquad \sum_i s_i=0.
$$

The function $f(a)=a-1-\log a$ satisfies $f'(a)=(a-1)/a$, so its unique minimum occurs at $a=1$ with value $f(1)=0$. Hence

$$
\log\kappa=\frac1d\sum_i\log a_i
\le\frac1d\sum_i(a_i-1)=0.
$$

Equality requires $a_i=1$ for every index, equivalently $d_i=(d-1)/2$ for every index. For a nonregular base, $\kappa<1$. To quantify the loss, use a second-order expansion with integral remainder:

$$
\log a=(a-1)-(a-1)^2\int_0^1
\frac{1-t}{[1+t(a-1)]^2}\,dt.
$$

Since $0<1+t(a-1)<2$,

$$
\int_0^1\frac{1-t}{[1+t(a-1)]^2}\,dt
\ge\frac14\int_0^1(1-t)\,dt=\frac18.
$$

Substitute $a_i$ and sum:

$$
\begin{aligned}
\log\kappa
&\le\frac1d\sum_i\left(\frac{s_i}{d}-\frac{s_i^2}{8d^2}\right)
=-\frac{\|s\|^2}{8d^3}.
\end{aligned}
$$

For odd $d$ each $s_i$ is even. Nonregularity implies that some $s_i\ne0$; the zero-sum condition then requires nonzero terms of opposite signs, each with absolute value at least 2. Thus $\|s\|^2\ge2^2+2^2=8$ and

$$
\kappa^N\le\exp[-N\|s\|^2/(8d^3)]\le e^{-N/d^3}.
$$

In model $\mathcal T$, let $W$ be the entrywise expectation of the adjacency matrix. For any nonnegative matrix of order $N$, let $\operatorname{Sym}(N)$ be all vertex permutations and let $\mathcal C_N$ consist of permutations with a single cycle of length $N$. Define the weighted permanent and weighted Hamiltonian cycle count by:

$$
\operatorname{per}W=\sum_{\sigma\in\operatorname{Sym}(N)}
\prod_{v=1}^N W_{v,\sigma(v)},\qquad
C(W)=\sum_{\sigma\in\mathcal C_N}\prod_{v=1}^N W_{v,\sigma(v)}.
$$

A single-cycle permutation already identifies cyclic starting points, so no additional division by the number of vertices is made. A fixed directed Hamiltonian cycle uses $N$ distinct unordered vertex pairs, and its random internal edges are independent. Its occurrence probability is therefore the product of the corresponding entries of $W$. Sum over cycles identified up to cyclic starting point:

$$
\mathbb EC_{\mathcal T}=C(W)\le\operatorname{per}W.
$$

The permanent contains all permutations. Each Hamiltonian cycle corresponds to one single-cycle permutation with nonnegative weight, proving the final inequality. We have not assumed independence for the edges in an arbitrary permutation: such a permutation can contain a two-cycle, whereas a tournament cannot contain both opposite edges.

## 8. Filling weighted rows, making them integral and applying Brégman

We apply this section for $m\ge2$. Model $\mathcal R$ also requires odd $m$, so there $m\ge3$. This covers all sufficiently large block orders. Every row of type $i$ in $W$ has sum

$$
r_i=md_i+\frac{m-1}{2}=mb_i-\frac12,\qquad
R_i=\lceil r_i\rceil.
$$

For a row of length $L$, denoted $w$, assume $0\le w_j\le1$. Its current sum is $r=\sum_{j=1}^Lw_j$, and its target integer sum $R$ satisfies $r\le R\le L$. The amount to add is $s_0=R-r$, and the available capacity is $\sum_j(1-w_j)=L-r\ge s_0$. Starting at $j=1$, choose successively

$$
\delta_j=\min(1-w_j,s_{j-1}),\qquad
s_j=s_{j-1}-\delta_j,\qquad w'_j=w_j+\delta_j.
$$

At each step the remaining mass satisfies

$$
s_j=\max(0,s_{j-1}-(1-w_j))
=\max\left(0,s_0-\sum_{h=1}^j(1-w_h)\right).
$$

The first equality subtracts the smaller of two quantities; the second follows by substitution starting at $j=1$.

The recursion gives $s_L=\max(0,s_0-\sum_j(1-w_j))=0$, so $0\le w'_j\le1$ and $\sum_jw'_j=R$. Every coefficient of the permanent is nonnegative, so these entrywise increases cannot decrease it.

Fix the other rows and write the permanent as $\sum_jw_jc_j$, where $c_j$ is the permanent obtained by deleting the current row and column $j$; thus $c_j\ge0$. If entries $w_a,w_b$ both lie strictly between 0 and 1, label them so that $c_a\ge c_b$ and take

$$
\eta=\min(1-w_a,w_b)>0,\qquad
w_a'=w_a+\eta,\qquad w_b'=w_b-\eta.
$$

The row sum is preserved, and

$$
\sum_jw_j'c_j-\sum_jw_jc_j=\eta(c_a-c_b)\ge0.
$$

At least one coordinate becomes 0 or 1, reducing the number of nonintegral coordinates. After at most $L-1$ steps there is at most one nonintegral coordinate. Since all other coordinates and the row sum $R$ are integers, the remaining coordinate must also be integral. Perform this operation on every row to obtain a zero–one matrix $V$. Each row of type $i$ has $R_i$ ones, and $\operatorname{per}W\le\operatorname{per}V$.

Here $V$ is an auxiliary matrix for the upper bound. Its required properties are zero–one entries and the specified row sums; diagonal entries may be 1. The theorem below applies to such general zero–one matrices.

Now invoke [Brégman's inequality, as stated in Lemma 2.1 of Alon's paper](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf): for a zero–one matrix with row sums $q_1,\ldots,q_L>0$,

$$
\operatorname{per}V\le\prod_{\ell=1}^L(q_\ell!)^{1/q_\ell}.
$$

Since $r_i\ge(m-1)/2>0$, the integer upper bound $R_i$ is at least 1. This verifies the positive-row-sum hypothesis of the cited Brégman bound. There are exactly $m$ rows of each type here, giving

$$
\operatorname{per}W\le\prod_{i=1}^d(R_i!)^{m/R_i}.
$$

This uses the original zero–one theorem; the concrete row operations above prove its applicability to the weighted matrix.

## 9. Normalization with explicit constants

If the permanent being estimated is zero, the nonnegative cycle count it bounds is also zero, and the desired bound already holds; we do not take the logarithm of zero. All logarithmic permanent calculations below and in Section 10 are made only when the corresponding permanent is positive. The resulting positive upper bounds also cover the zero case. Assume $m\ge2$ and $N=dm$. Write $R_i=mb_i+\varepsilon_i$. Then $|\varepsilon_i|\le1/2$ and

$$
R_i\ge m/2-1/2\ge m/4,\qquad R_i\le N.
$$

The rounding error follows from the target definition:

$$
0\le R_i-r_i<1,\qquad
\varepsilon_i=R_i-mb_i=(R_i-r_i)-\frac12
\in[-1/2,1/2).
$$

Use the remainder form of Stirling's bound for integers $R\ge1$:

$$
\log(R!)=R\log R-R+\frac12\log(2\pi R)
+\frac{\theta_R}{12R},\qquad 0<\theta_R<1.
$$

Therefore

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

For the last two terms we used $m/(2R_i)\le2$ and $m/(12R_i^2)\le4/(3m)$, respectively. The lower Stirling bound also gives

$$
\log(N!/2^N)\ge N\log(N/2)-N.
$$

Subtracting yields

$$
\log\frac{\operatorname{per}W}{N!/2^N}
\le m\sum_i\log\frac{2R_i}{N}
+2d\log(2\pi N)+\frac{4d}{3m}.
$$

Set $y_i=\varepsilon_i/(mb_i)$. Because $b_i\ge1/2$, we have $|y_i|\le1/m\le1/2$ and

$$
\frac{2R_i}{N}=a_i(1+y_i),\qquad
|\log(1+y_i)|
=\left|\int_0^{y_i}\frac{dt}{1+t}\right|
\le\frac{|y_i|}{1-|y_i|}\le\frac2m.
$$

Thus

$$
m\sum_i\log\frac{2R_i}{N}
\le m\sum_i\log a_i+2d=N\log\kappa+2d.
$$

Use $4d/(3m)\le2d/3$ and $N!/2^N=N\nu_N$ to obtain the explicit bound

$$
\frac{\mathbb EC_{\mathcal T}}{\nu_N}
\le e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N.
$$

With regular internal blocks, the actual old row sum in each sample is the positive integer $mb_i-1/2$. For a sample $G$ with adjacency matrix $A_G$, each cycle is a nonnegative single-cycle term in the permanent, so $C(G)\le\operatorname{per}A_G$. Apply Brégman directly to $A_G$, use the preceding estimates, and average over the samples to obtain

$$
\frac{\mathbb EC_{\mathcal R}}{\nu_N}
\le e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N.
$$

The regular model uses only admissible odd $m$. For a nonregular base, $\kappa<1$. Take the logarithm of the right-hand side and divide by $N$:

$$
\frac{\log(e^{8d/3}(2\pi)^{2d}N^{2d+1}\kappa^N)}{N}
=\log\kappa+
\frac{8d/3+2d\log(2\pi)+(2d+1)\log N}{N}
\longrightarrow\log\kappa<0,
$$

For completeness, for $N\ge1$,

$$
0\le\frac{\log N}{N}
=\frac1N\int_1^N\frac{dt}{t}
\le\frac1N\int_1^N\frac{dt}{\sqrt t}
=\frac{2(\sqrt N-1)}N\longrightarrow0.
$$

Denote the upper bound by $B_N$ and set $c=-\tfrac12\log\kappa>0$. Since $\log B_N/N\to\log\kappa=-2c$, beyond a threshold we have $\log B_N/N<-c$, and therefore $0\le B_N<e^{-cN}\to0$. The polynomial degree in the path bound differs, but division of its logarithm by $N$ again makes the constant terms and $\log(N+1)/N$ vanish by the displayed integral estimate.

Both normalized cycle expectations therefore tend to zero.

## 10. The added-vertex path bound with every normalization term retained

Fix the old tournament $G$. Add a vertex $v$ whose edges to old vertices are independently and fairly oriented. Each path $x_1\to\cdots\to x_N$ corresponds to the unique candidate cycle $v\to x_1\to\cdots\to x_N\to v$. The two required new edges have joint probability $(1/2)^2=1/4$. Deleting $v$ reverses the correspondence. Therefore

$$
\mathbb E[C_{\rm aug}\mid G]=H(G)/4,\qquad
4\nu_{N+1}=\frac{4N!}{2^{N+1}}=\frac{N!}{2^{N-1}}=\mu_N,
$$

$$
\frac{\mathbb EH}{\mu_N}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

Here $G_{\rm aug}$ is the random tournament after adding $v$, and $C_{\rm aug}:=C(G_{\rm aug})$. Conditional expectation first fixes $G$ and averages over the added edges. For independent internal blocks let $W_{\rm aug}$ be the entrywise expected augmented adjacency matrix. For regular internal blocks fix an actual augmented sample and denote its adjacency matrix by $A_{\rm aug}$. Apply the row filling and integrality operations of Section 8 to either input. Denote the resulting zero-one auxiliary matrix of order $(N+1)$ by $V_{\rm aug}$; it need not be a tournament adjacency matrix.

$$
\mathbb EC_{{\rm aug},\mathcal T}
=C(W_{\rm aug})\le\operatorname{per}W_{\rm aug}
\le\operatorname{per}V_{\rm aug},
$$

$$
C(G_{\rm aug})\le\operatorname{per}A_{\rm aug}
\le\operatorname{per}V_{\rm aug}
\qquad(\text{each sample of }\mathcal R).
$$

The first equality is used only for independent internal blocks. The second line holds separately for each sample and does not require independent edges inside a regular block.

For the augmented expectation matrix of $\mathcal T$, the old row sum is $mb_i$. For each actual augmented sample of $\mathcal R$, the old row sum is at most $mb_i+1/2$. Use the common choice

$$
R_i'=\lceil mb_i+1/2\rceil=mb_i+\varepsilon_i',
\qquad \frac12\le\varepsilon_i'<\frac32.
$$

Fill the new row to $R_0=N$. Since $b_i\le d-1/2$ and $m\ge2$, we have $mb_i+1/2\le N-1/2$ and hence $R_i'\le N$. Also $R_i'\ge m/2$. These filling targets do not exceed the augmented matrix's column count $N+1$, so the row operations of Section 8 apply. Brégman gives

$$
\log\operatorname{per}V_{\rm aug}
\le m\sum_i\frac{\log(R_i'!)}{R_i'}
+\frac{\log(N!)}N.
$$

Use $R_i'\ge m/4$ and $R_i'\le N+1$ to estimate the remainders for the old rows, keeping the new row separate:

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

Subtract $\log((N+1)!/2^{N+1})\ge(N+1)\log((N+1)/2)-(N+1)$. Regroup every leading term as follows:

$$
\begin{aligned}
&m\sum_i\log R_i'+\log N-(N+1)\log((N+1)/2)\\
&=m\sum_i\log(2R_i'/N)
+N\log(N/(N+1))+\log(2N/(N+1)).
\end{aligned}
$$

The second term is at most zero, and the third is at most $\log2$. The inequality $\log(1+y)\le y$, valid for $y\ge0$, follows from the integral $\int_0^y(1+t)^{-1}dt\le y$. Thus

$$
\begin{aligned}
m\sum_i\log(2R_i'/N)
&=N\log\kappa+
m\sum_i\log(1+\varepsilon_i'/(mb_i))\\
&\le N\log\kappa+\sum_i\frac{\varepsilon_i'}{b_i}
\le N\log\kappa+3d.
\end{aligned}
$$

Using $4d/(3m)\le2d/3$ now gives

$$
\begin{aligned}
\log\frac{\operatorname{per}V_{\rm aug}}{(N+1)!/2^{N+1}}
&\le N\log\kappa+\frac{11d}{3}+\frac1{12}+\log2\\
&\quad +(2d+1)\log(2\pi(N+1)).
\end{aligned}
$$

Exponentiate and substitute $(N+1)!/2^{N+1}=(N+1)\nu_{N+1}$. The two models satisfy, respectively,

$$
\frac{\mathbb EH_{\mathcal T}}{\mu_N}
\le 2e^{11d/3+1/12}(2\pi)^{2d+1}(N+1)^{2d+2}\kappa^N,
$$

$$
\frac{\mathbb EH_{\mathcal R}}{\mu_N}
\le 2e^{11d/3+1/12}(2\pi)^{2d+1}(N+1)^{2d+2}\kappa^N.
$$

For the second bound, constrain the augmented cycle count in each sample and then take expectations. No independence of edges inside regular blocks is assumed. For a fixed nonregular base, the logarithm of either bound divided by $N$ tends to $\log\kappa<0$, so both bounds tend to zero. If regular internal blocks are generated by the triangle-decomposition model, at every admissible order the internal outdegree of each old vertex is still $(m-1)/2$, the old row sum is still $mb_i-1/2$, and its augmented upper bound is still $mb_i+1/2$. These row bounds hold sample by sample, giving the displayed $\mathcal R$ bound in that model as well.

## 11. From limiting constants to the exact expected extremum for large blocks

For fixed $d$, each vertex pair has two possible directions, so there are $2^{\binom d2}$ labeled bases and at most that many ordinary isomorphism classes. Among regular bases, the carousel has limiting constant $r_d$, or $e^{1/d}r_d$, and all other regular bases have the positive gap from Section 6. The normalized expectations for nonregular bases tend to zero.

For each other base choose sufficiently large $m$ so that its actual normalized expectation is strictly smaller than the carousel's. Take the maximum of the finitely many thresholds to obtain $M_d$ from Section 1 and the unique ordinary isomorphism class. This uses fixed $d$ and does not assert uniformity as $d$ grows.

It remains to explain why every ordinarily isomorphic copy of the carousel attains the same maximum. Given an ordinary base isomorphism $\pi$, write a blow-up vertex as $(i,a)$. Then

$$
(i,a)\longmapsto(\pi(i),a)
$$

is a bijection between samples of the two blow-up models. The base isomorphism preserves directions between blocks; internal blocks are merely reordered, preserving their independent identical sampling probabilities. Every path and cycle corresponds uniquely under this bijection, so their expectations agree. Combined with the strict inequality for nonisomorphic bases, this identifies the entire ordinary carousel isomorphism class as the equality class.

## 12. Results obtained and remaining questions

Part I gives a finite algebraic proof for Conjecture 6 and the limit and monotonicity in Conjecture 2 of the cited Wormald version. With explicit use of his counting theorems and Fang–Huang's comparison, this manuscript obtains the fixed-base expectation assertion in Conjecture 1 and its path counterpart.

These results identify our spectral ratio exactly with the original random-model constants, removing the need to compute a Hessian separately for each base. They do not prove Wormald's Conjecture 3 for cycle extrema among all tournaments, give a new uniform error for global path extrema or an effective $M_d$, or establish a simultaneous limit with growing base and block orders. The general arguments await independent mathematical review. Historical attribution has not been exhaustively investigated, and no priority claim is made.

# Part III: Supplementary calculations for prepublication review

## A.1 The determinant polynomial of the transitive sign matrix

Let $T_n$ have upper-triangular entries 1, lower-triangular entries $-1$ and diagonal entries 0, and write $F_n(t)=\det(I+tT_n)$. We prove the closed form of Part I, Section 9 directly by row operations, without treating even principal determinants as an unexplained input.

For $n=1$, $F_1(t)=1=((1+t)+(1-t))/2$, proving the formula in that case. Now assume $n\ge2$. For the first $n-1$ rows simultaneously perform $R_i\leftarrow R_i-R_{i+1}$. The operation is implemented by an upper-triangular matrix with diagonal 1, so the determinant is preserved. In the resulting matrix the only potentially nonzero entries in the first $n-1$ rows are

$$
M_{ii}=1+t,\qquad M_{i,i+1}=t-1
$$

The last row is $(-t,\ldots,-t,1)$. Temporarily assume $t\ne-1,0$ and put

$$
r=\frac{1-t}{1+t}.
$$

Denote the top-left block of order $(n-1)$ by $B$. Its determinant is $(1+t)^{n-1}$. The top-right column $b$ has only its last entry nonzero, equal to $t-1$. Solve $Bx=b$ from the last row upwards:

$$
x_{n-1}=\frac{t-1}{1+t}=-r,
$$

$$
(1+t)x_i+(t-1)x_{i+1}=0
\quad\Longrightarrow\quad x_i=rx_{i+1}=-r^{n-i}.
$$

The Schur complement gives

$$
F_n(t)=(1+t)^{n-1}\left(1-t\sum_{k=1}^{n-1}r^k\right).
$$

First multiply the finite geometric sum by $1-r$; adjacent terms cancel:

$$
(1-r)\sum_{k=1}^{n-1}r^k
=(r+r^2+\cdots+r^{n-1})-(r^2+\cdots+r^n)
=r-r^n.
$$

Thus $\sum_{k=1}^{n-1}r^k=r(1-r^{n-1})/(1-r)$. Using $1-r=2t/(1+t)$, the expression in parentheses becomes

$$
\begin{aligned}
1-t\sum_{k=1}^{n-1}r^k
&=1-\frac{tr(1-r^{n-1})}{1-r}\\
&=1-\frac{1-t}{2}(1-r^{n-1})\\
&=\frac{1+t}{2}+\frac{1-t}{2}r^{n-1}.
\end{aligned}
$$

Multiply the bracket by $(1+t)^{n-1}$ and substitute $r=(1-t)/(1+t)$:

$$
\begin{aligned}
F_n(t)
&=\frac{(1+t)^n}{2}
+\frac{(1+t)^{n-1}(1-t)}2
\left(\frac{1-t}{1+t}\right)^{n-1}\\
&=\frac{(1+t)^n}{2}+\frac{(1-t)^n}{2}.
\end{aligned}
$$

Both sides are polynomials and agree for every $t$ except two values. They therefore also agree at $t=-1,0$. Substitute $t=1/d$ and $t=i/d$ to obtain the determinant ratio for the carousel model.

To justify the assertion about each principal determinant in Part I, Section 9, take nonempty $U$ and put $k=|U|$. In increasing original vertex order, $T_d[U]$ is exactly $T_k$. The highest-degree coefficient of $F_k(t)=\det(I+tT_k)$ is $\det T_k$; write $[t^k]$ for extraction of this coefficient. Thus

$$
\det T_d[U]=\det T_k=[t^k]F_k(t)
=\frac{1+(-1)^k}{2}
=\begin{cases}1,&k\ \text{even},\\0,&k\ \text{odd}.\end{cases}
$$

The empty principal determinant is 1 by convention. Thus the proved closed form determines every individual principal determinant.

## A.2 Alternating switching and ordinary carousel isomorphism

Let $d=2q+1$. Switch the transitive matrix by alternating signs $e_i=(-1)^{i-1}$ and $D_e=\operatorname{diag}(e_i)$. For $i<j$ and $\Delta=j-i$,

$$
(D_eT_dD_e)_{ij}=(-1)^\Delta.
$$

Define the carousel labeling map

$$
\phi(i)=(q+1)i\pmod d.
$$

Since $2(q+1)=d+1$, the numbers $q+1$ and $d$ are coprime, making $\phi$ a permutation.

If $\Delta=2r$, then $1\le r\le q$ and

$$
\phi(j)-\phi(i)\equiv(q+1)2r\equiv r\pmod d.
$$

This difference belongs to $\{1,\ldots,q\}$, precisely the condition for $\phi(i)\to\phi(j)$ in the carousel. The switched matrix entry is also 1.

If $\Delta=2r+1$, then $0\le r\le q-1$ and

$$
\phi(j)-\phi(i)\equiv q+1+r\pmod d.
$$

This difference belongs to $\{q+1,\ldots,2q\}$, so the direction is reversed; the switched matrix entry is $-1$. Skew symmetry handles $i>j$, and all diagonal entries are zero. Thus the map preserves each directed edge and is an ordinary isomorphism.

Part II also uses equality of the diagonal entries of powers of the transitive matrix. Define $Ze_j=e_{j+1}$ for $j<d$ and $Ze_d=-e_1$. When $i,j<d$,

$$
(Z^TT_dZ)_{ij}=(T_d)_{i+1,j+1}=(T_d)_{ij}.
$$

When $i<d,j=d$,

$$
(Z^TT_dZ)_{i,d}=-(T_d)_{i+1,1}=1=(T_d)_{i,d}.
$$

When $i=d,j<d$,

$$
(Z^TT_dZ)_{d,j}=-(T_d)_{1,j+1}=-1=(T_d)_{d,j}.
$$

The remaining diagonal entry is zero in both matrices. Therefore $Z^TT_dZ=T_d$, and for every integer $p\ge0$,

$$
Z^TT_d^{2p}Z=T_d^{2p}.
$$

Taking diagonal entries makes adjacent diagonal entries equal, with the two wraparound minus signs canceling.

## A.3 Complete expansions for the fourth-order determinant and fourth-moment equality

Let $a,b,c,g,e,f$ be six local real scalars, with $g$ distinct from the matrix order. Set

$$
M=\begin{pmatrix}
0&a&b&c\\
-a&0&g&e\\
-b&-g&0&f\\
-c&-e&-f&0
\end{pmatrix}.
$$

Write $M_{1j}$ for the order-three determinant obtained by deleting row 1 and column $j$, without the cofactor sign. Expanding along the first row gives the following separate calculations:

$$
\begin{aligned}
M_{12}
&=\det\begin{pmatrix}-a&g&e\\-b&0&f\\-c&-f&0\end{pmatrix}\\
&=(-a)(0-f(-f))-g((-b)0-f(-c))+e((-b)(-f)-0(-c))\\
&=-af^2-cgf+bef,\\
M_{13}
&=\det\begin{pmatrix}-a&0&e\\-b&-g&f\\-c&-e&0\end{pmatrix}\\
&=(-a)((-g)0-f(-e))-0+e((-b)(-e)-(-g)(-c))\\
&=-aef+be^2-cge,\\
M_{14}
&=\det\begin{pmatrix}-a&0&g\\-b&-g&0\\-c&-e&-f\end{pmatrix}\\
&=(-a)((-g)(-f)-0(-e))-0+g((-b)(-e)-(-g)(-c))\\
&=-agf+bge-cg^2.
\end{aligned}
$$

Each order-three determinant is itself expanded along its first row. Its three contributions come from the three first-row entries, with a zero entry contributing zero. Multiply by the coefficients in the order-four expansion:

$$
\begin{aligned}
\det M
&=-aM_{12}+bM_{13}-cM_{14}\\
&=(a^2f^2+acgf-abef)
+(-abef+b^2e^2-bcge)
+(acgf-bcge+c^2g^2)\\
&=a^2f^2+b^2e^2+c^2g^2-2abef+2acgf-2bcge\\
&=(af-be+cg)^2.
\end{aligned}
$$

When all six variables are $\pm1$, the expression $af-be+cg$ is a sum of three numbers in $\pm1$, taking values $\pm1$ or $\pm3$. Thus the determinant is 1 or 9. Let $D_4(S)$ count four-vertex principal determinants equal to 9. Expand by column multilinearity, choosing in each column either the identity column or the corresponding column of $tS$:

$$
\det(I+tS)=\sum_{U\subseteq[d]}t^{|U|}\det S[U].
$$

An odd-order skew-symmetric matrix $B$ satisfies $\det B=\det B^T=\det(-B)=-\det B$, so its determinant vanishes. Every second-order principal determinant is 1. Among fourth-order determinants, $D_4$ are 9 and all others are 1. Therefore

$$
\det(I+tS)=1+e_2t^2+e_4t^4+O(t^6),
$$

$$
e_2=\binom d2,\qquad
e_4=(\binom d4-D_4)+9D_4=\binom d4+8D_4.
$$

Use the following expansion only near $t=0$. Choose $|t|\,\|S\|_{\rm op}<1/2$. Every eigenvalue $\mu$ then satisfies $|t\mu|<1/2$. Define $\log(1+t\mu)$ by the logarithmic series with value 0 at 1. Interchanging the power series with a finite eigenvalue sum is valid, and

$$
\det(I+tS)=\prod_\mu(1+t\mu),\qquad
\operatorname{tr}S^k=\sum_\mu\mu^k.
$$

Eigenvalues are counted with multiplicity. The real skew-symmetric canonical form gives diagonalizability over the complex numbers; zero eigenvalues are included.

The logarithmic series for each eigenvalue gives

$$
\log\det(I+tS)
=\sum_{k\ge1}\frac{(-1)^{k+1}t^k}{k}\operatorname{tr}S^k
=-\frac{t^2}{2}\operatorname{tr}S^2
-\frac{t^4}{4}\operatorname{tr}S^4+O(t^6).
$$

Odd traces vanish because $\operatorname{tr}S^{2j+1}=\operatorname{tr}(S^{2j+1})^T=-\operatorname{tr}S^{2j+1}$. On the other hand, substitute $z=e_2t^2+e_4t^4+O(t^6)$ into $\log(1+z)=z-z^2/2+O(z^3)$. Since $z^2=e_2^2t^4+O(t^6)$ and $z^3=O(t^6)$, this gives

$$
\log\det(I+tS)=e_2t^2+(e_4-e_2^2/2)t^4+O(t^6).
$$

Equate the fourth-order coefficients and isolate the trace step by step:

$$
-\operatorname{tr}S^4/4=e_4-e_2^2/2,\qquad
\operatorname{tr}S^4=2e_2^2-4e_4
=2\binom d2^2-4\binom d4-32D_4(S).
$$

In the transitive matrix, any four vertices in increasing order have $a=b=c=g=e=f=1$, giving determinant $(1-1+1)^2=1$. Thus $D_4(T_d)=0$. Subtracting yields

$$
\operatorname{tr}T_d^4-\operatorname{tr}S^4=32D_4(S).
$$

If the fourth moments agree, $D_4(S)=0$. Choose local scalar signs $\epsilon_1=1,\epsilon_j=s_{1j}$ for $j>1$, and define $D_\epsilon=\operatorname{diag}(\epsilon_1,\ldots,\epsilon_d)$ and $S'=D_\epsilon S D_\epsilon$. In this paragraph abbreviate these scalars by $e_j=\epsilon_j$ and $D_\epsilon$ by $D_e$. After switching, $s'_{1j}=e_1s_{1j}e_j=s_{1j}^2=1$. Each principal determinant is multiplied by $(\det D_e[U])^2=1$, so $D_4$ is unchanged. Choose any $i<j<k$ all different from 1:

$$
\det S'[\{1,i,j,k\}]
=(s'_{jk}-s'_{ik}+s'_{ij})^2.
$$

If these three vertices form a directed triangle, $s'_{ij}=s'_{jk}=-s'_{ik}$, making the expression in parentheses $3s'_{ij}$ and its square 9, a contradiction. Thus the remaining vertices contain no directed triangle. If $i\to j$ and $j\to k$ but $i\not\to k$, then $k\to i$, producing a triangle. The direction relation is therefore a strict total order, and we can label vertices in this order. Vertex 1 dominates all remaining vertices, making the entire switched tournament transitive. Conversely, signed permutation similarity preserves traces, so it gives fourth-moment equality. For $d=3$, two vertices remain after switching; order them according to their unique edge.

## A.4 Reproducible steps for row integrality

Section 8 of Part II lists the coordinate filling amounts $\delta_j$, the remaining amounts $s_j$, the two-coordinate movement $\eta$, and the permanent change. Here are two integers that establish termination.

$$
q(w)=\#\{j:0<w_j<1\},\qquad
q(W)=\sum_{\ell=1}^L q(W_{\ell,\cdot}).
$$

Each two-coordinate movement preserves the integer row sum, makes at least one nonintegral coordinate integral, and leaves other integral coordinates unchanged. Thus $q(w)$ decreases by at least 1. Initially $q(w)\le L$, so it cannot decrease indefinitely. If it stopped at $q(w)=1$, the unique nonintegral coordinate would satisfy

$$
w_a=R-\sum_{j\ne a}w_j\in\mathbb Z,
$$

contradicting its nonintegrality. Thus termination occurs at $q(w)=0$. Processing a row does not change other rows. Every row becomes integral after at most $L-1$ two-coordinate movements, and the total number is at most $L(L-1)$. At every step the permanent changes by $\eta(c_a-c_b)\ge0$, as computed in Section 8.

## A.5 Checking each regrouped term in the added-vertex bound

Section 10 of Part II already gives the path bound with explicit constants. Here we split its logarithmic regrouping into separate terms so that no additional factor $N$ is hidden. Since $md=N$,

$$
m\sum_i\log R_i'
=m\sum_i\log(2R_i'/N)+N\log(N/2).
$$

we obtain

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

The denominator in the ensuing exponential bound is initially $(N+1)!/2^{N+1}$. On changing to the cycle-expectation denominator,

$$
\frac{(N+1)!/2^{N+1}}{\nu_{N+1}}
=\frac{(N+1)!}{N!}=N+1.
$$

the polynomial degree changes from $2d+1$ to $2d+2$. The added-vertex identity also gives

$$
\frac{\mathbb EH}{\mu_N}
=\frac{4\mathbb EC_{\rm aug}}{4\nu_{N+1}}
=\frac{\mathbb EC_{\rm aug}}{\nu_{N+1}}.
$$

One factor comes from the change in order and the other from the added-vertex probability; both have been retained explicitly.

## A.6 A common threshold for finitely many bases

Here $T$ denotes an ordinary isomorphism class of base tournaments; choose any representative to form the random blow-up. Part II, Section 11 proved that the expectation is independent of that choice. For a model $\mathcal M\in\{\mathcal T,\mathcal R\}$ and a fixed choice of count, define

$$
f_T(m)=
\begin{cases}
\mathbb EC_{\mathcal M}(T,m)/\nu_{dm},&\text{cycles},\\
\mathbb EH_{\mathcal M}(T,m)/\mu_{dm},&\text{paths},
\end{cases}
\qquad f_*(m)=f_{\mathrm{Car}_d}(m).
$$

Write $\ell_T=\lim_{m\to\infty}f_T(m)$ and $\ell_*=\lim_{m\to\infty}f_*(m)$. In model $\mathcal R$, both limits are restricted to odd $m$.

Fix one model and one count. Let the carousel limit be $\ell_*>0$ and let every other ordinary isomorphism class have limit $\ell_T<\ell_*$. Since $d\ge3$, the transitive base is nonregular whereas the carousel is regular, so the set of noncarousel isomorphism classes is nonempty. Finiteness and isomorphism invariance here are supplied by Part II, Section 11. Each noncarousel limit is strictly smaller, so the finite set of positive differences has a positive minimum:

$$
\delta=\min_{T\not\cong\mathrm{Car}_d}(\ell_*-\ell_T)>0.
$$

Nonregular classes have limit zero; regular noncarousel classes are handled by the strict spectral gap. For each class choose $M_T$ so that whenever $m\ge M_T$ its normalized expectation $f_T(m)$ satisfies

$$
|f_T(m)-\ell_T|<\delta/3.
$$

Impose the same error requirement on the carousel. Let $M$ be the maximum of these finitely many thresholds. Then

$$
f_*(m)-f_T(m)
>(\ell_*-\delta/3)-(\ell_T+\delta/3)
\ge\delta/3>0.
$$

Finally take the maximum of the four thresholds for two models and two counts. The regular internal-block model uses only odd $m$. This proves existence without inventing a numerical threshold from an ineffective asymptotic theorem.

## A.7 A calculus proof of the trigonometric inequality used in monotonicity

Part I uses $\tan y\ge y+y^3/3$ for $0\le y<\pi/2$. Set $f(y)=\tan y-y$. Then

$$
f'(y)=\tan^2y\ge0,\qquad f(0)=0,
$$

Thus $\tan y\ge y$. Next set $g(y)=\tan y-y-y^3/3$. We have

$$
g'(y)=\tan^2y-y^2\ge0,\qquad g(0)=0.
$$

The desired inequality follows. Moreover,

$$
\alpha(x)=\int_0^1\frac{dt}{1+x^2t^2}
\ge\int_0^1(1-x^2t^2)\,dt=1-x^2/3,
$$

where $(1+z)^{-1}-(1-z)=z^2/(1+z)\ge0$. This supplies the two elementary estimates used in the monotonicity calculation.

## A.8 Review findings and responsibility for the proofs

This review checked the quantifiers, models and Hessian definition in the three original conjectures. It recalculated the Schur complement's second derivatives, the angular minus sign, the factor $d$ in the basis-change determinant, equality transfer in weak majorization, the nonregular branch, path normalization, and the order of the two limits. No error overturning the main formulas or the fixed-base conclusions was found. This appendix expands previously abbreviated calculations without broadening the scope.

The accompanying programs check exact finite identities and finite enumerations, and record high-precision asymptotic diagnostics. They do not replace a proof for arbitrary orders or certify every analytic detail of the external theorems. This manuscript does not claim peer acceptance, formal certification or historical priority.

## References

1. N. C. Wormald. *Tournaments with many Hamilton cycles*. arXiv:2610.16245v1. [Fixed-version full text](https://arxiv.org/html/2610.16245v1); [historical note](https://arxiv.org/abs/2610.16245). We use the model definitions and Theorems 1, 4 and 5, and discuss Conjectures 1, 2 and 6.
2. Yijia Fang and Hao Huang. *Maximizing directed cycles in tournaments*. arXiv:2608.06238v1. [Section 3 of the fixed version](https://arxiv.org/html/2608.06238v1#S3). We use Corollary 3.4; fourth-moment equality is also recalculated in Appendix A.3.
3. Noga Alon. *The maximum number of Hamiltonian paths in tournaments*. Combinatorica 10 (1990), 319–324. [Author's full text](https://www.tau.ac.il/~nogaa/PDFS/hamilton.pdf). We use the Brégman permanent bound stated in Section 2.
