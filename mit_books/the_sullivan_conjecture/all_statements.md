# All Statements from *Topics in Algebraic Topology: The Sullivan Conjecture* (18.917, Fall 2007)

This document catalogs every Theorem, Lemma, Proposition, Corollary, Conjecture, and Scholium from the textbook. Definitions, Examples, Remarks, Exercises, Warnings, and Notation entries are excluded.

---

## Lecture 1: Introduction

### Conjecture 6 (Sullivan) [line 88]
Let p be a prime number. Let M be a topological space with an action of a finite p-group G. Assume that M is sufficiently nice (for simplicity, a simply connected finite G-CW complex). Then the canonical map $M^G \to (M^\vee)^{hG}$ induces an isomorphism on mod-p cohomology.

### Theorem 7 (Miller) [line 96]
Let M be a finite dimensional CW complex, and let G be a finite group. Then the space of maps Map(BG, M) is homotopy equivalent to M.

### Theorem 9 (Lannes) [line 122]
Let p be a prime number, and let V be an elementary abelian p-group. There exists a functor $T_V : \mathcal{U} \to \mathcal{U}$ with many pleasant properties: (1) The functor $T_V$ is exact. (2) The functor $T_V$ commutes with tensor products. (3) The functor $T_V$ commutes with suspension. (4) For every topological space Y, there is a canonical map $T_V \operatorname{H}^*(Y; \mathbf{Z}/p\mathbf{Z}) \to \operatorname{H}^*(\operatorname{Map}(BV, Y), \mathbf{Z}/p\mathbf{Z})$. Moreover, this map is an isomorphism if Y is a sufficiently nice p-complete space.

---

## Lecture 2: Steenrod Operations

### Proposition 13 [line 293]
The Steenrod squares are additive operations. Let V be a complex, and let $v, v' \in H^n V$. Then, for each integer k, we have $\overline{\operatorname{Sq}}^k(v+v') = \overline{\operatorname{Sq}}^k(v) + \overline{\operatorname{Sq}}^k(v') \in \operatorname{H}^{n+k}D_2(V)$. In particular, if V is equipped with a symmetric multiplication, we have $\operatorname{Sq}^{k}(v + v') = \operatorname{Sq}^{k}(v) + \operatorname{Sq}^{k}(v') \in \operatorname{H}^{n+k} V$.

---

## Lecture 3: Stability and the Cartan Formula

### Proposition 1 [line 343]
Let W be a complex and k an integer. Then the diagram $H^{*}(\Omega W) \xrightarrow{\sim} H^{*-1}(W)$ $\downarrow^{\overline{\operatorname{Sq}}^{k}} \qquad \downarrow^{\overline{\operatorname{Sq}}^{k}}$ $H^{*+k}(D_{2}(\Omega W)) \xrightarrow{\sim} H^{*+k}(\Omega(D_{2}W)) \xrightarrow{\sim} H^{*+k-1}(D_{2}(W))$ is commutative.

### Corollary 2 [line 407]
Let V be a complex equipped with a symmetric multiplication. Then $\Omega V$ inherits a symmetric multiplication. Moreover, the canonical isomorphism $H^* V \simeq H^{*+1}(\Omega V)$ commutes with the Steenrod operations $Sq^k$.

### Corollary 3 [line 413]
Let X be a pointed topological space, and $\Sigma X$ its suspension. Then the canonical isomorphism $\mathrm{H}^*(X; \mathbf{F}_2) \simeq \mathrm{H}^{*+1}(\Sigma X; \mathbf{F}_2)$ commutes with the action of the Steenrod operations $Sq^k$.

### Corollary 5 [line 427]
Let X be a topological space, and let $v \in H^n(X; \mathbf{F}_2)$. Then $\operatorname{Sq}^{k}(x) = x$ if $k = 0$, and $\operatorname{Sq}^{k}(x) = 0$ if $k < 0$.

### Proposition 7 [line 462]
Let V and W be complexes. Let $v \in H^m V$, $w \in H^n W$, so that we can form a class $v \otimes w \in H^{m+n}(V \otimes W)$. For every integer k, we have an equality $\psi \overline{\operatorname{Sq}}^{k}(v \otimes w) = \sum_{k=k'+k''} \overline{\operatorname{Sq}}^{k'}(v) \otimes \overline{\operatorname{Sq}}^{k''}(w)$ in the cohomology group $H^{m+n+k}(D_2(V) \otimes D_2(W))$.

### Corollary 9 [line 514]
Let V be a complex equipped with a good symmetric multiplication. Then, for every pair of elements $v, w \in H^*(V)$, the Cartan formula holds: $\operatorname{Sq}^{k}(vw) = \sum_{k=k'+k''} \operatorname{Sq}^{k'}(v) \operatorname{Sq}^{k''}(w)$.

### Corollary 10 [line 518]
Let X be a topological space, and let $x, y \in H^*(X; \mathbf{F}_2)$. Then, for each $n \geq 0$, $\operatorname{Sq}^{n}(xy) = \sum_{n=n'+n''} \operatorname{Sq}^{n'}(x) \operatorname{Sq}^{n''}(y)$.

### Corollary 11 [line 526]
Let $H^*(\mathbf{R}P^{\infty}; \mathbf{F}_2) = \mathbf{F}_2[t]$. Then the action of the Steenrod algebra on $\mathbf{F}_2[t]$ can be described by the following formula: $\operatorname{Sq}^k t^n = \binom{n}{k} t^{n+k}$.

---

## Lecture 4: The Adem Relations

### Proposition 5 (Adem Relations) [line 586]
Let V be a complex equipped with a good symmetric multiplication, and let $v \in H^n(V)$. For any pair of integers a < 2b, we have $\operatorname{Sq}^{a} \operatorname{Sq}^{b}(v) = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}(v)$.

### Lemma 13 [line 624]
Let p and q be positive integers, let V be a complex with a good symmetric multiplication, and let $v \in H^n(V)$. Then we have an equality $\sum_{l} (p - 2l, l) \operatorname{Sq}^{2n - q - l} \operatorname{Sq}^{n - p + l}(v) = \sum_{l'} (q - 2l', l') \operatorname{Sq}^{2n - p - l'} \operatorname{Sq}^{n - q - l'}(v)$ in $H^{4n-p-q}(V)$.

### Lemma 14 [line 662]
Let V be a complex, let p and q be positive integers, and let $v \in H^n(V)$. Then the sums $\sum_{l} (p-2l, l) \overline{\operatorname{Sq}}^{2n-q-l} \overline{\operatorname{Sq}}^{n-p+l}(v) \in \operatorname{H}^{4n-p-q}(D_2(D_2(V)))$ and $\sum_{l'} (q - 2l', l') \, \overline{\mathrm{Sq}}^{2n - p - l'} \, \overline{\mathrm{Sq}}^{n - p + l'}(v) \in \mathrm{H}^{4n - p - q}(D_2(D_2(V)))$ have the same image in $H^{4n-p-q}(D_4(V))$ under the map $\phi: D_2(D_2(V)) \to D_4(V)$.

### Lemma 15 [line 680]
Let p and q be positive integers. Then the expressions $\sum_{l} (p - 2l, l) \, \overline{\mathrm{Sq}}^{-q - l} \, x_{p - l} \in \mathrm{H}_{p + q}(BG)$ and $\sum_{l} (q - 2l', l') \overline{\operatorname{Sq}}^{-p-l'} x_{q-l'} \in H_{p+q}(BG)$ have the same image in $H_{p+q}(B\Sigma_4)$.

---

## Lecture 5: The Adem Relations (Continued)

### Proposition 3 [line 806]
Let V be a complex equipped with a symmetric multiplication, and let $v \in H^n(V)$. Then: (1) If $k \geq n$, then $S^k(v) \in H^{n+k}(D^2(V))$ has image $\sum_{l} \operatorname{Sq}^{l}(v) t^{k-l} \in \operatorname{H}^{*}(V)[t]$. (2) For all integers k, the element $S^k(v) \in H^{n+k}(D^T(V))$ has image $\sum_{l} \operatorname{Sq}^{l}(v) t^{k-l} \in \operatorname{H}^{*}(V)[t, t^{-1}]$.

### Corollary 4 [line 844]
The inclusion $j: \Sigma_2 \times \Sigma_2 \to G$ induces a restriction map on cohomology $H^*(BG) \to H^*(\Sigma_2 \times \Sigma_2) \simeq \mathbf{F}_2[t,u]$. For $k \geq n$, this map carries $S^k(u^n) \in H^{m+k}(BG)$ to $\sum_{n} (n-l,l)u^{n+l}t^{k-l}$.

### Corollary 5 [line 854]
The inclusion $j: \Sigma_2 \times \Sigma_2 \to G$ induces a map on homology $H_*(\Sigma_2 \times \Sigma_2) \to H_*(G)$ which is described by the formula $x_p \otimes x_q \mapsto \sum_{l} (p - 2l, l) \overline{\operatorname{Sq}}^{-q - l} x_{p - l}$.

---

## Lecture 6: Admissible Monomials

### Proposition 1 [line 907]
The big Steenrod algebra $A^{Big}$ is spanned (as an $\mathbf{F}_2$-vector space) by the admissible monomials $\operatorname{Sq}^I$. The usual Steenrod algebra A is spanned by the admissible monomials $\operatorname{Sq}^I$ where I is a sequence of positive integers.

### Scholium 2 [line 947]
Let $\mathcal{B}$ be the subspace of $\mathcal{A}^{\text{Big}}$ generated by $\text{Sq}^{I}$, where $I = (i_n, \dots, i_0)$ is an admissible sequence of nonpositive integers. Then $\mathcal{B}$ is a subalgebra of $\mathcal{A}^{\text{Big}}$.

### Proposition 3 [line 957]
The admissible monomials $\operatorname{Sq}^I$ form a basis for the big Steenrod algebra $\mathcal{A}^{Big}$. The admissible monomials of the form $\operatorname{Sq}^I$, where I is a sequence of positive integers, form a basis for the usual Steenrod algebra $\mathcal{A}$.

### Lemma 4 [line 963]
Let M be an unstable $\mathcal{A}^{Big}$-module, and let $I = (i_n, \ldots, i_0)$ be an admissible sequence of integers. Then $\operatorname{Sq}^I(m)$ vanishes whenever the excess of I is larger than the degree of m.

### Proposition 5 [line 977]
Let n be an integer. Then: (1) The free unstable $A^{Big}$-module $F^{Big}(n)$ has a basis consisting of elements $Sq^{I}\overline{\nu}_{n}$, where I is an admissible sequence of excess $\leq n$. (2) The free unstable A-module F(n) has a basis consisting of elements $\operatorname{Sq}^{I} \nu_{n}$, where I is an admissible sequence of positive integers of excess $\leq n$.

### Lemma 6 [line 995]
Let n and p be integers. Then there is a canonical isomorphism of vector spaces $\phi: \mathcal{F}^{Big}(n) \to \mathcal{F}^{Big}(n+p)$ described by the formula $\operatorname{Sq}^{i_m} \dots \operatorname{Sq}^{i_1} \operatorname{Sq}^{i_0} \overline{\nu}_n \mapsto \operatorname{Sq}^{i_m + 2^k p} \dots \operatorname{Sq}^{i_1 + 2p} \operatorname{Sq}^{i_0 + p} \overline{\nu}_{n+n}$.

---

## Lecture 7: Free Modules

### Proposition 1 [line 1067]
Let F(n) denote the free unstable A-module generated by one generator $\nu_n$ in degree n. Then the collection of elements $\{\operatorname{Sq}^I\nu_n\}$ is linearly independent in F(n), where I ranges over admissible sequences of positive integers having excess $\leq n$.

### Proposition 2 [line 1098]
The expressions $\{\operatorname{Sq}^I(x)\}$ form a basis for M, where I ranges over admissible sequences of positive integers having excess $\leq n$.

### Proposition 3 [line 1122]
Let $\epsilon \in E$. Then $\operatorname{Sq}^{I(\epsilon)}(x) = f_{\epsilon} + \sum_{\alpha} f_{\alpha}$ where $\alpha$ ranges over some subset of $\{\epsilon' \in E : \epsilon' < \epsilon\}$.

### Proposition 6 [line 1174]
Let n be a positive integer. Then the natural transformations $\{Sq^I\}$ form a basis for $Hom_{Fun}(Sym^n, Sym^*)$, where I ranges over positive admissible sequences of excess $\leq n$.

---

## Lecture 8: A Theorem of Gabriel-Kuhn-Popesco

### Theorem 5 (Kuhn, Gabriel-Popesco) [line 1287]
(1) The functor G admits a left adjoint F. (2) The functor G is fully faithful. (3) The functor F is exact.

### Lemma 7 [line 1301]
Let M be an $\mathbb{R}$-module and let $D \in \mathbb{C}$. If $u : M \to G(D)$ is a monomorphism in $Mod(\mathbb{R})$, then the adjoint map $u' : F(M) \to D$ is a monomorphism in $\mathbb{C}$.

### Corollary 8 [line 1329]
Let $C \in \mathcal{C}$. The counit map $v : FG(C) \to C$ is an isomorphism.

### Corollary 9 [line 1335]
The functor G is fully faithful.

### Lemma 10 [line 1374]
Suppose given an exact sequence of $\mathbb{R}$-modules $\ldots \to P_1 \to P_0 \to N$, where each $P_i$ is free. Then the induced sequence $\ldots \to F(P_1) \to F(P_0) \to F(N)$ is exact in C.

### Lemma 11 [line 1394]
Let P be a free $\mathbb{R}$-module, and let $M \subseteq P$. Then the induced map $F(M) \to F(P)$ is a monomorphism in $\mathbb{C}$.

---

## Lecture 9: The Injectivity of H*(BV)

### Proposition 1 [line 1416]
Let m and n be nonnegative integers. Then $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^m)$ has a basis given by the Steenrod operations $\{\operatorname{Sq}^I\}$, where I ranges over positive admissible sequences of degree m-n and excess $\leq n$.

### Proposition 2 [line 1422]
Let m and n be nonnegative integers. Then there is a canonical isomorphism $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n, \operatorname{Sym}^m) \simeq \operatorname{Hom}_{\mathcal{A}}(F(m), F(n))$.

### Proposition 5 [line 1454]
Let m and n be nonnegative integers. Then there is a canonical isomorphism $\operatorname{Hom}_{\operatorname{Fun}}(\Gamma^m, \Gamma^n) \simeq \operatorname{Hom}_{\mathcal{A}}(F(m), F(n))$.

### Proposition 13 [line 1515]
The category $\operatorname{Fun}^{an}$ is generated (under colimits) by the objects $\{\Gamma^n\}_{n \geq 0}$.

### Corollary 14 [line 1519]
The adjoint functors F and G (between $\mathcal{U}$ and $\operatorname{Fun}$) restrict to give adjoint functors between $\mathcal{U}$ and $\operatorname{Fun}^{an}$. Moreover, F is exact and G is fully faithful.

### Corollary 15 [line 1535]
The adjoint functors F and G restrict to give adjoint functors between $\mathcal{U}$ and $\operatorname{Fun}^{an}$.

### Proposition 16 [line 1556]
The functor $I_V$ is analytic.

### Proposition 17 [line 1579]
Let V be a finite dimensional $\mathbf{F}_2$-vector space. Then $H^*(BV)$ is an injective object of $\mathcal{U}$.

---

## Lecture 10: Analytic Functors

### Theorem 1 [line 1593]
The category $\operatorname{Fun}^{an}$ is generated (under colimits) by the divided power functors $\{\Gamma^n\}_{n \geq 0}$.

### Proposition 2 [line 1602]
Every polynomial functor is good.

### Proposition 3 [line 1614]
Let F be a polynomial functor of degree $\leq d$, and suppose that there exists a finite surjection $\bigoplus_{j=1}^{m} \Gamma^{n_j} \to F$. Then there exists a finite surjection $\bigoplus \Gamma^{n} \to F$ with $n \leq d$.

### Proposition 4 [line 1628]
Let F be a polynomial functor. Then there exists a monomorphism $F \hookrightarrow \bigoplus \operatorname{Sym}^{n_j}$ for some finite collection of nonnegative integers $n_j$.

### Proposition 5 [line 1640]
Let F be a polynomial subfunctor of $I_V$. Then there exists an injection $F \hookrightarrow \operatorname{Sym}^m$ for some nonnegative integer m.

### Proposition 6 [line 1662]
There exists an injection into $\operatorname{Sym}^m$.

### Lemma 7 [line 1679]
Locally finite polynomial functors are Noetherian.

### Proposition 8 [line 1692]
$(S^k)^{\otimes n}$ embeds in $\operatorname{Sym}^m$.

### Proposition 9 [line 1696]
There is a monomorphism $S^{k+1} \to \operatorname{Sym}^{2^k}$.

### Lemma 10 [line 1700]
There exists a monomorphism $\operatorname{Sym}^m \otimes \operatorname{Sym}^{m'} \to \operatorname{Sym}^{m''}$.

### Lemma 11 [line 1746]
Let F and F' be nonzero subfunctors of $S^{\infty}$. Then $F \cap F' \neq 0$.

---

## Lecture 11: Tensor Products and Unstable Algebras

### Theorem 2 [line 1804]
The tensor product of two unstable $A^{Big}$-modules is unstable.

### Corollary 3 [line 1854]
The tensor product of two unstable A-modules is unstable.

### Proposition 4 [line 1864]
There is a ring homomorphism $A \to A \otimes A$ (comultiplication) which makes the Steenrod algebra into a cocommutative Hopf algebra.

### Theorem 7 [line 1907]
The free unstable $A^{Big}$-algebra $F_{Alg}^{Big}(n)$ has a basis given by admissible monomials $\operatorname{Sq}^I \overline{\nu}_n$ where I is admissible with excess $\leq n$ and last entry $> n$. The free unstable A-algebra $F_{Alg}(n)$ has a basis given by admissible monomials $\operatorname{Sq}^I \nu_n$ where I is positive admissible with excess $\leq n$ and last entry $> n$.

---

## Lecture 12: Eilenberg-MacLane Spaces

### Proposition 1 [line 1943]
$F_{Alg}(n)$ has a specified basis of admissible monomials.

### Theorem 2 (Cartan-Serre) [line 1957]
The cohomology $H^*(K(\mathbf{F}_2, n); \mathbf{F}_2)$ is isomorphic as an unstable $\mathcal{A}$-algebra to $F_{Alg}(n)$.

### Corollary 3 [line 1959]
The map $F_{Alg}(n) \to H^*(K(\mathbf{F}_2,n))$ is an isomorphism.

### Theorem 4 [line 2001]
$H^*(K(\mathbf{F}_2,n))$ is a polynomial ring on specified generators.

---

## Lecture 13: The Dual Steenrod Algebra

### Proposition 1 [line 2134]
The map $\phi: G \to H_{\infty}$ is a monomorphism.

### Theorem 2 [line 2182]
The map $\phi$ induces an isomorphism $G \to \operatorname{End}(A^1)$.

### Corollary 4 [line 2212]
The dual Steenrod algebra $\mathcal{A}_*$ is a polynomial ring $\mathbf{F}_2[\xi_1, \xi_2, \ldots]$ where $\xi_i$ has degree $2^i - 1$.

---

## Lecture 14: The Frobenius and Verschiebung

### Proposition 1 [line 2274]
The Verschiebung map satisfies $V(\operatorname{Sq}^k(m)) = \operatorname{Sq}^{k/2}(m)$ if k is even, and 0 if k is odd.

### Proposition 3 [line 2295]
There is a canonical homomorphism $\Phi M \to M$ for every unstable module M.

### Proposition 5 [line 2333]
The map $f: \Phi F(n) \to F(n)$ is injective, with image described explicitly.

### Proposition 8 [line 2354]
There is a short exact sequence $0 \to \Phi F(n) \to F(n) \to \Sigma\Omega F(n) \to 0$.

### Theorem 9 [line 2367]
There is an exact sequence involving the derived functors of $\Omega$: $\ldots \to \Omega_s \Phi M \to \Omega_s M \to \Omega_{s-1} \Sigma \Omega M \to \ldots$

---

## Lecture 15: Noetherian Properties

### Theorem 4 [line 2419]
The category $\mathcal{U}$ of unstable modules over the Steenrod algebra is locally Noetherian.

### Lemma 5 [line 2425]
An object M of $\mathcal{U}$ is Noetherian if and only if every submodule of M is finitely generated.

### Theorem 6 [line 2439]
Every submodule of $F(n)$ is finitely generated.

### Lemma 7 [line 2443]
If $\Omega M$ is finitely generated and $M^0$ is finitely generated, then M is finitely generated.

### Proposition 8 [line 2493]
Finitely generated unstable modules are closed under tensor products.

### Proposition 9 [line 2497]
$F(m) \otimes F(n)$ is finitely generated.

### Proposition 10 [line 2510]
$F(1)^{\otimes n}$ is finitely generated.

---

## Lecture 16: Brown-Gitler Modules and Carlsson Modules

### Proposition 1 [line 2536]
There exists an unstable module $J(n)$ with the universal property that $\operatorname{Hom}_{\mathcal{U}}(M, J(n)) \simeq (M^n)^{\vee}$ for every unstable module M.

### Corollary 2 [line 2565]
The category $\mathcal{U}$ has enough injective objects.

### Proposition 3 [line 2583]
The inverse limit of Brown-Gitler modules $\varprojlim J(n)$ is injective in $\mathcal{U}$.

### Corollary 5 [line 2612]
The Carlsson module $K(n)$ is injective in $\mathcal{U}$.

### Proposition 6 [line 2616]
The map $\Phi M \to M$ induces an isomorphism $\operatorname{Hom}(M, K(n)) \to \operatorname{Hom}(\Phi M, K(n))$.

### Corollary 7 [line 2620]
$\operatorname{Hom}(\Sigma M, K(n)) = 0$ for every unstable module M.

### Corollary 8 [line 2626]
$K(n)$ is reduced (contains no nonzero suspended submodule).

### Proposition 9 [line 2644]
Every reduced module embeds in a product of Carlsson modules $\prod K(n_\alpha)$.

### Corollary 10 [line 2650]
$H^*(BV)$ is a direct summand of a product of Carlsson modules $\prod K(n_\alpha)$.

### Corollary 11 [line 2662]
$H^*(BV) \otimes J(k)$ is a direct summand of a product of Carlsson modules.

---

## Lecture 17: Injectivity of Tensor Products

### Theorem 1 [line 2684]
$K(n) \otimes J(k)$ is injective in $\mathcal{U}$.

### Lemma 2 [line 2696]
The map $\mu: K(n) \otimes J(k) \to K(n) \otimes J(k)$ is an isomorphism for $p \gg 0$.

### Lemma 3 [line 2769]
For p sufficiently large, there exist unique partitions satisfying certain conditions.

---

## Lecture 18: Lannes' T-functor

### Proposition 2 [line 2805]
The functor $N \mapsto M \otimes N$ admits a left adjoint $D_M$.

### Proposition 6 [line 2856]
Lannes' T-functor $T_V$ is exact.

### Proposition 7 [line 2897]
The submodule $M'$ has properties: it is a submodule of $T_V M$, the form $T_V M = M' \otimes H^*(BV)$, and the adjoint property holds.

### Proposition 8 [line 2923]
The canonical map $T_V \Sigma \to \Sigma T_V$ is an isomorphism: $T_V$ commutes with suspension.

---

## Lecture 19: T-functor and Tensor Products

### Proposition 1 [line 2983]
The canonical map $h_M: T_V \Phi M \to \Phi T_V M$ is an isomorphism.

### Theorem 2 [line 3023]
The canonical map $\mu_{M,N}: T_V(M \otimes N) \to T_V M \otimes T_V N$ is an isomorphism.

### Lemma 5 [line 3046]
The map $T(F(1) \otimes N) \to T(F(1)) \otimes T(N)$ is an isomorphism.

### Lemma 6 [line 3107]
$\Phi^p F(1) \otimes F(n)$ is generated by a single element for $p \gg 0$.

---

## Lecture 20: T-functor and Unstable Algebras

### Lemma 1 [line 3135]
$\Phi^p F(1) \otimes F(n)$ is generated by a single element for $p \gg 0$.

### Proposition 2 [line 3155]
If M is an unstable A-algebra, then $T_V M$ is an unstable A-algebra.

### Proposition 3 [line 3197]
$\operatorname{Hom}_K(T_V M, N) \simeq \operatorname{Hom}_K(M, N \otimes H^*(BV))$ for unstable algebras M and N.

### Corollary 4 [line 3219]
$T_V$ is left adjoint to the functor $N \mapsto N \otimes H^*(BV)$ on the category K of unstable algebras.

### Corollary 5 [line 3221]
$TF_{Alg}(n) \simeq F_{Alg}(n) \otimes \ldots \otimes F_{Alg}(0)$.

---

## Lecture 21: Mapping Spaces

### Theorem 1 [line 3282]
The map $\theta_n: T_V H^*(K(\mathbf{F}_2, n)) \to H^*(\operatorname{Map}(BV, K(\mathbf{F}_2, n)))$ is an isomorphism.

### Lemma 2 [line 3346]
If $|G/H|$ is odd, then the map $p: H_*(BH) \to H_*(BG)$ is an isomorphism on mod-2 homology.

---

## Lecture 22: E-infinity Algebras and Eilenberg-MacLane Spaces

### Theorem 1 [line 3424]
There is a homotopy pushout square of $E_\infty$-algebras associated to the free $E_\infty$-algebra on a generator.

### Lemma 2 [line 3453]
If M is a free $H^*R$-module, then the Kunneth isomorphism holds.

### Proposition 3 [line 3477]
$H^* F(n)$ is a polynomial ring on specified generators.

### Lemma 4 [line 3500]
$\operatorname{Sq}^I \operatorname{Sq}^0$ satisfies a specified formula.

### Lemma 5 [line 3538]
$\operatorname{Sq}^I \mu$ lies in the image of $\theta$.

### Corollary 6 [line 3554]
There is a homotopy pushout of $E_\infty$-algebras arising from $K(\mathbf{F}_2, n)$.

---

## Lecture 23: p-Finite Spaces

### Lemma 4 [line 3604]
A space X is p-finite if and only if it admits a filtration by principal fibrations with fibers $K(\mathbf{F}_p, n)$.

### Corollary 5 [line 3614]
A p-finite space has finite dimensional mod-p cohomology in each degree.

### Theorem 6 [line 3620]
For a homotopy pullback of p-finite spaces, the corresponding diagram of $E_\infty$-algebras (obtained by applying cochains) is a homotopy pushout.

### Theorem 8 [line 3662]
There is an isomorphism for local systems tensor products: $H^*(X; \mathcal{F} \otimes \mathcal{G}) \simeq H^*(X; \mathcal{F}) \otimes_{H^*(X)} H^*(X; \mathcal{G})$.

---

## Lecture 24: Convergence of the Eilenberg-Moore Spectral Sequence

### Lemma 2 [line 3762]
The exact functor $\alpha$ is a weak equivalence.

### Lemma 3 [line 3794]
The map $E_0 \to E$ induces a weak equivalence on $\operatorname{Map}(\operatorname{id}, -)$.

### Lemma 4 [line 3814]
Goodwillie's lemma about $E'$.

---

## Lecture 25: The Sullivan Conjecture (p-Profinite Case)

### Theorem 2 [line 3944]
The map $\theta_X: T_V H^*(X) \to H^*(X^{BV})$ is an isomorphism for every 2-finite space X.

### Proposition 4 [line 3968]
If $\theta_X$ is an isomorphism for every space in a homotopy pullback diagram of p-finite spaces, then $\theta$ is an isomorphism for the homotopy pullback.

---

## Lecture 26: p-Profinite Spaces

### Proposition 8 [line 4139]
For a p-profinite space X, the mapping space $X^{BV}$ exists as a p-profinite space.

### Theorem 11 [line 4172]
The map $\psi: T_V H^*(X) \to H^*(X^{BV})$ is an isomorphism for every p-profinite space X.

---

## Lecture 27: Cochain Algebras

### Theorem 2 [line 4220]
The functor $X \mapsto C^*(X; k)$ determines a fully faithful embedding from the homotopy category of p-profinite spaces into the homotopy category of $E_\infty$-algebras over k.

### Lemma 3 [line 4228]
The functor F carries homotopy limits to homotopy colimits.

### Lemma 4 [line 4256]
The class K of spaces for which the result holds contains all p-profinite spaces.

---

## Lecture 28: Atomicity

### Theorem 3 [line 4365]
Every connected p-finite space is atomic in the p-profinite category.

### Proposition 4 [line 4369]
The functor $X \mapsto X^{BV}$ preserves homotopy pushouts of p-profinite spaces.

### Proposition 6 [line 4430]
The following conditions on a p-profinite space X are equivalent: (conditions for atomicity).

### Corollary 7 [line 4441]
If $F \to E \to B$ is a fiber sequence with F and B atomic, then E is atomic.

### Corollary 8 [line 4453]
BG is atomic (in the p-profinite category) for every finite p-group G.

---

## Lecture 29: Atomicity of p-Finite Spaces

### Proposition 1 [line 4467]
The functor F carries totalizations to geometric realizations.

### Theorem 3 [line 4492]
Totalization commutes with homotopy pushouts under appropriate conditions.

### Corollary 5 [line 4560]
If each term in a simplicial p-profinite space is atomic, then the geometric realization is atomic.

### Corollary 6 [line 4572]
$K(G, n)$ is atomic for every finite abelian p-group G and $n \geq 1$.

### Theorem 7 [line 4580]
Every connected p-finite space is atomic.

### Proposition 8 [line 4598]
If X is atomic in $\mathfrak{S}_p^{\vee}$, then $X^{BV}$ is contractible in $\mathfrak{S}$ for every nontrivial elementary abelian p-group V.

---

## Lecture 30: The Sullivan Conjecture

### Theorem 1 [line 4644]
Let X be a p-profinite space. Then the diagonal map $X \to X^{BV}$ is an equivalence for every elementary abelian p-group V.

### Corollary 2 [line 4660]
Every map from a connected space K with finite mod-p cohomology into $X^{\vee}$ is homotopic to a constant map.

### Lemma 3 [line 4664]
The functor $X \mapsto X^{hG}$ preserves finite homotopy colimits.

### Theorem 4 [line 4674]
Sullivan's conjecture holds: for a finite p-group G acting on a p-finite space X, the map $X^G \to (X^\vee)^{hG}$ induces an equivalence on mod-p cohomology.

---

## Lecture 31: p-adic Completion

### Theorem 1 [line 4735]
Let X be a simply connected space with finitely generated homotopy groups. Then the p-adic completion $X_p^{\vee}$ has homotopy groups $\pi_n(X_p^{\vee}) \simeq \pi_n(X) \otimes \mathbf{Z}_p$.

### Lemma 2 [line 4743]
There is a pro-isomorphism for $H_i(K(\mathbf{Z}, 1))$.

### Corollary 3 [line 4755]
There is a pro-isomorphism for $K(\mathbf{Z}, n)$.

### Corollary 4 [line 4771]
The cohomology colimit isomorphism holds.

### Corollary 5 [line 4777]
The p-profinite completion of $K(\mathbf{Z}, n)$ is characterized.

### Corollary 6 [line 4783]
The map $K(\mathbf{Z}, n) \to K(\mathbf{Z}_p, 1)$ is a homotopy equivalence after p-adic completion.

### Lemma 7 [line 4787]
Product completion equivalence holds.

### Corollary 8 [line 4795]
$K(A, n)$ completion is characterized for finitely generated abelian groups A.

### Lemma 9 [line 4799]
Homotopy pullbacks are preserved under p-adic completion.

### Proposition 14 [line 4871]
$\mathbf{F}_p$-localization is characterized.

### Lemma 15 [line 4879]
If the order of a group G is invertible in $\mathbf{F}_p$, then homology with $\mathbf{F}_p$ coefficients vanishes.

---

## Lecture 32: Rationalization and the Arithmetic Square

### Theorem 3 [line 4931]
Rationalization of a simply connected space X is characterized: $X_{\mathbf{Q}}$ is simply connected with $\pi_n(X_{\mathbf{Q}}) \simeq \pi_n(X) \otimes \mathbf{Q}$.

### Lemma 4 [line 4938]
If the homotopy groups of X are rational vector spaces, then X is a rational space.

### Lemma 6 [line 4964]
If the homotopy groups of X are torsion groups, then the rational homology of X vanishes.

### Theorem 7 [line 5014]
The arithmetic square $X \to X_{\mathbf{Q}} \times \prod_p X_p^{\vee}$ is a homotopy pullback.

---

## Lecture 33: Applications of the Sullivan Conjecture

### Theorem 1 [line 5044]
Sullivan's conjecture for simply connected finite CW complexes: the canonical map $X \to \operatorname{Map}(BG, X)$ induces an equivalence on mod-p cohomology.

### Proposition 2 [line 5060]
The operations of p-adic completion, rationalization, and adelic completion are good (preserve the relevant structure).

### Lemma 3 [line 5068]
Rational spaces are good: every map from BG to a rational space is nullhomotopic.

### Lemma 4 [line 5120]
$|K'_{\bullet}| \to *$ is an $\mathbf{F}_p$-homology equivalence.

---

## Lecture 34: The Dwyer-Miller-Wilkerson Theorem

### Theorem 1 [line 5162]
(Dwyer-Miller-Wilkerson) If $H^*(X; \mathbf{F}_p) \simeq \mathbf{F}_p[t]$ as a graded ring (with $t$ in degree 2), then $X \simeq BSU(2)_p^{\vee}$.

### Lemma 2 [line 5177]
The action of $\mathcal{A}_p$ on $H^*(X)$ is completely determined.

### Corollary 3 [line 5195]
$H^*(X) \simeq H^*(BSU(2))$ as unstable $\mathcal{A}_p$-algebras.

### Lemma 4 [line 5215]
There exists a map $\beta: B\mathbf{Z}/p\mathbf{Z} \to X$ inducing a nontrivial map on cohomology.

### Theorem 5 [line 5290]
$X \simeq K(\mathbf{Z}_p, 2)_{h\mathbf{Z}/2\mathbf{Z}}$.

---

## Lecture 35: Truncated Modules and Functors

### Proposition 1 [line 5347]
$f(M)(V) = (T_V M)^0$ defines the functor $f$ from unstable modules to analytic functors.

### Proposition 5 [line 5433]
Let $n \geq 0$. (1) For every unstable A-module M, the functor $f_n M \in \operatorname{Fun}_n$ is analytic. (2) The functor $f_n$ determines an adjunction $\mathcal{U} \rightleftarrows \operatorname{Fun}_n^{\operatorname{an}}$. (3) The functor $f_n$ is exact. (4) The functor $g_n$ is fully faithful.

---

## Lecture 36: The Nil-Filtration

### Lemma 2 [line 5541]
Let X be an object of $\mathbb{C}$. The following conditions are equivalent: (1) For every $\mathcal{C}_0$-equivalence $Y \to Y'$, the induced map $\operatorname{Hom}_{\mathcal{C}}(Y',X) \to \operatorname{Hom}_{\mathcal{C}}(Y,X)$ is a bijection. (2) For every object $Z \in \mathcal{C}_0$, we have $\operatorname{Hom}_{\mathcal{C}}(Z,X) = \operatorname{Ext}_{\mathcal{C}}(Z,X) = 0$.

### Proposition 7 [line 5580]
Let C be a Grothendieck abelian category and $C_0 \subseteq C$ a Serre class. Then: (1) The inclusion $C / C_0 \subseteq C$ admits a left adjoint L. (2) The category $\mathcal{C} / \mathcal{C}_0$ is a Grothendieck abelian category. (3) The functor L is exact.

### Proposition 9 [line 5625]
Let $\mathbb{D}$ be a Grothendieck abelian category, and $F: \mathbb{C} \to \mathbb{D}$ a colimit-preserving functor. Then: (1) F factors through $L: \mathfrak{C} \to \mathfrak{C}/\mathfrak{C}_0$ if and only if F carries $C_0$-equivalences to isomorphisms. (2) The factored functor $F'$ is exact if and only if F is exact.

### Corollary 11 [line 5639]
Let $F: \mathcal{C} \to \mathcal{D}$ be an exact, colimit preserving functor between Grothendieck abelian categories. Then: (1) $\mathcal{C}_0 = \ker F$ is a Serre class. (2) F factors through $\mathfrak{C}/\mathfrak{C}_0$. (3) F admits a right adjoint G. (4) The factored functor is an equivalence if and only if G is fully faithful.

### Corollary 12 [line 5650]
The functor $f_n: \mathcal{U} \to \operatorname{Fun}_n$ induces an equivalence of categories $\mathcal{U} / \mathcal{K}_n \simeq \operatorname{Fun}_n$, where $\mathcal{K}_n$ denotes the Serre class consisting of all unstable A-modules M such that $\tau^{\leq n} T_V M$ vanishes for every finite dimensional $\mathbf{F}_2$-vector space V.

### Theorem 13 [line 5654]
For each $n \geq 0$, the Serre class $\mathcal{K}_n \subseteq \mathcal{U}$ is the smallest Serre class containing $\Sigma^{n+1}M$, for every $M \in \mathcal{U}$.

---

## Lecture 37: The Krull Filtration

### Proposition 2 [line 5690]
Let C be a locally Noetherian abelian category. Then: (1) Every object $M \in \mathcal{C}$ admits an injective hull $M \to I$, unique up to noncanonical isomorphism. If M is simple, then I is indecomposable. (2) Every direct sum of injective objects is injective. (3) Every injective object can be decomposed as a direct sum of indecomposable injectives.

### Proposition 9 [line 5718]
Let C be a locally Noetherian abelian category, and let I be an injective object of C. Then exactly one of the following statements holds: (1) I is the injective hull of a simple object $C \in \mathfrak{C}$ (which is determined up to isomorphism). (2) I belongs to $\mathbb{C}/\operatorname{Krull}^0(\mathbb{C})$ (and is injective there).

### Proposition 13 [line 5757]
An unstable A-module M belongs to $\operatorname{Krull}^0(\mathcal{U})$ if and only if M is locally finite.

### Proposition 14 [line 5777]
Let M be an unstable A-module. Then $M \in \text{Krull}^0(\mathfrak{U})$ if and only if $\overline{T}M = 0$.

### Theorem 15 [line 5783]
Every indecomposable injective object of U appears as a summand of $J(m) \otimes (H^*_{red}(B\mathbf{F}_2))^{\otimes n}$ for some integers m and n.

### Proposition 16 [line 5795]
Let M be an unstable A-module. Then $M \in \mathrm{Krull}^n(\mathfrak{U})$ if and only if $\overline{T}^{n+1}M \simeq 0$.

---

## Lecture 38: Epilogue

### Lemma 1 [line 5876]
The canonical functor $f_{\infty}: \mathcal{U} \to \varprojlim_n \operatorname{Fun}_n^{\operatorname{an}}$ is fully faithful.

### Lemma 2 [line 5884]
The Krull filtration $\operatorname{Krull}^0 \subseteq \operatorname{Krull}^1 \subseteq \dots$ on U is exhaustive. In other words, the smallest Serre class containing each $\operatorname{Krull}^i$ is U itself.

### Proposition 4 [line 5922]
The iterated suspension functor $\Sigma^n$ induces an equivalence of categories $\mathcal{U}/\operatorname{Nil}_1 \to \operatorname{Nil}_n/\operatorname{Nil}_{n+1}$.

### Proposition 6 [line 5942]
Let $\operatorname{Mod}_{\Sigma_n}$ denote the category of modules over the group ring $\mathbf{F}_2[\Sigma_n]$. Then the construction $R \mapsto F_R$ defines a functor $\operatorname{Mod}_{\Sigma_n} \to \operatorname{Fun}^{(n)}$. Moreover, the composition $\operatorname{Mod}_{\Sigma_n} \to \operatorname{Fun}^{(n)} \to \operatorname{Fun}^{(n)} / \operatorname{Fun}^{(n-1)}$ is an equivalence of categories.

### Theorem 7 [line 5960]
(1) The category U admits a filtration by Serre classes $\ldots \subseteq Nil_2 \subseteq Nil_1 \subseteq Nil_0 = \mathcal{U}$. Moreover, $\mathcal{U}$ embeds fully faithfully into $\varprojlim \mathcal{U}/\mathrm{Nil}_n$, and the successive quotients $\mathrm{Nil}_n/\mathrm{Nil}_{n+1}$ are equivalent to $\mathrm{Fun}^{\mathrm{an}}$. (2) The Krull filtration on $\mathbb{U}$ induces a filtration on each $\operatorname{Nil}_n/\operatorname{Nil}_{n+1}$, identified with the filtration by polynomial functors. (3) Each successive quotient $\operatorname{Fun}^{(n)}/\operatorname{Fun}^{(n-1)}$ can be identified with the category of representations of $\Sigma_n$ over $\mathbf{F}_2$.

### Theorem 8 [line 5991]
Let G and H be groups and $G \star H$ their free product. Let F be any finite group. Then any homomorphism $\phi : F \to G \star H$ is either conjugate to a homomorphism from F into G or conjugate to a homomorphism from F into H.
