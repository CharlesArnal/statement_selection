# All Mathematical Statements in Algebraic Topology I (MIT 18.905)

## Statement 1: Theorem 1.5
**d^2 = 0.** The composite $S_{n+1}(X) \xrightarrow{d} S_n(X) \xrightarrow{d} S_{n-1}(X)$ is zero.

## Statement 2: Theorem 5.2 (Homotopy Invariance)
If $f_0 \simeq f_1 : X \to Y$ then $f_{0,*} = f_{1,*} : H_n(X) \to H_n(Y)$.

## Statement 3: Corollary 5.5
Homotopy equivalences induce isomorphisms in homology.

## Statement 4: Corollary 5.7
Let X be a contractible space. The augmentation $\epsilon: H_*(X) \to \mathbf{Z}$ is an isomorphism.

## Statement 5: Lemma 4.7
Let $A \subseteq X$ be a subspace. There is a short exact sequence $0 \to S_n(A) \to S_n(X) \to S_n(X,A) \to 0$.

## Statement 6: Lemma 4.8
The boundary map descends to relative chains: $d: S_n(X,A) \to S_{n-1}(X,A)$, and the relative homology $H_n(X,A)$ is well-defined.

## Statement 7: Proposition 5.11
There is a long exact sequence in homology: $\cdots \to H_n(A) \to H_n(X) \to H_n(X,A) \xrightarrow{\partial} H_{n-1}(A) \to \cdots$

## Statement 8: Proposition 5.13
Let $A \subseteq X$ have a neighborhood that deformation retracts to it. Then $H_n(X,A) \cong \widetilde{H}_n(X/A)$.

## Statement 9: Lemma 5.10
If $A \to X$ is a deformation retract, then $H_*(X,A) = 0$.

## Statement 10: Theorem 6.2 (Excision)
Let $U \subseteq A \subseteq X$ with $\bar{U} \subseteq \text{Int}(A)$. Then $H_n(X-U, A-U) \to H_n(X,A)$ is an isomorphism.

## Statement 11: Lemma 8.3 (Locality Principle / Excision reformulation)
Let $\mathcal{U} = \{U_1, U_2\}$ be an open cover of X. Then the inclusion $S_*^{\mathcal{U}}(X) \hookrightarrow S_*(X)$ is a quasi-isomorphism.

## Statement 12: Theorem 9.4 (Mayer-Vietoris)
Let $A, B \subseteq X$ with $\text{Int}(A) \cup \text{Int}(B) = X$. There is a long exact sequence $\cdots \to H_n(A \cap B) \to H_n(A) \oplus H_n(B) \to H_n(X) \xrightarrow{\partial} H_{n-1}(A \cap B) \to \cdots$

## Statement 13: Corollary 10.5
If $m \neq n$, then $S^m$ and $S^n$ are not homotopy equivalent.

## Statement 14: Corollary 10.6
If $m \neq n$, then $\mathbb{R}^m$ and $\mathbb{R}^n$ are not homeomorphic.

## Statement 15: Lemma 11.6
The sequence $H_n(A) \xrightarrow{i_*-j_*} H_n(A) \oplus H_n(B) \to H_n(X) \xrightarrow{\partial} \cdots$ associated to a ladder of long exact sequences is exact.

## Statement 16: Theorem 12.3 (Equivalence of singular and cellular homology)
For a CW complex X, the cellular homology is isomorphic to the singular homology: $H^{CW}_n(X) \cong H_n(X)$.

## Statement 17: Proposition 16.2
Let $k, q \ge 0$. Then $H_q(S^k) \cong \begin{cases} \mathbf{Z} & q = 0 \text{ or } q = k \\ 0 & \text{otherwise} \end{cases}$.

## Statement 18: Theorem 17.1 (Brouwer Fixed Point Theorem)
Every continuous map $f: D^n \to D^n$ has a fixed point.

## Statement 19: Theorem 22.1 (Fundamental Theorem of Homological Algebra)
Let $\epsilon: M \to N$ be a map of R-modules. Let $E_* \to M$ be a projective resolution and $F_* \to N$ any resolution. Any map $f: M \to N$ lifts to a chain map $E_* \to F_*$, unique up to chain homotopy.

## Statement 20: Corollary 23.13
Let $i \mapsto C(i)$ be a directed system of chain complexes. Then there is a natural isomorphism $\varinjlim_i H_n(C(i)) \cong H_n(\varinjlim_i C(i))$.

## Statement 21: Corollary 23.14
Let $C_*$ be a chain complex of R-modules. The canonical map $\mathbf{Z} \otimes_\mathbf{Z} C_* \to C_*$ is an isomorphism, and $H_n(X; \mathbf{Z}) \cong H_n(X)$.

## Statement 22: Theorem 24.1 (Universal Coefficient Theorem)
Let R be a PID and $C_*$ a chain complex of free R-modules. Then there is a natural short exact sequence $0 \to H_n(C_*) \otimes M \xrightarrow{\alpha} H_n(C_* \otimes M) \xrightarrow{\partial} \text{Tor}_1^R(H_{n-1}(C_*), M) \to 0$ that splits (but not naturally).

## Statement 23: Theorem 25.2 (Algebraic Kunneth Theorem)
Let R be a PID and $C_*, D_*$ be chain complexes of R-modules with $C_n$ free for all n. There is a short exact sequence $0 \to \bigoplus_{p+q=n} H_p(C) \otimes H_q(D) \to H_n(C_* \otimes D_*) \to \bigoplus_{p+q=n-1} \text{Tor}_1^R(H_p(C), H_q(D)) \to 0$ that splits (but not naturally).

## Statement 24: Corollary 25.3
Let R be a PID and assume $C'_n$ and $C_n$ are R-free for all n. If $C'_* \to C_*$ and $D'_* \to D_*$ are homology isomorphisms then so is $C'_* \otimes D'_* \to C_* \otimes D_*$.

## Statement 25: Lemma 25.10
Let $\mathcal{C}$ be a category with models $\mathcal{M}$. If F is $\mathcal{M}$-free, $G' \to G$ is an $\mathcal{M}$-epimorphism, and $f: F \to G$ is any natural transformation, then there is a lifting $\bar{f}: F \to G'$.

## Statement 26: Theorem 25.11 (Acyclic Models)
Let $\mathcal{M}$ be a set of models in a category $\mathcal{C}$. Let $F_*$ and $G_*$ be functors from $\mathcal{C}$ to chain complexes with augmentations. Assume $F_n$ is $\mathcal{M}$-free for all n, and $G_* \to G \to 0$ is $\mathcal{M}$-exact. Then there is a unique chain homotopy class of chain maps $F_* \to G_*$ covering a given natural transformation $F \to G$.

## Statement 27: Corollary 25.12
Under the hypotheses of the Acyclic Models theorem, if $\theta$ is a natural isomorphism, each $G_n$ is $\mathcal{M}$-free, and $F_* \to F \to 0$ is $\mathcal{M}$-exact, then any natural chain map $F_* \to G_*$ covering $\theta$ is a natural chain homotopy equivalence.

## Statement 28: Theorem 25.13 (Eilenberg-Zilber Theorem)
There are unique chain homotopy classes of natural chain maps $S_*(X) \otimes S_*(Y) \leftrightarrows S_*(X \times Y)$ covering the usual isomorphism $H_0(X) \otimes H_0(Y) \cong H_0(X \times Y)$, and they are natural chain homotopy inverses.

## Statement 29: Corollary 25.14
There is a canonical natural isomorphism $H(S_*(X) \otimes S_*(Y)) \cong H_*(X \times Y)$.

## Statement 30: Theorem 25.15 (Kunneth Theorem for Spaces)
Take coefficients in a PID R. There is a short exact sequence $0 \to \bigoplus_{p+q=n} H_p(X) \otimes_R H_q(Y) \to H_n(X \times Y) \to \bigoplus_{p+q=n-1} \text{Tor}_1^R(H_p(X), H_q(Y)) \to 0$ natural in X, Y, that splits but not naturally.

## Statement 31: Corollary 26.2
Suppose R is a PID and $H_*(X;R)$ is free over R. Then $H_*(X;R)$ has the natural structure of a commutative graded coalgebra over R.

## Statement 32: Lemma 26.6
$H^0(X; N) = \text{Map}(\pi_0(X), N)$.

## Statement 33: Theorem 27.1 (Mixed Variance Universal Coefficient Theorem)
Let R be a PID and N an R-module, and let $C_*$ be a chain complex of free R-modules. Then there is a short exact sequence $0 \to \text{Ext}_R^1(H_{n-1}(C_*), N) \to H^n(\text{Hom}_R(C_*, N)) \to \text{Hom}_R(H_n(C_*), N) \to 0$ natural in $C_*$ and N, that splits (but not naturally).

## Statement 34: Proposition 28.3
Let $f \in S^p(X)$, $g \in S^q(Y)$, and $h \in S^r(Z)$, and let $\sigma: \Delta^{p+q+r} \to X \times Y \times Z$. Then $((f \times g) \times h)(\sigma) = (f \times (g \times h))(\sigma)$. (Associativity of the cohomology cross product.)

## Statement 35: Proposition 29.2
The cohomology cross product $\times: H^*(X) \otimes H^*(Y) \to H^*(X \times Y)$ is an R-algebra homomorphism.

## Statement 36: Corollary 29.4
Let $p, q > 0$. Any map $S^{p+q} \to S^p \times S^q$ induces the zero map in $H^{p+q}(-)$.

## Statement 37: Theorem 30.2 (Poincare Duality over F_2)
Let M be a compact manifold of dimension n. There exists a unique class $[M] \in H_n(M)$ such that for every p, q with p + q = n the pairing $H^p(M) \otimes H^q(M) \xrightarrow{\cup} H^n(M) \xrightarrow{\langle -, [M] \rangle} \mathbf{F}_2$ is perfect.

## Statement 38: Lemma 30.5
The restriction of a nondegenerate bilinear form on V to a subspace W is nondegenerate exactly when $W \cap W^{\perp} = 0$. In that case $W^{\perp}$ is also nondegenerate, and $V \cong W \oplus W^{\perp}$ respects the forms.

## Statement 39: Proposition 30.6
Any finite dimensional nondegenerate symmetric bilinear form over $\mathbf{F}_2$ splits as an orthogonal direct sum of forms with matrices [1] and $\begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$.

## Statement 40: Claim 30.7
$\begin{bmatrix} 1 & & \\ & 1 & \\ & & 1 \end{bmatrix}$ with an off-diagonal 1 is similar to the diagonal $\begin{bmatrix} 1 & & \\ & 1 & \\ & & 1 \end{bmatrix}$, i.e., the relation $I + H = 3I$ in the monoid of bilinear forms over $\mathbf{F}_2$.

## Statement 41: Proposition 30.8
There is an isomorphism $H^1(\Sigma_1 \# \Sigma_2) \cong H^1(\Sigma_1) \oplus H^1(\Sigma_2)$ compatible with the intersection forms.

## Statement 42: Theorem 30.9 (Classification of Surfaces)
Formation of the intersection bilinear form gives an isomorphism of commutative monoids $\text{Surf} \to \text{Bil}$.

## Statement 43: Lemma 31.4
If $\pi$ acts principally on X then the orbit projection map $X \to \pi \backslash X$ is a covering space.

## Statement 44: Theorem 31.5 (Unique Path Lifting)
Let $p: E \to B$ be a covering space, and $\omega: I \to B$ a path in the base. For any $e \in E$ such that $p(e) = \omega(0)$, there is a unique path $\widetilde{\omega}: I \to E$ such that $p\widetilde{\omega} = \omega$ and $\widetilde{\omega}(0) = e$.

## Statement 45: Theorem 31.6 (Classification of Covering Spaces)
Assume that B is semi-locally simply connected. Then the functor $\mathbf{Cov}_B \to \mathbf{Set}\text{-}\pi_1(B, b)$ is an equivalence of categories.

## Statement 46: Theorem 31.7 (Local Coefficient Systems Classification)
Let B be path connected and semi-locally simply connected. Then forming the fiber over a point gives an equivalence of categories from local coefficient systems of R-modules over B and R[$\pi_1(B,b)$]-modules.

## Statement 47: Theorem 31.9 (Orientation Theorem)
If M is compact, the map $j: H_n(M; R) \to \Gamma(M; o_M \otimes R)$ is an isomorphism.

## Statement 48: Corollary 31.10
If M is a compact connected n-manifold, then $H_n(M;R) \cong R$ if M is orientable, and $H_n(M;R) \cong R[2]$ if not.

## Statement 49: Theorem 32.1
Let M be an n-manifold and A a compact subset. Then $H_q(M|A;R) = 0$ for $q > n$, and $j_A: H_n(M|A;R) \to \Gamma(A; o_M \otimes R)$ is an isomorphism.

## Statement 50: Proposition 32.2
Let A and B be closed subspaces of M. If the orientation theorem holds for A, B, and $A \cap B$, then it holds for $A \cup B$.

## Statement 51: Proposition 32.3
Let $A_1 \supseteq A_2 \supseteq \cdots$ be a decreasing sequence of compact subsets of M. If the orientation theorem holds for each $A_n$, then it holds for $A = \bigcap A_i$.

## Statement 52: Lemma 32.4
Let $A_1 \supseteq A_2 \supseteq \cdots$ be a decreasing sequence of compact subsets of X with intersection A. Then $\varinjlim_i H_q(X, X - A_i) \xrightarrow{\cong} H_q(X, X - A)$.

## Statement 53: Lemma 32.5
Let $A_1 \supseteq A_2 \supseteq \cdots$ be a decreasing sequence of compact subsets in a Hausdorff space X with intersection A. For any open neighborhood U of A there exists i such that $A_i \subseteq U$.

## Statement 54: Claim 33.1
$\langle f^*b, x \rangle = \langle b, f_*x \rangle$ (naturality of Kronecker pairing).

## Statement 55: Lemma 33.2
Let $a \in H^p(X), b \in H^q(Y), x \in H_p(X), y \in H_q(Y)$. Then $\langle a \times b, x \times y \rangle = (-1)^{|x| \cdot |b|} \langle a, x \rangle \langle b, y \rangle$.

## Statement 56: Theorem 33.3 (Kunneth Theorem in Cohomology)
Let R be a PID. Assume $H_p(X)$ is a finitely generated free R-module for all p. Then $\times: H^*(X;R) \otimes_R H^*(Y;R) \to H^*(X \times Y;R)$ is an isomorphism.

## Statement 57: Proposition 34.1
The cap product enjoys the following properties: (1) $(a \cup b) \cap x = a \cap (b \cap x)$ and $1 \cap x = x$; (2) $f_*(f^*(b) \cap x) = b \cap f_*(x)$ (projection formula); (3) $\varepsilon(b \cap x) = \langle b, x \rangle$; (4) $\langle a \cap b, x \rangle = \langle a, b \cap x \rangle$.

## Statement 58: Theorem 34.2 (Poincare Duality)
Let M be a compact oriented n-manifold over a PID R. Then $- \cap [M]: H^p(M;R) \to H_q(M;R)$, $p+q=n$, is an isomorphism for all p.

## Statement 59: Lemma 34.3
Let $K \subseteq V \subseteq U \subseteq X$, with K closed and U, V open. Then restriction from $H^p(U)$ to $H^p(V)$ is compatible with the cap product action on $H_*(X, X - K)$.

## Statement 60: Lemma 34.5
Under regular neighborhood conditions, $\check{H}^*(K) \to H^*(K)$ is an isomorphism.

## Statement 61: Theorem 34.6
Let X be a compact subset of Euclidean space that is a retract of an open neighborhood. Then $\check{H}^*(X;R)$ is canonically isomorphic to Cech cohomology and is independent of the embedding.

## Statement 62: Theorem 35.2 (Long Exact Sequence for Cech Cohomology)
Let (K, L) be a closed pair in X. There is a long exact sequence $\cdots \to \check{H}^p(K,L) \to \check{H}^p(K) \to \check{H}^p(L) \xrightarrow{\delta} \check{H}^{p+1}(K,L) \to \cdots$.

## Statement 63: Theorem 35.3 (Excision for Cech Cohomology)
Suppose A and B are closed subsets of a normal space, or compact subsets of a Hausdorff space. Then $\check{H}^p(A \cup B, A) \xrightarrow{\cong} \check{H}^p(B, A \cap B)$.

## Statement 64: Lemma 35.7
If $\varphi: \mathcal{J} \to \mathcal{I}$ is cofinal then $\varinjlim_{\mathcal{J}} A\varphi \to \varinjlim_{\mathcal{I}} A$ is an isomorphism.

## Statement 65: Lemma 35.8
Under normality or compactness conditions, the order-preserving maps $\mathcal{U}_{(A \cup B,B)} \leftarrow \mathcal{U}_A \times \mathcal{U}_B \rightarrow \mathcal{U}_{(A,A \cap B)}$ are both cofinal.

## Statement 66: Corollary 35.9 (Mayer-Vietoris for Cech Cohomology)
Suppose A and B are closed in a normal space or compact in a Hausdorff space. There is a natural long exact Mayer-Vietoris sequence for Cech cohomology.

## Statement 67: Theorem 36.1 (Fully Relative Cap Product)
Let $L \subseteq K$ be closed subspaces of X. There is a fully relative cap product $\cap: \check{H}^p(K,L) \otimes H_n(X,X-K) \to H_q(X-L,X-K)$ such that appropriate ladders commute.

## Statement 68: Theorem 36.2
The Cech cohomology and singular homology Mayer-Vietoris sequences are compatible: for closed or compact A, B, there is a commutative ladder with cap product maps as rungs.

## Statement 69: Theorem 37.1 (Fully Relative Poincare Duality)
Let M be an n-manifold and $K \supseteq L$ a pair of compact subsets with R-orientation along K. Then $\cap [M]_K: \check{H}^p(K,L;R) \to H_q(M-L,M-K;R)$ is an isomorphism.

## Statement 70: Lemma 37.2
Let $A_1 \supseteq A_2 \supseteq \cdots$ be a decreasing sequence of compact subspaces of M. Then $\check{H}^p(A_k) \to \check{H}^p(A)$ is an isomorphism.

## Statement 71: Corollary 37.3
If M is a compact R-oriented n-manifold and L is closed, then there is a commuting ladder of isomorphisms relating Cech cohomology and singular homology.

## Statement 72: Corollary 37.4
If M is an n-manifold and K is compact with R-orientation along K, then $\cap [M]_K: \check{H}^p(K;R) \to H_q(M,M-K;R)$ is an isomorphism.

## Statement 73: Corollary 37.5 (Poincare Duality)
Let M be a compact R-oriented n-manifold. Then $\cap [M]: H^p(M;R) \to H_{n-p}(M;R)$ is an isomorphism.

## Statement 74: Theorem 38.1
Let M be an n-manifold and K a compact subset. An R-orientation along K determines a fundamental class $[M]_K$, and capping gives an isomorphism $\cap [M]_K: \check{H}^{n-q}(K;R) \xrightarrow{\cong} H_q(M,M-K;R)$.

## Statement 75: Corollary 38.2
$\check{H}^p(K;R) = 0$ for $p > n$.

## Statement 76: Theorem 38.4 (Alexander Duality)
For any compact subset K of $\mathbb{R}^n$, the composite $\check{H}^{n-q}(K;R) \xrightarrow{\cap [\mathbf{R}^n]_K} H_q(\mathbf{R}^n, \mathbf{R}^n - K; R) \xrightarrow{\partial} \widetilde{H}_{q-1}(\mathbf{R}^n - K; R)$ is an isomorphism.

## Statement 77: Corollary 38.5
If K is a compact subset of $\mathbb{R}^n$ then $\check{H}^n(K;R) = 0$.

## Statement 78: Corollary 38.6
The complement of a knot in $S^3$ is a homology circle.

## Statement 79: Theorem 38.8
Let R be a PID and M a compact R-oriented n-manifold. Then $a \otimes b \mapsto \langle a \cup b, [M] \rangle$ induces a perfect pairing $\frac{H^p(M;R)}{\text{tors}} \otimes_R \frac{H^q(M;R)}{\text{tors}} \to R$.

## Statement 80: Theorem 38.11 (Borsuk-Ulam)
For any continuous function $f: S^n \to \mathbb{R}^n$, there exists $x \in S^n$ such that $f(x) = f(-x)$.
