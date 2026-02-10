## Proposition 1.13
Let $F: \mathcal{C} \to \mathcal{D}$ be a functor. If F admits a right adjoint then it preserves colimits, in the sense that if $X: \mathcal{I} \to \mathcal{C}$ is a diagram in $\mathcal{C}$ with colimit cone $X \to c_L$, then $F \circ X \to F(c_L)$ is a colimit cone in $\mathcal{D}$. Dually, if F admits a left adjoint then it preserves limits.

## Lemma 1.14 [Yoneda lemma]
The association $x \mapsto \theta_x$ provides a bijection $\mathcal{C}(c, d) \xrightarrow{\cong} \text{Nat}(\mathcal{C}(d, -), \mathcal{C}(c, -))$ natural in c and d.

## Proposition 2.2
Let C be Cartesian closed. Then for any objects X, Y, Z, we have a natural bijection $C(X \times Y, Z) \cong C(X, Z^Y)$.

## Lemma 2.4
A map in Top is a quotient map if and only if it is an effective epimorphism.

## Proposition 2.7
The category kTop is Cartesian closed.

## Proposition 3.1
(1) Any locally compact Hausdorff space is compactly generated. (2) Any CW complex is compactly generated.

## Theorem 3.2
Let X and Y be CW-complexes with skeleta $Sk_iX$ and $Sk_jY$. Then the k-space product $X \times Y$ admits the structure of a CW complex in which the n-skeleton is $\bigcup_{i+j=n} Sk_iX \times Sk_jY$.

## Theorem 3.3 [Milnor]
If X is a pointed countable CW complex, then $\Omega X$ has the homotopy type of a pointed countable CW complex.

## Proposition 4.4
Let G be a compact Lie group and let $G \supseteq H \supseteq K$ a sequence of closed subgroups (also then compact Lie groups in their own right). Then the projection map between homogeneous spaces $G/K \to G/H$ is a fiber bundle.

## Theorem 4.5 [Ehresmann]
Suppose E and B are smooth manifolds, and let $p: E \to B$ be a smooth map. If p is a proper submersion, then it is a fiber bundle.

## Proposition 4.7 [Miyazaki]
CW-complexes are paracompact.

## Theorem 5.2 [Whitehead's little theorem]
If $f: X \to Y$ is a weak equivalence between CW-complexes, then it is a homotopy equivalence.

## Theorem 5.3
Let $f: X \to Y$ be a map of spaces. There exists a factorization $X \xrightarrow{j} Z \xrightarrow{q} Y$ such that Z is a CW-complex, j is a weak equivalence, and q is a fibration.

## Theorem 5.4
Any space X admits a CW approximation: a weak equivalence $Z \to X$ from a CW complex Z.

## Proposition 6.1
If $i: A \hookrightarrow X$ is a cofibration then it is a closed inclusion, and $(X, A)$ is an NDR pair.

## Theorem 7.1
If $p: E \to B$ is a fibration and B is path connected, then all fibers are homotopy equivalent.

## Theorem 7.3
The projection map from the mapping path space, $N_f \to B$, is a Serre fibration.

## Proposition 7.4
Any map $f: X \to Y$ of pointed spaces factors as $X \xrightarrow{i} N_f \xrightarrow{p} Y$ where i is a homotopy equivalence and p is a Serre fibration.

## Proposition 8.3
$\pi_n(X, x)$ is a group for $n \ge 1$, and is abelian for $n \ge 2$.

## Theorem 8.4
A fiber sequence $F \to E \xrightarrow{p} B$ determines a long exact sequence $\cdots \to \pi_{n+1}(B) \to \pi_n(F) \to \pi_n(E) \to \pi_n(B) \to \pi_{n-1}(F) \to \cdots \to \pi_0(F) \to \pi_0(E)$.

## Lemma 9.7
Let $p: E \to B$ be a Serre fibration with fiber F over the basepoint. The map $p_*: \pi_n(E, F) \to \pi_n(B)$ is an isomorphism for all $n \ge 1$.

## Theorem 10.1
If A is a retract of X then $\pi_n(X, A) = 0$ for all n implies $\pi_n(X) = 0$ for all n.

## Proposition 10.5
If $(X, A)$ is a relative CW complex and $p: E \to B$ is a Serre fibration, any commutative square admits a lift.

## Proposition 10.6
CW-approximation is a functor from the homotopy category of spaces to the homotopy category of CW-complexes, left adjoint to the inclusion.

## Theorem 11.1 [Blakers-Massey]
Let $A$ and $B$ be subcomplexes of a CW complex $X = A \cup B$. Suppose A is (m-1)-connected and B is (n-1)-connected, with $m, n \ge 1$. Then the map $\pi_q(A, A \cap B) \to \pi_q(X, B)$ is an isomorphism for $q < m + n - 1$ and a surjection for $q = m + n - 1$.

## Corollary 11.2 [Freudenthal suspension theorem]
Let X be a (k-1)-connected CW complex with $k \ge 1$. The suspension map $\sigma: \pi_q(X) \to \pi_{q+1}(\Sigma X)$ is an isomorphism for $q < 2k - 1$ and a surjection for $q = 2k - 1$.

## Lemma 12.1
$\pi_1(S^1) = \mathbb{Z}$.

## Theorem 12.2
Let $X$ be a path-connected space that is semi-locally simply connected. Then the universal cover $\widetilde{X}$ exists, is simply connected, and the map $\widetilde{X} \to X$ is a covering space.

## Proposition 12.3
If $X$ is a CW complex, there is a functorial construction producing from $X$ a space $\tau_{\le n} X$ and a map $X \to \tau_{\le n} X$ inducing isomorphisms on $\pi_q$ for $q \le n$ and such that $\pi_q(\tau_{\le n} X) = 0$ for $q > n$.

## Proposition 12.5
Every CW-complex $X$ admits a Postnikov tower, i.e. a sequence of fibrations $\cdots \to X_2 \to X_1 \to X_0$ with compatible maps $X \to X_n$ inducing isomorphisms on $\pi_q$ for $q \le n$.

## Lemma 13.1
The Hurewicz map $h: \pi_n(X) \to H_n(X)$ is a homomorphism.

## Theorem 13.2 [Hurewicz theorem]
If X is path-connected, $\pi_1(X)^{ab} \to H_1(X)$ is an isomorphism. If X is (n-1)-connected for n > 1, $\pi_n(X) \to H_n(X)$ is an isomorphism.

## Corollary 13.3
Let X be a simply connected space. If $\overline{H}_q(X) = 0$ for q < n then X is (n-1)-connected.

## Proposition 13.4
Let $\pi$ be an abelian group and n a positive integer. There is a CW complex M (a Moore space) with $\overline{H}_q(M) = \pi$ if $q = n$ and $0$ otherwise.

## Lemma 14.1
Let n be a positive integer and Y a pointed space with $\pi_q(Y, *) = 0$ for $q \neq n$. Then $\pi_n: [\tau_{\le n}M, Y]_* \to \text{Hom}(\pi, G)$ is an isomorphism.

## Corollary 14.2
For any positive integer n there is a functor Ab $\to$ Ho(CW$_*$) sending $\pi$ to a space of type $K(\pi,n)$, unique up to isomorphism.

## Theorem 14.3
If X is a CW complex, the canonical map $[X, K(\pi, n)] \to H^n(X; \pi)$ is an isomorphism. Cohomology is a representable functor.

## Proposition 15.1
Any Serre fibration is a Hurewicz fibration over a paracompact base.

## Proposition 15.2
The obstruction cochain $\theta_f$ associated to a map $f: X_n \to Y$ is a cocycle in $C^{n+1}(X, A; \pi_n(Y))$.

## Theorem 15.3
Let (X, A) be a relative CW-complex and Y a path-connected simple space. Let $f: X_n \to Y$. Then $f|_{X_{n-1}}$ extends to $X_{n+1}$ if and only if $[\theta_f] \in H^{n+1}(X, A; \pi_n(Y))$ is zero.

## Corollary 15.4
Let Y be a path connected simple space and (X, A) a relative CW complex. If $H^{n+1}(X, A; \pi_n(Y)) = 0$ for all $n \ge 1$ then any map $A \to Y$ extends to $X \to Y$. If moreover $H^n(X, A; \pi_n(Y)) = 0$ for all $n \ge 1$ then the extension is unique up to homotopy rel A.

## Lemma 16.11
Any (numerable) vector bundle $\xi$ admits a metric.

## Corollary 16.12
Any exact sequence $0 \to \xi' \to \xi \to \xi'' \to 0$ of vector bundles (over the same base) splits.

## Theorem 17.2
The functor Vect is I-invariant: $\text{pr}_1: X \times I \to X$ induces an isomorphism $\text{Vect}(X) \to \text{Vect}(X \times I)$.

## Corollary 17.3
Vect is a homotopy functor.

## Theorem 17.6 [Covering space theory]
Suppose X is path-connected and semi-locally simply connected. Then the constructions provide an equivalence of categories between left $\pi_1(X)$-sets and covering spaces of X.

## Theorem 17.9
$\text{Bun}_G$ is I-invariant, and hence is a homotopy functor.

## Theorem 18.3 [Illman]
If G is a compact Lie group and M a smooth manifold on which G acts by diffeomorphisms, then M admits a G-CW structure.

## Theorem 19.1
Let G be a topological group and $\xi: E \downarrow B$ a principal G-bundle with E weakly contractible. For any CW complex X, $[X,B] \to \text{Bun}_G(X)$ is bijective.

## Proposition 19.2
Let E be a weakly contractible G-space. Let (P, A) be a free relative G-CW complex. Then any equivariant map $A \to E$ extends to $P \to E$, uniquely up to equivariant homotopy rel A.

## Theorem 19.3 [Peter-Weyl]
Any compact Lie group admits a finite-dimensional faithful unitary representation.

## Lemma 19.4
Over a compact Hausdorff space, any vector bundle embeds in a trivial bundle.

## Corollary 19.5
Over a compact Hausdorff space, any vector bundle has a complement.

## Lemma 20.4
The classifying space construction sends natural transformations to homotopies.

## Corollary 20.5
An adjoint pair induces a homotopy equivalence on classifying spaces.

## Corollary 20.6
If C contains an initial or terminal object then BC is contractible.

## Theorem 20.7
The natural map $B(C \times D) \to BC \times BD$ is a homeomorphism.

## Proposition 21.3
If G is a Lie group, $B(GG) \to BG$ is a principal G-bundle, and $B(GG)$ is contractible.

## Proposition 21.4
If the open cover $\mathcal{U}$ of X admits a subordinate partition of unity, then $B\check{C}(\mathcal{U}) \to X$ is a homotopy equivalence.

## Theorem 23.1
A filtered complex $F_*C_*$ determines a natural spectral sequence with bigraded groups $E_{s,t}^r$, differentials $d^r$, and isomorphisms $E_{s,t}^{r+1} \cong H_{s,t}(E_{*,*}^r, d^r)$.

## Theorem 23.3
The spectral sequence of a first quadrant filtered complex converges to $H_*(C_*)$: $E_{s,t}^{\infty} \cong \text{gr}_{s} H_{s+t}(C_{*})$.

## Corollary 23.4
Let $f: C \to D$ be a map of first quadrant filtered chain complexes. If $E_{*,*}^r(f)$ is an isomorphism for some r, then $f_*: H_*(C) \to H_*(D)$ is an isomorphism.

## Theorem 24.1 [Serre spectral sequence]
Let $p: E \to B$ be a Serre fibration. There is a first quadrant spectral sequence with $E_{s,t}^2 = H_s(B; H_t(p^{-1}(-); M))$ converging to $H_*(E; M)$.

## Proposition 26.1 [Gysin sequence]
Let $p: E \to B$ be an oriented Serre fibration with fiber a homology (n-1)-sphere. There is a long exact Gysin sequence $\cdots \to H_{s+1}(B) \to H_{s-n+1}(B) \to H_s(E) \to H_s(B) \to \cdots$.

## Proposition 26.2
The bottom edge homomorphism in the Serre spectral sequence coincides with $p_*: H_n(E) \to H_n(B)$.

## Proposition 26.3
The left edge homomorphism coincides with $i_*: H_n(F) \to H_n(E)$.

## Proposition 26.5
The transgression and the linear relation from $H_n(B) \xleftarrow{p_*} H_n(E, F) \xrightarrow{\partial} H_{n-1}(F)$ coincide.

## Proposition 27.1
The Hurewicz map participates in a commutative ladder between the homotopy and Serre exact sequences.

## Lemma 27.2
Let X be (n-1)-connected. The transgression gives an isomorphism $\overline{H}_i(X) \to \overline{H}_{i-1}(\Omega X)$ for $i < 2n - 2$.

## Theorem 27.3 [Hurewicz, via Serre spectral sequence]
Let $n \geq 1$, X (n-1)-connected. Then $\overline{H}_i(X) = 0$ for $i < n$ and $\pi_n(X)^{ab} \to H_n(X)$ is an isomorphism.

## Theorem 27.4 [Relative Hurewicz]
Let X, A be simply connected, $n \geq 2$, $\pi_i(X, A) = 0$ for $2 \leq i < n$. Then $H_i(X, A) = 0$ for $i < n$ and $\pi_n(X,A) \to H_n(X,A)$ is an isomorphism.

## Corollary 27.5
Let X, A simply connected, $n \geq 2$. If $H_i(X, A) = 0$ for $2 \leq i < n$, then $\pi_i(X, A) = 0$ for $i < n$ and $\pi_n(X,A) \to H_n(X,A)$ is an isomorphism.

## Corollary 27.6 [Whitehead theorem]
Let $f: X \to Y$ be a map of path connected spaces. If $f_*$ on $\pi_q$ is iso for $q < n$ and epi for $q = n$, then $f_*$ on $H_q$ is iso for $q < n$ and epi for $q = n$. Converse holds if both simply connected.

## Corollary 27.7
Any weak equivalence induces a homology isomorphism. Conversely, for simply connected spaces, any homology isomorphism is a weak equivalence.

## Theorem 29.1
A first quadrant decreasing filtration on a cochain complex gives a convergent cohomological spectral sequence $E_r^{s,t} \Longrightarrow H^{s+t}(C)$.

## Theorem 29.2
For a Serre fibration $p: E \to B$ with coefficient ring R, there is a multiplicative cohomological spectral sequence $E_2^{s,t} = H^s(B; H^t(p^{-1}(-))) \Longrightarrow H^{s+t}(E)$.

## Theorem 29.3
For an R-oriented closed manifold M, $\langle e(\tau), [M] \rangle = \chi(M) \in R$.

## Lemma 30.6
Mod C monomorphisms, epimorphisms, and isomorphisms contain all isomorphisms, are closed under composition, and the isomorphisms satisfy 2-out-of-3.

## Proposition 30.7 [Mod C Vietoris-Begle]
For a fibration with path connected base and fiber, if $H_t(F) \in C$ for $t > 0$ (C a Serre ideal), then $\pi_*: H_n(E) \to H_n(B)$ is mod C iso.

## Proposition 30.8
Under hypotheses on low-dimensional homology of B and F, $\pi_*: H_i(E,F) \to H_i(B,*)$ is mod C iso for $i \leq n$.

## Theorem 30.9 [Mod C Hurewicz]
For C an acyclic Serre ring, X simply connected, $n \geq 2$: $\pi_q(X) \in C$ for $q < n$ iff $\overline{H}_q(X) \in C$ for $q < n$, and then $\pi_n(X) \to H_n(X)$ is mod C iso.

## Corollary 30.10
For simply connected X: (1) $H_q$ finitely generated iff $\pi_q$ finitely generated. (2) $H_q$ p-torsion iff $\pi_q$ p-torsion.

## Theorem 31.1
For simply connected X, if $\overline{H}_q(X; \mathbb{Z}_{(p)}) = 0$ for $q < n$, then $\pi_q(X) \otimes \mathbb{Z}_{(p)} = 0$ for $q < n$ and $\pi_n(X) \otimes \mathbb{Z}_{(p)} \to H_n(X; \mathbb{Z}_{(p)})$ is iso.

## Theorem 31.2 [Relative mod C Hurewicz]
For C acyclic Serre ideal, (X,A) simply connected: $\pi_i(X,A) \in C$ for $2 \le i < n$ iff $H_i(X,A) \in C$ for $2 \le i < n$, and then $h: \pi_n(X,A) \to H_n(X,A)$ is mod C iso.

## Theorem 31.3 [Mod C Whitehead]
For C acyclic Serre ideal, $f: X \to Y$ simply connected: mod C iso/epi conditions on $\pi_*$ are equivalent to mod C iso/epi conditions on $H_*$.

## Lemma 31.4
If $f: X \to Y$ induces iso in mod p homology (p-local homology finite type), then it induces mod $C_p$ iso in integral homology.

## Corollary 31.5
For simply connected X, Y with p-local finite type homology, mod p homology iso implies $\pi_*(X) \otimes \mathbb{Z}_{(p)} \cong \pi_*(Y) \otimes \mathbb{Z}_{(p)}$.

## Proposition 31.6
$\pi_i(S^n)$ is finite for all i except $i = n$ and (if n even) $i = 2n - 1$, when it is finitely generated of rank 1.

## Proposition 32.1
The transgression for the path loop fibration is the converse of the evaluation map relation.

## Proposition 32.2
For C a Serre ring, X simply connected with $\overline{H}_i(X) \in C$ for $i < n$: $\text{ev}_*: \overline{H}_{i-1}(\Omega X) \to \overline{H}_i(X)$ is mod C iso for $i < 2n - 1$.

## Theorem 32.3 [Mod C Freudenthal]
For C acyclic Serre ideal, X simply connected with $\overline{H}_i(X)$ zero mod C for $i < n$: $\pi_i(X) \to \pi_{i+1}(\Sigma X)$ is mod C iso for $i < 2n-1$.

## Corollary 32.4
$\pi_i(S^n) \to \pi_{i+1}(S^{n+1})$ is iso for $i < 2n - 1$ and epi for $i = 2n - 1$.

## Proposition 32.5
For $n \geq 2$, there is a map $h: \Omega S^n \to \Omega S^{2n-1}$ inducing iso in $H_{2n-2}$.

## Theorem 32.6
For positive even n, there is a fiber sequence $S^{n-1} \to \Omega S^n \to \Omega S^{2n-1}$. Localized at 2, also for odd n.

## Theorem 32.7 [Bousfield]
For any generalized homology theory $E_*$ and CW complex X, there is a Bousfield localization $L_EX$ terminal among $E_*$-equivalences from X.

## Theorem 32.8
$L_EX$ is $E_*$-local, and $X \to L_EX$ is initial among maps to $E_*$-local spaces.

## Lemma 32.9
Any $E_*$-equivalence between $E_*$-local CW complexes is a homotopy equivalence.

## Proposition 32.10
A simply connected CW complex is $H\mathbb{Q}_*$-local iff its positive-dimensional homology is rational.

## Theorem 33.3 [Chern classes]
Unique characteristic classes $c_k(\xi) \in H^{2k}(X; \mathbb{Z})$ for complex n-plane bundles satisfying $c_0 = 1$, $c_1^{(1)} = -e$, Whitney sum formula; $H^*(BU(n)) \cong \mathbb{Z}[c_1, \dots, c_n]$.

## Theorem 33.5 [Leray-Hirsch]
For a fibration with free finite-rank fiber cohomology and surjective restriction, $H^*(B) \otimes_R H^*(F) \cong H^*(E)$ as $H^*(B)$-modules.

## Theorem 33.6 [Stiefel-Whitney classes]
Unique classes $w_k(\xi) \in H^{2k}(X; \mathbb{F}_2)$ for real n-plane bundles satisfying analogous axioms; $H^*(BO(n); \mathbb{F}_2) \cong \mathbb{F}_2[w_1, \dots, w_n]$.

## Theorem 34.1
Unique Chern classes characterized by behavior under splitting; they generate all characteristic classes with no universal relations.

## Theorem 34.2
$H^*(BU(n)) = \mathbb{Z}[c_1,\ldots,c_n]$ with $c_n = (-1)^n e$.

## Theorem 34.3 [Splitting principle]
For a complex n-plane bundle $\xi$, there exists $f: \text{Fl}(\xi) \to X$ with $f^*\xi$ split and $f^*$ monic on cohomology.

## Theorem 34.4
$H^*(BU(n)) \cong H^*(BT^n)^{\Sigma_n}$; the $c_i$ map to elementary symmetric functions.

## Lemma 34.6
Conjugation by $g \in G$ induces the identity on BG up to homotopy.

## Proposition 35.2 [Thom isomorphism]
For R-oriented $\xi$, there is a unique Thom class $U$ and $- \cup U: H^*(B) \to \overline{H}^*(\text{Th}(\xi))$ is iso.

## Lemma 35.3
$\pi^*U = \pm e$ (Thom class pulls back to Euler class).

## Proposition 35.4
$e(\xi \times \eta) = e(\xi) \times e(\eta)$ (Euler class is multiplicative for products).

## Proposition 36.1
$H^*(BO(n); \mathbb{F}_2) = \mathbb{F}_2[w_1, ..., w_n]$.

## Lemma 36.2
$c_i(\overline{\xi}) = (-1)^i c_i(\xi)$.

## Theorem 36.5
$H^*(BSO(n))$ (away from 2) is polynomial on Pontryagin classes and Euler class.

## Proposition 37.5
$\text{Sq}^1 = \beta$.

## Proposition 37.6
$\text{Sq}^0 = 1$ on $\overline{H}^1$.

## Proposition 37.7
Steenrod operations are stable.

## Corollary 37.8
$\text{Sq}^0 = \text{id}$ on all $\overline{H}^q$.

## Corollary 37.9
$\text{Sq}^n$ is additive.

## Proposition 37.10 [Adem]
$A^*$ is generated by $\text{Sq}^{2^k}$.

## Corollary 37.11
If $H^*(X) = \mathbb{F}_2[x]/x^3$, then $|x|$ is a power of 2.

## Theorem 38.2 [Thom]
$\mathcal{N}_* = \mathbb{F}_2[x_i : i+1 \neq 2^k]$.

## Theorem 38.3 [Thom]
Steenrod's question: Yes (unoriented), No (oriented).

## Theorem 38.4 [Thom]
Pontryagin-Thom collapse: ambient cobordism classes $\cong \pi_{n+k}(MO(k))$.

## Theorem 38.5 [Thom]
$\mathcal{N}_n \cong \pi_n(MO)$.

## Lemma 38.6
Characteristic numbers are cobordism invariants.

## Corollary 38.7
Same Stiefel-Whitney numbers implies cobordant.

## Theorem 38.8 [Thom]
MO is a product of suspensions of $H\mathbb{F}_2$.

## Theorem 38.9 [G. Whitehead, Brown]
Generalized homology theories are represented by spectra.

## Proposition 39.2
$H_*(BO) = \mathbb{F}_2[a_1, a_2, \ldots]$.

## Proposition 39.3 [Hopf-Leray]
Connected commutative Hopf algebra of finite type over char 0 field is free commutative graded algebra.

## Corollary 39.4 [Hopf]
Rational cohomology of connected Lie group is exterior algebra on odd generators.

## Proposition 39.5 [Borel]
Connected commutative Hopf algebra of finite type over perfect field of char p has prescribed structure.

## Proposition 39.6
Cartan formula defines Hopf algebra structure on Steenrod algebra.

## Proposition 39.7
$A_* = \mathbb{F}_2[\zeta_1, \zeta_2, \ldots]$ with specified coproduct.

## Theorem 39.8
$H^*(MO)$ is free over $A^*$.

## Lemma 39.9 [Lagrange]
For connected Hopf algebra A and compatible connected coalgebra C, if Au is free then C is free as A-module.

## Proposition 39.10 [Thom]
$\text{Sq}^{i}U = w_{i} \cup U$.

## Proposition 40.1
For any spectrum E, $\pi_*(E) \otimes \mathbb{Q} \to H_*(E; \mathbb{Q})$ is an isomorphism.
