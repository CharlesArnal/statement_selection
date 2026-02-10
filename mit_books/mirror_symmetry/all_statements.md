# All Mathematical Statements from Mirror Symmetry Lecture Notes

## Statement 1: Definition 1 (Lecture 1)
A Calabi-Yau manifold is a complex manifold (X, J) (ideally, compact, 3-dimensional, maybe $b_1 = 0$) s.t. $K_X = \bigwedge^n T^*X \cong \mathcal{O}_X$, so $\exists$ a section $\Omega \in H^0(X, K_X)$, i.e. a holomorphic volume form.

## Statement 2: Conjecture 1 (Lecture 1)
Given a Calabi-Yau manifold $(X, J, \omega^{\mathbb{C}})$, one can find another Calabi-Yau manifold $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$ s.t. $H^q(X, \Omega^pTX) \cong H^q(X^{\vee}, \Omega^p_{X^{\vee}})$ naturally and vice versa, i.e. we get a local isomorphism on the tangent spaces to their corresponding moduli spaces. Additionally, we'd like to say that the superconformal field theories are equivalent.

## Statement 3: Conjecture 2 (Lecture 1) — Kontsevich's HMS
If $(X, J, \omega^{\mathbb{C}})$ and $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$ are mirrors, then $D^{b}\operatorname{Fuk}(X,\omega^{\mathbb{C}}) \cong D^{b}\operatorname{Coh}(X^{\vee}, J^{\vee})$ and $D^{b}\operatorname{Coh}(X, J) \cong D^{b}\operatorname{Fuk}(X^{\vee}, w^{\mathbb{C}^{\vee}})$ as an equivalence of triangulated categories.

## Statement 4: Conjecture 3 (Lecture 1) — SYZ
For $X, X^{\vee}$ mirrors, they carry mutually dual fibrations by special Lagrangian tori, i.e. $T^{n} \longrightarrow X$, $(T^{\vee})^{n} \longrightarrow X^{\vee}$ over a common base $B$. Here, $L^n \subset X$ is special Lagrangian if $\omega|_L = 0$ and Im $\Omega|_L = 0$, and $T^{\vee} = \text{Hom}(\pi_1(T), U(1))$.

## Statement 5: Proposition 1 (Lecture 2)
$J'$ is integrable $\Leftrightarrow \overline{\partial}s + \frac{1}{2}[s,s] = 0$.

## Statement 6: Theorem 1 (Lecture 2) — Bogomolov-Tian-Todorov
For X a compact Calabi-Yau ($\Omega_X^{n,0} \cong \mathcal{O}_X$) with $H^0(X,TX)=0$ (automorphisms are discrete), deformations of X are unobstructed and, assuming $\operatorname{Aut}(X,J)=\{1\}$, $\mathcal{M}_{CX}$ is locally a smooth manifold with $T\mathcal{M}_{CX}=H^1(X,TX)$.

## Statement 7: Theorem 2 (Lecture 2) — Griffiths Transversality
For a family $(X, J_t)$, $\alpha_t \in \Omega^{p,q}(X, J_t) \Longrightarrow \frac{d}{dt}|_{t=0}\alpha_t \in \Omega^{p,q} + \Omega^{p+1,q-1} + \Omega^{p-1,q+1}$.

## Statement 8: Definition 1 (Lecture 3)
$u: \Sigma \to X$ is a J-holomorphic map if $J \circ du = du \circ J$, i.e. $\overline{\partial}_J u = \frac{1}{2}(du + Jduj) = 0$. For $\beta \in H_2(X, \mathbb{Z})$, we obtain an associated moduli space $M_{g,k}(X,J,\beta) = \{(\Sigma,j,z_1,\ldots,z_k), u : \Sigma \to X | u_*[\Sigma] = \beta, \overline{\partial}_J u = 0\} / \sim$.

## Statement 9: Definition 2 (Lecture 3)
We say that a map $\Sigma \to X$ is simple (or "somewhere injective") if $\exists z \in \Sigma$ s.t. $du(z) \neq 0$ and $u^{-1}(u(z)) = \{z\}$.

## Statement 10: Theorem 2 (Lecture 3)
Let $\mathcal{J}(X,\omega)$ be the set of compatible almost-complex structures on X: then $\mathcal{J}^{reg}(X,\beta) = \{J \in \mathcal{J}(X,\omega) | \text{ every simple } J\text{-holomorphic curve in class } \beta \text{ is regular} \}$ is a Baire subset in $\mathcal{J}(X,\omega)$, and for $J \in \mathcal{J}^{reg}(X,\beta)$, $\mathcal{M}_{g,k}^*(X,J,\beta)$ is smooth (as an orbifold, if $\mathcal{M}_{g,k}$ is an orbifold) of real dimension 2d and carries a natural orientation.

## Statement 11: Definition 1 (Lecture 4)
$u: \Sigma \to X$ is J-holomorphic if $\overline{\partial}_J u = \frac{1}{2}(du + Jdu \cdot j) = 0$, and for $\beta \in H_2(X, \mathbb{Z})$, we have a moduli space $\mathcal{M}_{g,k}(X,J,\beta) = \{(\Sigma,j,z_1,\ldots,z_k), u|u_*[\Sigma] = \beta, \overline{\partial}_J u = 0\}/\sim$.

## Statement 12: Theorem 1 (Lecture 4)
The set $\mathcal{J}^{reg}(X,\beta)$ of $J \in \mathcal{J}(X,\omega)$ s.t. every simple J-holomorphic curve in class $\beta$ is regular is a Baire subset. For $J \in \mathcal{J}^{reg}(X,\beta)$, the subset of simple maps $\mathcal{M}_{g,k}^*(X,J,\beta) \subset \mathcal{M}_{g,k}(X,J,\beta)$ is smooth and oriented of dimension 2d.

## Statement 13: Theorem 2 (Lecture 4) — Gromov Compactness
If $u_n : \Sigma_n \to X$ is a sequence of J-holomorphic curves, $J \in \mathcal{J}(X,\omega)$, $E(u_n) = \int_{\Sigma_n} u_n^* \omega = \langle [\omega], u_{n*}[\Sigma_n] \rangle$ bounded $\leq E_0 < \infty$, then $\exists$ a subsequence which converges to a stable map $u_\infty : \Sigma_\infty \to X$.

## Statement 14: Definition 1 (Lecture 5)
The quantum cohomology of X is $QH^*(X) = (H^*(X;\Lambda),*)$.

## Statement 15: Theorem 1 (Lecture 5)
This [the quantum cohomology product *] is an associative algebra.

## Statement 16: Definition 2 (Lecture 5)
Let (X, J) be a Calabi-Yau 3-fold with $h^{1,0} = 0$ (so $h^{2,0} = 0$ and $H^{1,1} = H^2$). Then the complexified Kähler moduli space is $\mathcal{M}_{Kah} = (H^2(X, \mathbb{R}) + i\mathcal{K}(X, J))/H^2(X, \mathbb{Z}) = \{ [B + i\omega], \omega \ \text{Kahler} \}/H^2(X, \mathbb{Z})$.

## Statement 17: Theorem 2 (Lecture 5)
If $NC \cong \mathcal{O}(-1) \oplus \mathcal{O}(-1)$, then the contribution of C to $N_{k[C]}$ is $\frac{1}{k^3}$.

## Statement 18: Theorem 1 (Lecture 7)
All eigenvalues of $\phi_*$ [the monodromy action on cohomology] are roots of unity: thus $\exists N, k$ s.t. $(\phi_*^N - \text{id})^k = 0$. Moreover, $k \leq n + 1$.

## Statement 19: Theorem 2 (Lecture 7) — Cattani-Kaplan
All the elements of the form $\sum \lambda_i N_i, \lambda_i > 0$ have the same monodromy weight filtration.

## Statement 20: Definition 1 (Lecture 7) — Morrison
Given a family of Calabi-Yau n-folds $\mathcal{X} \to (D^*)^S \subset (D^2)^s$, $s = h^{n-1,1}(X)$, s.t. the Kodaira-Spencer map $T_*(D^*)^s \to H^1(TX_t)$ is an isomorphism at every point of $(D^*)^s$, we say that $0 \in (D^2)^s$ is a large complex structure limit (LCSL) point if (1) The monodromies $\phi_j$ around each factor are all unipotent. (2) Let $N_j = \log \phi_j$, $N = \sum \lambda_j N_j$ for $\lambda_j > 0$ arbitrary. Then the weight filtration $0 \subseteq W_0 \subseteq W_1 \subseteq \cdots \subseteq W_{2n} = H^n(X, \mathbb{Q})$ has dim $W_0 = \dim W_1 = 1$, dim $W_2 = \dim W_3 = s + 1$. (3) Let $\alpha_0^*$ be the generator of $W_0$, $\alpha_1^*$, $\cdots$, $\alpha_s^*$ the rest of a basis for $W_2$. Then $\exists m_{jk} \in \mathbb{Q}$ s.t. $N_j(\alpha_k^*) = m_{jk}\alpha_0^*$. We further require that $(m_{jk})$ is an invertible matrix.

## Statement 21: Lemma 1 (Lecture 7)
$W_{4-2i} = W_{2i}^{\perp}$.

## Statement 22: Proposition 1 (Lecture 7)
Given an LCSL point in the moduli space of Calabi-Yau 3-folds with $h^{2,1} = s$, $\exists$ a $\mathbb{Z}$-basis $(\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S)$ of $H_3(X, \mathbb{Z})$ s.t. $\beta_0 \in S_0$, $\beta_1, \ldots, \beta_s \in S_2$, $\alpha_1, \ldots, \alpha_s \in S_4, \alpha_0 \in S_6 = H_3(X)$ s.t. $(\alpha_i, \alpha_j) = (\beta_i, \beta_j) = 0$, $(\alpha_i, \beta_j) = \delta_{ij}$.

## Statement 23: Conjecture 1 (Lecture 7) — Mirror Symmetry
Let $f: \mathcal{X} \to (D^*)^S$ be a family of Calabi-Yau 3-folds with LCSL at 0. Then $\exists$ a Calabi-Yau 3-fold $\check{X}$ and choices of bases $\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S$ of $H_3(X, \mathbb{Z}), e_1, \ldots, e_S$ of $H^2(X, \mathbb{Z})$ s.t. under the map $m: (D^*)^S \to \mathcal{M}_{Kah}(\check{X}), (q_1, \ldots, q_S) \mapsto (\check{q}_i, \ldots, \check{q}_S), \check{q}_i = q_i$, we have a coincidence of Yukawa couplings.

## Statement 24: Proposition 1 (Lecture 9)
All periods $\int \check{\Omega}_{\psi}$ satisfy this [Picard-Fuchs] equation.

## Statement 25: Theorem 1 (Lecture 11)
If $[\omega] \cdot \pi_2(M) = 0$ and $[\omega] \cdot \pi_2(M, L_i) = 0$, then $\partial$ is well-defined, $\partial^2 = 0$, and $HF(L_0, L_1) = H^*(CF, \partial)$ is independent of the chosen J and invariant under Hamiltonian isotopies of $L_0$ and/or $L_1$.

## Statement 26: Corollary 1 (Lecture 11)
If $[\omega] \cdot \pi_2(M, L) = 0$ and $\psi$ is a Hamiltonian diffeomorphism s.t. $\psi(L), L$ are transverse, $\#(\psi(L) \cap L) \geq \sum b_i(L)$.

## Statement 27: Proposition 1 (Lecture 12)
If there is no bubbling, then $HF^*(\phi_H^1(L_0), L_1) \cong HF^*(L_0, L_1)$.

## Statement 28: Theorem 1 (Lecture 12) — Fukaya-Oh
For $\epsilon \to 0$, holomorphic strips between $L_0$ and $L_1$ are in one-to-one correspondence with the gradient trajectories of f, and $HF^*(L_0, L_1) \cong HM_{n-*}(f) \cong H^*(N)$.

## Statement 29: Definition 1 (Lecture 13)
(Assuming transversality) $q \circ p = \sum_{\substack{r \in L_0 \cap L_2 \\ \operatorname{ind}([u]) = 0}} (\# \mathcal{M}(p, q, r, [u], J)) T^{\omega(u)} r$.

## Statement 30: Proposition 1 (Lecture 13)
If $[\omega] \cdot \pi_2(M, L_i) = 0$, then the product structure defined above satisfies the Leibniz rule w.r.t. $\partial$, and hence induces a product on $HF^*$; this product structure will be associative.

## Statement 31: Proposition 2 (Lecture 13)
Assuming no bubbling of disks and spheres, $\forall m \geq 1, (p_1, \ldots, p_m), p_i \in L_{i-1} \cap L_i$, $\sum_{\substack{k,\ell \geq 1 \\ k+\ell = m+1 \\ 0 < j < \ell-1}} (-1)^* m_{\ell}(p_m, \dots, p_{j+k+1}, m_i(p_{j+k}, \dots, p_{j+1}), p_j, \dots, p_1) = 0$ where $* = \deg(p_1) + \cdots + \deg(p_i) + j$.

## Statement 32: Definition 2 (Lecture 13)
An $A_{\infty}$ category is a linear "category" where morphism spaces are equipped with algebraic operations $(m_k)_{k\geq 1}$ satisfying the $A_{\infty}$-relations.

## Statement 33: Definition 1 (Lecture 16)
A chain map $f: C_* \to D_*$ (i.e. a collection of maps $f_iC_i \to D_i$ commuting with $\partial$) is a quasi-isomorphism if the induced maps on cohomology are isomorphisms.

## Statement 34: Definition 1 (Lecture 17)
An additive category is one in which $\operatorname{Hom}(A,B)$ are abelian groups, composition is distributive, and there is a direct sum $\oplus$ and a zero object 0. An abelian category is an additive category s.t. every morphism has a kernel and cokernel, e.g. a kernel of $f: A \to B$ is a morphism $K \to A$ s.t. $g: C \to A$ factors through K uniquely iff $f \circ g = 0$.

## Statement 35: Definition 2 (Lecture 17)
For $\mathcal{A}$ an abelian category, the bounded derived category $D^b(\mathcal{A})$ is the triangulated category whose objects are bounded chain complexes in $\mathcal{A}$ and whose morphisms are given by chain maps up to homotopy localizing w.r.t. quasi-isomorphisms.

## Statement 36: Definition 3 (Lecture 17)
A triangulated category is an additive category with a shift functor [1] and a set of distinguished triangles satisfying various axioms.

## Statement 37: Proposition 1 (Lecture 17)
$\operatorname{Hom}_{D^b(\mathcal{A})}(A, B[k]) = \operatorname{Ext}_{\mathcal{A}}^k(A, B)$.

## Statement 38: Proposition 2 (Lecture 17)
For an exact triangle $A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{h} A[1]$ and an object E, we have long exact sequences $\cdots \to \operatorname{Hom}(E,A[i]) \xrightarrow{f_*} \operatorname{Hom}(E,B[i]) \xrightarrow{g_*} \operatorname{Hom}(E,C[i]) \xrightarrow{h_*} \operatorname{Hom}(E,A[i+1]) \to \cdots$ and $\cdots \to \operatorname{Hom}(A[i+1], E) \xrightarrow{h^*} \operatorname{Hom}(C[i], E) \xrightarrow{g^*} \operatorname{Hom}(B[i], E) \xrightarrow{f^*} \operatorname{Hom}(A[i], E) \to \cdots$.

## Statement 39: Conjecture 1 (Lecture 19)
$X, X^{\vee}$ are mirror Calabi-Yau varieties $\Leftrightarrow D^{\pi} \operatorname{Fuk}(X) \cong D^b \operatorname{Coh}(X^{\vee})$.

## Statement 40: Conjecture 1 (Lecture 21)
Generic points of $\check{X}$ parameterize isomorphism classes of $(L, \nabla)$, $L \subset X$ a Lagrangian torus and $\nabla$ a flat U(1)-connection on $\underline{\mathbb{C}} \to L$ (corresponding to elements of $\operatorname{Hom}(\pi_1 L, U(1))$).

## Statement 41: Definition 1 (Lecture 21)
A special Lagrangian submanifold is one with Im $(\Omega|_L) = 0$.

## Statement 42: Conjecture 2 (Lecture 21) — SYZ
$X, \check{X}$ carry dual fibrations by special Lagrangian tori $T^{n} \to X$ and $\check{T}^{n} \to \check{X}$ over a common base B, i.e. $\check{X} = \{(L, \nabla), L \text{ fiber of } \pi, \nabla \in \text{hom}(\pi_1 T, U(1))\}$.

## Statement 43: Proposition 1 (Lecture 21)
If $L \subset X$ is Lagrangian, $\Omega|_L \in \Omega^n(L,\mathbb{C})$ is $e^{i\phi}\psi \operatorname{vol}_g|_L$ with $e^{i\phi}: L \to S^1$ a phase function.

## Statement 44: Proposition 2 (Lecture 21)
First order deformations of special Lagrangian L in a strict (resp. almost) Calabi-Yau manifold are given by $\mathcal{H}^1(L,\mathbb{R})$ (resp. $\mathcal{H}^1_{\psi}(L,\mathbb{R})$), where $H^{1}_{\psi}(L,\mathbb{R}) = \{ \beta \in \Omega^{1}(L,\mathbb{R}) \mid d\beta = 0, d^{*}(\psi\beta) = 0 \}$. It is still true that $\mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$.

## Statement 45: Theorem 1 (Lecture 21) — McLean, Joyce
Deformations of special Lagrangians are unobstructed, i.e. the moduli space of special Lagrangians is a smooth manifold B with $T_LB \cong \mathcal{H}^1_{\psi}(L,\mathbb{R}) \cong H^1(L,\mathbb{R})$.

## Statement 46: Definition 1 (Lecture 22)
An affine structure on a manifold N is a set of coordinate charts with transition functions in $GL(n, \mathbb{Z}) \ltimes \mathbb{R}^n$.

## Statement 47: Corollary 1 (Lecture 22)
B [the base of the special Lagrangian fibration] carries two affine structures.

## Statement 48: Proposition 2 (Lecture 22)
$J^{\vee}$ [the almost-complex structure on the moduli space M of pairs (L, nabla)] is integrable.

## Statement 49: Proposition 3 (Lecture 22)
$\omega^{\vee}$ is a Kähler form compatible with $J^{\vee}$.

## Statement 50: Definition 1 (Lecture 24)
$\omega(L, \nabla) = \sum_{\substack{\beta \in \pi_2(X, L) \\ \mu(\beta) = 2}} n_{\beta} z_{\beta}(L, \nabla)$ where $z_{\beta} = e^{-2\pi \int_{\beta} \omega} \operatorname{hol}_{\partial\beta}(\nabla)$. [The superpotential.]

## Statement 51: Theorem 1 (Lecture 25)
$H^0(MF(W-\lambda)) = 0$, i.e. all matrix factorizations are nullhomotopic, unless $\lambda$ is a critical value of W.
