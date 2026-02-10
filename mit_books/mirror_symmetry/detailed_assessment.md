# Detailed Assessment of Statements Against Mathlib v4.27.0

## Statement 1: Definition 1 (Lecture 1) — Calabi-Yau Manifold
A Calabi-Yau manifold is a complex manifold (X, J) (ideally, compact, 3-dimensional, maybe $b_1 = 0$) s.t. $K_X = \bigwedge^n T^*X \cong \mathcal{O}_X$, so $\exists$ a section $\Omega \in H^0(X, K_X)$, i.e. a holomorphic volume form.

Assessment: non-included
Mathlib does not contain a definition of Calabi-Yau manifolds. The library has complex manifold infrastructure (in Mathlib/Geometry/Manifold/Complex.lean) and holomorphic functions, but no definition of the canonical bundle $K_X$ for complex manifolds, no notion of holomorphic volume forms, and no Calabi-Yau condition. Searches for "CalabiYau" returned no results. The algebraic geometry side (Mathlib/AlgebraicGeometry/) deals with schemes but does not formalize Calabi-Yau varieties either.

## Statement 2: Conjecture 1 (Lecture 1) — Mirror Symmetry for Hodge Numbers
Given a Calabi-Yau manifold $(X, J, \omega^{\mathbb{C}})$, one can find another Calabi-Yau manifold $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$ s.t. $H^q(X, \Omega^pTX) \cong H^q(X^{\vee}, \Omega^p_{X^{\vee}})$ naturally and vice versa.

Assessment: non-included
This is the foundational mirror symmetry conjecture. Mathlib has no notion of Calabi-Yau manifolds, Hodge numbers, Dolbeault cohomology, or mirror pairs. Searches for "Hodge" found only references in Perfectoid ring theory contexts (FontaineTheta, BDeRham), unrelated to Hodge theory on complex manifolds.

## Statement 3: Conjecture 2 (Lecture 1) — Kontsevich's HMS
If $(X, J, \omega^{\mathbb{C}})$ and $(X^{\vee}, J^{\vee}, \omega^{\mathbb{C}^{\vee}})$ are mirrors, then $D^{b}\operatorname{Fuk}(X,\omega^{\mathbb{C}}) \cong D^{b}\operatorname{Coh}(X^{\vee}, J^{\vee})$ and $D^{b}\operatorname{Coh}(X, J) \cong D^{b}\operatorname{Fuk}(X^{\vee}, w^{\mathbb{C}^{\vee}})$ as an equivalence of triangulated categories.

Assessment: non-included
While mathlib has triangulated categories (Mathlib/CategoryTheory/Triangulated/) and derived categories (Mathlib/Algebra/Homology/DerivedCategory/), it does not have Fukaya categories (search for "Fukaya" returned no results), coherent sheaves on complex manifolds in the differential-geometric sense, or any formulation of homological mirror symmetry. The notion of a Lagrangian submanifold is also absent (search for "Lagrangian" returned no results in the relevant sense).

## Statement 4: Conjecture 3 (Lecture 1) — SYZ Conjecture
For $X, X^{\vee}$ mirrors, they carry mutually dual fibrations by special Lagrangian tori.

Assessment: non-included
Mathlib has no notion of special Lagrangian submanifolds (search returned no results), Lagrangian torus fibrations, or any of the differential-geometric or symplectic-geometric machinery needed for this conjecture. The symplectic group exists (Mathlib/LinearAlgebra/SymplecticGroup.lean) but symplectic manifolds and Lagrangian submanifolds are not formalized.

## Statement 5: Proposition 1 (Lecture 2) — Integrability via Maurer-Cartan
$J'$ is integrable $\Leftrightarrow \overline{\partial}s + \frac{1}{2}[s,s] = 0$.

Assessment: non-included
This characterizes integrability of almost-complex structures via the Maurer-Cartan equation on the differential graded Lie algebra of $(0,1)$-forms valued in $T^{1,0}X$. Mathlib does not have almost-complex structures on manifolds (search for "almost complex" or "AlmostComplex" returned results only about complex manifolds, not the integrability question), Dolbeault operators, or differential graded Lie algebras in this geometric context.

## Statement 6: Theorem 1 (Lecture 2) — Bogomolov-Tian-Todorov
For X a compact Calabi-Yau with $H^0(X,TX)=0$, deformations of X are unobstructed and $\mathcal{M}_{CX}$ is locally a smooth manifold with $T\mathcal{M}_{CX}=H^1(X,TX)$.

Assessment: non-included
This deep theorem in complex geometry requires the full theory of deformations of complex structures, Calabi-Yau manifolds, and sheaf cohomology on complex manifolds. Searches for "Bogomolov", "Tian", "Todorov", and "unobstructed" returned no results in a relevant geometric context in mathlib.

## Statement 7: Theorem 2 (Lecture 2) — Griffiths Transversality
For a family $(X, J_t)$, $\alpha_t \in \Omega^{p,q}(X, J_t) \Longrightarrow \frac{d}{dt}|_{t=0}\alpha_t \in \Omega^{p,q} + \Omega^{p+1,q-1} + \Omega^{p-1,q+1}$.

Assessment: non-included
Griffiths transversality is a fundamental result in Hodge theory concerning how the Hodge filtration varies in families. Mathlib has no formalization of Hodge filtrations, variations of Hodge structure, or the Gauss-Manin connection. Searches for "Griffiths transversality" returned no results.

## Statement 8: Definition 1 (Lecture 3) — J-holomorphic map
$u: \Sigma \to X$ is a J-holomorphic map if $J \circ du = du \circ J$, i.e. $\overline{\partial}_J u = \frac{1}{2}(du + Jduj) = 0$.

Assessment: non-included
J-holomorphic curves are central to symplectic geometry and Gromov-Witten theory. Mathlib has no notion of almost-complex structures on manifolds, J-holomorphic maps, or the associated moduli spaces. The search for "GromovWitten" returned no results.

## Statement 9: Definition 2 (Lecture 3) — Simple (somewhere injective) map
A map $\Sigma \to X$ is simple if $\exists z \in \Sigma$ s.t. $du(z) \neq 0$ and $u^{-1}(u(z)) = \{z\}$.

Assessment: non-included
This is a specific notion from the theory of J-holomorphic curves in symplectic geometry, which is entirely absent from mathlib.

## Statement 10: Theorem 2 (Lecture 3) — Regularity of simple J-holomorphic curves
$\mathcal{J}^{reg}(X,\beta)$ is a Baire subset in $\mathcal{J}(X,\omega)$, and for $J \in \mathcal{J}^{reg}(X,\beta)$, $\mathcal{M}_{g,k}^*(X,J,\beta)$ is smooth of real dimension 2d and carries a natural orientation.

Assessment: non-included
This is a transversality theorem for J-holomorphic curves requiring Sard-Smale and Fredholm theory in infinite-dimensional settings. Mathlib does not have J-holomorphic curve theory. While Baire category theorem results exist, the symplectic geometry context is absent.

## Statement 11: Definition 1 (Lecture 4) — J-holomorphic map (restated)
$u: \Sigma \to X$ is J-holomorphic if $\overline{\partial}_J u = \frac{1}{2}(du + Jdu \cdot j) = 0$.

Assessment: non-included
This is a restatement of Statement 8. Same reasoning applies.

## Statement 12: Theorem 1 (Lecture 4) — Regularity of simple curves (restated)
The set $\mathcal{J}^{reg}(X,\beta)$ of $J$ s.t. every simple J-holomorphic curve in class $\beta$ is regular is a Baire subset. For $J \in \mathcal{J}^{reg}(X,\beta)$, $\mathcal{M}_{g,k}^*(X,J,\beta)$ is smooth and oriented of dimension 2d.

Assessment: non-included
This is a restatement of Statement 10. Same reasoning applies.

## Statement 13: Theorem 2 (Lecture 4) — Gromov Compactness
If $u_n : \Sigma_n \to X$ is a sequence of J-holomorphic curves with bounded energy, then $\exists$ a subsequence which converges to a stable map $u_\infty : \Sigma_\infty \to X$.

Assessment: non-included
Gromov's compactness theorem is a foundational result in symplectic topology. Mathlib has Gromov-Hausdorff distance (Mathlib/Topology/MetricSpace/GromovHausdorff.lean) but not Gromov compactness for J-holomorphic curves. The entire theory of pseudo-holomorphic curves and stable maps is absent.

## Statement 14: Definition 1 (Lecture 5) — Quantum Cohomology
The quantum cohomology of X is $QH^*(X) = (H^*(X;\Lambda),*)$.

Assessment: non-included
Quantum cohomology requires Gromov-Witten invariants, the Novikov ring, and the deformed cup product. None of these are present in mathlib. Searches for "quantum cohomology" and "QuantumCohomology" returned no results.

## Statement 15: Theorem 1 (Lecture 5) — Associativity of Quantum Cohomology
The quantum product * is associative.

Assessment: non-included
This result, which relies on the WDVV equations and properties of Gromov-Witten invariants (specifically the relation between 4-point and 3-point invariants via splitting), is not in mathlib. The entire framework of quantum cohomology is absent.

## Statement 16: Definition 2 (Lecture 5) — Complexified Kähler Moduli Space
The complexified Kähler moduli space is $\mathcal{M}_{Kah} = (H^2(X, \mathbb{R}) + i\mathcal{K}(X, J))/H^2(X, \mathbb{Z})$.

Assessment: non-included
Mathlib does not formalize Kähler manifolds, Kähler cones, or complexified Kähler moduli spaces. The "Kaehler" results found in mathlib (Mathlib/RingTheory/Kaehler/) pertain to Kähler differentials in commutative algebra, which is a different concept entirely.

## Statement 17: Theorem 2 (Lecture 5) — Multiple Cover Formula
If $NC \cong \mathcal{O}(-1) \oplus \mathcal{O}(-1)$, then the contribution of C to $N_{k[C]}$ is $\frac{1}{k^3}$.

Assessment: non-included
This is a result in Gromov-Witten theory about multiple covers of rational curves in Calabi-Yau 3-folds. The entire theory of Gromov-Witten invariants, normal bundles of curves, and multiple cover contributions is absent from mathlib.

## Statement 18: Theorem 1 (Lecture 7) — Monodromy Theorem
All eigenvalues of $\phi_*$ are roots of unity: thus $\exists N, k$ s.t. $(\phi_*^N - \text{id})^k = 0$. Moreover, $k \leq n + 1$.

Assessment: non-included
The monodromy theorem for degenerations of algebraic varieties requires the theory of variations of Hodge structure and the associated weight filtrations. Mathlib has no formalization of this. While mathlib has roots of unity and linear algebra, the geometric context (monodromy of families of manifolds) is absent.

## Statement 19: Theorem 2 (Lecture 7) — Cattani-Kaplan
All elements of the form $\sum \lambda_i N_i, \lambda_i > 0$ have the same monodromy weight filtration.

Assessment: non-included
This result from the theory of several-variable degenerations of Hodge structures is highly specialized. Mathlib has no concept of monodromy weight filtrations or the associated nilpotent orbit theorems.

## Statement 20: Definition 1 (Lecture 7) — Large Complex Structure Limit (Morrison)
Definition of LCSL point involving unipotent monodromies and specific dimensional conditions on the weight filtration.

Assessment: non-included
This definition is specific to the mirror symmetry literature and requires the full setup of variations of Hodge structure, monodromy, and weight filtrations. None of this infrastructure exists in mathlib.

## Statement 21: Lemma 1 (Lecture 7) — Weight Filtration Duality
$W_{4-2i} = W_{2i}^{\perp}$.

Assessment: non-included
This lemma about the weight filtration of monodromy on the cohomology of Calabi-Yau 3-folds requires the intersection pairing and weight filtration theory, which are absent from mathlib in this context.

## Statement 22: Proposition 1 (Lecture 7) — Symplectic Basis at LCSL
Given an LCSL point, $\exists$ a $\mathbb{Z}$-basis $(\alpha_0, \ldots, \alpha_S, \beta_0, \ldots, \beta_S)$ of $H_3(X, \mathbb{Z})$ with specified intersection properties.

Assessment: non-included
This result requires the full theory of LCSL degenerations and the intersection form on the middle cohomology of Calabi-Yau 3-folds. While mathlib has general facts about symplectic forms on vector spaces, the geometric context is absent.

## Statement 23: Conjecture 1 (Lecture 7) — Mirror Symmetry Conjecture
Let $f: \mathcal{X} \to (D^*)^S$ be a family of Calabi-Yau 3-folds with LCSL at 0. Then $\exists$ a mirror $\check{X}$ with coincidence of Yukawa couplings.

Assessment: non-included
This is the precise mathematical formulation of the mirror symmetry conjecture relating Yukawa couplings on the complex and Kähler moduli spaces. The entire setup (Calabi-Yau families, LCSL, Yukawa couplings, Gromov-Witten invariants) is absent from mathlib.

## Statement 24: Proposition 1 (Lecture 9) — Periods Satisfy Picard-Fuchs Equation
All periods $\int \check{\Omega}_{\psi}$ satisfy the Picard-Fuchs equation.

Assessment: non-included
The Picard-Fuchs equation for periods of holomorphic forms on algebraic varieties is not formalized in mathlib. The library has ordinary differential equations but not in the context of algebraic geometry and period integrals.

## Statement 25: Theorem 1 (Lecture 11) — Floer Homology Well-Defined
If $[\omega] \cdot \pi_2(M) = 0$ and $[\omega] \cdot \pi_2(M, L_i) = 0$, then $\partial$ is well-defined, $\partial^2 = 0$, and $HF(L_0, L_1)$ is independent of J and Hamiltonian isotopy invariant.

Assessment: non-included
Lagrangian Floer homology is a deep construction in symplectic topology. Searches for "Floer" and "Lagrangian" returned no results. Mathlib has no notion of symplectic manifolds (beyond the symplectic group), Lagrangian submanifolds, or Floer homology.

## Statement 26: Corollary 1 (Lecture 11) — Arnold's Conjecture (Special Case)
If $[\omega] \cdot \pi_2(M, L) = 0$ and $\psi$ is a Hamiltonian diffeomorphism s.t. $\psi(L), L$ are transverse, $\#(\psi(L) \cap L) \geq \sum b_i(L)$.

Assessment: non-included
Arnold's conjecture on Lagrangian intersections is a central problem in symplectic topology. Mathlib has Hofer's metric (Mathlib/Analysis/Hofer.lean) but not the full theory of Hamiltonian diffeomorphisms, Lagrangian intersections, or Floer homology needed for this result.

## Statement 27: Proposition 1 (Lecture 12) — Hamiltonian Isotopy Invariance
If there is no bubbling, then $HF^*(\phi_H^1(L_0), L_1) \cong HF^*(L_0, L_1)$.

Assessment: non-included
This result about invariance of Floer homology under Hamiltonian isotopy is part of the Floer theory framework, which is absent from mathlib.

## Statement 28: Theorem 1 (Lecture 12) — Fukaya-Oh
For $\epsilon \to 0$, holomorphic strips between $L_0$ and $L_1$ are in one-to-one correspondence with gradient trajectories of f, and $HF^*(L_0, L_1) \cong H^*(N)$.

Assessment: non-included
This is a foundational result connecting Floer homology to Morse homology in the cotangent bundle. Mathlib has neither Floer homology nor Morse homology.

## Statement 29: Definition 1 (Lecture 13) — Floer Product
The Floer product is defined by counting index-0 J-holomorphic triangles.

Assessment: non-included
The Floer product requires the full setup of Lagrangian Floer theory and moduli spaces of holomorphic polygons, which are absent from mathlib.

## Statement 30: Proposition 1 (Lecture 13) — Leibniz Rule and Associativity
If $[\omega] \cdot \pi_2(M, L_i) = 0$, then the Floer product satisfies the Leibniz rule w.r.t. $\partial$ and is associative on $HF^*$.

Assessment: non-included
This is part of the algebraic structure of Lagrangian Floer theory, which is entirely absent from mathlib.

## Statement 31: Proposition 2 (Lecture 13) — A-infinity Relations
The $A_\infty$-relations hold for the operations $m_k$ defined by counting holomorphic disks, assuming no bubbling.

Assessment: non-included
$A_\infty$-categories and their relations in the context of Fukaya categories are not formalized in mathlib. Searches for "AInfinity" and "A_infinity" returned no relevant results.

## Statement 32: Definition 2 (Lecture 13) — A-infinity Category
An $A_{\infty}$ category is a linear "category" where morphism spaces are equipped with algebraic operations $(m_k)_{k\geq 1}$ satisfying the $A_{\infty}$-relations.

Assessment: non-included
Mathlib does not contain a definition of $A_\infty$-categories. While it has extensive category theory infrastructure, the $A_\infty$ (homotopy-algebraic) framework is absent.

## Statement 33: Definition 1 (Lecture 16) — Quasi-isomorphism
A chain map $f: C_* \to D_*$ is a quasi-isomorphism if the induced maps on cohomology are isomorphisms.

Assessment: included
Mathlib contains the definition of quasi-isomorphisms in its homological algebra library. The file Mathlib/Algebra/Homology/QuasiIso.lean defines quasi-isomorphisms of homological complexes, and related files (ShortComplex/QuasiIso.lean) extend this to short complexes. The concept is used extensively in the derived category construction.

## Statement 34: Definition 1 (Lecture 17) — Additive and Abelian Category
An additive category has abelian group Hom sets with distributive composition, direct sums, and a zero object. An abelian category additionally has kernels and cokernels for every morphism.

Assessment: included
Mathlib has comprehensive definitions of additive categories (Mathlib/CategoryTheory/Preadditive/) and abelian categories (Mathlib/CategoryTheory/Abelian/). The Preadditive structure provides enrichment over abelian groups, and the Abelian structure adds kernels, cokernels, and exactness conditions. These are fundamental building blocks used throughout mathlib's category theory library.

## Statement 35: Definition 2 (Lecture 17) — Bounded Derived Category
The bounded derived category $D^b(\mathcal{A})$ is the triangulated category whose objects are bounded chain complexes and whose morphisms are chain maps up to homotopy, localized at quasi-isomorphisms.

Assessment: included
Mathlib contains the derived category construction in Mathlib/Algebra/Homology/DerivedCategory/Basic.lean. It defines the derived category as a localization of the homotopy category at quasi-isomorphisms. The bounded variants and the triangulated structure are also developed. Multiple files (KInjective.lean, KProjective.lean, Fractions.lean, etc.) build out the theory.

## Statement 36: Definition 3 (Lecture 17) — Triangulated Category
A triangulated category is an additive category with a shift functor [1] and distinguished triangles satisfying various axioms.

Assessment: included
Mathlib has a comprehensive development of triangulated categories in Mathlib/CategoryTheory/Triangulated/. The file Pretriangulated.lean defines pretriangulated categories with the shift functor and distinguished triangles, and Triangulated.lean adds the octahedral axiom. The rotation and mapping cone axioms are also formalized.

## Statement 37: Proposition 1 (Lecture 17) — Hom in Derived Category = Ext
$\operatorname{Hom}_{D^b(\mathcal{A})}(A, B[k]) = \operatorname{Ext}_{\mathcal{A}}^k(A, B)$.

Assessment: included
This fundamental identification is established in mathlib's derived category and Ext library. The files Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean and related files define Ext groups via the derived category and establish this correspondence. The file Ext/ExtClass.lean provides the extension class construction.

## Statement 38: Proposition 2 (Lecture 17) — Long Exact Sequences from Triangles
For an exact triangle $A \to B \to C \to A[1]$ and an object E, we have long exact sequences involving Hom groups.

Assessment: included
Long exact sequences associated to distinguished triangles are formalized in mathlib. The homological functor machinery in Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean provides this, and the Ext exact sequences are developed in Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean. The Yoneda functor from a triangulated category is shown to be homological, giving the long exact sequences.

## Statement 39: Conjecture 1 (Lecture 19) — HMS (restated)
$X, X^{\vee}$ are mirror Calabi-Yau varieties $\Leftrightarrow D^{\pi} \operatorname{Fuk}(X) \cong D^b \operatorname{Coh}(X^{\vee})$.

Assessment: non-included
This is a restatement of the homological mirror symmetry conjecture (Statement 3). The Fukaya category, coherent sheaves on complex manifolds, and the mirror symmetry framework are all absent from mathlib.

## Statement 40: Conjecture 1 (Lecture 21) — Mirror Points as Lagrangian Tori
Generic points of $\check{X}$ parameterize isomorphism classes of $(L, \nabla)$, $L \subset X$ a Lagrangian torus and $\nabla$ a flat U(1)-connection.

Assessment: non-included
This conjecture is part of the SYZ program in mirror symmetry. Mathlib has no notion of Lagrangian submanifolds, flat connections on line bundles over Lagrangians, or the SYZ mirror construction.

## Statement 41: Definition 1 (Lecture 21) — Special Lagrangian
A special Lagrangian submanifold is one with Im $(\Omega|_L) = 0$.

Assessment: non-included
Special Lagrangian submanifolds are a central concept in calibrated geometry and mirror symmetry. Searches for "special Lagrangian" and "SpecialLagrangian" returned no results. Mathlib has no formalization of calibrated geometry or special Lagrangian conditions.

## Statement 42: Conjecture 2 (Lecture 21) — SYZ (restated)
$X, \check{X}$ carry dual fibrations by special Lagrangian tori over a common base B.

Assessment: non-included
This is a restatement of the SYZ conjecture (Statement 4). Same reasoning applies.

## Statement 43: Proposition 1 (Lecture 21) — Phase Function of Lagrangian
If $L \subset X$ is Lagrangian, $\Omega|_L \in \Omega^n(L,\mathbb{C})$ is $e^{i\phi}\psi \operatorname{vol}_g|_L$ with $e^{i\phi}: L \to S^1$ a phase function.

Assessment: non-included
This is a pointwise linear algebra result about the restriction of holomorphic volume forms to Lagrangian submanifolds. Mathlib does not formalize Lagrangian submanifolds, holomorphic volume forms, or the calibration theory needed for this result.

## Statement 44: Proposition 2 (Lecture 21/22) — Deformations of Special Lagrangians
First order deformations of special Lagrangian L in a (strict/almost) Calabi-Yau manifold are given by $\mathcal{H}^1(L,\mathbb{R})$ (resp. $\mathcal{H}^1_{\psi}(L,\mathbb{R})$).

Assessment: non-included
This result by McLean on the infinitesimal deformation theory of special Lagrangians requires the full setup of calibrated geometry, Hodge theory on Riemannian manifolds, and the special Lagrangian condition. None of this is in mathlib.

## Statement 45: Theorem 1 (Lecture 21/22) — McLean-Joyce
Deformations of special Lagrangians are unobstructed, i.e. the moduli space is a smooth manifold B with $T_LB \cong H^1(L,\mathbb{R})$.

Assessment: non-included
McLean's theorem on the smoothness of the moduli space of special Lagrangians is a deep result in calibrated geometry requiring implicit function theorems in Banach spaces and the special Lagrangian deformation theory. Searches for "McLean" and "Joyce" returned no relevant results. This is entirely absent from mathlib.

## Statement 46: Definition 1 (Lecture 22) — Affine Structure
An affine structure on a manifold N is a set of coordinate charts with transition functions in $GL(n, \mathbb{Z}) \ltimes \mathbb{R}^n$.

Assessment: non-included
While mathlib has affine spaces (Mathlib/LinearAlgebra/AffineSpace/) and affine equivalences, it does not have the notion of an affine structure on a manifold in the sense of an atlas with affine transition functions. The concept of integral affine structures (with $GL(n,\mathbb{Z})$ transitions) relevant to mirror symmetry is absent.

## Statement 47: Corollary 1 (Lecture 22) — Two Affine Structures on B
B [the base of the special Lagrangian fibration] carries two affine structures.

Assessment: non-included
This corollary follows from the McLean-Joyce theorem and the two natural isomorphisms $T_LB \cong H^1(L,\mathbb{R})$ (symplectic and complex). The entire framework is absent from mathlib.

## Statement 48: Proposition 2 (Lecture 22) — Integrability of Mirror Complex Structure
$J^{\vee}$ [the almost-complex structure on the moduli space of special Lagrangian tori with flat connections] is integrable.

Assessment: non-included
This result about the integrability of the complex structure on the SYZ mirror requires the full theory of special Lagrangian fibrations and the moduli space construction. None of this is in mathlib.

## Statement 49: Proposition 3 (Lecture 22) — Mirror Kähler Form
$\omega^{\vee}$ is a Kähler form compatible with $J^{\vee}$.

Assessment: non-included
This result about the Kähler structure on the SYZ mirror is part of the SYZ mirror construction, which is entirely absent from mathlib. Mathlib does not formalize Kähler manifolds in the differential-geometric sense.

## Statement 50: Definition 1 (Lecture 24) — Superpotential
$W(L, \nabla) = \sum_{\substack{\beta \in \pi_2(X, L) \\ \mu(\beta) = 2}} n_{\beta} z_{\beta}(L, \nabla)$ where $z_{\beta} = e^{-2\pi \int_{\beta} \omega} \operatorname{hol}_{\partial\beta}(\nabla)$.

Assessment: non-included
The superpotential in the Landau-Ginzburg model context requires Maslov index theory, holomorphic disk counting, and the full Lagrangian Floer theory framework. Searches for "Maslov" returned no results. None of this is in mathlib.

## Statement 51: Theorem 1 (Lecture 25) — Matrix Factorizations Trivial Away from Critical Values
$H^0(MF(W-\lambda)) = 0$, i.e. all matrix factorizations are nullhomotopic, unless $\lambda$ is a critical value of W.

Assessment: non-included
Matrix factorizations are a concept from Landau-Ginzburg models and singularity theory. Searches for "matrix factorization" and "MatrixFactorization" returned no results. Mathlib does not contain the theory of matrix factorizations or Landau-Ginzburg models.
