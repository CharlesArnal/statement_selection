# Detailed Assessment: Mathlib Inclusion Status

## Section 1: Continuous representations of topological groups

**Proposition 1.6** (continuity of Banach representations): **non-included**
This result states that for Banach spaces, continuity of a representation is equivalent to continuity in the strong operator topology. While mathlib has general theory of continuous linear maps in `Mathlib/Topology/Algebra/Module/` and bounded operators, it does not specifically formulate this criterion for group representations on Banach spaces. The relevant representation theory infrastructure in `Mathlib/RepresentationTheory/` does not address topological continuity conditions.

## Section 2: K-finite vectors and matrix coefficients

**Lemma 2.2** (Hilbert space isomorphism for L^2(K)): **non-included**
This establishes the isometric isomorphism between the direct sum of endomorphism algebras of irreducible representations and L^2(K). While mathlib has L^2 spaces in `Mathlib/MeasureTheory/Function/L2Space.lean` and representation theory in `Mathlib/RepresentationTheory/`, there is no formalization of this decomposition for compact groups.

**Theorem 2.4** (Peter-Weyl theorem): **non-included**
The Peter-Weyl theorem asserts that matrix coefficients of irreducible representations form an orthonormal basis of L^2(K) for compact groups K. Despite being a fundamental result, it is not present in mathlib. Mathlib has `Mathlib/RepresentationTheory/` with basic representation theory and `Mathlib/Analysis/Fourier/` with Fourier analysis, but the Peter-Weyl theorem is not formalized.

## Section 3: Algebras of measures on locally compact groups

**Lemma 3.2** (Cauchy sequences of measures): **non-included**
A technical lemma about compactly supported measures. Mathlib has measure theory in `Mathlib/MeasureTheory/` but this specific result about Cauchy sequences in C(X)^* is not present.

**Proposition 3.3** (dual of C(X) is compactly supported measures): **non-included**
The Riesz representation theorem identifying C(X)^* with compactly supported measures. While mathlib has versions of the Riesz representation theorem (e.g., in `Mathlib/MeasureTheory/Measure/Regular.lean`), this specific formulation for locally compact spaces is not present in the required generality.

**Corollary 3.5** (tensor product of measure spaces): **non-included**
The isomorphism of completed tensor products of measure spaces. Not present in mathlib.

**Lemma 3.7** (continuity of group algebra action): **non-included**
Continuity of the group algebra action on a representation. Not formalized in mathlib.

**Corollary 3.8** (extension of action to measures): **non-included**
Extension of a continuous representation to a continuous algebra homomorphism from compactly supported measures. Not in mathlib.

## Section 4: Plancherel formulas, Dirac sequences, smooth vectors

**Proposition 4.1** (Plancherel theorem for compact groups): **non-included**
The Plancherel formula for compact groups. Mathlib has some Plancherel-type results in `Mathlib/Analysis/Fourier/` but only for abelian groups (Fourier transform on LCA groups), not for general compact groups.

**Proposition 4.3** (Plancherel formula for compact Lie groups): **non-included**
A refined Plancherel formula with absolute convergence for smooth functions on compact Lie groups. Not in mathlib.

**Lemma 4.5** (existence of Dirac sequences): **non-included**
Existence of approximate identities / Dirac sequences in C_c(G). While mathlib has general topology results, this specific construction for locally compact groups is not formalized.

**Corollary 4.6** (C_c(G) dense in Meas_c(G)): **non-included**
Density of continuous compactly supported functions in the space of compactly supported measures. Not in mathlib.

**Corollary 4.7** (K-finite vectors dense): **non-included**
Density of K-finite vectors in continuous representations of compact groups. Not in mathlib.

**Corollary 4.8** (L^2(K)^fin dense in C^k(K)): **non-included**
Density of K-finite vectors in smooth function spaces. Not in mathlib.

**Corollary 4.9** (irreducible reps of compact groups are finite-dimensional): **non-included**
Every irreducible continuous representation of a compact group is finite-dimensional. This is a classical result but is not formalized in mathlib. The closest material is in `Mathlib/RepresentationTheory/` but it deals with finite group representations and algebraic representations rather than topological representations of compact groups.

**Proposition 4.13** (smooth vectors and Lie algebra action): **non-included**
The construction of the derived representation on smooth vectors. Not in mathlib; the Lie group / Lie algebra representation theory in mathlib (`Mathlib/Algebra/Lie/`) is purely algebraic.

**Proposition 4.15** (V^infty dense, V^fin subset V^infty): **non-included**
Density of smooth vectors and inclusion of K-finite vectors in smooth vectors. Not in mathlib.

## Section 5: Admissible representations and (g, K)-modules

**Proposition 5.4** (K-finite vectors are smooth and form g-submodule): **non-included**
Not in mathlib. The (g, K)-module formalism is entirely absent from mathlib.

**Proposition 5.10** (K-finite vectors form admissible (g,K)-module): **non-included**
Not in mathlib. No formalization of admissible (g, K)-modules exists.

**Theorem 5.13** (Cartan's theorem on maximal compact subgroups): **non-included**
The existence and essential uniqueness of maximal compact subgroups in semisimple Lie groups. This deep structural result is not in mathlib; mathlib does not have the theory of real semisimple Lie groups.

**Theorem 5.15** (Harish-Chandra admissibility theorem): **non-included**
Every irreducible unitary representation of a semisimple Lie group is admissible. This foundational result for the representation theory of real semisimple groups is not in mathlib.

## Section 6: Weakly analytic vectors

**Theorem 6.3** (Harish-Chandra analyticity theorem): **non-included**
K-finite vectors in admissible representations are weakly analytic. Not in mathlib.

**Theorem 6.6** (Elliptic regularity): **non-included**
Smooth solutions of elliptic PDE with analytic coefficients are analytic. While mathlib has some PDE-related infrastructure in `Mathlib/Analysis/`, elliptic regularity is not formalized.

**Corollary 6.7** (smooth solutions of elliptic PDE are analytic): **non-included**
A consequence of elliptic regularity. Not in mathlib.

**Corollary 6.11** (G-action determined by (g,K)-module): **non-included**
Not in mathlib; requires the analytic theory of (g, K)-modules.

**Corollary 6.12** (closure of sub-(g,K)-module is G-invariant): **non-included**
Not in mathlib.

**Corollary 6.13** (bijection between subreps and (g,K)-submodules): **non-included**
Not in mathlib.

**Corollary 6.14** (irreducibility correspondence): **non-included**
Not in mathlib.

**Corollary 6.15** (finite length implies Harish-Chandra): **non-included**
Not in mathlib.

**Theorem 6.16** (exact faithful functor Rep G -> HC_G): **non-included**
Not in mathlib. The entire Harish-Chandra module theory is absent.

## Section 7: Infinitesimal equivalence and globalization

**Proposition 7.1** (infinitesimally equivalent unitary reps are isomorphic): **non-included**
Not in mathlib.

**Lemma 7.2** (Dixmier's lemma): **non-included**
The result that End_A(M) = C for simple modules over countable-dimensional algebras. While mathlib has Schur's lemma for algebraically closed fields in `Mathlib/RingTheory/SimpleModule/Basic.lean`, Dixmier's specific version for countable-dimensional algebras over C is not present.

**Corollary 7.3** (Schur's lemma for (g,K)-modules): **non-included**
Not in mathlib in this specific form for (g, K)-modules, although the abstract Schur's lemma is available.

**Theorem 7.5** (Harish-Chandra globalization theorem): **non-included**
Not in mathlib. This deep result about integrating Harish-Chandra modules to unitary representations requires analytic methods beyond the scope of current mathlib.

**Corollary 7.6** (equivalence of unitary reps and unitary HC modules): **non-included**
Not in mathlib.

## Section 8: Highest weight modules and Verma modules

**Proposition 8.5** (Verma module is free over U(n_-)): **non-included**
The isomorphism M_lambda = U(n_-) as left U(n_-)-modules. While mathlib has Lie algebra modules in `Mathlib/Algebra/Lie/Submodule.lean` and the universal enveloping algebra in `Mathlib/Algebra/Lie/UniversalEnveloping.lean`, Verma modules are not defined or studied in mathlib.

**Corollary 8.7** (weight decomposition of Verma module): **non-included**
The weight structure of Verma modules. Not in mathlib; Verma modules are not formalized.

**Proposition 8.8** (universal property of Verma modules): **non-included**
The universal property characterizing Verma modules. Not in mathlib.

**Proposition 8.9** (unique irreducible quotient of Verma module): **non-included**
Not in mathlib.

**Corollary 8.10** (classification of irreducible highest weight modules): **non-included**
Not in mathlib. While mathlib has weight spaces in `Mathlib/Algebra/Lie/Weights/`, it does not have highest weight modules or their classification.

**Proposition 8.12** (L_lambda finite-dimensional iff lambda in P_+): **non-included**
The criterion for finite-dimensionality of irreducible highest weight modules. Not in mathlib.

## Section 9: Representations of SL_2(R)

**Proposition 9.1** (classification of simple (g,K)-modules for SL_2(R)): **non-included**
The explicit classification of Harish-Chandra modules for SL_2(R). Not in mathlib.

**Theorem 9.3** (Gelfand-Naimark-Bargmann classification for SL_2(R)): **non-included**
The classification of irreducible unitary representations of SL_2(R). Not in mathlib.

## Section 10: Chevalley restriction theorem and Chevalley-Shephard-Todd theorem

**Theorem 10.1** (Chevalley restriction theorem): **non-included**
The isomorphism C[g]^g -> C[h]^W. This fundamental result about invariant polynomials on Lie algebras is not in mathlib. Mathlib has root systems in `Mathlib/LinearAlgebra/RootSystem/` and Lie algebras in `Mathlib/Algebra/Lie/`, but the Chevalley restriction theorem is not formalized.

**Theorem 10.6** (Chevalley-Shephard-Todd theorem, part I): **non-included**
C[V]^G is a polynomial algebra iff G is a complex reflection group. This result from invariant theory is not in mathlib. There is no formalization of complex reflection groups in mathlib.

## Section 11: Proof of the CST theorem, part I

**Lemma 11.1** (generators of invariant algebra): **included**
The statement that invariants of a finite group acting on a polynomial ring are finitely generated is essentially captured in mathlib's treatment of Noetherian rings and finite group actions. The general finite generation of invariant rings under finite group actions is available through `Mathlib/RingTheory/Noetherian/Basic.lean` and related files, though the specific formulation in terms of ideal generators may differ.

**Lemma 11.3** (complex reflection group invariant ideal property): **non-included**
A technical lemma specific to complex reflection groups. Not in mathlib.

**Lemma 11.4** (algebraic independence of generators): **non-included**
Not in mathlib in this specific form for invariant theory.

**Lemma 11.6** (group actions on affine spaces): **non-included**
Properties of finite group actions on affine spaces including the orbit-ideal correspondence. Not in mathlib in this algebro-geometric formulation.

## Section 12: Chevalley-Shephard-Todd theorem, part II

**Proposition 12.1** (Hilbert-Noether theorem): **included**
The statement that A is integral over A^G for a finite group G is essentially available in mathlib. The integrality of elements over invariant subrings under finite group actions can be established using `Mathlib/RingTheory/IntegralClosure/` and related files. The finite generation of A^G (the Hilbert-Noether lemma) also follows from general Noetherian results in mathlib.

**Theorem 12.2** (CST theorem, part II): **non-included**
The freeness of C[V] over C[V]^G and the regular representation structure. Not in mathlib.

**Lemma 12.3** (graded Nakayama lemma): **non-included**
A graded version of Nakayama's lemma for graded modules. While mathlib has Nakayama's lemma in `Mathlib/RingTheory/Nakayama.lean`, this graded version is not present.

**Proposition 12.4** (Ext vanishing for polynomial rings): **non-included**
The vanishing of Ext^i(M, N) for i > n over k[x_1,...,x_n]. While mathlib has some homological algebra in `Mathlib/Algebra/Homology/`, this specific global dimension result for polynomial rings is not formalized.

**Theorem 12.5** (Hilbert syzygies theorem): **non-included**
The rationality of Hilbert series for finitely generated graded modules over polynomial rings. While mathlib has Hilbert polynomials in `Mathlib/RingTheory/Polynomial/HilbertPoly.lean`, the full Hilbert syzygies theorem with free resolutions is not formalized.

**Lemma 12.6** (dimension drop by one element): **non-included**
A basic dimension inequality in commutative algebra. Not explicitly in mathlib in this form.

**Corollary 12.7** (dimension lower bound for zero sets): **non-included**
Not in mathlib.

**Lemma 12.8** (Koszul complex exactness for regular sequences): **included**
The exactness of the Koszul complex for regular sequences is essentially available in mathlib through `Mathlib/RingTheory/Regular/RegularSequence.lean`, which defines regular sequences and establishes their basic properties.

**Proposition 12.9** (isolated zero implies regular sequence): **included**
The result that homogeneous polynomials with only the origin as common zero form a regular sequence is closely related to material in `Mathlib/RingTheory/Regular/RegularSequence.lean`, though the exact formulation may not be present. The concept of regular sequences and their relation to complete intersections is partially available.

**Proposition 12.10** (freeness and rank for module over invariants): **non-included**
Not in mathlib.

## Section 13: Kostant's theorem

**Theorem 13.1** (Kostant's theorem for Sg): **non-included**
The freeness of Sg over (Sg)^g and the rank formula. This deep result in Lie theory is not in mathlib.

**Lemma 13.2** (L^2 convergence of Poisson-like kernel): **non-included**
A technical analysis lemma. Not in mathlib.

**Theorem 13.3** (Kostant's Hilbert polynomial formula): **non-included**
Not in mathlib.

**Corollary 13.4** (constant term identity for root products): **non-included**
A combinatorial identity involving root systems. Not in mathlib.

**Theorem 13.5** (Kostant's theorem for U(g)): **non-included**
The structure of U(g) as a Z(g)-module. While mathlib has the universal enveloping algebra in `Mathlib/Algebra/Lie/UniversalEnveloping.lean`, the center of U(g) and its structure theory are not developed.

## Section 14: Harish-Chandra isomorphism, maximal quotients

**Theorem 14.1** (Harish-Chandra isomorphism): **non-included**
The isomorphism Z(g) -> C[h^*]^{W bullet}. This fundamental result in Lie theory is not in mathlib. The center of the universal enveloping algebra and the Harish-Chandra map are not formalized.

**Corollary 14.3** (dim Hom_g(V, U_chi) = dim V[0]): **non-included**
Not in mathlib.

**Corollary 14.4** (V tensor U_chi is Harish-Chandra): **non-included**
Not in mathlib.

**Corollary 14.5** (irreducible locally finite bimodules are HC): **non-included**
Not in mathlib.

## Section 15: Category O of g-modules - I

**Lemma 15.3** (finite-dimensional weight spaces in O): **non-included**
Category O is not defined in mathlib. The BGG category O and its properties are entirely absent.

**Corollary 15.4** (Z(g) acts through finite-dim quotient on O): **non-included**
Not in mathlib.

**Corollary 15.7** (decomposition of O by infinitesimal character): **non-included**
Not in mathlib.

**Lemma 15.9** (finite length in O): **non-included**
Not in mathlib.

**Theorem 15.11** (Verma's theorem on Verma module embeddings): **non-included**
Not in mathlib. Verma modules and their homomorphisms are not formalized.

**Proposition 15.12** (stabilizer in W of point in h^*/Q): **non-included**
Not in mathlib.

## Section 16: Category O of g-modules - II

**Corollary 16.1** (equivalent conditions for dominant weights): **non-included**
Not in mathlib.

**Proposition 16.2** (projective covers in Noetherian abelian categories): **non-included**
The general theory of projective covers in abelian categories. While mathlib has some category theory in `Mathlib/CategoryTheory/`, this specific result about projective covers with the Krull-Schmidt property is not formalized.

**Proposition 16.4** (dominant Verma modules are projective in O): **non-included**
Not in mathlib.

**Corollary 16.5** (tensor with finite-dim preserves projectivity): **non-included**
Not in mathlib.

**Corollary 16.6** (O has enough projectives): **non-included**
Not in mathlib.

## Section 17: The nilpotent cone of g

**Lemma 17.1** (principal sl_2 decomposition of g): **non-included**
The decomposition of the adjoint representation under the principal sl_2 subalgebra. While mathlib has `Mathlib/Algebra/Lie/Sl2.lean`, the principal sl_2 subalgebra and its role in the structure theory are not developed.

**Lemma 17.2** (regularity of sum of simple root vectors): **non-included**
Not in mathlib.

**Corollary 17.3** (B_+-orbit of principal nilpotent): **non-included**
Not in mathlib.

**Proposition 17.4** (nilpotent cone is reduced): **non-included**
Not in mathlib. The nilpotent cone is not defined as an algebraic-geometric object in mathlib.

**Proposition 17.6** (nilpotent cone properties): **non-included**
Not in mathlib.

**Corollary 17.7** (U_chi is a domain): **non-included**
Not in mathlib.

## Section 18: Maps of finite type, Duflo-Joseph theorem

**Proposition 18.2** (Hom_fin(M,N) is admissible bimodule): **non-included**
Not in mathlib. The theory of finite type maps between modules in category O is entirely absent.

**Proposition 18.3** (Hom_fin commutes with tensor): **non-included**
Not in mathlib.

**Proposition 18.5** (multiplicity of V in Hom_fin(M_lambda, M_lambda)): **non-included**
Not in mathlib.

**Proposition 18.7** (injectivity of action map): **non-included**
Not in mathlib.

**Corollary 18.8** (Duflo-Joseph theorem): **non-included**
The isomorphism U_{chi} -> Hom_fin(M_lambda, M_lambda). Not in mathlib.

**Corollary 18.9** (V tensor U_chi -> Hom_fin isomorphism): **non-included**
Not in mathlib.

**Corollary 18.10** (infinitesimal characters of tensor products): **non-included**
Not in mathlib.

**Corollary 18.11** (HC bimodule decomposition): **non-included**
Not in mathlib.

## Section 19: Principal series representations

**Proposition 19.1** (residual finiteness of U(g)): **non-included**
The faithfulness of the action of U(g) on direct product of all finite-dimensional modules. Not in mathlib.

**Proposition 19.3** (Frobenius reciprocity for principal series): **non-included**
Not in mathlib.

**Proposition 19.4** (right action formula on M(lambda,mu)): **non-included**
Not in mathlib.

**Proposition 19.5** (isomorphism of principal series): **non-included**
Not in mathlib.

**Proposition 19.7** (exactness of H_lambda): **non-included**
Not in mathlib.

## Section 20: BGG reciprocity and BGG Theorem

**Lemma 20.1** (Ext vanishing for free U(n_-)-modules): **non-included**
Not in mathlib. The homological algebra of category O is absent.

**Corollary 20.2** (Ext vanishing for standardly filtered): **non-included**
Not in mathlib.

**Theorem 20.3** (characterization of standardly filtered modules): **non-included**
Not in mathlib.

**Lemma 20.4** (K=0 condition for standard filtrations): **non-included**
Not in mathlib.

**Corollary 20.5** (free U(n_-)-modules are standardly filtered): **non-included**
Not in mathlib.

**Theorem 20.6** (BGG reciprocity): **non-included**
The equality d^*_{lambda,mu} = d_{mu,lambda} relating multiplicities of standard modules in projective covers to composition multiplicities of Verma modules. This fundamental result in the theory of category O is not in mathlib.

**Corollary 20.7** (Cartan matrix formula): **non-included**
Not in mathlib.

**Proposition 20.9** (duality functor properties): **non-included**
Not in mathlib.

**Corollary 20.10** (enough injectives in O): **non-included**
Not in mathlib.

**Theorem 20.13** (BGG theorem): **non-included**
The converse to Verma's theorem: L_{mu-rho} occurs in the composition series of M_{lambda-rho} implies mu preceq lambda. Not in mathlib.

**Corollary 20.14** (equivalence of composition/embedding conditions): **non-included**
Not in mathlib.

## Section 21: Kazhdan-Lusztig theory

**Proposition 21.1** (T_w basis of Hecke algebra): **non-included**
The Hecke algebra and its standard basis. There is no Hecke algebra formalization in mathlib.

**Theorem 21.5** (existence/uniqueness of Kazhdan-Lusztig polynomials): **non-included**
Not in mathlib. Kazhdan-Lusztig polynomials are not defined in mathlib.

**Theorem 21.6** (Kazhdan-Lusztig conjecture): **non-included**
The deep theorem (proved by Beilinson-Bernstein and Brylinski-Kashiwara) relating KL polynomials to multiplicities in category O. Not in mathlib.

## Section 22: Projective functors

**Theorem 22.4** (i_lambda isomorphism for projective theta-functors): **non-included**
Not in mathlib. The theory of projective functors on category O is entirely absent.

**Proposition 22.5** (lifting projective theta-functors): **non-included**
Not in mathlib.

**Corollary 22.6** (lifting isomorphisms and decompositions): **non-included**
Not in mathlib.

**Proposition 22.7** (decomposition of projective functors): **non-included**
Not in mathlib.

## Section 23: Classification of projective functors

**Theorem 23.1** (projective functors determined by [F]): **non-included**
Not in mathlib.

**Theorem 23.2** (W-invariance of [F]): **non-included**
Not in mathlib.

**Lemma 23.3** (domination lemma): **non-included**
Not in mathlib.

**Lemma 23.4** (norm inequality for dominant weights): **non-included**
Not in mathlib.

**Theorem 23.6** (classification of indecomposable projective functors): **non-included**
Not in mathlib.

**Lemma 23.7** (S_*(F) characterization): **non-included**
Not in mathlib.

## Section 24: Translation functors

**Theorem 24.1** (translation functors equivalence): **non-included**
Not in mathlib. Translation functors are not defined.

**Theorem 24.4** (two-sided ideals and submodules correspondence): **non-included**
Not in mathlib.

**Corollary 24.5** (simple algebra criterion for U_theta): **non-included**
Not in mathlib.

## Section 25: Harish-Chandra bimodules

**Theorem 25.4** (Duflo's theorem on primitive ideals): **non-included**
Duflo's theorem that every prime ideal in U_theta is primitive and is the annihilator of a simple highest weight module. Not in mathlib. The theory of primitive ideals in enveloping algebras is not developed.

**Lemma 25.5** (enough projectives in HC^1_theta): **non-included**
Not in mathlib.

**Theorem 25.6** (classification of simples in HC^1_theta): **non-included**
Not in mathlib.

**Corollary 25.7** (finite length of HC bimodules): **non-included**
Not in mathlib.

**Theorem 25.8** (Bernstein-Gelfand equivalence): **non-included**
The equivalence between HC^1_theta and category O_chi. Not in mathlib.

**Proposition 25.10** (fully faithful criterion for T_lambda): **non-included**
Not in mathlib.

**Corollary 25.11** (realizability of HC bimodules): **non-included**
Not in mathlib.

## Section 26: Representations of SL_2(C)

**Proposition 26.1** (principal series for sl_2): **non-included**
Explicit description of Harish-Chandra bimodules for sl_2. Not in mathlib.

**Theorem 26.3** (Gelfand-Naimark classification for SL_2(C)): **non-included**
Classification of irreducible unitary representations of SL_2(C). Not in mathlib.

## Section 27: Geometry of complex semisimple Lie groups

**Theorem 27.3** (Borel-Weil theorem): **non-included**
The realization of irreducible representations as spaces of sections of line bundles on flag varieties. Not in mathlib. While mathlib has some algebraic geometry in `Mathlib/AlgebraicGeometry/`, the flag variety and its line bundles are not formalized.

**Corollary 27.5** (partial flag variety version of Borel-Weil): **non-included**
Not in mathlib.

**Theorem 27.8** (Springer resolution): **non-included**
The resolution of singularities of the nilpotent cone via the cotangent bundle of the flag variety. Not in mathlib.

**Theorem 27.11** (Kirillov-Kostant symplectic structure): **non-included**
The natural symplectic structure on coadjoint orbits. Not in mathlib. While mathlib has some symplectic geometry concepts, this specific result about coadjoint orbits is absent.

**Corollary 27.12** (codimension of singular locus of N): **non-included**
Not in mathlib.

**Corollary 27.13** (normality of N): **non-included**
Not in mathlib.

**Proposition 27.14** (properties of normal varieties): **non-included**
Basic properties of normal algebraic varieties. While mathlib has `Mathlib/AlgebraicGeometry/` with some normality concepts in rings, these geometric properties are not fully formalized.

**Proposition 27.15** (O(Y) -> O(X) isomorphism for resolutions): **non-included**
Not in mathlib.

**Theorem 27.16** (O(N) -> O(T^*F) isomorphism): **non-included**
Not in mathlib.

## Section 28: D-modules

**Proposition 28.9** (D-module = flat connection): **non-included**
The equivalence between left D-modules and O_X-modules with flat connections. Not in mathlib. D-modules are not formalized in mathlib.

## Section 29: Beilinson-Bernstein localization

**Theorem 29.1** (Beilinson-Bernstein: U_0 = D(F)): **non-included**
Not in mathlib. The Beilinson-Bernstein localization theory is entirely absent.

**Theorem 29.2** (Beilinson-Bernstein localization theorem): **non-included**
The equivalence between U_0-modules and D-modules on the flag variety. Not in mathlib.

**Corollary 29.4** (D-affinity of partial flag varieties): **non-included**
Not in mathlib.

**Theorem 29.6** (Beilinson-Bernstein for twisted D-modules): **non-included**
Not in mathlib.

**Theorem 29.7** (BB localization for antidominant lambda): **non-included**
Not in mathlib.

## Section 30: D-modules on algebraic varieties

**Proposition 30.2** (support of irreducible D-module is irreducible): **non-included**
Not in mathlib.

**Theorem 30.4** (Kashiwara's equivalence): **non-included**
Kashiwara's theorem relating D-modules supported on a closed subvariety to D-modules on that subvariety. Not in mathlib.

**Proposition 30.18** (K-equivariant D-modules on D-affine varieties): **non-included**
Not in mathlib.

**Corollary 30.20** (equivariant BB localization): **non-included**
Not in mathlib.

## Section 31: Classification of irreducible (g, K)-modules

**Theorem 31.1** (finitely many equivariant D-modules for finite orbit stratification): **non-included**
Not in mathlib.

**Proposition 31.3** (K acts on F with finitely many orbits): **non-included**
Not in mathlib.

**Theorem 31.4** (classification of irreducible (g,K)-modules): **non-included**
The classification of irreducible (g, K)-modules via the Beilinson-Bernstein equivalence and equivariant D-modules on the flag variety. Not in mathlib.
