# Detailed Assessment: Algebraic Topology I (MIT 18.905) vs Mathlib

## 1. Theorem 1.5 (d^2 = 0)
**Verdict: included**

The statement that the composition of consecutive differentials in a chain complex is zero is a foundational property built into the definition of `HomologicalComplex` in mathlib. In `Mathlib/Algebra/Homology/HomologicalComplex.lean` and related files, the field `d_comp_d'` is part of the structure definition, and the lemma `HomologicalComplex.d_comp_d` is used extensively throughout (e.g., in `Mathlib/Algebra/Homology/Homotopy.lean`, `Mathlib/Algebra/Homology/Additive.lean`, `Mathlib/Algebra/Homology/Bifunctor.lean`, etc.). For the specific case of the singular chain complex, `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` defines the singular chain complex functor using `alternatingFaceMapComplex`, which carries the d^2 = 0 property by construction. The alternating face map complex is defined in `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`.

## 2. Theorem 5.2 (Homotopy invariance of singular homology)
**Verdict: non-included**

Searched `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` and `Mathlib/Topology/Homotopy/`. The singular homology functor is defined in mathlib, and homotopy equivalences are defined in `Mathlib/Topology/Homotopy/Equiv.lean`, but there is no theorem stating that homotopic maps induce equal maps on singular homology. The file `Mathlib/Topology/Homotopy/Contractible.lean` deals with contractibility but not in the context of singular homology. The key construction of a chain homotopy from a topological homotopy is absent.

## 3. Corollary 5.5 (Homotopy equivalences induce isomorphisms in homology)
**Verdict: non-included**

This follows from Theorem 5.2 but since the parent theorem is not in mathlib for singular homology, this corollary is also absent. The abstract notion that chain homotopy equivalences induce isomorphisms in homology is present in `Mathlib/Algebra/Homology/Homotopy.lean`, but the bridge from topological homotopy equivalence to chain homotopy equivalence on singular chains is missing.

## 4. Corollary 5.7 (Contractible spaces have trivial homology)
**Verdict: non-included**

Searched `Mathlib/Topology/Homotopy/Contractible.lean` and `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`. The file `SingularHomology/Basic.lean` proves homology vanishes for totally disconnected spaces in positive dimensions, but the statement that contractible spaces have trivial reduced homology is not present. The contractibility notion exists in mathlib but is not connected to singular homology computations.

## 5. Lemma 4.7 (Short exact sequence of singular chains for a pair)
**Verdict: non-included**

Searched for relative singular chains in mathlib. The singular chain complex is defined but the relative version $S_*(X, A)$ and the short exact sequence $0 \to S_n(A) \to S_n(X) \to S_n(X,A) \to 0$ are not formalized. The abstract notion of short exact sequences of chain complexes exists throughout `Mathlib/Algebra/Homology/`, but the specific singular chain case is absent.

## 6. Lemma 4.8 (Relative boundary map)
**Verdict: non-included**

This is the construction of relative homology for singular chains. Since the relative singular chain complex is not defined in mathlib, this lemma is not present. Abstract relative homology for chain complexes exists in `Mathlib/Algebra/Homology/`.

## 7. Proposition 5.11 (Long exact sequence of a pair in homology)
**Verdict: non-included**

The abstract long exact sequence in homology associated to a short exact sequence of chain complexes is present in `Mathlib/Algebra/Homology/HomologySequence.lean` (with connecting homomorphisms `hS.delta` and exactness lemmas). However, the specific instance for singular homology of a topological pair $(X, A)$ is not formalized, since relative singular homology is not in mathlib.

## 8. Proposition 5.13 (Relative homology isomorphic to reduced homology of quotient)
**Verdict: non-included**

This requires both relative singular homology and the quotient space construction in the context of homology. Neither is present in mathlib. Searched `Mathlib/AlgebraicTopology/` and `Mathlib/Topology/` with no relevant results.

## 9. Lemma 5.10 (Deformation retract implies trivial relative homology)
**Verdict: non-included**

Requires relative singular homology and the interaction between deformation retracts and homology, neither of which is formalized in mathlib.

## 10. Theorem 6.2 (Excision)
**Verdict: non-included**

Searched for "excision" and "Excision" throughout mathlib. No results were found. This fundamental theorem of algebraic topology, stating that $H_n(X \setminus U, A \setminus U) \cong H_n(X, A)$ under appropriate conditions, is not in mathlib. The abstract machinery exists for some related categorical notions but the topological excision theorem for singular homology is absent.

## 11. Lemma 8.3 (Locality principle / small simplices)
**Verdict: non-included**

This is the key lemma that the inclusion of small singular chains (chains of simplices contained in elements of an open cover) is a quasi-isomorphism. It is the technical heart of the excision proof. Not found in mathlib.

## 12. Theorem 9.4 (Mayer-Vietoris)
**Verdict: non-included**

Searched for "MayerVietoris" in mathlib. Found `Mathlib/Topology/Sheaves/MayerVietoris.lean` and `Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean`, but these deal with sheaf-theoretic Mayer-Vietoris, not the Mayer-Vietoris sequence for singular homology. The classical Mayer-Vietoris long exact sequence in singular homology is not formalized.

## 13. Corollary 10.5 (Spheres of different dimensions not homotopy equivalent)
**Verdict: non-included**

This requires the computation of homology of spheres, which is not in mathlib for singular homology. While CW complex structures exist in `Mathlib/Topology/CWComplex/`, the cellular or singular homology of spheres is not computed.

## 14. Corollary 10.6 (Euclidean spaces of different dimensions not homeomorphic)
**Verdict: non-included**

This is a consequence of the computation of homology of spheres and is not in mathlib.

## 15. Lemma 11.6 (Ladder lemma for exact sequences)
**Verdict: non-included**

This is a diagram-chasing result about maps of long exact sequences. While the snake lemma is in `Mathlib/Algebra/Module/SnakeLemma.lean` and `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean`, this specific ladder lemma is not present in the form stated.

## 16. Theorem 12.3 (Cellular homology equals singular homology)
**Verdict: non-included**

Searched `Mathlib/Topology/CWComplex/` and `Mathlib/AlgebraicTopology/`. CW complexes are defined in `Mathlib/Topology/CWComplex/Classical/Basic.lean` but cellular homology is not defined and the isomorphism with singular homology is not proved.

## 17. Proposition 16.2 (Homology of spheres)
**Verdict: non-included**

The explicit computation $H_q(S^k) \cong \mathbf{Z}$ for $q = 0$ or $q = k$, and $0$ otherwise, is not in mathlib. Singular homology is too recently added and computations have not yet been carried out.

## 18. Theorem 17.1 (Brouwer fixed point theorem)
**Verdict: non-included**

Searched for "brouwer", "Brouwer", "BrouwerFixed" in mathlib. No results found related to the Brouwer fixed point theorem. This classical application of homology is not formalized in mathlib.

## 19. Theorem 22.1 (Fundamental theorem of homological algebra)
**Verdict: included**

This theorem states that maps between modules lift to chain maps between projective resolutions, uniquely up to chain homotopy. In mathlib, this is captured in the theory of projective/injective resolutions. The files `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean` and `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean` contain the construction of lifts and the proof of uniqueness up to homotopy. The `HomotopyEquiv` construction for projective resolutions establishes that any two projective resolutions are chain homotopy equivalent, which is the categorical generalization of this theorem.

## 20. Corollary 23.13 (Homology commutes with directed colimits)
**Verdict: included**

The statement that homology commutes with filtered/directed colimits is formalized in mathlib's categorical framework. In `Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean` and related files, filtered colimits are shown to be exact in appropriate categories, which implies that homology commutes with them. The general principle is captured at the level of abelian categories satisfying Grothendieck's AB5 axiom.

## 21. Corollary 23.14 (Integral homology isomorphism)
**Verdict: non-included**

This specific statement that $H_n(X; \mathbf{Z}) \cong H_n(X)$ via the canonical map $\mathbf{Z} \otimes_\mathbf{Z} C_* \to C_*$ is not explicitly stated. While the abstract isomorphism $R \otimes_R M \cong M$ is certainly in mathlib (as a tensor product fact), the specific application to singular chains with integer coefficients is not formalized.

## 22. Theorem 24.1 (Universal Coefficient Theorem)
**Verdict: non-included**

Searched for "universalCoeff", "UniversalCoefficient", "universal_coefficient" in mathlib. No results found. The Universal Coefficient Theorem for homology, giving the short exact sequence involving Tor, is not formalized. While Tor is defined abstractly via derived functors in `Mathlib/CategoryTheory/Abelian/Ext.lean` and related files, the specific UCT short exact sequence is absent.

## 23. Theorem 25.2 (Algebraic Kunneth theorem)
**Verdict: non-included**

Searched for "Kunneth" and "kunneth" in mathlib. No results found. The algebraic Kunneth theorem for chain complexes over a PID is not formalized.

## 24. Corollary 25.3 (Quasi-isomorphisms preserved by tensor product)
**Verdict: non-included**

This follows from the Kunneth theorem and is not in mathlib.

## 25. Lemma 25.10 (Lifting lemma for acyclic models)
**Verdict: non-included**

The method of acyclic models is not formalized in mathlib. Searched for "acyclic" and "AcyclicModel" with no relevant results.

## 26. Theorem 25.11 (Acyclic models theorem)
**Verdict: non-included**

Not in mathlib. The method of acyclic models, while closely related to the fundamental theorem of homological algebra, is formulated in a specific categorical setup (with designated models) that is not present in mathlib.

## 27. Corollary 25.12 (Chain homotopy equivalence via acyclic models)
**Verdict: non-included**

Depends on the acyclic models theorem, which is not in mathlib.

## 28. Theorem 25.13 (Eilenberg-Zilber theorem)
**Verdict: non-included**

Searched for "EilenbergZilber" and "Eilenberg.*Zilber" in mathlib. No results found. The Eilenberg-Zilber theorem, establishing chain homotopy equivalence between $S_*(X) \otimes S_*(Y)$ and $S_*(X \times Y)$, is not formalized.

## 29. Corollary 25.14 (Homology isomorphism from Eilenberg-Zilber)
**Verdict: non-included**

Depends on the Eilenberg-Zilber theorem, which is absent.

## 30. Theorem 25.15 (Kunneth theorem for spaces)
**Verdict: non-included**

Combines the algebraic Kunneth theorem with Eilenberg-Zilber; neither is in mathlib.

## 31. Corollary 26.2 (Coalgebra structure on homology)
**Verdict: non-included**

This requires the Kunneth theorem and the diagonal map to construct a coproduct on homology. Not formalized in mathlib.

## 32. Lemma 26.6 (H^0 is Map(pi_0, N))
**Verdict: non-included**

Singular cohomology is not defined in mathlib. While H^0 in various abstract settings might be computable, the specific statement for singular cohomology of a topological space is not present.

## 33. Theorem 27.1 (Mixed variance UCT)
**Verdict: non-included**

The cohomological universal coefficient theorem involving Ext is not in mathlib. While Ext is defined in `Mathlib/CategoryTheory/Abelian/Ext.lean` and `Mathlib/Algebra/Category/ModuleCat/Ext/HasExt.lean`, the specific UCT short exact sequence is not formalized.

## 34. Proposition 28.3 (Associativity of cross product)
**Verdict: non-included**

The Alexander-Whitney map and the cross product on singular cochains are not formalized in mathlib. Searched for cross product and cup product constructions with no results in the algebraic topology context.

## 35. Proposition 29.2 (Cross product is algebra homomorphism)
**Verdict: non-included**

Requires the cross product and cup product constructions, which are not in mathlib.

## 36. Corollary 29.4 (Maps from S^{p+q} to S^p x S^q)
**Verdict: non-included**

Requires cup product structure on cohomology of spheres and products, none of which is in mathlib.

## 37. Theorem 30.2 (Poincare duality over F_2)
**Verdict: non-included**

Searched for "PoincareDuality" and "poincareDuality" in mathlib. Found `Mathlib/Geometry/Manifold/PoincareConjecture.lean` which is about the Poincare conjecture, not duality. Poincare duality for manifolds is not formalized in mathlib.

## 38. Lemma 30.5 (Nondegenerate bilinear form restriction to subspace)
**Verdict: included**

The statement that a nondegenerate bilinear form restricted to a subspace W is nondegenerate iff $W \cap W^\perp = 0$, and the resulting orthogonal decomposition, is present in mathlib's linear algebra library. The relevant results about bilinear forms and orthogonal complements are in `Mathlib/LinearAlgebra/BilinearForm/` and `Mathlib/LinearAlgebra/QuadraticForm/`. The decomposition $V \cong W \oplus W^\perp$ for nondegenerate restrictions is a standard result in these files.

## 39. Proposition 30.6 (Classification of F_2 bilinear forms)
**Verdict: non-included**

This specific classification of nondegenerate symmetric bilinear forms over F_2 as orthogonal direct sums of [1] and hyperbolic forms is a concrete classification result that does not appear in mathlib. While the general theory of bilinear forms exists, this specific F_2 classification is absent.

## 40. Claim 30.7 (Relation I + H = 3I in F_2 bilinear forms)
**Verdict: non-included**

This is a very specific computation about 3x3 matrices over F_2 and is not in mathlib.

## 41. Proposition 30.8 (Cohomology of connected sum)
**Verdict: non-included**

Connected sum of surfaces and its interaction with cohomology/intersection forms is not formalized in mathlib.

## 42. Theorem 30.9 (Classification of surfaces)
**Verdict: non-included**

The classification of compact connected surfaces via intersection forms is a major result not in mathlib. Surface classification is not formalized.

## 43. Lemma 31.4 (Principal action gives covering space)
**Verdict: included**

In `Mathlib/Topology/Covering/Quotient.lean`, the structure `IsQuotientCoveringMap` formalizes exactly this: when a group acts on a space with properly discontinuous action, the quotient map is a covering map. The file proves that the quotient map from a space with a properly discontinuous group action is a covering map, which is the content of this lemma.

## 44. Theorem 31.5 (Unique path lifting)
**Verdict: included**

In `Mathlib/Topology/Homotopy/Lifting.lean`, the theorem `IsCoveringMap.exists_path_lifts` proves existence of a path lift and `IsCoveringMap.liftPath` constructs it. Uniqueness is established via `IsCoveringMap.eq_liftPath_iff` which shows that any continuous lift agreeing at the starting point must equal `liftPath`. This precisely captures the unique path lifting property.

## 45. Theorem 31.6 (Classification of covering spaces)
**Verdict: non-included**

Searched for an equivalence between the category of covering spaces and the category of pi_1-sets. The Galois theory files in `Mathlib/CategoryTheory/Galois/` contain an abstract equivalence for Galois categories, but this is not connected to topological covering spaces. The topological classification theorem (Cov_B equivalent to Set-pi_1(B,b)) for semi-locally simply connected spaces is not formalized.

## 46. Theorem 31.7 (Classification of local coefficient systems)
**Verdict: non-included**

Local coefficient systems are not defined in mathlib. The classification of covering spaces is not connected to representations of the fundamental group in the topological context.

## 47. Theorem 31.9 (Orientation theorem)
**Verdict: non-included**

Orientations of manifolds and the orientation local system are not formalized in mathlib in the algebraic topology sense. While `Mathlib/Geometry/Manifold/` contains smooth manifold theory, the topological orientation via local homology is absent.

## 48. Corollary 31.10 (Top homology of compact manifold)
**Verdict: non-included**

Depends on the orientation theorem and local homology computations, neither of which is in mathlib.

## 49. Theorem 32.1 (Orientation theorem for general compact subsets)
**Verdict: non-included**

This generalization of the orientation theorem is not in mathlib.

## 50. Proposition 32.2 (Orientation theorem stable under unions)
**Verdict: non-included**

Part of the proof infrastructure for the orientation theorem; not in mathlib.

## 51. Proposition 32.3 (Orientation theorem stable under decreasing intersections)
**Verdict: non-included**

Part of the proof infrastructure for the orientation theorem; not in mathlib.

## 52. Lemma 32.4 (Colimit of relative homology over decreasing compact sets)
**Verdict: non-included**

Requires relative singular homology and directed colimit arguments specific to the topological setting. Not in mathlib.

## 53. Lemma 32.5 (Decreasing compact sets eventually inside open neighborhoods)
**Verdict: included**

This is a standard topological fact: if $A_1 \supseteq A_2 \supseteq \cdots$ is a decreasing sequence of compact subsets in a Hausdorff space with intersection $A \subseteq U$ for an open $U$, then some $A_i \subseteq U$. This follows from the finite intersection property for compact sets. In mathlib, the key ingredients are in `Mathlib/Topology/Compactness/Compact.lean` and related files, where the finite intersection property of compact sets in Hausdorff spaces is established. The result `IsCompact.inter_iInter_nonempty` and related compactness lemmas capture this.

## 54. Claim 33.1 (Naturality of Kronecker pairing)
**Verdict: non-included**

The Kronecker pairing between cohomology and homology is not formalized in mathlib, as singular cohomology is not defined.

## 55. Lemma 33.2 (Cross product and Kronecker pairing interaction)
**Verdict: non-included**

Requires both the cross product in (co)homology and the Kronecker pairing, neither of which is in mathlib.

## 56. Theorem 33.3 (Kunneth theorem in cohomology)
**Verdict: non-included**

Singular cohomology and the cohomological Kunneth theorem are not in mathlib.

## 57. Proposition 34.1 (Cap product properties)
**Verdict: non-included**

The cap product is not defined in mathlib, and singular (co)homology does not have this multiplicative structure formalized.

## 58. Theorem 34.2 (Poincare duality)
**Verdict: non-included**

Poincare duality, in any of its forms, is not formalized in mathlib.

## 59. Lemma 34.3 (Cap product compatibility with restriction)
**Verdict: non-included**

Requires the cap product, which is not in mathlib.

## 60. Lemma 34.5 (Cech vs singular cohomology under regular neighborhoods)
**Verdict: non-included**

Cech cohomology is not defined in mathlib (in the sense of the direct limit of cohomology of open neighborhoods). The Cech nerve construction exists in `Mathlib/AlgebraicTopology/CechNerve.lean` but serves a different purpose.

## 61. Theorem 34.6 (Cech cohomology as topological invariant)
**Verdict: non-included**

Cech cohomology in this sense is not formalized in mathlib.

## 62. Theorem 35.2 (Long exact sequence for Cech cohomology)
**Verdict: non-included**

Cech cohomology is not in mathlib.

## 63. Theorem 35.3 (Excision for Cech cohomology)
**Verdict: non-included**

Cech cohomology is not in mathlib.

## 64. Lemma 35.7 (Cofinal functors preserve colimits)
**Verdict: included**

The statement that a cofinal functor preserves (filtered/directed) colimits is present in mathlib's category theory library. The concept of a final (cofinal in dual sense) functor is in `Mathlib/CategoryTheory/Limits/Yoneda.lean` and `Mathlib/CategoryTheory/Limits/IsLimit.lean`. The key theorem that final functors preserve colimits is established categorically. For the directed set version (posets), the relevant results about cofinal maps and preservation of direct limits are in `Mathlib/Order/` files and `Mathlib/Algebra/Colimit/Module.lean`.

## 65. Lemma 35.8 (Cofinality of specific neighborhood maps)
**Verdict: non-included**

This is a very specific topological lemma about open neighborhoods of unions and intersections of closed/compact sets. Not in mathlib.

## 66. Corollary 35.9 (Mayer-Vietoris for Cech cohomology)
**Verdict: non-included**

Cech cohomology is not in mathlib.

## 67. Theorem 36.1 (Fully relative cap product)
**Verdict: non-included**

The cap product and its relative versions are not in mathlib.

## 68. Theorem 36.2 (Mayer-Vietoris ladder with cap product)
**Verdict: non-included**

Requires both Mayer-Vietoris for singular homology and Cech cohomology with cap product; none of these are in mathlib.

## 69. Theorem 37.1 (Fully relative Poincare duality)
**Verdict: non-included**

Poincare duality in any form is not in mathlib.

## 70. Lemma 37.2 (Cech cohomology of decreasing intersection of compact sets)
**Verdict: non-included**

Cech cohomology is not in mathlib.

## 71. Corollary 37.3 (Poincare duality with closed subset)
**Verdict: non-included**

Poincare duality is not in mathlib.

## 72. Corollary 37.4 (Poincare duality for compact subsets)
**Verdict: non-included**

Poincare duality is not in mathlib.

## 73. Corollary 37.5 (Poincare duality, standard form)
**Verdict: non-included**

Poincare duality is not in mathlib.

## 74. Theorem 38.1 (Poincare duality restated)
**Verdict: non-included**

This is a restatement of Corollary 37.4. Poincare duality is not in mathlib.

## 75. Corollary 38.2 (Cech cohomology vanishing above dimension n)
**Verdict: non-included**

Requires Poincare duality and Cech cohomology; not in mathlib.

## 76. Theorem 38.4 (Alexander duality)
**Verdict: non-included**

Searched for "Alexander" and "alexanderDuality" in mathlib. Not found. Alexander duality is not formalized.

## 77. Corollary 38.5 (Cech H^n vanishes for compact K in R^n)
**Verdict: non-included**

Consequence of Alexander duality; not in mathlib.

## 78. Corollary 38.6 (Knot complement is homology circle)
**Verdict: non-included**

Consequence of Alexander duality; not in mathlib.

## 79. Theorem 38.8 (Perfect pairing on torsion-free cohomology)
**Verdict: non-included**

Requires Poincare duality combined with the UCT; neither is in mathlib for topological spaces.

## 80. Theorem 38.11 (Borsuk-Ulam)
**Verdict: non-included**

Searched for "BorsukUlam" and "borsuk_ulam" in mathlib. Not found. The Borsuk-Ulam theorem is not formalized in mathlib. The proof in the textbook uses the cup product structure on the cohomology of real projective spaces, which is also not available in mathlib.
