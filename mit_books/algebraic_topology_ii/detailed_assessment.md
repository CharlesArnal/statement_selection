Proposition 1.13:
included
Corresponds to `Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits` from Mathlib/CategoryTheory/Adjunction/Limits.lean

Lemma 1.14 [Yoneda lemma]:
included
Corresponds to `yoneda` and `yonedaEquiv` in Mathlib/CategoryTheory/Yoneda.lean

Proposition 2.2:
included
Corresponds to `CartesianClosed` typeclass and associated API in Mathlib/CategoryTheory/Closed/Cartesian.lean

Lemma 2.4:
non-included
Searched in Mathlib/Topology/ and Mathlib/CategoryTheory/. The notion of quotient map exists as `Topology.IsQuotientMap` but the characterization as effective epimorphism in the category Top is not formalized.

Proposition 2.7:
non-included
Searched in Mathlib/Topology/ and Mathlib/CategoryTheory/Closed/. The category kTop (compactly generated spaces) being Cartesian closed is not formalized. Mathlib has `CompactlyGeneratedSpace` but not this categorical property.

Proposition 3.1:
included
Part (1) corresponds to the instance that `WeaklyLocallyCompactSpace` + `T2Space` implies `CompactlyGeneratedSpace` in Mathlib/Topology/Compactness/CompactlyGeneratedSpace.lean (line ~348). Part (2) about CW complexes is not in mathlib (CW complexes have only basic definitions).

Theorem 3.2:
non-included
Searched in Mathlib/Topology/CWComplex/. The CW complex structure on products is not formalized. Mathlib has basic CW complex definitions but not this product theorem.

Theorem 3.3 [Milnor]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/CWComplex/. The loop space of a countable CW complex having CW type is not formalized.

Proposition 4.4:
non-included
Searched in Mathlib/Topology/FiberBundle/ and Mathlib/Geometry/Manifold/. The result about homogeneous spaces forming fiber bundles is not formalized. Mathlib has fiber bundles but not this result about Lie groups.

Theorem 4.5 [Ehresmann]:
non-included
Searched in Mathlib/Geometry/Manifold/ and Mathlib/Topology/FiberBundle/. Ehresmann's theorem (proper submersion is fiber bundle) is not formalized.

Proposition 4.7 [Miyazaki]:
non-included
Searched in Mathlib/Topology/CWComplex/ and Mathlib/Topology/Paracompact.lean. Paracompactness of CW complexes is not formalized. Mathlib has `ParacompactSpace` but not this specific result.

Theorem 5.2 [Whitehead's little theorem]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/CWComplex/. Whitehead's theorem (weak equivalence between CW complexes is homotopy equivalence) is not formalized. Mathlib has `ContinuousMap.HomotopyEquiv` but not this theorem.

Theorem 5.3:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/CWComplex/. CW approximation with fibration factorization is not formalized.

Theorem 5.4:
non-included
Searched in Mathlib/Topology/CWComplex/. CW approximation theorem is not formalized.

Proposition 6.1:
non-included
Searched in Mathlib/Topology/Homotopy/. Cofibrations and NDR pairs are not formalized in mathlib.

Theorem 7.1:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/FiberBundle/. The result that fibers of a fibration over a path-connected base are homotopy equivalent is not formalized.

Theorem 7.3:
non-included
Searched in Mathlib/Topology/Homotopy/. The mapping path space construction and its fibration property are not formalized. Mathlib has basic homotopy theory but not Serre fibrations.

Proposition 7.4:
non-included
Searched in Mathlib/Topology/Homotopy/. The factorization of maps into homotopy equivalence followed by Serre fibration is not formalized.

Proposition 8.3:
included
Corresponds to `HomotopyGroup.group` (group structure for n >= 1) and `HomotopyGroup.commGroup` (abelian for n >= 2) in Mathlib/Topology/Homotopy/HomotopyGroup.lean

Theorem 8.4:
included
The long exact sequence of homotopy groups for a fibration is partially formalized. Mathlib has `HomotopyGroup.longExactSeq` type constructions in Mathlib/Topology/Homotopy/HomotopyGroup.lean, though the full generality for Serre fibrations specifically may not be complete.

Lemma 9.7:
non-included
Searched in Mathlib/Topology/Homotopy/. The isomorphism $\pi_n(E, F) \cong \pi_n(B)$ for a Serre fibration is not formalized.

Theorem 10.1:
non-included
Searched in Mathlib/Topology/Homotopy/. This result about retracts and relative homotopy groups is not formalized.

Proposition 10.5:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/CWComplex/. The homotopy lifting/extension property for relative CW complexes and Serre fibrations is not formalized.

Proposition 10.6:
non-included
Searched in Mathlib/Topology/CWComplex/ and Mathlib/Topology/Homotopy/. CW approximation as a left adjoint functor is not formalized.

Theorem 11.1 [Blakers-Massey]:
non-included
Searched in Mathlib/Topology/Homotopy/. The Blakers-Massey excision theorem is not formalized.

Corollary 11.2 [Freudenthal suspension theorem]:
non-included
Searched in Mathlib/Topology/Homotopy/. The Freudenthal suspension theorem is not formalized. Mathlib has no `FreudenthalSuspension` or similar.

Lemma 12.1:
included
Corresponds to `Real.fundamentalGroup_circle_isoZalg` or the equivalent statement that $\pi_1(S^1) \cong \mathbb{Z}$ in Mathlib/Topology/Homotopy/HomotopyGroup.lean and Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean

Theorem 12.2:
non-included
Searched in Mathlib/Topology/Covering/. Mathlib has `IsCoveringMap` and some covering space theory in Mathlib/Topology/Covering/Basic.lean but the full universal cover construction for semi-locally simply connected spaces is not formalized.

Proposition 12.3:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. Postnikov truncation is not formalized.

Proposition 12.5:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. Postnikov towers are not formalized.

Lemma 13.1:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Hurewicz map and its homomorphism property are not formalized.

Theorem 13.2 [Hurewicz theorem]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Hurewicz theorem is not formalized. No `Hurewicz` or `hurewicz` found in mathlib.

Corollary 13.3:
non-included
Searched in Mathlib/Topology/Homotopy/. The converse to Hurewicz (homology vanishing implies connectivity) is not formalized.

Proposition 13.4:
non-included
Searched in Mathlib/Topology/CWComplex/ and Mathlib/AlgebraicTopology/. Moore space construction is not formalized.

Lemma 14.1:
non-included
Searched in Mathlib/AlgebraicTopology/. The representability lemma for Eilenberg-MacLane spaces is not formalized.

Corollary 14.2:
non-included
Searched in Mathlib/AlgebraicTopology/. The functoriality of K(pi,n) is not formalized. Mathlib has no Eilenberg-MacLane space construction.

Theorem 14.3:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/Topology/Homotopy/. The representability of cohomology by Eilenberg-MacLane spaces is not formalized.

Proposition 15.1:
non-included
Searched in Mathlib/Topology/Homotopy/Lifting.lean. This file mentions Hurewicz fibrations in a comment but does not formalize the result that Serre fibrations are Hurewicz over paracompact bases.

Proposition 15.2:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. Obstruction theory is not formalized.

Theorem 15.3:
non-included
Searched in Mathlib/Topology/Homotopy/. Obstruction theory for extending maps over CW skeleta is not formalized.

Corollary 15.4:
non-included
Searched in Mathlib/Topology/Homotopy/. Extension/uniqueness results from obstruction theory are not formalized.

Lemma 16.11:
non-included
Searched in Mathlib/Topology/FiberBundle/ and Mathlib/Topology/VectorBundle/. The existence of metrics on vector bundles is not formalized. Mathlib has `VectorBundle` but not this result.

Corollary 16.12:
non-included
Searched in Mathlib/Topology/VectorBundle/. The splitting of short exact sequences of vector bundles is not formalized.

Theorem 17.2:
non-included
Searched in Mathlib/Topology/VectorBundle/ and Mathlib/Topology/FiberBundle/. I-invariance of Vect (homotopy invariance of vector bundles) is not formalized.

Corollary 17.3:
non-included
Searched in Mathlib/Topology/VectorBundle/. Homotopy invariance of Vect is not formalized.

Theorem 17.6 [Covering space theory]:
non-included
Searched in Mathlib/Topology/Covering/. Mathlib has `IsCoveringMap` and basic properties but not the full equivalence of categories between pi_1-sets and covering spaces.

Theorem 17.9:
non-included
Searched in Mathlib/Topology/FiberBundle/. I-invariance of principal G-bundles is not formalized.

Theorem 18.3 [Illman]:
non-included
Searched in Mathlib/Topology/CWComplex/ and Mathlib/Geometry/Manifold/. Illman's theorem on G-CW structures is not formalized.

Theorem 19.1:
non-included
Searched in Mathlib/Topology/FiberBundle/ and Mathlib/AlgebraicTopology/. The representability theorem for principal bundles (classifying spaces) is not formalized.

Proposition 19.2:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/Topology/FiberBundle/. The equivariant extension theorem for free G-CW complexes is not formalized.

Theorem 19.3 [Peter-Weyl]:
non-included
Searched in Mathlib/RepresentationTheory/ and Mathlib/Topology/Algebra/. The Peter-Weyl theorem is not formalized. No `PeterWeyl` or `peterWeyl` found.

Lemma 19.4:
non-included
Searched in Mathlib/Topology/VectorBundle/. The embedding of vector bundles in trivial bundles over compact Hausdorff spaces is not formalized.

Corollary 19.5:
non-included
Searched in Mathlib/Topology/VectorBundle/. Existence of complements for vector bundles over compact Hausdorff spaces is not formalized.

Lemma 20.4:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/CategoryTheory/. The classifying space functor (nerve + geometric realization) sending natural transformations to homotopies is not fully formalized. Mathlib has nerves but not this homotopy result.

Corollary 20.5:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/CategoryTheory/. The result that adjoint functors induce homotopy equivalent classifying spaces is not formalized.

Corollary 20.6:
non-included
Searched in Mathlib/AlgebraicTopology/. Contractibility of classifying space of category with initial/terminal object is not formalized.

Theorem 20.7:
non-included
Searched in Mathlib/AlgebraicTopology/. The homeomorphism B(C x D) = BC x BD is not formalized.

Proposition 21.3:
non-included
Searched in Mathlib/AlgebraicTopology/. The construction of BG via the translation groupoid is not formalized.

Proposition 21.4:
non-included
Searched in Mathlib/AlgebraicTopology/CechNerve.lean. The Cech nerve construction exists but the homotopy equivalence result for covers with partitions of unity is not formalized.

Theorem 23.1:
non-included
Searched in Mathlib/Algebra/Homology/ and Mathlib/AlgebraicTopology/. Spectral sequences from filtered complexes are not formalized. No `SpectralSequence` found.

Theorem 23.3:
non-included
Searched in Mathlib/Algebra/Homology/. Convergence of spectral sequences is not formalized.

Corollary 23.4:
non-included
Searched in Mathlib/Algebra/Homology/. The comparison theorem for spectral sequences is not formalized.

Theorem 24.1 [Serre spectral sequence]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Serre spectral sequence is not formalized.

Proposition 26.1 [Gysin sequence]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Gysin sequence is not formalized.

Proposition 26.2:
non-included
Searched in Mathlib/AlgebraicTopology/. Edge homomorphisms in spectral sequences are not formalized.

Proposition 26.3:
non-included
Searched in Mathlib/AlgebraicTopology/. Edge homomorphisms are not formalized.

Proposition 26.5:
non-included
Searched in Mathlib/AlgebraicTopology/. The transgression is not formalized.

Proposition 27.1:
non-included
Searched in Mathlib/Topology/Homotopy/. The commutative ladder between homotopy and Serre exact sequences is not formalized.

Lemma 27.2:
non-included
Searched in Mathlib/Topology/Homotopy/. The transgression isomorphism for loop spaces is not formalized.

Theorem 27.3 [Hurewicz, Serre proof]:
non-included
Searched in Mathlib/Topology/Homotopy/. The Hurewicz theorem (even this proof via Serre spectral sequence) is not formalized.

Theorem 27.4 [Relative Hurewicz]:
non-included
Searched in Mathlib/Topology/Homotopy/. The relative Hurewicz theorem is not formalized.

Corollary 27.5:
non-included
Searched in Mathlib/Topology/Homotopy/. The converse to relative Hurewicz is not formalized.

Corollary 27.6 [Whitehead theorem]:
non-included
Searched in Mathlib/Topology/Homotopy/. The Whitehead theorem relating homotopy and homology isomorphisms is not formalized.

Corollary 27.7:
non-included
Searched in Mathlib/Topology/Homotopy/. The result that weak equivalences induce homology isomorphisms (and converse for simply connected spaces) is not formalized.

Theorem 29.1:
non-included
Searched in Mathlib/Algebra/Homology/. Cohomological spectral sequences are not formalized.

Theorem 29.2:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The multiplicative cohomology Serre spectral sequence is not formalized.

Theorem 29.3:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Euler characteristic formula via the Euler class is not formalized. No `EulerClass` found.

Lemma 30.6:
non-included
Searched in Mathlib/CategoryTheory/Abelian/SerreClass/. Mathlib has a `SerreClass` definition in Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean but it is the categorical notion for abelian categories, not Serre's homotopy-theoretic notion of Serre classes of abelian groups.

Proposition 30.7 [Mod C Vietoris-Begle]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The mod C Vietoris-Begle theorem is not formalized.

Proposition 30.8:
non-included
Searched in Mathlib/AlgebraicTopology/. This relative Serre spectral sequence result is not formalized.

Theorem 30.9 [Mod C Hurewicz]:
non-included
Searched in Mathlib/Topology/Homotopy/. The mod C Hurewicz theorem is not formalized.

Corollary 30.10:
non-included
Searched in Mathlib/Topology/Homotopy/. The finite generation and p-torsion corollaries are not formalized.

Theorem 31.1:
non-included
Searched in Mathlib/Topology/Homotopy/. The p-local Hurewicz theorem is not formalized.

Theorem 31.2 [Relative mod C Hurewicz]:
non-included
Searched in Mathlib/Topology/Homotopy/. The relative mod C Hurewicz theorem is not formalized.

Theorem 31.3 [Mod C Whitehead]:
non-included
Searched in Mathlib/Topology/Homotopy/. The mod C Whitehead theorem is not formalized.

Lemma 31.4:
non-included
Searched in Mathlib/Topology/Homotopy/. The link between mod p homology isomorphisms and mod C_p integral homology isomorphisms is not formalized.

Corollary 31.5:
non-included
Searched in Mathlib/Topology/Homotopy/. The p-local homotopy isomorphism from mod p homology isomorphism is not formalized.

Proposition 31.6:
non-included
Searched in Mathlib/Topology/Homotopy/. The finiteness of homotopy groups of spheres (Serre's theorem) is not formalized.

Proposition 32.1:
non-included
Searched in Mathlib/Topology/Homotopy/. The transgression/evaluation map relationship is not formalized.

Proposition 32.2:
non-included
Searched in Mathlib/Topology/Homotopy/. The mod C evaluation map isomorphism for loop spaces is not formalized.

Theorem 32.3 [Mod C Freudenthal]:
non-included
Searched in Mathlib/Topology/Homotopy/. The mod C Freudenthal suspension theorem is not formalized.

Corollary 32.4:
non-included
Searched in Mathlib/Topology/Homotopy/. The Freudenthal suspension theorem for spheres is not formalized.

Proposition 32.5:
non-included
Searched in Mathlib/Topology/Homotopy/. The James construction / map to loops on higher spheres is not formalized.

Theorem 32.6:
non-included
Searched in Mathlib/Topology/Homotopy/. The EHP fiber sequence is not formalized.

Theorem 32.7 [Bousfield]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/CategoryTheory/Localization/. Bousfield localization of spaces is not formalized.

Theorem 32.8:
non-included
Searched in Mathlib/Topology/Homotopy/. The addendum characterizing Bousfield localization is not formalized.

Lemma 32.9:
non-included
Searched in Mathlib/Topology/Homotopy/. The E_*-local Whitehead theorem is not formalized.

Proposition 32.10:
non-included
Searched in Mathlib/Topology/Homotopy/. Rational localization of simply connected spaces is not formalized.

Theorem 33.3 [Chern classes]:
non-included
Searched in Mathlib/Topology/VectorBundle/ and Mathlib/AlgebraicTopology/. Chern classes are not formalized. No `ChernClass` found.

Theorem 33.5 [Leray-Hirsch]:
non-included
Searched in Mathlib/Topology/Homotopy/ and Mathlib/AlgebraicTopology/. The Leray-Hirsch theorem is not formalized.

Theorem 33.6 [Stiefel-Whitney classes]:
non-included
Searched in Mathlib/Topology/VectorBundle/. Stiefel-Whitney classes are not formalized. No `StiefelWhitney` found.

Theorem 34.1:
non-included
Searched in Mathlib/Topology/VectorBundle/ and Mathlib/AlgebraicTopology/. The alternative characterization of Chern classes via Euler classes is not formalized.

Theorem 34.2:
non-included
Searched in Mathlib/AlgebraicTopology/. The computation H*(BU(n)) = Z[c_1,...,c_n] is not formalized.

Theorem 34.3 [Splitting principle]:
non-included
Searched in Mathlib/Topology/VectorBundle/. The splitting principle for complex vector bundles is not formalized.

Theorem 34.4:
non-included
Searched in Mathlib/AlgebraicTopology/. The isomorphism H*(BU(n)) = H*(BT^n)^{Sigma_n} is not formalized.

Lemma 34.6:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/Topology/Homotopy/. The triviality of conjugation on classifying spaces is not formalized.

Proposition 35.2 [Thom isomorphism]:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/Topology/VectorBundle/. The Thom isomorphism theorem is not formalized. No `ThomIsomorphism` found.

Lemma 35.3:
non-included
Searched in Mathlib/AlgebraicTopology/. The relationship between Thom class and Euler class is not formalized.

Proposition 35.4:
non-included
Searched in Mathlib/AlgebraicTopology/. Multiplicativity of the Euler class is not formalized.

Proposition 36.1:
non-included
Searched in Mathlib/AlgebraicTopology/. The computation H*(BO(n); F_2) is not formalized.

Lemma 36.2:
non-included
Searched in Mathlib/Topology/VectorBundle/. The effect of conjugation on Chern classes is not formalized.

Theorem 36.5:
non-included
Searched in Mathlib/AlgebraicTopology/. The computation of H*(BSO(n)) away from 2 is not formalized.

Proposition 37.5:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/Topology/Homotopy/. Steenrod operations are not formalized. No `Steenrod` found.

Proposition 37.6:
non-included
Searched in Mathlib/AlgebraicTopology/. Steenrod squares are not formalized.

Proposition 37.7:
non-included
Searched in Mathlib/AlgebraicTopology/. Stability of Steenrod operations is not formalized.

Corollary 37.8:
non-included
Searched in Mathlib/AlgebraicTopology/. $Sq^0 = id$ is not formalized.

Corollary 37.9:
non-included
Searched in Mathlib/AlgebraicTopology/. Additivity of Steenrod squares is not formalized.

Proposition 37.10 [Adem]:
non-included
Searched in Mathlib/AlgebraicTopology/. The Adem relations and generation of the Steenrod algebra are not formalized.

Corollary 37.11:
non-included
Searched in Mathlib/AlgebraicTopology/. The Hopf invariant one restriction is not formalized.

Theorem 38.2 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. The computation of unoriented cobordism ring is not formalized. No `Cobordism` found.

Theorem 38.3 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. Thom's answer to Steenrod's question on representability is not formalized.

Theorem 38.4 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. The Pontryagin-Thom collapse bijection is not formalized.

Theorem 38.5 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. The isomorphism between cobordism and homotopy of Thom spectra is not formalized.

Lemma 38.6:
non-included
Searched in Mathlib/AlgebraicTopology/. Cobordism invariance of characteristic numbers is not formalized.

Corollary 38.7:
non-included
Searched in Mathlib/AlgebraicTopology/. The Stiefel-Whitney number characterization of cobordism is not formalized.

Theorem 38.8 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. The splitting of MO as a product of Eilenberg-MacLane spectra is not formalized.

Theorem 38.9 [G. Whitehead, Brown]:
non-included
Searched in Mathlib/AlgebraicTopology/. The Brown representability theorem for generalized homology theories is not formalized.

Proposition 39.2:
non-included
Searched in Mathlib/AlgebraicTopology/. The computation of H_*(BO; F_2) is not formalized.

Proposition 39.3 [Hopf-Leray]:
non-included
Searched in Mathlib/RingTheory/HopfAlgebra/ and Mathlib/Algebra/. Mathlib has `HopfAlgebra` definition but not the Hopf-Leray structure theorem for connected Hopf algebras over characteristic zero.

Corollary 39.4 [Hopf]:
non-included
Searched in Mathlib/Topology/Algebra/ and Mathlib/RingTheory/HopfAlgebra/. Hopf's theorem on rational cohomology of Lie groups is not formalized.

Proposition 39.5 [Borel]:
non-included
Searched in Mathlib/RingTheory/HopfAlgebra/. Borel's structure theorem for Hopf algebras in finite characteristic is not formalized.

Proposition 39.6:
non-included
Searched in Mathlib/RingTheory/HopfAlgebra/ and Mathlib/AlgebraicTopology/. The Hopf algebra structure on the Steenrod algebra is not formalized.

Proposition 39.7:
non-included
Searched in Mathlib/AlgebraicTopology/. The Milnor computation of the dual Steenrod algebra is not formalized.

Theorem 39.8:
non-included
Searched in Mathlib/AlgebraicTopology/. Freeness of H*(MO) over the Steenrod algebra is not formalized.

Lemma 39.9 [Lagrange]:
non-included
Searched in Mathlib/RingTheory/HopfAlgebra/. This freeness result for coalgebra modules over Hopf algebras is not formalized.

Proposition 39.10 [Thom]:
non-included
Searched in Mathlib/AlgebraicTopology/. The Wu formula Sq^i(U) = w_i U is not formalized.

Proposition 40.1:
non-included
Searched in Mathlib/AlgebraicTopology/ and Mathlib/Topology/Homotopy/. The rational Hurewicz isomorphism for spectra is not formalized.
