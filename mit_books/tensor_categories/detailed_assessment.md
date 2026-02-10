# Detailed Assessment: Tensor Categories Statements in Mathlib

For each statement, we provide the status (included/non-included) and an explanation of the mathlib evidence.

---

## Chapter 1: Monoidal Categories and Tensor Categories

### 1. Definition 1.1.1 — Monoidal category
**Status:** included
**Explanation:** Formalized as `MonoidalCategory` in `Mathlib/CategoryTheory/Monoidal/Category.lean`. The class includes tensor product (`tensorObj`), associator, unit object, and the pentagon and triangle axioms. This is one of the most fundamental structures in mathlib's category theory library.

### 2. Definition 1.1.2 — Monoidal subcategory
**Status:** included
**Explanation:** Mathlib has `Mathlib/CategoryTheory/Monoidal/Subcategory.lean` which handles monoidal subcategories, including the notion of full monoidal subcategories closed under tensor product and containing the unit.

### 3. Definition 1.1.3 — Opposite monoidal category
**Status:** included
**Explanation:** Formalized in `Mathlib/CategoryTheory/Monoidal/Opposite.lean`. The opposite monoidal category (with reversed tensor product order) is defined and its properties established.

### 4. Proposition 1.2.2 — Unit constraint diagrams commute
**Status:** included
**Explanation:** These are part of the axioms/basic lemmas in `Mathlib/CategoryTheory/Monoidal/Category.lean`. The triangle axiom and its consequences are built into the `MonoidalCategory` class and derived in `CoherenceLemmas.lean`.

### 5. Proposition 1.2.3 — Unit naturality identities
**Status:** included
**Explanation:** These identities (l_{1 tensor X} = Id tensor l_X, etc.) are among the coherence lemmas in `Mathlib/CategoryTheory/Monoidal/CoherenceLemmas.lean`.

### 6. Proposition 1.2.4 — Uniqueness of unit object
**Status:** included
**Explanation:** The unit object is part of the `MonoidalCategory` structure. Its uniqueness up to unique isomorphism follows from the general theory. This is implicit in the formalization where the unit is a chosen component of the structure.

### 7. Proposition 1.2.7 — End(1) is commutative
**Status:** non-included
**Explanation:** While mathlib has extensive monoidal category theory, the specific result that the endomorphism monoid of the unit object is commutative does not appear to be explicitly stated as a theorem. The Eckmann-Hilton argument that would prove this is not formalized in this context.

### 8. Definition 1.2.6 — Monoidal category (with l, r)
**Status:** included
**Explanation:** This is the same as Definition 1.1.1 with explicit left and right unitors, which is exactly how `MonoidalCategory` is defined in mathlib, with `leftUnitor` and `rightUnitor` as part of `MonoidalCategoryStruct`.

### 9. Definition 1.4.1 — Monoidal functor
**Status:** included
**Explanation:** Formalized as `Functor.Monoidal` (and the weaker `Functor.LaxMonoidal`) in `Mathlib/CategoryTheory/Monoidal/Functor.lean`. Includes the monoidal structure isomorphism J and its compatibility axioms.

### 10. Proposition 1.4.3 — Monoidal functor unit constraints
**Status:** included
**Explanation:** The unit compatibility for monoidal functors is part of the `Functor.LaxMonoidal` and `Functor.Monoidal` definitions and lemmas in `Mathlib/CategoryTheory/Monoidal/Functor.lean`.

### 11. Definition 1.4.5 — Monoidal functor (complete definition)
**Status:** included
**Explanation:** Same as entry 9 above. The complete definition with (F, J, phi) is captured by `Functor.Monoidal` in mathlib.

### 12. Definition 1.5.1 — Morphism of monoidal functors
**Status:** included
**Explanation:** Formalized in `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean`. Monoidal natural transformations between monoidal functors are defined.

### 13. Proposition 1.6.4 — A-bimod equivalent to End_re(C)
**Status:** non-included
**Explanation:** While mathlib has bimodules (`Mathlib/CategoryTheory/Monoidal/Bimod.lean`) and endofunctor categories (`Mathlib/CategoryTheory/Monoidal/End.lean`), the specific equivalence between the monoidal category of A-bimodules and the category of right exact endofunctors of A-mod is not formalized.

### 14. Proposition 1.7.1 — Classification of monoidal functors on C_G^omega
**Status:** non-included
**Explanation:** The classification of monoidal functors between categories Vec_G^omega in terms of group cohomology is specialized tensor category theory not present in mathlib.

### 15. Theorem 1.8.5 — MacLane's Strictness Theorem
**Status:** non-included
**Explanation:** The theorem that every monoidal category is monoidally equivalent to a strict one is not directly formalized in mathlib. Mathlib has `Skeleton` for monoidal categories in `Mathlib/CategoryTheory/Monoidal/Skeleton.lean`, which shows that the skeleton of a monoidal category has a monoid structure, but the full strictification theorem is not present.

### 16. Theorem 1.9.1 — MacLane's Coherence Theorem
**Status:** included
**Explanation:** Formalized in `Mathlib/CategoryTheory/Monoidal/Free/Coherence.lean`. The coherence theorem is proved: any two parallel morphisms in the free monoidal category built from associators and unitors are equal. The file header explicitly states "the monoidal coherence theorem."

### 17. Definition 1.10.1 — Right dual
**Status:** included
**Explanation:** Formalized as `HasRightDual` and `ExactPairing` in `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`. The evaluation and coevaluation morphisms with the zig-zag identities are part of `ExactPairing`.

### 18. Definition 1.10.2 — Left dual
**Status:** included
**Explanation:** Formalized as `HasLeftDual` in `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`, dual to `HasRightDual`.

### 19. Proposition 1.10.4 — Uniqueness of duals
**Status:** included
**Explanation:** In mathlib, uniqueness is reflected by the fact that `HasRightDual X` provides a canonical choice, and the isomorphism `leftDual_rightDual` and `rightDual_leftDual` establish the canonical identifications. The result follows from adjunction/representability.

### 20. Proposition 1.10.7 — Dualization functor properties, (XY)* = Y*X*
**Status:** included
**Explanation:** The contravariant functor structure and the formula (X tensor Y)* = Y* tensor X* are established in `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`. The `rightAdjointMate` and related constructions formalize the functoriality of dualization.

### 21. Proposition 1.10.9 — Adjunction isomorphisms from duals
**Status:** included
**Explanation:** The adjunction Hom(U tensor V, W) = Hom(U, W tensor V*) is formalized in `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean` through the `tensorLeftHomEquiv` and related isomorphisms. Also see `closedOfHasLeftDual`.

### 22. Definition 1.10.11 — Rigid monoidal category
**Status:** included
**Explanation:** Formalized as `RigidCategory` in `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`, requiring both `RightRigidCategory` and `LeftRigidCategory`.

### 23. Definition 1.11.1 — Invertible object
**Status:** non-included
**Explanation:** While mathlib has the general notion of isomorphisms in categories, the specific notion of an invertible object in a monoidal category (where both ev and coev are isomorphisms) is not formalized as a dedicated definition. There is no `InvertibleObject` class in the monoidal category library.

### 24. Proposition 1.11.3 — Properties of invertible objects
**Status:** non-included
**Explanation:** Not formalized, as the definition of invertible objects is not present.

### 25. Definition 1.12.1 — Locally finite abelian category
**Status:** non-included
**Explanation:** Mathlib does not have the notion of "locally finite" k-linear abelian categories as used in tensor category theory. While it has `Abelian` categories and finite-dimensional Hom spaces in specific contexts, the abstract definition is not present.

### 26. Proposition 1.12.2 — Schur's lemma
**Status:** included
**Explanation:** Schur's lemma is formalized in `Mathlib/CategoryTheory/Preadditive/Schur.lean`. The results that morphisms between non-isomorphic simple objects are zero, and that endomorphisms of simple objects form a division ring (which is k when k is algebraically closed), are established.

### 27. Definition 1.12.3 — Multitensor / tensor category
**Status:** non-included
**Explanation:** The abstract definitions of multitensor category and tensor category (as locally finite k-linear abelian rigid monoidal categories with bilinear tensor product) are not in mathlib. Mathlib works with monoidal categories, rigid categories, etc., but does not bundle them into the specific "tensor category" package of Etingof et al.

### 28. Proposition 1.13.1 — Biexactness of tensor in multitensor categories
**Status:** non-included
**Explanation:** The specific result that the tensor product in a multitensor category is biexact is not formalized. Mathlib does not have the multitensor category framework.

### 29. Definition 1.13.3 — Multiring / ring category
**Status:** non-included
**Explanation:** Not in mathlib. This is specific to the Etingof et al. framework.

### 30. Corollary 1.13.4 — Im(f1 tensor f2) = Im(f1) tensor Im(f2)
**Status:** non-included
**Explanation:** Not formalized. Requires the multiring category framework.

### 31. Proposition 1.13.5 — Dualization functor is exact
**Status:** non-included
**Explanation:** The exactness of the dualization functor in a multiring category is not formalized. While mathlib has dualization in rigid categories, the exactness result in the specific categorical setting is not present.

### 32. Proposition 1.13.6 — P tensor X projective when X has dual
**Status:** non-included
**Explanation:** Not formalized in the categorical generality of the book. This requires the multiring category framework.

### 33. Corollary 1.13.7 — 1 projective iff semisimple
**Status:** non-included
**Explanation:** Not in mathlib. This is a result specific to multiring categories with duals.

### 34. Definition 1.14.1 — Quasi-tensor / tensor functor
**Status:** non-included
**Explanation:** The notion of a quasi-tensor functor (exact faithful with J not necessarily monoidal) is not in mathlib. Mathlib has monoidal functors but not this weaker notion.

### 35. Theorem 1.15.1 — End(1) is semisimple
**Status:** non-included
**Explanation:** The result that End(1) is semisimple in any multiring category is not formalized. This is specific tensor category theory.

### 36. Proposition 1.15.5 — Decomposition C = sum C_ij
**Status:** non-included
**Explanation:** The decomposition of a multiring category into component subcategories C_ij is not in mathlib.

### 37. Theorem 1.15.8 — Unit is simple in ring categories with duals
**Status:** non-included
**Explanation:** Not formalized. This fundamental result of tensor category theory is not present in mathlib.

### 38. Lemma 1.16.1 — Associativity of Grothendieck ring
**Status:** non-included
**Explanation:** While mathlib has Grothendieck groups in various contexts, the specific Grothendieck ring of a multiring category with its multiplicative structure is not formalized.

### 39. Proposition 1.16.2 — Quasi-tensor functor induces ring homomorphism
**Status:** non-included
**Explanation:** Not in mathlib.

### 40. Definition 1.18.1 — Finite abelian category
**Status:** non-included
**Explanation:** The abstract definition of a finite abelian category (equivalent to A-mod for finite dimensional A) is not formalized as a standalone concept in mathlib.

### 41. Definition 1.18.2 — Finite category equivalent characterization
**Status:** non-included
**Explanation:** Not in mathlib as a categorical definition.

### 42. Proposition 1.18.3 — End tensor product formula
**Status:** non-included
**Explanation:** The isomorphism End(F1) tensor End(F2) = End(F1 tensor F2) for exact functors on finite abelian categories is not formalized.

### 43. Definition 1.19.1 — Quasi-fiber / fiber functor
**Status:** non-included
**Explanation:** Not formalized in mathlib in the sense of tensor category theory. While mathlib has the forgetful functor (`forget`) from representation categories, the abstract notion of fiber functor is not defined.

### 44. Definition 1.20.1 — Coalgebra
**Status:** included
**Explanation:** Coalgebras are defined in mathlib. See `Mathlib/RingTheory/Coalgebra/` and the categorical version via comonoid objects in `Mathlib/CategoryTheory/Monoidal/Comon_.lean`.

### 45. Definition 1.20.2 — Comodule
**Status:** included
**Explanation:** Comodules are defined in mathlib, both algebraically and categorically. See `Mathlib/RingTheory/Coalgebra/` for algebraic comodules.

### 46. Theorem 1.21.1 — End(F) is a bialgebra
**Status:** non-included
**Explanation:** The reconstruction theorem showing that End(F) for a fiber functor F is a bialgebra is not formalized. This is Tannaka-type reconstruction theory. While mathlib has `Mathlib/RepresentationTheory/Tannaka.lean`, that file covers a different (group-theoretic) version of Tannaka duality.

### 47. Definition 1.21.2 — Bialgebra
**Status:** included
**Explanation:** Bialgebras are defined in `Mathlib/RingTheory/Bialgebra/Basic.lean`. The categorical version (bimonoid objects) is in `Mathlib/CategoryTheory/Monoidal/Bimon_.lean`.

### 48. Theorem 1.21.3 — Reconstruction for bialgebras
**Status:** non-included
**Explanation:** The full Tannaka-type reconstruction theorem for bialgebras (bijection between finite tensor categories with fiber functors and bialgebras) is not in mathlib.

### 49. Proposition 1.22.1 — Antipode axiom
**Status:** included
**Explanation:** The antipode axioms mu(S tensor Id) Delta = i epsilon are formalized in `Mathlib/RingTheory/HopfAlgebra/Basic.lean` as `mul_antipode_rTensor_comul` and `mul_antipode_lTensor_comul`. Also categorically in `Mathlib/CategoryTheory/Monoidal/Hopf_.lean`.

### 50. Definition 1.22.2 — Antipode
**Status:** included
**Explanation:** The antipode is defined as part of `HopfAlgebra` in `Mathlib/RingTheory/HopfAlgebra/Basic.lean` and categorically as part of `HopfObj` in `Mathlib/CategoryTheory/Monoidal/Hopf_.lean`.

### 51. Proposition 1.22.4 — Uniqueness of antipode
**Status:** included
**Explanation:** The uniqueness of the antipode follows from the fact that the antipode axioms uniquely determine the map. This is reflected in mathlib's definition where the antipode is a single determined map, and the structure theorem approach ensures uniqueness.

### 52. Proposition 1.22.5 — Antipode is antihomomorphism
**Status:** included
**Explanation:** The results `antipode_one`, `antipode_mul` (showing S(ab) = S(b)S(a)), and the coalgebra antihomomorphism properties are proved in `Mathlib/RingTheory/HopfAlgebra/Basic.lean`.

### 53. Corollary 1.22.6 — Rep(H) has duals when H has antipode
**Status:** non-included
**Explanation:** The specific result that the representation category of a bialgebra with antipode has right duals is not formalized categorically. While the algebraic dual construction is standard, the categorical statement is not in mathlib.

### 54. Definition 1.22.9 — Hopf algebra
**Status:** included
**Explanation:** Formalized as `HopfAlgebra` in `Mathlib/RingTheory/HopfAlgebra/Basic.lean`. Also categorically as `HopfObj` in `Mathlib/CategoryTheory/Monoidal/Hopf_.lean`.

### 55. Theorem 1.22.11 — Reconstruction for Hopf algebras
**Status:** non-included
**Explanation:** The full reconstruction theorem (bijection between rigid tensor categories with fiber functor and Hopf algebras) is not in mathlib.

### 56. Proposition 1.22.15 — Finite dim antipode is invertible
**Status:** non-included
**Explanation:** The result that a finite-dimensional bialgebra with antipode has invertible antipode (hence is a Hopf algebra) is not in mathlib. Mathlib defines Hopf algebras to have an antipode but does not prove this finite-dimensional result.

### 57. Theorem 1.23.1 — General reconstruction via coend
**Status:** non-included
**Explanation:** The general reconstruction theorem using coends is not formalized. While mathlib has `Mathlib/RepresentationTheory/Tannaka.lean`, it handles a simpler group-theoretic case, not the general coalgebra reconstruction.

### 58. Theorem 1.23.2 — Categories with functor biject with coalgebras
**Status:** non-included
**Explanation:** Not in mathlib. This is advanced reconstruction theory.

### 59. Definition 1.24.2 — Primitive element
**Status:** included
**Explanation:** Primitive elements in coalgebras/bialgebras are defined in mathlib. The concept appears in the context of Hopf algebras and Lie algebras.

### 60. Definition 1.24.6 — Skew-primitive element
**Status:** non-included
**Explanation:** Skew-primitive elements are not explicitly defined in mathlib.

### 61. Definition 1.25.1 — Quantum group U_q(sl_2)
**Status:** non-included
**Explanation:** Quantum groups are not defined in mathlib. There is no formalization of U_q(sl_2) or U_q(g).

### 62. Theorem 1.25.2 — Hopf structure on U_q(sl_2)
**Status:** non-included
**Explanation:** Not in mathlib; quantum groups are not formalized.

### 63. Definition 1.26.2 — Quantum group U_q(g)
**Status:** non-included
**Explanation:** Not in mathlib.

### 64. Theorem 1.26.3 — Hopf structure on U_q(g)
**Status:** non-included
**Explanation:** Not in mathlib.

### 65. Proposition 1.27.1 — Prim_{h,g}/k(h-g) = Ext^1(g,h)
**Status:** non-included
**Explanation:** This relationship between skew-primitive elements and Ext groups is not formalized.

### 66. Theorem 1.27.4 — Ext^1(1,1) = 0 in characteristic 0
**Status:** non-included
**Explanation:** This result about vanishing of self-extensions of the unit in characteristic 0 finite ring categories is not in mathlib.

### 67. Corollary 1.27.8 — Commutative Hopf = Fun(G,k) in char 0
**Status:** non-included
**Explanation:** The classification of commutative Hopf algebras over algebraically closed fields of characteristic 0 is not in mathlib. This follows from the Cartier-Kostant theorem.

### 68. Definition 1.28.1 — Pointed coalgebra
**Status:** non-included
**Explanation:** Not defined in mathlib in this generality.

### 69. Definition 1.28.3 — Pointed tensor category
**Status:** non-included
**Explanation:** Not in mathlib.

### 70. Definition 1.29.1 — Coradical filtration
**Status:** non-included
**Explanation:** The coradical filtration of coalgebras is not formalized in mathlib.

### 71. Proposition 1.29.4 — Cosemisimple iff C_0 = C_1
**Status:** non-included
**Explanation:** Not in mathlib; requires coradical filtration.

### 72. Proposition 1.29.6 — Injective on C_1 implies injective
**Status:** non-included
**Explanation:** Not in mathlib.

### 73. Theorem 1.30.1 — Chevalley's theorem
**Status:** non-included
**Explanation:** The result that tensor products of simple representations are semisimple in characteristic 0 is not explicitly in mathlib, though Maschke's theorem (for finite groups in char 0) is in `Mathlib/RepresentationTheory/Maschke.lean`. Chevalley's theorem is more general (applies to all groups and Lie algebras).

### 74. Lemma 1.30.2 — Completely reducible rep implies reductive
**Status:** non-included
**Explanation:** Not formalized in this generality in mathlib.

### 75. Definition 1.31.1 — Chevalley property
**Status:** non-included
**Explanation:** Not in mathlib.

### 76. Proposition 1.31.2 — Pointed => Chevalley
**Status:** non-included
**Explanation:** Not in mathlib.

### 77. Proposition 1.31.3 — Chevalley property and coradical filtration
**Status:** non-included
**Explanation:** Not in mathlib.

### 78. Corollary 1.31.5 — Pointed Hopf: coradical is Hopf filtration
**Status:** non-included
**Explanation:** Not in mathlib.

### 79. Proposition 1.32.3 — Pointed Hopf generated by grouplikes/skew-primitives
**Status:** non-included
**Explanation:** Not in mathlib.

### 80. Theorem 1.33.1 — Cartier-Kostant theorem
**Status:** non-included
**Explanation:** The Cartier-Kostant theorem (cocommutative Hopf algebras over algebraically closed fields of char 0 are semidirect products k[G] semidirect U(g)) is not in mathlib. This is a deep result in Hopf algebra theory.

### 81. Lemma 1.33.2 — Symmetric cocycles in SV
**Status:** non-included
**Explanation:** Not in mathlib.

### 82. Definition 1.34.1 — Normalized quasi-fiber functor
**Status:** non-included
**Explanation:** Not in mathlib; quasi-bialgebra theory is not formalized.

### 83. Proposition 1.34.4 — Quasi-bialgebra identities
**Status:** non-included
**Explanation:** Not in mathlib.

### 84. Definition 1.34.5 — Quasi-bialgebra
**Status:** non-included
**Explanation:** Quasi-bialgebras (with nontrivial associator Phi) are not defined in mathlib. The search confirms no results for "quasi-Hopf" or "quasiHopf" in mathlib.

### 85. Definition 1.34.6 — Twist for quasi-bialgebra
**Status:** non-included
**Explanation:** Not in mathlib.

### 86. Proposition 1.34.7 — Quasi-fiber functor unique up to twist
**Status:** non-included
**Explanation:** Not in mathlib.

### 87. Theorem 1.34.8 — Reconstruction for quasi-bialgebras
**Status:** non-included
**Explanation:** Not in mathlib.

### 88. Definition 1.35.2 — Antipode on quasi-bialgebra
**Status:** non-included
**Explanation:** Not in mathlib.

### 89. Theorem 1.35.6 — Reconstruction for quasi-Hopf algebras
**Status:** non-included
**Explanation:** Not in mathlib.

### 90. Definition 1.36.1 — Bialgebra twist
**Status:** non-included
**Explanation:** Not in mathlib.

### 91. Proposition 1.36.4 — Twists biject with fiber functors
**Status:** non-included
**Explanation:** Not in mathlib.

### 92. Proposition 1.36.5 — Fiber functors on Vec_G biject with H^2
**Status:** non-included
**Explanation:** Not in mathlib.

### 93. Proposition 1.37.1 — Quantum trace properties
**Status:** non-included
**Explanation:** Quantum traces are not defined in mathlib. While `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean` mentions some trace-related constructions, the full quantum trace theory is absent.

### 94. Proposition 1.37.3 — Quantum trace additivity
**Status:** non-included
**Explanation:** Not in mathlib.

### 95. Definition 1.38.1 — Pivotal structure
**Status:** non-included
**Explanation:** Pivotal categories are not defined in mathlib. There is no `PivotalCategory` class.

### 96. Definition 1.38.4 — Pivotal dimension
**Status:** non-included
**Explanation:** Not in mathlib.

### 97. Proposition 1.38.5 — dim_a is character of Grothendieck ring
**Status:** non-included
**Explanation:** Not in mathlib; requires pivotal categories and Grothendieck rings of tensor categories.

### 98. Corollary 1.38.6 — Dimensions are algebraic integers
**Status:** non-included
**Explanation:** Not in mathlib.

### 99. Definition 1.39.1 — Spherical structure
**Status:** non-included
**Explanation:** Spherical categories are not defined in mathlib. The search found no matches for "spherical" in the monoidal category library.

### 100. Theorem 1.39.2 — Left = right trace in spherical categories
**Status:** non-included
**Explanation:** Not in mathlib.

### 101. Proposition 1.41.1 — *V = V* in semisimple multitensor
**Status:** non-included
**Explanation:** The result that left and right duals coincide in semisimple multitensor categories is not in mathlib. Mathlib has both `HasLeftDual` and `HasRightDual` but does not prove their equivalence under semisimplicity.

### 102. Proposition 1.41.5 — Tr(a) != 0 for simple V
**Status:** non-included
**Explanation:** Not in mathlib.

### 103. Definition 1.42.1 — Z_+-ring
**Status:** non-included
**Explanation:** Z_+-rings (rings with a basis with nonnegative structure constants) are not defined in mathlib.

### 104. Definition 1.42.2 — Based ring, fusion ring
**Status:** non-included
**Explanation:** Based rings and fusion rings are not defined in mathlib.

### 105. Proposition 1.42.4 — Gr(C) is based/fusion ring
**Status:** non-included
**Explanation:** Not in mathlib.

### 106. Proposition 1.42.9 — Categorifications of Z[G]
**Status:** non-included
**Explanation:** Not in mathlib.

### 107. Proposition 1.43.2 — *-algebra is semisimple
**Status:** non-included
**Explanation:** While mathlib has semisimplicity of algebras, the specific result about *-algebras (C*-algebras with positive definite trace) being semisimple is not in this form.

### 108. Proposition 1.43.4 — Based ring tensor C is *-algebra
**Status:** non-included
**Explanation:** Not in mathlib.

### 109. Corollary 1.43.5 — Multifusion ring tensor C is semisimple
**Status:** non-included
**Explanation:** Not in mathlib.

### 110. Theorem 1.44.1 — Frobenius-Perron theorem
**Status:** non-included
**Explanation:** The Frobenius-Perron theorem for nonneg matrices (existence of dominant nonneg eigenvalue) is NOT formalized in mathlib. The search found references to "Perron" only in unrelated contexts (box integrals, irreducible matrices defs). The classical Perron-Frobenius theorem is missing.

### 111. Proposition 1.45.2 — Gr(C) is transitive Z_+-ring
**Status:** non-included
**Explanation:** Not in mathlib.

### 112. Definition 1.45.3 — Frobenius-Perron dimension
**Status:** non-included
**Explanation:** FPdim is not defined in mathlib. This is a concept from the theory of fusion categories.

### 113. Proposition 1.45.4 — FPdim properties
**Status:** non-included
**Explanation:** Not in mathlib.

### 114. Proposition 1.45.5 — FPdim is ring homomorphism
**Status:** non-included
**Explanation:** Not in mathlib.

### 115. Proposition 1.45.8 — FPdim invariant under *
**Status:** non-included
**Explanation:** Not in mathlib.

### 116. Corollary 1.45.9 — FPdim = 1 implies invertible
**Status:** non-included
**Explanation:** Not in mathlib.

### 117. Proposition 1.45.10 — Homomorphisms preserve FPdim
**Status:** non-included
**Explanation:** Not in mathlib.

### 118. Corollary 1.45.11 — Quasi-tensor functors preserve FPdim
**Status:** non-included
**Explanation:** Not in mathlib.

### 119. Proposition 1.45.15 — Kronecker's result
**Status:** non-included
**Explanation:** This result about eigenvalues of nonneg integer matrices less than 2 being 2cos(pi/n) is not in mathlib.

### 120. Corollary 1.45.16 — FPdim < 2 implies 2cos(pi/n)
**Status:** non-included
**Explanation:** Not in mathlib.

### 121. Definition 1.46.1 — Deligne tensor product
**Status:** non-included
**Explanation:** Deligne's tensor product of abelian categories is not defined in mathlib. The search found no results for "Deligne tensor" or "boxtimes" in the relevant files.

### 122. Proposition 1.46.2 — Deligne tensor product exists
**Status:** non-included
**Explanation:** Not in mathlib.

### 123. Proposition 1.46.3 — Deligne product of multitensor is multitensor
**Status:** non-included
**Explanation:** Not in mathlib.

### 124. Proposition 1.47.1 — K_0 is Gr-bimodule
**Status:** non-included
**Explanation:** Not in mathlib.

### 125. Proposition 1.47.2 — Tensor with projective covers formula
**Status:** non-included
**Explanation:** Not in mathlib.

### 126. Proposition 1.47.3 — Dual of projective is projective
**Status:** non-included
**Explanation:** Not in mathlib in the categorical generality.

### 127. Definition 1.47.4 — Regular object
**Status:** non-included
**Explanation:** Not in mathlib.

### 128. Definition 1.47.5 — FPdim of category
**Status:** non-included
**Explanation:** Not in mathlib.

### 129. Proposition 1.47.7 — Regular object absorbs tensor
**Status:** non-included
**Explanation:** Not in mathlib.

### 130. Definition 1.48.1 — Integral tensor category
**Status:** non-included
**Explanation:** Not in mathlib.

### 131. Proposition 1.48.2 — Integral iff Rep of quasi-Hopf
**Status:** non-included
**Explanation:** Not in mathlib.

### 132. Corollary 1.48.3 — Integral categories biject with quasi-Hopf algebras
**Status:** non-included
**Explanation:** Not in mathlib.

### 133. Definition 1.49.1 — Surjective functor
**Status:** non-included
**Explanation:** Not in mathlib in this categorical sense.

### 134. Theorem 1.49.3 — Surjective quasi-tensor preserves projectives
**Status:** non-included
**Explanation:** Not in mathlib.

### 135. Theorem 1.50.1 — F(R_C) = ratio * R_D
**Status:** non-included
**Explanation:** Not in mathlib.

### 136. Corollary 1.50.2 — FPdim divisibility
**Status:** non-included
**Explanation:** Not in mathlib.

### 137. Corollary 1.50.3 — Categorical freeness
**Status:** non-included
**Explanation:** Not in mathlib. The Nichols-Zoeller theorem is also not formalized.

### 138. Corollary 1.50.4 — Quasi-Hopf free over subalgebra
**Status:** non-included
**Explanation:** Not in mathlib.

### 139. Lemma 1.51.1 — L_rho is invertible
**Status:** non-included
**Explanation:** The distinguished invertible object is not defined in mathlib.

### 140. Lemma 1.51.2 — P_{D(i)} = P_i tensor L_rho
**Status:** non-included
**Explanation:** Not in mathlib.

### 141. Corollary 1.51.3 — Double dual of projectives
**Status:** non-included
**Explanation:** Not in mathlib.

### 142. Definition 1.51.4 — Distinguished invertible object
**Status:** non-included
**Explanation:** Not in mathlib.

### 143. Corollary 1.51.5 — Quasi-Hopf is Frobenius
**Status:** non-included
**Explanation:** Not in mathlib. While mathlib has Frobenius algebras in the context of field extensions, the result that quasi-Hopf algebras are Frobenius is not formalized.

### 144. Definition 1.52.1 — Left/right integral
**Status:** non-included
**Explanation:** Integrals in Hopf algebras are not defined in mathlib.

### 145. Proposition 1.52.3 — Existence/uniqueness of integrals
**Status:** non-included
**Explanation:** Not in mathlib.

### 146. Proposition 1.52.4 — L_rho = distinguished character
**Status:** non-included
**Explanation:** Not in mathlib.

### 147. Proposition 1.52.5 — Semisimplicity criteria via integrals
**Status:** non-included
**Explanation:** Not in mathlib.

### 148. Definition 1.52.6 — Unimodular category
**Status:** non-included
**Explanation:** Not in mathlib.

### 149. Theorem 1.53.1 — Cartan matrix degeneracy
**Status:** non-included
**Explanation:** Not in mathlib.

---

## Chapter 2: Module Categories

### 150. Definition 2.1.1 — Module category
**Status:** non-included
**Explanation:** Module categories over monoidal categories are not defined in mathlib. While mathlib has `Action` categories (`Mathlib/CategoryTheory/Monoidal/Action/`) which represent objects with a group action, the general notion of module category over a monoidal category is absent.

### 151. Definition 2.1.2 — Module category with unit constraint
**Status:** non-included
**Explanation:** Not in mathlib.

### 152. Proposition 2.1.3 — Module structures biject with monoidal functors to End
**Status:** non-included
**Explanation:** Not in mathlib. While `Mathlib/CategoryTheory/Monoidal/End.lean` defines the endofunctor monoidal category, the bijection with module category structures is not established.

### 153. Definition 2.1.6 — Module subcategory
**Status:** non-included
**Explanation:** Not in mathlib.

### 154. Definition 2.2.1 — Module functor
**Status:** non-included
**Explanation:** Not in mathlib.

### 155. Definition 2.3.1 — Abelian module category
**Status:** non-included
**Explanation:** Not in mathlib.

### 156. Proposition 2.4.1 — Direct sum of module categories
**Status:** non-included
**Explanation:** Not in mathlib.

### 157. Definition 2.4.3 — Indecomposable module category
**Status:** non-included
**Explanation:** Not in mathlib.

### 158. Definition 2.5.4 — Bimodule category
**Status:** non-included
**Explanation:** Not in mathlib.

### 159. Definition 2.6.1 — Exact module category
**Status:** non-included
**Explanation:** Not in mathlib.

### 160. Lemma 2.7.1 — Exact module category has enough projectives
**Status:** non-included
**Explanation:** Not in mathlib.

### 161. Corollary 2.7.2 — Exact + finitely many simples => finite
**Status:** non-included
**Explanation:** Not in mathlib.

### 162. Lemma 2.7.3 — P tensor X injective
**Status:** non-included
**Explanation:** Not in mathlib.

### 163. Corollary 2.7.4 — Projective = injective in exact module
**Status:** non-included
**Explanation:** Not in mathlib.

### 164. Lemma 2.7.6 — Equivalence relation on simples
**Status:** non-included
**Explanation:** Not in mathlib.

### 165. Proposition 2.7.7 — Decomposition of exact module category
**Status:** non-included
**Explanation:** Not in mathlib.

### 166. Proposition 2.7.8 — Module functors from exact are exact
**Status:** non-included
**Explanation:** Not in mathlib.

### 167. Definition 2.8.1 — Z_+-module
**Status:** non-included
**Explanation:** Not in mathlib.

### 168. Definition 2.8.3 — Irreducible Z_+-module
**Status:** non-included
**Explanation:** Not in mathlib.

### 169. Lemma 2.8.5 — Gr(M) irreducible for indecomposable exact M
**Status:** non-included
**Explanation:** Not in mathlib.

### 170. Proposition 2.8.7 — Finitely many irreducible Z_+-modules
**Status:** non-included
**Explanation:** Not in mathlib.

### 171. Definition 2.9.1 — Algebra in a category
**Status:** included
**Explanation:** Formalized as `MonObj` (monoid object, which when the monoidal category is preadditive is an algebra object) in `Mathlib/CategoryTheory/Monoidal/Mon_.lean`. The structure includes unit and multiplication morphisms with associativity and unit axioms.

### 172. Definition 2.9.5 — Module over algebra in category
**Status:** included
**Explanation:** Formalized as `ModObj` in `Mathlib/CategoryTheory/Monoidal/Mod_.lean`. A module over a monoid object in a monoidal category.

### 173. Definition 2.9.6 — Homomorphisms of modules
**Status:** included
**Explanation:** Module morphisms are defined in `Mathlib/CategoryTheory/Monoidal/Mod_.lean` as morphisms compatible with the module action.

### 174. Proposition 2.9.10 — Mod_C(A) is module category
**Status:** non-included
**Explanation:** While mathlib has `Mod_C(A)` as a category, the result that it forms a module category over C (in the sense of Definition 2.1.1) requires the module category framework which is absent.

### 175. Lemma 2.9.12 — Hom_A(X tensor A, M) = Hom(X, M)
**Status:** non-included
**Explanation:** Not explicitly in mathlib, though related adjunction results exist.

### 176. Definition 2.9.18 — Morita equivalence in categories
**Status:** non-included
**Explanation:** Morita equivalence for algebras in monoidal categories is not in mathlib. Classical Morita equivalence of rings is present elsewhere.

### 177. Definition 2.9.21 — Exact algebra
**Status:** non-included
**Explanation:** Not in mathlib.

### 178. Definition 2.9.22 — Tensor product over algebra
**Status:** non-included
**Explanation:** While mathlib has tensor products over algebras in the classical sense, the categorical version (tensor product over an algebra object in a monoidal category) is not fully formalized in this generality.

### 179. Definition 2.9.24 — Bimodule in category
**Status:** included
**Explanation:** Formalized as `Bimod` in `Mathlib/CategoryTheory/Monoidal/Bimod.lean`. Bimodule objects for pairs of monoid objects in a monoidal category are defined with left and right actions and compatibility.

### 180. Definition 2.10.2 — Internal Hom
**Status:** non-included
**Explanation:** While mathlib has internal Hom in closed monoidal categories (`Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`), the internal Hom for module categories (representing Hom(. tensor M1, M2)) is not formalized.

### 181. Lemma 2.10.4 — Internal Hom adjunction isomorphisms
**Status:** non-included
**Explanation:** Not in the module category context. Some related adjunctions exist for closed monoidal categories.

### 182. Corollary 2.10.6 — Internal Hom exact for exact module categories
**Status:** non-included
**Explanation:** Not in mathlib.

### 183. Proposition 2.10.7 — Characterization of exactness via internal Hom
**Status:** non-included
**Explanation:** Not in mathlib.

### 184. Theorem 2.11.2 — Main reconstruction for module categories
**Status:** non-included
**Explanation:** Not in mathlib. This is a categorical version of the Barr-Beck theorem.

### 185. Theorem 2.11.6 — Every finite module category = Mod_C(A)
**Status:** non-included
**Explanation:** Not in mathlib.

### 186. Proposition 2.12.2 — Fun_C(M1,M2) = A-B-bimodules
**Status:** non-included
**Explanation:** Not in mathlib.

### 187. Corollary 2.12.3 — Fun_C is abelian
**Status:** non-included
**Explanation:** Not in mathlib.

### 188. Lemma 2.13.2 — Composition of module functors is biexact
**Status:** non-included
**Explanation:** Not in mathlib.

### 189. Lemma 2.13.3 — Module functors have adjoints
**Status:** non-included
**Explanation:** Not in mathlib.

### 190. Corollary 2.13.4 — Module functors preserve projectives
**Status:** non-included
**Explanation:** Not in mathlib.

### 191. Proposition 2.13.5 — Fun_C(M1,M2) is finite
**Status:** non-included
**Explanation:** Not in mathlib.

### 192. Definition 2.14.1 — Dual category C*_M
**Status:** non-included
**Explanation:** The dual category construction is not in mathlib.

### 193. Lemma 2.14.3 — Unit in dual category
**Status:** non-included
**Explanation:** Not in mathlib.

### 194. Lemma 2.14.4 — M exact over C*_M
**Status:** non-included
**Explanation:** Not in mathlib.

### 195. Theorem 2.14.6 — Double centralizer theorem
**Status:** non-included
**Explanation:** The categorical double centralizer theorem (C = (C*_M)*_M) is not in mathlib. While the classical double centralizer theorem for rings/modules exists in some form, the categorical version is absent.

### 196. Lemma 2.14.7 — B-modules have form *A tensor X
**Status:** non-included
**Explanation:** Not in mathlib.

### 197. Corollary 2.14.9 — Exact module indecomposable over C*_M
**Status:** non-included
**Explanation:** Not in mathlib.

### 198. Lemma 2.14.10 — Fun_C(M1,M) exact over C*_M
**Status:** non-included
**Explanation:** Not in mathlib.

### 199. Theorem 2.14.11 — Bijection via duality
**Status:** non-included
**Explanation:** Not in mathlib.

### 200. Proposition 2.14.14 — Basic identity
**Status:** non-included
**Explanation:** Not in mathlib.

### 201. Definition 2.14.13 — Drinfeld center Z(C)
**Status:** included
**Explanation:** The Drinfeld center is defined in `Mathlib/CategoryTheory/Monoidal/Center.lean` as `Center C`. The definition includes half-braidings and the monoidal structure on the center. The forgetful functor from the center to C is also defined.

---

## Summary Statistics

- **Total statements:** 201
- **Included in Mathlib:** 33 (16.4%)
- **Not included in Mathlib:** 168 (83.6%)

### Included statements by topic:
- **Monoidal categories (basic definitions and axioms):** Definition 1.1.1, 1.1.2, 1.1.3, 1.2.6; Propositions 1.2.2, 1.2.3, 1.2.4 (7 items)
- **Monoidal functors:** Definitions 1.4.1, 1.4.5, 1.5.1; Proposition 1.4.3 (4 items)
- **Coherence:** Theorem 1.9.1 (1 item)
- **Duals and rigidity:** Definitions 1.10.1, 1.10.2, 1.10.11; Propositions 1.10.4, 1.10.7, 1.10.9 (6 items)
- **Schur's lemma:** Proposition 1.12.2 (1 item)
- **Coalgebras/Bialgebras/Hopf algebras:** Definitions 1.20.1, 1.20.2, 1.21.2, 1.22.2, 1.22.9, 1.24.2; Propositions 1.22.1, 1.22.4, 1.22.5 (9 items)
- **Algebras/modules/bimodules in categories:** Definitions 2.9.1, 2.9.5, 2.9.6, 2.9.24 (4 items)
- **Drinfeld center:** Definition 2.14.13 (1 item)

### Key areas NOT in Mathlib:
- Tensor category theory (multitensor, ring, fusion categories)
- Frobenius-Perron theory (dimensions, Frobenius-Perron theorem for matrices)
- Reconstruction theorems (Tannaka-type)
- Quasi-Hopf algebras and quasi-bialgebras
- Quantum groups
- Module categories over tensor categories
- Pivotal and spherical categories
- Chevalley property, coradical filtration
- Cartier-Kostant theorem
- Deligne tensor product
- Integrals in Hopf algebras
- Categorical freeness (Nichols-Zoeller type)
- Distinguished invertible object
- Dual categories and double centralizer theorem
