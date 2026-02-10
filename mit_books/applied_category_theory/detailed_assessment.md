# Detailed Assessment: Applied Category Theory Statements in Mathlib

## Statement 1: Definition 1.12 (Relation, Binary relation)
**Status**: included
**Explanation**: Relations and binary relations are basic concepts formalized throughout mathlib. Binary relations are represented as `α → α → Prop` and relations between two types as `α → β → Prop`.
**Mathlib references**: `Mathlib/Order/RelClasses.lean`, `Mathlib/Init/Order/Defs.lean`

## Statement 2: Definition 1.14 (Partition)
**Status**: included
**Explanation**: Partitions of sets are formalized in mathlib via `Setoid.Partition` and related structures, capturing the notion of a set decomposed into disjoint nonempty parts.
**Mathlib references**: `Mathlib/Order/Partition/Finpartition.lean`, `Mathlib/Data/Setoid/Partition.lean`

## Statement 3: Definition 1.18 (Equivalence relation)
**Status**: included
**Explanation**: Equivalence relations are a fundamental concept in mathlib, formalized via the `Equivalence` structure (reflexive, symmetric, transitive) and the `Setoid` typeclass.
**Mathlib references**: `Mathlib/Init/Logic.lean` (Equivalence), `Mathlib/Data/Setoid/Basic.lean`

## Statement 4: Proposition 1.19 (Partitions correspond to equivalence relations)
**Status**: included
**Explanation**: The bijection between partitions of a set and equivalence relations on it is established in mathlib through the `Setoid.Partition` API.
**Mathlib references**: `Mathlib/Data/Setoid/Partition.lean`

## Statement 5: Definition 1.21 (Quotient by equivalence relation)
**Status**: included
**Explanation**: Quotient types are built into Lean's type theory and extensively used in mathlib. Given a setoid, the quotient `Quotient s` is available.
**Mathlib references**: Built-in `Quotient` type, `Mathlib/Data/Setoid/Basic.lean`

## Statement 6: Definition 1.22 (Function)
**Status**: included
**Explanation**: Functions are primitive in Lean/mathlib as the function type `α → β`.
**Mathlib references**: Core Lean, `Mathlib/Logic/Function/Basic.lean`

## Statement 7: Definition 1.28 (Function composition)
**Status**: included
**Explanation**: Function composition is built into Lean as `Function.comp` (or `∘`).
**Mathlib references**: Core Lean, `Mathlib/Logic/Function/Basic.lean`

## Statement 8: Definition 1.30 (Preorder)
**Status**: included
**Explanation**: Preorders are formalized as the `Preorder` typeclass with `le_refl` and `le_trans`.
**Mathlib references**: `Mathlib/Order/Defs/Preorder.lean`, `Mathlib/Order/Defs/PartialOrder.lean`

## Statement 9: Definition 1.36 (Graph)
**Status**: included
**Explanation**: Graphs (quivers) are formalized in mathlib. The `Quiver` typeclass captures directed graphs with vertices and arrows.
**Mathlib references**: `Mathlib/Combinatorics/Quiver/Basic.lean`, `Mathlib/CategoryTheory/PathCategory.lean`

## Statement 10: Definition 1.59 (Monotone map)
**Status**: included
**Explanation**: Monotone maps are formalized as `Monotone f` (i.e., `∀ a b, a ≤ b → f a ≤ f b`) and as the bundled `OrderHom`.
**Mathlib references**: `Mathlib/Order/Monotone/Basic.lean`, `Mathlib/Order/Hom/Basic.lean`

## Statement 11: Proposition 1.70 (Identity and composition of monotone maps)
**Status**: included
**Explanation**: `monotone_id` establishes that the identity is monotone, and `Monotone.comp` establishes closure under composition.
**Mathlib references**: `Mathlib/Order/Monotone/Basic.lean`

## Statement 12: Definition 1.75 (Isomorphism of preorders)
**Status**: included
**Explanation**: Order isomorphisms are formalized as `OrderIso` (≃o), bundled monotone bijections with monotone inverse.
**Mathlib references**: `Mathlib/Order/Hom/Basic.lean`

## Statement 13: Proposition 1.78 (Monotone maps to Bool ↔ upper sets)
**Status**: included
**Explanation**: The correspondence between monotone maps to a two-element type and upper sets is captured in mathlib's `UpperSet` API.
**Mathlib references**: `Mathlib/Order/UpperLower/Basic.lean`

## Statement 14: Definition 1.81 (Meet and Join)
**Status**: included
**Explanation**: Meets (infima) and joins (suprema) are formalized via `Inf`, `Sup`, `SemilatticeInf`, `SemilatticeSup`, and the complete versions.
**Mathlib references**: `Mathlib/Order/Lattice.lean`, `Mathlib/Order/CompleteLattice.lean`

## Statement 15: Proposition 1.91 (Meet/join monotonicity w.r.t. subsets)
**Status**: included
**Explanation**: This is captured by `sInf_le_sInf` (if A ⊆ B then ⋀B ≤ ⋀A) and `sSup_le_sSup` in mathlib.
**Mathlib references**: `Mathlib/Order/CompleteLattice.lean`

## Statement 16: Definition 1.92 (Preserves meets/joins)
**Status**: included
**Explanation**: Preserving meets/joins is captured by conditions like `map_inf` and `map_sup` for lattice homomorphisms, and by `GaloisConnection` properties.
**Mathlib references**: `Mathlib/Order/Hom/Lattice.lean`, `Mathlib/Order/GaloisConnection/Basic.lean`

## Statement 17: Definition 1.93 (Generative effect)
**Status**: non-included
**Explanation**: The notion of "generative effect" as failure to preserve joins is specific to the applied category theory literature (Adam's thesis). This specific concept is not formalized in mathlib, though the underlying notion of not preserving joins is expressible.
**Mathlib references**: None

## Statement 18: Definition 1.95 (Galois connection)
**Status**: included
**Explanation**: Galois connections are formalized as `GaloisConnection l u`, defined by the condition `l a ≤ b ↔ a ≤ u b`.
**Mathlib references**: `Mathlib/Order/GaloisConnection/Defs.lean`, `Mathlib/Order/GaloisConnection/Basic.lean`

## Statement 19: Proposition 1.107 (Equivalent characterization of Galois connections)
**Status**: included
**Explanation**: The equivalent characterization via unit/counit conditions (p ≤ g(f(p)) and f(g(q)) ≤ q) is available in mathlib.
**Mathlib references**: `Mathlib/Order/GaloisConnection/Basic.lean` (`GaloisConnection.le_u_l`, `GaloisConnection.l_u_le`)

## Statement 20: Proposition 1.111 (Right adjoints preserve meets, left adjoints preserve joins)
**Status**: included
**Explanation**: This is formalized in mathlib. `GaloisConnection.l_sup` shows left adjoints preserve binary joins; `GaloisConnection.u_inf` shows right adjoints preserve binary meets. The general versions for arbitrary sups/infs are also present.
**Mathlib references**: `Mathlib/Order/GaloisConnection/Basic.lean` (`l_sup`, `u_inf`, `isLUB_l_image`, `isGLB_u_image`)

## Statement 21: Theorem 1.115 (Adjoint functor theorem for preorders)
**Status**: included
**Explanation**: The adjoint functor theorem for complete lattices is formalized. A monotone map on a complete lattice that preserves all infs has a left adjoint, and dually.
**Mathlib references**: `Mathlib/Order/GaloisConnection/Basic.lean`, `Mathlib/Order/CompleteLattice.lean`

## Statement 22: Definition 1.120 (Closure operator)
**Status**: included
**Explanation**: Closure operators are formalized as `ClosureOperator`, a monotone, extensive, and idempotent map.
**Mathlib references**: `Mathlib/Order/Closure.lean`

## Statement 23: Definition 2.2 (Symmetric monoidal preorder)
**Status**: non-included
**Explanation**: Symmetric monoidal preorders as defined in this book (a preorder with a monoidal product satisfying specific conditions) are not formalized as such in mathlib. Mathlib has `MonoidalCategory` for categories and ordered algebraic structures, but not this specific preorder-level concept.
**Mathlib references**: None directly; related concepts exist in `Mathlib/Order/Lattice.lean` for specific cases

## Statement 24: Proposition 2.38 (Opposite of symmetric monoidal preorder)
**Status**: non-included
**Explanation**: This specific statement about monoidal preorders is not formalized. Mathlib has the dual/opposite for categories but not for monoidal preorders per se.
**Mathlib references**: None

## Statement 25: Definition 2.41 (Monoidal monotone)
**Status**: non-included
**Explanation**: Monoidal monotone maps between monoidal preorders are not formalized in mathlib. The categorical analog (monoidal functor) exists but not at the preorder level.
**Mathlib references**: None

## Statement 26: Definition 2.46 (V-category / Enriched category)
**Status**: included
**Explanation**: Enriched categories are formalized in mathlib's `CategoryTheory.Enriched` directory.
**Mathlib references**: `Mathlib/CategoryTheory/Enriched/Ordinary/Basic.lean`, `Mathlib/CategoryTheory/Enriched/Basic.lean`

## Statement 27: Theorem 2.49 (Preorders ↔ Bool-categories)
**Status**: non-included
**Explanation**: The specific correspondence between preorders and Bool-enriched categories is not formalized in mathlib. While enriched categories exist and preorders exist, this particular equivalence has not been established.
**Mathlib references**: None

## Statement 28: Definition 2.51 (Metric space)
**Status**: included
**Explanation**: Metric spaces are extensively formalized in mathlib via `MetricSpace` and `PseudoMetricSpace`.
**Mathlib references**: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`, `Mathlib/Topology/MetricSpace/Basic.lean`

## Statement 29: Definition 2.53 (Lawvere metric space)
**Status**: non-included
**Explanation**: Lawvere metric spaces as Cost-categories are not formalized in mathlib. While `PseudoMetricSpace` captures similar ideas (dropping symmetry and allowing d(x,y) = 0 without x = y), the enriched-categorical viewpoint of Lawvere metric spaces is absent.
**Mathlib references**: None directly; `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` is related

## Statement 30: Definition 2.69 (V-functor / Enriched functor)
**Status**: included
**Explanation**: Enriched functors are formalized in mathlib's enriched category framework.
**Mathlib references**: `Mathlib/CategoryTheory/Enriched/Ordinary/Basic.lean`

## Statement 31: Definition 2.74 (Product of V-categories)
**Status**: included
**Explanation**: Products of enriched categories are available in mathlib's enriched category framework.
**Mathlib references**: `Mathlib/CategoryTheory/Enriched/Limits/HasConicalProducts.lean`

## Statement 32: Definition 2.79 (Symmetric monoidal closed preorder)
**Status**: non-included
**Explanation**: This preorder-level concept of monoidal closure is not formalized as such. Mathlib has `MonoidalClosed` for categories, not for preorders. The preorder analog is partially captured by residuated lattices.
**Mathlib references**: None directly; `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean` is the categorical version

## Statement 33: Proposition 2.87 (Properties of closed monoidal preorders)
**Status**: non-included
**Explanation**: These properties for monoidal preorders are not formalized at the preorder level. Some individual properties (like tensor-hom adjunction) exist at the category level.
**Mathlib references**: None directly

## Statement 34: Definition 2.90 (Unital commutative quantale)
**Status**: included
**Explanation**: Quantales are formalized in mathlib. A unital commutative quantale corresponds to a `CommQuantale` or similar structure.
**Mathlib references**: `Mathlib/Algebra/Order/Quantale.lean`

## Statement 35: Proposition 2.96 (All joins iff all meets)
**Status**: included
**Explanation**: This is captured by the fact that a complete lattice has both all sups and all infs. The proof that having all sups implies having all infs is standard in mathlib's complete lattice theory.
**Mathlib references**: `Mathlib/Order/CompleteLattice.lean`

## Statement 36: Proposition 2.98 (Closed iff tensor distributes over joins)
**Status**: non-included
**Explanation**: This specific characterization of when a monoidal preorder with all joins is closed is not formalized at the preorder level in mathlib. The categorical version of this relationship is partially present.
**Mathlib references**: None directly

## Statement 37: Definition 2.100 (V-matrix)
**Status**: non-included
**Explanation**: Matrices with entries in a quantale (V-matrices) are not formalized in mathlib. Standard matrices over rings/semirings exist but not the quantale-valued generalization.
**Mathlib references**: None

## Statement 38: Definition 3.6 (Category)
**Status**: included
**Explanation**: Categories are fundamentally formalized in mathlib via the `Category` typeclass.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Basic.lean`

## Statement 39: Definition 3.7 (Free category on a graph)
**Status**: included
**Explanation**: Free categories on quivers are formalized in mathlib via path categories.
**Mathlib references**: `Mathlib/CategoryTheory/PathCategory.lean`, `Mathlib/Combinatorics/Quiver/Path.lean`

## Statement 40: Definition 3.24 (Category of sets)
**Status**: included
**Explanation**: The category of types (serving as the category of sets) is formalized.
**Mathlib references**: `Mathlib/CategoryTheory/Types.lean`

## Statement 41: Definition 3.28 (Isomorphism in a category)
**Status**: included
**Explanation**: Isomorphisms are formalized as `Iso` in mathlib's category theory library.
**Mathlib references**: `Mathlib/CategoryTheory/Iso.lean`

## Statement 42: Definition 3.35 (Functor)
**Status**: included
**Explanation**: Functors are formalized as `CategoryTheory.Functor`.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Basic.lean`

## Statement 43: Definition 3.44 (Database instance as functor to Set)
**Status**: non-included
**Explanation**: The specific interpretation of database instances as functors C → Set is not formalized in mathlib. While functors to Type exist, the database-theoretic interpretation is absent.
**Mathlib references**: None

## Statement 44: Definition 3.49 (Natural transformation)
**Status**: included
**Explanation**: Natural transformations are formalized as `NatTrans`.
**Mathlib references**: `Mathlib/CategoryTheory/NatTrans.lean`

## Statement 45: Definition 3.51 (Diagram)
**Status**: included
**Explanation**: Diagrams as functors from an indexing category are the standard setup for limits/colimits in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/IsLimit.lean`

## Statement 46: Definition 3.54 (Functor category)
**Status**: included
**Explanation**: Functor categories are formalized in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Category.lean`

## Statement 47: Definition 3.60 (Instance homomorphism)
**Status**: non-included
**Explanation**: Instance homomorphisms in the database sense are not specifically formalized. Natural transformations between functors to Set exist but not under this terminology.
**Mathlib references**: None specific; `Mathlib/CategoryTheory/NatTrans.lean` covers the general case

## Statement 48: Definition 3.68 (Pullback of instance along functor)
**Status**: included
**Explanation**: Precomposition of a functor (pulling back along a functor) is standard in mathlib. This is `F ⋙ I` in mathlib notation.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Basic.lean` (functor composition `⋙`)

## Statement 49: Definition 3.70 (Adjunction of functors)
**Status**: included
**Explanation**: Adjunctions between functors are extensively formalized in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Adjunction/Basic.lean`

## Statement 50: Definition 3.79 (Terminal object)
**Status**: included
**Explanation**: Terminal objects are formalized via `IsTerminal` and `Limits.HasTerminal`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Terminal.lean`

## Statement 51: Proposition 3.84 (Terminal objects are isomorphic)
**Status**: included
**Explanation**: The uniqueness (up to unique isomorphism) of terminal objects is established in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Terminal.lean` (`IsTerminal.uniqueUpToIso`)

## Statement 52: Definition 3.86 (Product in a category)
**Status**: included
**Explanation**: Products are formalized via the binary products API.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean`

## Statement 53: Definition 3.92 (Cone and Limit)
**Status**: included
**Explanation**: Cones and limits are formalized as `Cone` and `IsLimit`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Cones.lean`, `Mathlib/CategoryTheory/Limits/IsLimit.lean`

## Statement 54: Theorem 3.95 (Finite limits in Set)
**Status**: included
**Explanation**: The construction of finite limits in the category of types is formalized. Limits are constructed as subtypes of products.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Types/Products.lean`, `Mathlib/CategoryTheory/Limits/Types/Pullbacks.lean`

## Statement 55: Definition 3.102 (Cocone and Colimit)
**Status**: included
**Explanation**: Cocones and colimits are formalized as `Cocone` and `IsColimit`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Cones.lean`, `Mathlib/CategoryTheory/Limits/IsLimit.lean`

## Statement 56: Definition 4.2 (Feasibility relation)
**Status**: non-included
**Explanation**: Feasibility relations as Bool-profunctors are specific to this textbook and are not formalized in mathlib.
**Mathlib references**: None

## Statement 57: Definition 4.8 (V-profunctor)
**Status**: non-included
**Explanation**: Enriched profunctors (V-profunctors) are not formalized in mathlib. There is a mention of profunctors in the Day convolution file but not a general theory.
**Mathlib references**: None; `Mathlib/CategoryTheory/Monoidal/DayConvolution/Closed.lean` mentions profunctors tangentially

## Statement 58: Definition 4.21 (Composition of V-profunctors)
**Status**: non-included
**Explanation**: Composition of enriched profunctors via the coend formula is not formalized in mathlib.
**Mathlib references**: None

## Statement 59: Theorem 4.23 (Category Prof_V)
**Status**: non-included
**Explanation**: The category of V-profunctors is not formalized in mathlib.
**Mathlib references**: None

## Statement 60: Definition 4.24 (Feas := Prof_Bool)
**Status**: non-included
**Explanation**: The category of feasibility relations is specific to this textbook and not in mathlib.
**Mathlib references**: None

## Statement 61: Lemma 4.27 (Unit profunctor is identity)
**Status**: non-included
**Explanation**: Not formalized as profunctors are not in mathlib.
**Mathlib references**: None

## Statement 62: Lemma 4.31 (Associativity of profunctor composition)
**Status**: non-included
**Explanation**: Not formalized as profunctors are not in mathlib.
**Mathlib references**: None

## Statement 63: Definition 4.34 (Companion and conjoint)
**Status**: non-included
**Explanation**: Companions and conjoints of V-functors are not formalized in mathlib.
**Mathlib references**: None

## Statement 64: Definition 4.42 (Collage of a profunctor)
**Status**: non-included
**Explanation**: The collage construction for profunctors is not formalized in mathlib.
**Mathlib references**: None

## Statement 65: Definition 4.58 (Dual / Compact closed category)
**Status**: included
**Explanation**: Compact closed categories (rigid categories) are formalized in mathlib via `ExactPairing` and `RigidCategory`. The snake equations are the triangle identities for exact pairings.
**Mathlib references**: `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`

## Statement 66: Proposition 4.60 (Compact closed implies monoidal closed)
**Status**: included
**Explanation**: The fact that a rigid (compact closed) category is monoidal closed is established in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean`

## Statement 67: Theorem 4.63 (Prof_V is compact closed)
**Status**: non-included
**Explanation**: As the category Prof_V is not formalized, this theorem about it being compact closed is also absent.
**Mathlib references**: None

## Statement 68: Definition 5.2 (Prop)
**Status**: non-included
**Explanation**: Props (PROducts and Permutations categories) as symmetric strict monoidal categories with ℕ as objects are not formalized in mathlib. This is a specialized concept from the theory of string diagrams.
**Mathlib references**: None

## Statement 69: Definition 5.11 (Prop functor)
**Status**: non-included
**Explanation**: Identity-on-objects strict monoidal functors between props are not formalized.
**Mathlib references**: None

## Statement 70: Definition 5.13 (Port graph)
**Status**: non-included
**Explanation**: Port graphs are a specialized combinatorial structure not formalized in mathlib.
**Mathlib references**: None

## Statement 71: Definition 5.25 (Prop signature)
**Status**: non-included
**Explanation**: Prop signatures (sets of generators with arities) are not formalized in mathlib.
**Mathlib references**: None

## Statement 72: Proposition 5.29 (Universal property of free prop)
**Status**: non-included
**Explanation**: Free props and their universal property are not formalized.
**Mathlib references**: None

## Statement 73: Definition 5.30 (Prop expression)
**Status**: non-included
**Explanation**: Inductively defined prop expressions are not formalized in mathlib.
**Mathlib references**: None

## Statement 74: Definition 5.36 (Rig)
**Status**: included
**Explanation**: A rig (also called a semiring) is formalized in mathlib as `Semiring`. The definition matches: an additive commutative monoid and a multiplicative monoid with distributivity and zero absorption.
**Mathlib references**: `Mathlib/Algebra/Ring/Defs.lean`

## Statement 75: Definition 5.45 (Matrix over a rig)
**Status**: included
**Explanation**: Matrices over semirings are formalized in mathlib.
**Mathlib references**: `Mathlib/Data/Matrix/Basic.lean`

## Statement 76: Definition 5.50 (Prop of R-matrices)
**Status**: non-included
**Explanation**: The prop Mat(R) with matrix multiplication as composition and direct sum as monoidal product is not formalized as a prop in mathlib. Matrices and their multiplication exist, but not the prop structure.
**Mathlib references**: None directly; `Mathlib/Data/Matrix/Basic.lean` has matrix multiplication

## Statement 77: Theorem 5.53 (Prop functor SFG_R → Mat(R))
**Status**: non-included
**Explanation**: Signal flow graphs and this functor are specific to the textbook and not in mathlib.
**Mathlib references**: None

## Statement 78: Proposition 5.54 (Matrix interpretation of signal flow graphs)
**Status**: non-included
**Explanation**: Signal flow graph theory is not in mathlib.
**Mathlib references**: None

## Statement 79: Proposition 5.56 (Surjectivity of signal flow graph functor)
**Status**: non-included
**Explanation**: Signal flow graph theory is not in mathlib.
**Mathlib references**: None

## Statement 80: Theorem 5.60 (Presentation of Mat(R))
**Status**: non-included
**Explanation**: The presentation of the prop Mat(R) by generators and relations is not in mathlib.
**Mathlib references**: None

## Statement 81: Definition 5.65 (Monoid object in a monoidal category)
**Status**: included
**Explanation**: Monoid objects in monoidal categories are formalized as `Mon_` in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Monoidal/Mon_.lean`

## Statement 82: Definition 5.79 (Prop of R-relations)
**Status**: non-included
**Explanation**: The prop Rel_R of R-valued relations is not formalized in mathlib.
**Mathlib references**: None

## Statement 83: Theorem 5.87 (Rel_R is compact closed)
**Status**: non-included
**Explanation**: As Rel_R is not formalized, this structural result is also absent.
**Mathlib references**: None

## Statement 84: Definition 6.1 (Initial object)
**Status**: included
**Explanation**: Initial objects are formalized via `IsInitial` and `Limits.HasInitial`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Terminal.lean`

## Statement 85: Definition 6.11 (Coproduct)
**Status**: included
**Explanation**: Coproducts are formalized via the coproducts API.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean` (via duality), `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`

## Statement 86: Definition 6.19 (Pushout)
**Status**: included
**Explanation**: Pushouts are formalized in mathlib's limits/shapes library.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Basic.lean` (pushouts defined as colimits)

## Statement 87: Definition 6.30 (Has finite colimits)
**Status**: included
**Explanation**: `HasFiniteColimits` is a standard typeclass in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/HasLimits.lean`

## Statement 88: Proposition 6.32 (Equivalent conditions for finite colimits)
**Status**: included
**Explanation**: The equivalence between having finite colimits, having initial object + pushouts, and having coequalizers + finite coproducts is established in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Constructions/FiniteProductsOfBinaryProducts.lean`, `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`

## Statement 89: Corollary 6.36 (FinSet and Set have finite colimits)
**Status**: included
**Explanation**: The category of types has all colimits, and the category of finite types has finite colimits.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Types/ColimitType.lean`

## Statement 90: Theorem 6.37 (Finite colimits in Set)
**Status**: included
**Explanation**: Colimits in the category of types are constructed as quotients of coproducts, matching the formula given.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Types/ColimitType.lean`, `Mathlib/CategoryTheory/Limits/Types/Pushouts.lean`

## Statement 91: Definition 6.43 (Cospan)
**Status**: non-included
**Explanation**: While cospans appear implicitly in pushout definitions, there is no dedicated `Cospan` type formalized in mathlib as a standalone concept for building categories.
**Mathlib references**: None as a standalone; pushouts use cospan-shaped diagrams

## Statement 92: Definition 6.45 (Category of cospans)
**Status**: non-included
**Explanation**: The category Cospan_C (with objects from C and cospans as morphisms composed via pushouts) is not formalized in mathlib.
**Mathlib references**: None

## Statement 93: Definition 6.52 (Frobenius structure / Frobenius monoid)
**Status**: non-included
**Explanation**: Special commutative Frobenius monoids in monoidal categories are not formalized in mathlib. While Frobenius algebras appear in ring theory contexts, the categorical Frobenius structure is absent.
**Mathlib references**: None in the categorical sense

## Statement 94: Definition 6.54 (Spider morphism)
**Status**: non-included
**Explanation**: Spider morphisms for Frobenius monoids are not formalized in mathlib.
**Mathlib references**: None

## Statement 95: Theorem 6.55 (Spider theorem)
**Status**: non-included
**Explanation**: The spider theorem (connected diagrams of Frobenius generators are determined by their type) is not formalized.
**Mathlib references**: None

## Statement 96: Theorem 6.58 (Presentation of hypergraph category generators)
**Status**: non-included
**Explanation**: The presentation theory for hypergraph categories is not in mathlib.
**Mathlib references**: None

## Statement 97: Definition 6.60 (Hypergraph category)
**Status**: non-included
**Explanation**: Hypergraph categories (symmetric monoidal categories with compatible Frobenius structures on all objects) are not formalized in mathlib.
**Mathlib references**: None

## Statement 98: Definition 6.75 (F-decorated cospan)
**Status**: non-included
**Explanation**: Decorated cospans are not formalized in mathlib. This is a specialized construction from applied category theory.
**Mathlib references**: None

## Statement 99: Theorem 6.77 (Hypergraph category of decorated cospans)
**Status**: non-included
**Explanation**: The construction of hypergraph categories from decorated cospans is not in mathlib.
**Mathlib references**: None

## Statement 100: Definition 6.97 (Operad underlying a monoidal category)
**Status**: non-included
**Explanation**: Operads are not formalized in mathlib. There are only tangential mentions.
**Mathlib references**: None

## Statement 101: Definition 6.99 (Algebra for an operad)
**Status**: non-included
**Explanation**: Operad algebras are not formalized in mathlib.
**Mathlib references**: None

## Statement 102: Proposition 6.101 (Cospan-algebras ≃ hypergraph props)
**Status**: non-included
**Explanation**: Neither Cospan-algebras nor hypergraph props are formalized in mathlib.
**Mathlib references**: None

## Statement 103: Proposition 7.3 (Pullback pasting lemma)
**Status**: included
**Explanation**: The pullback pasting lemma (if the right square is a pullback, then the left square is a pullback iff the whole rectangle is) is formalized in mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Connected.lean`

## Statement 104: Definition 7.5 (Monomorphism and Epimorphism)
**Status**: included
**Explanation**: Monomorphisms and epimorphisms are formalized as `Mono` and `Epi` typeclasses. The characterization via pullbacks/pushouts is also available.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean`, `Mathlib/CategoryTheory/EpiMono.lean`

## Statement 105: Definition 7.12 (Subobject classifier)
**Status**: non-included
**Explanation**: Subobject classifiers are not fully formalized in mathlib. There is some work on topos-related structures but `SubobjectClassifier` as a standalone definition does not appear as a general formalization. The `Topos.Classifier` file exists but focuses on Grothendieck toposes.
**Mathlib references**: `Mathlib/CategoryTheory/Topos/Classifier.lean` (partial, for Grothendieck toposes)

## Statement 106: Definition 7.22 (Presheaf)
**Status**: included
**Explanation**: Presheaves as functors C^op → Set are standard in mathlib, used extensively in the sites/sheaves framework.
**Mathlib references**: `Mathlib/CategoryTheory/Yoneda.lean`, `Mathlib/CategoryTheory/Sites/SheafOfTypes.lean`

## Statement 107: Definition 7.25 (Topology / Topological space)
**Status**: included
**Explanation**: Topological spaces are extensively formalized in mathlib via the `TopologicalSpace` typeclass.
**Mathlib references**: `Mathlib/Topology/Defs/Basic.lean`

## Statement 108: Definition 7.35 (Sheaf on a topological space)
**Status**: included
**Explanation**: Sheaves on topological spaces are formalized in mathlib, including the sheaf condition with matching families and unique gluing.
**Mathlib references**: `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean`, `Mathlib/Topology/Sheaves/Sheaf.lean`

## Statement 109: Definition 7.69 (Modality in Shv(X))
**Status**: non-included
**Explanation**: Modalities (Lawvere-Tierney topologies) as endomorphisms j: Ω → Ω on the subobject classifier satisfying idempotency, inflation, and meet-preservation are not formalized in mathlib.
**Mathlib references**: None

## Statement 110: Proposition 7.71 (Examples of modalities from propositions)
**Status**: non-included
**Explanation**: These specific constructions of modalities (p ⇒ -, p ∨ -, (- ⇒ p) ⇒ p) are not formalized as they depend on the unformalized modality concept.
**Mathlib references**: None

## Statement 111: Example 5.6 (Prop Bij)
**Status**: non-included
**Explanation**: The prop of bijections is not formalized in mathlib.
**Mathlib references**: None

## Statement 112: Example 5.7 (Prop Corel)
**Status**: non-included
**Explanation**: The prop of corelations is not formalized in mathlib.
**Mathlib references**: None

## Statement 113: Example 5.8 (Prop Rel)
**Status**: non-included
**Explanation**: The prop of relations is not formalized in mathlib as a prop.
**Mathlib references**: None
