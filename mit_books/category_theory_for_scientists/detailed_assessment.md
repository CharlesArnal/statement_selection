# Detailed Assessment: Mathlib Coverage

## Source: Category Theory for Scientists (David I. Spivak, MIT)

Each statement is assessed against the Mathlib library for Lean 4.

---

## Chapter 2: The Category of Sets

### Statement 1: Notation 2.1.1.1
**Status**: INCLUDED
**Explanation**: The empty set and the natural numbers are core types in Lean and Mathlib. The empty type is `Empty` (or `PEmpty` for `Prop`-valued emptiness), and the natural numbers are the built-in type `Nat`. Additionally, `Set.empty` or `(emptyset)` is available. These are foundational to Lean itself.
**Mathlib references**: `Init.Prelude` (for `Nat`), `Mathlib/Data/Set/Basic.lean` (for `Set.empty`), `Mathlib/Data/Set/Insert.lean`

### Statement 2: Lemma 2.1.2.12
**Status**: INCLUDED
**Explanation**: Isomorphism of sets is formalized via `Equiv` (bijections). `Equiv.refl`, `Equiv.symm`, and `Equiv.trans` provide reflexivity, symmetry, and transitivity respectively, showing that set isomorphism is an equivalence relation.
**Mathlib references**: `Mathlib/Logic/Equiv/Defs.lean` (`Equiv.refl`, `Equiv.symm`, `Equiv.trans`), `Mathlib/Logic/Equiv/Basic.lean`

### Statement 3: Definition 2.1.2.16
**Status**: INCLUDED
**Explanation**: Cardinality of finite sets is formalized via `Fintype.card`, which gives the number of elements in a type with a `Fintype` instance. There is also `Finset.card` for finite subsets and `Set.ncard` for sets.
**Mathlib references**: `Mathlib/Data/Fintype/Card.lean` (`Fintype.card`), `Mathlib/Data/Set/Card.lean`

### Statement 4: Lemma 2.1.2.18
**Status**: INCLUDED
**Explanation**: If two finite sets are isomorphic (i.e., there is an `Equiv` between them), they have the same cardinality. This is `Fintype.card_congr` which states that an equivalence between types implies equal cardinality.
**Mathlib references**: `Mathlib/Data/Fintype/Card.lean` (`Fintype.card_congr`)

### Statement 5: Definition 2.4.1.1
**Status**: INCLUDED
**Explanation**: The product of two sets/types is the built-in `Prod` type in Lean, consisting of ordered pairs `(a, b)` where `a : A` and `b : B`. This is a core language construct.
**Mathlib references**: Core Lean `Init.Prelude` (for `Prod`), `Mathlib/Data/Prod/Basic.lean`

### Statement 6: Lemma 2.4.1.10
**Status**: INCLUDED
**Explanation**: The universal property of the product is captured by `Prod.mk` and the projection functions `Prod.fst`, `Prod.snd`. In the categorical setting, `CategoryTheory.Limits.BinaryProductData` and `CategoryTheory.Limits.Types.binaryProductIso` formalize the universal property of products in the category of types.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean`, `Mathlib/CategoryTheory/Limits/Types.lean`

### Statement 7: Definition 2.4.2.1
**Status**: INCLUDED
**Explanation**: The coproduct (disjoint union) of two sets is formalized as `Sum` in Lean, with injections `Sum.inl` and `Sum.inr`. In the categorical setting, `CategoryTheory.Limits.Types.binaryCoproductIso` shows `Sum` is the coproduct in the category of types.
**Mathlib references**: `Mathlib/Data/Sum/Basic.lean`, `Mathlib/CategoryTheory/Limits/Types.lean`

### Statement 8: Lemma 2.4.2.7
**Status**: INCLUDED
**Explanation**: The universal property of the coproduct states that given functions from `X` and `Y` to `A`, there is a unique function from `X + Y` to `A`. This is `Sum.elim` in Lean, and categorically it is the colimit property for binary coproducts.
**Mathlib references**: `Mathlib/Data/Sum/Basic.lean` (`Sum.elim`), `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean`

### Statement 9: Definition 2.5.1.1
**Status**: INCLUDED
**Explanation**: The fiber product (pullback) of sets is formalized in Mathlib's category theory library. The pullback of `f : X -> B` and `g : Y -> B` is the subtype of pairs in `X x Y` where `f(x) = g(y)`. Categorically, this is captured by `CategoryTheory.Limits.pullback` and `CategoryTheory.Limits.PullbackCone`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`, `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`, `Mathlib/CategoryTheory/Limits/Types/Pullbacks.lean`

### Statement 10: Definition 2.5.1.12
**Status**: INCLUDED
**Explanation**: The preimage of an element under a function is formalized as `Set.preimage` (notation `f ⁻¹' s` for sets, or the fiber `f ⁻¹' {y}` for a single element). This is a fundamental operation on sets in Mathlib.
**Mathlib references**: `Mathlib/Data/Set/Image.lean` (`Set.preimage`), `Mathlib/Data/Set/Operations.lean`

### Statement 11: Lemma 2.5.1.14
**Status**: INCLUDED
**Explanation**: The universal property of the pullback is formalized categorically. Given a commuting square, there is a unique map to the pullback. This is `CategoryTheory.Limits.PullbackCone.isLimit` and the associated lift.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`, `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`

### Statement 12: Proposition 2.5.1.17
**Status**: INCLUDED
**Explanation**: The pullback of a monomorphism is a monomorphism. This is proved in Mathlib for general categories and specifically in the category of types.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Mono.lean` (`pullback.snd_of_mono`, `pullback.fst_of_mono`)

### Statement 13: Definition 2.5.2.1
**Status**: INCLUDED
**Explanation**: A span on two objects `A` and `B` is a triple `(R, f, g)` where `f : R -> A` and `g : R -> B`. In Mathlib's category theory library, spans are formalized as `CategoryTheory.Limits.WalkingSpan` and related structures; in the setting of sets, this is simply a type with two functions out of it.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Cospan.lean` (span-related definitions)

### Statement 14: Definition 2.5.2.3
**Status**: INCLUDED
**Explanation**: The composite of spans via fiber product is related to the composition of correspondences. The composition of two spans uses the pullback over the shared object. This is captured in Mathlib by pullback constructions.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`, `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Assoc.lean`

### Statement 15: Definition 2.5.3.1
**Status**: INCLUDED
**Explanation**: The equalizer of two parallel morphisms `f, g : X -> Y` is the subobject of `X` where `f` and `g` agree. This is formalized categorically as `CategoryTheory.Limits.equalizer` and in types as the subtype `{x | f x = g x}`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean` (`equalizer`, `Fork`)

### Statement 16: Definition 2.6.1.1
**Status**: INCLUDED
**Explanation**: Equivalence relations are formalized in Lean/Mathlib via the `Setoid` class (or `Equivalence` structure), which bundles a relation satisfying reflexivity, symmetry, and transitivity. `Setoid` is a type equipped with an equivalence relation.
**Mathlib references**: Core Lean `Init.Prelude` (`Equivalence`), `Mathlib/Order/Defs/PartialOrder.lean`, `Mathlib/Data/Setoid/Basic.lean`

### Statement 17: Lemma 2.6.1.7
**Status**: INCLUDED
**Explanation**: The smallest equivalence relation containing a given relation is formalized as `EqvGen`, the equivalence closure of a relation. `EqvGen R` is the smallest equivalence relation containing `R`.
**Mathlib references**: `Mathlib/Logic/Relation.lean` (`EqvGen`)

### Statement 18: Definition 2.6.2.1
**Status**: INCLUDED
**Explanation**: The pushout is formalized categorically in Mathlib. For types/sets, the pushout of `f : A -> X` and `g : A -> Y` is the quotient of `X + Y` by the relation identifying `f(a)` with `g(a)`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean` (pushout), `Mathlib/CategoryTheory/Limits/Types/Pushouts.lean`

### Statement 19: Lemma 2.6.2.8
**Status**: INCLUDED
**Explanation**: The universal property of the pushout is that it is the colimit of the span diagram. Given compatible maps from `X` and `Y` to some `Z`, there is a unique map from the pushout. This is `CategoryTheory.Limits.PushoutCocone.isColimit`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean` (pushout cocone), `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`

### Statement 20: Definition 2.6.3.1
**Status**: INCLUDED
**Explanation**: The coequalizer of two parallel morphisms `f, g : X -> Y` is the quotient of `Y` by the equivalence relation generated by `{(f(x), g(x))}`. This is formalized as `CategoryTheory.Limits.coequalizer`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean` (`coequalizer`, `Cofork`)

### Statement 21: Definition 2.7.1.1
**Status**: INCLUDED
**Explanation**: Retract sections and projections correspond to split monomorphisms and split epimorphisms. In Mathlib, `CategoryTheory.SplitMono` and `CategoryTheory.SplitEpi` formalize this concept, where a section is a morphism with a left inverse and a retraction has a right inverse. In the function setting, `Function.LeftInverse` and `Function.RightInverse` capture this.
**Mathlib references**: `Mathlib/CategoryTheory/EpiMono.lean` (`SplitMono`, `SplitEpi`), `Mathlib/Logic/Function/Basic.lean` (`Function.LeftInverse`, `Function.RightInverse`)

### Statement 22: Notation 2.7.2.1
**Status**: INCLUDED
**Explanation**: The set of functions from `A` to `B` is simply the function type `A -> B` in Lean. In Set-theoretic terms, `Set.pi` or simply the function space. The categorical `Hom` is `CategoryTheory.types` functor's hom-set.
**Mathlib references**: Core Lean (function types), `Mathlib/CategoryTheory/Types.lean`

### Statement 23: Proposition 2.7.2.3
**Status**: INCLUDED
**Explanation**: Currying is formalized as `Function.curry` and `Function.uncurry`, establishing the bijection between `(X x A -> Y)` and `(X -> (A -> Y))`. Categorically, this is the closed structure of the category of types.
**Mathlib references**: `Mathlib/Logic/Function/Basic.lean` (`Function.curry`, `Function.uncurry`), `Mathlib/CategoryTheory/Closed/Types.lean`

### Statement 24: Proposition 2.7.3.1
**Status**: INCLUDED
**Explanation**: The arithmetic identities for sets (involving products, coproducts, and exponentials) are formalized through various `Equiv` constructions in Mathlib, such as `Equiv.sumEmpty`, `Equiv.sumComm`, `Equiv.prodEmpty`, `Equiv.prodPUnit`, `Equiv.prodComm`, `Equiv.sumAssoc`, `Equiv.prodAssoc`, `Equiv.sumProdDistrib`, etc.
**Mathlib references**: `Mathlib/Logic/Equiv/Basic.lean` (various `Equiv` identities), `Mathlib/Logic/Equiv/Defs.lean`

### Statement 25: Definition 2.7.4.1
**Status**: INCLUDED
**Explanation**: The power set `P(B)` is formalized as `Set B` in Lean/Mathlib, which is the type of all subsets of `B` (i.e., `B -> Prop`). The `powerset` operation on `Finset` and `Set` is also available.
**Mathlib references**: `Mathlib/Data/Set/Basic.lean` (`Set`), `Mathlib/Data/Set/Insert.lean`

### Statement 26: Definition 2.7.4.4
**Status**: NOT INCLUDED
**Explanation**: The notion of a downward-closed family of subsets (abstract simplicial complex structure) as described by Spivak is not directly formalized in Mathlib. Mathlib has `IsLowerSet` for lower sets in a partial order, and `Geometry.SimplicialComplex` for geometric simplicial complexes in vector spaces, but not the combinatorial abstract simplicial complex defined as a downward-closed family of finite subsets with the atom condition.
**Mathlib references**: `Mathlib/Order/UpperLower/Basic.lean` (`IsLowerSet` -- related but different context), `Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean` (geometric, not abstract)

### Statement 27: Definition 2.7.4.9
**Status**: NOT INCLUDED
**Explanation**: The subobject classifier for the category Set (the two-element set with a truth value map) is not formalized as such in Mathlib. While Mathlib has `Prop` which serves as a subobject classifier in Lean's type theory, and there is work on subobject classifiers in topos theory (`CategoryTheory.Topos.Classifier`), the specific elementary construction for Set as described by Spivak is not directly available.
**Mathlib references**: `Mathlib/CategoryTheory/Topos/Classifier.lean` (general topos-theoretic concept, but not the specific Set-based construction)

### Statement 28: Proposition 2.7.4.10
**Status**: NOT INCLUDED
**Explanation**: The isomorphism `P(B) = Hom(B, Omega)` where `Omega = {True, False}` is essentially the statement that subsets correspond to characteristic functions. While this is a consequence of Lean's type theory (where `Set B = B -> Prop`), the specific formulation with a two-element subobject classifier and the explicit bijection with the power set is not formalized in Mathlib.
**Mathlib references**: None (the underlying idea is built into Lean's `Set B = B -> Prop`)

### Statement 29: Definition 2.7.4.11
**Status**: INCLUDED
**Explanation**: The characteristic function of a subset `B'` of `B` is essentially the membership predicate, which is built into Lean's definition of `Set B` as `B -> Prop`. The indicator function `Set.indicator` maps to values in a type with zero, assigning 1 inside the set and 0 outside.
**Mathlib references**: `Mathlib/Data/Set/Basic.lean` (membership), `Mathlib/Algebra/Order/Group/Indicator.lean` (`Set.indicator`)

### Statement 30: Definition 2.7.5.1
**Status**: INCLUDED
**Explanation**: `Function.Injective` and `Function.Surjective` are defined in Lean/Mathlib. Injective means `f(x) = f(x') -> x = x'` and surjective means `forall y, exists x, f(x) = y`.
**Mathlib references**: `Mathlib/Logic/Function/Basic.lean` (`Function.Injective`, `Function.Surjective`)

### Statement 31: Definition 2.7.5.3
**Status**: INCLUDED
**Explanation**: Monomorphisms and epimorphisms in a category are formalized as `CategoryTheory.Mono` and `CategoryTheory.Epi` typeclasses, encoding the cancellation properties.
**Mathlib references**: `Mathlib/CategoryTheory/EpiMono.lean` (`Mono`, `Epi`)

### Statement 32: Proposition 2.7.5.4
**Status**: INCLUDED
**Explanation**: The equivalence between injectivity and monomorphism, and between surjectivity and epimorphism, in the category of types is proved in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Types/Monomorphisms.lean`, `Mathlib/CategoryTheory/EpiMono.lean`

### Statement 33: Proposition 2.7.5.5
**Status**: INCLUDED
**Explanation**: This is a restatement of Statement 12 (the pullback of a monomorphism is a monomorphism) in the context of function sets. It is proved in general categorical terms.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Mono.lean`

### Statement 34: Definition 2.7.6.3
**Status**: INCLUDED
**Explanation**: While Spivak defines a multiset as a surjective function, Mathlib defines `Multiset` as a quotient of `List` by permutation equivalence, which is a different but equivalent formalization. Mathlib's `Multiset` type captures the same mathematical object.
**Mathlib references**: `Mathlib/Data/Multiset/Defs.lean` (`Multiset`), `Mathlib/Data/Multiset/Basic.lean`

### Statement 35: Definition 2.7.6.7
**Status**: INCLUDED
**Explanation**: A relative set over `B` (a set `E` with a function `pi : E -> B`) corresponds to an object in the over category `Over B`. In the category of types, this is `CategoryTheory.Over`. In pure type theory, it is simply a `Sigma` type or a bundled function.
**Mathlib references**: `Mathlib/CategoryTheory/Comma/Over/Basic.lean` (`Over`), `Mathlib/Data/Sigma/Basic.lean`

### Statement 36: Definition 2.7.6.12
**Status**: INCLUDED
**Explanation**: An `A`-indexed family of sets is simply a function `A -> Type` in Lean, or equivalently a dependent type. This is core to Lean's type theory. Categorically, it corresponds to a functor from a discrete category to Set.
**Mathlib references**: Core Lean (dependent types / `(a : A) -> Set a`), `Mathlib/Data/Sigma/Basic.lean` (for the total space)

---

## Chapter 3: Fundamental Considerations in Set

### Statement 37: Definition 3.1.1.1
**Status**: INCLUDED
**Explanation**: A monoid is formalized as the `Monoid` typeclass in Mathlib, consisting of a type with a binary operation `*`, an identity element `1`, and proofs of associativity and identity laws.
**Mathlib references**: `Mathlib/Algebra/Group/Defs.lean` (`Monoid`)

### Statement 38: Definition 3.1.1.13
**Status**: INCLUDED
**Explanation**: Lists in a type `X` are formalized as `List X` in Lean, which is the built-in inductive type of finite sequences. A list of length `n` with elements from `X` corresponds to a function `Fin n -> X` (or directly `List X`).
**Mathlib references**: Core Lean (`List`), `Mathlib/Data/List/Basic.lean`

### Statement 39: Definition 3.1.1.15
**Status**: INCLUDED
**Explanation**: The free monoid on a set `X` is formalized as `FreeMonoid X` in Mathlib, which is defined as `List X` with concatenation as the monoid operation and the empty list as the identity.
**Mathlib references**: `Mathlib/Algebra/FreeMonoid/Basic.lean` (`FreeMonoid`)

### Statement 40: Definition 3.1.1.17
**Status**: NOT INCLUDED
**Explanation**: While Mathlib has `PresentedMonoid` in `Mathlib/Algebra/PresentedMonoid/Basic.lean`, this is a relatively minimal formalization. The general notion of a monoid presentation with generators and relations as described by Spivak does exist in a basic form, but the treatment is not as developed as the textbook presentation. The file exists but provides limited functionality.
**Mathlib references**: `Mathlib/Algebra/PresentedMonoid/Basic.lean` (partial, minimal formalization)

### Statement 41: Definition 3.1.1.24
**Status**: NOT INCLUDED
**Explanation**: Cyclic monoids are not formalized in Mathlib. While `IsCyclic` exists for groups, there is no `IsCyclic` typeclass or definition for monoids specifically. The notion of a monoid with a single generator is not captured.
**Mathlib references**: None (cyclic groups exist in `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` but not cyclic monoids)

### Statement 42: Definition 3.1.2.1
**Status**: INCLUDED
**Explanation**: A monoid action is formalized via `MulAction` (for multiplicative monoids) and `SMul` in Mathlib. `MulAction M S` provides an action of monoid `M` on type `S` with the identity and compatibility laws.
**Mathlib references**: `Mathlib/GroupTheory/GroupAction/Defs.lean` (`MulAction`), `Mathlib/Algebra/Group/Action/Defs.lean`

### Statement 43: Proposition 3.1.2.11
**Status**: NOT INCLUDED
**Explanation**: The equivalence between a function `delta : Sigma x S -> S` and an action of the free monoid `List(Sigma)` on `S` (essentially the connection between deterministic finite automata and free monoid actions) is not formalized in Mathlib. While DFA is defined in `Mathlib/Computability/DFA.lean`, the explicit equivalence with free monoid actions is not established.
**Mathlib references**: `Mathlib/Computability/DFA.lean` (DFA definition, but not the equivalence with free monoid actions)

### Statement 44: Definition 3.1.4.1
**Status**: INCLUDED
**Explanation**: Monoid homomorphisms are formalized as `MonoidHom` (notation `M ->* M'`) in Mathlib, preserving the identity and multiplication.
**Mathlib references**: `Mathlib/Algebra/Group/Hom/Defs.lean` (`MonoidHom`)

### Statement 45: Proposition 3.1.4.5
**Status**: NOT INCLUDED
**Explanation**: The specific proposition that the only monoid homomorphism from `(Z, 0, +)` to `(N, 0, +)` is the zero map is not explicitly stated in Mathlib. While it could be derived from the fact that `N` has no additive inverses, this specific result is not formalized.
**Mathlib references**: None

### Statement 46: Proposition 3.1.4.9
**Status**: INCLUDED
**Explanation**: The universal property of the free monoid -- that monoid homomorphisms from `FreeMonoid(G)` to `M` correspond bijectively to functions from `G` to `M` -- is formalized via `FreeMonoid.lift` and its equivalence.
**Mathlib references**: `Mathlib/Algebra/FreeMonoid/Basic.lean` (`FreeMonoid.lift`, `FreeMonoid.liftEquiv`)

### Statement 47: Proposition 3.1.4.12
**Status**: INCLUDED
**Explanation**: Pulling back a monoid action along a monoid homomorphism is formalized via `MulAction.compHom`, which takes an action of `M'` on `S` and a homomorphism `f : M -> M'` and produces an action of `M` on `S`.
**Mathlib references**: `Mathlib/GroupTheory/GroupAction/Defs.lean` (`MulAction.compHom`)

### Statement 48: Definition 3.2.1.1
**Status**: INCLUDED
**Explanation**: Groups are formalized as the `Group` typeclass in Mathlib, extending `Monoid` with the requirement that every element has an inverse satisfying `a * a^(-1) = 1` and `a^(-1) * a = 1`.
**Mathlib references**: `Mathlib/Algebra/Group/Defs.lean` (`Group`)

### Statement 49: Proposition 3.2.1.2
**Status**: INCLUDED
**Explanation**: The uniqueness of inverses in a monoid follows from the cancellation properties. In Mathlib, this is implicit in the definition of `Group` (where `inv` is a function, not a relation) and can be derived from `mul_left_cancel` and `mul_right_cancel`.
**Mathlib references**: `Mathlib/Algebra/Group/Defs.lean` (uniqueness is built into the functional definition of `inv`)

### Statement 50: Definition 3.2.1.9
**Status**: INCLUDED
**Explanation**: Group actions are formalized via `MulAction` applied to groups. Since `Group` extends `Monoid`, the `MulAction` typeclass works for groups as well, providing the action laws.
**Mathlib references**: `Mathlib/GroupTheory/GroupAction/Defs.lean` (`MulAction`)

### Statement 51: Definition 3.2.1.12
**Status**: INCLUDED
**Explanation**: The orbit of an element `x` under a group action `G` is formalized as `MulAction.orbit G x`, defined as `{g . x | g : G}`.
**Mathlib references**: `Mathlib/GroupTheory/GroupAction/Basic.lean` (`MulAction.orbit`)

### Statement 52: Definition 3.2.1.16
**Status**: INCLUDED
**Explanation**: Group homomorphisms are formalized as `MonoidHom` applied to groups (since groups extend monoids, a monoid homomorphism between groups is automatically a group homomorphism). There is also `MulEquiv` for group isomorphisms.
**Mathlib references**: `Mathlib/Algebra/Group/Hom/Defs.lean` (`MonoidHom`)

### Statement 53: Definition 3.3.1.1
**Status**: INCLUDED
**Explanation**: A directed graph (quiver) is formalized as `Quiver` in Mathlib, consisting of a type of vertices and, for each pair of vertices, a type of arrows (edges). This corresponds to Spivak's `(V, A, src, tgt)`.
**Mathlib references**: `Mathlib/Combinatorics/Quiver/Basic.lean` (`Quiver`)

### Statement 54: Definition 3.3.2.1
**Status**: INCLUDED
**Explanation**: A path in a graph (quiver) is formalized as `Quiver.Path`, an inductive type representing head-to-tail sequences of arrows. The length of a path can be obtained via `Quiver.Path.length`.
**Mathlib references**: `Mathlib/Combinatorics/Quiver/Path.lean` (`Quiver.Path`)

### Statement 55: Definition 3.3.3.1
**Status**: INCLUDED
**Explanation**: Graph homomorphisms are formalized as `Prefunctor` in Mathlib's quiver library, consisting of a map on vertices and a map on arrows that preserves source and target.
**Mathlib references**: `Mathlib/Combinatorics/Quiver/Prefunctor.lean` (`Prefunctor`)

### Statement 56: Definition 3.3.3.9
**Status**: INCLUDED
**Explanation**: A binary relation on `X` is simply a function `X -> X -> Prop` in Lean, which corresponds to a subset of `X x X`. This is a fundamental concept built into the language. `Rel` is used as a synonym in some places.
**Mathlib references**: Core Lean (binary relations as `X -> X -> Prop`), `Mathlib/Logic/Relation.lean`

### Statement 57: Definition 3.4.1.1
**Status**: INCLUDED
**Explanation**: Preorders are formalized as the `Preorder` typeclass in Mathlib, providing a reflexive and transitive relation `<=`.
**Mathlib references**: `Mathlib/Order/Defs/PartialOrder.lean` (`Preorder`)

### Statement 58: Definition 3.4.1.14
**Status**: NOT INCLUDED
**Explanation**: A clique in a preorder (a subset where every pair of elements is related) is not formalized in Mathlib. While `SimpleGraph.Clique` exists for simple graphs, the notion of a clique in a preorder (where the relation is directed, so every pair satisfies `a <= b`) is different and not formalized.
**Mathlib references**: None (the graph-theoretic `SimpleGraph.Clique` in `Mathlib/Combinatorics/SimpleGraph/Clique.lean` is for undirected graphs, not preorders)

### Statement 59: Definition 3.4.2.1
**Status**: INCLUDED
**Explanation**: The meet (greatest lower bound / infimum) in a preorder is formalized via the `SemilatticeInf` typeclass (or `Inf` for general infima). The meet of two elements is `a \inf b` (or `inf a b`).
**Mathlib references**: `Mathlib/Order/Lattice.lean` (`SemilatticeInf`, `Inf`), `Mathlib/Order/Defs/PartialOrder.lean`

### Statement 60: Definition 3.4.3.1
**Status**: INCLUDED
**Explanation**: The opposite (dual) preorder is formalized as `OrderDual`, denoted `alpha^od`. `OrderDual alpha` has the same carrier as `alpha` but with the reversed order: `a <= b` in the dual iff `b <= a` in the original.
**Mathlib references**: `Mathlib/Order/Defs/PartialOrder.lean` (`OrderDual`), `Mathlib/Order/RelClasses.lean`

### Statement 61: Definition 3.4.4.1
**Status**: INCLUDED
**Explanation**: A morphism of preorders (order-preserving map) is formalized as `OrderHom` (notation `alpha ->o beta`) or via the `Monotone` predicate on functions.
**Mathlib references**: `Mathlib/Order/Hom/Basic.lean` (`OrderHom`), `Mathlib/Order/Monotone/Basic.lean` (`Monotone`)

### Statement 62: Lemma 3.5.2.5
**Status**: INCLUDED
**Explanation**: The property that congruences on a category (or graph) respect composition is built into the definition of congruences in Mathlib. For algebraic structures, `Con` (congruence relation) ensures compatibility with operations. For categories, the quotient category construction in Mathlib ensures path equivalences are compatible with composition.
**Mathlib references**: `Mathlib/Algebra/Group/Congruence/Basic.lean` (`Con`), `Mathlib/CategoryTheory/Quotient.lean`

### Statement 63: Definition 3.5.2.6
**Status**: NOT INCLUDED
**Explanation**: Database schemas as graph-with-congruence pairs are a concept specific to Spivak's applied category theory framework. This is not formalized in Mathlib, which focuses on pure mathematics rather than database theory applications.
**Mathlib references**: None

### Statement 64: Definition 3.5.3.1
**Status**: NOT INCLUDED
**Explanation**: Instances on database schemas (functors from a schema to Set) are part of Spivak's applied category theory framework. While the underlying concept of a functor to Set is thoroughly formalized in Mathlib, the specific database-theoretic framing is not present.
**Mathlib references**: None (the underlying functor concept is in `Mathlib/CategoryTheory/Functor/Basic.lean`)

---

## Chapter 4: Categories and Functors, without Admitting It

### Statement 65: Definition 4.1.1.1
**Status**: INCLUDED
**Explanation**: The definition of a category is formalized as `CategoryTheory.Category` in Mathlib, consisting of objects, morphism sets, identity morphisms, composition, and the identity and associativity laws.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Basic.lean` (`Category`)

### Statement 66: Definition 4.1.1.17
**Status**: INCLUDED
**Explanation**: Isomorphisms in a category are formalized as `CategoryTheory.Iso`, consisting of a morphism `hom : X -> Y` and an inverse `inv : Y -> X` with `hom >>> inv = id` and `inv >>> hom = id`.
**Mathlib references**: `Mathlib/CategoryTheory/Iso.lean` (`Iso`)

### Statement 67: Lemma 4.1.1.21
**Status**: INCLUDED
**Explanation**: The fact that isomorphism is an equivalence relation on objects is captured by `Iso.refl`, `Iso.symm`, and `Iso.trans`, and the `IsEquiv` instance for the isomorphism relation.
**Mathlib references**: `Mathlib/CategoryTheory/Iso.lean` (`Iso.refl`, `Iso.symm`, `Iso.trans`), `Mathlib/CategoryTheory/IsomorphismClasses.lean`

### Statement 68: Definition 4.1.2.1
**Status**: INCLUDED
**Explanation**: Functors between categories are formalized as `CategoryTheory.Functor`, consisting of an object map and a morphism map preserving identity and composition.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Basic.lean` (`Functor`)

### Statement 69: Proposition 4.1.2.8
**Status**: INCLUDED
**Explanation**: Preorders can be viewed as categories (thin categories), and the forgetful functor from preorders to quivers (graphs) is implicit in Mathlib's treatment. Every preorder gives rise to a category, and every category has an underlying quiver.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Preorder.lean` (preorders as categories), `Mathlib/Combinatorics/Quiver/Basic.lean` (underlying quiver)

### Statement 70: Proposition 4.1.2.28
**Status**: INCLUDED
**Explanation**: The category `Cat` of small categories and functors is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Cat.lean` (`Cat`)

### Statement 71: Theorem 4.2.1.3
**Status**: INCLUDED
**Explanation**: Monoids as one-object categories is formalized via `SingleObj`, which creates a category with a single object whose endomorphisms form the given monoid. The equivalence between `Mon` and one-object categories is established.
**Mathlib references**: `Mathlib/CategoryTheory/SingleObj.lean` (`SingleObj`)

### Statement 72: Theorem 4.2.1.6
**Status**: INCLUDED
**Explanation**: Groups as one-object groupoids is also handled by `SingleObj`. When a group is viewed as a one-object category via `SingleObj`, every morphism is automatically an isomorphism, making it a groupoid.
**Mathlib references**: `Mathlib/CategoryTheory/SingleObj.lean` (`SingleObj`), `Mathlib/CategoryTheory/Groupoid.lean`

### Statement 73: Proposition 4.2.1.17
**Status**: INCLUDED
**Explanation**: Preorders as thin categories (categories where each hom-set has at most one element) is formalized by the instance that makes any `Preorder` into a `Category`. The thinness property is captured by `Subsingleton (a \hom b)`.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Preorder.lean`

### Statement 74: Definition 4.2.3.7
**Status**: INCLUDED
**Explanation**: A groupoid is a category in which every morphism is an isomorphism. This is formalized as the `Groupoid` typeclass in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Groupoid.lean` (`Groupoid`)

### Statement 75: Definition 4.3.1.2
**Status**: INCLUDED
**Explanation**: Natural transformations between functors are formalized as `CategoryTheory.NatTrans`, consisting of component morphisms satisfying the naturality condition.
**Mathlib references**: `Mathlib/CategoryTheory/NatTrans.lean` (`NatTrans`)

### Statement 76: Lemma 4.3.1.4
**Status**: NOT INCLUDED
**Explanation**: The lemma that naturality only needs to be checked on generators is a meta-level observation about presentations of categories. This is not formalized in Mathlib as a general theorem, as Mathlib's treatment of natural transformations requires checking naturality for all morphisms.
**Mathlib references**: None

### Statement 77: Proposition 4.3.2.2
**Status**: INCLUDED
**Explanation**: The functor category `Fun(C, D)` is formalized in Mathlib, with functors as objects and natural transformations as morphisms.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Category.lean` (functor category)

### Statement 78: Notation 4.3.2.3
**Status**: INCLUDED
**Explanation**: The notation `D^C` for the functor category is available in Mathlib's functor category formalization, though the primary notation used is `C \func D` or `Functor C D`.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Category.lean`

### Statement 79: Lemma 4.3.2.12
**Status**: INCLUDED
**Explanation**: A natural transformation is a natural isomorphism if and only if each component is an isomorphism. This is formalized via `NatIso` and the characterization that a natural transformation is an iso in the functor category iff it is componentwise an iso.
**Mathlib references**: `Mathlib/CategoryTheory/NatIso.lean` (`NatIso`, `isIso_of_isIso_app`)

### Statement 80: Definition 4.3.2.16
**Status**: INCLUDED
**Explanation**: Whiskering of natural transformations (pre-composition and post-composition with functors) is formalized in Mathlib as `whiskerLeft` and `whiskerRight`.
**Mathlib references**: `Mathlib/CategoryTheory/Whiskering.lean` (`whiskerLeft`, `whiskerRight`)

### Statement 81: Definition 4.3.2.17
**Status**: INCLUDED
**Explanation**: Horizontal composition of natural transformations is formalized as `NatTrans.hcomp` in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/NatTrans.lean` (`NatTrans.hcomp`), `Mathlib/CategoryTheory/Whiskering.lean`

### Statement 82: Definition 4.3.3.1
**Status**: INCLUDED
**Explanation**: `C-Set = Fun(C, Set)` is the presheaf category, formalized as the functor category from `C` to `Type`. In Mathlib, this is simply the functor category `C \func Type`.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Category.lean`, `Mathlib/CategoryTheory/Types.lean`

### Statement 83: Definition 4.3.4.1
**Status**: INCLUDED
**Explanation**: Equivalence of categories is formalized as `CategoryTheory.Equivalence`, consisting of functors `F` and `G` with natural isomorphisms `F.comp G \cong Id` and `G.comp F \cong Id`.
**Mathlib references**: `Mathlib/CategoryTheory/Equivalence.lean` (`Equivalence`)

### Statement 84: Definition 4.3.4.8
**Status**: INCLUDED
**Explanation**: The skeleton of a category (choosing one representative from each isomorphism class) is formalized in Mathlib. The `Skeleton` construction picks one object from each isomorphism class.
**Mathlib references**: `Mathlib/CategoryTheory/Skeletal.lean`, `Mathlib/CategoryTheory/Limits/Skeleton.lean`

### Statement 85: Proposition 4.3.4.9
**Status**: INCLUDED
**Explanation**: The equivalence between a category and its skeleton is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Skeletal.lean` (skeleton equivalence)

### Statement 86: Definition 4.3.4.10
**Status**: INCLUDED
**Explanation**: A skeletal category (one where isomorphic objects are equal) is formalized via the `Skeletal` predicate in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Skeletal.lean` (`Skeletal`)

### Statement 87: Definition 4.3.4.12
**Status**: INCLUDED
**Explanation**: Full, faithful, and fully faithful functors are formalized in Mathlib. `Functor.Full` means the hom-map is surjective, `Functor.Faithful` means injective, and `Functor.FullyFaithful` combines both.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/FullyFaithful.lean` (`Functor.Full`, `Functor.Faithful`, `Functor.FullyFaithful`)

### Statement 88: Proposition 4.3.4.15
**Status**: INCLUDED
**Explanation**: An equivalence of categories induces a fully faithful functor. This is proved in Mathlib as part of the theory of equivalences.
**Mathlib references**: `Mathlib/CategoryTheory/Equivalence.lean` (equivalence implies fully faithful)

### Statement 89: Definition 4.4.1.2
**Status**: NOT INCLUDED
**Explanation**: Schema morphisms (in the database-theoretic sense of Spivak) are not formalized in Mathlib. This is an applied category theory concept specific to Spivak's framework.
**Mathlib references**: None

### Statement 90: Definition 4.5.1.8
**Status**: INCLUDED
**Explanation**: Products in a category (with the universal property) are formalized via `CategoryTheory.Limits.HasBinaryProducts` and `CategoryTheory.Limits.prod`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean` (`HasBinaryProducts`, `prod`)

### Statement 91: Definition 4.5.1.23
**Status**: INCLUDED
**Explanation**: Coproducts in a category are formalized via `CategoryTheory.Limits.HasBinaryCoproducts` and `CategoryTheory.Limits.coprod`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean` (`HasBinaryCoproducts`, `coprod`)

### Statement 92: Definition 4.5.2.1
**Status**: INCLUDED
**Explanation**: A diagram in a category is simply a functor `d : I -> C` from an indexing category `I` to `C`. This is the standard definition used throughout Mathlib's limits library.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Basic.lean` (`Functor`), `Mathlib/CategoryTheory/Limits/HasLimits.lean`

### Statement 93: Definition 4.5.2.6
**Status**: INCLUDED
**Explanation**: The left cone on a diagram (adding a cone point with morphisms to each object in the diagram) is formalized as `CategoryTheory.Limits.Cone`, which consists of a cone point and a natural transformation from the constant functor to the diagram.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Cones.lean` (`Cone`)

### Statement 94: Definition 4.5.2.11
**Status**: INCLUDED
**Explanation**: The right cone (cocone) on a diagram is formalized as `CategoryTheory.Limits.Cocone`, with a cocone point and a natural transformation from the diagram to the constant functor.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Cones.lean` (`Cocone`)

### Statement 95: Definition 4.5.3.2
**Status**: INCLUDED
**Explanation**: Initial and terminal objects are formalized as `CategoryTheory.Limits.IsInitial` and `CategoryTheory.Limits.IsTerminal`.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Terminal.lean` (`IsInitial`, `IsTerminal`), `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`

### Statement 96: Proposition 4.5.3.4
**Status**: INCLUDED
**Explanation**: Initial objects (resp. terminal objects) are unique up to unique isomorphism. This follows from the general fact that universal objects are unique up to unique isomorphism, formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/Shapes/Terminal.lean` (`IsInitial.uniqueUpToIso`, `IsTerminal.uniqueUpToIso`)

### Statement 97: Definition 4.5.3.19
**Status**: INCLUDED
**Explanation**: The limit of a diagram `X : I -> C` as a terminal object in the slice category (category of cones) is the standard definition used in Mathlib. A limit cone is an `IsLimit` cone, meaning it is terminal among all cones.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/IsLimit.lean` (`IsLimit`), `Mathlib/CategoryTheory/Limits/HasLimits.lean`

### Statement 98: Definition 4.5.3.26
**Status**: INCLUDED
**Explanation**: The colimit as an initial object in the coslice category (category of cocones) is formalized via `IsColimit`, meaning it is initial among all cocones.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/IsLimit.lean` (`IsColimit`), `Mathlib/CategoryTheory/Limits/HasLimits.lean`

### Statement 99: Definition 4.6.1.1
**Status**: INCLUDED
**Explanation**: The opposite category `C^op` is formalized in Mathlib. Objects are the same but morphisms are reversed.
**Mathlib references**: `Mathlib/CategoryTheory/Opposites.lean` (`Category` instance on `C^op`)

### Statement 100: Lemma 4.6.1.4
**Status**: INCLUDED
**Explanation**: The identity `(C^op)^op = C` and the equivalence `Fun(C, D) = Fun(C^op, D^op)` are formalized in Mathlib. `opOp` provides the isomorphism `(C^op)^op \cong C`, and functors between opposite categories are handled.
**Mathlib references**: `Mathlib/CategoryTheory/Opposites.lean` (`opOp`, `unop_op`)

### Statement 101: Definition 4.6.2.1
**Status**: INCLUDED
**Explanation**: The category of elements (Grothendieck construction) for a functor `J : C -> Set` is formalized in Mathlib. Objects are pairs `(c, x)` with `c` an object and `x` in `J(c)`.
**Mathlib references**: `Mathlib/CategoryTheory/Elements.lean` (`CategoryOfElements`), `Mathlib/CategoryTheory/Grothendieck.lean`

### Statement 102: Definition 4.6.3.1
**Status**: INCLUDED
**Explanation**: The full subcategory spanned by a set of objects is formalized in Mathlib. Given a predicate on objects, the full subcategory includes all morphisms between objects satisfying the predicate.
**Mathlib references**: `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean` (`FullSubcategory`), `Mathlib/CategoryTheory/Limits/FullSubcategory.lean`

### Statement 103: Definition 4.6.4.1
**Status**: INCLUDED
**Explanation**: The comma category `(F downarrow G)` for functors `F : A -> C` and `G : B -> C` is formalized in Mathlib. Objects are triples `(a, b, f)` with `f : F(a) -> G(b)`.
**Mathlib references**: `Mathlib/CategoryTheory/Comma/Basic.lean` (`Comma`)

### Statement 104: Proposition 4.6.5.1
**Status**: INCLUDED
**Explanation**: The arithmetic identities for small categories (products, coproducts, exponentials) are parallel to those for sets and are established through the cartesian closed structure of `Cat`. Many of these identities are formalized.
**Mathlib references**: `Mathlib/CategoryTheory/Category/Cat.lean`, `Mathlib/CategoryTheory/Category/Cat/CartesianClosed.lean`

---

## Chapter 5: Categories at Work

### Statement 105: Definition 5.1.1.1
**Status**: INCLUDED
**Explanation**: An adjunction `L \dashv R` between functors is formalized as `CategoryTheory.Adjunction`, providing the natural isomorphism `Hom(L(B), A) \cong Hom(B, R(A))`.
**Mathlib references**: `Mathlib/CategoryTheory/Adjunction/Basic.lean` (`Adjunction`)

### Statement 106: Proposition 5.1.1.2
**Status**: INCLUDED
**Explanation**: The free-forgetful adjunction between `MonCat` and `Type` (free monoid functor left adjoint to the forgetful functor) is formalized in Mathlib.
**Mathlib references**: `Mathlib/Algebra/Category/MonCat/Adjunctions.lean`

### Statement 107: Proposition 5.1.1.11
**Status**: INCLUDED
**Explanation**: The uniqueness of adjoints (if both `G` and `G'` are right adjoint to `F`, then `G \cong G'`) is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Adjunction/Unique.lean` (`rightAdjointUniq`)

### Statement 108: Proposition 5.1.3.1
**Status**: INCLUDED
**Explanation**: Left adjoints preserve colimits and right adjoints preserve limits. This is a fundamental theorem of category theory, formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Adjunction/Limits.lean` (`Adjunction.isColimitOfPreserves`, etc.)

### Statement 109: Notation 5.1.4.1
**Status**: INCLUDED
**Explanation**: The notation `C-Set = Fun(C, Set)` for the presheaf category is just the functor category from `C` to `Type`, which is standard in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Functor/Category.lean`

### Statement 110: Proposition 5.2.1.1
**Status**: INCLUDED
**Explanation**: The functor category `Fun(C, Set)` has all limits and colimits (computed pointwise). This is formalized in Mathlib: limits and colimits in functor categories are computed pointwise.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/FunctorCategory.lean`, `Mathlib/CategoryTheory/Limits/Types.lean`

### Statement 111: Definition 5.2.1.4
**Status**: INCLUDED
**Explanation**: This is the same definition as Statement 31: monomorphisms and epimorphisms in a category. `Mono` and `Epi` typeclasses.
**Mathlib references**: `Mathlib/CategoryTheory/EpiMono.lean` (`Mono`, `Epi`)

### Statement 112: Proposition 5.2.1.5
**Status**: INCLUDED
**Explanation**: A natural transformation in `Fun(C, Set)` is a monomorphism (resp. epimorphism) iff each component is injective (resp. surjective). This is proved in Mathlib for functor categories.
**Mathlib references**: `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean`, `Mathlib/CategoryTheory/Functor/EpiMono.lean`

### Statement 113: Definition 5.2.1.7
**Status**: INCLUDED
**Explanation**: Representable functors (`Hom(c, -)`) are formalized in Mathlib. The Yoneda embedding sends each object `c` to the representable functor `Hom(c, -)`.
**Mathlib references**: `Mathlib/CategoryTheory/Yoneda.lean` (`yoneda`, representable functors)

### Statement 114: Lemma 5.2.1.13
**Status**: INCLUDED
**Explanation**: Yoneda's lemma (Part 1): `Hom(Y_c, I) \cong I(c)` for any functor `I : C -> Set`. This is one of the most important results in category theory, formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Yoneda.lean` (`yonedaEquiv`)

### Statement 115: Lemma 5.2.1.19
**Status**: INCLUDED
**Explanation**: Yoneda's lemma (Part 2): The Yoneda embedding `Y : C^op -> C-Set` is fully faithful. This is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Yoneda.lean` (`yoneda.fullyFaithful`, `Yoneda.fullyFaithful`)

### Statement 116: Definition 5.2.1.23
**Status**: NOT INCLUDED
**Explanation**: The subobject classifier for presheaf categories `C-Set` is not fully formalized in Mathlib. While Mathlib has the notion of a subobject classifier in the topos-theoretic sense (`CategoryTheory.Topos.Classifier`), the explicit construction for presheaf categories with the sieve-based definition is not complete.
**Mathlib references**: `Mathlib/CategoryTheory/Topos/Classifier.lean` (general framework, but not the specific presheaf construction)

### Statement 117: Definition 5.2.3.2
**Status**: INCLUDED
**Explanation**: A presheaf on a topological space `X` is a functor `Open(X)^op -> Set`. This is formalized in Mathlib as `TopCat.Presheaf` or more generally using the opens of a topological space.
**Mathlib references**: `Mathlib/Topology/Sheaves/Presheaf.lean` (`TopCat.Presheaf`)

### Statement 118: Definition 5.2.3.5
**Status**: INCLUDED
**Explanation**: A sheaf on a topological space is a presheaf satisfying the sheaf condition (compatible local sections glue uniquely). This is formalized in Mathlib.
**Mathlib references**: `Mathlib/Topology/Sheaves/Sheaf.lean` (`TopCat.Sheaf`), `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean`

### Statement 119: Definition 5.3.2.1
**Status**: INCLUDED
**Explanation**: A monad on a category consists of a functor `T`, a unit `eta : Id -> T`, and a multiplication `mu : T . T -> T`, satisfying the monad laws. This is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Monad/Basic.lean` (`Monad`)

### Statement 120: Definition 5.3.3.1
**Status**: INCLUDED
**Explanation**: The Kleisli category of a monad `T` is formalized in Mathlib. Objects are the same as the base category, with `Hom(X, Y) = Hom(X, T(Y))`.
**Mathlib references**: `Mathlib/CategoryTheory/Monad/Kleisli.lean` (`Kleisli`)

### Statement 121: Definition 5.3.5.1
**Status**: INCLUDED
**Explanation**: The unit and counit of an adjunction are formalized in Mathlib as `Adjunction.unit` (a natural transformation `Id -> R . L`) and `Adjunction.counit` (a natural transformation `L . R -> Id`).
**Mathlib references**: `Mathlib/CategoryTheory/Adjunction/Basic.lean` (`Adjunction.unit`, `Adjunction.counit`)

### Statement 122: Proposition 5.3.5.3
**Status**: INCLUDED
**Explanation**: The Kleisli adjunction recovers the monad: given a monad `T`, the Kleisli category gives an adjunction whose associated monad is `T`. This is formalized in Mathlib.
**Mathlib references**: `Mathlib/CategoryTheory/Monad/Kleisli.lean`, `Mathlib/CategoryTheory/Monad/Adjunction.lean`

### Statement 123: Definition 5.4.1.1
**Status**: NOT INCLUDED
**Explanation**: Operads are not formalized in Mathlib. While there is some related infrastructure for monoidal categories and multicategories, the explicit notion of an operad (with sets of operations of each arity, composition maps, and the operad axioms) is not present.
**Mathlib references**: None

### Statement 124: Definition 5.4.1.8
**Status**: NOT INCLUDED
**Explanation**: Operad functors (morphisms of operads) are not formalized in Mathlib, since operads themselves are not formalized.
**Mathlib references**: None

### Statement 125: Definition 5.4.1.10
**Status**: NOT INCLUDED
**Explanation**: Operad algebras (operad functors to Sets) are not formalized in Mathlib, since operads themselves are not formalized.
**Mathlib references**: None

### Statement 126: Proposition 5.2.1.21
**Status**: INCLUDED
**Explanation**: The distributive law `(a + b) * c = a * c + b * c` for natural numbers can be proved using category-theoretic reasoning via Yoneda's lemma, but it is also directly available as `Nat.left_distrib` or `mul_add` in Mathlib. The category-theoretic proof path is supported by the Yoneda infrastructure.
**Mathlib references**: `Mathlib/Algebra/Group/Defs.lean` (`left_distrib`), `Mathlib/CategoryTheory/Yoneda.lean` (for the categorical proof approach)

---

## Summary

- **Total statements:** 126
- **INCLUDED in Mathlib:** 110
- **NOT INCLUDED in Mathlib:** 16
- **Coverage:** ~87%

**Statements NOT INCLUDED:**
| # | Statement | Reason |
|---|-----------|--------|
| 26 | Downward-closed subsets / abstract simplicial complex | Not formalized in the combinatorial sense |
| 27 | Subobject classifier for Set | Not formalized as explicit 2-element set construction |
| 28 | P(B) = Hom(B, Omega) | Not formalized with explicit subobject classifier |
| 40 | Monoid presentation | Only minimal formalization exists |
| 41 | Cyclic monoid | Only cyclic groups exist, not monoids |
| 43 | FSM as free monoid action | DFA exists but equivalence not established |
| 45 | Unique hom Z -> N | Specific result not formalized |
| 58 | Clique in a preorder | Graph cliques exist but not preorder cliques |
| 63 | Database schema | Applied CT concept not in Mathlib |
| 64 | Instance on a schema | Applied CT concept not in Mathlib |
| 76 | Naturality from generators | Meta-level observation not formalized |
| 89 | Schema morphism | Applied CT concept not in Mathlib |
| 116 | Subobject classifier for C-Set | General framework exists but not specific presheaf construction |
| 123 | Operad | Not formalized |
| 124 | Operad functor | Not formalized |
| 125 | Operad algebra | Not formalized |
