# Short Assessment: Mathlib Coverage

## Source: Category Theory for Scientists (David I. Spivak, MIT)

Each statement is marked as:
- **INCLUDED**: The statement (or its essential content) is formalized in Mathlib.
- **NOT INCLUDED**: The statement is not formalized in Mathlib, or only tangentially related material exists.

---

## Chapter 2: The Category of Sets

| # | Statement | Status |
|---|-----------|--------|
| 1 | Notation 2.1.1.1 (empty set, naturals) | INCLUDED |
| 2 | Lemma 2.1.2.12 (isomorphism is equivalence relation) | INCLUDED |
| 3 | Definition 2.1.2.16 (cardinality of finite sets) | INCLUDED |
| 4 | Lemma 2.1.2.18 (isomorphic finite sets have same cardinality) | INCLUDED |
| 5 | Definition 2.4.1.1 (product of sets) | INCLUDED |
| 6 | Lemma 2.4.1.10 (universal property for product) | INCLUDED |
| 7 | Definition 2.4.2.1 (coproduct of sets) | INCLUDED |
| 8 | Lemma 2.4.2.7 (universal property for coproduct) | INCLUDED |
| 9 | Definition 2.5.1.1 (pullback / fiber product) | INCLUDED |
| 10 | Definition 2.5.1.12 (preimage) | INCLUDED |
| 11 | Lemma 2.5.1.14 (universal property for pullback) | INCLUDED |
| 12 | Proposition 2.5.1.17 (pullback of mono is mono) | INCLUDED |
| 13 | Definition 2.5.2.1 (span) | INCLUDED |
| 14 | Definition 2.5.2.3 (composite span via fiber product) | INCLUDED |
| 15 | Definition 2.5.3.1 (equalizer) | INCLUDED |
| 16 | Definition 2.6.1.1 (equivalence relation) | INCLUDED |
| 17 | Lemma 2.6.1.7 (generating equivalence relations) | INCLUDED |
| 18 | Definition 2.6.2.1 (pushout) | INCLUDED |
| 19 | Lemma 2.6.2.8 (universal property for pushout) | INCLUDED |
| 20 | Definition 2.6.3.1 (coequalizer) | INCLUDED |
| 21 | Definition 2.7.1.1 (retract section and projection) | INCLUDED |
| 22 | Notation 2.7.2.1 (function set B^A) | INCLUDED |
| 23 | Proposition 2.7.2.3 (currying) | INCLUDED |
| 24 | Proposition 2.7.3.1 (arithmetic of sets) | INCLUDED |
| 25 | Definition 2.7.4.1 (power set) | INCLUDED |
| 26 | Definition 2.7.4.4 (downward-closed, abstract simplicial complex) | NOT INCLUDED |
| 27 | Definition 2.7.4.9 (subobject classifier for Set) | NOT INCLUDED |
| 28 | Proposition 2.7.4.10 (P(B) ≅ Hom(B, Ω)) | NOT INCLUDED |
| 29 | Definition 2.7.4.11 (characteristic function) | INCLUDED |
| 30 | Definition 2.7.5.1 (surjective, injective) | INCLUDED |
| 31 | Definition 2.7.5.3 (monomorphism, epimorphism in Set) | INCLUDED |
| 32 | Proposition 2.7.5.4 (injective ↔ mono, surjective ↔ epi) | INCLUDED |
| 33 | Proposition 2.7.5.5 (pullback of mono is mono) | INCLUDED |
| 34 | Definition 2.7.6.3 (multiset) | INCLUDED |
| 35 | Definition 2.7.6.7 (relative set / set over B) | INCLUDED |
| 36 | Definition 2.7.6.12 (A-indexed set) | INCLUDED |

## Chapter 3: Fundamental Considerations in Set

| # | Statement | Status |
|---|-----------|--------|
| 37 | Definition 3.1.1.1 (monoid) | INCLUDED |
| 38 | Definition 3.1.1.13 (list) | INCLUDED |
| 39 | Definition 3.1.1.15 (free monoid) | INCLUDED |
| 40 | Definition 3.1.1.17 (monoid presentation) | NOT INCLUDED |
| 41 | Definition 3.1.1.24 (cyclic monoid) | NOT INCLUDED |
| 42 | Definition 3.1.2.1 (monoid action) | INCLUDED |
| 43 | Proposition 3.1.2.11 (FSM as free monoid action) | NOT INCLUDED |
| 44 | Definition 3.1.4.1 (monoid homomorphism) | INCLUDED |
| 45 | Proposition 3.1.4.5 (unique hom ℤ → ℕ) | NOT INCLUDED |
| 46 | Proposition 3.1.4.9 (free monoid universal property) | INCLUDED |
| 47 | Proposition 3.1.4.12 (pullback of monoid action) | INCLUDED |
| 48 | Definition 3.2.1.1 (group) | INCLUDED |
| 49 | Proposition 3.2.1.2 (inverse is unique) | INCLUDED |
| 50 | Definition 3.2.1.9 (group action) | INCLUDED |
| 51 | Definition 3.2.1.12 (orbit) | INCLUDED |
| 52 | Definition 3.2.1.16 (group homomorphism) | INCLUDED |
| 53 | Definition 3.3.1.1 (graph) | INCLUDED |
| 54 | Definition 3.3.2.1 (path in a graph) | INCLUDED |
| 55 | Definition 3.3.3.1 (graph homomorphism) | INCLUDED |
| 56 | Definition 3.3.3.9 (binary relation) | INCLUDED |
| 57 | Definition 3.4.1.1 (preorder) | INCLUDED |
| 58 | Definition 3.4.1.14 (clique in a preorder) | NOT INCLUDED |
| 59 | Definition 3.4.2.1 (meet in a preorder) | INCLUDED |
| 60 | Definition 3.4.3.1 (opposite preorder) | INCLUDED |
| 61 | Definition 3.4.4.1 (morphism of preorders) | INCLUDED |
| 62 | Lemma 3.5.2.5 (congruence respects composition) | INCLUDED |
| 63 | Definition 3.5.2.6 (database schema) | NOT INCLUDED |
| 64 | Definition 3.5.3.1 (instance on a schema) | NOT INCLUDED |

## Chapter 4: Categories and Functors, without Admitting It

| # | Statement | Status |
|---|-----------|--------|
| 65 | Definition 4.1.1.1 (category) | INCLUDED |
| 66 | Definition 4.1.1.17 (isomorphism in a category) | INCLUDED |
| 67 | Lemma 4.1.1.21 (isomorphism is equivalence relation) | INCLUDED |
| 68 | Definition 4.1.2.1 (functor) | INCLUDED |
| 69 | Proposition 4.1.2.8 (functor PrO → Grph) | INCLUDED |
| 70 | Proposition 4.1.2.28 (category Cat) | INCLUDED |
| 71 | Theorem 4.2.1.3 (monoids as one-object categories) | INCLUDED |
| 72 | Theorem 4.2.1.6 (groups as one-object groupoids) | INCLUDED |
| 73 | Proposition 4.2.1.17 (preorders as thin categories) | INCLUDED |
| 74 | Definition 4.2.3.7 (groupoid) | INCLUDED |
| 75 | Definition 4.3.1.2 (natural transformation) | INCLUDED |
| 76 | Lemma 4.3.1.4 (naturality from generators) | NOT INCLUDED |
| 77 | Proposition 4.3.2.2 (functor category Fun(C, D)) | INCLUDED |
| 78 | Notation 4.3.2.3 (D^C notation) | INCLUDED |
| 79 | Lemma 4.3.2.12 (natural isomorphism characterization) | INCLUDED |
| 80 | Definition 4.3.2.16 (whiskering) | INCLUDED |
| 81 | Definition 4.3.2.17 (horizontal composition) | INCLUDED |
| 82 | Definition 4.3.3.1 (C-Set = Fun(C, Set)) | INCLUDED |
| 83 | Definition 4.3.4.1 (equivalence of categories) | INCLUDED |
| 84 | Definition 4.3.4.8 (skeleton / election) | INCLUDED |
| 85 | Proposition 4.3.4.9 (skeleton equivalent to original) | INCLUDED |
| 86 | Definition 4.3.4.10 (skeleton definition) | INCLUDED |
| 87 | Definition 4.3.4.12 (full and faithful functors) | INCLUDED |
| 88 | Proposition 4.3.4.15 (equivalence implies fully faithful) | INCLUDED |
| 89 | Definition 4.4.1.2 (schema morphism) | NOT INCLUDED |
| 90 | Definition 4.5.1.8 (product in a category) | INCLUDED |
| 91 | Definition 4.5.1.23 (coproduct in a category) | INCLUDED |
| 92 | Definition 4.5.2.1 (diagram in a category) | INCLUDED |
| 93 | Definition 4.5.2.6 (left cone) | INCLUDED |
| 94 | Definition 4.5.2.11 (right cone) | INCLUDED |
| 95 | Definition 4.5.3.2 (initial and terminal objects) | INCLUDED |
| 96 | Proposition 4.5.3.4 (initial/terminal objects unique up to iso) | INCLUDED |
| 97 | Definition 4.5.3.19 (limit as terminal object in slice) | INCLUDED |
| 98 | Definition 4.5.3.26 (colimit as initial object in coslice) | INCLUDED |
| 99 | Definition 4.6.1.1 (opposite category) | INCLUDED |
| 100 | Lemma 4.6.1.4 ((C^op)^op = C, Fun(C,D) ≅ Fun(C^op,D^op)) | INCLUDED |
| 101 | Definition 4.6.2.1 (category of elements / Grothendieck) | INCLUDED |
| 102 | Definition 4.6.3.1 (full subcategory) | INCLUDED |
| 103 | Definition 4.6.4.1 (comma category) | INCLUDED |
| 104 | Proposition 4.6.5.1 (arithmetic of categories) | INCLUDED |

## Chapter 5: Categories at Work

| # | Statement | Status |
|---|-----------|--------|
| 105 | Definition 5.1.1.1 (adjunction) | INCLUDED |
| 106 | Proposition 5.1.1.2 (free-forgetful adjunction Set ⊣ Mon) | INCLUDED |
| 107 | Proposition 5.1.1.11 (adjoint uniqueness) | INCLUDED |
| 108 | Proposition 5.1.3.1 (left adjoints preserve colimits) | INCLUDED |
| 109 | Notation 5.1.4.1 (C-Set = Fun(C, Set)) | INCLUDED |
| 110 | Proposition 5.2.1.1 (C-Set closed under (co)limits) | INCLUDED |
| 111 | Definition 5.2.1.4 (monomorphism, epimorphism) | INCLUDED |
| 112 | Proposition 5.2.1.5 (mono/epi in C-Set is pointwise) | INCLUDED |
| 113 | Definition 5.2.1.7 (representable functor) | INCLUDED |
| 114 | Lemma 5.2.1.13 (Yoneda's lemma, part 1) | INCLUDED |
| 115 | Lemma 5.2.1.19 (Yoneda's lemma, part 2: Yoneda embedding fully faithful) | INCLUDED |
| 116 | Definition 5.2.1.23 (subobject classifier for C-Set) | NOT INCLUDED |
| 117 | Definition 5.2.3.2 (presheaf) | INCLUDED |
| 118 | Definition 5.2.3.5 (sheaf) | INCLUDED |
| 119 | Definition 5.3.2.1 (monad) | INCLUDED |
| 120 | Definition 5.3.3.1 (Kleisli category) | INCLUDED |
| 121 | Definition 5.3.5.1 (unit and counit of adjunction) | INCLUDED |
| 122 | Proposition 5.3.5.3 (Kleisli adjunction recovers monad) | INCLUDED |
| 123 | Definition 5.4.1.1 (operad) | NOT INCLUDED |
| 124 | Definition 5.4.1.8 (operad functor) | NOT INCLUDED |
| 125 | Definition 5.4.1.10 (operad algebra) | NOT INCLUDED |
| 126 | Proposition 5.2.1.21 (distributive law via Yoneda) | INCLUDED |

---

## Summary

- **Total statements:** 126
- **INCLUDED in Mathlib:** 107
- **NOT INCLUDED in Mathlib:** 19
- **Coverage:** ~85%
