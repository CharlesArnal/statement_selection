# Detailed Assessment: Simplicity Theory Statements in Mathlib

## Summary

This textbook consists of OCR'd handwritten lecture notes on simplicity theory in model theory, following Wagner's book "Simple Theories" and the Kim-Pillay paper "From Stability to Simplicity." The material is highly specialized, covering dividing, forking, independence, Morley sequences, Lascar strong types, SU-rank, canonical bases, hyperimaginaries, and the Kim-Pillay characterization theorem.

Mathlib's model theory library (at `Mathlib/ModelTheory/`) contains foundational material: first-order languages, structures, semantics, syntax, satisfiability, the compactness theorem, complete theories, type spaces (with topology), definability, elementary maps/substructures, ultraproducts, Fraisse limits, and some algebraic applications. However, it does **not** contain any of the following concepts that are central to this textbook:
- Dividing / forking
- Independence (non-forking independence)
- Indiscernible sequences
- Morley sequences
- Simple theories
- Stable theories (as a model-theoretic property)
- SU-rank / D-rank
- Lascar strong types
- Canonical bases
- Hyperimaginaries
- Amalgamation bases
- The Independence Theorem
- The Kim-Pillay theorem

As a result, essentially **all** statements in this textbook are non-included in Mathlib. The only partial overlap is that Mathlib has the notion of complete types (`CompleteType`) and the compactness theorem, which appear as background framework in these notes.

---

## Statement-by-Statement Assessment

### 1. Fact 1 (Universal Domain Fact)
**Status:** non-included
**Explanation:** This fact concerns universal domains (monster models) in the positive model theory framework. Mathlib does not formalize monster models, universal domains, or the positive fragment framework used here. The closest Mathlib has is the general compactness theorem in `Mathlib/ModelTheory/Satisfiability.lean`, but the universal domain construction and its properties are absent.

### 2. Remark 1 (Existential Closure of Universal Domain)
**Status:** non-included
**Explanation:** This remark states that if U is a universal domain for Delta, then it is also a universal domain for the existential closure of Delta. Mathlib has no formalization of universal domains or positive fragments.

### 3. Fact 2 (S_n(T) as Maximal Consistent Types / Compact Topology)
**Status:** partially included
**Explanation:** Mathlib defines `CompleteType` in `Mathlib/ModelTheory/Types.lean` as the space of complete types over a theory, and `Mathlib/ModelTheory/Topology/Types.lean` defines the Stone topology on it and proves compactness. The identification of S_n(T) with maximal consistent sets is implicit in the definition. However, the specific characterization via automorphism orbits of a monster model (S_n(T) = U^n/Aut(U)) is not in Mathlib. This is the only statement with any partial overlap.

### 4. Lemma 1 (Extraction of Indiscernible Sequences via Erdos-Rado)
**Status:** non-included
**Explanation:** This is the standard Erdos-Rado theorem applied to extract indiscernible sequences from long sequences. Mathlib has neither the Erdos-Rado theorem in its combinatorial form nor the notion of indiscernible sequences in model theory. The Kruskal-Katona theorem file references Erdos but not the Erdos-Rado partition theorem.

### 5. Easy Fact (Extension of Indiscernible Sequences)
**Status:** non-included
**Explanation:** This states that indiscernible sequences can be extended to any desired length via compactness. Mathlib has no formalization of indiscernible sequences.

### 6. Corollary 1 (Extension/Extraction for Indiscernible Sequences)
**Status:** non-included
**Explanation:** The extension/extraction technique is a fundamental tool in model theory stating that A-indiscernible sequences can be "thickened" to B-indiscernible sequences for B containing A. Not in Mathlib.

### 7. Lemma 2 (Dividing Reduces to a Single Formula)
**Status:** non-included
**Explanation:** This states that a partial type divides over c iff some single formula in it divides over c. The concept of dividing is not defined anywhere in Mathlib.

### 8. Corollary 2 (Finite Character of Independence)
**Status:** non-included
**Explanation:** Non-forking independence has finite character: a is independent from b over c iff every finite sub-configuration is independent. Independence (non-forking) is not defined in Mathlib.

### 9. Corollary 3 (Downward Right-Hand Transitivity)
**Status:** non-included
**Explanation:** A basic property of dividing independence. Not in Mathlib as dividing is not defined.

### 10. Corollary 4 (Upward Left-Hand Transitivity)
**Status:** non-included
**Explanation:** Another basic property of dividing independence. Not in Mathlib.

### 11. Proposition 1 (Dividing Characterized by k-Inconsistency Witnesses)
**Status:** non-included
**Explanation:** This gives equivalent characterizations of dividing in terms of k-inconsistency witnesses. Dividing is not in Mathlib.

### 12. Theorem 1 (Characterization of Simplicity: TFAE)
**Status:** non-included
**Explanation:** This is a central theorem characterizing simple theories via the D-rank, the non-existence of long dividing chains, and finiteness of kappa^0(T). The concept of a simple theory is not defined in Mathlib.

### 13. Theorem 2 (D-rank Characterization of Non-Dividing)
**Status:** non-included
**Explanation:** This characterizes non-dividing via the D-rank (a rank on partial types). Neither D-rank nor dividing is in Mathlib.

### 14. Proposition 2 (Universality of Morley Sequences)
**Status:** non-included
**Explanation:** States that if a Morley sequence over c is also indiscernible over ac, then a is independent from the first element over c. Morley sequences are not defined in Mathlib.

### 15. Lemma 3 (Morley Sequence Independence)
**Status:** non-included
**Explanation:** Elements of a Morley sequence are independent from earlier elements. Not in Mathlib.

### 16. Lemma 4 (Existence of Morley Sequences)
**Status:** non-included
**Explanation:** Morley sequences exist for any type. Not in Mathlib.

### 17. Corollary 5 (Characterization of Dividing via Morley Sequences)
**Status:** non-included
**Explanation:** Dividing can be characterized by inconsistency of unions along all (equivalently, some) Morley sequences. Not in Mathlib.

### 18. Theorem 3 (Properties of Independence in Thick Simple Theories)
**Status:** non-included
**Explanation:** This is the main theorem listing the seven properties of non-forking independence in simple theories (invariance, finite character, symmetry, transitivity, extension, local character, independence theorem), plus a uniqueness converse. This is a cornerstone of simplicity theory. Not in Mathlib.

### 19. Corollary 6 (Improved Extension)
**Status:** non-included
**Explanation:** An improved version of the extension property for independence. Not in Mathlib.

### 20. Corollary 7 (Symmetry of Independence)
**Status:** non-included
**Explanation:** Non-forking independence is symmetric: a independent from b over c iff b independent from a over c. Not in Mathlib.

### 21. Corollary 8 (Transitivity of Independence)
**Status:** non-included
**Explanation:** Non-forking independence is transitive. Not in Mathlib.

### 22. Lemma 5 (Indiscernible Sequence Implies Independence)
**Status:** non-included
**Explanation:** The "tail" of an indiscernible sequence is independent from the initial segment. Not in Mathlib.

### 23. Lemma 6 (Indiscernible Sequence Yields Morley Sequence)
**Status:** non-included
**Explanation:** The second half of a long indiscernible sequence forms a Morley sequence over the first half. Not in Mathlib.

### 24. Corollary 9 (Non-Dividing and Consistent Union)
**Status:** non-included
**Explanation:** If a type does not divide over c, then its instances along an indiscernible sequence are jointly consistent. Not in Mathlib.

### 25. Improved Improved Extension
**Status:** non-included
**Explanation:** A partial type that does not divide can be completed to a full type that does not divide. Not in Mathlib.

### 26. Lemma 7 (Characterization of Lascar Strong Type Equality)
**Status:** non-included
**Explanation:** Lascar strong type equality is characterized by finite Lascar distance d_A(a,b) < infinity. Lascar strong types are not defined in Mathlib.

### 27. Lemma 8 (Extension for Strong Types)
**Status:** non-included
**Explanation:** In a simple theory, one can find a Lascar-strong-type-preserving independent extension. Not in Mathlib.

### 28. Lemma 9 (Amalgamation over Lascar Strong Types)
**Status:** non-included
**Explanation:** Partial types can be amalgamated while preserving non-dividing when Lascar strong types match. Not in Mathlib.

### 29. Corollary 10 (The Independence Theorem)
**Status:** non-included
**Explanation:** The Independence Theorem for simple theories: types over independent sets with matching Lascar strong types can be amalgamated. This is one of the most important results in simplicity theory. Not in Mathlib.

### 30. Corollary 11 (Strong Type Extension with Type Preservation)
**Status:** non-included
**Explanation:** A strengthening of the independence theorem preserving types over parameters. Not in Mathlib.

### 31. Corollary 12 (Morley Sequences from Equal Lascar Strong Types)
**Status:** non-included
**Explanation:** Two tuples with equal Lascar strong types that are independent start a Morley sequence. Not in Mathlib.

### 32. Corollary 13 (d_A Bound for Equal Lascar Strong Types)
**Status:** non-included
**Explanation:** If a and b have the same Lascar strong type over A, then d_A(a,b) <= 2. Not in Mathlib.

### 33. Corollary 14 (Type-Definability of Lascar Strong Type Equality)
**Status:** non-included
**Explanation:** Equality of Lascar strong types is type-definable. Not in Mathlib.

### 34. Corollary 15 (D-rank Characterization of Independence)
**Status:** non-included
**Explanation:** Independence is equivalent to preservation of D-rank. Not in Mathlib.

### 35. Important Corollary (Definable Independence)
**Status:** non-included
**Explanation:** Independence from b over c can be expressed by a partial type in the parameters a and c. Not in Mathlib.

### 36. Proposition 3 (Product of Types with Definable Independence)
**Status:** non-included
**Explanation:** Types with definable independence can be "tensored" to produce a product type. Not in Mathlib.

### 37. Lemma 10 (Morley Sequence Automorphic Images Remain Morley)
**Status:** non-included
**Explanation:** Automorphic images of Morley sequences that remain indiscernible in the same type are still Morley sequences. Not in Mathlib.

### 38. Lemma 11 (Equivalence of Hyperimaginary Type Equality: TFAE)
**Status:** non-included
**Explanation:** Three equivalent conditions for when two hyperimaginaries have the same type. Hyperimaginaries are not defined in Mathlib.

### 39. Fact 3 (Simplicity Transfers to Hyperimaginaries)
**Status:** non-included
**Explanation:** A structure is simple iff its hyperimaginary expansion is simple. Not in Mathlib.

### 40. Lemma 12 (Hyperimaginary Codes for Bounded Type-Definable Sets)
**Status:** non-included
**Explanation:** Bounded type-definable sets of hyperimaginaries have canonical parameters. Not in Mathlib.

### 41. Lemma 13 (Hyperimaginaries Reduce to Small Ones)
**Status:** non-included
**Explanation:** Every hyperimaginary is interdefinable with a tuple of small hyperimaginaries. Not in Mathlib.

### 42. Proposition 4 (Characterization of R-tilde)
**Status:** non-included
**Explanation:** A characterization of the refined parallelism relation R-tilde in terms of independence and E-class membership. Not in Mathlib.

### 43. Claim (R* Equals R^2)
**Status:** non-included
**Explanation:** The transitive closure of a generically transitive relation R equals its 2-iterate. Not in Mathlib.

### 44. Corollary 16 (R* is Type-Definable)
**Status:** non-included
**Explanation:** Consequence of R* = R^2; type-definability of the transitive closure. Not in Mathlib.

### 45. Theorem 4 (Properties of Canonical Bases)
**Status:** non-included
**Explanation:** Central theorem on canonical bases in simple theories: they are canonical parameters for parallelism classes, types do not divide over them, and they satisfy minimality properties. Canonical bases are not in Mathlib.

### 46. Theorem 5 (Kim-Pillay Characterization)
**Status:** non-included
**Explanation:** The Kim-Pillay theorem: a theory is simple iff it has an abstract independence relation satisfying the standard axioms. This is one of the most important theorems in simplicity theory. Not in Mathlib.

### 47. Lemma 14 (Characterization of Supersimplicity: TFAE)
**Status:** non-included
**Explanation:** Four equivalent characterizations of supersimplicity via SU-rank finiteness and local character with finite sets. Not in Mathlib.

### 48. Lemma 15 (SU-rank and Non-Dividing)
**Status:** non-included
**Explanation:** Relationship between SU-rank and non-dividing: non-dividing extensions preserve SU-rank. SU-rank is not defined in Mathlib.

### 49. Lascar Inequality I
**Status:** non-included
**Explanation:** SU(a/Ab) + SU(b/A) <= SU(ab/A) <= SU(a/bA) oplus SU(b/A). A fundamental inequality for SU-rank. Not in Mathlib.

### 50. Lascar Inequality II
**Status:** non-included
**Explanation:** If a is independent from b, SU-rank is additive with symmetric addition. Not in Mathlib.

### 51. Lascar Inequality III (Higher Exponent Symmetry)
**Status:** non-included
**Explanation:** A symmetry property of SU-rank drops at specific ordinal levels. Not in Mathlib.

### 52. Theorem 6 (Stability Characterization: TFAE)
**Status:** non-included
**Explanation:** Equivalence of stability with definability of types, counting types, and the R(phi,psi) rank being finite. While Mathlib has `IsComplete` for theories, stability as a model-theoretic property is not defined. Mathlib has no notion of stable theory, definable type (in the stability-theoretic sense), or the type-counting characterization.

### 53. Theorem 7 (Properties of Definable Types over Saturated Models)
**Status:** non-included
**Explanation:** In stable theories, types over saturated models have unique good definitions and their extensions are nonsplitting. Saturation in the model-theoretic sense and definable types are not formalized in Mathlib's model theory library.

### 54. Remark 2 (Good Definitions Imply Non-Dividing)
**Status:** non-included
**Explanation:** Types with good definitions have non-dividing extensions. Not in Mathlib.

### 55. Remark 3 (Nonsplitting Extensions Imply Lascar Strong)
**Status:** non-included
**Explanation:** Types with nonsplitting extensions to all supersets are Lascar strong. Not in Mathlib.

### 56. Corollary 17 (Stable Types over Saturated Models are Lascar Strong)
**Status:** non-included
**Explanation:** In stable theories, types over sufficiently saturated models are Lascar strong. Not in Mathlib.

### 57. Theorem 8 (Characterization of Stability via Stationarity: TFAE)
**Status:** non-included
**Explanation:** Stability is equivalent to simplicity plus stationarity of Lascar strong types, and to simplicity plus bounded multiplicity. Not in Mathlib.

### 58. Proposition 5 (Cofinal Class Criterion for Simplicity)
**Status:** non-included
**Explanation:** A criterion for simplicity involving independence along increasing sequences in cofinal classes. Not in Mathlib.

### 59. Consequence 1 (Types over Saturated Models are Lascar Strong)
**Status:** non-included
**Explanation:** If M is sufficiently saturated, types over M are Lascar strong with d_M(a,b) <= 2. Not in Mathlib.

### 60. Consequence 2 (Realization of Lascar Strong Types in Saturated Models)
**Status:** non-included
**Explanation:** All Lascar strong types over A are realized in sufficiently saturated models containing A. Not in Mathlib.

### 61. Consequence 3 (Co-heir Property)
**Status:** non-included
**Explanation:** In stable theories, independence over a saturated model is characterized by the co-heir property. Not in Mathlib.

### 62. Theorem 9 (Canonical Bases in Stable First-Order Theories)
**Status:** non-included
**Explanation:** In stable first-order theories, canonical bases for stationary types are given by canonical parameters of their definitions. Not in Mathlib.

### 63. Corollary 18 (tp(a/acl^{eq}(A)) is Lascar Strong)
**Status:** non-included
**Explanation:** In stable theories, the type over the algebraic closure in eq is Lascar strong. Not in Mathlib.

### 64. Theorem 10 (PAPA for Stable Theories)
**Status:** non-included
**Explanation:** Stable theories have the PAPA (amalgamation property for pairs of automorphisms) over models. Not in Mathlib.

### 65. Theorem 10' (PAPA over Algebraically Closed Sets)
**Status:** non-included
**Explanation:** Extension of PAPA to algebraically closed sets. Not in Mathlib.

### 66. Theorem 10'' (PAPA for Stable CATs)
**Status:** non-included
**Explanation:** PAPA for stable compact abstract theories over saturated models. Not in Mathlib.

### 67. Theorem 11 (Properties of T_A: Model Companion with Automorphism)
**Status:** non-included
**Explanation:** If T is stable and T_0 = T + "sigma is an automorphism" has a model companion T_A, then T_A is simple, and independence in T_A can be characterized in terms of independence in T. This is a deep result connecting stability and simplicity. Not in Mathlib.

### 68. Fact 4 (Random Graph Properties)
**Status:** non-included
**Explanation:** The theory of the random graph is complete, has QE, is omega-categorical, is the model completion of the theory of graphs, and is simple with a combinatorial independence relation. While Mathlib has `Mathlib/ModelTheory/Graph.lean`, it does not establish these properties of the random graph theory. The Graph.lean file only defines graph language basics.

### 69. Claim (Independence in Hilbert Space)
**Status:** non-included
**Explanation:** In the Hilbert space universal domain, independence is orthogonality of projections, satisfying all simple independence axioms. This is a concrete example in the positive/CAT framework. Not in Mathlib.

### 70. Lemma 16 (Unique Orthogonal Extension in Hilbert Space)
**Status:** non-included
**Explanation:** Types in the Hilbert space setting have unique orthogonal extensions. Not in Mathlib.

### 71. Fact 5 (Thin Formula Characterization of d_A)
**Status:** non-included
**Explanation:** Lascar distance at most 1 is characterized by the absence of thin formulas. Not in Mathlib.

### 72. Theorem 12 (Independence Theorem over Cofinal Classes)
**Status:** non-included
**Explanation:** The independence theorem can be proved assuming it only for types over a cofinal class of "distinguished" sets. Not in Mathlib.

---

## Overall Statistics

- **Total statements identified:** 72
- **Included in Mathlib:** 0
- **Partially included:** 1 (Fact 2 -- type spaces and compact topology)
- **Non-included:** 71

The near-total absence of these statements from Mathlib is expected. Simplicity theory is an advanced topic in model theory that builds on a substantial infrastructure (dividing, forking, indiscernible sequences, Morley sequences, etc.) that Mathlib has not yet formalized. Mathlib's model theory library covers the basics of first-order logic (languages, structures, semantics, the compactness theorem, complete types, definability, elementary embeddings) but has not yet developed the stability-theoretic or simplicity-theoretic machinery.
