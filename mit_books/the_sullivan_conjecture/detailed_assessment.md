# Detailed Assessment: Topics in Algebraic Topology: The Sullivan Conjecture (MIT 18.917) vs Mathlib v4.27.0

## Overview

This textbook covers highly specialized algebraic topology centered on the Sullivan conjecture and its proof via Lannes' T-functor. The core mathematical machinery involves:

- **Steenrod algebra and Steenrod operations** (Sq^k, Adem relations, admissible monomials, dual Steenrod algebra)
- **Unstable modules and algebras over the Steenrod algebra** (category U, free unstable modules F(n), Brown-Gitler modules J(n), Carlsson modules K(n))
- **Lannes' T-functor** (left adjoint to tensoring with H*(BV), exactness, compatibility with tensor products and algebras)
- **Eilenberg-MacLane spaces** (cohomology computations, Cartan-Serre theorem)
- **p-finite and p-profinite spaces** (atomicity, mapping spaces, cochain algebras)
- **E-infinity algebras** (homotopy pushouts, Eilenberg-Moore spectral sequence)
- **p-adic completion, rationalization, and the arithmetic square**
- **Analytic functors, Nil-filtration, Krull filtration** on the category of unstable modules

**None of this material is formalized in Mathlib v4.27.0.** A comprehensive search confirmed:

- **No Steenrod algebra or operations**: Search for "Steenrod" across all of Mathlib returned zero results.
- **No Eilenberg-MacLane spaces**: Search for "EilenbergMacLane" and variants returned zero results.
- **No Lannes' T-functor**: Search for "Lannes" and "Tfunctor" returned zero results.
- **No Sullivan conjecture**: Search for "Sullivan" returned zero results in any algebraic topology context.
- **No unstable modules/algebras**: Search for "unstable module" and "unstable algebra" returned zero results.
- **No Brown-Gitler modules or Carlsson modules**: Search for "BrownGitler", "Brown.Gitler", and "Carlsson" returned zero results.
- **No Adem relations**: Search for "Adem" returned results only in unrelated contexts (Rademacher theorem, matrix characteristic polynomial).
- **No cohomology operations**: Search for "cohomology operation" and "CohomologyOperation" returned zero results.
- **No E-infinity algebras**: Search for "E_infinity" and "EInfinity" returned results only in unrelated analysis/order theory contexts.
- **No p-adic homotopy theory or p-completion of spaces**: Search for "rationalization" and "p.adic homotopy" returned zero relevant results. While Mathlib has p-adic numbers and completions in analysis, it has no p-adic completion of topological spaces in the homotopy-theoretic sense.
- **No classifying spaces BG in homotopy theory**: Mathlib has no construction of classifying spaces of groups.
- **No Kurosh subgroup theorem** (Theorem 8, Lecture 38): Search for "Kurosh" returned zero relevant results. While Mathlib has free products of groups (Mathlib/GroupTheory/CoprodI.lean), it does not contain the theorem that finite subgroups of a free product are conjugate into a factor.

### What Mathlib does have (but does not bridge the gap)

Mathlib v4.27.0 does contain some general categorical infrastructure that is tangentially related to statements in this book, but in no case does the mathlib content actually formalize the specific statements made in the textbook:

1. **Gabriel-Popescu theorem** (Mathlib/CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/GabrielPopescu.lean): Mathlib proves that for a Grothendieck abelian category C with separator G, the functor Hom(G, -) is fully faithful with an exact left adjoint. However, the textbook's Theorem 5 (Lecture 8) states this in the specific context of the category of unstable modules over the Steenrod algebra, which does not exist in Mathlib. The abstract categorical result is present but the specific application (and indeed the specific category it is applied to) is not.

2. **Serre classes** (Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean, Bousfield.lean): Mathlib defines Serre classes and proves basic properties including localization. However, the textbook's use of Serre classes is specifically within the category of unstable modules (the Nil-filtration, Krull filtration), which is not formalized.

3. **Grothendieck abelian categories with enough injectives** (Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean): Mathlib proves Grothendieck abelian categories have enough injectives. However, the textbook's results about injective objects (Corollary 2, Lecture 16; Proposition 2, Lecture 37) are specifically about injective objects in the category U of unstable modules, which does not exist in Mathlib.

4. **Hopf algebras** (Mathlib/RingTheory/HopfAlgebra/): Mathlib has a general definition of Hopf algebras. However, Proposition 4 (Lecture 11) states that the Steenrod algebra is a cocommutative Hopf algebra via a specific comultiplication, which requires the Steenrod algebra itself -- absent from Mathlib.

5. **Free products of groups** (Mathlib/GroupTheory/CoprodI.lean): Mathlib has the construction of free products (coproducts) of groups. However, Theorem 8 (Lecture 38, the Kurosh-type result that finite subgroups of a free product are conjugate into a factor) is not proved in Mathlib.

6. **Profinite spaces** (Mathlib/Topology/Category/Profinite/): Mathlib has the category of profinite spaces (compact, totally disconnected, Hausdorff spaces). However, the textbook's p-profinite spaces are pro-objects in the category of p-finite spaces, which is a homotopy-theoretic concept entirely different from the point-set topological notion in Mathlib.

---

## Statements 1--3 (Lecture 1: Introduction)

### Statement 1: Conjecture 6 (Sullivan) [line 88]
The Sullivan conjecture: for a finite p-group G acting on a simply connected finite G-CW complex M, the map $M^G \to (M^\vee)^{hG}$ induces an isomorphism on mod-p cohomology.

**Assessment: non-included**

This is the central conjecture of the entire textbook. It requires: finite G-CW complexes, fixed point sets, p-completion, homotopy fixed points, and mod-p cohomology. None of these concepts exist in Mathlib. Searches for "Sullivan", "homotopy fixed", "homotopy orbit", and "CW complex" in algebraic topology contexts returned no relevant results.

### Statement 2: Theorem 7 (Miller) [line 96]
Miller's theorem: Map(BG, M) is homotopy equivalent to M for finite dimensional CW complexes M and finite groups G.

**Assessment: non-included**

Requires classifying spaces BG, mapping spaces in homotopy theory, and CW complexes. None present in Mathlib.

### Statement 3: Theorem 9 (Lannes) [line 122]
Lannes' theorem on the T-functor: $T_V$ is exact, commutes with tensor products and suspension, and computes cohomology of mapping spaces from BV.

**Assessment: non-included**

Requires the Steenrod algebra, the category of unstable modules, Lannes' T-functor, and classifying spaces. All absent from Mathlib.

---

## Statement 4 (Lecture 2: Steenrod Operations)

### Statement 4: Proposition 13 [line 293]
Additivity of Steenrod squares.

**Assessment: non-included**

Requires the definition of Steenrod squares, which does not exist in Mathlib.

---

## Statements 5--12 (Lecture 3: Stability and the Cartan Formula)

### Statements 5--12: Propositions 1, 7; Corollaries 2, 3, 5, 9, 10, 11
These statements cover: stability of Steenrod operations (compatibility with loop spaces and suspension), the Cartan formula ($\text{Sq}^n(xy) = \sum \text{Sq}^{n'}(x)\text{Sq}^{n''}(y)$), basic properties ($\text{Sq}^0 = \text{id}$, $\text{Sq}^k = 0$ for $k < 0$), and the action of the Steenrod algebra on $H^*(\mathbb{R}P^\infty)$.

**Assessment: non-included (all 8 statements)**

All require Steenrod operations, which are entirely absent from Mathlib. Even the underlying cohomology theory (mod-2 singular cohomology with cup product structure and functorial operations) is not developed to the level needed.

---

## Statements 13--16 (Lecture 4: The Adem Relations)

### Statements 13--16: Proposition 5 (Adem Relations), Lemmas 13--15
The Adem relations $\text{Sq}^a\text{Sq}^b = \sum \binom{2k-a}{b-k-1}\text{Sq}^{b+k}\text{Sq}^{a-k}$ for $a < 2b$, and supporting lemmas involving the symmetric groups $\Sigma_2$ and $\Sigma_4$.

**Assessment: non-included (all 4 statements)**

Requires the Steenrod algebra, extended Steenrod squares on chain-level constructions ($D_2(V)$, $D_4(V)$), and the homology of symmetric groups. None present in Mathlib.

---

## Statements 17--19 (Lecture 5: The Adem Relations, Continued)

### Statements 17--19: Proposition 3, Corollaries 4--5
Further results on Steenrod operations in terms of the total Steenrod square and restriction maps on group homology.

**Assessment: non-included (all 3 statements)**

Same reasons as Lecture 4. Requires Steenrod operations and homology of symmetric groups.

---

## Statements 20--25 (Lecture 6: Admissible Monomials)

### Statements 20--25: Propositions 1, 3, 5; Scholium 2; Lemmas 4, 6
Structure theory of the Steenrod algebra: spanning by admissible monomials, basis theorem, the big Steenrod algebra $\mathcal{A}^{\text{Big}}$, free unstable modules $F^{\text{Big}}(n)$ and $F(n)$.

**Assessment: non-included (all 6 statements)**

The Steenrod algebra, its "big" variant, admissible sequences, and unstable modules are entirely absent from Mathlib.

---

## Statements 26--29 (Lecture 7: Free Modules)

### Statements 26--29: Propositions 1--3, 6
Linear independence of admissible monomials in free unstable modules, basis theorems, and natural transformations between symmetric power functors.

**Assessment: non-included (all 4 statements)**

Requires the Steenrod algebra and its representation theory (unstable modules), which are absent from Mathlib.

---

## Statements 30--35 (Lecture 8: A Theorem of Gabriel-Kuhn-Popesco)

### Statement 30: Theorem 5 (Kuhn, Gabriel-Popesco) [line 1287]
The functor G admits a left adjoint F; G is fully faithful; F is exact.

**Assessment: non-included**

While Mathlib has a Gabriel-Popescu theorem (Mathlib/CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/GabrielPopescu.lean), the textbook states this in a different form: it is about a specific functor G from the category of unstable A-modules (which does not exist in Mathlib) to a module category. The abstract Gabriel-Popescu theorem in Mathlib takes a different form (for a Grothendieck abelian category with a separator, the Hom functor is fully faithful with exact left adjoint). The textbook's version is a variant due to Kuhn applied in a specific algebraic context that is not formalized.

### Statements 31--35: Lemmas 7, 10, 11; Corollaries 8, 9
Supporting results: monomorphisms are preserved by the adjoint, the counit is an isomorphism, G is fully faithful, F preserves exactness on free resolutions.

**Assessment: non-included (all 5 statements)**

These are consequences of the specific Gabriel-Popesco setup in the category of unstable modules, which does not exist in Mathlib. While some of these statements have abstract categorical analogues, the specific context (unstable A-modules) is not formalized.

---

## Statements 36--43 (Lecture 9: The Injectivity of H*(BV))

### Statements 36--43: Propositions 1, 2, 5, 13, 16, 17; Corollaries 14, 15
These establish that $H^*(BV)$ is injective in the category of unstable modules, via the theory of analytic functors and the equivalence between unstable modules and analytic functors.

**Assessment: non-included (all 8 statements)**

Requires the category of unstable modules over the Steenrod algebra, analytic functors, divided power functors, and the cohomology of classifying spaces. All absent from Mathlib.

---

## Statements 44--54 (Lecture 10: Analytic Functors)

### Statements 44--54: Theorem 1; Propositions 2--6, 8, 9; Lemmas 7, 10, 11
Theory of analytic functors: generation by divided power functors, polynomial functors, Noetherian properties, embeddings into symmetric power functors.

**Assessment: non-included (all 11 statements)**

These concern the category of strict polynomial functors and analytic functors in the sense of homotopy theory (not analytic functions). This entire framework is absent from Mathlib.

---

## Statements 55--58 (Lecture 11: Tensor Products and Unstable Algebras)

### Statement 57: Proposition 4 [line 1864]
The Steenrod algebra is a cocommutative Hopf algebra.

**Assessment: non-included**

While Mathlib has a definition of Hopf algebras (Mathlib/RingTheory/HopfAlgebra/Basic.lean), the Steenrod algebra itself does not exist in Mathlib, so the specific statement that it carries a Hopf algebra structure cannot be expressed.

### Statements 55, 56, 58: Theorem 2; Corollary 3; Theorem 7
Stability of tensor products of unstable modules, free unstable algebras.

**Assessment: non-included (all 3 statements)**

Requires unstable modules and algebras over the Steenrod algebra.

---

## Statements 59--62 (Lecture 12: Eilenberg-MacLane Spaces)

### Statements 59--62: Proposition 1; Theorem 2 (Cartan-Serre); Corollary 3; Theorem 4
The cohomology of Eilenberg-MacLane spaces $K(\mathbf{F}_2, n)$ is computed as the free unstable algebra $F_{\text{Alg}}(n)$, which is a polynomial ring on specific generators.

**Assessment: non-included (all 4 statements)**

Mathlib has no construction of Eilenberg-MacLane spaces (search for "EilenbergMacLane" returned zero results), no computation of their cohomology, and no free unstable algebras.

---

## Statements 63--65 (Lecture 13: The Dual Steenrod Algebra)

### Statements 63--65: Proposition 1; Theorem 2; Corollary 4
The dual Steenrod algebra $\mathcal{A}_* \cong \mathbf{F}_2[\xi_1, \xi_2, \ldots]$ is a polynomial ring with $|\xi_i| = 2^i - 1$.

**Assessment: non-included (all 3 statements)**

The Steenrod algebra and its dual are absent from Mathlib.

---

## Statements 66--70 (Lecture 14: The Frobenius and Verschiebung)

### Statements 66--70: Propositions 1, 3, 5, 8; Theorem 9
The Frobenius functor $\Phi$ and Verschiebung on unstable modules, and the exact sequence involving derived functors of the loop functor $\Omega$.

**Assessment: non-included (all 5 statements)**

Requires the category of unstable modules, the Frobenius endofunctor, and derived loop functors in this algebraic context. All absent from Mathlib.

---

## Statements 71--77 (Lecture 15: Noetherian Properties)

### Statements 71--77: Theorems 4, 6; Lemmas 5, 7; Propositions 8--10
The category of unstable modules is locally Noetherian; submodules of $F(n)$ are finitely generated; finitely generated unstable modules are closed under tensor products.

**Assessment: non-included (all 7 statements)**

While Mathlib has Noetherian objects in categories (Mathlib/CategoryTheory/Subobject/NoetherianObject.lean, Mathlib/CategoryTheory/Noetherian.lean), these results are specifically about the category of unstable modules over the Steenrod algebra, which does not exist in Mathlib.

---

## Statements 78--87 (Lecture 16: Brown-Gitler Modules and Carlsson Modules)

### Statements 78--87: Propositions 1, 3, 6, 9; Corollaries 2, 5, 7, 8, 10, 11
Brown-Gitler modules $J(n)$, Carlsson modules $K(n)$, their injectivity, the category $\mathcal{U}$ having enough injectives, and the relationship between reduced modules and Carlsson modules.

**Assessment: non-included (all 10 statements)**

Brown-Gitler modules and Carlsson modules are specialized constructions in the category of unstable modules. None of this exists in Mathlib.

---

## Statements 88--90 (Lecture 17: Injectivity of Tensor Products)

### Statements 88--90: Theorem 1; Lemmas 2, 3
$K(n) \otimes J(k)$ is injective in $\mathcal{U}$; supporting combinatorial lemmas.

**Assessment: non-included (all 3 statements)**

Requires Brown-Gitler and Carlsson modules in the category of unstable modules.

---

## Statements 91--94 (Lecture 18: Lannes' T-functor)

### Statements 91--94: Propositions 2, 6, 7, 8
Construction of Lannes' T-functor as a left adjoint, its exactness, its decomposition, and its commutation with suspension.

**Assessment: non-included (all 4 statements)**

Lannes' T-functor is absent from Mathlib (search for "Lannes" returned zero results).

---

## Statements 95--98 (Lecture 19: T-functor and Tensor Products)

### Statements 95--98: Proposition 1; Theorem 2; Lemmas 5, 6
$T_V$ commutes with the Frobenius, with tensor products ($T_V(M \otimes N) \cong T_V M \otimes T_V N$), and supporting lemmas.

**Assessment: non-included (all 4 statements)**

Requires Lannes' T-functor and unstable modules.

---

## Statements 99--103 (Lecture 20: T-functor and Unstable Algebras)

### Statements 99--103: Lemma 1; Propositions 2, 3; Corollaries 4, 5
$T_V$ preserves unstable algebras, is left adjoint to tensoring with $H^*(BV)$ on the category of unstable algebras, and $T_V F_{\text{Alg}}(n)$ decomposes as a tensor product.

**Assessment: non-included (all 5 statements)**

Requires Lannes' T-functor, unstable algebras, and classifying spaces.

---

## Statements 104--105 (Lecture 21: Mapping Spaces)

### Statements 104--105: Theorem 1; Lemma 2
$T_V H^*(K(\mathbf{F}_2, n)) \cong H^*(\text{Map}(BV, K(\mathbf{F}_2, n)))$; odd-index transfer in group homology.

**Assessment: non-included (both statements)**

Requires Lannes' T-functor, Eilenberg-MacLane spaces, mapping spaces, and classifying spaces.

---

## Statements 106--111 (Lecture 22: E-infinity Algebras and Eilenberg-MacLane Spaces)

### Statements 106--111: Theorem 1; Lemma 2; Proposition 3; Lemmas 4, 5; Corollary 6
Homotopy pushout squares of $E_\infty$-algebras, Kunneth isomorphisms, cohomology of free $E_\infty$-algebras, and their relation to Eilenberg-MacLane spaces.

**Assessment: non-included (all 6 statements)**

$E_\infty$-algebras (operadic algebra) are not formalized in Mathlib. Search for "E_infinity" and "EInfinity" returned no relevant results.

---

## Statements 112--115 (Lecture 23: p-Finite Spaces)

### Statements 112--115: Lemma 4; Corollary 5; Theorems 6, 8
Characterization of p-finite spaces via principal fibrations, finite-dimensionality of cohomology, homotopy pushouts of cochain algebras, and tensor product decomposition for local systems.

**Assessment: non-included (all 4 statements)**

p-finite spaces, principal fibrations with Eilenberg-MacLane fibers, and cochain algebras are absent from Mathlib.

---

## Statements 116--118 (Lecture 24: Convergence of the Eilenberg-Moore Spectral Sequence)

### Statements 116--118: Lemmas 2, 3, 4
Technical lemmas on weak equivalences and Goodwillie's lemma related to convergence of the Eilenberg-Moore spectral sequence.

**Assessment: non-included (all 3 statements)**

Spectral sequences are not formalized in Mathlib. The Eilenberg-Moore spectral sequence requires cochain algebra theory absent from Mathlib.

---

## Statements 119--120 (Lecture 25: The Sullivan Conjecture, p-Profinite Case)

### Statements 119--120: Theorem 2; Proposition 4
$T_V H^*(X) \cong H^*(X^{BV})$ for 2-finite spaces; homotopy pullbacks preserve this isomorphism.

**Assessment: non-included (both statements)**

Requires Lannes' T-functor, p-finite spaces, and mapping spaces with classifying spaces.

---

## Statements 121--122 (Lecture 26: p-Profinite Spaces)

### Statements 121--122: Proposition 8; Theorem 11
Existence of mapping spaces in p-profinite spaces; the T-functor isomorphism extends to all p-profinite spaces.

**Assessment: non-included (both statements)**

p-profinite spaces in the homotopy-theoretic sense are absent from Mathlib. (Mathlib has profinite spaces as a point-set topological concept, which is different.)

---

## Statements 123--125 (Lecture 27: Cochain Algebras)

### Statements 123--125: Theorem 2; Lemmas 3, 4
The cochain functor $X \mapsto C^*(X; k)$ is a fully faithful embedding from p-profinite spaces to $E_\infty$-algebras; it carries homotopy limits to homotopy colimits.

**Assessment: non-included (all 3 statements)**

Requires p-profinite spaces, cochain algebras, and $E_\infty$-algebra theory.

---

## Statements 126--130 (Lecture 28: Atomicity)

### Statements 126--130: Theorem 3; Propositions 4, 6; Corollaries 7, 8
Connected p-finite spaces are atomic; the mapping space functor preserves homotopy pushouts; characterization of atomicity; $BG$ is atomic for finite p-groups.

**Assessment: non-included (all 5 statements)**

Atomicity is a concept specific to p-profinite homotopy theory, absent from Mathlib.

---

## Statements 131--136 (Lecture 29: Atomicity of p-Finite Spaces)

### Statements 131--136: Proposition 1; Theorem 3; Corollaries 5, 6; Theorem 7; Proposition 8
Totalizations commute with homotopy pushouts; atomicity of simplicial p-profinite spaces; $K(G, n)$ is atomic; connected p-finite spaces are atomic; contractibility of $X^{BV}$ for atomic X.

**Assessment: non-included (all 6 statements)**

Requires p-profinite homotopy theory and atomicity, absent from Mathlib.

---

## Statements 137--140 (Lecture 30: The Sullivan Conjecture)

### Statement 140: Theorem 4 [line 4674]
The Sullivan conjecture: for a finite p-group G acting on a p-finite space X, the map $X^G \to (X^\vee)^{hG}$ is an equivalence on mod-p cohomology.

**Assessment: non-included**

This is the culmination of the entire book. It requires the full apparatus of Lannes' T-functor theory, p-profinite homotopy theory, and atomicity.

### Statements 137--139: Theorem 1; Corollary 2; Lemma 3
The diagonal map $X \to X^{BV}$ is an equivalence for p-profinite spaces; maps from spaces with finite mod-p cohomology into $X^\vee$ are nullhomotopic; homotopy fixed points preserve finite homotopy colimits.

**Assessment: non-included (all 3 statements)**

Same reasons as Theorem 4 above.

---

## Statements 141--151 (Lecture 31: p-adic Completion)

### Statements 141--151: Theorem 1; Lemma 2; Corollaries 3--6, 8; Lemmas 7, 9; Proposition 14; Lemma 15
p-adic completion of simply connected spaces: $\pi_n(X_p^\vee) \cong \pi_n(X) \otimes \mathbf{Z}_p$; pro-isomorphisms for $K(\mathbf{Z}, n)$; cohomology of p-adic completions; $\mathbf{F}_p$-localization.

**Assessment: non-included (all 11 statements)**

p-adic completion of spaces (in the homotopy-theoretic sense), Eilenberg-MacLane spaces, and $\mathbf{F}_p$-localization of spaces are absent from Mathlib. Mathlib's p-adic analysis concerns the p-adic numbers as a valued field, not homotopy-theoretic completions.

---

## Statements 152--155 (Lecture 32: Rationalization and the Arithmetic Square)

### Statements 152--155: Theorem 3; Lemmas 4, 6; Theorem 7
Rationalization of simply connected spaces: $\pi_n(X_\mathbf{Q}) \cong \pi_n(X) \otimes \mathbf{Q}$; spaces with rational homotopy groups are rational; torsion homotopy groups imply vanishing rational homology; the arithmetic square.

**Assessment: non-included (all 4 statements)**

Rationalization of spaces and the arithmetic square in homotopy theory are absent from Mathlib. While Mathlib has rational numbers and tensor products, the homotopy-theoretic localization framework is not formalized.

---

## Statements 156--159 (Lecture 33: Applications of the Sullivan Conjecture)

### Statements 156--159: Theorem 1; Proposition 2; Lemmas 3, 4
Applications: $\text{Map}(BG, X) \simeq X$ for simply connected finite CW complexes; p-adic completion and rationalization are "good"; rational spaces are good; $\mathbf{F}_p$-homology equivalences.

**Assessment: non-included (all 4 statements)**

These are consequences of the Sullivan conjecture requiring the full apparatus developed in the book.

---

## Statements 160--164 (Lecture 34: The Dwyer-Miller-Wilkerson Theorem)

### Statements 160--164: Theorem 1; Lemma 2; Corollary 3; Lemma 4; Theorem 5
The Dwyer-Miller-Wilkerson theorem: if $H^*(X; \mathbf{F}_p) \cong \mathbf{F}_p[t]$ then $X \simeq BSU(2)_p^\vee$; determination of the Steenrod algebra action; existence of maps from $B\mathbf{Z}/p$ inducing nontrivial cohomology.

**Assessment: non-included (all 5 statements)**

Requires the Steenrod algebra action on cohomology, classifying spaces, and p-adic completion of spaces.

---

## Statements 165--166 (Lecture 35: Truncated Modules and Functors)

### Statements 165--166: Propositions 1, 5
The functor $f$ from unstable modules to analytic functors via $f(M)(V) = (T_V M)^0$; the truncation functor $f_n$ defines an adjunction and is exact.

**Assessment: non-included (both statements)**

Requires Lannes' T-functor and the category of unstable modules.

---

## Statements 167--172 (Lecture 36: The Nil-Filtration)

### Statements 167--172: Lemma 2; Propositions 7, 9; Corollaries 11, 12; Theorem 13
Characterization of objects orthogonal to a Serre class; localization of Grothendieck abelian categories by Serre classes yields a Grothendieck abelian category; equivalence $\mathcal{U}/\mathcal{K}_n \simeq \text{Fun}_n$; characterization of the Serre classes $\mathcal{K}_n$.

**Assessment: non-included (all 6 statements)**

While Mathlib has Serre classes (Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean) and Grothendieck abelian categories with localization (Mathlib/CategoryTheory/Abelian/SerreClass/Bousfield.lean), these results are specifically about the Nil-filtration on the category of unstable modules. The abstract localization theory in Mathlib does not include the statement that a Serre quotient of a Grothendieck abelian category is Grothendieck abelian (Proposition 7), nor the specific results about the unstable module category.

---

## Statements 173--178 (Lecture 37: The Krull Filtration)

### Statement 173: Proposition 2 [line 5690]
Injective hulls exist in locally Noetherian abelian categories; direct sums of injectives are injective; injectives decompose as direct sums of indecomposables.

**Assessment: non-included**

While Mathlib has enough injectives for Grothendieck abelian categories, it does not have the specific decomposition theory for injective objects (injective hulls, Krull-Remak-Schmidt for injectives in locally Noetherian categories). Search for "injective hull" and "injectiveHull" in CategoryTheory returned no results.

### Statements 174--178: Proposition 9; Propositions 13, 14; Theorem 15; Proposition 16
Classification of indecomposable injectives; characterization of the Krull filtration on $\mathcal{U}$; locally finite modules; the T-functor and Krull filtration.

**Assessment: non-included (all 5 statements)**

The Krull filtration on the category of unstable modules is absent from Mathlib.

---

## Statements 179--184 (Lecture 38: Epilogue)

### Statements 179--183: Lemmas 1, 2; Proposition 4; Proposition 6; Theorem 7
The functor $f_\infty$ is fully faithful; the Krull filtration is exhaustive; the Nil-filtration quotients are identified with analytic functors; symmetric group representations give successive quotients; the complete structure theorem for the category $\mathcal{U}$.

**Assessment: non-included (all 5 statements)**

Requires the full theory of unstable modules, Nil-filtration, and Krull filtration.

### Statement 184: Theorem 8 [line 5991]
Any homomorphism from a finite group F to a free product $G \star H$ is conjugate to a homomorphism into G or into H.

**Assessment: non-included**

This is essentially the Kurosh subgroup theorem (or a consequence thereof). While Mathlib has free products of groups (Mathlib/GroupTheory/CoprodI.lean) with the normal form theorem, it does not contain the Kurosh subgroup theorem or this result about finite subgroups of free products. Search for "Kurosh" returned zero relevant results, and search for "conjugate" within the free product files returned no results about subgroup conjugacy.

---

## Summary

**0 out of 184 statements are included in Mathlib v4.27.0.**

This is expected given that the textbook covers extremely specialized material in algebraic topology. The core mathematical objects -- the Steenrod algebra, Steenrod operations, unstable modules, Lannes' T-functor, Eilenberg-MacLane spaces, classifying spaces, p-profinite spaces, and E-infinity algebras -- are all absent from Mathlib. Mathlib's algebraic topology is limited to simplicial sets/objects, the fundamental groupoid, basic homotopy groups, the Dold-Kan correspondence, and rudimentary singular homology. The gap between what is formalized and what this textbook requires is substantial.

While Mathlib does contain some general categorical infrastructure (Gabriel-Popescu theorem, Serre classes, Grothendieck abelian categories, Hopf algebras, free products of groups) that appears in the textbook, in every case the textbook applies this infrastructure to specific objects (the category of unstable modules, the Steenrod algebra) that do not exist in Mathlib, making the specific statements non-included.
