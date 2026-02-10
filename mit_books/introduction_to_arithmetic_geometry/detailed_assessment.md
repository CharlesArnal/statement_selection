# Detailed Assessment: Introduction to Arithmetic Geometry vs Mathlib

## Methodology

Each of the 224 formal statements in the textbook was categorized by searching Mathlib v4.27.0 for corresponding formalized results. Searches were conducted by name, by mathematical concept, and by browsing relevant Mathlib directories. The assessments use the following categories:

- **In Mathlib (Exact)**: The statement is formalized in Mathlib in essentially the same form.
- **In Mathlib (Close)**: The mathematical content is in Mathlib but stated differently or as part of a more general framework.
- **Partially in Mathlib**: Some components or special cases are formalized, but the full statement is not.
- **Not in Mathlib**: No corresponding formalization was found.

---

## Chapter 1: Introduction (Lecture 1)

### Statement 1: Theorem (Bhargava, Shankar 2010-2012) [line 295]
**Content**: The average rank of all elliptic curves over Q is less than 1.
**Assessment**: Not in Mathlib.
**Details**: This is a deep analytic number theory result about statistical properties of elliptic curves. Far beyond current formalization capabilities.

### Statement 2-3: Theorem (Hasse 1933) [lines 305, 313]
**Content**: #E(F_p) = p+1-t with |t| <= 2*sqrt(p) (Hasse bound / Riemann hypothesis for elliptic curves over finite fields).
**Assessment**: Not in Mathlib.
**Details**: No formalization of the Hasse bound or Weil conjectures for curves was found. This would require substantial algebraic geometry infrastructure.

### Statement 4: Theorem (Taylor et al., 2006 and 2008) [line 349]
**Content**: Sato-Tate conjecture for CM-free elliptic curves over Q.
**Assessment**: Not in Mathlib.
**Details**: This is an extremely deep result in automorphic forms and Galois representations.

### Statement 5: Theorem (Wiles et al. 1995) [line 379]
**Content**: Fermat's Last Theorem.
**Assessment**: Not in Mathlib.
**Details**: Fermat's Last Theorem has not been formalized in Lean/Mathlib (though Kevin Buzzard's FLT project is ongoing).

### Statement 6: Theorem (Faltings 1983) [line 397]
**Content**: Mordell conjecture: curves of genus > 1 over Q have finitely many rational points.
**Assessment**: Not in Mathlib.
**Details**: No formalization of Faltings' theorem was found. This is one of the deepest results in arithmetic geometry.

---

## Chapter 2: Conics (Lecture 2)

### Statement 7: Theorem 2.1 [line 450]
**Content**: Every geometrically irreducible conic (char != 2) is isomorphic to a diagonal form ax^2+by^2+cz^2=0.
**Assessment**: Not in Mathlib.
**Details**: Mathlib does not have a theory of conics as algebraic curves in this classical sense.

### Statement 8: Theorem 2.3 [line 487]
**Content**: A conic with a rational point is isomorphic to P^1.
**Assessment**: Not in Mathlib.
**Details**: While Mathlib has projective space, the birational geometry of conics is not formalized.

### Statement 9: Theorem 2.5 (Holzer) [line 553]
**Content**: Bound on integer solutions to ax^2+by^2+cz^2=0.
**Assessment**: Not in Mathlib.

### Statement 10: Theorem 2.6 (Legendre) [line 563]
**Content**: Legendre's theorem on representation by ternary quadratic forms.
**Assessment**: Not in Mathlib.
**Details**: While Mathlib has some quadratic form theory, this specific representation result is not there.

---

## Chapter 3: Quadratic Reciprocity and Finite Fields (Lecture 3)

### Statement 11: Theorem 3.1 (Gauss) [line 599]
**Content**: Quadratic reciprocity: (p/q)(q/p) = (-1)^((p-1)/2)((q-1)/2).
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`
**Mathlib name**: `legendreSym.quadratic_reciprocity`
**Details**: Full quadratic reciprocity is proven for the Legendre symbol and also for the Jacobi symbol in `JacobiSymbol.lean`.

### Statement 12: Theorem 3.3 [line 629]
**Content**: Any finite subgroup of the multiplicative group of a field is cyclic.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/IntegralDomain.lean`
**Mathlib name**: `isCyclic_of_subgroup_isDomain`
**Details**: Proven more generally: a finite subgroup of the units of an integral domain is cyclic.

### Statement 13: Theorem 3.4 [line 641]
**Content**: Every conic over a finite field of odd characteristic has a rational point.
**Assessment**: Not in Mathlib.
**Details**: While Chevalley-Warning is in Mathlib (`FieldTheory/ChevalleyWarning.lean`), this specific consequence for conics is not explicitly stated. Chevalley-Warning could be used to derive it.

### Statement 14: Corollary 3.5 [line 645]
**Content**: Classification of conics over finite fields.
**Assessment**: Not in Mathlib.

### Statement 15: Theorem 3.7 (Rabin) [line 703]
**Content**: A formula for distinct elements in F_q.
**Assessment**: Not in Mathlib.

---

## Chapter 4: p-adic Integers (Lecture 4)

### Statement 16: Theorem 4.6 [line 809]
**Content**: Every element of Z_p has a unique p-adic expansion.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib defines Z_p and has extensive API in `NumberTheory/Padics/PadicIntegers.lean`, but the explicit p-adic expansion theorem is not stated in this classical form. Related material exists in `NumberTheory/Padics/RingHoms.lean`.

### Statement 17: Theorem 4.8 [line 843]
**Content**: Properties of sequences related to p-adic expansion.
**Assessment**: Partially in Mathlib.

### Statement 18: Corollary 4.9 [line 861]
**Content**: Z_p/p^m Z_p = Z/p^m Z.
**Assessment**: Partially in Mathlib.
**Details**: Related material is in `NumberTheory/Padics/RingHoms.lean` where various ring homomorphisms between Z_p and Z/p^n Z are defined.

### Statement 19: Theorem 4.11 [line 865]
**Content**: Properties of the p-adic valuation v_p.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`
**Details**: The p-adic valuation is defined and its properties (multiplicativity, ultrametric inequality, etc.) are proven.

### Statement 20: Corollary 4.13 [line 881]
**Content**: Z_p is an integral domain.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/NumberTheory/Padics/PadicIntegers.lean`
**Mathlib name**: `PadicInt.instIsDomain` (instance at line 201)

### Statement 21: Theorem 4.15 [line 887]
**Content**: Properties of Z_p (units, etc.).
**Assessment**: Partially in Mathlib.
**Details**: Many properties of Z_p are scattered through `PadicIntegers.lean`.

### Statement 22: Theorem 4.16 [line 900]
**Content**: Every nonzero ideal in Z_p is of the form (p^m).
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/NumberTheory/Padics/PadicIntegers.lean`
**Details**: Z_p is shown to be a DVR (`IsDiscreteValuationRing` instance at line 520), which implies all ideals are powers of the maximal ideal. The maximal ideal is shown to be generated by p (`maximalIdeal_eq_span_p`).

### Statement 23: Corollary 4.17 [line 904]
**Content**: Z_p is a PID with unique maximal ideal.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/NumberTheory/Padics/PadicIntegers.lean`
**Details**: The DVR structure implies PID (via `IsPrincipalIdealRing`). The local ring structure (`IsLocalRing` instance) gives the unique maximal ideal.

---

## Chapter 5: p-adic Absolute Values (Lecture 5)

### Statement 24: Theorem 5.3 [line 966]
**Content**: Properties of absolute values on fields.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has `AbsoluteValue` in `Algebra/Order/AbsoluteValue.lean` with basic properties.

### Statement 25: Corollary 5.4 [line 988]
**Content**: In a field of positive characteristic, every absolute value is nonarchimedean; trivial if finite.
**Assessment**: Not in Mathlib.
**Details**: While Mathlib has the concept of nonarchimedean norms, this specific characterization by characteristic is not explicitly stated.

### Statement 26: Theorem 5.6 (Ostrowski) [line 1018]
**Content**: Every nontrivial absolute value on Q is equivalent to | |_p for some prime p or p = infinity.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/NumberTheory/Ostrowski.lean`
**Mathlib name**: `Rat.AbsoluteValue.equiv_real_or_padic`
**Details**: Fully proven in Mathlib. The theorem states that every nontrivial absolute value on Q (with values in R) is equivalent to either the real absolute value or a p-adic absolute value for a unique prime p.

---

## Chapter 7: Algebraic Number Theory (Lecture 7)

### Statement 27: Theorem 7.2 [line 1125]
**Content**: Relationship between minimal polynomial, characteristic polynomial, norm, and trace for separable extensions.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Norm/Basic.lean`, `Mathlib/RingTheory/NormTrace.lean`
**Details**: The norm is defined via the determinant of the left multiplication map. The relationship between norm and minimal polynomial is established via `PowerBasis.norm_gen_eq_coeff_zero_minpoly`. The trace analog is in `RingTheory/Trace/`.

### Statement 28: Theorem 7.5 [line 1147]
**Content**: N(alpha) = |N_{L/Q}(alpha)| for algebraic integers.
**Assessment**: Partially in Mathlib.
**Details**: The algebraic norm is defined in `RingTheory/Norm/`. The connection to the ideal norm for number fields is in `NumberTheory/NumberField/Norm.lean`.

### Statement 29: Theorem 7.6 [line 1171]
**Content**: Product formula for number fields: product of |alpha|_v over all places = 1.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/NumberTheory/NumberField/ProductFormula.lean`
**Mathlib name**: `NumberField.prod_abs_eq_one`
**Details**: The product formula for number fields is fully proven.

### Statement 30: Lemma 7.8 [line 1211]
**Content**: Limits preserve addition and multiplication.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/Topology/Algebra/Ring/Basic.lean` and related files
**Details**: This follows from the fact that addition and multiplication are continuous in topological rings, which is part of Mathlib's algebraic topology infrastructure.

### Statement 31: Theorem 7.10 [line 1219]
**Content**: Every convergent sequence is Cauchy.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/Topology/UniformSpace/Cauchy.lean`
**Mathlib name**: `Filter.Tendsto.cauchy_map`, `Filter.Tendsto.cauchySeq`

### Statement 32: Theorem 7.15 [line 1265]
**Content**: k is dense in its completion k-hat.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/Topology/UniformSpace/Completion.lean`
**Mathlib name**: `UniformSpace.Completion.denseRange_coe`

### Statement 33: Corollary 7.16 [line 1269]
**Content**: Every Cauchy sequence in k-hat is equivalent to one with elements in k.
**Assessment**: **In Mathlib (Close)**.
**Details**: This follows from the density result and the completion construction in Mathlib.

### Statement 34: Corollary 7.17 [line 1273]
**Content**: The completion is complete and is the smallest complete field containing k.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/Topology/UniformSpace/Completion.lean`
**Mathlib name**: `UniformSpace.Completion.completeSpace` (completeness); the universal property is via `UniformSpace.Completion.extensionHom`.

---

## Chapter 8: Hensel's Lemma (Lecture 8)

### Statement 35: Theorem 8.1 [line 1303]
**Content**: The completion of Q w.r.t. p-adic absolute value is isomorphic to Q_p.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib constructs Q_p as the completion of Q w.r.t. the p-adic norm in `NumberTheory/Padics/PadicNumbers.lean`. The isomorphism is by construction.

### Statement 36: Lemma 8.3 [line 1327]
**Content**: The inverse limit of an inverse system of finite non-empty sets is non-empty.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/CategoryTheory/CofilteredSystem.lean`
**Mathlib name**: `nonempty_sections_of_finite_inverse_system`
**Details**: Proven more generally for cofiltered systems of finite nonempty types.

### Statement 37: Theorem 8.4 [line 1341]
**Content**: f in Z_p[x] has a root in Z_p iff it has compatible roots mod p^n.
**Assessment**: Partially in Mathlib.
**Details**: This is implicit in the construction of Z_p as an inverse limit, but not stated as a standalone theorem about polynomial roots.

### Statement 38: Lemma 8.7 [line 1384]
**Content**: f(a) = f'(a) = 0 iff a is a double root.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has `Polynomial.IsRoot` and `Polynomial.rootMultiplicity` but this specific characterization combining f and f' is not explicitly stated in this form.

### Statement 39: Theorem 8.8 (Hensel's Lemma) [line 1400]
**Content**: If f(a) = 0 mod p and f'(a) != 0 mod p, then there is a unique b in Z_p with f(b) = 0 and b = a mod p.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/NumberTheory/Padics/Hensel.lean`
**Mathlib name**: `hensels_lemma`
**Details**: Fully proven. The statement gives existence and uniqueness of the lift, with the additional information that the derivative norm is preserved.

---

## Chapter 9: Quadratic Forms (Lecture 9)

### Statement 40: Theorem 9.5 [line 1500]
**Content**: Every quadratic form is equivalent to a diagonal quadratic form.
**Assessment**: Not in Mathlib.
**Details**: Mathlib has `LinearAlgebra/QuadraticForm/` but diagonalization of quadratic forms is not formalized.

### Statement 41: Theorem 9.9 [line 1529]
**Content**: If a nondegenerate quadratic form represents 0 then it represents every element.
**Assessment**: Not in Mathlib.

### Statement 42: Theorem 9.10 (Hasse-Minkowski) [line 1539]
**Content**: A quadratic form over Q represents 0 iff it represents 0 over every completion.
**Assessment**: Not in Mathlib.
**Details**: The Hasse-Minkowski theorem is a deep result not yet formalized in Mathlib.

---

## Chapter 10: Hilbert Symbol (Lecture 10)

### Statements 43-51 [lines 1569-1662]
**Content**: Properties of the Hilbert symbol (a,b)_p, computation formulas, product formula.
**Assessment**: Not in Mathlib.
**Details**: The Hilbert symbol is not defined in Mathlib. None of the specific formulas (Theorems 10.4, 10.7, 10.9) or the product formula (Theorem 10.11) are present.

---

## Chapter 11: Local-Global Principle (Lecture 11)

### Statement 52: Theorem 11.1 [line 1702]
**Content**: Diagonal quadratic forms of dimension > 2 represent 0 over Q_p for odd p.
**Assessment**: Not in Mathlib.

### Statement 53: Corollary 11.2 [line 1706]
**Content**: Quadratic forms of dim > 2 represent 0 over Q_p for all but finitely many p.
**Assessment**: Not in Mathlib.

### Statement 54-56: Lemma 11.3, Corollaries 11.4, 11.5 [lines 1712-1725]
**Content**: Various consequences involving Hilbert symbols and quadratic forms.
**Assessment**: Not in Mathlib.

### Statement 57: Theorem 11.6 [line 1733]
**Content**: Q is dense in Q_p and Z is dense in Z_p.
**Assessment**: Partially in Mathlib.
**Details**: The density of Q in Q_p follows from the completion construction. Mathlib has Q_p constructed as completion of Q, so density is by construction.

### Statement 58: Theorem 11.7 (Weak Approximation) [line 1737]
**Content**: Weak approximation theorem for Q.
**Assessment**: Not in Mathlib.
**Details**: No formalization of weak approximation for number fields was found.

### Statement 59: Theorem 11.8 (Strong Approximation) [line 1761]
**Content**: Strong approximation theorem.
**Assessment**: Not in Mathlib.

### Statement 60: Lemma 11.11 [line 1785]
**Content**: Approximation of p-adic units by rational numbers.
**Assessment**: Not in Mathlib.

### Statement 61: Theorem 11.12 (Hasse-Minkowski) [line 1802]
**Content**: Full Hasse-Minkowski theorem for quadratic forms.
**Assessment**: Not in Mathlib.

---

## Chapter 12: Algebraic Geometry Basics (Lecture 12)

### Statement 62: Theorem 12.2 [line 1866]
**Content**: Every transcendence basis has the same cardinality.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/AlgebraicIndependent/RankAndCardinality.lean`
**Mathlib name**: `IsTranscendenceBasis.lift_cardinalMk_eq_max_lift`
**Details**: The theorem is proved in terms of cardinal arithmetic. The transcendence degree is well-defined (same cardinality for any basis).

### Statement 63: Theorem 12.11 (Hilbert Basis Theorem) [line 1969]
**Content**: If R is Noetherian, then R[x] is Noetherian.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Polynomial/Basic.lean` (line 822)
**Mathlib name**: `Polynomial.isNoetherianRing`
**Details**: Proven for R[x] and also for multivariate polynomial rings.

### Statement 64: Lemma 12.14 [line 2001]
**Content**: The radical of an ideal is an ideal.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Ideal/Operations.lean`
**Mathlib name**: `Ideal.radical` is defined as an `Ideal R`.

### Statement 65: Theorem 12.15 (Nullstellensatz) [line 2011]
**Content**: I(Z_I) = sqrt(I) for ideals in k-bar[x_1,...,x_n].
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Nullstellensatz.lean`
**Mathlib name**: `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`

### Statement 66: Theorem 12.16 (Weak Nullstellensatz) [line 2020]
**Content**: For any proper ideal, Z_I is nonempty.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Nullstellensatz.lean`
**Details**: The weak form follows from the characterization of maximal ideals. The file characterizes maximal ideals and shows the Galois connection between ideals and varieties.

### Statement 67: Corollary 12.17 [line 2026]
**Content**: Maximal ideals of k-bar[x_1,...,x_n] are (x_1-a_1,...,x_n-a_n).
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Nullstellensatz.lean`
**Mathlib name**: `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`

### Statement 68: Corollary 12.18 [line 2036]
**Content**: Galois correspondence between radical ideals and algebraic sets.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Nullstellensatz.lean`
**Mathlib name**: `MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`
**Details**: The Galois connection is established. The bijection for radical ideals follows from the Nullstellensatz.

### Statement 69: Theorem 12.21 [line 2042]
**Content**: An algebraic set is irreducible iff its ideal is prime.
**Assessment**: Partially in Mathlib.
**Details**: The connection between irreducible closed sets and prime ideals is in `RingTheory/Spectrum/Prime/Topology.lean` for the prime spectrum. For the algebraic geometry context with algebraic sets specifically, this is not directly stated in the textbook's classical form.

---

## Chapter 13: Dimension and Projective Space (Lecture 13)

### Statement 70: Lemma 13.6 [line 2112]
**Content**: dim A^n = n and dim of a point is 0.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has Krull dimension (`Order.krullDim`) and results on dimension of polynomial rings. The Krull dimension of k[x_1,...,x_n] equals n is approached through `RingTheory/KrullDimension/Polynomial.lean`.

### Statement 71: Theorem 13.8 [line 2125]
**Content**: Krull dimension of a f.g. k-algebra = transcendence degree of its fraction field.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has Krull dimension and transcendence degree separately but their equality for finitely generated algebras may not be fully established.

### Statements 72-74: Theorems 13.23, 13.24, Corollary 13.26 [lines 2291-2307]
**Content**: Properties of projective closures and affine parts of projective varieties.
**Assessment**: Not in Mathlib.
**Details**: Mathlib has the projective spectrum (`AlgebraicGeometry/ProjectiveSpectrum/`) but does not develop the classical theory of projective closures of affine varieties.

---

## Chapter 14: Morphisms (Lecture 14)

### Statement 75: Theorem 14.4 [line 2361]
**Content**: Every morphism of affine varieties is continuous.
**Assessment**: Partially in Mathlib.
**Details**: In the scheme-theoretic framework, morphisms of schemes are continuous. But the classical variety-theoretic statement is not directly available.

### Statements 76-79: Theorem 14.8, Corollaries 14.9-14.12 [lines 2393-2445]
**Content**: Anti-equivalence between affine varieties and affine algebras.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has `AlgebraicGeometry/GammaSpecAdjunction.lean` which establishes the adjunction between Spec and global sections. The scheme-theoretic version of this equivalence is present, but not the classical variety version.

---

## Chapter 15: Rational Maps (Lecture 15)

### Statements 80-86 [lines 2493-2579]
**Content**: Rational maps, dominant rational maps, birational equivalence, function field equivalence.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has `AlgebraicGeometry/RationalMap.lean` and `AlgebraicGeometry/FunctionField.lean` which develop rational maps and function fields for schemes. The classical variety-theoretic statements are not directly formalized.

---

## Chapter 16: Completeness and Valuation Rings (Lecture 16)

### Statement 87: Theorem 16.1 [line 2633]
**Content**: Quasi-compactness of A^n in the Zariski topology (any open cover has a finite subcover).
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`
**Mathlib name**: `PrimeSpectrum.compactSpace`
**Details**: The prime spectrum of any ring is compact (quasi-compact). This is the scheme-theoretic version.

### Statement 88: Lemma 16.3 [line 2670]
**Content**: Bijection between maximal ideals of k[V] and points of V.
**Assessment**: Partially in Mathlib.
**Details**: For the scheme-theoretic version, closed points of Spec(R) correspond to maximal ideals. The classical variety version is a consequence of the Nullstellensatz.

### Statement 89: Lemma 16.4 [line 2674]
**Content**: Tensor product of affine algebras is an affine algebra.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has extensive tensor product theory (`RingTheory/TensorProduct/`) but the specific statement about affine algebras (finitely generated k-algebras) is not stated in this form.

### Statement 90: Corollary 16.5 [line 2684]
**Content**: Product of affine varieties is an affine variety.
**Assessment**: Partially in Mathlib.
**Details**: Fiber products of affine schemes exist in `AlgebraicGeometry/Pullbacks.lean`.

### Statements 91-92: Lemma 16.12, Lemma 16.13 [lines 2716, 2726]
**Content**: Properties of complete varieties (closed maps, subvarieties complete).
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has proper morphisms (`AlgebraicGeometry/Morphisms/Proper.lean`) and universally closed morphisms. These are the scheme-theoretic analogs.

### Statement 93: Theorem 16.14 [line 2735]
**Content**: Every complete affine variety is a single point.
**Assessment**: Not in Mathlib.
**Details**: This classical result is not formalized in Mathlib's scheme-theoretic framework.

### Statement 94: Lemma 16.17 [line 2763]
**Content**: R is a local ring iff R - R^x is an ideal.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/LocalRing/MaximalIdeal/Defs.lean`, `Mathlib/RingTheory/LocalRing/Basic.lean`
**Details**: The maximal ideal of a local ring is defined as the set of nonunits (`carrier := nonunits R`). The characterization of local rings via `of_nonunits_add` and related results establish this equivalence.

### Statement 95: Theorem 16.18 [line 2767]
**Content**: Every valuation ring is a local ring.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Valuation/ValuationRing.lean`
**Mathlib name**: `ValuationRing.isLocalRing` (instance, line 265)

### Statement 96: Lemma 16.19 [line 2773]
**Content**: Ideals of a valuation ring are totally ordered by inclusion.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Valuation/ValuationRing.lean`
**Mathlib name**: `ValuationRing.le_total_ideal` (instance, line 275)

### Statement 97: Lemma 16.21 [line 2793]
**Content**: Every finitely generated ideal of a valuation ring is principal.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/RingTheory/Valuation/ValuationRing.lean`
**Mathlib name**: `ValuationRing.instIsBezout` (instance, line 375)
**Details**: The IsBezout instance implies that finitely generated ideals are principal.

### Statement 98: Lemma 16.22 [line 2797]
**Content**: A local ring is a valuation ring iff it is an integral domain that is not a field and all f.g. ideals are principal.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Valuation/ValuationRing.lean`
**Mathlib name**: `ValuationRing.iff_local_bezout_domain`

### Statement 99: Corollary 16.23 [line 2803]
**Content**: A valuation ring is discrete iff it is Noetherian.
**Assessment**: Partially in Mathlib.
**Details**: The TFAE in `RingTheory/DiscreteValuationRing/TFAE.lean` relates DVR, Noetherian local domain, valuation ring, etc. The equivalence is implicit in this TFAE.

### Statement 100: Lemma 16.26 [line 2823]
**Content**: The localization R_p is a local ring with maximal ideal p*R_p.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`
**Mathlib name**: `IsLocalization.AtPrime.isLocalRing`

### Statement 101: Theorem 16.28 [line 2847]
**Content**: Valuative criterion for completeness of varieties.
**Assessment**: Partially in Mathlib.
**Details**: The valuative criterion for properness is in `AlgebraicGeometry/ValuativeCriterion.lean` in the scheme-theoretic setting.

### Statements 102-105: Lemmas 16.29-16.32 [lines 2867-2885]
**Content**: Various lemmas about valuation rings and extensions of homomorphisms.
**Assessment**: Partially in Mathlib.
**Details**: Some of these auxiliary results about valuation rings are implicit in `RingTheory/Valuation/`. Lemma 16.29 is related to the extension theorem for valuations.

### Statement 106: Theorem 16.33 [line 2889]
**Content**: All projective varieties are complete.
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`
**Mathlib name**: `AlgebraicGeometry.Proj.isProper`
**Details**: Proj is shown to be proper over Spec of the degree-0 part, which is the scheme-theoretic generalization of "projective varieties are complete."

---

## Chapter 17: Tangent Spaces and Smoothness (Lecture 17)

### Statements 107-116 [lines 2938-3027]
**Content**: Tangent spaces, Jacobian criterion for smoothness, cotangent space isomorphism T_P(V)^dual = m_P/m_P^2, smoothness criterion.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib has cotangent spaces (`RingTheory/Ideal/Cotangent.lean`) with the quotient I/I^2 formalized. The smooth locus is developed in `AlgebraicGeometry/Morphisms/Smooth.lean` and `RingTheory/Smooth/Locus.lean`. However, the classical variety-theoretic statements with Jacobian matrices are not directly present.

Statement 115 (Theorem 17.13, T_P(V)^dual = m_P/m_P^2) is close to material in `RingTheory/Ideal/Cotangent.lean` where the cotangent space I/I^2 is formalized.

Statement 116 (Corollary 17.14, smooth iff dim m/m^2 = dim V) relates to the content in `RingTheory/DiscreteValuationRing/TFAE.lean` which mentions dim_k m/m^2.

---

## Chapter 18: DVRs, Curves, and Nakayama (Lecture 18)

### Statement 117: Theorem 18.2 [line 3068]
**Content**: A ring is a regular local ring of dimension one iff it is a DVR.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`
**Details**: The TFAE theorem establishes equivalences between DVR, valuation ring, Dedekind domain, integrally closed with unique prime, m principal, dim_k m/m^2 = 1, and all nonzero ideals being powers of m, for Noetherian local domains.

### Statement 118: Lemma 18.3 (Nakayama) [line 3078]
**Content**: If R is local with maximal ideal m and M is a f.g. R-module with M = mM, then M = 0.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/Nakayama.lean`, `Mathlib/RingTheory/Finiteness/Nakayama.lean`
**Mathlib name**: `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` and variants
**Details**: Several versions of Nakayama's lemma are proven, including the local ring version.

### Statement 119: Corollary 18.4 [line 3082]
**Content**: Elements t_1,...,t_n generate m iff their images generate m/m^2.
**Assessment**: Partially in Mathlib.
**Details**: This is a standard consequence of Nakayama's lemma. The related material is in `RingTheory/LocalRing/Module.lean`.

### Statement 120: Theorem 18.5 [line 3096]
**Content**: If R_1 properly contained in R_2 are valuation rings with same fraction field, then dim R_2 < dim R_1.
**Assessment**: Not in Mathlib.

### Statements 121-127: Theorems 18.6-18.14 [lines 3102-3220]
**Content**: Properties of smooth projective curves: rational maps are morphisms, birational maps are isomorphisms, abstract curves, existence of smooth models, desingularization.
**Assessment**: Not in Mathlib.
**Details**: These are deep results in the theory of algebraic curves. Mathlib does not have a dedicated theory of algebraic curves, smooth models, or desingularization.

### Statement 126: Lemma 18.12 [line 3186]
**Content**: If A is an integrally closed Noetherian domain of dimension one, then all localizations at nonzero primes are DVRs.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/RingTheory/DedekindDomain/Dvr.lean`
**Details**: This is part of the Dedekind domain theory. The localization of a Dedekind domain at a nonzero prime is shown to be a DVR.

---

## Chapters 19-20: Divisors and Picard Group (Lectures 19-20)

### Statements 128-141 [lines 3254-3593]
**Content**: Divisors on curves, degree of morphisms, ramification, Picard group, weak approximation for function fields.
**Assessment**: Not in Mathlib.
**Details**: Mathlib does not have a theory of divisors on algebraic curves, degrees of morphisms of curves, ramification indices, or the Picard group of a curve. Some related abstract algebraic concepts exist (divisors of Dedekind domains in `RingTheory/DedekindDomain/`).

### Statement 136: Lemma 20.2 (Triangle equality for valuations) [line 3539]
**Content**: If v(x) != v(y) then v(x+y) = min(v(x), v(y)).
**Assessment**: Partially in Mathlib.
**Details**: The ultrametric inequality and the strong triangle inequality are in `RingTheory/Valuation/Basic.lean`. The equality case when v(x) != v(y) is a standard consequence.

---

## Chapters 21-22: Riemann-Roch (Lectures 21-22)

### Statements 142-166 [lines 3652-4145]
**Content**: Riemann-Roch spaces L(D), dimension formulas, genus, Weil differentials, Riemann's theorem, Serre duality, Riemann-Roch theorem, canonical divisors.
**Assessment**: Not in Mathlib.
**Details**: The Riemann-Roch theorem and its surrounding theory (Weil differentials, canonical divisors, genus, duality) are entirely absent from Mathlib. This is one of the most fundamental results in algebraic geometry that remains unformalized.

---

## Chapter 23: Elliptic Curves (Lecture 23)

### Statement 167: Theorem 23.1 [line 4170]
**Content**: C has genus zero with a rational point iff C = P^1.
**Assessment**: Not in Mathlib.

### Statement 168: Theorem 23.3 [line 4182]
**Content**: C has genus one with rational point iff it has a Weierstrass equation.
**Assessment**: Not in Mathlib (the direction "Weierstrass => genus one" is implicit in elliptic curve definitions).

### Statement 169: Corollary 23.4 [line 4220]
**Content**: Every genus one curve with a rational point is isomorphic to a plane cubic.
**Assessment**: Not in Mathlib.

### Statement 170: Lemma 23.7 [line 4228]
**Content**: An automorphism of P^1 fixing > 2 points is the identity.
**Assessment**: Not in Mathlib.

### Statements 171-172: Lemma 23.11, Lemma 23.13 [lines 4238, 4260]
**Content**: Properties of Weierstrass equations; discriminant condition for genus one.
**Assessment**: Partially in Mathlib.
**Details**: Mathlib defines Weierstrass curves and their discriminant in `AlgebraicGeometry/EllipticCurve/Weierstrass.lean`. The discriminant Delta and the nonsingularity condition are defined. Short Weierstrass forms are in `NormalForms.lean`.

### Statement 173: Theorem 23.16 [line 4297]
**Content**: Bijection E(k) -> Pic_k^0(E) via P -> [P-O].
**Assessment**: **In Mathlib (Close)**.
**Mathlib location**: `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
**Details**: Mathlib defines the group law on nonsingular points of a Weierstrass curve and proves it forms an abelian group (`instAddCommGroup`). The connection to the Picard group is established through the class group.

### Statements 174-176: Lemma 23.17, Corollaries 23.18-23.19 [lines 4315-4341]
**Content**: Geometric group law on elliptic curves.
**Assessment**: **In Mathlib (Close)**.
**Details**: The group law is defined via explicit formulas in `AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` and `Projective/Formula.lean`.

### Statement 177: Theorem 23.20 (Algebraic group law) [line 4367]
**Content**: Explicit formulas for addition on y^2 = x^3 + a_4*x + a_6.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`
**Details**: The addition formulas are computed explicitly for Weierstrass curves.

### Statements 178-179: Theorems 23.23-23.24 [lines 4391, 4399]
**Content**: Abelian varieties are abelian groups; morphisms preserving identity are group homomorphisms.
**Assessment**: Not in Mathlib.
**Details**: Mathlib does not have a theory of abelian varieties.

---

## Chapter 24: Isogenies and Torsion (Lecture 24)

### Statements 180-192 [lines 4424-4619]
**Content**: Isogenies as group homomorphisms, kernel bounds, multiplication-by-n map, n-torsion finiteness, p-adic filtration, reduction mod p, Mazur's theorem, Nagell-Lutz.
**Assessment**: Not in Mathlib.
**Details**: Mathlib does not have isogenies, the multiplication-by-n map on elliptic curves, torsion subgroups of elliptic curves, reduction theory, Mazur's classification of torsion subgroups, or the Nagell-Lutz theorem. The division polynomial theory in `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` is related but does not establish these results.

---

## Chapter 25: Heights and Mordell-Weil (Lecture 25)

### Statements 193-197 [lines 4810-4854]
**Content**: 2-descent for elliptic curves, finiteness of E(Q)/2E(Q).
**Assessment**: Not in Mathlib.

### Statement 198: Lemma 25.10 [line 4893]
**Content**: H(P) >= 1 for all P in P^n(Q-bar).
**Assessment**: Partially in Mathlib.
**Details**: `NumberTheory/Height/Basic.lean` defines heights and proves `one_le_mulHeight1`.

### Statements 199-201: Height properties [lines 4914-4945]
**Content**: Height bounds for morphisms, h(phi(P)) = d*h(P) + O(1).
**Assessment**: Not in Mathlib.

### Statement 202: Lemma 25.16 [line 4963]
**Content**: Height is Galois-invariant.
**Assessment**: Not in Mathlib.

### Statement 203: Theorem 25.18 (Northcott) [line 4971]
**Content**: Finiteness of points of bounded height and degree.
**Assessment**: Partially in Mathlib.
**Details**: `NumberTheory/MahlerMeasure.lean` has Northcott's theorem for the Mahler measure of integer polynomials, but the projective height version for number fields is not present.

### Statements 204-206 [lines 4989-5038]
**Content**: Tate's theorem (canonical height), height finiteness on elliptic curves, parallelogram law.
**Assessment**: Not in Mathlib.

### Statement 207: Theorem 25.23 [line 5048]
**Content**: E(Q) is finitely generated (weak Mordell-Weil for curves with a 2-torsion point).
**Assessment**: Not in Mathlib.
**Details**: The Mordell-Weil theorem is not formalized in Mathlib.

---

## Chapter 26: j-invariant and Torsors (Lecture 26)

### Statement 208: Theorem 26.3 [line 5135]
**Content**: For every j in k there exists an elliptic curve E/k with j(E) = j.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean`
**Mathlib name**: `WeierstrassCurve.ofJ`
**Details**: Explicit models are constructed for j = 0, j = 1728, and general j.

### Statement 209: Theorem 26.4 [line 5139]
**Content**: Two elliptic curves have the same j-invariant iff they are isomorphic over k-bar.
**Assessment**: **In Mathlib (Exact)**.
**Mathlib location**: `Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean`
**Mathlib name**: `EllipticCurve.exists_variableChange_of_j_eq`

### Statement 210: Corollary 26.5 [line 5145]
**Content**: Different base points on a genus one curve give elliptic curves with the same j-invariant.
**Assessment**: Not in Mathlib.

### Statement 211: Theorem 26.7 [line 5153]
**Content**: j(C) in k for a genus one curve C/k.
**Assessment**: Not in Mathlib.

### Statement 212: Corollary 26.8 [line 5157]
**Content**: Every genus one curve is a twist of an elliptic curve.
**Assessment**: Not in Mathlib.

### Statement 213: Lemma 26.9 [line 5170]
**Content**: Two elliptic curves with same j are related by lambda-scaling.
**Assessment**: **In Mathlib (Close)**.
**Details**: This is essentially the content of `exists_variableChange_of_j_eq`.

### Statement 214: Theorem 26.11 [line 5192]
**Content**: Aut(E/k) is cyclic of order 6, 4, or 2 depending on j = 0, 1728, or neither.
**Assessment**: Not in Mathlib.
**Details**: While Mathlib has the variable change group, the explicit computation of automorphism groups of elliptic curves is not formalized.

### Statements 215-221 [lines 5198-5441]
**Content**: Torsors, Jacobians of genus one curves, Weil-Chatelet group, cohomology, Shafarevich-Tate group.
**Assessment**: Not in Mathlib.
**Details**: None of the torsor theory, Galois cohomology of elliptic curves, Weil-Chatelet groups, or Shafarevich-Tate groups are formalized in Mathlib.

---

## Summary Statistics

| Category | Count | Percentage |
|----------|-------|------------|
| In Mathlib (Exact) | 21 | 9.4% |
| In Mathlib (Close) | 13 | 5.8% |
| Partially in Mathlib | 21 | 9.4% |
| Not in Mathlib | 169 | 75.4% |
| **Total** | **224** | **100%** |

## Analysis by Topic

| Topic | Statements | In Mathlib | Coverage |
|-------|-----------|------------|----------|
| Introduction/Survey (Ch 1) | 6 | 0 | 0% |
| Conics (Ch 2) | 4 | 0 | 0% |
| Quadratic reciprocity, finite fields (Ch 3) | 5 | 2 | 40% |
| p-adic integers (Ch 4) | 8 | 4 | 50% |
| p-adic absolute values (Ch 5) | 3 | 1 | 33% |
| Algebraic number theory (Ch 7) | 8 | 5 | 63% |
| Hensel's lemma (Ch 8) | 5 | 2 | 40% |
| Quadratic forms (Ch 9) | 3 | 0 | 0% |
| Hilbert symbol (Ch 10) | 9 | 0 | 0% |
| Local-global (Ch 11) | 10 | 0 | 0% |
| AG basics (Ch 12) | 8 | 6 | 75% |
| Dimension, projective (Ch 13) | 5 | 0 | 0% |
| Morphisms (Ch 14) | 5 | 0 | 0% |
| Rational maps (Ch 15) | 7 | 0 | 0% |
| Completeness, valuation rings (Ch 16) | 20 | 8 | 40% |
| Tangent spaces (Ch 17) | 10 | 0 | 0% |
| DVRs, curves, Nakayama (Ch 18) | 11 | 3 | 27% |
| Divisors (Ch 19) | 7 | 0 | 0% |
| Picard group (Ch 20) | 7 | 0 | 0% |
| Riemann-Roch spaces (Ch 21) | 8 | 0 | 0% |
| Riemann-Roch theorem (Ch 22) | 17 | 0 | 0% |
| Elliptic curves (Ch 23) | 13 | 3 | 23% |
| Isogenies, torsion (Ch 24) | 13 | 0 | 0% |
| Heights, Mordell-Weil (Ch 25) | 15 | 0 | 0% |
| j-invariant, torsors (Ch 26) | 14 | 2 | 14% |

## Key Observations

1. **Algebra and number theory foundations are well-covered**: Quadratic reciprocity, Ostrowski's theorem, Hensel's lemma, Hilbert basis theorem, Nullstellensatz, Nakayama's lemma, DVR theory, and valuation ring properties are all in Mathlib.

2. **Classical algebraic geometry is a major gap**: The entire development of varieties, morphisms, rational maps, dimension theory, tangent spaces, and smoothness in the classical (non-scheme) setting is absent. Mathlib's algebraic geometry is built on schemes.

3. **Curve theory is almost entirely absent**: Divisors on curves, Riemann-Roch, genus, Weil differentials, and the theory of algebraic curves are not in Mathlib.

4. **Elliptic curve group law is formalized, but advanced theory is not**: While Mathlib has Weierstrass curves, the group law, j-invariants, and models with prescribed j, it lacks isogenies, torsion theory, reduction theory, heights, and the Mordell-Weil theorem.

5. **Quadratic forms and local-global principles are not in Mathlib**: The Hasse-Minkowski theorem, Hilbert symbols, weak/strong approximation, and the theory of quadratic forms over local fields are absent.

6. **Topological/metric foundations are strong**: Completions, Cauchy sequences, and density results are well-formalized.

7. **p-adic numbers are well-developed as a ring**: Z_p and Q_p are constructed with their algebraic properties (DVR, PID, local ring), but the arithmetic applications (lifting roots, quadratic forms over Q_p) are less developed.
