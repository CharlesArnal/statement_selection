# Short Assessment: Introduction to Arithmetic Geometry vs Mathlib

## Summary

- **Total statements found**: 224 (including 3 duplicates in Ch 1)
- **Statements with close mathlib match**: ~30
- **Statements with partial/related mathlib coverage**: ~25
- **Statements not in mathlib**: ~169

**Overall coverage: approximately 13% exact match, 24% if including partial matches.**

## Statements Found in Mathlib

| # | Statement | Mathlib Location | Match Quality |
|---|-----------|-----------------|---------------|
| 11 | Theorem 3.1 (Quadratic Reciprocity) | `NumberTheory.LegendreSymbol.QuadraticReciprocity` | Exact |
| 12 | Theorem 3.3 (Finite subgroup of mult. group is cyclic) | `RingTheory.IntegralDomain.isCyclic_of_subgroup_isDomain` | Exact |
| 20 | Corollary 4.13 (Z_p is integral domain) | `NumberTheory.Padics.PadicIntegers` (IsDomain instance) | Exact |
| 22 | Theorem 4.16 (Ideals of Z_p are (p^m)) | `NumberTheory.Padics.PadicIntegers` (IsDiscreteValuationRing instance) | Close |
| 23 | Corollary 4.17 (Z_p is PID with unique maximal ideal) | `NumberTheory.Padics.PadicIntegers` (IsDiscreteValuationRing, maximalIdeal_eq_span_p) | Close |
| 26 | Theorem 5.6 (Ostrowski) | `NumberTheory.Ostrowski.equiv_real_or_padic` | Exact |
| 31 | Theorem 7.10 (Convergent => Cauchy) | `Topology.UniformSpace.Cauchy` (Filter.Tendsto.cauchy_map) | Exact |
| 32 | Theorem 7.15 (k dense in completion) | `Topology.UniformSpace.Completion.denseRange_coe` | Exact |
| 34 | Corollary 7.17 (Completion is complete) | `Topology.UniformSpace.Completion.completeSpace` | Exact |
| 36 | Lemma 8.3 (Inverse limit of finite nonempty sets nonempty) | `CategoryTheory.CofilteredSystem.nonempty_sections_of_finite_inverse_system` | Close |
| 39 | Theorem 8.8 (Hensel's lemma) | `NumberTheory.Padics.Hensel.hensels_lemma` | Exact |
| 62 | Theorem 12.2 (Transcendence bases have same cardinality) | `RingTheory.AlgebraicIndependent.RankAndCardinality` | Close |
| 63 | Theorem 12.11 (Hilbert basis theorem) | `RingTheory.Polynomial.Basic` (Hilbert basis theorem) | Exact |
| 64 | Lemma 12.14 (Radical of ideal is an ideal) | `RingTheory.Ideal.Operations` (radical definition) | Exact |
| 65 | Theorem 12.15 (Nullstellensatz) | `RingTheory.Nullstellensatz.vanishingIdeal_zeroLocus_eq_radical` | Exact |
| 66 | Theorem 12.16 (Weak Nullstellensatz) | `RingTheory.Nullstellensatz` (maximal ideal characterization) | Close |
| 67 | Corollary 12.17 (Maximal ideals are (x_1-a_1,...)) | `RingTheory.Nullstellensatz.eq_vanishingIdeal_singleton_of_isMaximal` | Close |
| 87 | Theorem 16.1 (Quasi-compactness of Zariski topology) | `RingTheory.Spectrum.Prime.Topology.compactSpace` | Close |
| 94 | Lemma 16.17 (Local ring iff R - R^x is ideal) | `RingTheory.LocalRing` (maximalIdeal defined as nonunits) | Exact |
| 95 | Theorem 16.18 (Valuation ring is local) | `RingTheory.Valuation.ValuationRing.isLocalRing` | Exact |
| 96 | Lemma 16.19 (Ideals of valuation ring are totally ordered) | `RingTheory.Valuation.ValuationRing.le_total_ideal` | Exact |
| 97 | Lemma 16.21 (f.g. ideals of valuation ring are principal) | `RingTheory.Valuation.ValuationRing` (IsBezout instance) | Close |
| 98 | Lemma 16.22 (Local + Bezout <=> valuation ring) | `RingTheory.Valuation.ValuationRing.iff_local_bezout_domain` | Exact |
| 100 | Lemma 16.26 (Localization at prime is local ring) | `RingTheory.Localization.AtPrime.isLocalRing` | Exact |
| 117 | Theorem 18.2 (Regular local ring dim 1 <=> DVR) | `RingTheory.DiscreteValuationRing.TFAE` | Exact |
| 118 | Lemma 18.3 (Nakayama's lemma) | `RingTheory.Nakayama` / `RingTheory.Finiteness.Nakayama` | Exact |
| 126 | Lemma 18.12 (Integrally closed Noetherian dim 1 => localizations are DVRs) | `RingTheory.DedekindDomain.Dvr` | Exact |
| 173 | Theorem 23.16 (Group law via Picard group bijection) | `AlgebraicGeometry.EllipticCurve.Affine.Point` (instAddCommGroup) | Close |
| 208 | Theorem 26.3 (Existence of EC with given j-invariant) | `AlgebraicGeometry.EllipticCurve.ModelsWithJ` | Exact |
| 209 | Theorem 26.4 (Same j => isomorphic over k-bar) | `AlgebraicGeometry.EllipticCurve.IsomOfJ.exists_variableChange_of_j_eq` | Exact |

## Statements NOT in Mathlib (Notable Absences)

- Hasse bound / Weil conjectures for curves (Theorems in Ch 1)
- Fermat's Last Theorem (Wiles)
- Faltings' theorem (Mordell conjecture)
- Hasse-Minkowski theorem (Theorems 9.10, 11.12)
- Hilbert symbol properties (Chapter 10)
- Weak/strong approximation theorems (Theorems 11.7, 11.8)
- Riemann-Roch theorem (Theorem 22.21) and all Weil differential results
- Mazur's torsion theorem (Theorem 24.20)
- Nagell-Lutz theorem (Theorem 24.21)
- Mordell-Weil theorem / finite generation of E(Q) (Theorem 25.23)
- Northcott's theorem for projective height (Theorem 25.18)
- Automorphism groups of elliptic curves (Theorem 26.11)
- Isogenies and dual isogenies (Chapter 24)
- Weil-Chatelet group and Shafarevich-Tate group (Chapter 26)
- All algebraic geometry results on varieties, morphisms, birational equivalence (Chapters 13-17)
- Genus and curve classification results (Chapters 21-23)
