# Detailed Assessment: Intersection Theory on Moduli Spaces vs. Mathlib

## Overview

This document provides a statement-by-statement assessment of every formal mathematical statement found in the textbook "Intersection Theory on Moduli Spaces" against the mathlib library (v4.27.0). The textbook is an advanced treatment of algebraic geometry covering Grassmannians, moduli spaces of curves, Hilbert schemes, GIT quotients, Brill-Noether theory, and the Kodaira dimension of M_g.

**Overall result: 5 of 91 statements have any form of mathlib coverage (partial or full), and only 2 have a direct formalization.**

---

## Part 1: The Grassmannian (Chapter 2)

### Theorem 2.1 (Line 89) -- Schubert classes form a basis of Grassmannian cohomology
**Mathlib status: NOT IN MATHLIB**

Mathlib defines the Grassmannian `Module.Grassmannian R M k` in `Mathlib/RingTheory/Grassmannian.lean` as the set of submodules of M whose quotient is locally free of rank k. However, there is no cohomology theory for algebraic varieties in mathlib, no definition of Schubert varieties, and no Schubert classes. The entire framework of intersection theory and cell decompositions is absent. The Grassmannian in mathlib is purely at the commutative-algebra level (a set, not yet a scheme).

### Theorem 2.6 (Line 115) -- Kleiman's Transversality Theorem
**Mathlib status: NOT IN MATHLIB**

This requires algebraic group actions, transitive group actions on schemes, generic transversality, and fiber product dimension formulas. None of these are in mathlib. Mathlib has no theory of algebraic groups acting on schemes, no generic fiber dimension results, and no transversality statements.

### Lemma 2.7 (Line 124) -- Flatness and generic equidimensionality
**Mathlib status: NOT IN MATHLIB**

Requires flat morphisms with equidimensional fibers and generic smoothness. While mathlib has the definition of flat morphisms (`AlgebraicGeometry.Morphisms.Flat`), it lacks generic smoothness theorems and fiber dimension theory.

### Theorem 2.8 (Line 148) -- Cohomology ring of G(k,n)
**Mathlib status: NOT IN MATHLIB**

Requires cohomology ring structure, Chern classes of tautological/quotient bundles, and the presentation as a quotient ring. None of these exist in mathlib. Mathlib has no Chern classes, no cohomology rings, and no vector bundles on the Grassmannian.

### Proposition 2.9 (Line 156) -- Chern classes of tautological bundle as Schubert cycles
**Mathlib status: NOT IN MATHLIB**

Same obstacles as Theorem 2.8. No Chern classes or Schubert cycles in mathlib.

### Theorem 2.10 (Line 166) -- Pieri's Formula
**Mathlib status: NOT IN MATHLIB**

A combinatorial formula for multiplying a special Schubert cycle with an arbitrary Schubert cycle. No Schubert calculus exists in mathlib. No Pieri formula, no related combinatorics in the Grassmannian context.

### Theorem 2.12 (Line 178) -- Giambelli's Formula
**Mathlib status: NOT IN MATHLIB**

Expresses arbitrary Schubert cycles as determinants of special Schubert cycles. Same fundamental absence of Schubert calculus machinery.

### Theorem 2.18 (Line 235) -- Representability of Grassmannian functor
**Mathlib status: PARTIAL**

**Mathlib file:** `Mathlib/RingTheory/Grassmannian.lean`

The Grassmannian is defined in mathlib as a structure `Module.Grassmannian R M k` -- the set of submodules whose quotient is locally free of rank k. This is the correct definition at the module level. However, the TODO list in the file explicitly states that the following are NOT yet done:
- The Grassmannian functor sending an R-algebra A to G(k, A tensor_R M; A)
- Charts and their functorial properties
- The scheme structure on the Grassmannian
- **Representability of the Grassmannian functor**

So the definition exists but the representability theorem itself is not proved. This is a **partial match**: the mathematical object is defined but the key theorem about it is absent.

---

## Part 2: Littlewood-Richardson Rule (Chapter 3)

### Theorem 3.1 (Line 338) -- Mondrian tableaux LR rule
**Mathlib status: NOT IN MATHLIB**

A combinatorial rule for computing Littlewood-Richardson coefficients using Mondrian tableaux. No Littlewood-Richardson coefficients, no Schubert calculus, no Mondrian tableaux in mathlib.

---

## Part 3: Chow Rings of M_{0,n}-bar

### Theorem 1.1 (Line 380) -- Chow ring of blow-ups
**Mathlib status: NOT IN MATHLIB**

Requires blow-ups of smooth varieties, Chow rings, normal bundles, Chern classes, and the structure of the exceptional divisor. Mathlib has none of these. There is no concept of blow-up in mathlib's algebraic geometry, and no Chow theory at all.

### Theorem 1.2 (Line 398) -- Keel's theorem on Chow ring of M_{0,n}-bar
**Mathlib status: NOT IN MATHLIB**

Requires the moduli space M_{0,n}-bar, its boundary divisors, and Chow ring presentation. Entirely absent from mathlib.

### Theorem 1.10 (Line 471) -- Vanishing of homology of affine varieties
**Mathlib status: NOT IN MATHLIB**

This is a result about singular homology of smooth complex affine varieties (Lefschetz hyperplane theorem type result). Mathlib has no singular homology for algebraic varieties.

### Proposition 1.13 (Line 485) -- Basis for H^2 of M_{0,n}-bar
**Mathlib status: NOT IN MATHLIB**

Requires M_{0,n}-bar and its cohomology. Not in mathlib.

---

## Part 4: Cohomology of M_{g,n}-bar

### Theorem 2.1 (Line 519) -- Generators of H^2(M_{g,n}-bar)
**Mathlib status: NOT IN MATHLIB**

Requires the moduli stack M_{g,n}-bar, tautological classes (kappa, psi, delta), and cohomology. None exist in mathlib.

### Proposition 2.2 (Line 552) -- Restriction to boundary injectivity
**Mathlib status: NOT IN MATHLIB**

### Proposition 2.3 (Line 566) -- Boundary component cohomology
**Mathlib status: NOT IN MATHLIB**

### Proposition 2.4 (Line 578) -- Injectivity of gluing pullback
**Mathlib status: NOT IN MATHLIB**

### Lemma 2.9 (Line 640) -- Mumford's relation (kappa = 12 lambda - delta + psi)
**Mathlib status: NOT IN MATHLIB**

One of the fundamental relations in the theory of moduli of curves. Requires the Hodge bundle, tautological classes, and Grothendieck-Riemann-Roch. None of these are in mathlib.

---

## Part 5: Vanishing of Odd Cohomology

### Theorem 3.1 (Line 709) -- Vanishing of H^1, H^3, H^5 of M_{g,n}-bar
**Mathlib status: NOT IN MATHLIB**

### Lemma 3.2 (Line 719) -- Reduction Lemma for odd cohomology
**Mathlib status: NOT IN MATHLIB**

---

## Part 6: Picard Group of Moduli Space

### Theorem 4.1 (Line 814) -- Picard group of M_g-bar
**Mathlib status: NOT IN MATHLIB**

While mathlib has a Picard group for commutative rings (`Mathlib/RingTheory/PicardGroup.lean`), this is purely algebraic (invertible modules up to isomorphism). The Picard group of the moduli stack M_g-bar is a geometric object requiring divisor class groups on stacks, which is entirely absent from mathlib. This is a **tangential connection** at best -- the underlying concept of "Picard group" exists in a completely different context.

### Theorem 4.2 (Line 818) -- Picard group of M_{g,n}-bar
**Mathlib status: NOT IN MATHLIB**

Same reasoning as Theorem 4.1.

---

## Part 7: Construction of Moduli Space

### Theorem 1.7 (Line 963) -- Deligne-Mumford-Knudsen existence of coarse moduli space
**Mathlib status: NOT IN MATHLIB**

This is one of the foundational theorems of the field. Mathlib has no moduli spaces, no stacks, no stable curves, and no coarse moduli space construction. The concept of a Deligne-Mumford stack does not exist in mathlib.

---

## Part 8: Hilbert Schemes

### Theorem 2.2 (Line 979) -- Representability of Hilbert functor (Grothendieck)
**Mathlib status: NOT IN MATHLIB**

One of the most important representability results in algebraic geometry. Mathlib has the Hilbert polynomial (`Mathlib/RingTheory/Polynomial/HilbertPoly.lean`) but this is purely about the polynomial itself, not the Hilbert scheme. There is no Hilbert functor, no Hilbert scheme, and no representability result.

### Theorem 2.3 (Line 991) -- Castelnuovo-Mumford regularity bound
**Mathlib status: NOT IN MATHLIB**

Requires coherent sheaf cohomology on projective space, which is not in mathlib.

### Proposition 2.5 (Line 1007) -- Regularity cascade
**Mathlib status: NOT IN MATHLIB**

### Proposition 2.6 (Line 1067) -- Flattening stratification
**Mathlib status: NOT IN MATHLIB**

A key technical result about coherent sheaves. Mathlib has no flattening stratification.

### Proposition 2.8 (Line 1122) -- Unique flat extension over DVR
**Mathlib status: NOT IN MATHLIB**

While mathlib has DVR theory, it does not have flat extensions of subschemes over DVRs.

### Theorem 2.16 (Line 1149) -- Zariski tangent space to Hilbert scheme
**Mathlib status: NOT IN MATHLIB**

Requires Hilbert scheme + identification of tangent space with Hom(I/I^2, O_Y). While mathlib has cotangent modules (`Mathlib/RingTheory/Ideal/Cotangent.lean`), the Hilbert scheme context is missing.

### Theorem 2.18 (Line 1159) -- Cohomology of projective bundle
**Mathlib status: NOT IN MATHLIB**

Requires projective bundles and their cohomology ring structure. Mathlib has no projective bundles in the algebraic geometry sense and no cohomology ring.

### Theorem 2.27 (Line 1214) -- Murphy's Law for Hilbert schemes
**Mathlib status: NOT IN MATHLIB**

A deep result about the "universality" of singularities in Hilbert schemes. Far beyond mathlib's reach.

---

## Part 9: Stable Reduction

### Theorem 4.1 (Line 1237) -- Stable reduction theorem
**Mathlib status: NOT IN MATHLIB**

Requires stable curves, DVRs, base change for curves. While mathlib has DVR theory, there is no stable curve theory.

---

## Part 10: Stacks and Valuative Criteria

### Theorem 5.9 (Line 1356) -- Criterion for Deligne-Mumford stacks
**Mathlib status: NOT IN MATHLIB**

Mathlib has no algebraic stacks of any kind.

### Theorem 5.10 (Line 1369) -- Valuative criterion for separatedness (stacks)
**Mathlib status: YES (for schemes, not stacks)**

**Mathlib file:** `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean`

The valuative criterion for separatedness is formalized in mathlib for morphisms of schemes:
```
IsSeparated.eq_valuativeCriterion :
    @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated
```
This says a morphism is separated iff it is quasi-separated and satisfies the uniqueness part of the valuative criterion. The textbook states the result for Deligne-Mumford stacks, which is a more general context. But the scheme-level result is a **full match** for the scheme case.

### Theorem 5.11 (Line 1373) -- Valuative criterion of properness (stacks)
**Mathlib status: YES (for schemes, not stacks)**

**Mathlib file:** `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean`

Similarly formalized for schemes:
```
IsProper.eq_valuativeCriterion :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType
```
This says a morphism is proper iff it is qcqs, locally of finite type, and satisfies the full valuative criterion. Again, the textbook states this for stacks, but the scheme version is a **full match**.

### Theorem 5.12 (Line 1379) -- Keel-Mori theorem (coarse moduli from DM stacks)
**Mathlib status: NOT IN MATHLIB**

Requires DM stacks and algebraic spaces, neither of which exist in mathlib.

---

## Part 11: GIT

### Lemma 6.1 (Line 1395) -- Invariant separation of orbits
**Mathlib status: NOT IN MATHLIB**

Requires geometrically reductive groups and invariant theory in the algebraic geometry sense. Not in mathlib.

### Theorem 6.2 (Line 1401) -- Existence of GIT quotient
**Mathlib status: NOT IN MATHLIB**

GIT quotients are not defined in mathlib. The entire theory of geometric invariant theory is absent.

### Theorem 6.3 (Line 1414) -- Haboush's theorem (reductive = geometrically reductive)
**Mathlib status: NOT IN MATHLIB**

Requires algebraic group theory (reductive groups, geometrically reductive groups). Mathlib has representation theory infrastructure but not these algebraic geometry notions.

### Theorem 6.4 (Line 1416) -- Nagata's theorem (finite generation of invariant ring)
**Mathlib status: NOT IN MATHLIB**

While mathlib has `Mathlib/RingTheory/Invariant/` dealing with invariant subrings in the Galois theory context, Nagata's theorem about finite generation of invariant rings under geometrically reductive group actions is not formalized.

### Theorem 6.11 (Line 1465) -- GIT quotient for projective varieties
**Mathlib status: NOT IN MATHLIB**

### Theorem 6.13 (Line 1484) -- Hilbert-Mumford numerical criterion
**Mathlib status: NOT IN MATHLIB**

Requires one-parameter subgroups, the numerical function mu, and stability notions.

### Theorem 6.18 (Line 1523) -- Hilbert stability of smooth curves
**Mathlib status: NOT IN MATHLIB**

### Theorem 6.21 (Line 1542) -- Potential stability
**Mathlib status: NOT IN MATHLIB**

### Lemma 6.22 (Line 1548) -- Closure of H^{ss}
**Mathlib status: NOT IN MATHLIB**

### Lemma 6.23 (Line 1554) -- Hilbert semistable implies DM stable
**Mathlib status: NOT IN MATHLIB**

### Lemma 6.24 (Line 1558) -- DM stable curves have models in H^{ss}
**Mathlib status: NOT IN MATHLIB**

### Lemma 6.25 (Line 1562) -- H^{ss} implies Hilbert stable
**Mathlib status: NOT IN MATHLIB**

### Theorem 6.27 (Line 1576) -- Projectivity of M_g-bar
**Mathlib status: NOT IN MATHLIB**

### Theorem 6.28 (Line 1578) -- Irreducibility of M_g-bar
**Mathlib status: NOT IN MATHLIB**

### Claim 6.29 (Line 1584) -- Hilbert stable curves not in hyperplane
**Mathlib status: NOT IN MATHLIB**

---

## Part 12: Topology of Moduli Space

### Theorem 1.4 (Line 1665) -- Uniformization of Riemann surfaces
**Mathlib status: NOT IN MATHLIB**

A foundational result of complex analysis/geometry. Mathlib has no Riemann surfaces and no uniformization theorem.

### Theorem 1.6 (Line 1669) -- Homeomorphisms of S^2 isotopic to identity
**Mathlib status: NOT IN MATHLIB**

This is a statement in low-dimensional topology. Mathlib has no isotopy theory or mapping class groups.

### Lemma 1.8 (Line 1686) -- Trace vs. geodesic length on hyperbolic surfaces
**Mathlib status: NOT IN MATHLIB**

Requires hyperbolic geometry and Fuchsian groups. Not in mathlib.

### Lemma 1.9 (Line 1709) -- Right-angled hexagons in hyperbolic plane
**Mathlib status: NOT IN MATHLIB**

### Proposition 1.11 (Line 1725) -- Teichmuller modular group acts properly discontinuously
**Mathlib status: NOT IN MATHLIB**

Teichmuller space is not defined in mathlib (the "Teichmuller" files in mathlib are about Teichmuller representatives in Witt vectors, a completely unrelated concept).

### Lemma 1.12 (Line 1729) -- Discreteness of geodesic length spectrum
**Mathlib status: NOT IN MATHLIB**

### Theorem 3.1 (Line 1945) -- Homotopy type of M_{g,n}
**Mathlib status: NOT IN MATHLIB**

### Theorem 3.3 (Line 1974) -- Harer stability for mapping class groups
**Mathlib status: NOT IN MATHLIB**

Homological stability is not addressed in mathlib.

### Theorem 3.4 (Line 1987) -- Mumford's Conjecture (Madsen-Weiss theorem)
**Mathlib status: NOT IN MATHLIB**

One of the deepest results about moduli of curves, proved by Madsen-Weiss. Far beyond mathlib.

### Lemma 4.2 (Line 2010) -- Dehn twist reduction of intersections
**Mathlib status: NOT IN MATHLIB**

Requires surface topology and Dehn twists. Not in mathlib.

### Lemma 4.3 (Line 2018) -- Multi-curve Dehn twist reduction
**Mathlib status: NOT IN MATHLIB**

### Lemma 4.4 (Line 2022) -- Meridian fixed by Dehn twist sequence
**Mathlib status: NOT IN MATHLIB**

### Proposition 4.5 (Line 2068) -- Vanishing of H_1 of mapping class group
**Mathlib status: NOT IN MATHLIB**

---

## Part 13: Kontsevich Moduli Space

### Theorem 1.7 (Line 2230) -- Existence of Kontsevich moduli space
**Mathlib status: NOT IN MATHLIB**

Requires stable maps, Kontsevich moduli spaces. Entirely absent from mathlib.

### Theorem 1.10 (Line 2249) -- Smoothness for convex targets
**Mathlib status: NOT IN MATHLIB**

### Lemma 1.14 (Line 2288) -- Transverse intersection on homogeneous spaces
**Mathlib status: NOT IN MATHLIB**

### Theorem 1.21 (Line 2384) -- Quantum cohomology is associative
**Mathlib status: NOT IN MATHLIB**

Quantum cohomology does not exist in mathlib.

### Theorem 2.1 (Line 2455) -- Pandharipande: divisors on M_{0,n}(P^r, d)
**Mathlib status: NOT IN MATHLIB**

### Claims 2.2-2.5 (Lines 2461-2477) -- Generator claims for divisor group
**Mathlib status: NOT IN MATHLIB**

### Proposition 2.8 (Line 2499) -- Enumerative counts via intersection theory
**Mathlib status: NOT IN MATHLIB**

---

## Part 14: Divisors on Kontsevich Space

### Theorem 3.3 (Line 2575) -- Vakil's result on D_H components
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.1 (Line 2625) -- Injective map on Picard groups
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.2 (Line 2690) -- Picard group isomorphism and cone structure
**Mathlib status: NOT IN MATHLIB**

### Lemmas 4.5-4.7, Proposition 4.8 (Lines 2730-2777) -- NEF divisor properties
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.9 (Line 2833) -- Contraction morphism
**Mathlib status: NOT IN MATHLIB**

### Proposition 4.12 (Line 2855) -- Effective cone containment
**Mathlib status: NOT IN MATHLIB**

### Lemma 4.13 (Line 2889) -- D_deg class formula
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.14 (Line 2918) -- Effective cone of M_{0,0}(P^d, d)
**Mathlib status: NOT IN MATHLIB**

### Lemma 4.16 (Line 2928) -- Moving curve criterion
**Mathlib status: NOT IN MATHLIB**

### Proposition 4.17 (Line 2949) -- Linear system properties
**Mathlib status: NOT IN MATHLIB**

---

## Part 15: Kodaira Dimension of M_g

### Lemma 1.5 (Line 3051) -- Characterization of big line bundles
**Mathlib status: NOT IN MATHLIB**

Requires the concept of "big" line bundles, Iitaka dimension, and section growth. Not in mathlib.

### Lemma 1.6 (Line 3060) -- Kodaira's Lemma
**Mathlib status: NOT IN MATHLIB**

Despite the name appearing in mathlib search results, there is no Kodaira's Lemma in the algebraic geometry sense. The hits are false positives from unrelated code.

### Proposition 1.7 (Line 3078) -- Equivalent characterizations of big divisors
**Mathlib status: NOT IN MATHLIB**

### Theorem 2.1 (Line 3095) -- Canonical class of M_g-bar
**Mathlib status: NOT IN MATHLIB**

### Theorem 3.2 (Line 3129) -- Ample cone of M_g-bar (a lambda - b delta ample iff a > 11b)
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.1 (Line 3139) -- M_g-bar is of general type for g >= 24 (Harris-Mumford, Eisenbud-Harris)
**Mathlib status: NOT IN MATHLIB**

One of the landmark results about moduli of curves. Far beyond mathlib.

### Theorem 4.2 (Line 3161) -- Extension of pluricanonical forms
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.3 (Line 3173) -- Automorphism action on stable curves
**Mathlib status: NOT IN MATHLIB**

### Lemma 4.4 (Line 3182) -- Automorphism action on smooth curves
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.5 (Line 3199) -- Brill-Noether divisor class
**Mathlib status: NOT IN MATHLIB**

### Theorem 4.8 (Line 3223) -- Petri divisor class
**Mathlib status: NOT IN MATHLIB**

---

## Part 16: Brill-Noether Theory

### Proposition 5.3 (Line 3267) -- Existence of low-degree meromorphic functions
**Mathlib status: NOT IN MATHLIB**

### Theorem 5.4 (Line 3271) -- Brill-Noether theorem (dimension of W_d^r)
**Mathlib status: NOT IN MATHLIB**

A foundational theorem of algebraic curve theory. Not in mathlib.

### Theorem 5.6 (Line 3283) -- Eisenbud-Harris osculating flag transversality
**Mathlib status: NOT IN MATHLIB**

### Proposition 5.7 (Line 3291) -- Plucker formula for ramification
**Mathlib status: NOT IN MATHLIB**

### Theorem 5.9 (Line 3329) -- Gieseker-Petri theorem
**Mathlib status: NOT IN MATHLIB**

### Proposition 5.12 (Line 3354) -- Equivalent conditions for limit linear series
**Mathlib status: NOT IN MATHLIB**

### Theorem 5.14 (Line 3396) -- Limit linear series on tree-like curves
**Mathlib status: NOT IN MATHLIB**

### Theorem 5.16 (Line 3421) -- Brill-Noether divisor class (repeated)
**Mathlib status: NOT IN MATHLIB**

---

## Part 17: The F-Conjecture

### Theorem 6.8 (Line 3530) -- Reduction of F-conjecture to genus 0
**Mathlib status: NOT IN MATHLIB**

---

## Summary of Mathlib Coverage by Topic Area

| Topic Area | Statements | In Mathlib | Notes |
|------------|-----------|------------|-------|
| Grassmannian / Schubert calculus | 9 | 1 partial | Grassmannian defined but not as scheme; no Schubert theory |
| Chow rings of M_{0,n}-bar | 4 | 0 | No Chow theory, no M_{0,n} |
| Cohomology of M_{g,n}-bar | 7 | 0 | No moduli spaces, no tautological classes |
| Picard group of moduli | 2 | 0 | Picard group exists for rings only |
| Moduli space construction | 1 | 0 | No stacks, no coarse moduli spaces |
| Hilbert schemes | 8 | 0 | No Hilbert functor/scheme |
| Stable reduction | 1 | 0 | No stable curves |
| Stacks and valuative criteria | 4 | 2 | Valuative criteria for schemes only |
| GIT | 14 | 0 | No GIT, no reductive groups |
| Topology of moduli | 14 | 0 | No Teichmuller, no mapping class groups |
| Kontsevich spaces | 8 | 0 | No stable maps |
| Divisors on Kontsevich space | 13 | 0 | No cone theory |
| Kodaira dimension | 6 | 0 | No birational geometry |
| Brill-Noether theory | 8 | 0 | No linear series |
| **Total** | **91** | **3 (2 full + 1 partial)** | |

## What Mathlib Does Have (Relevant Infrastructure)

While the specific theorems are almost entirely absent, mathlib has developed foundational infrastructure that would be prerequisite for formalizing some of the simpler results:

1. **Schemes** (`AlgebraicGeometry/Scheme.lean`): The category of schemes is defined.
2. **Morphism properties** (`AlgebraicGeometry/Morphisms/`): Separated, proper, finite type, flat, etale, smooth, closed immersion -- all defined.
3. **Valuative criteria** (`AlgebraicGeometry/ValuativeCriterion.lean`): Full characterizations of separated and proper in terms of valuative criteria.
4. **Projective Spec** (`AlgebraicGeometry/ProjectiveSpectrum/`): Proj construction exists and is proved proper.
5. **Grassmannian** (`RingTheory/Grassmannian.lean`): Module-level Grassmannian defined (as a set of submodules).
6. **Picard group of rings** (`RingTheory/PicardGroup.lean`): Invertible modules, class group.
7. **Cotangent module** (`RingTheory/Ideal/Cotangent.lean`, `RingTheory/Extension/Cotangent/`): I/I^2, Kahler differentials.
8. **Projectivization** (`LinearAlgebra/Projectivization/`): Set-level projectivization of vector spaces.
9. **Invariant subrings** (`RingTheory/Invariant/`): In the Galois theory context.
10. **Fundamental groupoid** (`AlgebraicTopology/FundamentalGroupoid/`): Simply connected spaces defined.

## Distance Assessment

The gap between this textbook and mathlib is enormous. To formalize even the most basic results (say, the cohomology ring of the Grassmannian), one would need to build:
- Chern classes of vector bundles
- Singular cohomology or Chow groups for varieties
- Cell decomposition / Schubert cells
- Ring structure on cohomology/Chow

To formalize moduli space results, one would additionally need:
- Algebraic stacks (including the 2-categorical framework)
- Stable curves (including deformation theory)
- The construction of M_g as a DM stack
- Tautological classes (lambda, psi, delta, kappa)

These represent years of formalization effort. The textbook operates at a level of algebraic geometry that is approximately 3-5 major development layers above what currently exists in mathlib.
