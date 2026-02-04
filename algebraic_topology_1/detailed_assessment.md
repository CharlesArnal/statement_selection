# Detailed Assessment: Algebraic Topology 1 Statements in Mathlib

## Overview

This document provides a detailed assessment of each mathematical statement from Haynes Miller's "Lectures on Algebraic Topology" (18.905, Fall 2016) against the Mathlib library.

**Assessment Legend:**
- ✅ **Present**: Statement is fully formalized in mathlib
- 🟡 **Partial**: Related concepts exist but statement not directly available
- ❌ **Absent**: Statement or required concepts not in mathlib

---

## Chapter 1: Singular Homology

### Section 1-2: Introduction and Homology

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 1.5**: d² = 0 | ✅ Present | `Mathlib/Algebra/Homology/HomologicalComplex.lean` - `d_comp_d` states that differential squared is zero for chain complexes |

### Section 3-4: Categories, Functors, Natural Transformations

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Lemma 4.7**: Isomorphism iff split epi and split mono | ✅ Present | `Mathlib/CategoryTheory/EpiMono.lean` - Contains `SplitEpi`, `SplitMono` and related lemmas |
| **Lemma 4.8**: Functors preserve split epi/mono | ✅ Present | `Mathlib/CategoryTheory/Functor/EpiMono.lean` |

### Section 5: Homotopy, Star-shaped Regions

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 5.2** [Homotopy invariance]: H∗(f₀) = H∗(f₁) if f₀ ≃ f₁ | ❌ Absent | Mathlib defines singular homology but homotopy invariance is not proven |
| **Corollary 5.5**: Homotopy equivalences induce isomorphisms | ❌ Absent | Requires homotopy invariance |
| **Corollary 5.7**: Contractible space has trivial homology | ❌ Absent | `Mathlib/Topology/Homotopy/Contractible.lean` defines contractibility but doesn't connect to homology |
| **Lemma 5.10**: Chain homotopic maps induce same maps in homology | ✅ Present | `Mathlib/Algebra/Homology/Homotopy.lean` - Chain homotopy theory is well-developed |
| **Proposition 5.11**: Homotopic maps induce chain homotopic maps | ❌ Absent | Singular chains construction exists but this property not proven |
| **Proposition 5.13**: S∗(X) → Z is chain homotopy equiv for star-shaped X | ❌ Absent | Not formalized |

### Section 6: Homotopy Invariance of Homology

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 6.1**: Homotopy determines natural chain homotopy | ❌ Absent | Not formalized |
| **Theorem 6.2** [Cross product]: Existence and properties | ❌ Absent | Cross product not defined in mathlib |

### Section 7-8: Homology Cross Product, Relative Homology

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Lemma 7.1**, **Theorem 7.2**: Cross product in homology | ❌ Absent | Not formalized |
| **Lemma 8.4**: Quotient chain complex | ✅ Present | `Mathlib/Algebra/Homology/HomologicalComplex.lean` - Quotient complexes exist |

### Section 9: The Homology Long Exact Sequence

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 9.1** [Long exact sequence] | ✅ Present | `Mathlib/Algebra/Homology/HomologySequence.lean` - Full abstract treatment |
| **Proposition 9.4** [Five lemma] | ✅ Present | `Mathlib/Algebra/FiveLemma.lean` - Both module and abelian category versions |
| **Corollary 9.5**: Map of short exact sequences | ✅ Present | Follows from five lemma |
| **Proposition 9.6**: Two-out-of-three for pairs | 🟡 Partial | Follows from five lemma, not stated explicitly |

### Section 10: Excision and Applications

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 10.2** [Excision] | ❌ Absent | **Major gap** - Excision not formalized |
| **Corollary 10.3**: Quotient isomorphism | ❌ Absent | Requires excision |
| **Proposition 10.4**: Homology of spheres | ❌ Absent | Not computed |
| **Corollary 10.5**: Sⁿ ≁ Sᵐ for n ≠ m | ❌ Absent | Requires sphere homology |
| **Corollary 10.6**: Rⁿ ≁ Rᵐ for n ≠ m | ❌ Absent | Requires sphere homology |
| **Theorem 10.7** [Brouwer fixed-point] | ❌ Absent | **Major gap** - Not formalized |
| **Theorem 10.8**: Degree map surjective | ❌ Absent | Degree not defined |

### Section 11: Eilenberg-Steenrod Axioms and Locality

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 11.4** [Locality principle] | ❌ Absent | Not formalized |
| **Theorem 11.5** [Mayer-Vietoris] | ❌ Absent | `Mathlib/Topology/Sheaves/MayerVietoris.lean` is for sheaves, not singular homology |
| **Lemma 11.6**: Exact sequence from ladder | 🟡 Partial | Related techniques exist |

### Section 12-13: Subdivision and Locality Proof

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Proposition 12.1**: Subdivision is chain homotopic to identity | ❌ Absent | Not formalized |
| **Lemma 13.1-13.4**: Technical subdivision lemmas | ❌ Absent | Not formalized |
| **Lemma 13.3** [Lebesgue covering lemma] | ✅ Present | `Mathlib/Topology/MetricSpace/Lebesgue.lean` |
| **Theorem 13.5** [Locality principle] | ❌ Absent | Not formalized |

---

## Chapter 2: Computational Methods

### Section 14-15: CW-complexes

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 14.8**: CW-complex is Hausdorff | ✅ Present | `Mathlib/Topology/CWComplex/Classical/Basic.lean` |
| **Proposition 15.3**: Compact subset lies in finite subcomplex | 🟡 Partial | CW-complex basics exist |
| **Proposition 15.5**: S∞ is contractible | ❌ Absent | Not formalized |

### Section 16: Homology of CW-complexes

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Proposition 16.2**: Homology of skeleta | ❌ Absent | Cellular homology not in mathlib |
| **Theorem 16.3**: Cellular ≅ singular homology | ❌ Absent | **Major gap** - Cellular homology not formalized |
| **Corollary 16.4**: Even-cell CW complex | ❌ Absent | Requires cellular homology |

### Section 17-18: Projective Space, Euler Characteristic

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Proposition 17.1**: Homology of RPⁿ | ❌ Absent | Not computed |
| **Theorem 18.1**: χ(X) depends only on homotopy type | ❌ Absent | Euler characteristic not defined topologically |
| **Lemma 18.2**: Rank in short exact sequence | ✅ Present | Linear algebra facts available |
| **Theorem 18.3**: χ(X) = Σ(−1)ᵏ rank Hₖ(X) | ❌ Absent | Requires homology computation |
| **Theorem 18.4** [Wall]: Minimal CW structure | ❌ Absent | Not formalized |
| **Proposition 18.5**: Moore space construction | ❌ Absent | Not formalized |

### Section 20-22: Tensor Product, Tor, FTHA

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Proposition 20.11**: Homology with coefficients | 🟡 Partial | Tensor products exist; homology with coefficients partially defined |
| **Proposition 21.1**: Tensor is right exact | ✅ Present | `Mathlib/RingTheory/Flat/Basic.lean` and related |
| **Lemma 21.2**: Direct sum preserves exactness | ✅ Present | Standard algebraic facts |
| **Theorem 22.1** [FTHA]: Lift to chain map | ✅ Present | `Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean` - Projective resolutions well-developed |

### Section 23: Hom and Lim

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Lemma 23.1**: Hom-tensor adjunction | ✅ Present | `Mathlib/LinearAlgebra/TensorProduct.lean` and related |
| **Proposition 23.10**: Tensor commutes with colimit | ✅ Present | Colimit theory well-developed |
| **Proposition 23.12**: Direct limit is exact | ✅ Present | Filtered colimits preserve exactness |
| **Corollary 23.14**: H∗(X; Q) = H∗(X) ⊗ Q | ❌ Absent | Requires homology with coefficients |

### Section 24-25: Universal Coefficient Theorem, Künneth

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 24.1** [UCT] | ❌ Absent | **Major gap** - Not formalized |
| **Theorem 25.2** [Künneth] | ❌ Absent | **Major gap** - Not formalized |
| **Theorem 25.11** [Eilenberg-Zilber] | ❌ Absent | Not formalized |

---

## Chapter 3: Cohomology and Duality

### Section 26-29: Cohomology and Cup Product

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Proposition 27.1** [Cohomology UCT] | ❌ Absent | Not formalized |
| **Theorem 28.1**: H∗(X; R) is graded commutative ring | ❌ Absent | Cup product not defined |
| **Proposition 29.2**: Cross product is algebra map | ❌ Absent | Not formalized |
| **Corollary 29.4**: Map Sᵖ⁺ᵍ → Sᵖ × Sᵍ is zero in top homology | ❌ Absent | Not formalized |

### Section 30: Surfaces and Bilinear Forms

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 30.2** [Poincaré duality, F₂] | ❌ Absent | **Major gap** - Not formalized |
| **Lemma 30.5**, **Proposition 30.6**: Bilinear forms over F₂ | 🟡 Partial | Bilinear forms exist in `LinearAlgebra/SesquilinearForm` |
| **Theorem 30.9**: Classification of surfaces | ❌ Absent | Not formalized |

### Section 31-32: Local Coefficients and Orientations

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 31.5** [Unique path lifting] | 🟡 Partial | Covering space theory exists in `Topology/Covering` |
| **Theorem 31.6**: Covering spaces ↔ π₁-sets | 🟡 Partial | Fundamental groupoid exists but equivalence not complete |
| **Theorem 31.9** [Orientation Theorem] | ❌ Absent | Not formalized |
| **Theorem 32.1**: Local-to-global for manifolds | ❌ Absent | Not formalized |

### Section 33-35: Products and Čech Cohomology

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 33.3** [Cohomology Künneth] | ❌ Absent | Not formalized |
| **Proposition 34.1**: Cap product properties | ❌ Absent | Cap product not defined |
| **Theorem 34.2** [Poincaré duality] | ❌ Absent | **Major gap** |
| **Theorem 35.2-35.3**: Čech cohomology axioms | ❌ Absent | `CechNerve.lean` exists but not full Čech cohomology |

### Section 36-37: Relative Cap Product and Poincaré Duality

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 36.1-36.2**: Fully relative cap product | ❌ Absent | Not formalized |
| **Theorem 37.1** [Fully relative Poincaré duality] | ❌ Absent | Not formalized |
| **Corollary 37.5** [Poincaré duality] | ❌ Absent | **Major gap** |

### Section 38: Applications

| Statement | Status | Mathlib Location/Notes |
|-----------|--------|----------------------|
| **Theorem 38.4** [Alexander duality] | ❌ Absent | **Major gap** |
| **Theorem 38.8**: Perfect pairing from Poincaré duality | ❌ Absent | Requires Poincaré duality |
| **Theorem 38.11** [Borsuk-Ulam] | ❌ Absent | **Major gap** - Not formalized |

---

## Summary by Category

### Statements with Full Mathlib Coverage (~10 statements)
1. d² = 0 (chain complexes)
2. Split epi/mono characterization
3. Functors preserve split epi/mono
4. Chain homotopic maps induce same homology map
5. Long exact sequence in homology
6. Five lemma
7. Quotient chain complex
8. Hom-tensor adjunction
9. FTHA (projective resolution lifting)
10. Direct limits preserve exactness

### Statements with Partial Coverage (~10 statements)
- CW-complex basics (definition, Hausdorff)
- Covering spaces (basic definitions)
- Fundamental groupoid (basic theory)
- Bilinear forms (abstract theory)
- Tensor product properties (abstract)
- Singular homology (basic definition only)

### Statements Not in Mathlib (~80 statements)
**Major gaps include:**
- Homotopy invariance of singular homology
- Excision theorem
- Mayer-Vietoris for singular homology
- Homology of spheres
- Brouwer fixed-point theorem
- Cellular homology
- Universal Coefficient Theorem
- Künneth theorem
- Cup/cap products
- Poincaré duality
- Alexander duality
- Borsuk-Ulam theorem
- Orientation theory for manifolds

---

## Recommendations for Formalization Priority

### High Priority (Foundational)
1. **Homotopy invariance** - Enables all applications of homology
2. **Excision** - Key computational tool
3. **Mayer-Vietoris** - Essential for computations

### Medium Priority (Computational)
4. **Homology of spheres** - Basic example
5. **Cellular homology** - Computational workhorse
6. **Universal Coefficient Theorem** - Coefficients changes
7. **Künneth theorem** - Products

### Lower Priority (Advanced)
8. **Cup/cap products** - Ring structure
9. **Poincaré duality** - Manifold theory
10. **Alexander duality** - Applications
11. **Brouwer/Borsuk-Ulam** - Famous applications
