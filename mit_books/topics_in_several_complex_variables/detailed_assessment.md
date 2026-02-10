# Detailed Assessment: Mathlib Coverage
## Topics in Several Complex Variables (MIT 18.117)

This document provides a detailed assessment of whether each formal mathematical statement from the textbook is formalized in Lean 4's mathlib library (v4.27.0).

**Key context:** This course covers several complex variables (SCV), Dolbeault cohomology, Kaehler geometry, Hodge theory, elliptic operators, pseudodifferential operators, symplectic reduction, toric varieties, and Morse theory. Mathlib's complex analysis is almost entirely single-variable. The only statements that have mathlib coverage are basic single-variable results reviewed in the first chapter.

---

## Chapter 1: Holomorphic Functions in One Variable (Review)

### Statement 1. Unique analytic continuation (one variable)
**Status: Included**
The identity theorem for analytic functions is proved in mathlib: if two analytic functions agree on a set with an accumulation point in a connected domain, they agree everywhere. The key result is `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.
**Mathlib references:** `Mathlib/Analysis/Analytic/IsolatedZeros.lean`

### Statement 2. Maximum modulus principle (one variable)
**Status: Included**
The maximum modulus principle for complex-differentiable functions is fully formalized. If `|f|` has a local maximum at an interior point of a connected domain, then `f` is constant. Key results include `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn` and related theorems.
**Mathlib references:** `Mathlib/Analysis/Complex/AbsMax.lean`

### Statement 3. Holomorphic with Re(f) = 0 implies constant
**Status: Partially Included**
This is not stated as a standalone lemma in mathlib. However, it follows from the open mapping theorem (or maximum modulus principle) applied to `exp(f)`, both of which are in mathlib. The open mapping theorem is in `Mathlib/Analysis/Complex/OpenMapping.lean` and the maximum modulus principle in `AbsMax.lean`. The specific statement about vanishing real part is not directly formalized.
**Mathlib references:** `Mathlib/Analysis/Complex/AbsMax.lean`, `Mathlib/Analysis/Complex/OpenMapping.lean`

---

## Chapter 2: Holomorphic Functions in Several Variables

### Statement 4. Cauchy-Green integral solves dbar equation (1D)
**Status: Not Included**
This lemma states that the Cauchy-Green integral operator (the Pompeiu integral) yields a smooth solution to the inhomogeneous Cauchy-Riemann equation in one complex variable. Mathlib has the Cauchy integral formula for holomorphic functions (`Mathlib/Analysis/Complex/CauchyIntegral.lean`) but not the Cauchy-Green/Pompeiu integral operator or the dbar equation framework.
**Searched:** `Analysis/Complex/CauchyIntegral.lean`, `Analysis/Complex/` directory. No dbar/Cauchy-Green operator found.

### Statement 5. Product rule for dbar operator
**Status: Not Included**
The Cauchy-Riemann operator (dbar) and its Leibniz rule for smooth functions are not formalized in mathlib. Mathlib has no framework for the dbar operator on functions of several complex variables.
**Searched:** `Analysis/Complex/` directory. No dbar operator formalization found.

### Statement 6. Cauchy integral formula for polydisks
**Status: Not Included**
The iterated Cauchy integral formula for holomorphic functions on polydisks in C^n is a fundamental result of several complex variables. Mathlib's Cauchy integral formula (`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` in `CauchyIntegral.lean`) is strictly single-variable. There is no polydisk or multi-variable integration framework.
**Searched:** `Analysis/Complex/CauchyIntegral.lean` -- single variable only. No polydisk or C^n holomorphic function theory.

### Statement 7. Power series expansion on polydisks
**Status: Not Included**
Multi-variable power series expansion of holomorphic functions on polydisks is not in mathlib. Mathlib has single-variable power series (`HasFPowerSeriesAt`, `FormalMultilinearSeries`) but these are single-variable/Banach-space-valued, not the multi-index series of SCV.
**Searched:** `Analysis/Analytic/Basic.lean`, `Analysis/Analytic/ConvergenceRadius.lean`. Single-variable framework only.

### Statement 8. Unique analytic continuation (several variables)
**Status: Not Included**
The identity theorem for holomorphic functions on connected open sets in C^n. While mathlib has the single-variable version (Statement 1), the several-variable version requires the SCV framework which is absent. The single-variable result in `IsolatedZeros.lean` is for functions `K -> E` where `K` is a nontrivially normed field, which is intrinsically one-dimensional.
**Searched:** `Analysis/Analytic/IsolatedZeros.lean` -- works over `K` (one-dimensional). No multi-variable holomorphic function theory.

### Statement 9. Maximum modulus principle (several variables)
**Status: Not Included**
Same situation as Statement 8. The single-variable maximum modulus principle is in mathlib, but the several-variable version on connected open sets in C^n requires the SCV framework. Mathlib's `AbsMax.lean` works for functions on normed spaces but specifically uses complex-differentiability in one variable.
**Searched:** `Analysis/Complex/AbsMax.lean`. The theorems there concern `DiffContOnCl` for functions differentiable over `C`, but the proofs use single-variable arguments (circle integrals). The general Banach space version does technically apply to C^n, but the statement as given in the book (using the language of holomorphic functions on open sets in C^n) is not directly formalized.

### Statement 10. Cauchy-Green integral (smooth version)
**Status: Not Included**
This is a restatement/elaboration of Statement 4 for compactly supported smooth functions. Not in mathlib.
**Searched:** Same as Statement 4.

### Statement 11. Multidimensional inhomogeneous CR equation
**Status: Not Included**
The solution of the multi-variable inhomogeneous Cauchy-Riemann equation via iterated one-dimensional integrals is a core result of SCV. Entirely absent from mathlib.
**Searched:** `Analysis/Complex/` directory. No multi-variable CR theory.

### Statement 12. Compactly supported solution to ICR equation
**Status: Not Included**
A uniquely higher-dimensional phenomenon: the ICR equation has compactly supported solutions when the complement of the support is connected. Not in mathlib.
**Searched:** `Analysis/Complex/` directory. No such result.

### Statement 13. Hartogs' extension theorem
**Status: Not Included**
Hartogs' theorem -- that holomorphic functions on the complement of a compact set in C^n (n >= 2) extend to all of C^n -- is a cornerstone result specific to several complex variables. Completely absent from mathlib.
**Searched:** Grep for `Hartogs` across all of mathlib. No results.

---

## Chapter 3: The Dolbeault Complex

### Statements 14--19. Dolbeault complex exactness results
**Status: Not Included**
Statements 14 through 19 concern the exactness of the Dolbeault complex (the dbar complex of (0,q)-forms) on polydisks, including local exactness (Theorem 1), degree reduction (Theorem 2), the full exactness (Theorem 3), and technical lemmas about exhaustions by polydisks. The entire Dolbeault cohomology framework -- differential forms of type (p,q), the dbar operator on forms, the Dolbeault complex -- is absent from mathlib.
**Searched:** Grep for `Dolbeault`, `dbar`, `del_bar` across all of mathlib. No results.

### Statement 20. Intersection of pseudo-convex domains is pseudo-convex
**Status: Not Included**
Pseudoconvexity is a fundamental notion in SCV with no formalization in mathlib.
**Searched:** Grep for `pseudoConvex`, `pseudo_convex`, `plurisubharmonic` across all of mathlib. No results.

### Statement 21. Dolbeault complex exact iff pseudo-convex
**Status: Not Included**
This deep characterization connecting Dolbeault cohomology to domain geometry is not in mathlib. Both concepts are absent.
**Searched:** Same as Statements 14-19 and 20.

### Statement 22. Exactness of complexes on polydisks
**Status: Not Included**
Further exactness results for auxiliary complexes on polydisks. Not in mathlib.
**Searched:** Same as Statements 14-19.

### Statement 23. Poincare lemma (convex domains)
**Status: Not Included**
The Poincare lemma states that the de Rham complex is exact on convex (or contractible) domains. Mathlib has no de Rham complex or Poincare lemma for differential forms.
**Searched:** Grep for `Poincare.*Lemma`, `poincare.*lemma`, `exact.*deRham` across all of mathlib. No results.

### Statement 24. Closed (1,1)-form has potential on polydisk
**Status: Not Included**
The dbar-Poincare lemma for (1,1)-forms. Requires the (p,q)-form framework absent from mathlib.
**Searched:** Same as Statements 14-19.

### Statement 25. Holomorphic iff pullback preserves (1,0)-forms
**Status: Not Included**
This characterization of holomorphic maps via the pullback of (1,0)-forms requires the type decomposition of differential forms, which is not in mathlib.
**Searched:** Same as Statements 14-19.

### Statement 26. Pullback of (p,q)-forms by holomorphic maps
**Status: Not Included**
Compatibility of pullback with the (p,q)-decomposition and with the dbar operator. Not in mathlib.
**Searched:** Same as Statements 14-19.

---

## Chapter 4: Inverse and Implicit Function Theorems

### Statement 27. Real inverse function theorem
**Status: Included**
The inverse function theorem in the real (smooth) setting is fully formalized in mathlib. `HasStrictFDerivAt.localInverse` provides the local inverse, and `HasStrictFDerivAt.to_localInverse` shows the inverse is differentiable. The theorem works for Banach spaces over any complete nontrivially normed field, which includes R^n.
**Mathlib references:** `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`, `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FiniteDimensional.lean`

### Statement 28. Holomorphic inverse function theorem
**Status: Partially Included**
Mathlib's inverse function theorem (`HasStrictFDerivAt.localInverse`) is stated for Banach spaces over any complete nontrivially normed field, so it applies when the field is C. However, the specifically holomorphic formulation (biholomorphism of neighborhoods in C^n) is not stated as a separate theorem. The abstract result does yield the desired conclusion but the language of biholomorphic maps between open sets in C^n is not part of mathlib's vocabulary.
**Mathlib references:** `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`

### Statement 29. Canonical form for independent holomorphic functions
**Status: Not Included**
This is a holomorphic version of the rank theorem / submersion theorem: if df_1, ..., df_k are linearly independent at p, there exists a biholomorphic coordinate change making f_i = z_i. While mathlib has the implicit function theorem framework (`Mathlib/Analysis/Calculus/Implicit.lean`), this specific canonical form result for holomorphic submersions in several complex variables is not formalized.
**Searched:** `Analysis/Calculus/Implicit.lean`, `Analysis/Calculus/InverseFunctionTheorem/`. The abstract implicit function theorem is present but not the holomorphic canonical form.

---

## Chapter 5: Complex Manifolds

### Statement 30. CP^n is compact
**Status: Not Included**
Complex projective space is not formalized as a topological or complex manifold in mathlib. Mathlib has projective spaces in the algebraic geometry sense but not the analytic/topological construction of CP^n with its standard topology.
**Searched:** Grep for `ProjectiveSpace`, `Complex.*Projective`, `CompactProjectiveSpace` across mathlib. The `CP` hits are unrelated (category theory, completion, etc.).

### Statement 31. CP^n is a complex n-manifold
**Status: Not Included**
Requires both CP^n and the notion of complex manifold, neither of which is in mathlib in the differential-geometric sense.
**Searched:** Same as Statement 30.

### Statements 32--33. Non-singular hypersurfaces in CP^n
**Status: Not Included**
These results about smooth hypersurfaces defined by homogeneous polynomials in CP^n require the framework of complex projective varieties and complex manifolds, absent from mathlib.
**Searched:** Same as Statement 30.

### Statements 34--37. Analytic continuation, maximum modulus, and constancy on manifolds
**Status: Not Included**
These extend single-variable results to complex manifolds. While the single-variable analogues exist in mathlib (Statements 1, 2), the manifold versions require the framework of complex manifolds and holomorphic functions on manifolds, which is not in mathlib.
**Searched:** `Analysis/Complex/AbsMax.lean`, `Analysis/Analytic/IsolatedZeros.lean`. Single-variable only. No complex manifold theory.

### Statements 38--39. Tangent/cotangent decomposition
**Status: Not Included**
The (1,0) and (0,1) decomposition of the complexified cotangent bundle of a complex manifold is not formalized. Mathlib has no framework for complex manifolds or their tangent bundle decomposition.
**Searched:** No complex manifold or type decomposition in mathlib.

### Statement 40. Implicit function theorem on manifolds
**Status: Not Included**
While mathlib has the abstract implicit function theorem for Banach spaces, the manifold version (choosing holomorphic coordinates adapted to given functions) is not formalized. Mathlib's smooth manifold library does not include a manifold-level implicit function theorem.
**Searched:** `Analysis/Calculus/Implicit.lean`, `Geometry/Manifold/`. No manifold-level implicit function theorem.

---

## Chapter 6: Cech Cohomology

### Statements 41--46. Cech cohomology and Cech-Dolbeault isomorphism
**Status: Not Included**
Statements 41-46 develop Cech cohomology for sheaves (coboundary operator, homotopy operators, vanishing for smooth functions, Hormander's theorem, Cech-Dolbeault isomorphism). Mathlib has the Cech nerve construction (`Mathlib/AlgebraicTopology/CechNerve.lean`) as a simplicial object in category theory, but no computational Cech cohomology for sheaves on manifolds, no Hormander L^2 estimates, and no Cech-Dolbeault comparison.
**Searched:** `AlgebraicTopology/CechNerve.lean` (simplicial nerve only), `Topology/Sheaves/` (basic sheaf axioms only). Grep for `CechCohomology` found no results. Grep for `Hormander` found no results.

---

## Chapter 7: Symplectic and Kaehler Geometry

### Statement 47. Non-degenerate alternating form: even dimension and standard basis
**Status: Not Included**
The theorem that a non-degenerate alternating bilinear form forces even dimension and admits a symplectic basis is a classical result in linear algebra. Mathlib has the symplectic group defined via the canonical matrix J (`Mathlib/LinearAlgebra/SymplecticGroup.lean`) but does not prove the abstract classification theorem for non-degenerate alternating forms.
**Searched:** `LinearAlgebra/SymplecticGroup.lean` (defines J matrix and symplectic group but not the classification theorem). Grep for `alternating.*nondegenerate`, `SymplecticForm` found no results.

### Statement 48. Non-degeneracy via top exterior power
**Status: Not Included**
Characterization of non-degeneracy of an alternating 2-form via omega^n != 0. Not in mathlib.
**Searched:** Same as Statement 47.

### Statement 49. J* action on (k,l)-forms
**Status: Not Included**
Complex structure action on the (k,l) decomposition of forms. Requires (p,q)-form framework absent from mathlib.
**Searched:** No (p,q)-form decomposition in mathlib.

### Statement 50. Darboux theorem (symplectic)
**Status: Not Included**
The Darboux theorem in symplectic geometry (local normal form for symplectic forms) is not in mathlib. Mathlib's `Analysis/Calculus/Darboux.lean` is the intermediate value property for derivatives, which is an entirely different result. There is no symplectic geometry framework in mathlib.
**Searched:** `Analysis/Calculus/Darboux.lean` (intermediate value theorem for derivatives, unrelated). Grep for `symplectic` found only `LinearAlgebra/SymplecticGroup.lean` (matrix group, not differential geometry).

### Statements 51--57. Kaehler geometry and Fubini-Study form
**Status: Not Included**
These results cover the Darboux theorem for Kaehler forms, uniqueness of Kaehler potentials, the Fubini-Study symplectic form on CP^n, and related constructions. Mathlib has the algebraic notion of Kaehler differentials (`RingTheory/Kaehler/`) which is about algebraic derivations and has nothing to do with Kaehler manifolds in differential geometry. No Kaehler manifold theory exists in mathlib.
**Searched:** Grep for `Kaehler`, `Kahler` found only `RingTheory/Kaehler/` (algebraic, unrelated). Grep for `FubiniStudy`, `fubini_study` found no results.

---

## Chapter 8: Double Complexes and Cohomology

### Statement 58. Cohomology isomorphism from exact double complex
**Status: Not Included**
This abstract homological algebra result (zigzag argument for double complexes) is a standard tool. While mathlib has extensive homological algebra in the category-theoretic sense (`Algebra/Homology/`), the specific double complex spectral sequence / zigzag argument for the Dolbeault-Cech comparison is not formalized as stated.
**Searched:** `Algebra/Homology/` directory. The category-theoretic homological algebra does not include this specific double complex result in the form needed.

---

## Chapter 9: Differential Operators on Manifolds

### Statements 59--64. Differential operators, symbols, and transposes
**Status: Not Included**
These statements develop the theory of linear differential operators on manifolds: the principal symbol, the symbol calculus (composition law), the formal transpose, and their intrinsic definitions on manifolds. Mathlib has no framework for differential operators in the PDE/microlocal analysis sense.
**Searched:** Grep for `PseudoDifferential`, `pseudoDifferential`, `symbol.*operator` across mathlib. No results.

### Statement 65. Fredholm theorem for elliptic operators
**Status: Not Included**
The Fredholm alternative for elliptic operators on compact manifolds (finite-dimensional kernel, range characterized by orthogonality to kernel of transpose) is a deep result of PDE theory. Mathlib has a TODO comment about Fredholm operators in `Analysis/Normed/Operator/Banach.lean` but no actual Fredholm operator theory.
**Searched:** Grep for `Fredholm` across mathlib. Only found a TODO comment in `Banach.lean`. Grep for `Elliptic.*operator`, `elliptic.*differential` found no results.

### Statements 66--68. Parametrix and Fredholm decomposition
**Status: Not Included**
Construction of parametrices for elliptic operators and the Fredholm decomposition of function spaces. Not in mathlib.
**Searched:** Same as Statement 65.

---

## Chapter 10: Fourier Analysis on Torus

### Statements 69--72. Fourier coefficients and convergence
**Status: Not Included**
These results concern the behavior of Fourier coefficients for smooth functions on the torus: the Fourier transform of derivatives, rapid decay of coefficients, convergence of Fourier series, and convergence of lattice sums. Mathlib has some Fourier analysis (`Analysis/Fourier/AddCircleMulti.lean`) but not the specific smooth convergence results or rapid decay estimates needed here.
**Searched:** `Analysis/Fourier/AddCircleMulti.lean` -- contains multi-dimensional Fourier coefficient definitions but not the specific smooth convergence/rapid decay results stated.

---

## Chapter 11: Pseudodifferential Operators

### Statements 73--78. Pseudodifferential operator theory
**Status: Not Included**
The entire framework of pseudodifferential operators -- symbol classes S^m, parametrix construction, symbol reduction, kernel smoothness off the diagonal -- is absent from mathlib. This is highly specialized microlocal analysis.
**Searched:** Grep for `PseudoDifferential`, `pseudoDifferential` across mathlib. No results.

### Statement 79. Global parametrix for elliptic operators on bundles
**Status: Not Included**
The existence of a global parametrix (an approximate inverse modulo smoothing operators) for elliptic operators on vector bundles over compact manifolds. Not in mathlib.
**Searched:** Same as Statements 73-78.

---

## Chapter 12: Elliptic Operators on Vector Bundles

### Statements 80--82. Hermitian bundles and Fredholm theory
**Status: Not Included**
These develop the theory of differential operators between Hermitian vector bundles: local Hermitian trivializations, the formal transpose for Hermitian bundle operators, and the main Fredholm theorem. While mathlib has vector bundles (`Topology/VectorBundle/`) and even Hermitian structures in some algebraic contexts, the PDE theory of elliptic operators on bundles is entirely absent.
**Searched:** `Topology/VectorBundle/` (basic vector bundle theory). No elliptic operator or Fredholm theory for bundles.

---

## Chapter 13: Elliptic Complexes and Hodge Theory

### Statements 83--85. Symbols of de Rham and Dolbeault operators
**Status: Not Included**
Computing the principal symbols of the exterior derivative and dbar operator, and proving the de Rham and Dolbeault complexes are elliptic. Requires both the differential operator symbol framework and differential forms, neither available at this level in mathlib.
**Searched:** No de Rham complex, no symbol calculus in mathlib.

### Statement 86. Hodge decomposition theorem
**Status: Not Included**
The Hodge decomposition (every form decomposes uniquely into exact + coexact + harmonic) is a deep result requiring elliptic PDE theory on compact Riemannian manifolds. Not in mathlib.
**Searched:** Grep for `HodgeStar`, `hodge_star`, `Hodge` across mathlib. Hits in `Perfectoid` and `Fraisse` are unrelated.

### Statement 87. Harmonic forms = kernel of Laplacian
**Status: Not Included**
Requires the Hodge Laplacian on differential forms, which is not in mathlib.
**Searched:** Same as Statement 86.

### Statements 88--92. Hodge star and interior product
**Status: Not Included**
The Hodge star operator, its properties on product spaces, the formal adjoint of exterior multiplication, and interior product identities. While mathlib has exterior algebras (`LinearAlgebra/ExteriorAlgebra/`), the Hodge star operator on an oriented inner product space and the associated PDE theory are not formalized.
**Searched:** Grep for `HodgeStar` found no results. `LinearAlgebra/ExteriorAlgebra/` has algebraic exterior algebra but no Hodge star.

---

## Chapter 14: Kaehler Identities and Lefschetz Theory

### Statements 93--100. Kaehler identities and Lefschetz operator
**Status: Not Included**
The Kaehler identities (commutator relations between the Lefschetz operator L, its adjoint, the differentials d, dbar, and their formal adjoints) are fundamental results of Kaehler geometry. None of this framework exists in mathlib: no Kaehler manifolds, no Lefschetz operator on forms, no Hodge theory.
**Searched:** Grep for `Lefschetz`, `lefschetz` across mathlib. Hits in model theory and algebraic geometry are unrelated (Ax-Grothendieck). No Kaehler geometry.

---

## Chapter 15: Representation Theory (sl(2) Module Theory)

### Statements 101--115. sl(2) representation theory and Hard Lefschetz
**Status: Not Included**
These develop the representation theory of sl(2,C) (weight decomposition, irreducible modules, primitive decomposition) and apply it to prove the Hard Lefschetz theorem. While mathlib has Lie algebra theory (`Algebra/Lie/`) including `sl_2` (`Algebra/Lie/Classical.lean`), the specific finite-dimensional representation theory (classification of irreducible modules, weight space decomposition) and its application to Kaehler geometry are not formalized.
**Searched:** `Algebra/Lie/Classical.lean` (defines classical Lie algebras). No finite-dimensional representation classification. No Hard Lefschetz theorem.

---

## Chapter 16: Poincare Duality and Further Kaehler Identities

### Statement 116. Poincare duality pairing is non-degenerate
**Status: Not Included**
Poincare duality for the de Rham cohomology of compact oriented manifolds is not in mathlib. Mathlib has no de Rham cohomology.
**Searched:** Grep for `PoincareDuality`, `Poincare.*duality`, `deRham` across mathlib. No results.

### Statements 117--123. Hodge star on harmonic forms and Kaehler Laplacian
**Status: Not Included**
These results (codifferential formula, Hodge star preserves harmonicity, compatibility of Riemannian and symplectic structures, anti-commutativity of d and d^C, L and L^t commuting with the Laplacian, Laplacian decomposition) all require the Kaehler geometry and Hodge theory framework absent from mathlib.
**Searched:** Same as previous Kaehler/Hodge searches.

---

## Chapter 17: Group Actions and Symplectic Reduction

### Statements 124--132. Group actions, quotients, and symplectic reduction
**Status: Not Included**
These cover: differentials of group actions as Lie algebra morphisms, smooth quotient manifold theorem for free proper actions, holomorphic quotient theorem, basic forms, exact sequences for tangent spaces of fibrations, Marsden-Weinstein symplectic reduction, and moment map properties. Mathlib has group actions on topological spaces and some orbit/quotient constructions, but not the smooth manifold quotient theorem, symplectic reduction, or moment maps.
**Searched:** Grep for `MomentMap`, `moment_map`, `Hamiltonian.*action` across mathlib. No results. Grep for `symplectic` found only the matrix symplectic group.

---

## Chapter 18: Kaehler Reduction and GIT

### Statements 133--137. Kaehler reduction and GIT quotient
**Status: Not Included**
These develop the relationship between Kaehler reduction and geometric invariant theory: gradient vector fields from moment maps, the main theorem identifying the GIT quotient with the symplectic reduction (including that the reduced space is Kaehler), and supporting lemmas on orbit geometry. This is highly specialized differential/algebraic geometry entirely absent from mathlib.
**Searched:** No Kaehler geometry, no moment map theory, no GIT quotient in mathlib.

---

## Chapter 19: Toric Varieties and Moment Maps

### Statements 138--145. Toric geometry
**Status: Not Included**
These develop the theory of toric varieties via symplectic reduction of C^d by torus actions: the moment map for linear torus actions, properness from polarization, stabilizer formulas, freeness conditions, reduced symplectic form, and stable set decomposition. Mathlib has no toric variety theory.
**Searched:** No toric geometry, no moment map theory in mathlib.

---

## Chapter 20: Toric Geometry and Morse Theory

### Statements 146--155. Morse theory on toric varieties and McMullen-Stanley theorem
**Status: Not Included**
These results apply Morse theory to toric manifolds: regular value criteria from polytope geometry, the main theorem identifying Morse data with polytope combinatorics (vertices, adjacency), Betti number formulas, and the McMullen-Stanley theorem on h-vectors of simple polytopes. Mathlib has no Morse theory and no toric geometry.
**Searched:** Grep for `MorseFunction`, `morse_function`, `Morse.*theory` across mathlib. No results.

---

## Summary

| Status | Count |
|--------|-------|
| Included | 3 |
| Partially Included | 2 |
| Not Included | 150 |
| **Total** | **155** |

**Mathlib coverage: 3 out of 155 statements (1.9%)**

### Included statements (3):
1. **Statement 1** (Unique analytic continuation, one variable) -- `Mathlib/Analysis/Analytic/IsolatedZeros.lean`
2. **Statement 2** (Maximum modulus principle, one variable) -- `Mathlib/Analysis/Complex/AbsMax.lean`
3. **Statement 27** (Real inverse function theorem) -- `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`

### Partially included statements (2):
1. **Statement 3** (Re(f) = 0 implies constant) -- follows from formalized results but not directly stated
2. **Statement 28** (Holomorphic inverse function theorem) -- the abstract result applies but holomorphic language is not used

### Major absent areas:
- **Several complex variables core:** Hartogs' theorem, polydisk Cauchy formula, multi-variable power series, pseudoconvexity, domains of holomorphy
- **Dolbeault cohomology:** dbar operator, (p,q)-forms, Dolbeault complex, exactness results
- **Kaehler geometry:** Kaehler manifolds, Kaehler potentials, Fubini-Study form, Kaehler identities
- **Hodge theory:** Hodge star, Hodge decomposition, harmonic forms, Laplacian on forms
- **Elliptic PDE theory:** Differential operators on manifolds, principal symbols, Fredholm theory, parametrices
- **Pseudodifferential operators:** Symbol classes, pseudodifferential calculus
- **Symplectic geometry:** Darboux theorem, symplectic reduction, moment maps
- **Toric geometry:** Toric varieties, polytope combinatorics, Morse theory applications
- **Representation theory applications:** sl(2) modules, Hard Lefschetz theorem
- **Complex manifolds:** CP^n as a manifold, holomorphic maps between manifolds
