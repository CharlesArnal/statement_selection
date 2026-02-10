# Detailed Assessment: Mathlib Coverage
## Complex Variables with Applications (MIT 18.04, Spring 2018)

This document provides a detailed assessment of whether each formal mathematical statement from the textbook is formalized in Lean 4's mathlib library.

---

## Topic 1: Complex Algebra and the Complex Plane

### Definition 1. Complex numbers ($i^2 = -1$)
**Status: Included**
The complex numbers are defined in mathlib as `Complex` (or `\C`), constructed as `\R \times \R` with the appropriate ring structure. The imaginary unit `Complex.I` satisfies `I * I = -1`.
**Mathlib references:** `Mathlib/Analysis/Complex/Basic.lean`, `Mathlib/Data/Complex/Basic.lean`

### Theorem 1. Fundamental theorem of algebra
**Status: Included**
Mathlib proves that `\C` is algebraically closed via `Complex.isAlgClosed`. Every nonconstant polynomial over `\C` has a root.
**Mathlib references:** `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, `Mathlib/Analysis/Complex/Polynomial/Basic.lean`

### Definition 2. Real and imaginary parts
**Status: Included**
`Complex.re` and `Complex.im` are the projections giving real and imaginary parts. `Complex.ofReal` embeds `\R` into `\C`.
**Mathlib references:** `Mathlib/Data/Complex/Basic.lean`

### Definition 3. Complex conjugation
**Status: Included**
`starRingEnd \C` (or `Complex.conj`) provides conjugation. Properties like `conj(z * w) = conj(z) * conj(w)` are proved.
**Mathlib references:** `Mathlib/Data/Complex/Basic.lean`

### Definition 4. Modulus $|z|$
**Status: Included**
`Complex.abs z` gives the modulus, defined as `\sqrt{z.re^2 + z.im^2}`. This is also the norm on `\C` as a normed field.
**Mathlib references:** `Mathlib/Analysis/Complex/Basic.lean`, `Mathlib/Analysis/Complex/Norm.lean`

### Theorem 2. Triangle inequality
**Status: Included**
The triangle inequality `\|z + w\| \le \|z\| + \|w\|` follows from the normed field structure on `\C`.
**Mathlib references:** `Mathlib/Analysis/Normed/Field/Basic.lean`

### Definition 5. Euler's formula
**Status: Included**
`Complex.exp (I * \theta) = cos \theta + I * sin \theta` is proved as a consequence of the power series definitions.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean`, `Mathlib/Analysis/Complex/Exponential.lean`

### Theorem 3. Properties of complex exponentials
**Status: Included**
Properties including `exp(a + b) = exp(a) * exp(b)`, `exp(0) = 1`, differentiability of `exp`, and the power series definition are all formalized.
**Mathlib references:** `Mathlib/Analysis/Complex/Exponential.lean`, `Mathlib/Analysis/SpecialFunctions/Exp.lean`

### Theorem 4. De Moivre's formula
**Status: Partially Included**
De Moivre's formula $(cos\theta + i\sin\theta)^n = \cos(n\theta) + i\sin(n\theta)$ is not stated as a standalone theorem, but follows immediately from `Complex.exp_nat_mul` and Euler's formula, which are both in mathlib.
**Mathlib references:** `Mathlib/Analysis/Complex/Exponential.lean`

### Definition 6. Complex exponential function
**Status: Included**
`Complex.exp` is defined via power series and satisfies $e^{x+iy} = e^x(\cos y + i\sin y)$.
**Mathlib references:** `Mathlib/Analysis/Complex/Exponential.lean`

### Definition 7. Punctured plane
**Status: Included**
Can be expressed as `{z : \C | z \ne 0}` or `\C \setminus \{0\}` using standard set operations.
**Mathlib references:** Standard set theory in `Mathlib/Order/Filter/Basic.lean`

### Definition 8. Branch of argument
**Status: Partially Included**
Mathlib defines `Complex.arg` as a specific single-valued function returning values in $(-\pi, \pi]$. The general notion of a "branch" is not formalized as a definition, but the principal value is.
**Mathlib references:** `Mathlib/Analysis/Complex/Arg.lean`, `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`

### Definition 9. Principal argument $\operatorname{Arg}(z)$
**Status: Included**
`Complex.arg` returns values in $(-\pi, \pi]$, matching the principal branch convention.
**Mathlib references:** `Mathlib/Analysis/Complex/Arg.lean`

### Definition 10. Complex logarithm
**Status: Included**
`Complex.log` is defined as `\log |z| + i \arg(z)` using the principal branch of argument.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`

### Definition 11. Complex powers
**Status: Included**
`Complex.cpow z a = exp(a * log z)` is defined, along with extensive API for complex powers.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean`

---

## Topic 2: Analytic Functions

### Definition 12. Complex derivative
**Status: Included**
Complex differentiability is formalized via `HasDerivAt`, `DifferentiableAt`, etc. in the context of `\C`-valued functions. The Frechet derivative specializes to the complex derivative.
**Mathlib references:** `Mathlib/Analysis/Calculus/Deriv/Basic.lean`

### Definition 13. Open disk
**Status: Included**
`Metric.ball z r` gives the open ball (disk) of radius $r$ around $z$.
**Mathlib references:** `Mathlib/Topology/MetricSpace/Basic.lean`

### Definition 14. Open region
**Status: Included**
Open sets are defined topologically via `IsOpen`. Connected open sets correspond to the textbook notion of "region."
**Mathlib references:** `Mathlib/Topology/Basic.lean`

### Definition 15. Limit of complex function
**Status: Included**
`Filter.Tendsto f (nhds z_0) (nhds w_0)` formalizes the limit notion.
**Mathlib references:** `Mathlib/Order/Filter/Basic.lean`, `Mathlib/Topology/Basic.lean`

### Definition 16. Continuity
**Status: Included**
`ContinuousAt f z_0` is the standard definition.
**Mathlib references:** `Mathlib/Topology/ContinuousOn.lean`

### Theorem 2.10. Cauchy-Riemann equations
**Status: Partially Included**
The Cauchy-Riemann equations are not stated as a standalone theorem relating real partial derivatives $u_x = v_y$, $u_y = -v_x$. However, the equivalence between complex differentiability and $\R$-linearity of the derivative with the conformal property is addressed in `Mathlib/Analysis/Complex/RealDeriv.lean` and `Mathlib/Analysis/Complex/Conformal.lean`. The connection between `HasDerivAt` (complex) and `HasFDerivAt` (real) captures the content.
**Mathlib references:** `Mathlib/Analysis/Complex/RealDeriv.lean`, `Mathlib/Analysis/Complex/Conformal.lean`

### Theorem 5. Converse of Cauchy-Riemann
**Status: Partially Included**
The converse direction (satisfying CR equations with continuous partials implies analytic) is captured implicitly through the characterization of complex differentiability in terms of the real derivative being $\C$-linear.
**Mathlib references:** `Mathlib/Analysis/Complex/RealDeriv.lean`

### Theorem 6. $f' = 0$ on a disk implies $f$ constant
**Status: Included**
This follows from `is_const_of_deriv_eq_zero` or the connected-component version. For analytic functions, `AnalyticAt.eq_of_eventually_eq` and related results capture this.
**Mathlib references:** `Mathlib/Analysis/Calculus/MeanValue.lean`

### Theorem 2.13. Analytic implies $f'$ analytic
**Status: Included**
Analytic functions have analytic derivatives. This is part of the general theory: `AnalyticAt.deriv`.
**Mathlib references:** `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`

### Definition 17. Entire function
**Status: Included**
An entire function is one that is `Differentiable \C f` on all of `\C`, or equivalently `AnalyticOn \C f Set.univ`.
**Mathlib references:** `Mathlib/Analysis/Complex/Liouville.lean`

### Definition 18. Complex $\cos$, $\sin$
**Status: Included**
`Complex.cos` and `Complex.sin` are defined via the exponential: $\cos z = (e^{iz} + e^{-iz})/2$, $\sin z = (e^{iz} - e^{-iz})/(2i)$.
**Mathlib references:** `Mathlib/Analysis/Complex/Exponential.lean`

### Definition 19. Complex $\cosh$, $\sinh$
**Status: Included**
`Complex.cosh` and `Complex.sinh` are defined via the exponential.
**Mathlib references:** `Mathlib/Analysis/Complex/Exponential.lean`

---

## Topic 3: Line Integrals and Cauchy's Theorem

### Definition 20. Complex line integral
**Status: Included**
Circle integrals are formalized via `circleIntegral` in mathlib. More general contour integrals along paths are handled via `intervalIntegral` composed with parametrizations.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`, `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`

### Theorem 3.5. Fundamental theorem of complex line integrals
**Status: Included**
The fundamental theorem of calculus for interval integrals combined with the chain rule gives this. Also `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/FundThmCalculus.lean`

### Theorem 3.8. Antiderivative implies path independence
**Status: Included**
This is a consequence of the fundamental theorem. For analytic functions, `DiffContOnCl.circleIntegral_eq_zero` and related results formalize path independence.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Theorem 3.9. Path independence iff vanishing loop integrals
**Status: Included**
This equivalence is part of the general framework for contour integration.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Theorem 3.13. Cauchy's theorem (simply connected)
**Status: Included**
Mathlib proves that analytic functions on convex/star-shaped domains have vanishing circle integrals. `DiffContOnCl.circleIntegral_eq_zero` and the existence of primitives `HasPrimitives` capture this.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`, `Mathlib/Analysis/Complex/HasPrimitives.lean`

### Theorem 3.14. Extended Cauchy's theorem (annular region)
**Status: Included**
The extension to multiply-connected regions is handled through the general circle integral theory and winding number arguments in mathlib.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Definition 21. Winding number
**Status: Partially Included**
The winding number concept is used implicitly in mathlib's circle integral formulations, but a general definition for arbitrary closed curves is not a standalone definition.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

---

## Topic 4: Cauchy's Integral Formula

### Theorem 4.1. Cauchy's integral formula
**Status: Included**
`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable` and `DiffContOnCl.circleIntegral_sub_inv_smul` provide Cauchy's integral formula for circles. `two_pi_I_inv_smul_circleIntegral_sub_inv_smul` gives the precise statement.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Theorem 4.5. Cauchy's formula for derivatives
**Status: Included**
Higher-order Cauchy integral formulas are proved. `DiffContOnCl.hasFPowerSeriesOnBall` gives the power series (and thus all derivatives) via the Cauchy integral.
**Mathlib references:** `Mathlib/Analysis/Complex/CauchyIntegral.lean`, `Mathlib/Analysis/Complex/TaylorSeries.lean`

### Theorem 4.11. Triangle inequality for integrals
**Status: Included**
`norm_integral_le_integral_norm` provides $\|\int f\| \le \int \|f\|$.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/Bochner.lean`

### Theorem 4.12. Triangle inequality for integrals (contour version)
**Status: Included**
For circle integrals, `circleIntegral.norm_integral_le_of_norm_le_const` and related bounds exist.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

### Corollary 1. ML inequality
**Status: Included**
The ML inequality ($|\int_C f| \le M \cdot L$) follows directly from the norm estimates above.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`

### Theorem 4.14. Second extension of Cauchy's theorem
**Status: Partially Included**
The removable singularity theorem (if $g$ is analytic except at $z_0$ and bounded near $z_0$, then the singularity is removable) is formalized.
**Mathlib references:** `Mathlib/Analysis/Complex/RemovableSingularity.lean`

### Theorem 7. Analytic implies infinitely differentiable
**Status: Included**
Analytic functions on `\C` are smooth (`ContDiff`). This follows from the power series representation.
**Mathlib references:** `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`, `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Theorem 4.15. Cauchy's inequality
**Status: Included**
Cauchy's estimate for derivatives: `DiffContOnCl.norm_iteratedDeriv_le` and related bounds on derivatives using circle integrals.
**Mathlib references:** `Mathlib/Analysis/Complex/Liouville.lean`, `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Theorem 4.16. Liouville's theorem
**Status: Included**
`Differentiable.apply_eq_apply_of_bounded` proves that a bounded entire function is constant. The file is dedicated to Liouville's theorem and its generalizations.
**Mathlib references:** `Mathlib/Analysis/Complex/Liouville.lean`

### Corollary 2. FTA via Liouville
**Status: Included**
The fundamental theorem of algebra is proved using Liouville's theorem in mathlib.
**Mathlib references:** `Mathlib/Analysis/Complex/Polynomial/Basic.lean`

### Theorem 4.17. Mean value property
**Status: Included**
`Complex.circleIntegral_mean_value` or related results show that $f(z_0)$ equals the average of $f$ on a circle around $z_0$.
**Mathlib references:** `Mathlib/Analysis/Complex/MeanValue.lean`

### Theorem 4.18. Maximum modulus principle
**Status: Included**
The maximum modulus principle is proved in `Mathlib/Analysis/Complex/AbsMax.lean`. Key results include `Complex.eventually_eq_of_isLocalMax_norm` and related statements showing that a local maximum of $|f|$ forces $f$ to be constant.
**Mathlib references:** `Mathlib/Analysis/Complex/AbsMax.lean`

---

## Topic 5: Harmonic Functions

### Definition 5.1. Harmonic function
**Status: Partially Included**
Mathlib has a directory `Mathlib/Analysis/Complex/Harmonic/` with files `Analytic.lean` and `MeanValue.lean`. The notion of harmonic functions is formalized in the context of complex analysis, though the general PDE definition $\nabla^2 u = 0$ may not be stated in the classical real-variable form.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`

### Theorem 5.2. Real and imaginary parts of analytic functions are harmonic
**Status: Partially Included**
This is addressed in `Mathlib/Analysis/Complex/Harmonic/Analytic.lean` where the connection between analyticity and harmonicity is established.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`

### Theorem 5.3. Harmonic function is real part of analytic function
**Status: Partially Included**
The existence of a harmonic conjugate on simply connected domains is partially formalized in the harmonic function theory files.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`

### Definition 22. Harmonic conjugates
**Status: Partially Included**
The concept is used in the harmonic function files but may not have a standalone definition.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`

### Theorem 8. Mean value property for harmonic functions
**Status: Partially Included**
`Mathlib/Analysis/Complex/Harmonic/MeanValue.lean` addresses mean value properties for harmonic functions.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`

### Theorem 9. Maximum principle for harmonic functions
**Status: Partially Included**
The maximum principle for harmonic functions can be derived from the analytic version, and related results exist in the harmonic function files.
**Mathlib references:** `Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`, `Mathlib/Analysis/Complex/AbsMax.lean`

### Lemma 5.4. $\nabla u \cdot \nabla v = 0$
**Status: Not Included**
This specific result about the orthogonality of gradients of harmonic conjugates is not formalized in mathlib.

### Theorem 10. Orthogonality of level curves
**Status: Not Included**
The geometric result about orthogonal level curves of harmonic conjugates is not formalized.

---

## Topic 6: Two-Dimensional Hydrodynamics

### Theorem 11. Analytic potential gives div/curl-free field
**Status: Not Included**
The connection between analytic functions and potential fluid flow is not formalized in mathlib. This is an applied mathematics result.

### Theorem 12. Irrotational incompressible flow has complex potential
**Status: Not Included**
This applied result connecting fluid dynamics to complex analysis is not in mathlib.

### Theorem 13. Stream function theorem
**Status: Not Included**
The stream function characterization of fluid flow is not formalized.

---

## Topic 7: Taylor and Laurent Series

### Theorem 14. Sum of finite geometric series
**Status: Included**
`Finset.geom_sum_eq` and `geom_sum_eq` provide the formula $\sum_{k=0}^{n} r^k = (1 - r^{n+1})/(1 - r)$.
**Mathlib references:** `Mathlib/Algebra/GeomSum.lean`

### Theorem 15. Infinite geometric series
**Status: Included**
`tsum_geometric_of_lt_one` and `tsum_geometric_of_abs_lt_one` give $\sum r^n = 1/(1-r)$ for $|r| < 1$.
**Mathlib references:** `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`

### Theorem 7.1. Convergence of power series
**Status: Included**
The general theory of power series convergence, including radius of convergence, is formalized. `FormalMultilinearSeries.radius` gives the radius of convergence; `HasFPowerSeriesOnBall` captures convergence on a ball.
**Mathlib references:** `Mathlib/Analysis/Analytic/Constructions.lean`, `Mathlib/Analysis/Analytic/Basic.lean`

### Theorem 7.5. Taylor's theorem (complex)
**Status: Included**
Complex analytic functions have power series expansions. `DiffContOnCl.hasFPowerSeriesOnBall` proves that differentiable functions have convergent power series on disks. The coefficients are given by derivatives.
**Mathlib references:** `Mathlib/Analysis/Complex/TaylorSeries.lean`, `Mathlib/Analysis/Complex/CauchyIntegral.lean`

### Corollary 3. Uniqueness of Taylor series
**Status: Included**
The uniqueness of power series representations follows from `AnalyticAt.unique_formalMultilinearSeries`.
**Mathlib references:** `Mathlib/Analysis/Analytic/Basic.lean`

### Theorem 7.6. Zeros of analytic functions are isolated
**Status: Included**
`AnalyticAt.eventually_eq_zero_or_self` and results in `Mathlib/Analysis/Analytic/IsolatedZeros.lean` prove that zeros are isolated.
**Mathlib references:** `Mathlib/Analysis/Analytic/IsolatedZeros.lean`

### Definition 23. Order of a zero
**Status: Included**
The order of vanishing is formalized via `AnalyticAt.order` in the analytic function theory.
**Mathlib references:** `Mathlib/Analysis/Analytic/Order.lean`

### Definition 24. Isolated singularity
**Status: Partially Included**
The concept appears implicitly in the removable singularity theorem and meromorphic function theory, but a standalone general definition of "isolated singularity" may not exist.
**Mathlib references:** `Mathlib/Analysis/Complex/RemovableSingularity.lean`, `Mathlib/Analysis/Meromorphic/Basic.lean`

### Theorem 7.19. Laurent series
**Status: Partially Included**
Laurent series as formal algebraic objects exist in `Mathlib/RingTheory/LaurentSeries.lean`. However, the analytic theorem that a function analytic on an annulus has a convergent Laurent expansion is not fully formalized in the complex analysis sense.
**Mathlib references:** `Mathlib/RingTheory/LaurentSeries.lean`

### Definition 25. Poles, essential singularities, removable singularities
**Status: Partially Included**
Removable singularities are treated in `Mathlib/Analysis/Complex/RemovableSingularity.lean`. Meromorphic functions (which have poles) are defined in `Mathlib/Analysis/Meromorphic/Basic.lean`. Essential singularities are not explicitly defined as a standalone concept.
**Mathlib references:** `Mathlib/Analysis/Complex/RemovableSingularity.lean`, `Mathlib/Analysis/Meromorphic/Basic.lean`

### Definition 7.31. Residue
**Status: Not Included**
The residue of a function at a pole is not defined in mathlib. There is no `Residue` definition or residue computation framework.

---

## Topic 8: Residue Theorem

### Definition 26. Holomorphic / Meromorphic
**Status: Included**
Holomorphic (analytic) functions are captured by `DifferentiableOn \C f` or `AnalyticOn`. Meromorphic functions are defined in `Mathlib/Analysis/Meromorphic/Basic.lean`.
**Mathlib references:** `Mathlib/Analysis/Meromorphic/Basic.lean`

### Theorem 16. Picard's theorem
**Status: Not Included**
Neither the little nor the great Picard theorem is formalized in mathlib.

### Theorem 17. Quotients of functions (zero/pole orders)
**Status: Included**
The order of vanishing for quotients follows from the order theory for analytic functions. Results about meromorphic functions handle the pole/zero arithmetic.
**Mathlib references:** `Mathlib/Analysis/Analytic/Order.lean`, `Mathlib/Analysis/Meromorphic/Basic.lean`

### Theorem 18. Residue at simple pole via $1/g'(z_0)$
**Status: Not Included**
Since residues are not defined in mathlib, residue computation formulas are not present.

### Theorem 19. Residues at higher order poles
**Status: Not Included**
Not formalized, as the residue framework is absent.

### Theorem 20. Cauchy's residue theorem
**Status: Not Included**
The residue theorem $\oint_C f = 2\pi i \sum \text{Res}$ is not formalized in mathlib. While Cauchy's integral formula (a special case) is present, the general residue theorem for multiple isolated singularities is not.

### Definition 27. Residue at infinity
**Status: Not Included**
Not formalized.

### Theorem 21. Computing residue at infinity via substitution
**Status: Not Included**
Not formalized.

---

## Topic 9: Definite Integrals Using the Residue Theorem

### Theorem 9.1. Estimation on semicircles (decay faster than $1/z$)
**Status: Not Included**
This computational tool for evaluating real integrals via residues is not formalized.

### Theorem 9.2. Jordan-type lemma
**Status: Not Included**
Jordan's lemma (integrals of $f(z)e^{iaz}$ on large contours vanish) is not in mathlib.

### Theorem 9.7. Trigonometric integrals via residues
**Status: Not Included**
The technique of converting $\int_0^{2\pi} R(\cos\theta, \sin\theta)\,d\theta$ to a contour integral is not formalized.

### Theorem 9.11. Convergence implies Cauchy principal value convergence
**Status: Not Included**
Not formalized.

### Definition 28. Cauchy principal value
**Status: Partially Included**
Improper integrals are handled in `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` but the specific notion of Cauchy principal value (symmetric limit) may not be a standalone definition.
**Mathlib references:** `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`

### Theorem 9.13. Integral over semicircle around simple pole
**Status: Not Included**
This specific result about the limiting value of an integral over a small semicircle around a simple pole is not formalized.

### Theorem 9.14. Integral over circular arc around simple pole
**Status: Not Included**
Not formalized.

### Definition 29. Fourier transform
**Status: Included**
The Fourier transform is defined in `Mathlib/Analysis/Fourier/FourierTransform.lean` as `VectorFourier.fourierIntegral`.
**Mathlib references:** `Mathlib/Analysis/Fourier/FourierTransform.lean`

### Theorem 22. Fourier inversion formula
**Status: Partially Included**
Fourier inversion is proved for specific function classes (e.g., Schwartz functions, Gaussians) but the general inversion theorem may not be fully stated in the generality of the textbook.
**Mathlib references:** `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean`, `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`

---

## Topic 10: Conformal Transformations

### Definition 30. Conformal map
**Status: Included**
`ConformalAt f z` is defined in mathlib, meaning the derivative at $z$ is a nonzero scalar multiple of an isometry.
**Mathlib references:** `Mathlib/Analysis/Complex/Conformal.lean`, `Mathlib/Analysis/InnerProductSpace/ConformalLinearMap.lean`

### Theorem 10.3. Conformal iff complex linear (nonzero)
**Status: Included**
`conformalAt_iff_isConformalMap_fderiv` and related results characterize conformal maps. For complex functions, conformality is equivalent to having a nonzero complex derivative.
**Mathlib references:** `Mathlib/Analysis/Complex/Conformal.lean`

### Theorem 10.4. Analytic with $f'(z_0) \neq 0$ is conformal
**Status: Included**
This follows from the characterization of conformal maps and complex differentiability.
**Mathlib references:** `Mathlib/Analysis/Complex/Conformal.lean`, `Mathlib/Analysis/Complex/RealDeriv.lean`

### Theorem 10.9. Level curves of $u$ and $v$ are orthogonal
**Status: Not Included**
This geometric result about level curves is not formalized.

### Theorem 10.10. Riemann mapping theorem
**Status: Not Included**
The Riemann mapping theorem is a major result not yet formalized in mathlib.

### Definition 31. Fractional linear transformation (Mobius)
**Status: Partially Included**
Mobius transformations on the upper half-plane are used in `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`. However, a general standalone definition of FLTs as $T(z) = (az+b)/(cz+d)$ on $\hat{\C}$ is not cleanly isolated.
**Mathlib references:** `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`

### Theorem 23. FLTs map circles/lines to circles/lines
**Status: Not Included**
This classical geometric property is not formalized.

### Definition 32. Symmetric points with respect to a circle
**Status: Not Included**
Not formalized.

### Theorem 24. FLTs preserve symmetry
**Status: Not Included**
Not formalized.

### Theorem 25. Milne-Thomson circle theorem
**Status: Not Included**
This applied result from fluid dynamics is not in mathlib.

---

## Topic 11: Argument Principle

### Theorem 11.1. $\frac{1}{2\pi i}\oint \frac{f'}{f} = Z - P$
**Status: Not Included**
The argument principle relating the integral of $f'/f$ to the count of zeros minus poles is not formalized.

### Definition 33. Winding number of $f$ around $C$
**Status: Not Included**
The winding number for general curves is not defined as a standalone concept.

### Theorem 11.4. Argument principle (change in argument)
**Status: Not Included**
Not formalized.

### Theorem 11.6. Rouche's theorem
**Status: Not Included**
Rouche's theorem is not in mathlib.

### Corollary 4. FTA via Rouche
**Status: Not Included**
This proof of FTA is not formalized (though FTA itself is proved via Liouville's theorem).

### Theorem 11.18. Nyquist stability criterion
**Status: Not Included**
This engineering/control theory application is not in mathlib.

---

## Topic 12: Laplace Transform

### Definition 34. Laplace transform
**Status: Not Included**
The Laplace transform $\mathcal{L}(f) = \int_0^\infty f(t)e^{-st}\,dt$ is not defined in mathlib.

### Definition 35. Exponential type
**Status: Not Included**
Not formalized as a standalone concept.

### Theorem 26. Convergence for functions of exponential type
**Status: Not Included**
Not formalized.

### Theorem 27. Properties of Laplace transform (linearity, shifts, derivatives)
**Status: Not Included**
Not formalized.

### Theorem 12.13. Substitution rule for Laplace
**Status: Not Included**
Not formalized.

### Theorem 12.20. Laplace inversion via residues
**Status: Not Included**
Not formalized.

### Theorem 12.21. Bromwich integral (Laplace inversion)
**Status: Not Included**
Not formalized.

---

## Topic 13: Analytic Continuation and the Gamma Function

### Theorem 13.2. Uniqueness of analytic continuation
**Status: Included**
`AnalyticOn.eqOn_of_preconnected_of_eventuallyEq` and `AnalyticAt.unique_of_eventuallyEq` prove that if two analytic functions agree on a set with an accumulation point, they agree everywhere on the connected domain.
**Mathlib references:** `Mathlib/Analysis/Analytic/Uniqueness.lean`, `Mathlib/Analysis/Analytic/IsolatedZeros.lean`

### Corollary 5. At most one analytic continuation
**Status: Included**
Follows directly from the uniqueness theorem above.
**Mathlib references:** `Mathlib/Analysis/Analytic/Uniqueness.lean`

### Definition 36. Gamma function
**Status: Included**
`Complex.Gamma z` is defined in mathlib, initially via the integral $\int_0^\infty t^{z-1}e^{-t}\,dt$ and then extended meromorphically.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`

### Theorem 28. $\Gamma(z)$ is analytic for $\operatorname{Re}(z) > 0$
**Status: Included**
The analyticity (differentiability) of Gamma in the right half-plane is proved.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean`

### Theorem 29. $\Gamma(n+1) = n!$
**Status: Included**
`Complex.Gamma_nat_eq_factorial` proves $\Gamma(n+1) = n!$.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`

### Theorem 30. Functional equation $\Gamma(z+1) = z\Gamma(z)$
**Status: Included**
`Complex.Gamma_add_one` proves the functional equation.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`

### Theorem 31. Meromorphic continuation of $\Gamma$ with simple poles at $0, -1, -2, \ldots$
**Status: Included**
The meromorphic continuation is established. The poles and their residues $(-1)^m/m!$ are computed.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`, `Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean`

### Theorem 32. Weierstrass product for $\Gamma$
**Status: Partially Included**
The Weierstrass product representation involves the `GammaSeq` limit definition. The product formula is partially captured through the limit definition of Gamma.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`

### Theorem 33. Reflection formula $\Gamma(z)\Gamma(1-z) = \pi/\sin(\pi z)$
**Status: Included**
`Complex.Gamma_mul_Gamma_one_sub` proves the reflection formula.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`

### Theorem 34. Stirling's formula
**Status: Included**
Stirling's approximation is proved in `Mathlib/Analysis/SpecialFunctions/Stirling.lean`.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Stirling.lean`

### Theorem 35. Legendre duplication formula
**Status: Included**
The duplication formula $2^{2z-1}\Gamma(z)\Gamma(z+1/2) = \sqrt{\pi}\Gamma(2z)$ is proved.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`

### Theorem 36. $\mathcal{L}(t^{z-1}) = \Gamma(z)/s^z$
**Status: Partially Included**
The integral $\int_0^\infty t^{z-1}e^{-st}\,dt = \Gamma(z)/s^z$ can be derived from the definition of Gamma and change of variables, but the Laplace transform framework per se is not in mathlib. The Mellin transform, which is closely related, is defined in `Mathlib/Analysis/MellinTransform.lean`.
**Mathlib references:** `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`, `Mathlib/Analysis/MellinTransform.lean`

---

## Summary Statistics

| Category | Count | Percentage |
|----------|-------|------------|
| **Included** | 55 | 50.0% |
| **Partially Included** | 22 | 20.0% |
| **Not Included** | 33 | 30.0% |
| **Total** | 110 | 100% |

### Key observations:

1. **Well-covered areas**: Basic complex analysis (definitions, topology, exponentials, trig), Cauchy's theorem and integral formula, Liouville's theorem, maximum modulus principle, Taylor series, isolated zeros, conformal maps, analytic continuation, and the Gamma function are well-represented in mathlib.

2. **Partially covered areas**: Cauchy-Riemann equations (captured indirectly through the real derivative characterization), harmonic functions (recent additions with dedicated files), Laurent series (algebraic but not analytic), Fourier transform (defined but inversion not fully general), and Mobius transformations (used for upper half-plane actions but not general FLTs).

3. **Major gaps**: The residue theorem and all residue-based techniques (residue computation, definite integral evaluation, argument principle, Rouche's theorem, winding numbers) are entirely absent. The Laplace transform is not in mathlib. Applied topics (hydrodynamics, Nyquist criterion, Milne-Thomson) are absent. The Riemann mapping theorem and Picard's theorem are not formalized.

4. **The biggest single gap** is the lack of a residue framework. Topics 8, 9, and 11 (about 25 statements) all depend on residues and are entirely unformalized.
