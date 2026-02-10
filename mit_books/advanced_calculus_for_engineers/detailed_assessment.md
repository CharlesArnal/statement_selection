# Detailed Assessment

## Statement 1: Continuity of Components of Complex Functions
**Verdict**: included

This statement asserts that if f(z) = u + iv is continuous, then its real and imaginary parts u(x,y) and v(x,y) are individually continuous. In mathlib, the continuity of the real and imaginary parts of a complex-valued function follows directly from the fact that `Complex.re` and `Complex.im` are continuous linear maps (see `Complex.continuous_re` and `Complex.continuous_im` in `Mathlib/Analysis/Complex/Basic.lean` and related files). This is a standard fact about the topology of the complex numbers and is fully formalized.

## Statement 2: Cauchy-Riemann Equations
**Verdict**: included

The Cauchy-Riemann equations state that if f(z) = u + iv is analytic, then du/dx = dv/dy and du/dy = -dv/dx. In mathlib, this is formalized in `Mathlib/Analysis/Complex/Conformal.lean` in the section labeled `CauchyRiemann`. The key theorem is `differentiableAt_complex_iff_differentiableAt_real` (line 284), which states that a function on the complex numbers is complex-differentiable at a point if and only if it is real-differentiable there and the real derivative maps I to I times its value on 1. This is precisely the abstract/coordinate-free form of the Cauchy-Riemann equations. The traditional partial-derivative formulation is an immediate consequence.

## Statement 3: Cauchy Integral Theorem (Cauchy-Goursat Theorem)
**Verdict**: included

The Cauchy Integral Theorem states that the contour integral of an analytic function over a closed curve is zero. In mathlib, this is proved in `Mathlib/Analysis/Complex/CauchyIntegral.lean`. The key result is `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` (line 267), which proves this for rectangular contours. The file's documentation (lines 21-22) explicitly states "we prove the Cauchy-Goursat theorem." While the formulation is for rectangles (rather than arbitrary simple closed curves), this is the standard approach in mathlib and captures the essential content of the theorem.

## Statement 4: ML-Formula (Estimation Lemma)
**Verdict**: included

The ML-formula states that |integral_C f(z) dz| <= M * length(C) when |f(z)| <= M on C. In mathlib, this type of integral estimation bound is available through `norm_integral_le_of_norm_le` and related lemmas in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` and `Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`. For circle integrals specifically, similar bounds are used in `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`. The general principle that the norm of an integral is bounded by the integral of the norm, combined with the bound on the integrand, gives this result.

## Statement 5: Cauchy Integral Formula
**Verdict**: included

The Cauchy Integral Formula states f(z_0) = (1/(2*pi*i)) * oint_C f(z)/(z - z_0) dz for f analytic inside C. This is explicitly proved in `Mathlib/Analysis/Complex/CauchyIntegral.lean`. The theorem `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` (line 534) and its variant `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` (line 497) are exactly this formula for circle contours. The file's documentation (lines 57-62) explicitly labels these as the "Cauchy integral formula."

## Statement 6: Residue at Simple Pole (g/h form)
**Verdict**: non-included

This theorem states that if f(z) = g(z)/h(z) with g, h analytic, h(z_0) = 0, h'(z_0) != 0, and g(z_0) != 0, then Res_{z=z_0} f(z) = g(z_0)/h'(z_0). I searched `Mathlib/Analysis/Complex/` and `Mathlib/Analysis/Meromorphic/` for any formalization of residues. While mathlib has a `Meromorphic` framework (in `Mathlib/Analysis/Meromorphic/`), with notions of order and poles, it does not contain an explicit residue computation theorem of this form. The algebraic residue (as a coefficient of the Laurent series) is not formalized as a standalone concept with computational rules like g(z_0)/h'(z_0).

## Statement 7: Residue Formula for mth Order Poles
**Verdict**: non-included

This theorem gives the formula for the residue at an mth order pole: C_{-1} = (1/(m-1)!) * lim_{z->z_0} d^{m-1}/dz^{m-1} [(z - z_0)^m f(z)]. As with Statement 6, mathlib does not contain explicit residue computation formulas. The meromorphic function framework exists but does not include these classical residue calculation tools. I searched for "residue", "Residue", and related terms across all of mathlib and found no matching formalization.

## Statement 8: Residue Theorem
**Verdict**: non-included

The Residue Theorem states that oint_C f(z) dz = 2*pi*i * sum of residues at enclosed singularities. I searched extensively in `Mathlib/Analysis/Complex/` and `Mathlib/Analysis/Meromorphic/` for any formalization of the residue theorem. While the Cauchy integral formula is present (which can be viewed as a special case), the general residue theorem -- relating the contour integral of a meromorphic function to the sum of its residues at enclosed poles -- is not formalized in mathlib. The notion of "residue" itself lacks a formal definition in the library suitable for this theorem.

## Statement 9: Theorem 1 (Vanishing Integral on Large Arc)
**Verdict**: non-included

This theorem states that if z*f(z) -> 0 uniformly as |z| = R -> infinity, then the integral of f(z) over a circular arc of radius R vanishes as R -> infinity. I searched mathlib for "Jordan", "vanishing integral", and related terms in the complex analysis directories. This is a standard estimation lemma used in contour integration but is not formalized in mathlib. No matching results were found.

## Statement 10: Theorem 2 (Jordan's Lemma)
**Verdict**: non-included

Jordan's Lemma states that if f(z) -> 0 uniformly as |z| -> infinity, then the integral of e^{i*alpha*z} * f(z) over a semicircular arc vanishes as the radius goes to infinity (for appropriate sign of alpha and choice of upper/lower half-plane). I searched for "Jordan", "jordan_lemma", and related patterns. The Jordan-related results in mathlib concern the Jordan-Holder theorem, Jordan decomposition of measures, and Jordan algebras -- none related to the complex analysis estimation lemma. This is not present in mathlib.

## Statement 11: Theorem 3 (Small Circle Integral Vanishes)
**Verdict**: non-included

This theorem states that if (z - z_0)*f(z) -> 0 uniformly as the radius delta -> 0 around z_0, then the integral of f(z) over the small circle vanishes. I searched for related estimation lemmas in `Mathlib/Analysis/Complex/` and `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`. While there are some integral bounds, this specific vanishing theorem for small circles is not formalized in mathlib.

## Statement 12: Theorem 4 (Half-Residue at Simple Pole on Contour)
**Verdict**: non-included

This theorem states that the integral over a semicircular indent of radius epsilon around a simple pole z_0 on the contour converges to i*pi * Res f(z) as epsilon -> 0 (i.e., half the full residue contribution). I searched for "half residue", "indent", "semicircle" across mathlib's complex analysis files. This is a standard tool in contour integration around poles on the real axis but is not formalized in mathlib.

## Statement 13: Frobenius Method Theorem
**Verdict**: non-included

The Frobenius theorem describes the solution structure at regular singular points of second-order linear ODEs based on the indicial equation roots: the number and form of Frobenius-type solutions depend on whether the roots differ by a non-integer, an integer, or are equal. I searched for "Frobenius", "indicial", "regular singular", and "fuchsian" across all of mathlib. No relevant results were found. Mathlib does not contain the theory of ODEs at regular singular points or the Frobenius method.

## Statement 14: Sturm-Liouville Eigenvalue Theorem
**Verdict**: non-included

This theorem states that for a proper Sturm-Liouville problem, the eigenvalues form a discrete set and the eigenfunctions are orthogonal with respect to the weight function r(x). I searched for "SturmLiouville", "sturm_liouville", "eigenvalue ODE", and "selfAdjoint eigenvalue" across mathlib. While `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` has results about self-adjoint operators and their eigenspaces being orthogonal, the specific Sturm-Liouville ODE theory (involving p(x), q(x), r(x), boundary conditions, and the discreteness of eigenvalues for second-order differential operators) is not formalized in mathlib.

## Statement 15: Fourier Convergence Theorem
**Verdict**: included

Fourier's theorem states that any piecewise continuous function can be expanded in a Fourier series with L^2 convergence. In mathlib, Fourier series are formalized in `Mathlib/Analysis/Fourier/AddCircle.lean`. The key theorem `hasSum_fourier_series_L2` (line 409) proves that the Fourier series of an L^2 function converges to the function in the L^2 topology. Additionally, `hasSum_fourier_series_of_summable` (line 470) proves pointwise convergence when the Fourier coefficients are summable. Parseval's identity is also present as `hasSum_sq_fourierCoeff`. While the book's statement is for piecewise continuous functions and sine series specifically, the mathlib formalization covers the general L^2 convergence of Fourier series, which subsumes this result.
