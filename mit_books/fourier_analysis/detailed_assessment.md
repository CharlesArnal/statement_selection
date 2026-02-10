Theorem (Parseval's formula):
included
Parseval's identity is formalized in mathlib. In `Mathlib/Analysis/InnerProductSpace/l2Space.lean`, the theorem `HilbertBasis.tsum_inner_mul_inner` gives the Parseval-type identity for Hilbert bases. The specific case for Fourier series on the circle is covered via `orthonormal_fourier` and the Hilbert basis structure `fourierBasis` in `Mathlib/Analysis/Fourier/AddCircle.lean`, which together yield Parseval's formula for L^2(T).

Strong Law of Large Numbers:
included
The strong law of large numbers is formalized in `Mathlib/Probability/StrongLaw.lean` as `ProbabilityTheory.strong_law_ae` and `ProbabilityTheory.strong_law_ae_real`. The theorem shows that for i.i.d. integrable random variables, the Cesaro averages converge almost surely to the expectation.

Proposition 1 (Fourier coefficient decay for C^1):
non-included
Searched for results about Fourier coefficient decay in `Mathlib/Analysis/Fourier/AddCircle.lean` and related files. No formalization of the specific bound |f_hat(n)| <= C/|n| for C^1 periodic functions was found. The Riemann-Lebesgue lemma is present but this quantitative decay rate for smooth functions is not.

Lemma 1 (Riemann-Lebesgue Lemma):
included
The Riemann-Lebesgue lemma is formalized in `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean`. The main result `tendsto_integral_exp_inner_smul_cocompact` shows that the Fourier transform of an L^1 function tends to zero. The real-line version `Real.tendsto_integral_exp_smul_cocompact` and the formulation via `Real.zero_at_infty_fourier` are also present.

Theorem 1 (Dini Test):
non-included
Searched for Dini test or Dini criterion in mathlib. The file `Mathlib/Topology/UniformSpace/Dini.lean` contains Dini's theorem on monotone convergence of continuous functions, which is a different result. The Dini test for pointwise convergence of Fourier series is not formalized.

Corollary 1 (Pointwise and Lp convergence for C^1):
non-included
Searched in `Mathlib/Analysis/Fourier/AddCircle.lean` and related Fourier series files. While the orthonormality and Hilbert basis structure are present, the specific pointwise convergence result s_N(x) -> f(x) for C^1 functions and the L^p convergence are not formalized.

Corollary 2 (Orthonormal basis for L^2(T)):
included
Formalized in `Mathlib/Analysis/Fourier/AddCircle.lean`. The theorem `orthonormal_fourier` establishes orthonormality of the Fourier monomials, and the Hilbert basis `fourierBasis` (line 388) is constructed via `HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top ...)`. This gives both the L^2 convergence and Parseval's identity.

Theorem 1 (Fejer's Theorem):
non-included
Searched for "Fejer", "Fejér", and approximate identity results specific to the circle group. No formalization of Fejer's theorem (uniform convergence of Cesaro means for continuous periodic functions) was found in mathlib.

Corollary 1 (Density of trigonometric polynomials in C(T)):
non-included
While the density of the span of Fourier monomials in L^p is established in `Mathlib/Analysis/Fourier/AddCircle.lean` (via `span_fourierLp_closure_eq_top`), the specific density in the uniform norm (C(T)) corresponding to Fejer's corollary is not directly formalized as a standalone result.

Lemma 1 (Approximate Identity Lemma for periodic functions):
non-included
Searched for approximate identity results in mathlib. While `MeasureTheory.Integral.PeakFunction` deals with related concepts, the specific approximate identity lemma for convolution on the circle with the three conditions (i)-(iii) is not formalized as stated.

Proposition 1 (Young's inequality for convolution on T):
non-included
Searched for convolution norm bounds in `Mathlib/Analysis/Convolution.lean` and `Mathlib/MeasureTheory/Group/Convolution.lean`. Young's inequality for convolution on the circle group (||f*g||_p <= ||f||_p ||g||_1) in the periodic setting is not explicitly formalized, though general convolution infrastructure exists.

Theorem 1 (L^1 convergence of Cesaro means):
non-included
Searched in Fourier analysis files. The L^1 convergence of the Cesaro means sigma_N f to f for L^1(T) functions is not formalized in mathlib. The related Hilbert basis and L^2 theory is present but not this L^1 result.

Corollary 1 (Uniqueness of Fourier Series):
non-included
Searched for Fourier uniqueness results in `Mathlib/Analysis/Fourier/AddCircle.lean`. While the Hilbert basis structure implies injectivity on L^2, the explicit statement that if f is in L^1(T) and all Fourier coefficients vanish then f = 0 a.e. does not appear as a standalone theorem.

Proposition 2 (Fourier transform of derivative):
non-included
Searched for derivative-Fourier coefficient relationships. The formula f_hat'(n) = in * f_hat(n) for periodic C^1 functions is not formalized in `Mathlib/Analysis/Fourier/AddCircle.lean` or related files. The Schwartz space Fourier derivative formula in `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean` is a different (though related) result for R rather than the circle.

Theorem 2 (Weyl equidistribution theorem):
non-included
Searched for equidistribution and Weyl in mathlib. The search for "Weyl" only returned results about Weyl groups in root systems, which is entirely different. No formalization of the Weyl equidistribution theorem was found.

Theorem 1 (Fourier inversion on Schwartz class):
included
Formalized in `Mathlib/Analysis/Fourier/Inversion.lean`. The theorems `Continuous.fourierInv_fourier_eq` and `MeasureTheory.Integrable.fourierInv_fourier_eq` give the Fourier inversion formula. Additionally, `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean` provides the Fourier transform as a continuous linear equivalence on the Schwartz space via `fourierTransformCLE`.

Corollary 1 (Plancherel identity on Schwartz class):
included
Formalized in `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean` via `SchwartzMap.integral_inner_fourier_fourier` (Plancherel's theorem for Schwartz functions) and in `Mathlib/Analysis/Fourier/LpSpace.lean` via `norm_fourier_eq` and `inner_fourier_eq`.

Corollary 2 (Extension of Fourier transform to L^2):
included
The extension of the Fourier transform to L^2 is formalized in `Mathlib/Analysis/Fourier/LpSpace.lean`. The Plancherel theorem `norm_fourier_eq` shows ||F f|| = ||f|| for L^2 functions, and the Fourier transform on L^2 is defined through the density approach.

Corollary 3 (Injectivity of Fourier transform on L^2):
included
This follows from the Plancherel theorem in `Mathlib/Analysis/Fourier/LpSpace.lean`: since `norm_fourier_eq` shows the Fourier transform is an isometry on L^2, it is injective. If F(f) = 0 then ||f|| = ||F(f)|| = 0 so f = 0.

Corollary 4 (Fourier inversion on L^2):
included
Formalized in `Mathlib/Analysis/Fourier/LpSpace.lean` and `Mathlib/Analysis/Fourier/Inversion.lean`. The Fourier transform on L^2 is shown to be invertible, and the inverse is the expected formula involving the conjugate Fourier transform.

Proposition 1 (Consistency of L^1 and L^2 Fourier transforms):
non-included
Searched for results about consistency between L^1 and L^2 definitions. While both definitions exist in mathlib (the integral definition in `Mathlib/Analysis/Fourier/FourierTransform.lean` and the L^2 extension in `Mathlib/Analysis/Fourier/LpSpace.lean`), the explicit statement that they agree on L^1 ∩ L^2 was not found as a standalone theorem.

Theorem 2 (Fourier inversion via partial sums on L^2):
non-included
Searched for L^2 convergence of truncated Fourier inversion integrals. The result that s_N(x) = (1/2pi) integral from -N to N of f_hat(xi) e^{ixxi} converges to f in L^2 is not formalized as a standalone result in mathlib.

Proposition 2 (Consistency of L^1 and L^2 inverse Fourier transforms):
non-included
Same situation as Proposition 1 above but for the inverse transform. The consistency between the L^1 and L^2 inverse Fourier transforms is not explicitly formalized.

Theorem 3 (Cesaro inversion on L^1(R)):
non-included
Searched for Cesaro/Fejer-type summation for Fourier integrals on R. No formalization of the L^1 convergence of the Cesaro means of the Fourier inversion integral was found.

Corollary 5 (Injectivity of Fourier transform on L^1):
non-included
Searched for injectivity of the Fourier transform on L^1(R). While `Measure.ext_of_charFun` in `Mathlib/MeasureTheory/Measure/CharacteristicFunction.lean` gives uniqueness for measures via characteristic functions, the specific statement that f in L^1(R) with f_hat = 0 implies f = 0 is not formalized as a standalone result.

Theorem 4 (Approximate identity on R):
non-included
Searched for approximate identity results on R. While `MeasureTheory.Integral.PeakFunction` contains related peak function estimates, the specific approximate identity theorem (K_epsilon * f -> f in L^1 for any L^1 kernel K with integral 1) is not formalized in this generality.

Proposition 1 (Fourier transform of finite measures is bounded continuous):
non-included
Searched for boundedness and continuity of the Fourier transform of finite measures. While `charFun` is defined in `Mathlib/MeasureTheory/Measure/CharacteristicFunction.lean`, the explicit statement that it maps to bounded continuous functions (as a mapping F: M_+(R) -> C_b(R)) is not given as a standalone proposition.

Theorem 1 (Uniqueness of Fourier transform of measures):
included
Formalized in `Mathlib/MeasureTheory/Measure/CharacteristicFunction.lean` as `Measure.ext_of_charFun`, which states that if two finite measures have the same characteristic function, they are equal.

Proposition 2 (Weak convergence via Fourier transforms):
non-included
Searched for Levy continuity theorem or weak convergence via Fourier transforms. While the characteristic function infrastructure exists, the specific result that pointwise convergence of Fourier transforms of measures implies weak convergence is not formalized as a standalone theorem.

Proposition 3 (Portmanteau-type result for weak convergence):
included
Portmanteau-type results for weak convergence of measures are formalized in `Mathlib/MeasureTheory/Measure/Portmanteau.lean`. The results about limsup and liminf of measures of open/closed sets under weak convergence are present.

Theorem 2 (Central Limit Theorem):
non-included
Searched for central limit theorem in mathlib. No formalization was found. The file `Mathlib/Probability/StrongLaw.lean` covers the strong law but not the CLT. The Gaussian distribution infrastructure in `Mathlib/Probability/Distributions/Gaussian/` provides foundations but the CLT itself is not stated.

Lemma 1 (Taylor expansion of exponential):
non-included
Searched for Taylor remainder bounds for the complex exponential. While Taylor series and remainder estimates exist in mathlib, the specific bound |R(x)| <= 4 min(|x|^2, |x|^3) for the remainder in the second-order expansion of e^{ix} is not formalized.

Proposition 4 (Fourier inversion on S'(R)):
non-included
The Fourier transform on tempered distributions is defined in `Mathlib/Analysis/Distribution/TemperedDistribution.lean` with an `instFourierTransform` instance. However, the explicit statement that the inverse Fourier transform on S'(R) inverts the Fourier transform (as a standalone proposition) was not found.

Proposition 1 (Continuity of inner product):
included
Formalized in `Mathlib/Analysis/InnerProductSpace/Continuous.lean`. The theorem `continuous_inner` establishes that the inner product is continuous as a function of both variables, and `ContinuousAt.inner`, `Continuous.inner` provide the convergence of inner products under norm convergence.

Theorem 1 (Characterization of orthonormal bases in Hilbert spaces):
included
Formalized in `Mathlib/Analysis/InnerProductSpace/l2Space.lean` through the `HilbertBasis` structure. The equivalences between density of span, completeness (f = 0 if all inner products vanish), norm convergence of partial sums, and Parseval's identity are all captured. Key results include `HilbertBasis.dense_span`, `HilbertBasis.hasSum_repr`, and `HilbertBasis.mk`.

Proposition 2 (Convergence and inner product of orthonormal expansions):
included
Formalized in `Mathlib/Analysis/InnerProductSpace/l2Space.lean`. The theorem `inner_eq_tsum` shows that the inner product of elements in l^2 equals the sum of componentwise inner products. The convergence of orthonormal expansions with square-summable coefficients follows from the `HilbertBasis` and `lp` infrastructure.

Polarization Formula:
included
The polarization identity is formalized in `Mathlib/Analysis/InnerProductSpace/Basic.lean` as `inner_eq_sum_norm_sq_div_four` (as noted in the file header line 22). This expresses the inner product in terms of norms, which is the content of the polarization formula.

Theorem 1 (L^p is a Banach space):
included
Formalized in `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`. The instance `instCompleteSpace` (line 394) establishes that Lp E p mu is a complete space for 1 <= p, making it a Banach space together with the norm structure from `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`.

Theorem 2 (Density of C_0^infty in L^p):
included
Formalized in `Mathlib/Analysis/Normed/Lp/SmoothApprox.lean` as `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`, which shows that smooth compactly supported functions (C_0^infty) are dense in L^p for p != infinity. This is the content of Theorem 2 in the textbook.

Theorem 1 (Finite-dimensional distributions of rescaled random walk):
non-included
Searched for random walk convergence and finite-dimensional distribution results. No formalization of the convergence of finite-dimensional distributions of rescaled random walks to Gaussian distributions was found in mathlib.

Theorem 2 (Wiener's construction of Brownian motion):
non-included
Searched for Brownian motion, Wiener process, and related constructions. No formalization of Brownian motion or Wiener's Fourier series construction was found in mathlib.

Proposition 1 (Sum of independent Gaussians):
non-included
Searched for results about sums of independent Gaussians converging to a Gaussian. While `Mathlib/Probability/Distributions/Gaussian/Basic.lean` has Gaussian distribution infrastructure, the specific L^2 convergence result for infinite sums of independent Gaussians is not formalized.

Lemma 1 (Characterization of multivariate Gaussian by linear combinations):
non-included
Searched for multivariate Gaussian characterization results. While `Mathlib/Probability/Distributions/Gaussian/CharFun.lean` has characteristic function formulas for Gaussians, the characterization of joint Gaussian distributions by their linear combinations and covariance matrices is not formalized.

Proposition 2 (Characterization of Brownian motion by covariance):
non-included
No formalization of Brownian motion exists in mathlib, so this characterization via the covariance function E(B(s)B(t)) = min(s,t) is not present.

Lemma 2 (Fourth moment bound for Gaussians):
non-included
Searched for moment bounds for Gaussian random variables. While basic Gaussian distribution properties exist in `Mathlib/Probability/Distributions/Gaussian/`, the specific fourth moment bound E(|a_1|^4) = 3 and the product bound are not formalized.

Lemma 3 (Beta integral bound):
non-included
Searched for beta integral and related bounds. While the beta function and gamma function are developed in `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`, the specific bound R_beta(m) <= 100 m^{-1-beta} for the integral of r^m (1-r)^beta is not formalized.

Lemma 4 (Integrability of gradient of random power series):
non-included
This is a specialized result about random power series with Gaussian coefficients. No formalization of random power series or their gradient integrability properties was found in mathlib.

Lemma 5 (Holder continuity from gradient bound):
non-included
Searched for Holder continuity results derived from gradient bounds. While `Mathlib/MeasureTheory/Function/Holder.lean` contains Holder function infrastructure, the specific result about Holder continuity of boundary values of analytic functions from interior gradient bounds is not formalized.
