# Detailed Assessment: Functions of a Complex Variable (18.112)

## Theorem 1 (Lecture 2) [b^x = E(xL(b))]:
included
The identity $b^x = \exp(x \log b)$ for real $b > 0$ and $x \in \mathbb{R}$ is a basic property of the real exponential and logarithm in Mathlib. The real exponential and logarithm are defined in `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` and `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`. The relation `Real.rpow_def_of_pos` in `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` establishes $b^x = \exp(x \cdot \log b)$ for positive $b$.

## Corollary 1 (Lecture 2) [b^{x+y} = b^x b^y]:
included
This is the additive-to-multiplicative homomorphism property of $b^x$. It follows directly from `Real.rpow_add` in `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, which states that for $b > 0$, $b^{x+y} = b^x \cdot b^y$.

## Proposition 1 (Lecture 2) [e^{z+w} = e^z e^w]:
included
The complex exponential's additive homomorphism property $e^{z+w} = e^z e^w$ is `Complex.exp_add` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean` (or more precisely, it comes from the general `exp_add` for normed algebras in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean` and the underlying definition in `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`).

## Theorem 2 (Lecture 2) [Roots of unity]:
included
The characterization of roots of $z^n = 1$ as powers of $\omega = e^{2\pi i/n}$ is covered in Mathlib. The primitive roots of unity are developed in `Mathlib/RingTheory/RootsOfUnity/Complex.lean` and `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`. In particular, `Complex.isPrimitiveRoot_exp_of_coprime` and related results establish that $e^{2\pi i/n}$ is a primitive $n$-th root of unity.

## Theorem 3 (Lecture 2) [Log of a product]:
included
The relationship $\operatorname{Log}(z_1 z_2) = \operatorname{Log}(z_1) + \operatorname{Log}(z_2) + n \cdot 2\pi i$ for $n \in \{0, \pm 1\}$ is addressed in Mathlib. The complex logarithm is defined in `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`. The result `Complex.log_mul_eq_add_log_iff` and related lemmas describe when $\log(z_1 z_2) = \log z_1 + \log z_2$ and the conditions on the arguments.

## Theorem 1 (Lecture 3) [Gauss-Lucas]:
included
The Gauss-Lucas theorem is proved in `Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean`. The main result `Polynomial.rootSet_derivative_subset_convexHull_rootSet` states that the roots of $P'$ lie in the convex hull of the roots of $P$, which is exactly the "stronger version" stated in the lecture.

## Proposition 1 (Lecture 3) [Convex hull as convex combinations]:
included
The characterization of the convex hull of a finite set as the set of convex combinations is a standard result in Mathlib. It is proved as `Finset.convexHull_eq` in `Mathlib/Analysis/Convex/Combination.lean` and `convexHull_eq` for general sets, showing that $\operatorname{convexHull}(S) = \{\sum m_i a_i \mid m_i \ge 0, \sum m_i = 1, a_i \in S\}$.

## Theorem 1 (Lecture 6) [Nonintersecting circles mapped to concentric circles]:
non-included
This result states that any two nonintersecting circles can be mapped to concentric circles via a Mobius transformation. I searched `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`, `Mathlib/Analysis/Complex/Circle.lean`, and `Mathlib/Analysis/Complex/Conformal.lean`. Mathlib has the action of $\operatorname{SL}_2(\mathbb{R})$ on the upper half-plane and basic conformal map theory, but does not contain this specific geometric result about mapping nonintersecting circles to concentric circles.

## Theorem 1 (Lecture 8) [Integration by substitution for complex integrals]:
non-included
The complex change-of-variables formula $\int_{\varphi(\gamma)} f(w)\, dw = \int_{\gamma} f(\varphi(z)) \varphi'(z)\, dz$ for holomorphic $\varphi$ is not directly stated in Mathlib. I searched `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` and `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`. While Mathlib has the real change-of-variables formula and various circle integral results, the general complex contour substitution theorem is not formalized.

## Theorem 2 (Lecture 8) [Integral of R(z^2) over circle is zero]:
non-included
This result that $\int_{\gamma} R(z^2)\, dz = 0$ for any circle $\gamma$ around the origin (when $R(z^2) \neq 0$ on $\gamma$) is a specific consequence of the substitution $z \mapsto -z$. I searched in `Mathlib/MeasureTheory/Integral/CircleIntegral.lean` and `Mathlib/Analysis/Complex/CauchyIntegral.lean` and found no corresponding result.

## Theorem 1 (Lecture 10) [Taylor's Theorem for analytic functions]:
included
Taylor's theorem for holomorphic functions is well-covered in Mathlib. The file `Mathlib/Analysis/Complex/TaylorSeries.lean` provides `Complex.hasSum_taylorSeries_on_ball` and `Complex.taylorSeries_eq_on_ball`, showing that a holomorphic function equals its Taylor series on any ball contained in the domain. The more general framework `DiffContOnCl.hasFPowerSeriesOnBall` in `Mathlib/Analysis/Complex/CauchyIntegral.lean` also establishes power series representations via Cauchy integrals.

## Theorem 9 (Lecture 11) [Casorati-Weierstrass]:
non-included
The Casorati-Weierstrass theorem states that a holomorphic function comes arbitrarily close to any complex value in every neighborhood of an essential singularity. I searched for "Casorati", "Weierstrass.*essential", "essential.*singularity" in Mathlib and found no matches. While Mathlib has the removable singularity theorem in `Mathlib/Analysis/Complex/RemovableSingularity.lean`, the Casorati-Weierstrass theorem about the dense image near essential singularities is not present.

## Theorem 1 (Lecture 13) [Cauchy's Theorem, general form]:
included
The general form of Cauchy's theorem (for curves homologous to zero) is established in Mathlib. The file `Mathlib/Analysis/Complex/CauchyIntegral.lean` contains results such as `DiffContOnCl.circleIntegral_eq_zero` and `circleIntegral_eq_zero_of_differentiable_on_off_countable`, which prove that the integral of a holomorphic function over a circle (or suitable closed curve) in a simply connected domain is zero. The simply connected case is also handled.

## Theorem 2 (Lecture 13) [Cauchy's Integral Formula, general form]:
included
The Cauchy integral formula is proved in `Mathlib/Analysis/Complex/CauchyIntegral.lean`. The key results are `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` and `DiffContOnCl.circleIntegral_sub_inv_smul`, which establish $f(z) = \frac{1}{2\pi i} \int_C \frac{f(\zeta)}{\zeta - z}\, d\zeta$ for holomorphic $f$ and suitable contours.

## Theorem 17' (Lecture 14) [Residue Theorem]:
non-included
The residue theorem is not formalized in Mathlib. I searched for "residue", "Residue" in `Mathlib/Analysis/Complex/` and in `Mathlib/Analysis/Meromorphic/` and found no residue theorem. The meromorphic function framework exists in `Mathlib/Analysis/Meromorphic/` but the notion of residue and the residue theorem are absent.

## Theorem 18' (Lecture 14) [Argument Principle]:
non-included
The argument principle ($\frac{1}{2\pi i} \int_{\gamma} \frac{f'}{f}\, dz = N - P$) is not in Mathlib. I searched for "argument principle", "winding number", "windingNumber" in Mathlib and found no results. The lack of a formal winding number and residue theorem means the argument principle is also missing.

## Corollary 1 (Lecture 14) [Rouche's Theorem]:
non-included
Rouche's theorem is not in Mathlib. I searched for "rouche", "Rouche" across all of Mathlib and found no matches. Since the argument principle (on which Rouche's theorem depends) is also absent, this is expected.

## Theorem 1 (Lecture 16) [Harmonic function as real part of holomorphic]:
included
The result that a harmonic function on a simply connected domain is the real part of a holomorphic function is proved in `Mathlib/Analysis/Complex/Harmonic/Analytic.lean`. The theorem `harmonic_is_realOfHolomorphic` establishes that if $f : \mathbb{C} \to \mathbb{R}$ is harmonic on an open ball, then $f$ is the real part of a holomorphic function on that ball. The simply connected case follows from the ball case.

## Corollary 1 (Lecture 16) [Mean value property for harmonic functions]:
included
The mean value property for harmonic functions is proved in `Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`. The theorem `HarmonicOnNhd.circleAverage_eq` establishes that if $f$ is harmonic in a neighborhood of a closed ball, then $f(c) = \frac{1}{2\pi} \int_0^{2\pi} f(c + re^{i\theta})\, d\theta$.

## Theorem 20 (Lecture 16) [Mean value on annulus]:
non-included
This result states that the average of a harmonic function on a circle of radius $r$ in an annulus is an affine function of $\log r$. I searched in `Mathlib/Analysis/Complex/Harmonic/` and `Mathlib/Analysis/Complex/MeanValue.lean` and `Mathlib/Analysis/Complex/CauchyIntegral.lean`. While the mean value property on a disk is in Mathlib, this extension to annuli (showing $\frac{1}{2\pi}\int_0^{2\pi} u(z_0 + re^{i\theta})\, d\theta = \alpha \log r + \beta$) is not present.

## Theorem 2 (Lecture 16) [Schwarz / Poisson integral theorem]:
non-included
The Schwarz-Poisson theorem states that the Poisson integral of a piecewise continuous boundary function is harmonic in the disk and recovers the boundary values at points of continuity. I searched for "Poisson" and "Schwarz" in `Mathlib/Analysis/Complex/` and the harmonic function files. While the Poisson kernel appears implicitly in some Cauchy integral computations, the full Schwarz theorem with boundary value recovery is not formalized in Mathlib.

## Theorem 1 (Lecture 17) [Mittag-Leffler's Theorem]:
non-included
The Mittag-Leffler theorem (constructing meromorphic functions with prescribed poles and singular parts) is not in Mathlib. I searched for "MittagLeffler", "mittag_leffler" and found references only in `Mathlib/CategoryTheory/CofilteredSystem.lean` (the categorical Mittag-Leffler condition, which is a different concept) and `Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean` (which mentions it in a docstring but does not prove the general theorem). The complex-analytic Mittag-Leffler theorem is absent.

## Lemma 1 (Lecture 17) [Abel/Dirichlet summation test]:
included
The Dirichlet summation test (also known as Abel's summation by parts) is in Mathlib. The relevant results are in `Mathlib/Topology/Algebra/InfiniteSum/Dini.lean` and `Mathlib/Analysis/Normed/Group/InfiniteSum.lean`. The general summation by parts formula and convergence criteria for $\sum a_n v_n$ when partial sums of $a_n$ are bounded and $v_n$ is decreasing to zero are covered by `Finset.sum_by_parts` (Abel summation) and `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` and related results.

## Theorem 1 (Lecture 19) [Montel's Theorem]:
non-included
Montel's theorem (that a uniformly bounded family of holomorphic functions on a region has a subsequence converging uniformly on compact subsets) is not in Mathlib. I searched for "Montel", "normal family", "normalFamily" in Mathlib. The Arzela-Ascoli theorem exists in `Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`, but the specific complex-analytic version (Montel's theorem), which requires proving equicontinuity from uniform boundedness via Cauchy's estimates, is not formalized.

## Theorem 1 (Lectures 21-22) [Newman's Tauberian Theorem]:
non-included
Newman's analytic/Tauberian theorem (used in the short proof of the Prime Number Theorem) states that if $f(t)$ is bounded and locally integrable with Laplace transform $g(z)$ extending holomorphically to $\operatorname{Re}(z) \ge 0$, then $\int_0^\infty f(t)\, dt = g(0)$. I searched for "Newman", "Tauberian", "prime number theorem" in Mathlib. While `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` proves $\zeta(s) \ne 0$ on $\operatorname{Re}(s) \ge 1$ and `Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean` has the Euler product, the Tauberian theorem and the Prime Number Theorem itself are not yet in Mathlib (only partial Chebyshev-type bounds in `Mathlib/NumberTheory/Chebyshev.lean`).
