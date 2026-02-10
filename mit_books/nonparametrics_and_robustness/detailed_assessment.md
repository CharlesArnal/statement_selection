# Detailed Assessment - Nonparametrics and Robustness

## Statement 1: Theorem 1.1 (Bretagnolle-Massart KMT Theorem)
**Status**: non-included
This is the main KMT (Komlos-Major-Tusnady) theorem giving an explicit rate of approximation of the empirical process by a Brownian bridge in the sup norm, with specific constants c=12, K=2, lambda=1/6. Searched in Mathlib/Probability/ and Mathlib/MeasureTheory/. Mathlib has no formalization of empirical processes, Brownian bridges, or KMT-type strong approximation results. No Brownian bridge or empirical distribution function is defined in mathlib.

## Statement 2: Lemma 1.2 (Tusnady's Lemma - Binomial-Normal Approximation)
**Status**: non-included
Quantitative bound on approximation of quantile-transformed binomial by normal. Searched in Mathlib/Probability/ProbabilityMassFunction/Binomial.lean and Mathlib/Probability/Distributions/Gaussian/. Mathlib has a PMF for the binomial distribution and a Gaussian distribution, but no quantile functions (inverse CDFs), and no quantitative coupling or approximation results between discrete and continuous distributions.

## Statement 3: Theorem 1.3 (Probability Integral Transform)
**Status**: non-included
States that if F is continuous, F(X) ~ U[0,1], and F^{-1}(V) has distribution F when V ~ U[0,1]. Searched in Mathlib/Probability/CDF.lean and Mathlib/Probability/Distributions/Uniform.lean. Mathlib has a CDF definition and properties (monotonicity, limits), and a notion of uniform distribution, but the probability integral transform theorem (that applying a continuous CDF to its random variable yields a uniform) is not formalized. No inverse CDF / quantile function is defined.

## Statement 4: Lemma 1.4 (Tusnady's Lemma - Binomial Tail Bounds)
**Status**: non-included
Precise comparison of binomial tail probabilities with normal tail probabilities. Searched in Mathlib/Probability/ProbabilityMassFunction/Binomial.lean and Mathlib/Probability/Distributions/Gaussian/. No such comparison results exist in mathlib. The binomial PMF in mathlib is defined as a probability mass function but lacks tail probability estimates.

## Statement 5: Lemma 1.5 (Stirling's Formula with Remainder)
**Status**: non-included
States that n! = (n/e)^n sqrt(2 pi n) A_n where A_n = 1 + beta_n/(12n) with beta_n decreasing to 1. Searched in Mathlib/Analysis/SpecialFunctions/Stirling.lean. Mathlib proves Stirling's formula in the form that n!/[sqrt(2n) (n/e)^n] -> sqrt(pi), and proves the lower bound sqrt(2 pi n)(n/e)^n <= n!. However, the specific correction-term formulation with A_n = 1 + beta_n/(12n) and the monotone decrease of beta_n to 1 is not formalized. Mathlib's Stirling result is asymptotic rather than giving the specific remainder structure of Lemma 1.5.

## Statement 6: Lemma 1.6 (Normal Probability on Intervals)
**Status**: non-included
A lower bound on normal probability of an interval [a,b] involving sinh. Searched in Mathlib/Probability/Distributions/Gaussian/ and Mathlib/Analysis/SpecialFunctions/. No such explicit lower bound on normal probabilities of finite intervals is available in mathlib.

## Statement 7: Lemma 1.7 (Logarithm Lower Bounds)
**Status**: non-included
Specific numerical bounds: log(1+x) >= lambda x for given pairs (alpha, lambda). Searched in Mathlib/Analysis/SpecialFunctions/Log/Basic.lean. Mathlib has log_le_sub_one_of_pos (log x <= x - 1 for x > 0), which is related but is an upper bound, not a lower bound. These specific numerical concavity bounds are not formalized.

## Statement 8: Lemma 1.8 (Log Interval Bound)
**Status**: non-included
Technical bound specific to the KMT proof construction. No relevant content in mathlib.

## Statement 9: Lemma 1.9 (Chernoff/Bennett-type Binomial Bounds)
**Status**: non-included
Exponential tail bounds for binomial random variables including Chernoff and Bennett inequalities. Searched in Mathlib/Probability/Moments/SubGaussian.lean and Mathlib/Probability/Moments/Basic.lean. Mathlib has some sub-Gaussian moment bounds (mgf_le_of_subGaussian) and mentions of Chernoff/Hoeffding-type results, but does not have the specific Chernoff bound for binomial random variables, nor Bennett's inequality. The formulations in mathlib are for sub-Gaussian random variables, not specifically for binomials.

## Statement 10: Lemma 1.10 (Empirical Process on Intervals)
**Status**: non-included
Tail bound for the empirical process restricted to an interval using the martingale property and Bennett's inequality. No empirical process is formalized in mathlib. Searched in Mathlib/Probability/ extensively.

## Statement 11: Lemma 1.11 (Brownian Bridge Supremum Distribution)
**Status**: non-included
Exact distribution and exponential bound for the supremum of a Brownian bridge on a subinterval. No Brownian bridge is defined in mathlib. Searched for "BrownianBridge", "brownian_bridge", "Brownian" in Mathlib/Probability/.

## Statement 12: Lemma 1.12 (Linearity of Isonormal Process)
**Status**: non-included
An isonormal process on a Hilbert space H is linear: L(cf+g) = cL(f) + L(g) a.s. No isonormal process or Gaussian process is defined in mathlib. Searched for "isonormal", "GaussianProcess", "WienerProcess" in mathlib -- no results.

## Statement 13: Lemma 1.13 (Affine Functions and Schauder Coefficients)
**Status**: non-included
If f is affine, its Schauder coefficients f_{j,k} = 0. No Schauder basis is formalized in mathlib. Searched for "Schauder" and "schauder_basis" -- no results.

## Statement 14: Lemma 1.14 (Schauder Expansion - Finite)
**Status**: non-included
Piecewise linear approximation [f]_r expressed via Schauder basis. No Schauder basis formalization exists in mathlib.

## Statement 15: Lemma 1.15 (Schauder Expansion - Continuous Functions)
**Status**: non-included
Uniform convergence of Schauder expansion for continuous functions on [0,1]. No Schauder basis in mathlib.

## Statement 16: Lemma 1.16 (Wiener and Bridge Schauder Coefficients)
**Status**: non-included
Equality of Schauder coefficients of Brownian bridge and Wiener process. Neither Wiener process nor Brownian bridge nor Schauder basis is in mathlib.

## Statement 17: Lemma 1.17 (Independence of Bridge Schauder Coefficients)
**Status**: non-included
The Schauder coefficients W_{j,k}(B_.) are independent N(0, 2^{-j-2}). No Brownian bridge, Wiener process, or Schauder basis in mathlib.

## Statement 18: Lemma 1.18 (Orthogonality of Haar Functions)
**Status**: non-included
The Haar-like functions g_{j,k} are orthogonal in L^2([0,1]). Searched for "Haar" and "haar_basis" in mathlib -- no Haar basis or Haar wavelet formalization found. Mathlib does have L^2 inner product spaces but not these specific functions.

## Statement 19: Theorem (Delta Method)
**Status**: non-included
If sqrt(n)(Y_n - mu) -> N(0, sigma^2) in distribution and f is differentiable at mu, then sqrt(n)(f(Y_n) - f(mu)) -> N(0, f'(mu)^2 sigma^2). Searched for "delta method", "asymptotic normal" in mathlib -- no results. Mathlib lacks the general theory of convergence in distribution and central limit theorem-type results. The Gaussian distribution is defined (Mathlib/Probability/Distributions/Gaussian/) but convergence in distribution to a Gaussian is not formalized.

## Statement 20: Theorem 1 (Affine Equivariance and Symmetry)
**Status**: non-included
Consequences of affine equivariance for location/scatter functionals at symmetric/invariant distributions. This is specific to robust statistics. Searched in Mathlib/Probability/ and Mathlib/LinearAlgebra/AffineSpace/. No robustness or equivariance concepts for statistical functionals exist in mathlib.

## Statement 21: Proposition 2 (Equivariant Functionals and Breakdown)
**Status**: non-included
Existence of laws with prescribed mass on a compact set such that all affinely equivariant location functionals diverge. Purely a robust statistics result; no such concepts in mathlib.

## Statement 22: Theorem 3 (Obenchain - Singularly Affine Equivariant Location)
**Status**: non-included
Singularly affine equivariant location functional on R^d for d >= 2 must be the sample mean. Statistical functional theory; not in mathlib.

## Statement 23: Theorem 4 (Singularly Affine Equivariant Scatter)
**Status**: non-included
Singularly affine equivariant scatter functional on R^d for d >= 2 must be proportional to sample covariance when applied to centered data. Statistical functional theory; not in mathlib.

## Statement 24: Theorem 5 (Breakdown-Collapse Tradeoff)
**Status**: non-included
For affinely equivariant scatter functionals, breakdown point + collapse point <= 1. Robust statistics; not in mathlib.

## Statement 25: Proposition 6 (Location Functional Continuity Obstruction)
**Status**: non-included
Affinely equivariant location functional with delta_C^* = 1/2 cannot be extended continuously to certain discrete laws. Robust statistics; not in mathlib.

## Statement 26: Theorem 7 (Upper Bounds for Breakdown Points)
**Status**: non-included
Upper bounds for replacement and contamination breakdown points of affinely equivariant functionals. Robust statistics; not in mathlib.

## Statement 27: Proposition 8 (MVE/Shorth Non-Uniqueness)
**Status**: non-included
The minimum-volume ellipsoid and shorth functionals have breakdown point 0 at laws with continuous densities. Robust statistics; not in mathlib.

## Statement 28: Theorem 1 (Breakdown Points - Order Statistics)
**Status**: non-included
The jth order statistic Z_{(j)} has breakdown point (1/n) min(j-1, n-j). Searched in Mathlib/Probability/ -- no order statistics or breakdown point concepts in mathlib.

## Statement 29: Theorem 2 (Breakdown Point Upper Bound for Location Equivariant Statistics)
**Status**: non-included
Any real-valued statistic equivariant for location has breakdown point < 1/2. Robust statistics; not in mathlib.

## Statement 30: Proposition 3.3.4 (Adjustment Functions)
**Status**: non-included
Characterization of adjustment functions for M-estimation: a_2 is an adjustment function iff a_1 - a_2 is P-integrable. M-estimation theory; not in mathlib.

## Statement 31: Lemma 3.3.8 (Adjustability and Adjustment Functions)
**Status**: non-included
If gamma_a(theta) is real, then h(theta,.) is also an adjustment function. M-estimation theory; not in mathlib.

## Statement 32: Lemma 3.3.9 (Lower Semicontinuity of gamma)
**Status**: non-included
Under assumptions (A-1)-(A-3), gamma(theta) = E(h(theta,x) - a(x)) is lower semicontinuous via monotone convergence. Mathlib has lower semicontinuity (Mathlib/Topology/Semicontinuity/) and monotone convergence but this specific statistical application is not formalized.

## Statement 33: Lemma 3.3.10 (Compactness of M-estimator Sequences)
**Status**: non-included
Under assumptions (A-1), (A-3)-(A-5), approximate M-estimators eventually lie in a compact set. M-estimation theory; not in mathlib.

## Statement 34: Theorem 3.3.13 (Consistency of Approximate M-estimators)
**Status**: non-included
Under stated assumptions, approximate M-estimators converge almost uniformly to theta_0. This is Huber's consistency theorem for M-estimators. Not in mathlib. Mathlib has the strong law of large numbers (Mathlib/Probability/StrongLaw.lean) which is used in the proof, but the M-estimator consistency result itself is not formalized.

## Statement 35: Theorem 3.3.15 (Kullback-Leibler Divergence Nonnegativity)
**Status**: included
States I(P,Q) >= 0 with equality iff P = Q. This corresponds to two results in Mathlib/InformationTheory/KullbackLeibler/Basic.lean: the lemma `integral_llr_add_sub_measure_univ_nonneg` (Gibbs' inequality: the KL divergence is nonneg) and `klDiv_eq_zero_iff` (converse Gibbs' inequality: KL divergence between two finite measures is zero iff they are equal). The proof in mathlib uses the same core inequality log x <= x - 1 (available as `Real.log_le_sub_one_of_pos` in Mathlib/Analysis/SpecialFunctions/Log/Basic.lean).

## Statement 36: Theorem 3.3.16 (Consistency of Approximate MLE)
**Status**: non-included
Consistency of approximate maximum likelihood estimators under the stated regularity conditions. Uses Theorem 3.3.15 to verify (A-3) and (A-4). Not in mathlib; no MLE consistency theory is formalized.

## Statement 37: Theorem (Spatial Median Existence and Uniqueness)
**Status**: non-included
For any probability measure P on R^d, a spatial median exists. If P is not concentrated in a line, the spatial median is unique. Searched in Mathlib/Probability/ and Mathlib/Analysis/. No spatial median concept exists in mathlib. Mathlib has convex functions (Mathlib/Analysis/Convex/) and the notion of minimizers, but not the specific spatial median construction.

## Statement 38: Theorem (Obenchain - Full Version)
**Status**: non-included
This is essentially the same as Theorem 3 (Statement 22) but stated in the more explicit notation of the dedicated handout. Singularly affine equivariant location functional on P_{n,d} for d >= 2 must be the sample mean. Not in mathlib.

## Statement 39: Theorem (M-estimator Breakdown Point)
**Status**: non-included
M-estimator with odd, nondecreasing, nonconstant, bounded psi function has the same breakdown point as the median: (1/2 - 1/n) for n even, (1/2 - 1/(2n)) for n odd. Robust statistics; not in mathlib.
