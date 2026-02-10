Proposition 1.1:
included
This is the standard characterization of continuity between metric spaces via open preimages, closed preimages, and sequential continuity. In mathlib, `Continuous` is defined topologically via open preimages in `Mathlib/Topology/Defs/Basic.lean`. The sequential characterization is in `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` (e.g., `continuous_iff_sequentialContinuous` for first-countable spaces). The closed preimage version follows from `Continuous.isClosedPreimage`.

Proposition 1.2:
included
The equivalence of all norms on finite-dimensional spaces is a classical result. In mathlib, this is established via `LinearMap.continuous_of_finiteDimensional` and related results in `Mathlib/Analysis/NormedSpace/FiniteDimension.lean`. The key result is that any linear map from a finite-dimensional space is continuous, which implies norm equivalence.

Proposition 1.3:
included
The equivalence of continuity, continuity at 0, boundedness of the unit ball image, and the operator norm bound for linear functionals on normed spaces. In mathlib, this is captured by `LinearMap.continuous_iff_isClosed_ker`, `ContinuousLinearMap` machinery, and `NormedSpace.operatorNorm` in `Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean` and related files. The key characterization is that a linear map is continuous iff it is bounded.

Lemma 1.4:
included
Decomposition of a continuous function into positive and negative parts. In mathlib, this is handled via the lattice structure on continuous functions. The positive and negative parts are defined via `f \sqcup 0` and `(-f) \sqcup 0` in `Mathlib/Topology/ContinuousFunction/Ordered.lean`. The fact that max and min of continuous functions are continuous is a basic result.

Lemma 1.5:
non-included
The Jordan decomposition of a continuous linear functional on C_0(X) into the difference of two positive functionals. While mathlib has the Jordan decomposition for signed measures in `Mathlib/MeasureTheory/VectorMeasure/Decomposition/JordanSub.lean` and `Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean`, the specific statement about decomposing a functional on C_0(X) at the functional level (before the Riesz representation theorem is applied) does not appear to be directly formalized.

Lemma 1.7:
included
That the construction from a positive linear functional on C_0(X) yields an outer measure. This is part of the Riesz-Markov-Kakutani representation theorem construction in mathlib. The outer measure construction appears in `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean` and `Mathlib/MeasureTheory/Measure/Content.lean`.

Lemma 1.8:
included
Existence of a smooth (or continuous) partition of unity subordinate to an open cover of a compact set in a locally compact metric space. In mathlib, partitions of unity are developed in `Mathlib/Topology/PartitionOfUnity.lean` and `Mathlib/Topology/MetricSpace/PartitionOfUnity.lean`, where `BumpCovering` and `PartitionOfUnity` types provide subordinate partitions.

Proposition 2.3:
included
That the collection of Caratheodory measurable sets for any outer measure forms a sigma-algebra. In mathlib, this is the core of `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`, where `OuterMeasure.IsCaratheodory` defines measurability and the measurable sets are shown to form a sigma-algebra via `OuterMeasure.caratheodoryMeasurableSpace`.

Theorem 2.4:
included
Caratheodory's theorem: the Caratheodory measurable sets form a sigma-algebra and the outer measure restricted to them is a complete measure. This is the main result of `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`. The construction `OuterMeasure.toMeasure` produces a measure from an outer measure.

Proposition 2.5:
included
That open sets are measurable for the outer measure constructed from a positive functional on C_0(X). This is part of the Riesz-Markov-Kakutani construction in `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean`, where the resulting measure is shown to be a Borel measure (hence all open sets are measurable).

Proposition 2.6:
included
That the measure constructed from a positive functional via Caratheodory's theorem is a Borel measure. This follows from the Riesz-Markov-Kakutani representation in mathlib, where the constructed measure is shown to be a Borel measure. See `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean`.

Proposition 2.8:
included
That the measure constructed is a Radon measure (inner regular on open sets, outer regular on Borel sets). In mathlib, the Riesz-Markov-Kakutani theorem produces a regular measure; regularity properties are in `Mathlib/MeasureTheory/Measure/Regular.lean`.

Lemma 2.9:
included
That the outer measure of a rectangular set equals its standard volume. This is part of the construction of Lebesgue measure in mathlib. The volume of rectangles/boxes is handled in `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` and related files.

Proposition 2.10:
included
That Lebesgue measure is a Borel measure. In mathlib, Lebesgue measure is defined as `MeasureTheory.volume` on `R^n` and is a Borel measure by construction. See `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`.

Lemma 3.1:
included
That measurability can be checked on a generating set of the target sigma-algebra. In mathlib, this corresponds to `Measurable.of_generating` or the general framework where measurability is checked on generators of the Borel sigma-algebra. The relevant infrastructure is in `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.

Proposition 3.2:
included
That continuous maps between metric spaces are Borel measurable. In mathlib, this is `Continuous.measurable` in `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`, which states that continuous functions between topological spaces with Borel sigma-algebras are measurable.

Proposition 3.3:
included
Approximation of non-negative measurable functions by an increasing sequence of simple functions. In mathlib, this is `MeasureTheory.SimpleFunc.eapprox_tendsto` and related results in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`.

Lemma 4.2:
included
That the integral of a non-negative function over E is zero iff the function is zero a.e. on E. In mathlib, this is captured by `MeasureTheory.lintegral_eq_zero_iff` in `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`.

Theorem 4.3:
included
The Monotone Convergence Theorem for the Lebesgue integral. In mathlib, this is `MeasureTheory.lintegral_iSup` and `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone` in `Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean` and `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`.

Lemma 4.5:
included
Fatou's lemma for non-negative functions. In mathlib, this is `MeasureTheory.lintegral_liminf_le` in `Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`.

Theorem 4.6:
included
The Dominated Convergence Theorem. In mathlib, this is `MeasureTheory.tendsto_integral_of_dominated_convergence` in `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` for Bochner integrals and `MeasureTheory.lintegral_tendsto_of_dominated_convergence` for extended non-negative integrals.

Lemma 4.7:
included
Young's inequality for products: a^gamma * b^{1-gamma} <= gamma*a + (1-gamma)*b. In mathlib, this is a special case of the AM-GM inequality. The relevant result is `Real.inner_le_iff` or `Young.inner_le_Lp_mul_Lq`-type results, and more directly `Real.rpow_natCast` related inequalities. A version appears as `Real.add_rpow_le_mul_rpow_of_nonneg` and related in `Mathlib/Analysis/MeanInequalities.lean`.

Lemma 4.8:
included
Holder's inequality. In mathlib, this is `MeasureTheory.NNNorm.inner_le_Lnorm_mul_Lnorm` and `MeasureTheory.inner_le_Lnorm_mul_Lnorm` and related results in `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` and `Mathlib/Analysis/MeanInequalities.lean`.

Proposition 4.9:
included
Minkowski's inequality (triangle inequality for L^p norms). In mathlib, this is established as part of showing that `Lp` is a normed space. The triangle inequality for `L^p` seminorms is in `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`.

Theorem 4.11:
included
That L^p spaces are Banach spaces (complete normed spaces). In mathlib, the completeness of `Lp` spaces is `Lp.instCompleteSpace` in `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`.

Theorem 4.12:
included
The Riesz representation theorem identifying the dual of C_0(X) with finite Radon measures. In mathlib, the Riesz-Markov-Kakutani representation theorem is developed in `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean`, `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`, and `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`.

Lemma 5.2:
included
That a closed convex subset of a Hilbert space contains a unique element of smallest norm. In mathlib, this is `exists_norm_eq_iInf_of_complete_convex` and `norm_eq_iInf_iff_inner_le_zero` in `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` and `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`.

Proposition 5.3:
included
The Riesz representation theorem for Hilbert spaces: every continuous linear functional is of the form u(phi) = <phi, v> for a unique v. In mathlib, this is `InnerProductSpace.toDual` and related results in `Mathlib/Analysis/InnerProductSpace/LinearMap.lean`, which establish the isometric isomorphism between a Hilbert space and its dual.

Corollary 5.4:
included
That continuous linear functionals on L^2 are given by integration against an L^2 function. This follows directly from the Hilbert space Riesz representation (Proposition 5.3) applied to L^2, which is a Hilbert space in mathlib. The inner product on `Lp` is in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`.

Lemma 6.1:
included
If V embeds continuously and densely in W, then the dual of W embeds continuously in the dual of V. In mathlib, this is a consequence of the general theory of continuous linear maps and their adjoints/transposes. The relevant infrastructure is in `Mathlib/Topology/Algebra/Module/StrongTopology.lean` and `Mathlib/Analysis/NormedSpace/Dual.lean`.

Proposition 6.3:
included
That C_0^1(R^n) with the norm ||u||_{C^1} = ||u||_infinity + sum||partial_i u||_infinity is a Banach space. In mathlib, the completeness of spaces of continuously differentiable functions with bounded derivatives is established via `ContDiff` and the associated norms. The completeness of C^k with the standard norm follows from the completeness of C^0 (which is `BoundedContinuousFunction.instCompleteSpace`). Relevant infrastructure is in `Mathlib/Topology/ContinuousFunction/Bounded/Basic.lean`.

Proposition 6.7:
non-included
That S(R^n) is a complete metric space with the metric d(u,v) = sum 2^{-k} ||u-v||_{(k)}/(1+||u-v||_{(k)}). While mathlib defines the Schwartz space `SchwartzMap` as a Frechet space with its seminorms in `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean`, the specific metric defined here via the standard trick for converting a countable family of seminorms into a metric is not explicitly formalized in this exact form. The topology on SchwartzMap is defined differently.

Corollary 7.2:
non-included
Equivalence of different Schwartz space seminorm families. While mathlib defines the Schwartz space `SchwartzMap` in `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean` with its seminorms, the specific equivalence of the seminorm families stated here (using multi-index notation) is not explicitly formalized in this exact form.

Lemma 7.1:
included
Characterization of Schwartz functions: phi is in S(R^n) iff phi is smooth and sup|x^alpha D^beta phi| < infinity for all multi-indices. In mathlib, this is essentially the definition of `SchwartzMap` in `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean`, where a Schwartz function is defined via rapid decay of all derivatives.

Proposition 7.3:
included
A linear functional on S(R^n) is continuous iff it is bounded by a Schwartz seminorm. In mathlib, the topology on `SchwartzMap` is defined by the family of seminorms in `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean`, and continuity of linear functionals is characterized by boundedness with respect to these seminorms. Tempered distributions are defined in `Mathlib/Analysis/Distribution/TemperedDistribution.lean`.

Lemma 7.5:
non-included
That the support of a tempered distribution (defined via the largest open set on which it vanishes) is closed. While mathlib defines `SchwartzMap` and tempered distributions, the specific notion of support for tempered distributions and the proof that it is closed is not explicitly formalized in mathlib.

Proposition 8.1:
included
If v is in C_0^0(R^n) and psi is in S(R^n) then their convolution is in C_0^0 and satisfies the sup-norm bound. Convolution is defined in `Mathlib/Analysis/Convolution.lean` (via `MeasureTheory.Convolution`) and bounds on convolutions are available there.

Proposition 8.2:
included
Approximation to the identity: v * phi_t -> v in C_0^0 as t -> 0. In mathlib, approximation to the identity results appear in `Mathlib/Analysis/Convolution.lean` and `Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`, where convolution with mollifiers is shown to converge.

Corollary 8.3:
non-included
That C_0^k is dense in C_0^p for k >= p. This specific density result for the spaces C_0^k with the C^p topology is not explicitly formalized in mathlib in this generality.

Proposition 8.4:
non-included
That S(R^n) is dense in C_0^k(R^n) for any k >= 0. While mathlib has density results for smooth functions (e.g., `ContDiff.dense`-type results), the specific statement about density of Schwartz space in C_0^k is not directly available.

Corollary 8.5:
non-included
Injectivity of the map from finite Radon measures to tempered distributions. This specific embedding result is not formalized in mathlib.

Proposition 8.6:
included
Continuity in the mean for L^2 functions: ||tau_t f - f||_{L^2} -> 0 as t -> 0. In mathlib, translation continuity in L^p is available; see `MeasureTheory.Lp.continuous_translation` or related results about the action of translations being continuous on L^p spaces.

Proposition 8.7:
included
Smooth partition of unity subordinate to an open cover of a compact set. In mathlib, this is `SmoothPartitionOfUnity` and `BumpCovering.toPartitionOfUnity` in `Mathlib/Topology/PartitionOfUnity.lean` and `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`.

Lemma 8.8:
non-included
That C_c^infinity(R^n) is dense in S(R^n). While mathlib defines `SchwartzMap` and `HasCompactSupport`, the density of compactly supported smooth functions in the Schwartz space topology is not explicitly stated in mathlib.

Proposition 8.9:
non-included
If u in S'(R^n) and supp(u) is empty then u = 0. While this is a basic fact about distributions, mathlib's tempered distribution infrastructure in `Mathlib/Analysis/Distribution/TemperedDistribution.lean` does not include a formalization of support for distributions or this vanishing result.

Proposition 8.10:
non-included
If u in S'(R^n) satisfies x_j u = 0 for all j then u = c*delta. This characterization of distributions supported at the origin is a classical result in distribution theory, but it is not formalized in mathlib.

Proposition 8.11:
included
Fourier transform is a continuous linear map on S(R^n). In mathlib, the Fourier transform on Schwartz space is defined and shown to be continuous in `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`.

Lemma 8.12:
included
The Fourier transform of the Gaussian exp(-|x|^2/2) is (2*pi)^{n/2} exp(-|xi|^2/2). In mathlib, this is `fourierIntegral_gaussian` or related results in `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`.

Theorem 9.1:
included
The Fourier transform is an isomorphism on S(R^n). In mathlib, the Fourier transform on Schwartz space is shown to be a topological linear equivalence in `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`.

Lemma 9.2:
included
Parseval's identity for Schwartz functions. In mathlib, Parseval/Plancherel results are in `Mathlib/Analysis/Fourier/FourierTransform.lean`, establishing the isometry property of the Fourier transform on L^2.

Proposition 9.3:
included
The Plancherel theorem: the Fourier transform extends to a unitary isomorphism L^2(R^n) -> L^2(R^n). In mathlib, this is established in `Mathlib/Analysis/Fourier/FourierTransform.lean` and `Mathlib/Analysis/Fourier/LpSpace.lean`, where the Fourier transform is shown to extend to an isometry on L^2.

Lemma 9.4:
non-included
Characterization of integer-order Sobolev spaces: u in H^m(R^n) iff D^alpha u in L^2 for |alpha| <= m. Mathlib does not have a formalization of Sobolev spaces H^m(R^n) in the classical PDE sense, though it has some pieces like derivatives of L^p functions.

Proposition 9.6:
non-included
Fourier transform gives an isomorphism of Sobolev spaces H^m(R^n). Since Sobolev spaces H^m(R^n) are not formalized in mathlib, this result is not available.

Proposition 9.7:
non-included
Characterization of negative-order Sobolev spaces as sums of derivatives of L^2 functions. Sobolev spaces of negative order are not formalized in mathlib.

Proposition 9.8:
non-included
Each Sobolev space H^m(R^n) is a Hilbert space. Since Sobolev spaces are not formalized in mathlib, this is not available.

Theorem 10.1:
non-included
The Sobolev embedding theorem: H^m(R^n) embeds in C_0^0(R^n) for m > n/2. Sobolev embedding is not formalized in mathlib. Searched `Mathlib/Analysis` for `SobolevEmbedding`, `sobolev_embedding`, `ContDiff.*Sobolev` with no results.

Corollary 10.3:
non-included
If m > n/2 + k then H^m(R^n) embeds in C_0^k(R^n). This extension of Sobolev embedding is not in mathlib since Sobolev spaces themselves are not formalized.

Proposition 10.2:
non-included
Differentiation maps H^m to H^{m-|alpha|}. Since Sobolev spaces are not formalized in mathlib, this result is not available.

Proposition 10.4:
non-included
S(R^n) equals the intersection of weighted Sobolev spaces. Since general (weighted) Sobolev spaces are not in mathlib, this characterization is not available.

Theorem 10.5:
non-included
Schwartz representation theorem: every tempered distribution is a finite sum of derivatives of continuous functions vanishing at infinity. This structural result about tempered distributions is not formalized in mathlib.

Lemma 10.6:
non-included
A technical identity involving <x>^{2N}, derivatives, and polynomials used in the Schwartz representation theorem. Not formalized in mathlib.

Proposition 11.1:
non-included
S(R^n) is weakly dense in S'(R^n). While mathlib defines tempered distributions as the dual of Schwartz space, the weak density statement is not explicitly formalized.

Proposition 11.2:
non-included
Weak convergence in S'(R^n) is preserved under linear operations, differentiation, and multiplication by polynomials. Not explicitly stated in mathlib's distribution theory.

Theorem 11.4:
non-included
The Malgrange-Ehrenpreis theorem: every non-zero constant coefficient differential operator has a tempered fundamental solution. This deep result from PDE theory is not formalized in mathlib. Searched for `hypoelliptic`, `elliptic.*operator`, `EllipticOperator` with no results.

Lemma 11.5:
non-included
The Cauchy kernel E(x,y) = -1/(2*pi*(x+iy)) is locally integrable and satisfies d-bar E = delta. This specific PDE result about the fundamental solution of d-bar is not in mathlib.

Theorem 11.6:
non-included
Properties of convolution of a tempered distribution with a Schwartz function: smoothness, support containment, and singular support containment. While mathlib has some convolution theory, these distribution-theoretic results are not formalized.

Lemma 11.7:
non-included
Convolution of a compactly supported tempered distribution with a Schwartz function is Schwartz. Not formalized in mathlib.

Theorem 11.9:
non-included
For hypoelliptic operators P(D), sing supp(u) = sing supp(P(D)u). The concepts of hypoellipticity and singular support are not formalized in mathlib.

Lemma 11.10:
non-included
Multiplication of a tempered distribution by a polynomial is well-defined in S'(R^n). While mathlib's Schwartz space has multiplication by polynomials on the function side, the distribution-side statement is not explicitly available.

Theorem 11.12:
non-included
Every elliptic differential operator is hypoelliptic. Neither ellipticity nor hypoellipticity is defined in mathlib. Searched for `elliptic`, `hypoelliptic`, `EllipticOperator` with no results.

Lemma 11.13:
non-included
Construction of a parametrix for homogeneous elliptic operators via the Fourier transform. This is part of elliptic PDE theory not formalized in mathlib.

Lemma 11.14:
non-included
Derivative estimates for the reciprocal of an elliptic polynomial: |D^alpha(1/P(xi))| <= C_alpha |xi|^{-m-|alpha|}. A technical PDE lemma not in mathlib.

Proposition 11.15:
non-included
Singular support of convolution: sing supp(u * f) is contained in sing supp(u) + sing supp(f) when one factor has compact support. The notion of singular support is not formalized in mathlib.

Proposition 11.16:
non-included
Existence and uniqueness of forward solutions to the heat equation with compactly supported source in S'(R^n). Not formalized in mathlib.

Theorem 11.17:
non-included
Existence and uniqueness of u in C_0^infinity(R^n) solving Delta u = f for f in S(R^n), n >= 3. This solvability result for the Laplacian is not in mathlib.

Lemma 12.1:
non-included
Derivative estimates for homogeneous degree-0 smooth functions on R^n \ {0}. This technical result about homogeneous functions is not in mathlib.

Lemma 12.3:
non-included
Cone support and cone singular support of tempered distributions are closed subsets of B^n. The concepts of cone support (Csp) and cone singular support (Css) are not defined in mathlib.

Corollary 12.4:
non-included
Css(u) = empty set iff u in S(R^n). The cone singular support is not defined in mathlib.

Lemma 12.5:
non-included
Pairing of distributions with disjoint cone singular supports. Not formalized in mathlib.

Lemma 12.6:
non-included
Convolution defined when Css(u) does not meet S^{n-1}. Not in mathlib.

Lemma 12.7:
non-included
Decomposition of distributions relative to a closed set on the sphere. Not in mathlib.

Lemma 12.8:
non-included
Css(phi * u) is contained in Css(u) intersect S^{n-1} for phi in S(R^n). Not in mathlib.

Corollary 12.9:
non-included
Bound on Css of convolution. Not in mathlib.

Lemma 12.10:
non-included
Convolution defined under antipodal cone singular support condition. Not in mathlib.

Lemma 12.11:
non-included
Css of the Fourier transform of a conic cutoff is contained in {0}. Not in mathlib.

Lemma 12.13:
non-included
Stability of the wavefront set complement under localization. The wavefront set (WF and WF_sc) is not defined in mathlib. Searched for `waveFrontSet`, `singularSupport`, `WaveFrontSet` with no results.

Proposition 12.14:
non-included
Structure of WF_sc(u) as a closed subset of the boundary of B^n x B^n, and projection properties relating WF to singular support and WF_sc to cone singular support. Not in mathlib.

Corollary 12.15:
non-included
WF_sc(u) = empty set iff u in S(R^n). Not in mathlib.

Proposition 12.16:
non-included
Decomposition characterization of points not in WF_sc(u). Not in mathlib.

Corollary 12.17:
non-included
Symmetry of WF_sc under Fourier transform: (p, q) in WF_sc(u) iff (q, -p) in WF_sc(hat{u}). Not in mathlib.

Theorem 12.18:
non-included
Product and convolution of distributions defined under wavefront set conditions. This is the main microlocal multiplication/convolution theorem. Not in mathlib.

Proposition 16.1:
included
The spectrum of a bounded linear operator on a Hilbert space is a compact subset of {|z| <= ||T||}. In mathlib, `spectrum.isCompact` is in `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`, and the bound `spectrum.subset_closedBall_norm` or equivalent appears there as well. The Neumann series argument is in `Mathlib/Analysis/Normed/Ring/Units.lean`.

Proposition 16.2:
included
For a bounded self-adjoint operator A, the spectrum is contained in [m, M] where m and M are the infimum and supremum of <Ax, x> over unit vectors, and both m and M are in the spectrum. In mathlib, results about the spectrum of self-adjoint operators being real are in `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean` and `Mathlib/Analysis/Matrix/Spectrum.lean`. The characterization `IsSelfAdjoint.spectrum_subset_real` and spectral bounds are available.

Proposition 16.3:
included
The polynomial functional calculus estimate: ||p(A)|| <= sup_{t in [m,M]} |p(t)| for self-adjoint A. In mathlib, the continuous functional calculus for C*-algebras is developed in `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` and related files. The isometric property of the CFC map `cfcHom` implies this norm bound, as the CFC extends the polynomial calculus and preserves the spectral norm.
