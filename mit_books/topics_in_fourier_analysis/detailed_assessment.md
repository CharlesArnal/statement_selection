# Detailed Assessment: Topics in Fourier Analysis Statements in Mathlib

## Statement 1: Theorem 1.1
**Status**: non-included
**Explanation**: This theorem states that for $\varphi \in L^p(\lambda_{[0,1]}; \mathbb{C})$, the Abel-summed Fourier series $\sum r^{|m|} (\varphi, \mathfrak{e}_m) \mathfrak{e}_m$ converges to $\varphi$ in $L^p$ as $r \nearrow 1$, and uniformly for continuous periodic functions. Mathlib has `span_fourierLp_closure_eq_top` which shows the span of Fourier monomials is dense in $L^p$ spaces, but this specific Abel-summation convergence result (involving the factor $r^{|m|}$) is not formalized. Searched for Abel summation in Fourier context, Fejer kernels, and Cesaro summation in `Analysis/Fourier/AddCircle.lean` and broadly across Mathlib, finding no match.

## Statement 2: Theorem 1.2
**Status**: included
**Explanation**: This theorem states that $\{\mathfrak{e}_m : m \in \mathbb{Z}\}$ is an orthonormal basis in $L^2([0,1); \mathbb{C})$, and the Fourier series converges in $L^2$, with Parseval's identity holding. Mathlib formalizes all of this: `orthonormal_fourier` proves orthonormality, `fourierBasis` constructs the Hilbert basis, `hasSum_fourier_series_L2` proves $L^2$ convergence of the Fourier series, and `hasSum_sq_fourierCoeff` proves Parseval's identity.
**Mathlib references**: `Mathlib/Analysis/Fourier/AddCircle.lean` (`orthonormal_fourier`, `fourierBasis`, `hasSum_fourier_series_L2`, `hasSum_sq_fourierCoeff`).

## Statement 3: Corollary 1.3
**Status**: included
**Explanation**: This states that if $\varphi$ is continuous periodic and the Fourier coefficients are absolutely summable, then the Fourier series converges uniformly to $\varphi$. Mathlib has `hasSum_fourier_series_of_summable` which proves exactly this: if the sequence of Fourier coefficients of a continuous map $f : \text{AddCircle } T \to \mathbb{C}$ is summable, then the Fourier series converges to $f$ in the uniform-convergence topology.
**Mathlib references**: `Mathlib/Analysis/Fourier/AddCircle.lean` (`hasSum_fourier_series_of_summable`, `has_pointwise_sum_fourier_series_of_summable`).

## Statement 4: Lemma 1.4
**Status**: included
**Explanation**: This lemma relates the Fourier coefficients of a function to those of its derivative via integration by parts: $(\varphi, \mathfrak{e}_m) = (i/(2\pi m))^\ell (\varphi^{(\ell)}, \mathfrak{e}_m)$ for periodic smooth functions. Mathlib has `fourierCoeffOn_of_hasDerivAt` which expresses the Fourier coefficients of $f$ in terms of those of $f'$ via integration by parts, which is essentially the $\ell = 1$ case. The general case follows by iteration.
**Mathlib references**: `Mathlib/Analysis/Fourier/AddCircle.lean` (`fourierCoeffOn_of_hasDerivAt`, `fourierCoeffOn_of_hasDeriv_right`).

## Statement 5: Theorem 3.1
**Status**: non-included
**Explanation**: This theorem defines Bernoulli polynomials via a specific inductive construction involving coefficients $b_\ell$ and characterizes them as the unique polynomials satisfying $B_0 = 1$, $B'_{\ell+1} = -B_\ell$, and $B_\ell(1) = B_\ell(0)$ for $\ell \ge 2$. Mathlib has Bernoulli polynomials in `Mathlib/NumberTheory/BernoulliPolynomials.lean` with the derivative relation `derivative_bernoulli_add_one : derivative (bernoulli (k + 1)) = (k + 1) * bernoulli k` and the endpoint equality `bernoulliFun_endpoints_eq_of_ne_one` in `Mathlib/NumberTheory/ZetaValues.lean`. However, the sign convention differs (the textbook uses $B'_{\ell+1} = -B_\ell$ while Mathlib uses $B'_{k+1} = (k+1) B_k$, reflecting different sign conventions for Bernoulli numbers). The specific inductive construction and uniqueness characterization in the form stated here are not present.

## Statement 6: Theorem 3.2
**Status**: included
**Explanation**: This theorem gives the Fourier expansion of Bernoulli polynomials and the formula $\zeta(2\ell) = (-1)^{\ell+1} 2^{2\ell-1} \pi^{2\ell} b_{2\ell}$ for values of the Riemann zeta function at even integers. Mathlib has `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` giving the Fourier expansion of Bernoulli functions, `fourierCoeff_bernoulli_eq` giving the Fourier coefficients, and `hasSum_zeta_nat` providing the formula $\zeta(2k) = (-1)^{k+1} 2^{2k-1} \pi^{2k} B_{2k}/(2k)!$, along with the special cases `hasSum_zeta_two` and `hasSum_zeta_four`.
**Mathlib references**: `Mathlib/NumberTheory/ZetaValues.lean` (`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`, `fourierCoeff_bernoulli_eq`, `hasSum_zeta_nat`, `hasSum_zeta_two`, `hasSum_zeta_four`), `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean` (`riemannZeta_two_mul_nat`).

## Statement 7: Theorem 3.3
**Status**: non-included
**Explanation**: This is the Euler-Maclaurin summation formula, expressing the difference between an integral and a Riemann sum in terms of Bernoulli polynomials and a remainder. Searched for "Euler Maclaurin", "euler_maclaurin", "EulerMaclaurin" across all of Mathlib and found no results. This formula is not formalized in Mathlib v4.27.0.

## Statement 8: Theorem 5.1
**Status**: non-included
**Explanation**: This provides a quantitative rate of convergence for the Fejer kernel convolution $F_n * \varphi(x)$ to $\varphi(x)$ for Holder-continuous functions, with explicit constants. Searched for Fejer kernels, Cesaro summation, and Holder convergence rates in Fourier context across Mathlib. No formalization was found for the Fejer kernel or its convergence properties.

## Statement 9: Theorem 5.2
**Status**: non-included
**Explanation**: This states that $F_n * \varphi(x) \to \varphi(x)$ a.e. for $L^1$ functions (a.e. convergence of Fejer means). Searched for Fejer, Cesaro, and a.e. convergence of Fourier means across Mathlib. While Mathlib has the Lebesgue differentiation theorem in `MeasureTheory/Covering/Differentiation.lean`, the specific result about Fejer kernel convergence is not present.

## Statement 10: Lemma 7.1
**Status**: included
**Explanation**: This lemma states that for $f \in C^1 \cap L^1$ with $f' \in L^1$, the Fourier transform of $f'$ equals $-i\xi \hat{f}(\xi)$. Mathlib has `Real.fourier_deriv` which states that the Fourier transform of the derivative of $f$ is given by multiplication by $2\pi I x$ (with appropriate conventions). The sign/constant difference is just a matter of Fourier transform normalization convention.
**Mathlib references**: `Mathlib/Analysis/Fourier/FourierTransformDeriv.lean` (`Real.fourier_deriv`, `Real.fourier_fderiv`).

## Statement 11: Theorem 7.2
**Status**: included
**Explanation**: This is the Poisson summation formula $\sum_{n \in \mathbb{Z}} f(n) = \sum_{n \in \mathbb{Z}} \hat{f}(2\pi n)$. Mathlib has `Real.tsum_eq_tsum_fourier` which proves Poisson summation in the form $\sum_{n \in \mathbb{Z}} f(x + n) = \sum_{n \in \mathbb{Z}} \mathcal{F} f(n) \cdot \text{fourier}_n(x)$, evaluated at $x = 0$. There is also `SchwartzMap.tsum_eq_tsum_fourier` for Schwartz functions and `Real.tsum_eq_tsum_fourier_of_rpow_decay` under decay conditions similar to those in the textbook.
**Mathlib references**: `Mathlib/Analysis/Fourier/PoissonSummation.lean` (`Real.tsum_eq_tsum_fourier`, `SchwartzMap.tsum_eq_tsum_fourier`, `Real.tsum_eq_tsum_fourier_of_rpow_decay`).

## Statement 12: Theorem 10.1
**Status**: non-included
**Explanation**: This theorem states that the Hermite functions $H_m$ satisfy $\|H_m\|_{L^2(\gamma)} = (m!)^{1/2}$ and form an orthogonal basis in $L^2(\gamma; \mathbb{C})$ (with respect to the Gaussian measure). Mathlib has Hermite polynomials in `RingTheory/Polynomial/Hermite/Basic.lean` with algebraic properties and the relation to Gaussians in `RingTheory/Polynomial/Hermite/Gaussian.lean`, but the $L^2$ orthogonality with respect to the Gaussian measure and the orthogonal basis property are not formalized.

## Statement 13: Theorem 11.1
**Status**: non-included
**Explanation**: This states that the Hermite functions $h_m$ are eigenfunctions of the Fourier transform: $\hat{h}_m = (2\pi)^{1/2} i^m h_m$. Mathlib does not have this result. The Hermite polynomials are defined algebraically, and the Fourier transform eigenfunction property has not been formalized. Searched for Hermite-Fourier eigenfunction relationships across Mathlib without finding a match.

## Statement 14: Corollary 11.2
**Status**: non-included
**Explanation**: This gives bounds on the $L^1$ norm, uniform norm, and another uniform bound for normalized Hermite functions $\tilde{h}_m$. These analytic estimates on Hermite functions are not in Mathlib. The Hermite polynomial formalization is purely algebraic, not analytic.

## Statement 15: Theorem 11.3
**Status**: non-included
**Explanation**: This theorem gives the Hermite function expansion of the heat kernel $q(t,x,y)$ and relates it to Fourier analysis. This involves both the heat kernel on $\mathbb{R}$ and the Hermite function expansion, neither of which is formalized in the required form in Mathlib. Searched for Ornstein-Uhlenbeck, Mehler kernel, and heat kernel Hermite expansion without results.

## Statement 16: Lemma 12.1
**Status**: non-included
**Explanation**: This is a technical identity involving the Fourier transform, Hermite functions, and Gaussian factors, relating a weighted integral to a Hermite function series. This very specific identity is not in Mathlib. The necessary Hermite function analysis infrastructure is absent.

## Statement 17: Theorem 12.2
**Status**: non-included
**Explanation**: This states that for $f \in L^1 \cap L^2$, the Fourier transform can be expressed as $\hat{f} = (2\pi)^{1/2} \sum i^m (f, \tilde{h}_m) \tilde{h}_m$ a.e. This is the Hermite function expansion of the Fourier transform. While Mathlib has the Fourier transform on $L^2$ as a linear isometry equivalence (`fourierTransformLi` in `Analysis/Fourier/LpSpace.lean`), the specific Hermite function expansion is not present.

## Statement 18: Lemma 13.1
**Status**: non-included
**Explanation**: This gives the bound $\|x\varphi\|_{\mathscr{S}^{(m)}} \vee \|\partial\varphi\|_{\mathscr{S}^{(m)}} \le 3^m \|\varphi\|_{\mathscr{S}^{(m+1)}}$ for Schwartz seminorms. While Mathlib defines Schwartz space seminorms in `Analysis/Distribution/SchwartzSpace/Basic.lean`, this specific seminorm comparison inequality involving the textbook's $\mathscr{S}^{(m)}$ seminorms (which are Hermite-function based) is not formalized. Mathlib's Schwartz seminorms use $\|x\|^k \cdot \|\text{iteratedFDeriv } n\, f(x)\|$ rather than the Hermite-function-based norms used here.

## Statement 19: Theorem 13.2
**Status**: non-included
**Explanation**: This theorem gives several properties: density of $\mathscr{S}$ in $\mathscr{S}^{(m)}$, comparison between different Schwartz seminorm families, characterization of Schwartz convergence, and the convergence of Hermite function expansions in $\mathscr{S}$. While Mathlib has the Schwartz space as a topological vector space with seminorms, the specific Hermite-function-based seminorms $\mathscr{S}^{(m)}$ and their properties as stated here are not formalized.

## Statement 20: Corollary 13.3
**Status**: non-included
**Explanation**: This defines the map $S: L^2 \to \ell^2$ by Hermite function coefficients and proves it restricts to isometric isomorphisms $\mathscr{S}^{(m)} \to \mathfrak{s}^{(m)}$. Mathlib has the general Hilbert basis machinery in `Analysis/InnerProductSpace/l2Space.lean`, but the specific Hermite-function-based isomorphism between Schwartz space and a sequence space is not formalized.

## Statement 21: Lemma 13.4
**Status**: non-included
**Explanation**: This is a characterization of relative compactness in weighted $\ell^2$ spaces: a subset is relatively compact iff it is bounded and "tight" (the tail sums converge to zero uniformly). Mathlib has `Analysis/InnerProductSpace/l2Space.lean` for the $\ell^2$ space structure, but this specific compactness criterion for weighted $\ell^2$ spaces is not formalized.

## Statement 22: Theorem 13.5
**Status**: non-included
**Explanation**: This states that $\mathscr{S}^{(m)}$ is a separable Hilbert space, $\mathscr{S}$ is a complete separable metric space, and characterizes relative compactness in $\mathscr{S}$ by boundedness. While Mathlib defines the Schwartz space topology via seminorms and proves it is a locally convex space, the completeness/separability and the specific compactness characterization are not explicitly formalized. Searched for "Schwartz complete", "Schwartz separable" across Mathlib without results.

## Statement 23: Theorem 13.6
**Status**: included
**Explanation**: This states that the Fourier transform is an isomorphism from $\mathscr{S}(\mathbb{R};\mathbb{C})$ onto itself, with the seminorm relation $\|\hat{\varphi}\|_{\mathscr{S}^{(m)}} = (2\pi)^{1/2} \|\varphi\|_{\mathscr{S}^{(m)}}$. Mathlib has `fourierTransformCLE` (alias for `FourierTransform.fourierCLE`) which gives the Fourier transform as a continuous linear equivalence on the Schwartz space, and `fourierTransformCLM` as a continuous linear map. The Fourier inversion theorem for Schwartz functions is also formalized via `instFourierPair`. Plancherel's theorem on Schwartz functions is in `integral_inner_fourier_fourier` and `norm_fourier_toL2_eq`.
**Mathlib references**: `Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean` (`fourierTransformCLM`, `fourierTransformCLE`, `instFourierPair`, `integral_inner_fourier_fourier`, `norm_fourier_toL2_eq`).

## Statement 24: Lemma 14.1
**Status**: non-included
**Explanation**: This states that every continuous linear functional on $\mathscr{S}$ is bounded by some Schwartz seminorm $\|\cdot\|_{\mathscr{S}^{(m)}}$. While Mathlib defines tempered distributions as continuous linear maps on Schwartz space (`TemperedDistribution` in `Analysis/Distribution/TemperedDistribution.lean`), the specific characterization that every such functional is controlled by a single Schwartz seminorm level is not explicitly formalized. The Schwartz space uses a family of seminorms, and continuity with respect to the Schwartz topology inherently involves such bounds, but this explicit lemma is not stated.

## Statement 25: Theorem 14.2
**Status**: non-included
**Explanation**: This defines the negative Sobolev-type spaces $\mathscr{S}^{(-m)}$ as duals of $\mathscr{S}^{(m)}$, with norm characterization via the harmonic oscillator operator $\mathcal{H}$. Mathlib has tempered distributions but not these specific Sobolev-type scales of spaces $\mathscr{S}^{(-m)}$ based on the harmonic oscillator. Searched for negative Schwartz spaces, Sobolev-Schwartz, and harmonic oscillator operator across Mathlib without results.

## Statement 26: Theorem 14.3
**Status**: non-included
**Explanation**: This characterizes non-negative tempered distributions as measures with polynomial growth, and conversely embeds such measures into tempered distributions. While Mathlib has `MeasureTheory.Measure.toTemperedDistribution` for temperate growth measures and `Function.HasTemperateGrowth.toTemperedDistribution` for temperate growth functions, the full characterization of non-negative tempered distributions as measures (the converse direction and the specific growth conditions) is not formalized.

## Statement 27: Theorem 14.4
**Status**: non-included
**Explanation**: This extends the measure-to-distribution embedding to $L^p$ functions with respect to measures of polynomial growth, giving explicit bounds on the Schwartz space norms. While Mathlib has `MeasureTheory.Lp.toTemperedDistribution` for embedding $L^p$ functions as tempered distributions, the specific norm bounds involving the textbook's $\mathscr{S}^{(-m_p-3)}$ norms are not present.

## Statement 28: Theorem 14.5
**Status**: non-included
**Explanation**: This characterizes distributions in $\mathscr{S}^{(-n+1)}$ supported at $\{0\}$ as finite linear combinations of derivatives of the Dirac delta. This is a standard result in distribution theory, but Mathlib does not have the notion of the support of a tempered distribution or this characterization. Searched for distribution support, point support, and Dirac delta distribution characterization without finding a match.

## Statement 29: Lemma 14.6
**Status**: non-included
**Explanation**: This is a representation lemma for distributions satisfying certain conditions (related to Levy-Khintchine theory), expressing them as integrals against a Levy measure. This is part of the Levy-Khintchine representation theory, which is not formalized in Mathlib. Searched for Levy-Khintchine, infinitely divisible, and Levy measure across Mathlib without results.

## Statement 30: Theorem 14.7
**Status**: non-included
**Explanation**: This is the Levy-Khintchine representation theorem, decomposing a distribution satisfying certain conditions into a Gaussian part, a drift, and a jump measure integral. This is a fundamental result in probability theory / Levy process theory, and it is not formalized in Mathlib v4.27.0. Searched for Levy-Khintchine, infinitely divisible distributions across Mathlib without finding matches.

## Statement 31: Theorem 15.1
**Status**: non-included
**Explanation**: This provides the extension of a continuous operator $A$ on $\mathscr{S}$ (with formal adjoint $A^*$) to a continuous operator on $\mathscr{S}^*$ (tempered distributions) via $\langle \varphi, Au \rangle = \langle A^*\varphi, u \rangle$. While Mathlib defines operations on tempered distributions (derivative via `instLineDeriv`, multiplication via `smulLeftCLM`, Fourier transform via `fourierTransformCLM`), the general abstract extension theorem as stated is not formalized as a standalone result.

## Statement 32: Lemma 15.2
**Status**: non-included
**Explanation**: This gives bounds on the Schwartz seminorm of a product $\varphi f$ where $f$ is a smooth function with polynomially bounded derivatives. Mathlib has `SchwartzMap.smulLeftCLM` for multiplication of Schwartz functions by smooth functions of temperate growth, which implicitly involves seminorm bounds, but the explicit bound in the form stated here (with specific constants $C_m$, $F_m$, and the shift from $\mathscr{S}^{(m)}$ to $\mathscr{S}^{(m+k_m)}$) is not formalized.

## Statement 33: Theorem 15.3
**Status**: non-included
**Explanation**: This states that the convolution of a Schwartz function $\psi$ with a tempered distribution $u$ is a continuous function with polynomial growth, and satisfies $\widehat{\psi * u} = \hat{\psi}\hat{u}$. Mathlib has `SchwartzMap.convolution` defined in `Analysis/Fourier/Convolution.lean` and the Fourier convolution theorem for Schwartz functions (`SchwartzMap.fourier_convolution`), but the convolution of a Schwartz function with a tempered distribution (as opposed to two Schwartz functions or two $L^1$ functions) is not formalized.

## Statement 34: Lemma 17.1
**Status**: non-included
**Explanation**: This states that the sets $S(\mu, r; \varphi_1, \ldots, \varphi_n)$ with $\varphi_i \in C_c^\infty(\mathbb{R}^N; \mathbb{R})$ form a neighborhood basis for the weak topology on probability measures. While Mathlib has the weak topology on probability measures (defined via bounded continuous functions in `MeasureTheory/Measure/ProbabilityMeasure.lean`), the specific neighborhood basis characterization using test functions from $C_c^\infty$ is not formalized.

## Statement 35: Theorem 17.2
**Status**: included
**Explanation**: This states that the weak topology on $\mathbf{M}_1(\mathbb{R}^N)$ is a separable, metrizable topology. Mathlib has `instMetrizableSpaceProbabilityMeasure` which proves that the topology of convergence in distribution on a separable Borel space is metrizable, using the Levy-Prokhorov metric. The result is established through the Levy-Prokhorov metric homeomorphism.
**Mathlib references**: `Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean` (`instMetrizableSpaceProbabilityMeasure`, `LevyProkhorov.probabilityMeasureHomeomorph`).

## Statement 36: Theorem 17.3
**Status**: included
**Explanation**: This is the Portmanteau theorem, giving equivalent characterizations of weak convergence of probability measures: convergence against bounded continuous functions, limsup condition for closed sets, liminf condition for open sets, convergence for sets with null boundary, and conditions involving upper/lower semicontinuous functions. Mathlib has the Portmanteau theorem formalized with multiple implications: `limsup_measure_closed_le_of_tendsto` (T implies C), `limsup_measure_closed_le_iff_liminf_measure_open_ge` (C iff O), `tendsto_measure_of_null_frontier` (O implies B), `tendsto_of_forall_isOpen_le_liminf` (O implies T), and `tendsto_of_limsup_measure_closed_le` (C implies T). The characterizations via upper/lower semicontinuous functions (items v and vi) are not explicitly present, but the main equivalences are.
**Mathlib references**: `Mathlib/MeasureTheory/Measure/Portmanteau.lean` (`FiniteMeasure.limsup_measure_closed_le_of_tendsto`, `limsup_measure_closed_le_iff_liminf_measure_open_ge`, `tendsto_measure_of_null_frontier`, `tendsto_of_forall_isOpen_le_liminf`, `tendsto_of_limsup_measure_closed_le`, `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`).

## Statement 37: Theorem 17.4
**Status**: non-included
**Explanation**: This is a dominated convergence result for weakly convergent measures: if $\mu_n \xrightarrow{w} \mu$ and $\psi$ is a continuous non-negative dominating function with $\langle \psi, \mu_n \rangle \to \langle \psi, \mu \rangle$, then $\langle \varphi_n, \mu_n \rangle \to \langle \varphi, \mu \rangle$ for dominated converging integrands. The first part (lower semicontinuity of the integral of a non-negative continuous function) follows from the Portmanteau theorem, but the full dominated convergence statement for weakly converging measures is not explicitly formalized in Mathlib. Searched for dominated convergence in weak convergence context without finding a direct match.

## Statement 38: Theorem 17.5
**Status**: included
**Explanation**: This is Prokhorov's theorem: a subset of $\mathbf{M}_1(\mathbb{R}^N)$ is relatively compact in the weak topology if and only if it is tight. Mathlib has `isCompact_closure_of_isTightMeasureSet` which proves that the closure of a tight set of probability measures is compact, and the equivalence between tightness and relative compactness.
**Mathlib references**: `Mathlib/MeasureTheory/Measure/Prokhorov.lean` (`isCompact_closure_of_isTightMeasureSet`, `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`).

## Statement 39: Theorem 18.1
**Status**: non-included
**Explanation**: This states that $\mu_n \xrightarrow{w} \mu$ if and only if $\hat{\mu}_n(\xi) \to \hat{\mu}(\xi)$ for each $\xi$, and that convergence is uniform on compacta. While Mathlib has the characteristic function of a finite measure (`charFun` in `MeasureTheory/Measure/CharacteristicFunction.lean`) and the uniqueness theorem `Measure.ext_of_charFun`, the equivalence between weak convergence and pointwise convergence of characteristic functions (Levy's continuity theorem in its basic form) is not formalized. Searched for charFun convergence, charFun tendsto, and Levy continuity without results.

## Statement 40: Theorem 18.2
**Status**: non-included
**Explanation**: This is Levy's continuity theorem in its full form, characterizing tightness via uniform equicontinuity of characteristic functions near the origin and providing the criterion for weak convergence. This is not formalized in Mathlib v4.27.0. The characteristic function infrastructure exists but the convergence theorem does not.

## Statement 41: Theorem 18.3
**Status**: non-included
**Explanation**: This is Bochner's theorem: a function $f: \mathbb{R}^N \to \mathbb{C}$ is a characteristic function if and only if $f$ is continuous, $f(0) = 1$, and $f$ is non-negative definite. This fundamental result connecting positive definite functions and probability measures is not formalized in Mathlib. Searched for positive definite characteristic function, Bochner theorem across Mathlib without results.

## Statement 42: Theorem 19.1
**Status**: non-included
**Explanation**: This states that under non-degeneracy conditions for the parameters $(b, A, M)$ of an infinitely divisible distribution, the measure $\mu_{(b,A,M)}$ assigns positive probability to all non-empty open sets. This is part of the theory of infinitely divisible distributions / Levy processes, which is not formalized in Mathlib.

## Statement 43: Theorem 19.2
**Status**: non-included
**Explanation**: This characterizes when $\mu_{(b,A,M)}$ is supported on $[0,\infty)$ (i.e., is a subordinator) in terms of conditions on $A$, $M$, and $b$. This is part of the Levy-Khintchine / infinitely divisible distribution theory, not formalized in Mathlib.

## Statement 44: Theorem 22.1
**Status**: non-included
**Explanation**: This is the Riesz-Thorin interpolation theorem, stating that a linear operator bounded on $L^{p_0}$ and $L^{p_1}$ is also bounded on intermediate $L^{p_\theta}$ spaces with interpolated norm bounds. Searched for "Riesz Thorin", "riesz_thorin", and "interpolation theorem" across all of Mathlib. This fundamental result in functional analysis / harmonic analysis is not formalized in Mathlib v4.27.0.

## Statement 45: Lemma 22.2
**Status**: included
**Explanation**: This is the Hadamard three-lines lemma (also known as the three-lines theorem): if $F$ is bounded and continuous on the closed strip $\{z : \text{Re } z \in [0,1]\}$, analytic on its interior, and bounded by $m_0$ on $\text{Re } z = 0$ and $m_1$ on $\text{Re } z = 1$, then $|F(z)| \le m_0^{1-x} m_1^x$ for $z = x + iy$ in the strip. Mathlib has `norm_le_interp_of_mem_verticalClosedStrip'` which is precisely this result, proved using Phragmen-Lindelof methods.
**Mathlib references**: `Mathlib/Analysis/Complex/Hadamard.lean` (`norm_le_interp_of_mem_verticalClosedStrip'`, `norm_le_interp_of_mem_verticalClosedStrip_0_1'`).
