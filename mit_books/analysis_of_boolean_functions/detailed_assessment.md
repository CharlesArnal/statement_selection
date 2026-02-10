# Detailed Assessment: Analysis of Boolean Functions (18.218, Spring 2021)

## Statement 1: Claim 2.1 (Orthonormality of characters)
**Status**: non-included
**Explanation**: This states that the collection of characters $\{\chi_S\}_{S\subseteq[n]}$ on the Boolean hypercube $\{-1,1\}^n$ forms an orthonormal basis. While mathlib has general orthonormality theory (`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`) and character theory for finite abelian groups (`Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean`), the specific discrete Fourier analysis setup on $\{-1,1\}^n$ with characters $\chi_S(x) = \prod_{i \in S} x_i$ is not formalized. The finite abelian group Fourier analysis in mathlib works over $\mathbb{Z}/n\mathbb{Z}$ (ZMod) rather than the Boolean hypercube $(\mathbb{Z}/2\mathbb{Z})^n$ with this particular character basis.
**Mathlib references**: `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` (related but different setting)

## Statement 2: Claim 2.2 (Plancherel/Parseval)
**Status**: non-included
**Explanation**: Plancherel's and Parseval's equalities for Boolean functions. Mathlib has Plancherel/Parseval for the continuous Fourier transform on $L^2$ spaces (`Mathlib/Analysis/Fourier/LpSpace.lean`) with `norm_fourier_eq` and `inner_fourier_eq`, but not for the discrete Fourier analysis on the Boolean hypercube $\{-1,1\}^n$.
**Mathlib references**: `Mathlib/Analysis/Fourier/LpSpace.lean` (continuous analog only)

## Statement 3: Claim 2.3 (Variance formula)
**Status**: non-included
**Explanation**: The variance of a Boolean function expressed as $\operatorname{var}(f) = \sum_{S \neq \emptyset} \widehat{f}(S)^2$. This is specific to discrete Fourier analysis on the Boolean hypercube and is not in mathlib.
**Mathlib references**: None

## Statement 4: Claim 1.1 (Convolution in Fourier domain)
**Status**: non-included
**Explanation**: The convolution theorem $\widehat{f * g}(S) = \widehat{f}(S)\widehat{g}(S)$ for Boolean functions. While mathlib has convolution (`Mathlib/Analysis/Convolution.lean`), this is for the continuous setting. The discrete Boolean hypercube convolution and its Fourier-domain identity are not formalized.
**Mathlib references**: `Mathlib/Analysis/Convolution.lean` (continuous analog only)

## Statement 5: Theorem 1.2 (BLR Linearity Test)
**Status**: non-included
**Explanation**: The BLR linearity test analysis is a foundational result in property testing and theoretical computer science. It is not formalized in mathlib, which does not cover property testing or this style of Boolean function analysis.
**Mathlib references**: None

## Statement 6: Remark 1.3 (Roth's theorem analogy)
**Status**: non-included
**Explanation**: This is an informal remark drawing an analogy to Roth's theorem, not a formal mathematical statement.
**Mathlib references**: None

## Statement 7: Definition 2.1 (Restrictions)
**Status**: non-included
**Explanation**: The notion of restricting a Boolean function by fixing some coordinates is a fundamental concept in Boolean function analysis not present in mathlib.
**Mathlib references**: None

## Statement 8: Definition 2.2 (Random Restriction)
**Status**: non-included
**Explanation**: Random restrictions of Boolean functions are not formalized in mathlib. This is a specialized concept from Boolean function analysis.
**Mathlib references**: None

## Statement 9: Claim 2.3 (Fourier coefficients of restriction)
**Status**: non-included
**Explanation**: The formula for Fourier coefficients of a restricted function in terms of the original function's coefficients is specific to discrete Boolean Fourier analysis and is not in mathlib.
**Mathlib references**: None

## Statement 10: Claim 2.4 (Expected squared Fourier coefficient of restriction)
**Status**: non-included
**Explanation**: This corollary about expected squared Fourier coefficients under random restrictions is part of the Boolean function analysis toolkit not covered in mathlib.
**Mathlib references**: None

## Statement 11: Definition 2.5 (p-random restriction)
**Status**: non-included
**Explanation**: The concept of p-random restrictions, where the set of live variables is also randomly chosen, is not in mathlib.
**Mathlib references**: None

## Statement 12: Definition 2.6 (Fourier weight)
**Status**: non-included
**Explanation**: The level-d Fourier weight $W^{=d}[f]$ is a standard concept in Boolean function analysis not present in mathlib.
**Mathlib references**: None

## Statement 13: Claim 2.7 (Expected Fourier weight under p-random restriction)
**Status**: non-included
**Explanation**: This formula relating expected Fourier weight after a p-random restriction to binomial probabilities is not in mathlib.
**Mathlib references**: None

## Statement 14: Corollary 2.8 (Fourier weight reduction under restriction)
**Status**: non-included
**Explanation**: A corollary about how random restrictions reduce Fourier weight, not present in mathlib.
**Mathlib references**: None

## Statement 15: Definition 2.9 (Weight around level d)
**Status**: non-included
**Explanation**: The definition of Fourier weight around a given level is specific to Boolean function analysis and not in mathlib.
**Mathlib references**: None

## Statement 16: Corollary 2.10 (Preservation of Fourier weight under restriction)
**Status**: non-included
**Explanation**: This corollary about preservation of Fourier weight near a given level under random restrictions is not in mathlib.
**Mathlib references**: None

## Statement 17: Fact 1.1 (Chernoff-Hoeffding bound)
**Status**: non-included
**Explanation**: While mathlib has some concentration inequality infrastructure in `Mathlib/Probability/Moments/SubGaussian.lean` and moment bounds in `Mathlib/Probability/Moments/Basic.lean`, the specific Chernoff-Hoeffding bound stated here (for bounded independent random variables) does not appear to be formalized in mathlib in this exact form. Mathlib's treatment is partial; there is sub-Gaussian theory but not the classical Hoeffding inequality statement.
**Mathlib references**: `Mathlib/Probability/Moments/SubGaussian.lean` (related infrastructure)

## Statement 18: Claim 1.2 (PAC estimation of Fourier coefficients)
**Status**: non-included
**Explanation**: This is an algorithmic statement about PAC learning / estimating Fourier coefficients with sample complexity bounds. Mathlib does not cover learning theory or algorithmic guarantees.
**Mathlib references**: None

## Statement 19: Claim 2.1 (Membership query estimation)
**Status**: non-included
**Explanation**: This is an algorithmic claim about estimating sums of squared Fourier coefficients via membership queries. Learning theory and query complexity are not covered in mathlib.
**Mathlib references**: None

## Statement 20: Theorem 3.1 (Learning sparse functions)
**Status**: non-included
**Explanation**: This is the Goldreich-Levin algorithm for learning Fourier-sparse Boolean functions. It is a computational/algorithmic result and is outside the scope of mathlib.
**Mathlib references**: None

## Statement 21: Remark 3.2 (Goldreich-Levin)
**Status**: non-included
**Explanation**: This is an informal remark about the origin of the algorithm, not a formal mathematical statement.
**Mathlib references**: None

## Statement 22: Definition 1.1 (Influence)
**Status**: non-included
**Explanation**: The influence of a coordinate on a Boolean function is a fundamental concept in Boolean function analysis. It is not formalized in mathlib, which does not have a dedicated Boolean function analysis library.
**Mathlib references**: None

## Statement 23: Definition 1.2 (Total Influence)
**Status**: non-included
**Explanation**: The total influence (sum of individual influences) is not formalized in mathlib.
**Mathlib references**: None

## Statement 24: Definition 2.1 (Discrete derivatives)
**Status**: non-included
**Explanation**: Discrete derivatives of Boolean functions are not defined in mathlib. This is a concept specific to analysis on the Boolean hypercube.
**Mathlib references**: None

## Statement 25: Definition 2.2 (L^2 influence)
**Status**: non-included
**Explanation**: The $L^2$ generalization of influence for real-valued functions on the Boolean hypercube is not in mathlib.
**Mathlib references**: None

## Statement 26: Claim 3.1 (Total influence = average sensitivity)
**Status**: non-included
**Explanation**: The combinatorial interpretation of total influence as average sensitivity is not in mathlib.
**Mathlib references**: None

## Statement 27: Lemma 4.1 (Russo-Margulis)
**Status**: non-included
**Explanation**: The Russo-Margulis lemma relating the derivative of the p-biased measure of a monotone function to its total influence is a key result in Boolean function analysis and percolation theory. It is not formalized in mathlib. No search hits for "Russo" or "Margulis" in the relevant context or "sharp threshold" were found.
**Mathlib references**: None

## Statement 28: Remark 4.2
**Status**: non-included
**Explanation**: Informal remark, not a formal mathematical statement.
**Mathlib references**: None

## Statement 29: Claim 5.1 (Fourier formula for derivative)
**Status**: non-included
**Explanation**: The Fourier expansion of the discrete derivative is specific to Boolean Fourier analysis and is not in mathlib.
**Mathlib references**: None

## Statement 30: Corollary 5.2 (Influence Fourier formula)
**Status**: non-included
**Explanation**: The formula $I_i[f] = \sum_{S \ni i} \widehat{f}(S)^2$ expressing influence via Fourier coefficients is not in mathlib.
**Mathlib references**: None

## Statement 31: Corollary 5.3 (Total influence Fourier formula)
**Status**: non-included
**Explanation**: The formula $I[f] = \sum_{S} |S| \widehat{f}(S)^2$ is not in mathlib.
**Mathlib references**: None

## Statement 32: Corollary 5.4 (Poincare inequality)
**Status**: non-included
**Explanation**: The Poincare inequality for Boolean functions ($I[f] \geq \operatorname{var}(f)$) is not in mathlib. While mathlib has Poincare-type results in continuous settings (e.g., in ergodic theory), the discrete Boolean hypercube version is not present.
**Mathlib references**: None (the hit in `Mathlib/Dynamics/Ergodic/Conservative.lean` is unrelated)

## Statement 33: Theorem 5.5 (KKL theorem)
**Status**: non-included
**Explanation**: The Kahn-Kalai-Linial theorem is a landmark result in Boolean function analysis. It is not formalized in mathlib.
**Mathlib references**: None

## Statement 34: Definition 0.1 (L^p norm)
**Status**: included
**Explanation**: The $L^p$ norm is a standard concept that is extensively formalized in mathlib through the general measure-theoretic $L^p$ space infrastructure, applicable to any measure space including the uniform measure on $\{-1,1\}^n$.
**Mathlib references**: `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`, `Mathlib/MeasureTheory/Function/LpSeminorm/`

## Statement 35: Lemma 1.1 (Degree 1 hypercontractivity)
**Status**: non-included
**Explanation**: The hypercontractive inequality for degree-1 Boolean functions is not in mathlib. The entire hypercontractivity theory for the Boolean hypercube is absent.
**Mathlib references**: None

## Statement 36: Theorem 2.1 (Hypercontractive inequality)
**Status**: non-included
**Explanation**: The Bonami-Beckner hypercontractive inequality for Boolean functions is not formalized in mathlib. No results matching "hypercontractive" or "Bonami" were found.
**Mathlib references**: None

## Statement 37: Definition 2.2 (Noise operator)
**Status**: non-included
**Explanation**: The noise operator $T_\rho$ on the Boolean hypercube is not defined in mathlib.
**Mathlib references**: None

## Statement 38: Theorem 2.3 (Hypercontractive inequality, noise operator formulation)
**Status**: non-included
**Explanation**: The noise-operator formulation of hypercontractivity is not in mathlib.
**Mathlib references**: None

## Statement 39: Claim 2.4 (Noise operator Fourier formula)
**Status**: non-included
**Explanation**: The action of the noise operator on Fourier coefficients is not in mathlib.
**Mathlib references**: None

## Statement 40: Definition 3.1 (Noisy hypercube)
**Status**: non-included
**Explanation**: The noisy hypercube graph is not defined in mathlib.
**Mathlib references**: None

## Statement 41: Definition 3.2 (Edge expansion)
**Status**: non-included
**Explanation**: Edge expansion of graphs is not formally defined in mathlib's graph theory library.
**Mathlib references**: None

## Statement 42: Definition 3.3 (Small set expander)
**Status**: non-included
**Explanation**: The notion of small set expansion is not defined in mathlib.
**Mathlib references**: None

## Statement 43: Claim 3.4 (Noisy hypercube is small-set expander)
**Status**: non-included
**Explanation**: This result about the noisy hypercube being a small-set expander is not in mathlib.
**Mathlib references**: None

## Statement 44: Remark 3.5
**Status**: non-included
**Explanation**: Informal remark extending Claim 3.4.
**Mathlib references**: None

## Statement 45: Theorem 3.6 (Concentration for low-degree functions)
**Status**: non-included
**Explanation**: This concentration inequality for low-degree Boolean functions (a consequence of hypercontractivity) is not in mathlib.
**Mathlib references**: None

## Statement 46: Remark 3.7
**Status**: non-included
**Explanation**: Informal remark about tightness.
**Mathlib references**: None

## Statement 47: Theorem 3.8 (Anti-concentration for low-degree functions)
**Status**: non-included
**Explanation**: This anti-concentration result for low-degree Boolean functions is not in mathlib.
**Mathlib references**: None

## Statement 48: Lemma 3.9 (1-norm trick)
**Status**: non-included
**Explanation**: The 1-norm trick ($\|f\|_2 \leq 3^d \|f\|_1$ for degree-d functions) is not in mathlib.
**Mathlib references**: None

## Statement 49: Theorem 1.1 (FKN theorem)
**Status**: non-included
**Explanation**: The Friedgut-Kalai-Naor theorem about stability of degree-1 Boolean functions is not in mathlib.
**Mathlib references**: None

## Statement 50: Remark 1.2
**Status**: non-included
**Explanation**: Informal remark about extensions to degree $d$.
**Mathlib references**: None

## Statement 51: Claim 2.1 (Degree of indicator of small set)
**Status**: non-included
**Explanation**: The lower bound on the degree of the indicator of a small set on the Boolean hypercube is not in mathlib.
**Mathlib references**: None

## Statement 52: Lemma 2.2 (Fourier spectrum of small sets)
**Status**: non-included
**Explanation**: This result about the Fourier spectrum of small sets is not in mathlib.
**Mathlib references**: None

## Statement 53: Remark 2.3
**Status**: non-included
**Explanation**: Informal remark about quantitative improvements.
**Mathlib references**: None

## Statement 54: Theorem 3.1 (KKL, influence-version)
**Status**: non-included
**Explanation**: This is a restatement of the KKL theorem focusing on the influence version. Not in mathlib.
**Mathlib references**: None

## Statement 55: Corollary 3.2 (KKL standard)
**Status**: non-included
**Explanation**: The standard formulation of the KKL theorem ($\max_i I_i[f] \geq \Omega(\frac{\log n}{n} \operatorname{var}(f))$) is not in mathlib.
**Mathlib references**: None

## Statement 56: Claim 4.1 (Tribes function)
**Status**: non-included
**Explanation**: The Tribes function construction showing tightness of KKL is not in mathlib.
**Mathlib references**: None

## Statement 57: Theorem 0.1 (KKL restated)
**Status**: non-included
**Explanation**: Another restatement of the KKL theorem. Not in mathlib.
**Mathlib references**: None

## Statement 58: Theorem 1.1 (Talagrand's KKL)
**Status**: non-included
**Explanation**: Talagrand's strengthening of the KKL theorem is not in mathlib.
**Mathlib references**: None

## Statement 59: Theorem 2.1 (Friedgut junta theorem)
**Status**: non-included
**Explanation**: Friedgut's junta theorem about approximation of low-influence Boolean functions by juntas is not in mathlib.
**Mathlib references**: None

## Statement 60: Theorem 3.1 (Edge isoperimetric inequality)
**Status**: non-included
**Explanation**: The edge isoperimetric inequality on the Boolean hypercube is not in mathlib.
**Mathlib references**: None

## Statement 61: Theorem 3.2 (Margulis)
**Status**: non-included
**Explanation**: Margulis's inequality relating vertex boundary and edge boundary is not in mathlib.
**Mathlib references**: None

## Statement 62: Theorem 3.3 (Talagrand)
**Status**: non-included
**Explanation**: Talagrand's inequality $\mathbb{E}[\sqrt{s_f(x)}] \geq \Omega(\operatorname{var}(f))$ is not in mathlib.
**Mathlib references**: None

## Statement 63: Theorem 3.4 (Talagrand, stronger)
**Status**: non-included
**Explanation**: The stronger version of Talagrand's inequality incorporating the unbalancedness of the function is not in mathlib.
**Mathlib references**: None

## Statement 64: Theorem 3.5 (Talagrand, combined)
**Status**: non-included
**Explanation**: Talagrand's combined isoperimetric inequality mixing vertex boundary and KKL-type bounds is not in mathlib.
**Mathlib references**: None

## Statement 65: Definition 1.1 (Noise Stability)
**Status**: non-included
**Explanation**: Noise stability of Boolean functions is not defined in mathlib.
**Mathlib references**: None

## Statement 66: Theorem 1.2 (Majority is stablest)
**Status**: non-included
**Explanation**: The "Majority is Stablest" theorem by Mossel, O'Donnell, and Oleszkiewicz is a deep result not formalized in mathlib.
**Mathlib references**: None

## Statement 67: Claim 1.3 (Fourier formula for stability)
**Status**: non-included
**Explanation**: The Fourier expression for noise stability is not in mathlib.
**Mathlib references**: None

## Statement 68: Theorem 1.4 (Sheppard's Formula)
**Status**: non-included
**Explanation**: Sheppard's formula for the noise stability of majority is not in mathlib.
**Mathlib references**: None

## Statement 69: Theorem 2.1 (Arrow's impossibility theorem)
**Status**: non-included
**Explanation**: Arrow's impossibility theorem from social choice theory is not formalized in mathlib. No results related to Arrow's theorem, social choice, or Condorcet were found.
**Mathlib references**: None

## Statement 70: Claim 2.2 (NAE_3 Fourier expansion)
**Status**: non-included
**Explanation**: The Fourier expansion of the NAE_3 function is not in mathlib.
**Mathlib references**: None

## Statement 71: Definition 2.3 (Negative correlation)
**Status**: non-included
**Explanation**: The distribution of negatively-correlated inputs is not defined in mathlib in this Boolean function context.
**Mathlib references**: None

## Statement 72: Theorem 2.4 (Robust Arrow's theorem)
**Status**: non-included
**Explanation**: The robust version of Arrow's theorem via Fourier analysis is not in mathlib.
**Mathlib references**: None

## Statement 73: Definition 3.1 (Noise Sensitivity)
**Status**: non-included
**Explanation**: Noise sensitivity of Boolean functions is not defined in mathlib.
**Mathlib references**: None

## Statement 74: Claim 3.2 (Fourier formula for noise sensitivity)
**Status**: non-included
**Explanation**: The Fourier expression for noise sensitivity is not in mathlib.
**Mathlib references**: None

## Statement 75: Theorem 4.1 (BKS level-k inequality)
**Status**: non-included
**Explanation**: The Benjamini-Kalai-Schramm level-k inequality is not in mathlib.
**Mathlib references**: None

## Statement 76: Corollary 4.2
**Status**: non-included
**Explanation**: This corollary of the BKS theorem is not in mathlib.
**Mathlib references**: None

## Statement 77: Corollary 4.3
**Status**: non-included
**Explanation**: This corollary relating noise sensitivity to the parameter $M(f)$ is not in mathlib.
**Mathlib references**: None

## Statement 78: Theorem 4.4 (BKS for monotone)
**Status**: non-included
**Explanation**: The two-sided BKS characterization for monotone functions is not in mathlib.
**Mathlib references**: None

## Statement 79: Theorem 4.5 (Weaker BKS)
**Status**: non-included
**Explanation**: The quantitatively weaker version of the BKS theorem is not in mathlib.
**Mathlib references**: None

## Statement 80: Lemma 5.1 (Level k inequality)
**Status**: non-included
**Explanation**: The level-k inequality for sparse Boolean functions is not in mathlib.
**Mathlib references**: None

## Statement 81: Remark 5.2
**Status**: non-included
**Explanation**: Informal remark.
**Mathlib references**: None

## Statement 82: Claim 6.1 (Decoupling partition)
**Status**: non-included
**Explanation**: The decoupling lemma for partitioning variables is not in mathlib.
**Mathlib references**: None

## Statement 83: Theorem 3.1 (Dinur-Friedgut)
**Status**: non-included
**Explanation**: The Dinur-Friedgut theorem about intersecting families being close to junta intersecting families is not in mathlib. While mathlib has the basic definition of intersecting families and some EKR-type results (`Mathlib/Combinatorics/SetFamily/Intersecting.lean`), this structural junta theorem is far beyond what is currently formalized.
**Mathlib references**: `Mathlib/Combinatorics/SetFamily/Intersecting.lean` (basic intersecting family definition only)

## Statement 84: Claim 3.2 (Upwards closure preserves intersecting)
**Status**: non-included
**Explanation**: While mathlib has the definition of intersecting families and some basic properties, this specific claim about upwards closures preserving the intersecting property is not explicitly formalized. Mathlib has `UpperSet` infrastructure in `Mathlib/Order/UpperLower/Basic.lean` but not this specific combination.
**Mathlib references**: `Mathlib/Combinatorics/SetFamily/Intersecting.lean`, `Mathlib/Order/UpperLower/Basic.lean` (related but this specific result not present)

## Statement 85: Definition 3.3 (Quasi-randomness)
**Status**: non-included
**Explanation**: The notion of quasi-randomness for Boolean functions with respect to the p-biased measure is not in mathlib.
**Mathlib references**: None

## Statement 86: Definition 3.5 (Quasi-random family)
**Status**: non-included
**Explanation**: This is the family-level version of quasi-randomness, not in mathlib.
**Mathlib references**: None

## Statement 87: Lemma 3.6 (Regularity lemma)
**Status**: non-included
**Explanation**: This regularity lemma for decomposing functions into quasi-random restrictions is not in mathlib.
**Mathlib references**: None

## Statement 88: Lemma 4.1 (Quasi-random sharp threshold)
**Status**: non-included
**Explanation**: This result about quasi-random monotone functions having sharp thresholds is not in mathlib.
**Mathlib references**: None

## Statement 89: Claim 4.2 (Simple EKR)
**Status**: non-included
**Explanation**: This simple version of the Erdos-Ko-Rado theorem (if $\mu_{1/2}(\mathcal{G}) + \mu_{1/2}(\mathcal{H}) > 1$ then there are disjoint sets) is not explicitly in mathlib in this form. While mathlib has intersecting family theory, this specific cross-intersection statement with measures is not present.
**Mathlib references**: `Mathlib/Combinatorics/SetFamily/Intersecting.lean` (related but not this result)

## Statement 90: Lemma 4.3 (Quasi-random not cross-intersecting)
**Status**: non-included
**Explanation**: This result about quasi-random families not being cross-intersecting is not in mathlib.
**Mathlib references**: None

## Statement 91: Theorem 1.1 (Invariance principle)
**Status**: non-included
**Explanation**: The Mossel-O'Donnell-Oleszkiewicz invariance principle is not in mathlib. This is a deep result connecting Boolean function analysis to Gaussian space analysis.
**Mathlib references**: None

## Statement 92: Corollary 1.2 (Invariance principle, qualitative)
**Status**: non-included
**Explanation**: The qualitative version of the invariance principle is not in mathlib.
**Mathlib references**: None

## Statement 93: Theorem 2.1 (Berry-Essen Theorem)
**Status**: non-included
**Explanation**: The Berry-Esseen theorem (a quantitative central limit theorem) is not formalized in mathlib. There is no central limit theorem in mathlib at all.
**Mathlib references**: None

## Statement 94: Lemma 3.1 (Hypercontractivity for Gaussian space)
**Status**: non-included
**Explanation**: Hypercontractivity for Gaussian space (the Nelson/Gross hypercontractive inequality) is not in mathlib. While mathlib has Hermite polynomials (`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), the hypercontractive inequality for functions in Gaussian space is not present.
**Mathlib references**: `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean` (Hermite polynomials defined, but hypercontractivity not proved)

## Statement 95: Lemma 3.2 (Hypercontractivity for mixed inputs)
**Status**: non-included
**Explanation**: Hypercontractivity for functions on mixed Boolean/Gaussian inputs is not in mathlib.
**Mathlib references**: None

## Statement 96: Theorem 5.1 (Invariance for non-smooth test functions)
**Status**: non-included
**Explanation**: Extension of the invariance principle to non-smooth (cutoff) test functions is not in mathlib.
**Mathlib references**: None

## Statement 97: Theorem 5.2 (Carbery-Wright)
**Status**: non-included
**Explanation**: The Carbery-Wright anti-concentration inequality for polynomials of Gaussian random variables is not in mathlib.
**Mathlib references**: None

## Statement 98: Theorem 5.3 (Invariance with Fourier tails)
**Status**: non-included
**Explanation**: The extension of the invariance principle to functions that are only approximately low-degree is not in mathlib.
**Mathlib references**: None

## Statement 99: Definition 6.1 (Gaussian noise operator)
**Status**: non-included
**Explanation**: The Ornstein-Uhlenbeck / Gaussian noise operator is not defined in mathlib.
**Mathlib references**: None

## Statement 100: Definition 6.2 (Gaussian noise stability)
**Status**: non-included
**Explanation**: Gaussian noise stability is not defined in mathlib.
**Mathlib references**: None

## Statement 101: Theorem 6.3 (Borel's theorem)
**Status**: non-included
**Explanation**: Borel's theorem (that half-spaces maximize noise stability among balanced bounded functions in Gaussian space) is not in mathlib.
**Mathlib references**: None

## Statement 102: Theorem 6.4 (Majority is Stablest, formal)
**Status**: non-included
**Explanation**: The formal version of the Majority is Stablest theorem (deduced from the invariance principle and Borel's theorem) is not in mathlib.
**Mathlib references**: None

## Statement 103: Theorem 1.1 (NP-hardness of Max-Cut/VC)
**Status**: non-included
**Explanation**: NP-hardness results are computational complexity statements. Mathlib does not formalize complexity theory or NP-hardness.
**Mathlib references**: None

## Statement 104: Theorem 3.1 (PCP Theorem)
**Status**: non-included
**Explanation**: The PCP theorem is a fundamental result in computational complexity. It is not formalized in mathlib.
**Mathlib references**: None

## Statement 105: Theorem 3.2 (Hastad)
**Status**: non-included
**Explanation**: Hastad's hardness of approximation result for 3-SAT is not in mathlib.
**Mathlib references**: None

## Statement 106: Theorem 3.3 (Max-Cut NP-hardness)
**Status**: non-included
**Explanation**: NP-hardness of approximating Max-Cut is not in mathlib.
**Mathlib references**: None

## Statement 107: Theorem 3.4 (Vertex-Cover NP-hardness)
**Status**: non-included
**Explanation**: NP-hardness of approximating Vertex Cover is not in mathlib.
**Mathlib references**: None

## Statement 108: Definition 3.5 (Unique-Games)
**Status**: non-included
**Explanation**: The Unique Games problem is a concept from computational complexity not defined in mathlib.
**Mathlib references**: None

## Statement 109: Conjecture 3.6 (Unique-Games Conjecture)
**Status**: non-included
**Explanation**: The Unique Games Conjecture is an open conjecture in computational complexity, not present in mathlib.
**Mathlib references**: None

## Statement 110: Theorem 1.1 (GW for almost bipartite)
**Status**: non-included
**Explanation**: The refined analysis of the Goemans-Williamson algorithm for near-bipartite graphs is not in mathlib.
**Mathlib references**: None

## Statement 111: Theorem 2.1 (KKMO Max-Cut hardness)
**Status**: non-included
**Explanation**: The Khot-Kindler-Mossel-O'Donnell hardness result for Max-Cut (assuming UGC) is not in mathlib.
**Mathlib references**: None

## Statement 112: Conjecture 2.3 (UGC restated)
**Status**: non-included
**Explanation**: Restatement of the UGC, not in mathlib.
**Mathlib references**: None

## Statement 113: Lemma 2.4 (Reduction analysis)
**Status**: non-included
**Explanation**: The analysis of the gap-preserving reduction from UG to Max-Cut is not in mathlib.
**Mathlib references**: None

## Statement 114: Theorem 2.5 (MIS for negative correlation)
**Status**: non-included
**Explanation**: This version of Majority is Stablest for negative correlation parameters is not in mathlib.
**Mathlib references**: None

## Statement 115: Lemma 2.6
**Status**: non-included
**Explanation**: This technical lemma about Fourier coefficients in the UG reduction is not in mathlib.
**Mathlib references**: None

## Statement 116: Theorem 1.1 (IS hardness)
**Status**: non-included
**Explanation**: UGC-based hardness of Independent Set is not in mathlib.
**Mathlib references**: None

## Statement 117: Corollary 1.2 (VC hardness)
**Status**: non-included
**Explanation**: UGC-based hardness of Vertex Cover approximation is not in mathlib. While mathlib defines vertex covers (`Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`), it does not have computational hardness results.
**Mathlib references**: `Mathlib/Combinatorics/SimpleGraph/VertexCover.lean` (definition only)

## Statement 118: Definition 1.3 (p-biased Kneser graph)
**Status**: non-included
**Explanation**: The p-biased Kneser graph is not defined in mathlib.
**Mathlib references**: None

## Statement 119: Definition 1.4 (Strongish UGC)
**Status**: non-included
**Explanation**: This strengthened form of the Unique Games Conjecture is not in mathlib.
**Mathlib references**: None

## Statement 120: Theorem 1.5 (Strongish UG reduction)
**Status**: non-included
**Explanation**: The reduction from UGC to the strongish form is not in mathlib.
**Mathlib references**: None

## Statement 121: Lemma 2.1 (IS reduction analysis)
**Status**: non-included
**Explanation**: The analysis of the reduction from Strongish UG to Independent Set is not in mathlib.
**Mathlib references**: None

## Statement 122: Lemma 3.1 (Juntas are intersecting)
**Status**: non-included
**Explanation**: This lemma about the t-assignment satisfying constraints is specific to the UG-to-IS reduction and is not in mathlib.
**Mathlib references**: None

## Statement 123: Claim 2.1 (2-approx VC)
**Status**: non-included
**Explanation**: The 2-approximation algorithm for vertex cover is an algorithmic result not formalized in mathlib.
**Mathlib references**: None
