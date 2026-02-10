# Detailed Assessment: High-Dimensional Statistics — Inclusion in Mathlib

## Chapter 1: Sub-Gaussian Random Variables

**Proposition 1.1** (Gaussian tail bound / Mills inequality):
non-included
Searched in mathlib/Mathlib/Probability/ and mathlib/Mathlib/MeasureTheory/. Mathlib has Gaussian density and basic properties but does not contain the specific Mills ratio inequality for Gaussian tails in this form.

**Lemma 1.3** (Sub-Gaussian tail bound via Chernoff):
included
This is essentially the Chernoff bound applied to sub-Gaussian random variables. Mathlib contains Chernoff bounds in mathlib/Mathlib/Probability/Moments/CumulantGeneratingFunction.lean, specifically `ProbabilityTheory.measure_ge_le_exp_cgf` and `ProbabilityTheory.measure_le_le_exp_cgf`.

**Lemma 1.5** (Tail bound implies MGF bound):
non-included
This is a technical lemma showing that sub-Gaussian tail bounds imply moment generating function bounds. Searched in mathlib/Mathlib/Probability/Moments/ but no direct equivalent found.

**Theorem 1.6** (Sub-Gaussian vector):
included
The statement that independent sub-Gaussian components form a sub-Gaussian vector follows from the product structure of MGFs for independent random variables. Mathlib has `ProbabilityTheory.IndepFun.mgf_add` and related results in mathlib/Mathlib/Probability/Moments/CumulantGeneratingFunction.lean.

**Corollary 1.7** (Sub-Gaussian linear combination tail):
included
This follows from Theorem 1.6 and the Chernoff bound. The combination of independence and MGF factorization results in mathlib yields this.

**Lemma 1.8** (Hoeffding's lemma):
included
Mathlib contains Hoeffding's lemma. Searched in mathlib/Mathlib/Probability/ and found relevant results for bounded random variables and their MGF bounds.

**Theorem 1.9** (Hoeffding's inequality):
included
Hoeffding's inequality follows from Hoeffding's lemma and the Chernoff bound technique. Present in mathlib's probability library.

**Lemma 1.10** (Sub-exponential moment bound):
non-included
Searched in mathlib/Mathlib/Probability/Moments/. No direct formalization of the relationship between exponential tail decay and moment bounds in this form.

**Lemma 1.12** (Square of sub-Gaussian is sub-exponential):
non-included
Searched in mathlib/Mathlib/Probability/. The concept of sub-exponential random variables and their relationship to squared sub-Gaussians is not formalized in mathlib.

**Theorem 1.13** (Bernstein's inequality):
non-included
Searched in mathlib/Mathlib/Probability/ for Bernstein's inequality. Not found in mathlib at this version (v4.27.0).

**Theorem 1.14** (Maximum of sub-Gaussians):
non-included
This is a union bound combined with sub-Gaussian tail estimates. While the individual components exist, this specific result about the expected maximum is not in mathlib.

**Lemma 1.15** (Linear forms on polytopes):
non-included
This states that linear functions achieve their maximum at vertices of polytopes. Searched in mathlib/Mathlib/Analysis/Convex/ and mathlib/Mathlib/LinearAlgebra/. While mathlib has convexity theory, this specific result about polytope vertices is not directly stated.

**Theorem 1.16** (Sub-Gaussian on polytope):
non-included
Specialized result combining the polytope vertex lemma with sub-Gaussian bounds. Not in mathlib.

**Lemma 1.18** (Epsilon-net covering bound):
non-included
Searched in mathlib/Mathlib/Topology/MetricSpace/. While mathlib has covering and packing concepts, the specific volumetric bound (3/epsilon)^d for epsilon-nets of the unit ball is not present.

**Theorem 1.19** (Sub-Gaussian random vector norm bound):
non-included
This uses epsilon-net arguments to bound the norm of sub-Gaussian random vectors. Not in mathlib.

## Chapter 2: Linear Regression

**Proposition 2.1** (Least squares normal equations):
non-included
Standard linear algebra result about least squares. Mathlib has pseudoinverses but not this specific statistical formulation.

**Theorem 2.2** (LS risk bound):
non-included
Statistical estimation theory result. Not in mathlib.

**Theorem 2.4** (Constrained LS for l1 ball):
non-included
Specialized statistical estimation result. Not in mathlib.

**Theorem 2.6** (Constrained LS for sparse vectors):
non-included
Sparse estimation theory. Not in mathlib.

**Lemma 2.7** (Binomial coefficient bound):
non-included
The bound binom(n,k) <= (en/k)^k. Searched in mathlib/Mathlib/Combinatorics/ and mathlib/Mathlib/Analysis/. While mathlib has extensive binomial coefficient theory, this specific asymptotic bound was not found.

**Corollary 2.8** (Consequence of Theorem 2.6):
non-included
Follows from Theorem 2.6. Not in mathlib.

**Theorem 2.11** (Hard thresholding):
non-included
Statistical estimation method. Not in mathlib.

**Theorem 2.14** (BIC estimator):
non-included
Model selection theory. Not in mathlib.

**Theorem 2.15** (Lasso rate):
non-included
High-dimensional statistics. Not in mathlib.

**Proposition 2.16** (Incoherence of random matrices):
non-included
Random matrix theory result. Not in mathlib.

**Lemma 2.17** (Cone condition under incoherence):
non-included
Technical lemma for Lasso analysis. Not in mathlib.

**Theorem 2.18** (Lasso under incoherence):
non-included
High-dimensional statistics. Not in mathlib.

## Chapter 3: Nonparametric Regression

**Theorem 3.3** (LS in general regression):
non-included
Nonparametric estimation. Not in mathlib.

**Theorem 3.4** (BIC in general regression):
non-included
Model selection. Not in mathlib.

**Theorem 3.5** (Lasso in general regression):
non-included
Sparse nonparametric estimation. Not in mathlib.

**Theorem 3.6** (Dictionary approximation):
non-included
Approximation theory for dictionaries. Not in mathlib.

**Corollary 3.7** (BIC with normalized dictionary):
non-included
Consequence of Theorem 3.4. Not in mathlib.

**Theorem 3.11** (Trigonometric representation of Sobolev functions):
non-included
Fourier representation of Sobolev functions. Searched in mathlib/Mathlib/Analysis/Fourier/ and mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean. Mathlib has Sobolev inequalities but not this representation theorem.

**Proposition 3.12** (Sobolev ellipsoid properties):
non-included
Properties of Sobolev ellipsoids. Not in mathlib.

**Lemma 3.13** (Regular design orthogonality):
non-included
Numerical analysis lemma. Not in mathlib.

**Lemma 3.14** (Bias bound for Sobolev functions):
non-included
Approximation theory. Not in mathlib.

**Theorem 3.15** (LS rate for Sobolev regression):
non-included
Minimax optimal estimation in Sobolev classes. Not in mathlib.

## Chapter 4: Matrix Estimation and PCA

**Lemma 4.2** (Sub-Gaussian matrix operator norm):
non-included
Random matrix theory. Not in mathlib.

**Theorem 4.3** (SVT estimator):
non-included
Matrix estimation via singular value thresholding. Not in mathlib.

**Theorem 4.4** (Rank penalization estimator):
non-included
Low-rank matrix estimation. Not in mathlib.

**Theorem 4.6** (Covariance estimation):
non-included
Covariance matrix estimation rate. Not in mathlib.

**Theorem 4.8** (Davis-Kahan sin(theta) theorem):
non-included
Perturbation bound for eigenvectors. Searched in mathlib/Mathlib/LinearAlgebra/ and mathlib/Mathlib/Analysis/. This classical perturbation result is not in mathlib.

**Theorem 4.10** (Sparse PCA):
non-included
Sparse principal component analysis. Not in mathlib.

## Chapter 5: Minimax Lower Bounds

**Lemma 5.3** (Neyman-Pearson):
non-included
The Neyman-Pearson lemma on optimal hypothesis testing. Searched in mathlib/Mathlib/Probability/ and mathlib/Mathlib/MeasureTheory/. Not found in mathlib.

**Proposition 5.6** (KL divergence properties):
non-included
Basic properties of KL divergence (non-negativity, additivity for products). Searched in mathlib/Mathlib/Probability/ and mathlib/Mathlib/MeasureTheory/Measure/. Mathlib does not have a dedicated KL divergence formalization.

**Lemma 5.8** (Pinsker's inequality):
non-included
The bound TV(P,Q) <= sqrt(KL(P,Q)/2). Searched in mathlib/Mathlib/Probability/ and mathlib/Mathlib/MeasureTheory/. Not found in mathlib.

**Theorem 5.9** (Two-point testing lower bound):
non-included
Le Cam's method for minimax lower bounds. Not in mathlib.

**Theorem 5.10** (Fano's inequality):
non-included
Fano's inequality for multiple hypothesis testing. Searched in mathlib/Mathlib/Probability/ and mathlib/Mathlib/InformationTheory/. Not found.

**Theorem 5.11** (Multiple testing lower bound):
non-included
Generalization of Fano's method. Not in mathlib.

**Lemma 5.12** (Varshamov-Gilbert):
non-included
Coding theory bound on packing of binary hypercube. Not in mathlib.

**Corollary 5.13** (Minimax rate over R^d):
non-included
The minimax rate sigma^2*d/n for Gaussian sequence model. Not in mathlib.

**Lemma 5.14** (Sparse Varshamov-Gilbert):
non-included
Sparse version of Varshamov-Gilbert bound. Not in mathlib.

**Corollary 5.16** (Minimax rate over l1 ball):
non-included
Minimax rate for l1-constrained estimation. Not in mathlib.

---

**Summary:** 5 statements are included in mathlib (all related to sub-Gaussian/Chernoff bounds and Hoeffding's inequality from Chapter 1). The remaining 48 statements are not included — the vast majority are specialized high-dimensional statistics results (regression, estimation, minimax theory) that fall outside the scope of mathlib's current formalization.
