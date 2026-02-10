# Detailed Assessment of Mathematical Statements

## Statement 1: Theorem (No-Free-Lunch Theorem, Version 1)
For any integer $n \geq 1$, any classifier $\hat{h}$ built from $(X_1, Y_1), \ldots, (X_n, Y_n)$ and any $\varepsilon > 0$, there exists a distribution $P_{X,Y}$ for (X,Y) such that $R(h^*) = 0$ and $\mathbb{E}R(\hat{h}_n) \geq 1/2 - \varepsilon$.

Assessment: non-included
This is a foundational result in statistical learning theory stating that without restricting the hypothesis class, no learning algorithm can achieve low risk universally. Searched mathlib for "NoFreeLunch", "PAC", "learning", "classifier", and related learning-theoretic terms. Mathlib does not contain any statistical learning theory results of this nature. The library focuses on pure probability theory and measure theory but does not include machine learning minimax lower bounds.

## Statement 2: Theorem (No-Free-Lunch Theorem, Version 2)
For any classifier $\hat{h}$ built from $(X_1, Y_1), \ldots, (X_n, Y_n)$ and any sequence $\{a_n\}_n > 0$ that converges to 0, there exists a distribution $P_{X,Y}$ for (X,Y) such that $R(h^*) = 0$ and $\mathbb{E}R(\hat{h}_n) \ge a_n$, for all $n \ge 1$.

Assessment: non-included
This is a stronger version of the no-free-lunch theorem showing that convergence of the classification error can be arbitrarily slow. As with Statement 1, mathlib does not contain statistical learning theory minimax lower bounds. Searched for "NoFreeLunch", "PAC", "learning", and related terms without finding matching formalization.

## Statement 3: Theorem (Bayes Classifier Optimality)
For any classifier h, the following identity holds:
$$R(h) - R(h^*) = \int_{h \neq h^*} |2\eta(x) - 1| P_x(dx) = \mathbb{E}_X[|2\eta(X) - 1| \mathbf{1}(h(X) \neq h^*(X))]$$
In particular, the classification error $R^*$ of the Bayes classifier is the minimizer of R(h) over all classifiers h. Moreover,
$$R(h^*) = \mathbb{E}[\min(\eta(X), 1 - \eta(X))] \le \frac{1}{2}.$$

Assessment: non-included
This establishes the optimality of the Bayes classifier and gives an explicit formula for the excess risk. Searched mathlib under Probability/ for "Bayes", "classifier", "excess_risk", "regression_function" and found no formalization. Mathlib has some decision theory in `Probability/Decision/Risk/` but this concerns abstract minimax risk definitions, not the specific Bayes classifier optimality result for binary classification.

## Statement 4: Theorem (Hoeffding's Theorem)
Let $X_1, \ldots, X_n$ be n independent random variables such that $X_i \in [0, 1]$ almost surely. Then for any t > 0,
$$\mathbb{P}\left(\left|\frac{1}{n}\sum_{i=1}^{n}X_{i} - \mathbb{E}X_{i}\right| > t\right) \leq 2e^{-2nt^{2}}.$$

Assessment: included
Hoeffding's inequality is formalized in mathlib at `Mathlib/Probability/Moments/SubGaussian.lean`. The file contains `measure_sum_ge_le_of_iIndepFun` which is described as "Hoeffding's inequality for sums of independent sub-Gaussian random variables." The sub-Gaussian framework in mathlib generalizes bounded random variables (which are sub-Gaussian by Hoeffding's lemma), so the classical Hoeffding bound for bounded random variables follows from the sub-Gaussian Hoeffding inequality combined with Hoeffding's lemma.

## Statement 5: Lemma (Hoeffding's Lemma)
If $Z \in [a, b]$ almost surely and $\mathbb{E}Z = 0$, then
$$\mathbb{E}e^{sZ} \leq e^{\frac{s^2(b-a)^2}{8}}.$$

Assessment: included
Hoeffding's lemma is formalized in mathlib at `Mathlib/Probability/Moments/SubGaussian.lean`. The file explicitly lists `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` as "Hoeffding's lemma for random variables with expectation zero." This proves that a bounded, centered random variable has sub-Gaussian moment generating function with the appropriate parameter, which is exactly Hoeffding's lemma.

## Statement 6: Theorem (ERM Oracle Inequality for Finite Dictionary)
The estimator $\hat{h}$ satisfies
$$R(\hat{h}) \le R(\bar{h}) + \sqrt{\frac{2\log(2M/\delta)}{n}}$$
with probability at least $1 - \delta$. In expectation, it holds that
$$\mathbb{E}[R(\hat{h})] \le R(\bar{h}) + \sqrt{\frac{2\log(2M)}{n}}.$$

Assessment: non-included
This is a fundamental oracle inequality for empirical risk minimization over a finite hypothesis class. It combines Hoeffding's inequality with a union bound argument. Searched mathlib for "ERM", "empirical_risk", "oracle", "finite_dictionary" and found no formalization. Mathlib does not contain learning-theoretic oracle inequalities or empirical risk minimization results.

## Statement 7: Theorem (Azuma-Hoeffding)
Suppose that $\{\Delta_i\}_i$ are martingale differences with respect to the filtration $\{\mathcal{F}_i\}_i$, and let $A_i, B_i \in \mathcal{F}_{i-1}$ satisfy $A_i \leq \Delta_i \leq B_i$ almost surely for every i. Then
$$\mathbb{P}\left[\frac{1}{n}\sum_{i}\Delta_{i} > t\right] \leq \exp\left(-\frac{2n^{2}t^{2}}{\sum_{i=1}^{n}\|B_{i} - A_{i}\|_{\infty}^{2}}\right).$$

Assessment: included
The Azuma-Hoeffding inequality is formalized in mathlib at `Mathlib/Probability/Moments/SubGaussian.lean`. The file explicitly lists `measure_sum_ge_le_of_HasCondSubgaussianMGF` as "the Azuma-Hoeffding inequality for sub-Gaussian random variables." The formalization uses the framework of conditionally sub-Gaussian random variables, which generalizes the classical bounded martingale difference setting.

## Statement 8: Theorem (Bounded Differences Inequality / McDiarmid's Inequality)
If $g: \mathcal{X} \to \mathbb{R}$ satisfies the bounded differences condition with constants $c_i$, then
$$\mathbb{P}\left[|g(X_1,\ldots,X_n) - \mathbb{E}[g(X_1,\ldots,X_n)]| > t\right] \le 2\exp\left(-\frac{2t^2}{\sum_i c_i^2}\right).$$

Assessment: non-included
McDiarmid's inequality (also known as the Bounded Differences Inequality) is a consequence of Azuma-Hoeffding applied to the Doob martingale of the function g. Searched mathlib for "McDiarmid", "bounded_differences", "BoundedDifferences" and found no formalization. While Azuma-Hoeffding is in mathlib, the specific bounded differences corollary and the construction of the Doob martingale from a function satisfying bounded differences are not formalized.

## Statement 9: Theorem (Bernstein's Inequality)
Let $X_1, \ldots, X_n$ be independent, centered random variables with $|X_i| \leq c$ for every i, and write $\sigma^2 = n^{-1} \sum_i \text{Var}(X_i)$ for the average variance. Then
$$\mathbb{P}\left[\frac{1}{n}\sum_{i}X_{i} > t\right] \leq \exp\left(-\frac{nt^{2}}{2\sigma^{2} + \frac{2}{3}tc}\right).$$

Assessment: non-included
Bernstein's inequality is a variance-sensitive concentration inequality that improves upon Hoeffding when the variance is small. Searched mathlib for "Bernstein" and found files related to Bernstein polynomials (`Analysis/SpecialFunctions/Bernstein.lean`, `RingTheory/Polynomial/Bernstein.lean`) and the Schroeder-Bernstein theorem, but not Bernstein's concentration inequality. The file `Probability/Moments/SubGaussian.lean` deals with sub-Gaussian random variables but does not include the Bernstein-type variance-adaptive bound.

## Statement 10: Theorem (Fast Rate under Massart's Noise Condition)
Let $\mathcal{E}(\hat{h})$ denote the excess risk of the empirical risk minimizer $\hat{h} = \hat{h}^{\text{erm}}$. If Massart's noise condition is satisfied with constant $\gamma$, then
$$\mathcal{E}(\hat{h}) \le \frac{\log(M/\delta)}{\gamma n}$$
with probability at least $1 - \delta$.

Assessment: non-included
This result gives fast rates for ERM under Massart's noise condition, which controls how close the regression function is to 1/2. Searched mathlib for "Massart", "noise_condition", "fast_rate", "excess_risk" and found no formalization. This is a specialized learning-theoretic result not present in mathlib.

## Statement 11: Theorem (Fast Rate under Tsybakov's Noise Condition)
Let $\mathcal{H}$ be a finite class of cardinality $M$ such that $h^* \in \mathcal{H}$. If Tsybakov's noise condition is satisfied with exponent $\kappa \geq 1$, then with probability at least $1 - \delta$,
$$\mathcal{E}(\hat{h}) \le C_{\kappa}\left(\frac{\log(M/\delta)}{n}\right)^{\kappa/(2\kappa-1)}.$$

Assessment: non-included
This extends the fast rate result to Tsybakov's more general noise condition, which allows for a continuous range of noise levels parameterized by the exponent $\kappa$. Searched mathlib for "Tsybakov", "noise_exponent", "margin_condition" and found no formalization. This is a specialized statistical learning theory result not present in mathlib.

## Statement 12: Theorem (Symmetrization / Rademacher Complexity Bound)
Let $\mathcal{H}$ be a class of classifiers and $\hat{h} = \hat{h}^{\text{erm}}$. Then
$$\mathbb{E}[\mathcal{E}(\hat{h})] \le 2\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^n \varepsilon_i \ell(h, Z_i)\right]$$
where $\varepsilon_1, \ldots, \varepsilon_n$ are independent Rademacher random variables.

Assessment: non-included
This result bounds the expected excess risk of the ERM by the Rademacher complexity of the loss class. Searched mathlib for "Rademacher" and found `Analysis/Calculus/Rademacher.lean` which is about Rademacher's theorem on differentiability of Lipschitz functions, not Rademacher complexity in learning theory. No formalization of Rademacher complexity or symmetrization bounds for empirical processes was found.

## Statement 13: Lemma (Symmetrization Lemma)
$$\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^{n}(P - P_n)f_h\right] \le 2\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^{n}\varepsilon_i f_h(Z_i)\right]$$
where $\varepsilon_1, \ldots, \varepsilon_n$ are i.i.d. Rademacher random variables.

Assessment: non-included
The symmetrization lemma is a key tool in empirical process theory that replaces expectations over the data distribution with expectations over Rademacher random variables. Searched mathlib for "symmetrization", "Rademacher_complexity", "empirical_process" and found no relevant formalization. Mathlib does not contain empirical process theory results.

## Statement 14: Lemma (Contraction Lemma / Ledoux-Talagrand)
If $\phi: \mathbb{R} \to \mathbb{R}$ is L-Lipschitz with $\phi(0) = 0$, then
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}}\sum_{i=1}^{n}\varepsilon_i\phi(f(Z_i))\right] \le L\mathbb{E}\left[\sup_{f \in \mathcal{F}}\sum_{i=1}^{n}\varepsilon_i f(Z_i)\right].$$

Assessment: non-included
The contraction lemma (Ledoux-Talagrand) states that composing with a Lipschitz function does not increase the Rademacher complexity. Searched mathlib for "contraction_lemma", "contraction_principle", "Ledoux", "Talagrand" and found no formalization. This is an empirical process theory result not present in mathlib.

## Statement 15: Theorem (Massart's Finite Lemma)
Let $x_1, \ldots, x_N \in \mathbb{R}^n$ with $\max_j \|x_j\| \leq r$. Then
$$\mathbb{E}\left[\max_{1 \le j \le N} \sum_{i=1}^{n} \varepsilon_i x_{ij}\right] \le r\sqrt{2\log N}.$$

Assessment: non-included
Massart's finite lemma gives a bound on the expected maximum of Rademacher sums over a finite set. Searched mathlib for "Massart", "finite_lemma", "Rademacher" and found no formalization. This is a concentration/empirical process result not present in mathlib.

## Statement 16: Theorem (Dudley's Entropy Integral / Chaining Bound)
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}} \frac{1}{n}\sum_{i=1}^n \varepsilon_i f(Z_i)\right] \le \frac{c}{n}\int_0^{\text{diam}(\mathcal{F})} \sqrt{\log N(\mathcal{F}, \|\cdot\|_n, \varepsilon)}\, d\varepsilon$$
where $N(\mathcal{F}, \|\cdot\|_n, \varepsilon)$ is the covering number of $\mathcal{F}$ w.r.t. the empirical $L^2$ norm at scale $\varepsilon$.

Assessment: non-included
Dudley's entropy integral bounds the Rademacher complexity by an integral involving covering numbers. While mathlib does have covering numbers formalized in `Topology/MetricSpace/CoveringNumbers.lean`, the chaining argument and the Dudley integral bound connecting covering numbers to Rademacher complexity are not formalized. Searched for "Dudley", "chaining", "entropy_integral" without results.

## Statement 17: Lemma (Sauer-Shelah Lemma / Sauer's Lemma)
If the VC-dimension of $\mathcal{H}$ is $V$, then for all $n \geq V$,
$$\sup_{z_1,\ldots,z_n} |\{(h(z_1),\ldots,h(z_n)) : h \in \mathcal{H}\}| \le \sum_{k=0}^{V} \binom{n}{k} \le \left(\frac{en}{V}\right)^V.$$

Assessment: included
The Sauer-Shelah lemma is formalized in mathlib at `Mathlib/Combinatorics/SetFamily/Shatter.lean`. The file contains both `card_le_card_shatterer` (Pajor's variant of the Sauer-Shelah lemma) and `card_shatterer_le_sum_vcDim` which is labeled as "The Sauer-Shelah lemma." The VC dimension is defined as `vcDim` in the same file. The formalization bounds the cardinality of the shatterer by the sum of binomial coefficients up to the VC dimension, which is equivalent to the textbook statement.

## Statement 18: Theorem (VC Dimension Bound on Excess Risk)
If the VC-dimension of $\mathcal{H}$ is $V < \infty$, then
$$\mathbb{E}[\mathcal{E}(\hat{h})] \le C\sqrt{\frac{V\log(n/V)}{n}}.$$

Assessment: non-included
This result combines the Sauer-Shelah lemma, Dudley's entropy integral, and symmetrization to bound the excess risk in terms of VC dimension. While mathlib has Sauer-Shelah, it does not have the chain of results connecting VC dimension to excess risk bounds. Searched for "VC", "excess_risk", "VCBound" without finding a complete formalization of this learning-theoretic bound.

## Statement 19: Theorem (Lower Bound via VC Dimension)
For any $V \geq 1$ and $n \geq V$, there exists a class $\mathcal{H}$ of VC-dimension $V$ and a distribution $P_{X,Y}$ with $h^* \in \mathcal{H}$ such that for any classifier $\hat{h}$ built from $n$ observations,
$$\mathbb{E}[\mathcal{E}(\hat{h})] \geq c\sqrt{\frac{V}{n}}.$$

Assessment: non-included
This is a minimax lower bound showing that the VC dimension rate is optimal up to logarithmic factors. Searched mathlib for "minimax", "lower_bound", "VC" and found no formalization. Minimax lower bounds in statistical learning theory are not present in mathlib.

## Statement 20: Theorem (Convex Risk Bound via Rademacher Complexity)
For convex surrogate $\phi$-risk minimization over a class $\mathcal{F}$ with $\|f\|_\infty \leq 1$ for all $f \in \mathcal{F}$, if $\phi$ is L-Lipschitz, then
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}} |R_{n,\phi}(f) - R_\phi(f)|\right] \le 2L \cdot \mathfrak{R}_n(\mathcal{F})$$
where $\mathfrak{R}_n(\mathcal{F})$ is the Rademacher complexity of $\mathcal{F}$.

Assessment: non-included
This extends the Rademacher complexity bound to convex surrogate losses. Searched mathlib for "Rademacher", "surrogate", "convex_risk", "phi_risk" and found no formalization. This is a learning-theoretic result combining empirical process theory with convex analysis that is not present in mathlib.

## Statement 21: Theorem (Representer Theorem)
Consider the minimization of $\hat{R}_{n,\phi}(f) + \lambda\|f\|_{\mathcal{H}_K}^2$ over a reproducing kernel Hilbert space $\mathcal{H}_K$. Then the minimizer has the form
$$\hat{f}(\cdot) = \sum_{i=1}^n \alpha_i K(X_i, \cdot)$$
for some $\alpha_1, \ldots, \alpha_n \in \mathbb{R}$.

Assessment: non-included
The Representer Theorem is a foundational result in kernel methods and RKHS theory. Searched mathlib for "representer", "RKHS", "reproducing", "ReproducingKernel" and found no relevant formalization. Mathlib has inner product spaces (`Analysis/InnerProductSpace/`) and orthogonal projections, but does not formalize reproducing kernel Hilbert spaces or the representer theorem.

## Statement 22: Theorem (Projected Gradient Descent Convergence)
Let $f$ be a convex function on a closed convex set $\mathcal{C} \subset \mathbb{R}^d$ with $\text{diam}(\mathcal{C}) \leq R$ and $\|g\| \leq L$ for all $g \in \partial f(x)$, $x \in \mathcal{C}$. Then projected gradient descent with step size $\eta = \frac{R}{L\sqrt{k}}$ satisfies
$$f(\bar{x}_k) - f(x^*) \le \frac{LR}{\sqrt{k}}.$$

Assessment: non-included
This is a standard convergence rate result for projected gradient descent on convex functions. Searched mathlib for "gradient_descent", "GradientDescent", "projected", "subgradient" and found no formalization. Mathlib does not contain optimization algorithm convergence results. While convex analysis tools exist in mathlib (convex functions, subgradients), the iterative algorithmic convergence analysis is absent.

## Statement 23: Theorem (Mirror Descent Convergence)
Assume that $\Phi$ is $\alpha$-strongly convex on $\mathcal{C} \cap \mathcal{D}$ w.r.t. $\|\cdot\|$ and $R^{2} = \sup_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x) - \min_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x)$. Then, Mirror Descent with $\eta = \frac{R}{L}\sqrt{\frac{2\alpha}{k}}$ gives
$$f(\bar{x}_k) - f(x^*) \le RL\sqrt{\frac{2}{\alpha k}}.$$

Assessment: non-included
Mirror descent convergence is a generalization of projected gradient descent using Bregman divergences. Searched mathlib for "mirror_descent", "MirrorDescent", "Bregman", "strongly_convex" and found no formalization. Mathlib does not contain Bregman divergences or mirror descent analysis.

## Statement 24: Corollary (Mirror Descent on the Simplex)
Let f be a convex function on $\Delta_d$ such that $\|g\|_{\infty} \le L$ for all $g \in \partial f(x)$, $x \in \Delta_d$. Then, Mirror descent with $\eta = \frac{1}{L} \sqrt{\frac{2 \log(d)}{k}}$ gives
$$f(\overline{x}_k) - f(x^*) \le L\sqrt{\frac{2\log(d)}{k}}.$$

Assessment: non-included
This is the specific application of mirror descent with the negative entropy potential on the simplex, which yields a logarithmic dependence on the dimension. As with Statement 23, mathlib does not contain mirror descent analysis. Searched for "mirror", "simplex", "entropy" in the optimization context without results.

## Statement 25: Theorem (Stochastic Gradient Descent Convergence)
Let $\mathcal{C}$ be a closed convex subset of $\mathbb{R}^d$ such that $\operatorname{diam}(\mathcal{C}) \leq R$. Assume that the convex function $f(x) = \mathbb{E}[\ell(x,Z)]$ attains its minimum on $\mathcal{C}$ at $x^* \in \mathbb{R}^d$. Assume that $\ell(x,Z)$ is convex $P_Z$ a.s. and that $\mathbb{E}\|\tilde{g}\|^2 \leq L^2$ for all $\tilde{g} \in \partial \ell(x,Z)$ for all x. Then if $\eta_s \equiv \eta = \frac{R}{L\sqrt{k}}$,
$$\mathbb{E}[f(\bar{x}_k)] - f(x^*) \le \frac{LR}{\sqrt{k}}.$$

Assessment: non-included
This extends the projected gradient descent convergence result to the stochastic setting where only noisy gradient estimates are available. Searched mathlib for "stochastic_gradient", "SGD", "stochastic_optimization" and found no formalization. Mathlib does not contain stochastic optimization results.

## Statement 26: Theorem (Stochastic Mirror Descent Convergence)
Assume that $\Phi$ is $\alpha$-strongly convex on $\mathcal{C} \cap \mathcal{D}$ w.r.t. $\|\cdot\|$ and $R^{2} = \sup_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x) - \min_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x)$. Then, Stochastic Mirror Descent with $\eta = \frac{R}{L}\sqrt{\frac{2\alpha}{k}}$ outputs $\bar{x}_k$ such that
$$\mathbb{E}[f(\bar{x}_k)] - f(x^*) \le RL\sqrt{\frac{2}{\alpha k}}.$$

Assessment: non-included
This extends mirror descent convergence to the stochastic setting. As with Statements 23 and 25, mathlib does not contain Bregman divergences, mirror descent, or stochastic optimization results. Searched for "stochastic_mirror", "Bregman" without results.

## Statement 27: Theorem (Exponential Weights Regret Bound)
Assume $\ell(\cdot, z)$ is convex for all $z \in \mathcal{Z}$ and that $\ell(p, z) \in [0, 1]$ for all $p \in \Delta^K, z \in \mathcal{Z}$. Then the EW strategy has regret
$$R_n \le \frac{\log K}{\eta} + \frac{\eta n}{2}.$$
In particular, for $\eta = \sqrt{\frac{2 \log K}{n}}$,
$$R_n \le \sqrt{2n\log K}.$$

Assessment: non-included
This is a fundamental result in online learning theory bounding the regret of the exponential weights algorithm. Searched mathlib for "regret", "exponential_weights", "online_learning", "expert" and found no formalization. Mathlib does not contain online learning or regret analysis results.

## Statement 28: Theorem (FPL Regret Bound)
FPL with $\eta = \frac{1}{\sqrt{Kn}}$ yields expected regret:
$$\mathbb{E}_{\xi}[R_n] \le 2\sqrt{2nK}.$$

Assessment: non-included
Follow the Perturbed Leader is an online learning algorithm. Searched mathlib for "FPL", "perturbed_leader", "regret" and found no formalization. Online learning algorithms and their regret analysis are not present in mathlib.

## Statement 29: Lemma (Be-The-Leader Lemma)
For all loss function $\ell(p, z)$, let $p_t^* = \arg\min_{p \in \Delta^K} \sum_{s=1}^t \ell(p, z_s)$. Then we have
$$\sum_{t=1}^{n} \ell(p_t^*, z_t) \le \sum_{t=1}^{n} \ell(p_n^*, z_t).$$

Assessment: non-included
The Be-The-Leader lemma is a simple but useful result in online learning showing that the hindsight-optimal strategy does at least as well cumulatively as any fixed strategy. Searched mathlib for "leader", "BTL", "online" and found no formalization. This is an online learning result not present in mathlib.

## Statement 30: Theorem (UCB Regret Bound)
The UCB policy has regret
$$R_n \le 8 \sum_{k,\Delta_k > 0} \frac{\log n}{\Delta_k} + (1 + \frac{\pi^2}{3}) \sum_{k=1}^K \Delta_k.$$

Assessment: non-included
The Upper Confidence Bound algorithm and its regret analysis are foundational results in the multi-armed bandit literature. Searched mathlib for "UCB", "bandit", "upper_confidence", "arm" and found no formalization. Multi-armed bandit theory is not present in mathlib.

## Statement 31: Theorem (Bounded Regret Policy)
BRP has regret
$$R_n \le \Delta + \frac{16}{\Delta}.$$

Assessment: non-included
This result shows that when a separator between arm means is known, bounded (non-growing) regret is achievable. Searched mathlib for "bounded_regret", "bandit", "BRP" and found no formalization. This is a bandit theory result not present in mathlib.

## Statement 32: Lemma (Prediction with Individual Sequences)
For a stable $\phi$, the following are equivalent:
a) $\exists (\hat{q}_t)_{t=1,\dots,n} \forall y_1,\dots,y_n \quad \mathbb{E}\left[\frac{1}{n} \sum_{t=1}^n \mathbb{1}\{\hat{y}_t \neq y_t\}\right] \leq \phi(y_1,\dots,y_n)$
b) $\mathbb{E}[\phi(\epsilon_1,\ldots,\epsilon_n)] \geq \frac{1}{2}$ where $\epsilon_1,\ldots,\epsilon_n$ are Rademacher random variables.

Assessment: non-included
This is a characterization result from the theory of prediction of individual sequences, connecting the existence of a prediction strategy to a probabilistic condition involving Rademacher random variables. Searched mathlib for "individual_sequence", "prediction", "stable" in this context and found no formalization. This is a specialized online learning / sequential prediction result not present in mathlib.

## Statement 33: Lemma (Unbiased Estimator for Bandit Feedback)
$\hat{l}(e_i, z_t) = \frac{l(e_j, z_t) \mathbb{I}(a_t = e_j)}{P(a_t = e_j)}$ is an unbiased estimator of $l(e_i, z_t)$.

Assessment: non-included
This is the importance-weighted estimator used in adversarial bandit algorithms (Exp3). Searched mathlib for "importance_weighting", "unbiased_estimator", "bandit" and found no formalization. Bandit algorithm analysis is not present in mathlib.

## Statement 34: Theorem (Geometric Hedge Regret Bound for Linear Bandits)
Using Geometric Hedge algorithm for linear bandit with bandit feedback, with $\gamma = \frac{1}{n^{1/3}}$ and $\eta = \sqrt{\frac{\log n}{kn^{4/3}}}$, we have
$$\mathbb{E}[R_n] \le C n^{2/3} \sqrt{\log n} \, k^{3/2}.$$

Assessment: non-included
This is a regret bound for the Geometric Hedge algorithm in the linear bandit setting. Searched mathlib for "geometric_hedge", "linear_bandit", "regret" and found no formalization. Linear bandit theory is not present in mathlib.

## Statement 35: Theorem (Improved Linear Bandit Regret via Design Matrix)
Let $C_t = \mathbb{E}_{a_t \sim q_t}[a_t a_t^T]$, $\hat{z}_t = (a_t^T z_t) C_t^{-1} a_t$, and $\gamma = 0$. Using Geometric Hedge algorithm with $\eta = 2\sqrt{\frac{\log n}{n}}$ for linear bandit with bandit feedback leads to
$$\mathbb{E}[R_n] \le CK\sqrt{n\log n}.$$

Assessment: non-included
This improves the linear bandit regret bound using the design matrix approach. Searched mathlib for "linear_bandit", "design_matrix", "regret" and found no formalization. This is a specialized online learning result not present in mathlib.

## Statement 36: Theorem (Von Neumann Minimax Theorem)
$$\max_{p \in \Delta_n} \min_{q \in \Delta_m} p^\top M q = \min_{q \in \Delta_m} \max_{p \in \Delta_n} p^\top M q.$$

Assessment: non-included
The Von Neumann minimax theorem for zero-sum games. Searched mathlib for "minimax", "vonNeumann", "VonNeumann" and found `Order/SaddlePoint.lean` which contains the trivial minimax inequality (`iSup2_iInf2_le_iInf2_iSup2`) and saddle point theory. However, the actual Von Neumann minimax theorem (that the minimax equals the maximin for bilinear functions over simplices) is not formalized. The file `Probability/Decision/Risk/Basic.lean` contains minimax-related definitions but not the classical theorem. The saddle point file has definitions and the trivial inequality direction but not the full minimax equality.

## Statement 37: Theorem (Sion's Minimax Theorem)
Let A and Z be convex, compact spaces, and $f: A \times Z \to \mathbb{R}$. If $f(a, \cdot)$ is upper semicontinuous and quasiconcave on $Z$ for all $a \in A$ and $f(\cdot,z)$ is lower semicontinuous and quasiconvex on $A$ for all $z \in Z$, then
$$\inf_{a \in A} \sup_{z \in Z} f(a, z) = \sup_{z \in Z} \inf_{a \in A} f(a, z).$$

Assessment: non-included
Sion's minimax theorem generalizes Von Neumann's theorem to quasiconvex-quasiconcave functions on convex compact sets. Searched mathlib for "Sion", "minimax" and found no formalization of Sion's theorem. The `Order/SaddlePoint.lean` file has the trivial minimax inequality but not the full Sion theorem. This is a result from topological game theory not currently in mathlib.

## Statement 38: Theorem (Blackwell's Approachability Theorem)
Let S be a closed convex set of $\mathbb{R}^d$ with $\|x\| \leq R$ for all $x \in S$. If for all $z$, there exists $a$ such that $\ell(a, z) \in S$, then S is approachable. Moreover, there exists a strategy such that
$$d(\bar{\ell}_n, S) \le \frac{2R}{\sqrt{n}}.$$

Assessment: non-included
Blackwell's approachability theorem is a fundamental result in game theory that generalizes minimax theory to vector-valued payoffs. Searched mathlib for "Blackwell", "approachability", "vector_payoff" and found no formalization. This is a game-theoretic result not present in mathlib.

## Statement 39: Theorem (Potential-Based Approachability Rate)
If $\|\ell(a,z)\| \leq R$ holds for all $a \in \mathcal{A}, z \in \mathcal{Z}$ and all assumptions on the potential $\Phi$ are satisfied, then
$$\Phi(\bar{\ell}_n) \le \frac{4R^2h\log n}{n}.$$

Assessment: non-included
This is a refined approachability result using potential functions to adapt to the geometry of the problem. Searched mathlib for "approachability", "potential", "Blackwell" and found no formalization. This is an advanced game-theoretic/online learning result not present in mathlib.

## Statement 40: Lemma (Separating Hyperplane from Potential)
For any convex, closed set S and $z \in S$, $x \in S^C$, the following properties hold:
- $\langle z - \pi(x), \nabla \Phi(x) \rangle \leq 0$,
- $\langle x - \pi(x), \nabla \Phi(x) \rangle \ge \Phi(x)$.
In particular, if $\Phi$ is positive on $S^C$, then $H:=\{y\mid \langle y-\pi(x),\nabla\Phi(x)\rangle=0\}$ is a separating hyperplane.

Assessment: non-included
This lemma is part of the potential-based approachability framework. It uses properties of convex functions and Bregman projections. While mathlib has convex analysis tools and inner product space projections (`Analysis/InnerProductSpace/Projection/`), the specific combination with Bregman divergences and the potential function framework is not formalized. Searched for "Bregman", "potential_function" without results.

## Statement 41: Proposition (Bregman Projection Inequality)
For all $z \in S$, it holds
$$\langle \nabla \Phi(\pi(x)) - \nabla \Phi(x), \pi(x) - z \rangle \le 0.$$

Assessment: non-included
This is a property of Bregman projections, analogous to the variational characterization of orthogonal projections in Hilbert spaces. While mathlib has orthogonal projection theory in `Analysis/InnerProductSpace/Projection/`, the generalization to Bregman projections (defined via general convex functions rather than the quadratic norm) is not formalized. Searched for "Bregman" without results.

## Statement 42: Theorem (Minimax Regret for Combinatorial Bandits)
Let $n \geq d^2$. In the full information and semi-bandit games, we have
$$0.008 \, d\sqrt{n} \leq \overline{R}_n \leq d\sqrt{2n},$$
and in the bandit game,
$$0.01 \, d^{3/2}\sqrt{n} \le \overline{R}_n \le 2 \, d^{5/2}\sqrt{2n}.$$

Assessment: non-included
This provides matching upper and lower bounds on the minimax regret for combinatorial bandit problems. Searched mathlib for "combinatorial_bandit", "minimax_regret", "semi_bandit" and found no formalization. Combinatorial bandit theory and minimax regret analysis are not present in mathlib.
