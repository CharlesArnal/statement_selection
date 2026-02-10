# All Mathematical Statements from Mathematics of Machine Learning

## Statement 1: Theorem (No-Free-Lunch Theorem, Version 1)
For any integer $n \geq 1$, any classifier $\hat{h}$ built from $(X_1, Y_1), \ldots, (X_n, Y_n)$ and any $\varepsilon > 0$, there exists a distribution $P_{X,Y}$ for (X,Y) such that $R(h^*) = 0$ and $\mathbb{E}R(\hat{h}_n) \geq 1/2 - \varepsilon$.

## Statement 2: Theorem (No-Free-Lunch Theorem, Version 2)
For any classifier $\hat{h}$ built from $(X_1, Y_1), \ldots, (X_n, Y_n)$ and any sequence $\{a_n\}_n > 0$ that converges to 0, there exists a distribution $P_{X,Y}$ for (X,Y) such that $R(h^*) = 0$ and $\mathbb{E}R(\hat{h}_n) \ge a_n$, for all $n \ge 1$.

## Statement 3: Theorem (Bayes Classifier Optimality)
For any classifier h, the following identity holds:
$$R(h) - R(h^*) = \int_{h \neq h^*} |2\eta(x) - 1| P_x(dx) = \mathbb{E}_X[|2\eta(X) - 1| \mathbf{1}(h(X) \neq h^*(X))]$$
In particular, the classification error $R^*$ of the Bayes classifier is the minimizer of R(h) over all classifiers h. Moreover,
$$R(h^*) = \mathbb{E}[\min(\eta(X), 1 - \eta(X))] \le \frac{1}{2}.$$

## Statement 4: Theorem (Hoeffding's Theorem)
Let $X_1, \ldots, X_n$ be n independent random variables such that $X_i \in [0, 1]$ almost surely. Then for any t > 0,
$$\mathbb{P}\left(\left|\frac{1}{n}\sum_{i=1}^{n}X_{i} - \mathbb{E}X_{i}\right| > t\right) \leq 2e^{-2nt^{2}}.$$

## Statement 5: Lemma (Hoeffding's Lemma)
If $Z \in [a, b]$ almost surely and $\mathbb{E}Z = 0$, then
$$\mathbb{E}e^{sZ} \leq e^{\frac{s^2(b-a)^2}{8}}.$$

## Statement 6: Theorem (ERM Oracle Inequality for Finite Dictionary)
The estimator $\hat{h}$ satisfies
$$R(\hat{h}) \le R(\bar{h}) + \sqrt{\frac{2\log(2M/\delta)}{n}}$$
with probability at least $1 - \delta$. In expectation, it holds that
$$\mathbb{E}[R(\hat{h})] \le R(\bar{h}) + \sqrt{\frac{2\log(2M)}{n}}.$$

## Statement 7: Theorem (Azuma-Hoeffding)
Suppose that $\{\Delta_i\}_i$ are martingale differences with respect to the filtration $\{\mathcal{F}_i\}_i$, and let $A_i, B_i \in \mathcal{F}_{i-1}$ satisfy $A_i \leq \Delta_i \leq B_i$ almost surely for every i. Then
$$\mathbb{P}\left[\frac{1}{n}\sum_{i}\Delta_{i} > t\right] \leq \exp\left(-\frac{2n^{2}t^{2}}{\sum_{i=1}^{n}\|B_{i} - A_{i}\|_{\infty}^{2}}\right).$$

## Statement 8: Theorem (Bounded Differences Inequality / McDiarmid's Inequality)
If $g: \mathcal{X} \to \mathbb{R}$ satisfies the bounded differences condition with constants $c_i$, then
$$\mathbb{P}\left[|g(X_1,\ldots,X_n) - \mathbb{E}[g(X_1,\ldots,X_n)]| > t\right] \le 2\exp\left(-\frac{2t^2}{\sum_i c_i^2}\right).$$

## Statement 9: Theorem (Bernstein's Inequality)
Let $X_1, \ldots, X_n$ be independent, centered random variables with $|X_i| \leq c$ for every i, and write $\sigma^2 = n^{-1} \sum_i \text{Var}(X_i)$ for the average variance. Then
$$\mathbb{P}\left[\frac{1}{n}\sum_{i}X_{i} > t\right] \leq \exp\left(-\frac{nt^{2}}{2\sigma^{2} + \frac{2}{3}tc}\right).$$

## Statement 10: Theorem (Fast Rate under Massart's Noise Condition)
Let $\mathcal{E}(\hat{h})$ denote the excess risk of the empirical risk minimizer $\hat{h} = \hat{h}^{\text{erm}}$. If Massart's noise condition is satisfied with constant $\gamma$, then
$$\mathcal{E}(\hat{h}) \le \frac{\log(M/\delta)}{\gamma n}$$
with probability at least $1 - \delta$.

## Statement 11: Theorem (Fast Rate under Tsybakov's Noise Condition)
Let $\mathcal{H}$ be a finite class of cardinality $M$ such that $h^* \in \mathcal{H}$. If Tsybakov's noise condition is satisfied with exponent $\kappa \geq 1$, then with probability at least $1 - \delta$,
$$\mathcal{E}(\hat{h}) \le C_{\kappa}\left(\frac{\log(M/\delta)}{n}\right)^{\kappa/(2\kappa-1)}.$$

## Statement 12: Theorem (Symmetrization / Rademacher Complexity Bound)
Let $\mathcal{H}$ be a class of classifiers and $\hat{h} = \hat{h}^{\text{erm}}$. Then
$$\mathbb{E}[\mathcal{E}(\hat{h})] \le 2\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^n \varepsilon_i \ell(h, Z_i)\right]$$
where $\varepsilon_1, \ldots, \varepsilon_n$ are independent Rademacher random variables.

## Statement 13: Lemma (Symmetrization Lemma)
$$\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^{n}(P - P_n)f_h\right] \le 2\mathbb{E}\left[\sup_{h \in \mathcal{H}} \frac{1}{n}\sum_{i=1}^{n}\varepsilon_i f_h(Z_i)\right]$$
where $\varepsilon_1, \ldots, \varepsilon_n$ are i.i.d. Rademacher random variables.

## Statement 14: Lemma (Contraction Lemma / Ledoux-Talagrand)
If $\phi: \mathbb{R} \to \mathbb{R}$ is L-Lipschitz with $\phi(0) = 0$, then
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}}\sum_{i=1}^{n}\varepsilon_i\phi(f(Z_i))\right] \le L\mathbb{E}\left[\sup_{f \in \mathcal{F}}\sum_{i=1}^{n}\varepsilon_i f(Z_i)\right].$$

## Statement 15: Theorem (Massart's Finite Lemma)
Let $x_1, \ldots, x_N \in \mathbb{R}^n$ with $\max_j \|x_j\| \leq r$. Then
$$\mathbb{E}\left[\max_{1 \le j \le N} \sum_{i=1}^{n} \varepsilon_i x_{ij}\right] \le r\sqrt{2\log N}.$$

## Statement 16: Theorem (Dudley's Entropy Integral / Chaining Bound)
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}} \frac{1}{n}\sum_{i=1}^n \varepsilon_i f(Z_i)\right] \le \frac{c}{n}\int_0^{\text{diam}(\mathcal{F})} \sqrt{\log N(\mathcal{F}, \|\cdot\|_n, \varepsilon)}\, d\varepsilon$$
where $N(\mathcal{F}, \|\cdot\|_n, \varepsilon)$ is the covering number of $\mathcal{F}$ w.r.t. the empirical $L^2$ norm at scale $\varepsilon$.

## Statement 17: Lemma (Sauer-Shelah Lemma / Sauer's Lemma)
If the VC-dimension of $\mathcal{H}$ is $V$, then for all $n \geq V$,
$$\sup_{z_1,\ldots,z_n} |\{(h(z_1),\ldots,h(z_n)) : h \in \mathcal{H}\}| \le \sum_{k=0}^{V} \binom{n}{k} \le \left(\frac{en}{V}\right)^V.$$

## Statement 18: Theorem (VC Dimension Bound on Excess Risk)
If the VC-dimension of $\mathcal{H}$ is $V < \infty$, then
$$\mathbb{E}[\mathcal{E}(\hat{h})] \le C\sqrt{\frac{V\log(n/V)}{n}}.$$

## Statement 19: Theorem (Lower Bound via VC Dimension)
For any $V \geq 1$ and $n \geq V$, there exists a class $\mathcal{H}$ of VC-dimension $V$ and a distribution $P_{X,Y}$ with $h^* \in \mathcal{H}$ such that for any classifier $\hat{h}$ built from $n$ observations,
$$\mathbb{E}[\mathcal{E}(\hat{h})] \geq c\sqrt{\frac{V}{n}}.$$

## Statement 20: Theorem (Convex Risk Bound via Rademacher Complexity)
For convex surrogate $\phi$-risk minimization over a class $\mathcal{F}$ with $\|f\|_\infty \leq 1$ for all $f \in \mathcal{F}$, if $\phi$ is L-Lipschitz, then
$$\mathbb{E}\left[\sup_{f \in \mathcal{F}} |R_{n,\phi}(f) - R_\phi(f)|\right] \le 2L \cdot \mathfrak{R}_n(\mathcal{F})$$
where $\mathfrak{R}_n(\mathcal{F})$ is the Rademacher complexity of $\mathcal{F}$.

## Statement 21: Theorem (Representer Theorem)
Consider the minimization of $\hat{R}_{n,\phi}(f) + \lambda\|f\|_{\mathcal{H}_K}^2$ over a reproducing kernel Hilbert space $\mathcal{H}_K$. Then the minimizer has the form
$$\hat{f}(\cdot) = \sum_{i=1}^n \alpha_i K(X_i, \cdot)$$
for some $\alpha_1, \ldots, \alpha_n \in \mathbb{R}$.

## Statement 22: Theorem (Projected Gradient Descent Convergence)
Let $f$ be a convex function on a closed convex set $\mathcal{C} \subset \mathbb{R}^d$ with $\text{diam}(\mathcal{C}) \leq R$ and $\|g\| \leq L$ for all $g \in \partial f(x)$, $x \in \mathcal{C}$. Then projected gradient descent with step size $\eta = \frac{R}{L\sqrt{k}}$ satisfies
$$f(\bar{x}_k) - f(x^*) \le \frac{LR}{\sqrt{k}}.$$

## Statement 23: Theorem (Mirror Descent Convergence)
Assume that $\Phi$ is $\alpha$-strongly convex on $\mathcal{C} \cap \mathcal{D}$ w.r.t. $\|\cdot\|$ and $R^{2} = \sup_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x) - \min_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x)$. Then, Mirror Descent with $\eta = \frac{R}{L}\sqrt{\frac{2\alpha}{k}}$ gives
$$f(\bar{x}_k) - f(x^*) \le RL\sqrt{\frac{2}{\alpha k}}.$$

## Statement 24: Corollary (Mirror Descent on the Simplex)
Let f be a convex function on $\Delta_d$ such that $\|g\|_{\infty} \le L$ for all $g \in \partial f(x)$, $x \in \Delta_d$. Then, Mirror descent with $\eta = \frac{1}{L} \sqrt{\frac{2 \log(d)}{k}}$ gives
$$f(\overline{x}_k) - f(x^*) \le L\sqrt{\frac{2\log(d)}{k}}.$$

## Statement 25: Theorem (Stochastic Gradient Descent Convergence)
Let $\mathcal{C}$ be a closed convex subset of $\mathbb{R}^d$ such that $\operatorname{diam}(\mathcal{C}) \leq R$. Assume that the convex function $f(x) = \mathbb{E}[\ell(x,Z)]$ attains its minimum on $\mathcal{C}$ at $x^* \in \mathbb{R}^d$. Assume that $\ell(x,Z)$ is convex $P_Z$ a.s. and that $\mathbb{E}\|\tilde{g}\|^2 \leq L^2$ for all $\tilde{g} \in \partial \ell(x,Z)$ for all x. Then if $\eta_s \equiv \eta = \frac{R}{L\sqrt{k}}$,
$$\mathbb{E}[f(\bar{x}_k)] - f(x^*) \le \frac{LR}{\sqrt{k}}.$$

## Statement 26: Theorem (Stochastic Mirror Descent Convergence)
Assume that $\Phi$ is $\alpha$-strongly convex on $\mathcal{C} \cap \mathcal{D}$ w.r.t. $\|\cdot\|$ and $R^{2} = \sup_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x) - \min_{x \in \mathcal{C} \cap \mathcal{D}} \Phi(x)$. Then, Stochastic Mirror Descent with $\eta = \frac{R}{L}\sqrt{\frac{2\alpha}{k}}$ outputs $\bar{x}_k$ such that
$$\mathbb{E}[f(\bar{x}_k)] - f(x^*) \le RL\sqrt{\frac{2}{\alpha k}}.$$

## Statement 27: Theorem (Exponential Weights Regret Bound)
Assume $\ell(\cdot, z)$ is convex for all $z \in \mathcal{Z}$ and that $\ell(p, z) \in [0, 1]$ for all $p \in \Delta^K, z \in \mathcal{Z}$. Then the EW strategy has regret
$$R_n \le \frac{\log K}{\eta} + \frac{\eta n}{2}.$$
In particular, for $\eta = \sqrt{\frac{2 \log K}{n}}$,
$$R_n \le \sqrt{2n\log K}.$$

## Statement 28: Theorem (FPL Regret Bound)
FPL with $\eta = \frac{1}{\sqrt{Kn}}$ yields expected regret:
$$\mathbb{E}_{\xi}[R_n] \le 2\sqrt{2nK}.$$

## Statement 29: Lemma (Be-The-Leader Lemma)
For all loss function $\ell(p, z)$, let $p_t^* = \arg\min_{p \in \Delta^K} \sum_{s=1}^t \ell(p, z_s)$. Then we have
$$\sum_{t=1}^{n} \ell(p_t^*, z_t) \le \sum_{t=1}^{n} \ell(p_n^*, z_t).$$

## Statement 30: Theorem (UCB Regret Bound)
The UCB policy has regret
$$R_n \le 8 \sum_{k,\Delta_k > 0} \frac{\log n}{\Delta_k} + (1 + \frac{\pi^2}{3}) \sum_{k=1}^K \Delta_k.$$

## Statement 31: Theorem (Bounded Regret Policy)
BRP has regret
$$R_n \le \Delta + \frac{16}{\Delta}.$$

## Statement 32: Lemma (Prediction with Individual Sequences)
For a stable $\phi$, the following are equivalent:
a) $\exists (\hat{q}_t)_{t=1,\dots,n} \forall y_1,\dots,y_n \quad \mathbb{E}\left[\frac{1}{n} \sum_{t=1}^n \mathbb{1}\{\hat{y}_t \neq y_t\}\right] \leq \phi(y_1,\dots,y_n)$
b) $\mathbb{E}[\phi(\epsilon_1,\ldots,\epsilon_n)] \geq \frac{1}{2}$ where $\epsilon_1,\ldots,\epsilon_n$ are Rademacher random variables.

## Statement 33: Lemma (Unbiased Estimator for Bandit Feedback)
$\hat{l}(e_i, z_t) = \frac{l(e_j, z_t) \mathbb{I}(a_t = e_j)}{P(a_t = e_j)}$ is an unbiased estimator of $l(e_i, z_t)$.

## Statement 34: Theorem (Geometric Hedge Regret Bound for Linear Bandits)
Using Geometric Hedge algorithm for linear bandit with bandit feedback, with $\gamma = \frac{1}{n^{1/3}}$ and $\eta = \sqrt{\frac{\log n}{kn^{4/3}}}$, we have
$$\mathbb{E}[R_n] \le C n^{2/3} \sqrt{\log n} \, k^{3/2}.$$

## Statement 35: Theorem (Improved Linear Bandit Regret via Design Matrix)
Let $C_t = \mathbb{E}_{a_t \sim q_t}[a_t a_t^T]$, $\hat{z}_t = (a_t^T z_t) C_t^{-1} a_t$, and $\gamma = 0$ (so that $p_t = q_t$). Using Geometric Hedge algorithm with $\eta = 2\sqrt{\frac{\log n}{n}}$ for linear bandit with bandit feedback leads to
$$\mathbb{E}[R_n] \le CK\sqrt{n\log n}.$$

## Statement 36: Theorem (Von Neumann Minimax Theorem)
$$\max_{p \in \Delta_n} \min_{q \in \Delta_m} p^\top M q = \min_{q \in \Delta_m} \max_{p \in \Delta_n} p^\top M q.$$

## Statement 37: Theorem (Sion's Minimax Theorem)
Let A and Z be convex, compact spaces, and $f: A \times Z \to \mathbb{R}$. If $f(a, \cdot)$ is upper semicontinuous and quasiconcave on $Z$ for all $a \in A$ and $f(\cdot,z)$ is lower semicontinuous and quasiconvex on $A$ for all $z \in Z$, then
$$\inf_{a \in A} \sup_{z \in Z} f(a, z) = \sup_{z \in Z} \inf_{a \in A} f(a, z).$$

## Statement 38: Theorem (Blackwell's Approachability Theorem)
Let S be a closed convex set of $\mathbb{R}^d$ with $\|x\| \leq R$ for all $x \in S$. If for all $z$, there exists $a$ such that $\ell(a, z) \in S$, then S is approachable. Moreover, there exists a strategy such that
$$d(\bar{\ell}_n, S) \le \frac{2R}{\sqrt{n}}.$$

## Statement 39: Theorem (Potential-Based Approachability Rate)
If $\|\ell(a,z)\| \leq R$ holds for all $a \in \mathcal{A}, z \in \mathcal{Z}$ and all assumptions on the potential $\Phi$ are satisfied, then
$$\Phi(\bar{\ell}_n) \le \frac{4R^2h\log n}{n}.$$

## Statement 40: Lemma (Separating Hyperplane from Potential)
For any convex, closed set S and $z \in S$, $x \in S^C$, the following properties hold:
- $\langle z - \pi(x), \nabla \Phi(x) \rangle \leq 0$,
- $\langle x - \pi(x), \nabla \Phi(x) \rangle \ge \Phi(x)$.
In particular, if $\Phi$ is positive on $S^C$, then $H:=\{y\mid \langle y-\pi(x),\nabla\Phi(x)\rangle=0\}$ is a separating hyperplane.

## Statement 41: Proposition (Bregman Projection Inequality)
For all $z \in S$, it holds
$$\langle \nabla \Phi(\pi(x)) - \nabla \Phi(x), \pi(x) - z \rangle \le 0.$$

## Statement 42: Theorem (Minimax Regret for Combinatorial Bandits)
Let $n \geq d^2$. In the full information and semi-bandit games, we have
$$0.008 \, d\sqrt{n} \leq \overline{R}_n \leq d\sqrt{2n},$$
and in the bandit game,
$$0.01 \, d^{3/2}\sqrt{n} \le \overline{R}_n \le 2 \, d^{5/2}\sqrt{2n}.$$
