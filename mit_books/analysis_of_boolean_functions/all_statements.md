# All Statements: Analysis of Boolean Functions (18.218, Spring 2021)

## Statement 1: Claim 2.1
The collection $\{\chi_S\}_{S\subseteq[n]}$ forms an orthonormal set (In particular, it is a linearly independent set), where $\chi_S(x) = \prod_{i \in S} x_i$ for $S \subseteq [n]$ and $x \in \{-1,1\}^n$.

## Statement 2: Claim 2.2
The following holds for any $f, g: \{-1, 1\}^n \to \mathbb{R}$:
1. Plancherel's equality: $\langle f, g \rangle = \sum_{S \subseteq [n]} \widehat{f}(S) \widehat{g}(S)$.
2. Parseval's equality: $\|f\|_2^2 = \sum_{S \subset [n]} \widehat{f}(S)^2$.

## Statement 3: Claim 2.3
$\operatorname{var}(f) = \sum_{S \neq \emptyset} \widehat{f}(S)^2$.

## Statement 4: Claim 1.1 (Lecture 2)
For all $S \subseteq [n]$ it holds that $\widehat{f * g}(S) = \widehat{f}(S)\widehat{g}(S)$, where $(f * g)(x) = \mathbb{E}_{y} [f(y)g(xy)]$.

## Statement 5: Theorem 1.2 (BLR Linearity Test)
Suppose $f: \{-1,1\}^n \to \{-1,1\}$ is a function such that $\Pr_{x,y} [f(x)f(y) = f(xy)] \geqslant \frac{1}{2} + \delta$. Then there exists $S \subseteq [n]$ such that $\widehat{f}(S) \geqslant 2\delta$.

## Statement 6: Remark 1.3
Those familiar with Roth's theorem regarding the appearance of 3-term arithmetic progressions in dense subsets of $[N]$ may notice the similarity between the arguments.

## Statement 7: Definition 2.1 (Random Restrictions)
Suppose we have a function $f: \{-1,1\}^n \to \mathbb{R}$, a set of coordinates $J \subseteq [n]$ and an assignment $z \in \{-1,1\}^{\bar{J}}$. The restricted function $f_{\bar{J}\to z}: \{-1,1\}^J \to \mathbb{R}$ is defined by $f_{\bar{J}\to z}(y) = f(x_{\bar{J}} = z, x_J = y)$.

## Statement 8: Definition 2.2 (Random Restriction)
Given $f: \{-1,1\}^n \to \mathbb{R}$ and $J \subseteq [n]$, a random restriction of $f$ on $J$ is a function $f_{\bar{J}\to z}$ wherein $z \in \{-1,1\}^{\bar{J}}$ is sampled uniformly at random.

## Statement 9: Claim 2.3 (Lecture 2)
Let $f: \{-1,1\}^n \to \mathbb{R}$, $J \subseteq [n]$, $z \in \{-1,1\}^{\overline{J}}$ and $S \subseteq J$. We have $\widehat{f_{\bar{J}\to z}}(S) = \sum_{T\subseteq \bar{J}} \widehat{f}(S\cup T)\chi_T(z)$.

## Statement 10: Claim 2.4
Let $f: \{-1,1\}^n \to \mathbb{R}$, $J \subseteq [n]$ and $S \subseteq J$. We have $\mathbb{E}_{z}\left[\widehat{f_{\bar{J}\to z}}(S)^{2}\right] = \sum_{T\subseteq \bar{J}}\widehat{f}(S\cup T)^{2}$.

## Statement 11: Definition 2.5 (p-random restriction)
Given a function $f: \{-1,1\}^n \to \mathbb{R}$ and a parameter $p \in [0,1]$, a p-random restriction is sampled by: taking $J \subseteq [n]$ randomly by including each $i \in [n]$ in $J$ with probability $p$, and then taking $z \in \{-1,1\}^{\overline{J}}$.

## Statement 12: Definition 2.6 (Fourier weight)
Let $f: \{-1,1\}^n \to \mathbb{R}$ be a function, and $d \in \mathbb{N}$. The level $d$ Fourier weight of a function $f$ is defined as $W^{=d}[f] = \sum_{|S|=d} \widehat{f}(S)^2$. We also define $W^{\leqslant d}[f] = \sum_{i \leqslant d} W^{=i}[f]$ and $W^{\geqslant d}[f] = \sum_{i \geqslant d} W^{=i}[f]$.

## Statement 13: Claim 2.7
Let $f: \{-1,1\}^n \to \mathbb{R}$, $d \in \mathbb{N}$, and let $(J,z)$ be a p-random restriction. Then $\mathbb{E}_{J,z}\left[W^{=d}[f_{\bar{J}\to z}]\right] = \sum_{Q}\widehat{f}(Q)^{2}\Pr\left[\operatorname{Bin}(|Q|,p) = d\right]$.

## Statement 14: Corollary 2.8
Suppose that $f: \{-1,1\}^n \to \{-1,1\}$ satisfies $W_{\geqslant d}[f] \leqslant \varepsilon$, and let $(J,z)$ be a p-random restriction. Then $\mathbb{E}_{J,z}\left[W^{\geqslant 2pd}[f_{\bar{J}\to z}]\right]\leqslant \varepsilon + \exp(-\Theta(pd))$.

## Statement 15: Definition 2.9
We define the weight around level $d$ to be $W^{\approx d}[f] = \sum_{d \leqslant k \leqslant 2d} W^{=k}[f]$.

## Statement 16: Corollary 2.10
Let $d \in \mathbb{N}$ and $p \in [0,1]$ be such that $pd \geqslant 10$. Suppose that $f: \{-1,1\}^n \to \{-1,1\}$ satisfies $W_{\geqslant d}[f] \leqslant \varepsilon$, and let $(J,z)$ be a p-random restriction. Then $\mathbb{E}_{J,z}\left[W^{\approx pd}[f_{\bar{J}\to z}]\right]\geqslant \Omega(W^{\approx d}[f])$.

## Statement 17: Fact 1.1 (Chernoff-Hoeffding bound)
Suppose $Y_1, \ldots, Y_n$ are independent random variables such that $|Y_i| \le 1$ almost surely. Then for every $\varepsilon > 0$, $\Pr\left[\sum_{i=1}^{n} Y_i - \sum_{i=1}^{n} \mathbb{E}[Y_i] \geqslant \varepsilon n\right] \leqslant 2e^{-\frac{\varepsilon^2}{2+\varepsilon}n}$.

## Statement 18: Claim 1.2 (Lecture 3)
For all $\varepsilon, \delta > 0$, there is $q = O\left(\frac{\log(1/\delta)}{\varepsilon^2}\right)$ and an algorithm such that given random input-output pairs of $f: \{-1,1\}^n \to [-1,1]$ and a character $S \subseteq [n]$, the algorithm produces an estimate $a_S$ of $\widehat{f}(S)$ such that $\Pr\left[|\widehat{f}(S) - a_S| \geqslant \varepsilon\right] \leqslant \delta$.

## Statement 19: Claim 2.1 (Lecture 3)
For all $\varepsilon, \delta > 0$, there is $q = O\left(\frac{\log(1/\delta)}{\varepsilon^2}\right)$ and an algorithm performing the following task. Given membership queries to $f: \{-1,1\}^n \to [-1,1]$, and sets $T \subseteq J \subseteq [n]$, the algorithm outputs a number $b_{T,J}$ such that $\Pr\left[ b_{T,J} - \sum_{S: S \cap J = T} \widehat{f}(S)^2 \geqslant \varepsilon \right] \leqslant \delta$.

## Statement 20: Theorem 3.1 (Learning sparse functions)
For all $t, \varepsilon, \delta > 0$ there exists an algorithm whose runtime is $\operatorname{poly}(n, t, 1/\varepsilon, 1/\delta)$ such that given oracle access to a $(t, \varepsilon)$-sparse function $f: \{-1,1\}^n \to \{-1,1\}$, the algorithm produces a hypothesis $H: \{-1,1\}^n \to \{-1,1\}$ such that $\|f - H\|_2^2 \le 4\varepsilon + \delta$.

## Statement 21: Remark 3.2
This algorithm (Goldreich-Levin hardcore bit) has its origin from the field of cryptography.

## Statement 22: Definition 1.1 (Influence)
For a function $f: \{-1,1\}^n \to \{0,1\}$ and a coordinate $i \in [n]$, the influence of $i$ is defined as $I_i[f] = \Pr_{x \in \{-1,1\}^n} [f(x) \neq f(x^{\oplus i})]$.

## Statement 23: Definition 1.2 (Total Influence)
For a function $f: \{-1,1\}^n \to \{0,1\}$, the total influence of $f$ is defined as $I[f] = \sum_{i=1}^{n} I_i[f]$.

## Statement 24: Definition 2.1 (Discrete derivatives)
Given a function $f: \{-1,1\}^n \to \mathbb{R}$ and $i \in [n]$, the discrete derivative of $f$ along $i$ is $\partial_i f(y) = \frac{1}{2} (f(x_i = 1, x_{-i} = y) - f(x_i = -1, x_{-i} = y))$.

## Statement 25: Definition 2.2 (L^2 influence)
Given a function $f: \{-1,1\}^n \to \mathbb{R}$ and $i \in [n]$, the $L^2$ influence of $i$ on $f$ is $I_i[f] = \|\partial_i f\|_2^2$. The total $L^2$ influence of $f$ is $I[f] = \sum_{i=1}^n I_i[f]$.

## Statement 26: Claim 3.1 (Total influence = average sensitivity)
If $f: \{-1,1\}^n \to \{-1,1\}$, then $I[f] = \mathbb{E}_x[s_f(x)]$, where $s_f(x)$ is the number of edges adjacent to $x$ that cross the bi-partition.

## Statement 27: Lemma 4.1 (Russo-Margulis)
Let $f: \{0,1\}^n \to \{0,1\}$ be a monotone function. Then $\frac{d}{dp}\mu_p(f) = I[f; \mu_p^{\otimes n}]$.

## Statement 28: Remark 4.2
There are arguably simpler proofs in the literature, but we give this one since it nicely highlights the intuition.

## Statement 29: Claim 5.1 (Fourier formula for derivative)
For a function $f: \{-1,1\}^n \to \mathbb{R}$ and $i \in [n]$, we have $\partial_i f(y) = \sum_{S \ni i} \widehat{f}(S) \chi_{S \setminus \{i\}}(y)$.

## Statement 30: Corollary 5.2
$I_i[f] = \sum_{S \ni i} \widehat{f}(S)^2$.

## Statement 31: Corollary 5.3
$I[f] = \sum_{S} |S| \widehat{f}(S)^2$.

## Statement 32: Corollary 5.4 (Poincare inequality)
For any $f: \{-1,1\}^n \to \mathbb{R}$ we have that $I[f] \geqslant \operatorname{var}(f)$.

## Statement 33: Theorem 5.5 (KKL theorem)
There is an absolute constant $c>0$, such that for any $f:\{-1,1\}^n \to \{-1,1\}$, there is $i\in[n]$ such that $I_i[f]\geqslant c\frac{\log n}{n}\operatorname{var}(f)$.

## Statement 34: Definition 0.1 (L^p norm)
For any $p \ge 1$ we define the $L^p$ norm of $f: \{-1,1\}^n \to \mathbb{R}$ as $\|f\|_p = \left( \mathbb{E}_{x \sim \{-1,1\}^n} [|f(x)|^p] \right)^{1/p}$.

## Statement 35: Lemma 1.1 (Degree 1 hypercontractivity)
If $f: \{-1,1\}^n \to \mathbb{R}$ has degree 1, then $\|f\|_4 \leqslant \sqrt{3}\|f\|_2$. More generally, for any $q \geqslant 2$, $\|f\|_q \leqslant \sqrt{q-1}\|f\|_2$.

## Statement 36: Theorem 2.1 (Hypercontractive inequality, low-degree formulation)
If $f: \{-1,1\}^n \to \mathbb{R}$ has degree $d$, and $q \ge 2$ then $\|f\|_q \le \sqrt{q-1}^d \|f\|_2$.

## Statement 37: Definition 2.2 (Noise operator)
Let $x \in \{-1,1\}^n$, and let $\rho \in [0,1]$. The distribution of $\rho$-correlated inputs with $x$, denoted as $y \sim T_{\rho}x$, is defined as: for each $i \in [n]$ independently, set $y_i = x_i$ with probability $\rho$, and otherwise resample $y_i$ uniformly.

## Statement 38: Theorem 2.3 (The hypercontractive inequality, noise operator formulation)
For all $f: \{-1,1\}^n \to \mathbb{R}$, $1 \le p \le q$ and $0 \le \rho \le \sqrt{\frac{p-1}{q-1}}$ it holds that $\|T_{\rho}f\|_q \le \|f\|_p$.

## Statement 39: Claim 2.4 (Effect of noise operator on Fourier coefficients)
For all $f: \{-1,1\}^n \to \mathbb{R}$ and $\rho \in [0,1]$ we have that $T_{\rho}f(x) = \sum_{S \subseteq [n]} \rho^{|S|} \widehat{f}(S) \chi_S(x)$.

## Statement 40: Definition 3.1 (Noisy hypercube)
For $\rho \in [0,1]$, the $\rho$-noisy hypercube graph is the graph on the vertex set $\{-1,1\}^n$, whose edges are sampled according to the $T_\rho$ process.

## Statement 41: Definition 3.2 (Edge expansion)
Let $G = (V, E, w)$ be a weighted regular graph, and let $S \subseteq V$ be a vertex set. The expansion of $S$ is $\Phi_G(S) = \Pr_{x \in S, y \sim_w N(x)} [y \notin S]$.

## Statement 42: Definition 3.3 (Small set expander)
A graph $G = (V, E, w)$ is called an $(\varepsilon, \delta)$-small set expander if for any $S \subseteq V$ of size at most $\delta n$, it holds that $\Phi_G(S) \geqslant 1 - \varepsilon$.

## Statement 43: Claim 3.4 (Noisy hypercube is small-set expander)
For $\rho = \frac{1}{\sqrt{3}}$, the noisy hypercube graph is a small-set expander.

## Statement 44: Remark 3.5
There is nothing special about $\rho = 1/\sqrt{3}$, and the noisy hypercube is a small-set expander for any $\rho$ bounded away from 1.

## Statement 45: Theorem 3.6 (Concentration for low-degree functions)
Suppose $f: \{-1,1\}^n \to \mathbb{R}$ is a function of degree at most $d$, and let $t \geqslant 2^d$. Then $\Pr_{x}[|f(x)| \ge t\|f\|_2] \le e^{-\frac{t^{2/d}}{2}}$.

## Statement 46: Remark 3.7
The exponent $t^{2/d}$ is tight.

## Statement 47: Theorem 3.8 (Anti-concentration for low-degree functions)
Suppose $f: \{-1,1\}^n \to \mathbb{R}$ is a function of degree at most $d$, and let $0 < \theta < 1$. Then $\Pr_{x} [|f(x)| \ge \theta \|f\|_2] \ge \frac{(1 - \theta^2)^2}{9^d}$.

## Statement 48: Lemma 3.9 (1-norm trick)
Let $f: \{-1,1\}^n \to \mathbb{R}$ be a function of degree at most $d$. Then $\|f\|_2 \leqslant 3^d \|f\|_1$.

## Statement 49: Theorem 1.1 (FKN theorem)
Suppose a function $f: \{-1,1\}^n \to \{-1,1\}$ is $\varepsilon$-close to a degree 1 function in $\ell_2^2$, i.e. $\|f-f^{=1}\|_2^2 \leqslant \varepsilon$. Then, there exists $b_i \in \{-1,1\}$ and $i \in [n]$ such that $\|f-b_ix_i\|_2 = O(\varepsilon)$.

## Statement 50: Remark 1.2
An interesting question which is not fully understood asks for extensions of the FKN theorem to degree $d$ functions.

## Statement 51: Claim 2.1 (Lecture 6, degree of indicator of small set)
$\deg(1_S) \geqslant \Omega(\log(1/\delta))$ for $S \subseteq \{-1,1\}^n$ with $|S| = \delta 2^n$.

## Statement 52: Lemma 2.2 (Fourier spectrum of small sets)
Let $f: \{-1,1\}^n \to \{-1,0,1\}$ be a function such that $0 < \Pr_x [f(x) \neq 0] \leqslant \delta$. Then $\sum_{|S| \leqslant \frac{1}{20} \log(1/\delta)} \widehat{f}(S)^2 \leqslant \delta^{24/20}$.

## Statement 53: Remark 2.3
With a bit more effort, one may even show a bound of the form $\delta^2 \log^d(1/\delta)$.

## Statement 54: Theorem 3.1 (Lecture 6, KKL theorem restated)
Let $f: \{-1,1\}^n \to \{-1,1\}$ be such that $I[f] \leqslant K \operatorname{var}(f)$. Then there exists $i \in [n]$ such that $I_i[f] \geqslant e^{-O(K)}$.

## Statement 55: Corollary 3.2 (KKL standard formulation)
For any $f: \{-1,1\}^n \to \{-1,1\}$, there is $i \in [n]$ such that $I_i[f] \geqslant \Omega\left(\frac{\log n}{n} \operatorname{var}(f)\right)$.

## Statement 56: Claim 4.1 (Tribes function)
There exists $f: \{0,1\}^n \to \{0,1\}$ with $\operatorname{var}(f) \geqslant \Omega(1)$ and $I_i[f] = O(\log n/n)$ for all $i \in [n]$.

## Statement 57: Theorem 0.1 (KKL restated, Lecture 7)
Let $f: \{-1,1\}^n \to \{-1,1\}$ be a function such that $I[f] \leqslant K \cdot \operatorname{var}(f)$. Then there is an $i \in [n]$ such that $I_i[f] \geqslant e^{-O(K)}$.

## Statement 58: Theorem 1.1 (Talagrand's version of KKL)
There exists an absolute constant $C > 0$, such that for any $f : \{-1, 1\}^n \to \{-1, 1\}$ it holds that $C\sum_{i=1}^{n} \frac{I_i[f]}{\log(1/I_i[f])} \geqslant \operatorname{var}(f)$.

## Statement 59: Theorem 2.1 (Friedgut junta theorem)
Let $f: \{-1,1\}^n \to \{-1,1\}$. Then for every $\varepsilon > 0$, there exists $J \subseteq [n]$ of size at most $2^{O\left(\frac{I[f]}{\varepsilon\operatorname{var}(f)}\right)}$ and a $J$-junta $g: \{-1,1\}^n \to \{-1,1\}$ such that $\|f-g\|_2 \leqslant \varepsilon$.

## Statement 60: Theorem 3.1 (Edge isoperimetric inequality)
For all $f: \{-1,1\}^n \to \{-1,1\}$ it holds that $I[f] \geqslant \Pr[f(x) = -1] \log \left(\frac{1}{\Pr[f(x) = -1]}\right)$.

## Statement 61: Theorem 3.2 (Margulis)
For all $f: \{-1,1\}^n \to \{-1,1\}$, $\mu(V - \operatorname{boundary}(S))I[f] \geqslant \Omega(\operatorname{var}(f)^2)$.

## Statement 62: Theorem 3.3 (Talagrand)
For all $f: \{-1,1\}^n \to \{-1,1\}$, $\mathbb{E}_{x}\left[\sqrt{s_f(x)}\right]\geqslant \Omega(\operatorname{var}(f))$.

## Statement 63: Theorem 3.4 (Talagrand, stronger)
For all $f: \{-1, 1\}^n \to \{-1, 1\}$, $\mathbb{E}_{x}\left[\sqrt{s_{f}(x)}\right] \geqslant \Omega\left(\operatorname{var}(f)\sqrt{\log\left(\frac{1}{\operatorname{var}(f)}\right)}\right)$.

## Statement 64: Theorem 3.5 (Talagrand, combined)
There exists $0 < \alpha < 1/2$ such that for all $f: \{-1,1\}^n \to \{-1,1\}$, $\mathbb{E}_{x}\left[\sqrt{s_f(x)}\right] \geqslant \Omega\left(\operatorname{var}(f)\log^{1/2-\alpha}\left(\frac{1}{\operatorname{var}(f)}\right)\log^{\alpha}\left(\frac{1}{M(f)}\right)\right)$.

## Statement 65: Definition 1.1 (Noise Stability)
Let $f: \{-1,1\}^n \to \mathbb{R}$, and $\rho \in [0,1]$. The stability of $f$ with parameter $\rho$ is $\operatorname{Stab}_{\rho}(f) = \langle f, T_{\rho} f \rangle$.

## Statement 66: Theorem 1.2 (Majority is stablest)
For all $\rho > 0$, $\delta > 0$ there is $\tau > 0$ such that if $f: \{-1,1\}^n \to \{-1,1\}$ is balanced, and $I_i[f] \leqslant \tau$ for all $i \in [n]$, then $\operatorname{Stab}_{\rho}(f) \leqslant \operatorname{Stab}_{\rho}(\operatorname{Majority}) + \delta$.

## Statement 67: Claim 1.3 (Fourier formula for stability)
Let $f: \{-1,1\}^n \to \mathbb{R}$, $\rho \in [0,1]$. Then $\operatorname{Stab}_{\rho}(f) = \sum_{S} \rho^{|S|} \widehat{f}(S)^2$.

## Statement 68: Theorem 1.4 (Sheppard's Formula)
$\operatorname{Stab}_{\rho}(\operatorname{Majority}_n) = 1 - \frac{2}{\pi}\operatorname{arccos}(\rho) + o(1)$.

## Statement 69: Theorem 2.1 (Arrow's impossibility theorem)
Suppose $f: \{-1,1\}^n \to \{-1,1\}$ is an unanimous voting rule such that $f(\vec{1}) = 1$, $f(-\vec{1}) = -1$. If in 3-candidate election $f$ always has a Condorcet winner, then $f$ is a dictatorship.

## Statement 70: Claim 2.2 (Fourier expansion of NAE_3)
$\operatorname{NAE}_3(a, b, c) = \frac{3}{4} - \frac{1}{4}(ab + bc + ac)$.

## Statement 71: Definition 2.3 (Negative correlation)
Let $-1 \le \rho < 0$. The distribution of $\rho$-correlated inputs is the joint distribution of $(a,b) \in \{-1,1\}^2$ such that marginally each one is uniformly distributed and $\mathbb{E}[ab] = \rho$.

## Statement 72: Theorem 2.4 (Robust Arrow's theorem)
Suppose $f: \{-1,1\}^n \to \{-1,1\}$ is a voting rule such that the probability of reaching a Condorcet paradox is at most $\varepsilon$. Then, $f$ is $\varepsilon$-close to a dictatorship or an anti-dictatorship.

## Statement 73: Definition 3.1 (Noise Sensitivity)
Let $f: \{-1,1\}^n \to \mathbb{R}$, and $\varepsilon > 0$. The noise sensitivity of $f$ is $\operatorname{NS}_{\varepsilon}(f) = \frac{1}{2} - \frac{1}{2}\operatorname{Stab}_{1-2\varepsilon}(f)$.

## Statement 74: Claim 3.2 (Fourier formula for noise sensitivity)
Let $f: \{-1,1\}^n \to \mathbb{R}$. Then $\operatorname{NS}_{\varepsilon}(f) = \frac{1}{2} \sum_{S} (1 - (1-2\varepsilon)^{|S|}) \widehat{f}(S)^2$.

## Statement 75: Theorem 4.1 (BKS level-k inequality)
There exists an absolute constant $C > 0$, such that for all $k \in \mathbb{N}$, $W^{=k}[f] \leqslant \left(\frac{C}{k}\right)^k M(f) \log\left(\frac{k}{M(f)}\right)^{k-1}$.

## Statement 76: Corollary 4.2
There exists an absolute constant $c > 0$, such that for all $k \le c \log(1/M(f))$ we have $W^{=k}[f] \leqslant \sqrt{M(f)}$.

## Statement 77: Corollary 4.3
There exists an absolute constant $\alpha > 0$ such that for all $\varepsilon > 0$ and $f: \{-1,1\}^n \to \{-1,1\}$, $\left|\frac{1}{2}\operatorname{var}(f) - \operatorname{NS}_{\varepsilon}(f)\right| \leqslant M(f)^{\alpha\varepsilon}$.

## Statement 78: Theorem 4.4 (BKS for monotone functions)
There exists $\alpha > 0$ such that for all monotone $f: \{-1,1\}^n \to \{-1,1\}$, $(1-\varepsilon)M(f)\leqslant \left|\frac{1}{2}\operatorname{var}(f)-\operatorname{NS}_{\varepsilon}(f)\right|\leqslant M(f)^{\alpha\varepsilon}$.

## Statement 79: Theorem 4.5 (Weaker BKS)
There exists an absolute constant $C > 0$, such that for all $k \in \mathbb{N}$, $W^{=k}[f] \leqslant C^k M(f) \log \left(\frac{1}{M(f)}\right)^{k-1}$.

## Statement 80: Lemma 5.1 (Level k inequality)
Suppose $g: \{-1,1\}^n \to \{-1,0,1\}$ is non-zero with probability $\delta$, and let $k \in \mathbb{N}$. Then $W^{\leqslant k}[g] \leqslant \delta^2 (e \log(2/\delta))^k$.

## Statement 81: Remark 5.2
The level 0 weight of $g$ is $\delta^2$. Lemma 5.1 tells us that the level 1 weight can only jump multiplicatively by a logarithmic factor.

## Statement 82: Claim 6.1 (Decoupling)
There is a partition $(I, J)$ of $[n]$ such that $\sum_{\substack{|S|=k\\|S\cap I|=1}} \widehat{f}(S)^2 \geqslant \frac{1}{e} W^{=k}[f]$.

## Statement 83: Theorem 3.1 (Dinur-Friedgut, Lecture 11)
For all $\zeta > 0$, $\varepsilon > 0$ there exists $J \in \mathbb{N}$ such that if $\mathcal{F} \subseteq \{0,1\}^n$ is an intersecting family and $\zeta < p < 1/2$, then there exists an intersecting $J$-junta $\mathcal{J}$ such that $\mu_p(\mathcal{F} \setminus \mathcal{J}) \leqslant \varepsilon$.

## Statement 84: Claim 3.2 (Upwards closure preserves intersecting)
Suppose $\mathcal{F}$ is an intersecting family. Then $\mathcal{F}^{\uparrow}$ is also intersecting.

## Statement 85: Definition 3.3 (Quasi-randomness)
A Boolean function $f : \{0,1\}^n \to \{0,1\}$ is $(r,\varepsilon)$ quasi-random with respect to $p$ if for any $R \subseteq [n]$ of size at most $r$, and any $z \in \{0,1\}^R$ it holds that $|\mu_p(f_{R\to z}) - \mu_p(f)| \leqslant \varepsilon$.

## Statement 86: Definition 3.5
We say $\mathcal{F}$ is $(r, \varepsilon)$ quasi-random with respect to $p$ if $1_{\mathcal{F}}$ is $(r, \varepsilon)$ quasi-random with respect to $p$.

## Statement 87: Lemma 3.6 (Regularity lemma for quasi-randomness)
For all $r \in \mathbb{N}$, $\varepsilon > 0$, $\delta, \zeta > 0$ there exists $J \in \mathbb{N}$ such that if $\zeta \leqslant p \leqslant 1 - \zeta$, and $f: \{0,1\}^n \to \{0,1\}$ is any Boolean function, then there exists a set $T \subseteq [n]$ of size at most $J$, such that $\Pr_{z \sim \mu_p^T} \left[ f_{T \to z} \text{ is not } (r, \varepsilon) \text{ quasi-random} \right] \leqslant \delta$.

## Statement 88: Lemma 4.1 (Quasi-random sharp threshold)
For all $\zeta, \alpha > 0$, there exists $r \in \mathbb{N}$, $\varepsilon > 0$ such that if $\zeta < p < 1/2$ and $f:\{0,1\}^n \to \{0,1\}$ is monotone with $\mu_p(f)\geqslant \alpha$ and $f$ is $(r,\varepsilon)$ quasi-random, then $\mu_{p+\zeta/2}(f)\geqslant 0.9$.

## Statement 89: Claim 4.2 (Simple EKR)
Suppose $\mathcal{G}, \mathcal{H} \subseteq P([n])$ are such that $\mu_{1/2}(\mathcal{G}) + \mu_{1/2}(\mathcal{H}) > 1$. Then there are disjoint $F \in \mathcal{F}, G \in \mathcal{G}$.

## Statement 90: Lemma 4.3 (Quasi-random families not cross-intersecting)
For all $\alpha, \zeta > 0$ there exists $r \in \mathbb{N}$, $\varepsilon > 0$ such that if $\zeta < p < 1/2$ and $\mathcal{G}, \mathcal{H}$ are monotone families with $\mu_p(\mathcal{G}), \mu_p(\mathcal{H}) \geqslant \alpha$ and each is $(r, \varepsilon)$-quasi-random, then there are disjoint $G \in \mathcal{G}$, $H \in \mathcal{H}$.

## Statement 91: Theorem 1.1 (Invariance principle)
For all $d \in \mathbb{N}$, if $f(x_1, \ldots, x_n) = \sum_{|S| \leq d} \widehat{f}(S)\chi_S(x)$ is a function of degree at most $d$, and $\psi: \mathbb{R} \to \mathbb{R}$ is smooth with $\|\psi'''\|_{\infty} \leq C$, then $\left|\mathbb{E}_{x \sim \{-1,1\}^n} [\psi(f(x))] - \mathbb{E}_{z \sim N(0,I_n)} [\psi(f(z))]\right| \leqslant \frac{C}{2} 2^{3d/2} \sum_{i=1}^n I_i[f]^{3/2}$.

## Statement 92: Corollary 1.2 (Invariance principle, qualitative)
For all $C, \varepsilon > 0$, $d \in \mathbb{N}$ there is $\tau > 0$ such that if $f$ has degree at most $d$, $\psi$ is smooth with $\|\psi'''\|_{\infty} \leqslant C$ and $\operatorname{var}(f) \leqslant C$, then $\left|\mathbb{E}_{x \sim \{-1,1\}^n} [\psi(f(x))] - \mathbb{E}_{z \sim N(0,I_n)} [\psi(f(z))]\right| \leqslant \varepsilon$.

## Statement 93: Theorem 2.1 (Berry-Essen Theorem)
If $f(x_1, ..., x_n) = \sum_{i=1}^n a_i x_i$, and $\psi: \mathbb{R} \to \mathbb{R}$ is smooth with $\|\psi'''\|_{\infty} \leqslant C$, then $\left|\mathbb{E}_{x \sim \{-1,1\}^n} [\psi(f(x))] - \mathbb{E}_{z \sim N(0,I_n)} [\psi(f(z))]\right| \leqslant \frac{C}{2} \sum_{i=1}^n |a_i|^3$.

## Statement 94: Lemma 3.1 (Hypercontractivity for Gaussian space)
Suppose $f:(\mathbb{R}^n,\mu^{\otimes n})\to\mathbb{R}$ is a function of degree at most $d$, and $q\geqslant 2$. Then $\|f\|_q \leqslant \sqrt{q-1}^d \|f\|_2$.

## Statement 95: Lemma 3.2 (Hypercontractivity for mixed inputs)
Suppose $f: \{-1,1\}^t \times \mathbb{R}^{n-t} \to \mathbb{R}$ is a function of degree at most $d$, and $q \ge 2$. Then $\|f\|_q \leqslant \sqrt{q-1}^d \|f\|_2$.

## Statement 96: Theorem 5.1 (Invariance for non-smooth test functions)
For all $d \in \mathbb{N}$, $\varepsilon > 0$ there is $\tau > 0$ such that if $f$ has degree at most $d$ and $\max_i I_i[f] \leqslant \tau$, then $\left|\mathbb{E}_{x \sim \{-1,1\}^n} [\psi_0(f(x))] - \mathbb{E}_{z \sim N(0,I_n)} [\psi_0(f(z))]\right| \leqslant \varepsilon$.

## Statement 97: Theorem 5.2 (Carbery-Wright)
Suppose $f(x) = \sum_{0 < |S| \le d} a_S \chi_S$ is a multi-linear polynomial with $\sum_S a_S^2 \le 1$, and $I \subseteq \mathbb{R}$ is an interval of length at most $\varepsilon$. Then $\Pr_{z \sim N(0,1)} [|f(z)| \leqslant \varepsilon] \leqslant O(d\varepsilon^{1/d})$.

## Statement 98: Theorem 5.3 (Invariance principle with Fourier tails)
For all $C, \varepsilon > 0$, $d \in \mathbb{N}$ there is $\tau > 0$ such that if $\max_i I_i[f^{\leqslant d}] \leqslant \tau$ and $\psi$ is piecewise smooth and $C$-Lipschitz, then $\left|\mathbb{E}_{x} [\psi(f(x))] - \mathbb{E}_{z} [\psi(f(z))]\right| \leq \varepsilon + 2C \|f^{\geqslant d}\|_2$.

## Statement 99: Definition 6.1 (Gaussian noise operator)
For $\rho \in [0,1]$, the operator $U_{\rho}$ acting on functions $f: \mathbb{R}^n \to \mathbb{R}$ is $U_{\rho}(z) = \mathbb{E}_{w \sim N(0, I_n)} [f(\rho z + \sqrt{1 - \rho^2} w)]$.

## Statement 100: Definition 6.2 (Gaussian noise stability)
Given $\rho \in [0,1]$ and $f: \mathbb{R}^n \to \mathbb{R}$, the noise stability of $f$ with parameter $\rho$ is $\operatorname{Stab}_{\rho}(f) = \langle f, U_{\rho} f \rangle$.

## Statement 101: Theorem 6.3 (Borel's theorem)
Let $\rho \in [0,1]$, and $f: \mathbb{R}^n \to [-1,1]$ with $\mathbb{E}[f] = 0$. Then $\operatorname{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi}\operatorname{Arccos}(\rho)$.

## Statement 102: Theorem 6.4 (Majority is Stablest, formal)
For all $\varepsilon > 0$, $\rho \in (0,1)$ there are $d \in \mathbb{N}$ and $\tau > 0$ such that if $f : \{-1,1\}^n \to [-1,1]$ is balanced and $\max_i I_i[f^{\leq d}] \leq \tau$, then $\operatorname{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi} \operatorname{Arccos}(\rho) + \varepsilon$.

## Statement 103: Theorem 1.1 (Lecture 15, NP-hardness)
Suppose there exists an efficient algorithm for the Max-Cut problem (or the Minimum Vertex-Cover problem). Then there exists an efficient algorithm for the 3-SAT problem.

## Statement 104: Theorem 3.1 (PCP Theorem)
There exists $s < 1$, such that gap-3SAT$[1, s]$ is NP-hard.

## Statement 105: Theorem 3.2 (Hastad)
For all $\varepsilon > 0$, gap-3SAT$\left[1, \frac{7}{8} + \varepsilon\right]$ is NP-hard.

## Statement 106: Theorem 3.3 (Max-Cut NP-hardness)
It is NP-hard to approximate the Max-Cut problem within factor $\frac{16}{17}$.

## Statement 107: Theorem 3.4 (Vertex-Cover NP-hardness)
It is NP-hard to approximate the Minimum Vertex-Cover problem within factor 1.36.

## Statement 108: Definition 3.5 (Unique-Games)
An instance of Unique-Games is composed of a bipartite, bi-regular graph $G = (V = L \cup R, E)$, a finite alphabet $\Sigma$, and a collection of constraints $\Phi = (\phi_e)_{e \in E}$ where each $\phi_e$ is a 1-to-1 map $\phi_e: \Sigma \to \Sigma$.

## Statement 109: Conjecture 3.6 (Unique-Games Conjecture)
For all $\varepsilon, \delta > 0$, there exists $k \in \mathbb{N}$ such that given a Unique-Games instance $\Psi$, it is NP-hard to distinguish between: YES case $\operatorname{val}(\Psi) \ge 1 - \varepsilon$ and NO case $\operatorname{val}(\Psi) \leq \delta$.

## Statement 110: Theorem 1.1 (Lecture 16, GW algorithm)
Suppose $G=(V,E)$ has a cut of size $(1-\varepsilon)|E|$. Then the expected size of the cut in the Goemans-Williamson algorithm is at least $\left(1-\frac{2}{\pi}\sqrt{\varepsilon}-O(\varepsilon^{1.5})\right)|E|$.

## Statement 111: Theorem 2.1 (KKMO, Max-Cut hardness)
Assuming the Unique-Games Conjecture, for all $\rho \in (0,1)$ and $\varepsilon > 0$, given a graph $G = (V, E)$ it is NP-hard to distinguish between: YES case with cut of fractional size at least $\frac{1}{2} + \frac{1}{2}\rho - \varepsilon$, and NO case with all cuts at most $1 - \frac{1}{\pi} \operatorname{Arccos}(\rho) + \varepsilon$.

## Statement 112: Conjecture 2.3 (UGC restated)
For all $\eta > 0$, there exists $k \in \mathbb{N}$ such that gap-UniqueGames$_k[1-\varepsilon,\delta]$ is NP-hard.

## Statement 113: Lemma 2.4 (Reduction analysis)
For all $\rho \in (0,1)$, $\delta > 0$ there is $\eta > 0$ such that: (1) Completeness: if $\Psi$ is at least $1-\eta$ satisfiable, then there is a cut in $G$ of weight at least $\frac{1}{2}(1+\rho)-\delta$. (2) Soundness: if $\Psi$ is at most $\eta$ satisfiable, then $G$ has no cut exceeding $1 - \frac{1}{\pi}\operatorname{Arccos}(\rho) + \delta$.

## Statement 114: Theorem 2.5 (MIS for negative correlation)
For all $\rho \in (0,1)$, $\delta > 0$ there exist $d \in \mathbb{N}$, $\tau > 0$ such that if $f : \{-1,1\}^n \to [-1,1]$ with $\max_i I_i^{\leqslant d}[f] \leqslant \tau$, then $\operatorname{Stab}_{-\rho}(f)\geqslant \frac{2}{\pi}\operatorname{Arccos}(\rho)-1-\delta$.

## Statement 115: Lemma 2.6
$\widehat{g_u}(S) = \mathbb{E}_{w:(u,w)\in E}\left[\widehat{g_w}(\phi_{(u,w)}S)\right]$.

## Statement 116: Theorem 1.1 (Lecture 17, IS hardness)
Assuming UGC, for all $\varepsilon > 0$, given a graph $G = (V, E)$ it is NP-hard to distinguish between: YES case $\operatorname{IS}(G) \geqslant (\frac{1}{2} - \varepsilon) n$ and NO case $\operatorname{IS}(G) \leqslant \varepsilon n$.

## Statement 117: Corollary 1.2 (VC hardness)
Assuming UGC, for all $\varepsilon > 0$, it is NP-hard to distinguish between: YES case $\operatorname{VC}(G) \leq (\frac{1}{2} + \varepsilon) n$ and NO case $\operatorname{VC}(G) \ge (1 - \varepsilon)n$.

## Statement 118: Definition 1.3 (p-biased Kneser graph)
The $p$-biased Kneser graph has vertex set $P([n])$ with weight $\mu_p(A) = p^{|A|}(1-p)^{n-|A|}$ and edges $E = \{(A, B) \mid A \cap B = \emptyset\}$.

## Statement 119: Definition 1.4 (Strongish UGC)
For $\eta > 0$, $t \in \mathbb{N}$, a strongish form of UGC with YES case: there exists $X' \subseteq X$ of size at least $(1 - \eta)|X|$ and assignment satisfying all constraints inside $X'$; NO case: for all $X'$ of size $\geq \eta|X|$ and $t$-assignment, not all constraints in $X'$ are satisfied.

## Statement 120: Theorem 1.5 (Strongish UG reduction)
Assuming UGC, for all $t \in \mathbb{N}$, $\eta > 0$, the problem gap-StrongishUG$_t[1 - \eta, \eta]$ is NP-hard.

## Statement 121: Lemma 2.1 (IS reduction analysis)
For all $\varepsilon > 0$, $p = \frac{1}{2} - \varepsilon$ there are $t \in \mathbb{N}$ and $\eta > 0$ such that: (1) YES case: $G$ has an independent set of weight at least $p - \varepsilon$; (2) NO case: the heaviest independent set has weight at most $\varepsilon$.

## Statement 122: Lemma 3.1 (Juntas are intersecting)
$H$ defined above satisfies all of the constraints inside $X'$.

## Statement 123: Claim 2.1 (Lecture 16, 2-approx VC)
There is an efficient algorithm that finds a vertex-cover of size at most $2\gamma n$ when the minimum vertex-cover has size $\gamma n$.
