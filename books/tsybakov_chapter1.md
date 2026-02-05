# Chapter 1: Nonparametric Estimators

*From: A. B. Tsybakov, Introduction to Nonparametric Estimation*

---

## 1.1 Examples of nonparametric models and problems

### 1. Estimation of a probability density

Let $X_1, \ldots, X_n$ be identically distributed real valued random variables whose common distribution is absolutely continuous with respect to the Lebesgue measure on $\mathbb{R}$. The density of this distribution, denoted by $p$, is a function from $\mathbb{R}$ to $[0, +\infty)$ supposed to be unknown. The problem is to estimate $p$.

An estimator of $p$ is a function $x \mapsto \hat{p}_n(x) = \hat{p}_n(x, X_1, \ldots, X_n)$ measurable with respect to the observation $X = (X_1, \ldots, X_n)$. If we know a priori that $p$ belongs to a parametric family $\{g(x, \theta) : \theta \in \Theta\}$, where $g(\cdot, \cdot)$ is a given function, and $\Theta$ is a subset of $\mathbb{R}^k$ with a fixed dimension $k$ independent of $n$, then estimation of $p$ is equivalent to estimation of the finite-dimensional parameter $\theta$. This is a parametric problem of estimation. On the contrary, if such a prior information about $p$ is not available we deal with a nonparametric problem. In nonparametric estimation it is usually assumed that $p$ belongs to some "massive" class $\mathcal{P}$ of densities. For example, $\mathcal{P}$ can be the set of all the continuous probability densities on $\mathbb{R}$ or the set of all the Lipschitz continuous probability densities on $\mathbb{R}$. Classes of such type will be called nonparametric classes of functions.

### 2. Nonparametric regression

Assume that we have $n$ independent pairs of random variables $(X_1, Y_1), \ldots, (X_n, Y_n)$ such that

$$Y_i = f(X_i) + \xi_i, \quad X_i \in [0, 1], \tag{1.1}$$

where the random variables $\xi_i$ satisfy $\mathbb{E}(\xi_i) = 0$ for all $i$ and where the function $f$ from $[0, 1]$ to $\mathbb{R}$ (called the regression function) is unknown. The problem of nonparametric regression is to estimate $f$ given a priori that this function belongs to a nonparametric class of functions $\mathcal{F}$. For example, $\mathcal{F}$ can be the set of all the continuous functions on $[0, 1]$ or the set of all the convex functions, etc. An estimator of $f$ is a function $x \mapsto \hat{f}_n(x) = \hat{f}_n(x, X)$ defined on $[0, 1]$ and measurable with respect to the observation $X = (X_1, \ldots, X_n, Y_1, \ldots, Y_n)$. In what follows, we will mainly focus on the particular case $X_i = i/n$.

### 3. Gaussian white noise model

This is an idealized model that provides an approximation to the nonparametric regression (1.1). Consider the following stochastic differential equation:

$$dY(t) = f(t)dt + \frac{1}{\sqrt{n}} dW(t), \quad t \in [0, 1],$$

where $W$ is a standard Wiener process on $[0, 1]$, the function $f$ is an unknown function on $[0, 1]$, and $n$ is an integer. We assume that a sample path $X = \{Y(t), 0 \le t \le 1\}$ of the process $Y$ is observed. The statistical problem is to estimate the unknown function $f$. In the nonparametric case it is only known a priori that $f \in \mathcal{F}$ where $\mathcal{F}$ is a given nonparametric class of functions. An estimator of $f$ is a function $x \mapsto \hat{f}_n(x) = \hat{f}_n(x, X)$ defined on $[0, 1]$ and measurable with respect to the observation $X$.

In either of the three above cases, we are interested in the asymptotic behavior of estimators as $n \to \infty$.

## 1.2 Kernel density estimators

We start with the first of the three problems described in Section 1.1. Let $X_1, \ldots, X_n$ be independent identically distributed (i.i.d.) random variables that have a probability density $p$ with respect to the Lebesgue measure on $\mathbb{R}$. The corresponding distribution function is $F(x) = \int_{-\infty}^{x} p(t) dt$. Consider the empirical distribution function

$$F_n(x) = \frac{1}{n} \sum_{i=1}^{n} \mathbf{1}(X_i \le x),$$

where $\mathbf{1}(\cdot)$ denotes the indicator function. By the strong law of large numbers, we have

$$F_n(x) \to F(x), \quad \forall x \in \mathbb{R},$$

almost surely as $n \to \infty$. Therefore, $F_n(x)$ is a consistent estimator of $F(x)$ for every $x \in \mathbb{R}$. How can we estimate the density $p$? One of the first intuitive solutions is based on the following argument. For sufficiently small $h > 0$ we can write an approximation

$$p(x) \approx \frac{F(x + h) - F(x - h)}{2h}.$$

Replacing $F$ by the estimate $F_n$ we define

$$\hat{p}_n^R(x) = \frac{F_n(x + h) - F_n(x - h)}{2h}.$$

The function $\hat{p}_n^R$ is an estimator of $p$ called the Rosenblatt estimator. We can rewrite it in the form:

$$\hat{p}_n^R(x) = \frac{1}{2nh} \sum_{i=1}^{n} \mathbf{1}(x - h < X_i \le x + h) = \frac{1}{nh} \sum_{i=1}^{n} K_0\left(\frac{X_i - x}{h}\right),$$

where $K_0(u) = \frac{1}{2} \mathbf{1}(-1 < u \le 1)$. A simple generalization of the Rosenblatt estimator is given by

$$\hat{p}_n(x) = \frac{1}{nh} \sum_{i=1}^{n} K\left(\frac{X_i - x}{h}\right), \tag{1.2}$$

where $K : \mathbb{R} \to \mathbb{R}$ is an integrable function satisfying $\int K(u) du = 1$. Such a function $K$ is called a kernel and the parameter $h$ is called a bandwidth of the estimator (1.2). The function $x \mapsto \hat{p}_n(x)$ is called the kernel density estimator or the Parzen–Rosenblatt estimator.

In the asymptotic framework, as $n \to \infty$, we will consider a bandwidth $h$ that depends on $n$, denoting it by $h_n$, and we will suppose that the sequence $(h_n)_{n \ge 1}$ tends to 0 as $n \to \infty$. The notation $h$ without index $n$ will also be used for brevity whenever this causes no ambiguity.

Some classical examples of kernels are the following:
- $K(u) = \frac{1}{2} \mathbf{1}(|u| \le 1)$ (the rectangular kernel)
- $K(u) = (1 - |u|) \mathbf{1}(|u| \le 1)$ (the triangular kernel)
- $K(u) = \frac{3}{4}(1 - u^2) \mathbf{1}(|u| \le 1)$ (the parabolic/Epanechnikov kernel)
- $K(u) = \frac{15}{16}(1 - u^2)^2 \mathbf{1}(|u| \le 1)$ (the biweight kernel)
- $K(u) = \frac{1}{\sqrt{2\pi}} \exp(-u^2/2)$ (the Gaussian kernel)
- $K(u) = \frac{1}{2} \exp(-|u|/\sqrt{2}) \sin(|u|/\sqrt{2} + \pi/4)$ (the Silverman kernel)

Note that if the kernel $K$ takes only nonnegative values and if $X_1, \ldots, X_n$ are fixed, then the function $x \mapsto \hat{p}_n(x)$ is a probability density.

The Parzen–Rosenblatt estimator can be generalized to the multidimensional case. For example, we can define a kernel density estimator in two dimensions as follows. Suppose that we observe $n$ pairs of random variables $(X_1, Y_1), \ldots, (X_n, Y_n)$ such that $(X_i, Y_i)$ are i.i.d. with a density $p(x, y)$ in $\mathbb{R}^2$. A kernel estimator of $p(x, y)$ is then given by the formula

$$\hat{p}_n(x, y) = \frac{1}{nh^2} \sum_{i=1}^{n} K\left(\frac{X_i - x}{h}\right) K\left(\frac{Y_i - y}{h}\right) \tag{1.3}$$

where $K : \mathbb{R} \to \mathbb{R}$ is a kernel defined as above and $h > 0$ is a bandwidth.

### 1.2.1 Mean squared error of kernel estimators

A basic measure of the accuracy of estimator $\hat{p}_n$ is its mean squared risk (or mean squared error) at an arbitrary fixed point $x_0 \in \mathbb{R}$:

$$\text{MSE} = \text{MSE}(x_0) \triangleq \mathbb{E}_p\left[(\hat{p}_n(x_0) - p(x_0))^2\right].$$

Here, MSE stands for "mean squared error" and $\mathbb{E}_p$ denotes the expectation with respect to the distribution of $(X_1, \ldots, X_n)$:

$$\mathbb{E}_p\left[(\hat{p}_n(x_0) - p(x_0))^2\right] \triangleq \int \cdots \int (\hat{p}_n(x_0, x_1, \ldots, x_n) - p(x_0))^2 \prod_{i=1}^{n} [p(x_i) dx_i].$$

We have

$$\text{MSE} = b^2(x_0) + \sigma^2(x_0) \tag{1.4}$$

where

$$b(x_0) = \mathbb{E}_p[\hat{p}_n(x_0)] - p(x_0)$$

and

$$\sigma^2(x_0) = \mathbb{E}_p\left[(\hat{p}_n(x_0) - \mathbb{E}_p[\hat{p}_n(x_0)])^2\right].$$

**Definition 1.1.** The quantities $b(x_0)$ and $\sigma^2(x_0)$ are called the bias and the variance of the estimator $\hat{p}_n$ at a point $x_0$, respectively.

To evaluate the mean squared risk of $\hat{p}_n$ we will analyze separately its variance and bias.

#### Variance of the estimator $\hat{p}_n$

**Proposition 1.1.** Suppose that the density $p$ satisfies $p(x) \le p_{\max} < \infty$ for all $x \in \mathbb{R}$. Let $K : \mathbb{R} \to \mathbb{R}$ be a function such that

$$\int K^2(u) du < \infty. \tag{1.5}$$

Then for any $x_0 \in \mathbb{R}$, $h > 0$, and $n \ge 1$ we have

$$\sigma^2(x_0) \le \frac{C_1}{nh}$$

where $C_1 = p_{\max} \int K^2(u) du$.

*Proof.* Put

$$\eta_i(x_0) = K\left(\frac{X_i - x_0}{h}\right) - \mathbb{E}_p\left[K\left(\frac{X_i - x_0}{h}\right)\right].$$

The random variables $\eta_i(x_0)$, $i = 1, \ldots, n$, are i.i.d. with zero mean and variance

$$\mathbb{E}_p[\eta_i^2(x_0)] \le \mathbb{E}_p\left[K^2\left(\frac{X_i - x_0}{h}\right)\right] = \int K^2\left(\frac{z - x_0}{h}\right) p(z) dz \le p_{\max} h \int K^2(u) du.$$

Then

$$\sigma^2(x_0) = \mathbb{E}_p\left[\left(\frac{1}{nh} \sum_{i=1}^{n} \eta_i(x_0)\right)^2\right] = \frac{1}{n^2 h^2} \cdot n \cdot \mathbb{E}_p[\eta_1^2(x_0)] \le \frac{C_1}{nh}. \tag{1.6}$$

We conclude that if the bandwidth $h = h_n$ is such that $nh \to \infty$ as $n \to \infty$, then the variance $\sigma^2(x_0)$ goes to 0 as $n \to \infty$.

#### Bias of the estimator $\hat{p}_n$

The bias of the kernel density estimator has the form

$$b(x_0) = \mathbb{E}_p[\hat{p}_n(x_0)] - p(x_0) = \frac{1}{h} \int K\left(\frac{z - x_0}{h}\right) p(z) dz - p(x_0).$$

We now analyze the behavior of $b(x_0)$ as a function of $h$ under some regularity conditions on the density $p$ and on the kernel $K$.

In what follows $\lfloor \beta \rfloor$ will denote the greatest integer strictly less than the real number $\beta$.

**Definition 1.2.** Let $T$ be an interval in $\mathbb{R}$ and let $\beta$ and $L$ be two positive numbers. The Hölder class $\Sigma(\beta, L)$ on $T$ is defined as the set of $\ell = \lfloor \beta \rfloor$ times differentiable functions $f : T \to \mathbb{R}$ whose derivative $f^{(\ell)}$ satisfies

$$|f^{(\ell)}(x) - f^{(\ell)}(x')| \le L|x - x'|^{\beta - \ell}, \quad \forall x, x' \in T.$$

**Definition 1.3.** Let $\ell \ge 1$ be an integer. We say that $K : \mathbb{R} \to \mathbb{R}$ is a kernel of order $\ell$ if the functions $u \mapsto u^j K(u)$, $j = 0, 1, \ldots, \ell$, are integrable and satisfy

$$\int K(u) du = 1, \quad \int u^j K(u) du = 0, \quad j = 1, \ldots, \ell.$$

Some examples of kernels of order $\ell$ will be given in Section 1.2.2. It is important to note that another definition of an order $\ell$ kernel is often used in the literature: a kernel $K$ is said to be of order $\ell + 1$ (with integer $\ell \ge 1$) if Definition 1.3 holds and $\int u^{\ell+1} K(u) du \ne 0$. Definition 1.3 is less restrictive and seems to be more natural, since there is no need to assume that $\int u^{\ell+1} K(u) du \ne 0$ for noninteger $\beta$. For example, Proposition 1.2 given below still holds if $\int u^{\ell+1} K(u) du = 0$ and even if this integral does not exist.

Suppose now that $p$ belongs to the class of densities $\mathcal{P} = \mathcal{P}(\beta, L)$ defined as follows:

$$\mathcal{P}(\beta, L) = \left\{ p : p \ge 0, \int p(x) dx = 1, \text{ and } p \in \Sigma(\beta, L) \text{ on } \mathbb{R} \right\}$$

and assume that $K$ is a kernel of order $\ell$. Then the following result holds.

**Proposition 1.2.** Assume that $p \in \mathcal{P}(\beta, L)$ and let $K$ be a kernel of order $\ell = \lfloor \beta \rfloor$ satisfying

$$\int |u|^\beta |K(u)| du < \infty.$$

Then for all $x_0 \in \mathbb{R}$, $h > 0$ and $n \ge 1$ we have

$$|b(x_0)| \le C_2 h^\beta$$

where

$$C_2 = \frac{L}{\ell!} \int |u|^\beta |K(u)| du.$$

*Proof.* We have

$$b(x_0) = \frac{1}{h} \int K\left(\frac{z - x_0}{h}\right) p(z) dz - p(x_0) = \int K(u) \left(p(x_0 + uh) - p(x_0)\right) du.$$

Next,

$$p(x_0 + uh) = p(x_0) + p'(x_0) uh + \cdots + \frac{(uh)^\ell}{\ell!} p^{(\ell)}(x_0 + \tau uh), \tag{1.7}$$

where $0 \le \tau \le 1$. Since $K$ has order $\ell = \lfloor \beta \rfloor$, we obtain

$$b(x_0) = \int K(u) \frac{(uh)^\ell}{\ell!} p^{(\ell)}(x_0 + \tau uh) du = \int K(u) \frac{(uh)^\ell}{\ell!} \left(p^{(\ell)}(x_0 + \tau uh) - p^{(\ell)}(x_0)\right) du$$

and

$$|b(x_0)| \le \int |K(u)| \frac{|uh|^\ell}{\ell!} \left|p^{(\ell)}(x_0 + \tau uh) - p^{(\ell)}(x_0)\right| du \le L \int |K(u)| \frac{|uh|^\ell}{\ell!} |\tau uh|^{\beta - \ell} du \le C_2 h^\beta.$$

#### Upper bound on the mean squared risk

From Propositions 1.1 and 1.2, we see that the upper bounds on the bias and variance behave in opposite ways as the bandwidth $h$ varies. The variance decreases as $h$ grows, whereas the bound on the bias increases (cf. Figure 1.1). The choice of a small $h$ corresponding to a large variance is called an undersmoothing. Alternatively, with a large $h$ the bias cannot be reasonably controlled, which leads to oversmoothing. An optimal value of $h$ that balances bias and variance is located between these two extremes. Figure 1.2 shows typical plots of the corresponding density estimators. To get an insight into the optimal choice of $h$, we can minimize in $h$ the upper bound on the MSE obtained from the above results.

If $p$ and $K$ satisfy the assumptions of Propositions 1.1 and 1.2, we obtain

$$\text{MSE} \le C_2^2 h^{2\beta} + \frac{C_1}{nh}. \tag{1.8}$$

The minimum with respect to $h$ of the right hand side of (1.8) is attained at

$$h_n^* = \left(\frac{C_1}{2\beta C_2^2}\right)^{\frac{1}{2\beta+1}} n^{-\frac{1}{2\beta+1}}.$$

Therefore, the choice $h = h_n^*$ gives

$$\text{MSE}(x_0) = O\left(n^{-\frac{2\beta}{2\beta+1}}\right), \quad n \to \infty,$$

uniformly in $x_0$. We have the following result.

**Theorem 1.1.** Assume that condition (1.5) holds and the assumptions of Proposition 1.2 are satisfied. Fix $\alpha > 0$ and take $h = \alpha n^{-\frac{1}{2\beta+1}}$. Then for $n \ge 1$ the kernel estimator $\hat{p}_n$ satisfies

$$\sup_{x_0 \in \mathbb{R}} \sup_{p \in \mathcal{P}(\beta, L)} \mathbb{E}_p[(\hat{p}_n(x_0) - p(x_0))^2] \le C n^{-\frac{2\beta}{2\beta+1}},$$

where $C > 0$ is a constant depending only on $\beta$, $L$, $\alpha$ and on the kernel $K$.

*Proof.* We apply (1.8) as shown above. To justify the application of Proposition 1.1, it remains to prove that there exists a constant $p_{\max} < \infty$ satisfying

$$\sup_{x \in \mathbb{R}} \sup_{p \in \mathcal{P}(\beta, L)} p(x) \le p_{\max}. \tag{1.9}$$

To show (1.9), consider $K^*$ which is a bounded kernel of order $\ell$, not necessarily equal to $K$. Applying Proposition 1.2 with $h = 1$ we get that, for any $x_0 \in \mathbb{R}$ and any $p \in \mathcal{P}(\beta, L)$,

$$\left|\int K^*(z - x_0) p(z) dz - p(x_0)\right| \le C^* \triangleq \frac{L}{\ell!} \int |u|^\beta |K^*(u)| du.$$

Therefore, for any $x \in \mathbb{R}$ and any $p \in \mathcal{P}(\beta, L)$,

$$p(x) \le \frac{C^*}{2} + \int |K^*(z - x)| p(z) dz \le \frac{C^*}{2} + K^*_{\max},$$

where $K^*_{\max} = \sup_{u \in \mathbb{R}} |K^*(u)|$. Thus, we get (1.9) with $p_{\max} = \frac{C^*}{2} + K^*_{\max}$.

Under the assumptions of Theorem 1.1, the rate of convergence of the estimator $\hat{p}_n(x_0)$ is $\psi_n = n^{-\frac{\beta}{2\beta+1}}$, which means that for a finite constant $C$ and for all $n \ge 1$ we have

$$\sup_{p \in \mathcal{P}(\beta, L)} \mathbb{E}_p\left[(\hat{p}_n(x_0) - p(x_0))^2\right] \le C \psi_n^2.$$

Now the following two questions arise. Can we improve the rate $\psi_n$ by using other density estimators? What is the best possible rate of convergence? To answer these questions it is useful to consider the minimax risk $R_n^*$ associated to the class $\mathcal{P}(\beta, L)$:

$$R_n^*(\mathcal{P}(\beta, L)) \triangleq \inf_{T_n} \sup_{p \in \mathcal{P}(\beta, L)} \mathbb{E}_p\left[(T_n(x_0) - p(x_0))^2\right],$$

where the infimum is over all estimators. One can prove a lower bound on the minimax risk of the form $R_n^*(\mathcal{P}(\beta, L)) \ge C' \psi_n^2 = C' n^{-\frac{2\beta}{2\beta+1}}$ with some constant $C' > 0$ (cf. Chapter 2, Exercise 2.8). This implies that under the assumptions of Theorem 1.1 the kernel estimator attains the optimal rate of convergence $n^{-\frac{\beta}{2\beta+1}}$ associated with the class of densities $\mathcal{P}(\beta, L)$. Exact definitions and discussions of the notion of optimal rate of convergence will be given in Chapter 2.

#### Positivity constraint

It follows easily from Definition 1.3 that kernels of order $\ell \ge 2$ must take negative values on a set of positive Lebesgue measure. The estimators $\hat{p}_n$ based on such kernels can also take negative values. This property is sometimes emphasized as a drawback of estimators with higher order kernels, since the density $p$ itself is nonnegative. However, this remark is of minor importance because we can always use the positive part estimator

$$\hat{p}_n^+(x) \triangleq \max\{0, \hat{p}_n(x)\}$$

whose risk is smaller than or equal to the risk of $\hat{p}_n$:

$$\mathbb{E}_p\left[(\hat{p}_n^+(x_0) - p(x_0))^2\right] \le \mathbb{E}_p\left[(\hat{p}_n(x_0) - p(x_0))^2\right], \quad \forall x_0 \in \mathbb{R}. \tag{1.10}$$

In particular, Theorem 1.1 remains valid if we replace there $\hat{p}_n$ by $\hat{p}_n^+$. Thus, the estimator $\hat{p}_n^+$ is nonnegative and attains fast convergence rates associated with higher order kernels.

---

*[End of extracted section containing Propositions 1.1 and 1.2]*
