# Chapter 3: Dimension-free Convex Optimization

*From: S. Bubeck, Convex Optimization: Algorithms and Complexity*

---

We investigate here variants of the gradient descent scheme. This iterative algorithm, which can be traced back to Cauchy [1847], is the simplest strategy to minimize a differentiable function $f$ on $\mathbb{R}^n$. Starting at some initial point $x_1 \in \mathbb{R}^n$ it iterates the following equation:

$$x_{t+1} = x_t - \eta \nabla f(x_t), \tag{3.1}$$

where $\eta > 0$ is a fixed step-size parameter. The rationale behind (3.1) is to make a small step in the direction that minimizes the local first order Taylor approximation of $f$ (also known as the steepest descent direction).

As we shall see, methods of the type (3.1) can obtain an oracle complexity independent of the dimension. This feature makes them particularly attractive for optimization in very high dimension.

Apart from Section 3.3, in this chapter $\|\cdot\|$ denotes the Euclidean norm. The set of constraints $\mathcal{X} \subset \mathbb{R}^n$ is assumed to be compact and convex. We define the projection operator $\Pi_{\mathcal{X}}$ on $\mathcal{X}$ by

$$\Pi_{\mathcal{X}}(x) = \arg\min_{y \in \mathcal{X}} \|x - y\|.$$

The following lemma will prove to be useful in our study. It is an easy corollary of Proposition 1.3.

**Lemma 3.1.** Let $x \in \mathcal{X}$ and $y \in \mathbb{R}^n$, then

$$(\Pi_{\mathcal{X}}(y) - x)^\top (\Pi_{\mathcal{X}}(y) - y) \le 0,$$

which also implies $\|\Pi_{\mathcal{X}}(y) - x\|^2 + \|y - \Pi_{\mathcal{X}}(y)\|^2 \le \|y - x\|^2$.

Unless specified otherwise all the proofs in this chapter are taken from Nesterov [2004a] (with slight simplification in some cases).

## 3.1 Projected subgradient descent for Lipschitz functions

In this section we assume that $\mathcal{X}$ is contained in an Euclidean ball centered at $x_1 \in \mathcal{X}$ and of radius $R$. Furthermore we assume that $f$ is such that for any $x \in \mathcal{X}$ and any $g \in \partial f(x)$ (we assume $\partial f(x) \ne \emptyset$), one has $\|g\| \le L$. Note that by the subgradient inequality and Cauchy-Schwarz this implies that $f$ is $L$-Lipschitz on $\mathcal{X}$, that is $|f(x) - f(y)| \le L\|x - y\|$.

In this context we make two modifications to the basic gradient descent (3.1). First, obviously, we replace the gradient $\nabla f(x)$ (which may not exist) by a subgradient $g \in \partial f(x)$. Secondly, and more importantly, we make sure that the updated point lies in $\mathcal{X}$ by projecting back (if necessary) onto it. This gives the projected subgradient descent algorithm which iterates the following equations for $t \ge 1$:

$$y_{t+1} = x_t - \eta g_t, \quad \text{where } g_t \in \partial f(x_t), \tag{3.2}$$
$$x_{t+1} = \Pi_{\mathcal{X}}(y_{t+1}). \tag{3.3}$$

We prove now a rate of convergence for this method under the above assumptions.

**Theorem 3.2.** The projected subgradient descent method with $\eta = \frac{R}{L\sqrt{t}}$ satisfies

$$f\left(\frac{1}{t} \sum_{s=1}^{t} x_s\right) - f(x^*) \le \frac{RL}{\sqrt{t}}.$$

*Proof.* Using the definition of subgradients, the definition of the method, and the elementary identity $2a^\top b = \|a\|^2 + \|b\|^2 - \|a - b\|^2$, one obtains

$$f(x_s) - f(x^*) \le g_s^\top(x_s - x^*) = \frac{1}{\eta}(x_s - y_{s+1})^\top(x_s - x^*) = \frac{1}{2\eta}\left(\|x_s - x^*\|^2 + \|x_s - y_{s+1}\|^2 - \|y_{s+1} - x^*\|^2\right) = \frac{1}{2\eta}\left(\|x_s - x^*\|^2 - \|y_{s+1} - x^*\|^2\right) + \frac{\eta}{2}\|g_s\|^2.$$

Now note that $\|g_s\| \le L$, and furthermore by Lemma 3.1, $\|y_{s+1} - x^*\| \ge \|x_{s+1} - x^*\|$. Summing the resulting inequality over $s$, and using that $\|x_1 - x^*\| \le R$ yield

$$\sum_{s=1}^{t}(f(x_s) - f(x^*)) \le \frac{R^2}{2\eta} + \frac{\eta L^2 t}{2}.$$

Plugging in the value of $\eta$ directly gives the statement (recall that by convexity $f((1/t) \sum_{s=1}^{t} x_s) \le \frac{1}{t}\sum_{s=1}^{t} f(x_s)$).

We will show in Section 3.5 that the rate given in Theorem 3.2 is unimprovable from a black-box perspective. Thus to reach an $\varepsilon$-optimal point one needs $\Theta(1/\varepsilon^2)$ calls to the oracle. In some sense this is an astonishing result as this complexity is independent of the ambient dimension $n$. On the other hand this is also quite disappointing compared to the scaling in $\log(1/\varepsilon)$ of the center of gravity and ellipsoid method of Chapter 2.

## 3.2 Gradient descent for smooth functions

We say that a continuously differentiable function $f$ is $\beta$-smooth if the gradient $\nabla f$ is $\beta$-Lipschitz, that is

$$\|\nabla f(x) - \nabla f(y)\| \le \beta\|x - y\|.$$

Note that if $f$ is twice differentiable then this is equivalent to the eigenvalues of the Hessians being smaller than $\beta$. In this section we explore potential improvements in the rate of convergence under such a smoothness assumption. In order to avoid technicalities we consider first the unconstrained situation, where $f$ is a convex and $\beta$-smooth function on $\mathbb{R}^n$. The next theorem shows that gradient descent, which iterates $x_{t+1} = x_t - \eta\nabla f(x_t)$, attains a much faster rate in this situation than in the non-smooth case of the previous section.

**Theorem 3.3.** Let $f$ be convex and $\beta$-smooth on $\mathbb{R}^n$. Then gradient descent with $\eta = \frac{1}{\beta}$ satisfies

$$f(x_t) - f(x^*) \le \frac{2\beta\|x_1 - x^*\|^2}{t - 1}.$$

Before embarking on the proof we state a few properties of smooth convex functions.

**Lemma 3.4.** Let $f$ be a $\beta$-smooth function on $\mathbb{R}^n$. Then for any $x, y \in \mathbb{R}^n$, one has

$$|f(x) - f(y) - \nabla f(y)^\top(x - y)| \le \frac{\beta}{2}\|x - y\|^2.$$

*Proof.* We represent $f(x) - f(y)$ as an integral, apply Cauchy-Schwarz and then $\beta$-smoothness:

$$|f(x) - f(y) - \nabla f(y)^\top(x - y)| = \left|\int_0^1 \nabla f(y + t(x-y))^\top(x-y) dt - \nabla f(y)^\top(x-y)\right| \le \int_0^1 \|\nabla f(y + t(x-y)) - \nabla f(y)\| \cdot \|x-y\| dt \le \int_0^1 \beta t \|x-y\|^2 dt = \frac{\beta}{2}\|x-y\|^2.$$

In particular this lemma shows that if $f$ is convex and $\beta$-smooth, then for any $x, y \in \mathbb{R}^n$, one has

$$0 \le f(x) - f(y) - \nabla f(y)^\top(x - y) \le \frac{\beta}{2}\|x - y\|^2. \tag{3.4}$$

This gives in particular the following important inequality to evaluate the improvement in one step of gradient descent:

$$f\left(x - \frac{1}{\beta}\nabla f(x)\right) - f(x) \le -\frac{1}{2\beta}\|\nabla f(x)\|^2. \tag{3.5}$$

**Lemma 3.5.** Let $f$ be such that (3.4) holds true. Then for any $x, y \in \mathbb{R}^n$, one has

$$f(x) - f(y) \le \nabla f(x)^\top(x - y) - \frac{1}{2\beta}\|\nabla f(x) - \nabla f(y)\|^2.$$

*Proof.* Let $z = y - \frac{1}{\beta}(\nabla f(y) - \nabla f(x))$. Then one has

$$f(x) - f(y) = f(x) - f(z) + f(z) - f(y) \le \nabla f(x)^\top(x - z) + \nabla f(y)^\top(z - y) + \frac{\beta}{2}\|z - y\|^2 = \nabla f(x)^\top(x - y) + (\nabla f(x) - \nabla f(y))^\top(y - z) + \frac{1}{2\beta}\|\nabla f(x) - \nabla f(y)\|^2 = \nabla f(x)^\top(x - y) - \frac{1}{2\beta}\|\nabla f(x) - \nabla f(y)\|^2.$$

We can now prove Theorem 3.3.

*Proof.* Using (3.5) and the definition of the method one has

$$f(x_{s+1}) - f(x_s) \le -\frac{1}{2\beta}\|\nabla f(x_s)\|^2.$$

In particular, denoting $\delta_s = f(x_s) - f(x^*)$, this shows:

$$\delta_{s+1} \le \delta_s - \frac{1}{2\beta}\|\nabla f(x_s)\|^2.$$

One also has by convexity

$$\delta_s \le \nabla f(x_s)^\top(x_s - x^*) \le \|x_s - x^*\| \cdot \|\nabla f(x_s)\|.$$

We will prove that $\|x_s - x^*\|$ is decreasing with $s$, which with the two above displays will imply

$$\delta_{s+1} \le \delta_s - \frac{1}{2\beta\|x_1 - x^*\|^2}\delta_s^2.$$

Let us see how to use this last inequality to conclude the proof. Let $\omega = \frac{1}{2\beta\|x_1 - x^*\|^2}$, then

$$\omega\delta_s^2 + \delta_{s+1} \le \delta_s \Rightarrow \frac{1}{\delta_{s+1}} - \frac{1}{\delta_s} \ge \omega \Rightarrow \frac{1}{\delta_t} \ge \omega(t-1).$$

Thus it only remains to show that $\|x_s - x^*\|$ is decreasing with $s$. Using Lemma 3.5 one immediately gets

$$(\nabla f(x) - \nabla f(y))^\top(x - y) \ge \frac{1}{\beta}\|\nabla f(x) - \nabla f(y)\|^2. \tag{3.6}$$

We use this as follows (together with $\nabla f(x^*) = 0$)

$$\|x_{s+1} - x^*\|^2 = \|x_s - \frac{1}{\beta}\nabla f(x_s) - x^*\|^2 = \|x_s - x^*\|^2 - \frac{2}{\beta}\nabla f(x_s)^\top(x_s - x^*) + \frac{1}{\beta^2}\|\nabla f(x_s)\|^2 \le \|x_s - x^*\|^2 - \frac{1}{\beta^2}\|\nabla f(x_s)\|^2 \le \|x_s - x^*\|^2,$$

which concludes the proof.

### The constrained case

We now come back to the constrained problem: minimize $f(x)$ subject to $x \in \mathcal{X}$. Similarly to what we did in Section 3.1 we consider the projected gradient descent algorithm, which iterates $x_{t+1} = \Pi_{\mathcal{X}}(x_t - \eta\nabla f(x_t))$.

**Lemma 3.6.** Let $x, y \in \mathcal{X}$, $x^+ = \Pi_{\mathcal{X}}\left(x - \frac{1}{\beta}\nabla f(x)\right)$, and $g_{\mathcal{X}}(x) = \beta(x - x^+)$. Then the following holds true:

$$f(x^+) - f(y) \le g_{\mathcal{X}}(x)^\top(x - y) - \frac{1}{2\beta}\|g_{\mathcal{X}}(x)\|^2.$$

*Proof.* We first observe that

$$\nabla f(x)^\top(x^+ - y) \le g_{\mathcal{X}}(x)^\top(x^+ - y). \tag{3.7}$$

Indeed the above inequality is equivalent to $\left(x^+ - \left(x - \frac{1}{\beta}\nabla f(x)\right)\right)^\top(x^+ - y) \le 0$, which follows from Lemma 3.1. Now we use (3.7) as follows to prove the lemma (we also use (3.4) which still holds true in the constrained case)

$$f(x^+) - f(y) = f(x^+) - f(x) + f(x) - f(y) \le \nabla f(x)^\top(x^+ - x) + \frac{\beta}{2}\|x^+ - x\|^2 + \nabla f(x)^\top(x - y) = \nabla f(x)^\top(x^+ - y) + \frac{1}{2\beta}\|g_{\mathcal{X}}(x)\|^2 \le g_{\mathcal{X}}(x)^\top(x^+ - y) + \frac{1}{2\beta}\|g_{\mathcal{X}}(x)\|^2 = g_{\mathcal{X}}(x)^\top(x - y) - \frac{1}{2\beta}\|g_{\mathcal{X}}(x)\|^2.$$

**Theorem 3.7.** Let $f$ be convex and $\beta$-smooth on $\mathcal{X}$. Then projected gradient descent with $\eta = \frac{1}{\beta}$ satisfies

$$f(x_t) - f(x^*) \le \frac{3\beta\|x_1 - x^*\|^2 + f(x_1) - f(x^*)}{t}.$$

*Proof.* Lemma 3.6 immediately gives

$$f(x_{s+1}) - f(x_s) \le -\frac{1}{2\beta}\|g_{\mathcal{X}}(x_s)\|^2,$$

and

$$f(x_{s+1}) - f(x^*) \le \|g_{\mathcal{X}}(x_s)\| \cdot \|x_s - x^*\|.$$

We will prove that $\|x_s - x^*\|$ is decreasing with $s$, which with the two above displays will imply

$$\delta_{s+1} \le \delta_s - \frac{1}{2\beta\|x_1 - x^*\|^2}\delta_{s+1}^2.$$

An easy induction shows that

$$\delta_s \le \frac{3\beta\|x_1 - x^*\|^2 + f(x_1) - f(x^*)}{s}.$$

Thus it only remains to show that $\|x_s - x^*\|$ is decreasing with $s$. Using Lemma 3.6 one can see that $g_{\mathcal{X}}(x_s)^\top(x_s - x^*) \ge \frac{1}{2\beta}\|g_{\mathcal{X}}(x_s)\|^2$ which implies

$$\|x_{s+1} - x^*\|^2 = \|x_s - \frac{1}{\beta}g_{\mathcal{X}}(x_s) - x^*\|^2 = \|x_s - x^*\|^2 - \frac{2}{\beta}g_{\mathcal{X}}(x_s)^\top(x_s - x^*) + \frac{1}{\beta^2}\|g_{\mathcal{X}}(x_s)\|^2 \le \|x_s - x^*\|^2.$$

## 3.3 Conditional gradient descent, aka Frank-Wolfe

We describe now an alternative algorithm to minimize a smooth convex function $f$ over a compact convex set $\mathcal{X}$. The conditional gradient descent, introduced in Frank and Wolfe [1956], performs the following update for $t \ge 1$, where $(\gamma_s)_{s \ge 1}$ is a fixed sequence:

$$y_t \in \arg\min_{y \in \mathcal{X}} \nabla f(x_t)^\top y \tag{3.8}$$
$$x_{t+1} = (1 - \gamma_t)x_t + \gamma_t y_t. \tag{3.9}$$

In words conditional gradient descent makes a step in the steepest descent direction given the constraint set $\mathcal{X}$. From a computational perspective, a key property of this scheme is that it replaces the projection step of projected gradient descent by a linear optimization over $\mathcal{X}$, which in some cases can be a much simpler problem.

**Theorem 3.8.** Let $f$ be a convex and $\beta$-smooth function w.r.t. some norm $\|\cdot\|$, $R = \sup_{x,y \in \mathcal{X}} \|x - y\|$, and $\gamma_s = \frac{2}{s+1}$ for $s \ge 1$. Then for any $t \ge 2$, one has

$$f(x_t) - f(x^*) \le \frac{2\beta R^2}{t + 1}.$$

*Proof.* The following inequalities hold true, using respectively $\beta$-smoothness, the definition of $x_{s+1}$, the definition of $y_s$, and the convexity of $f$:

$$f(x_{s+1}) - f(x_s) \le \nabla f(x_s)^\top(x_{s+1} - x_s) + \frac{\beta}{2}\|x_{s+1} - x_s\|^2 \le \gamma_s \nabla f(x_s)^\top(y_s - x_s) + \frac{\beta}{2}\gamma_s^2 R^2 \le \gamma_s \nabla f(x_s)^\top(x^* - x_s) + \frac{\beta}{2}\gamma_s^2 R^2 \le \gamma_s(f(x^*) - f(x_s)) + \frac{\beta}{2}\gamma_s^2 R^2.$$

Rewriting this inequality in terms of $\delta_s = f(x_s) - f(x^*)$ one obtains

$$\delta_{s+1} \le (1 - \gamma_s)\delta_s + \frac{\beta}{2}\gamma_s^2 R^2.$$

A simple induction using that $\gamma_s = \frac{2}{s+1}$ finishes the proof.

In addition to being projection-free and "norm-free", the conditional gradient descent satisfies a perhaps even more important property: it produces sparse iterates.

## 3.4 Strong convexity

We will now discuss another property of convex functions that can significantly speed-up the convergence of first order methods: strong convexity. We say that $f : \mathcal{X} \to \mathbb{R}$ is $\alpha$-strongly convex if it satisfies the following improved subgradient inequality:

$$f(x) - f(y) \le \nabla f(x)^\top(x - y) - \frac{\alpha}{2}\|x - y\|^2. \tag{3.13}$$

It is immediate to verify that a function $f$ is $\alpha$-strongly convex if and only if $x \mapsto f(x) - \frac{\alpha}{2}\|x\|^2$ is convex (in particular if $f$ is twice differentiable then the eigenvalues of the Hessians of $f$ have to be larger than $\alpha$).

### 3.4.1 Strongly convex and Lipschitz functions

We consider here the projected subgradient descent algorithm with time-varying step size $(\eta_t)_{t \ge 1}$.

**Theorem 3.9.** Let $f$ be $\alpha$-strongly convex and $L$-Lipschitz on $\mathcal{X}$. Then projected subgradient descent with $\eta_s = \frac{2}{\alpha(s+1)}$ satisfies

$$f\left(\sum_{s=1}^{t} \frac{2s}{t(t+1)} x_s\right) - f(x^*) \le \frac{2L^2}{\alpha(t+1)}.$$

### 3.4.2 Strongly convex and smooth functions

As we will see now, having both strong convexity and smoothness allows for a drastic improvement in the convergence rate. We denote $\kappa = \frac{\beta}{\alpha}$ for the condition number of $f$. The key observation is that Lemma 3.6 can be improved to:

$$f(x^+) - f(y) \le g_{\mathcal{X}}(x)^\top(x - y) - \frac{1}{2\beta}\|g_{\mathcal{X}}(x)\|^2 - \frac{\alpha}{2}\|x - y\|^2. \tag{3.14}$$

**Theorem 3.10.** Let $f$ be $\alpha$-strongly convex and $\beta$-smooth on $\mathcal{X}$. Then projected gradient descent with $\eta = \frac{1}{\beta}$ satisfies for $t \ge 0$,

$$\|x_{t+1} - x^*\|^2 \le \exp\left(-\frac{t}{\kappa}\right)\|x_1 - x^*\|^2.$$

**Lemma 3.11.** Let $f$ be $\beta$-smooth and $\alpha$-strongly convex on $\mathbb{R}^n$. Then for all $x, y \in \mathbb{R}^n$, one has

$$(\nabla f(x) - \nabla f(y))^\top(x - y) \ge \frac{\alpha\beta}{\beta + \alpha}\|x - y\|^2 + \frac{1}{\beta + \alpha}\|\nabla f(x) - \nabla f(y)\|^2.$$

**Theorem 3.12.** Let $f$ be $\beta$-smooth and $\alpha$-strongly convex on $\mathbb{R}^n$. Then gradient descent with $\eta = \frac{2}{\alpha + \beta}$ satisfies

$$f(x_{t+1}) - f(x^*) \le \frac{\beta}{2}\exp\left(-\frac{4t}{\kappa + 1}\right)\|x_1 - x^*\|^2.$$

## 3.5 Lower bounds

We prove here various oracle complexity lower bounds.

**Theorem 3.13.** Let $t \le n$, $L, R > 0$. There exists a convex and $L$-Lipschitz function $f$ such that for any black-box procedure satisfying (3.15),

$$\min_{1 \le s \le t} f(x_s) - \min_{x \in B_2(R)} f(x) \ge \frac{RL}{2(1 + \sqrt{t})}.$$

There also exists an $\alpha$-strongly convex and $L$-Lipschitz function $f$ such that for any black-box procedure satisfying (3.15),

$$\min_{1 \le s \le t} f(x_s) - \min_{x \in B_2(L/(2\alpha))} f(x) \ge \frac{L^2}{8\alpha t}.$$

**Theorem 3.14.** Let $t \le (n-1)/2$, $\beta > 0$. There exists a $\beta$-smooth convex function $f$ such that for any black-box procedure satisfying (3.15),

$$\min_{1 \le s \le t} f(x_s) - f(x^*) \ge \frac{3\beta}{32} \frac{\|x_1 - x^*\|^2}{(t+1)^2}.$$

**Theorem 3.15.** Let $\kappa > 1$. There exists a $\beta$-smooth and $\alpha$-strongly convex function $f : \ell_2 \to \mathbb{R}$ with $\kappa = \beta/\alpha$ such that for any $t \ge 1$ and any black-box procedure satisfying (3.15) one has

$$f(x_t) - f(x^*) \ge \frac{\alpha}{2}\left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^{2(t-1)}\|x_1 - x^*\|^2.$$

Note that for large values of the condition number $\kappa$ one has

$$\left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^{2(t-1)} \approx \exp\left(-\frac{4(t-1)}{\sqrt{\kappa}}\right).$$

## 3.6 Geometric descent

So far our results leave a gap in the case of smooth optimization: gradient descent achieves an oracle complexity of $O(1/\varepsilon)$ (respectively $O(\kappa \log(1/\varepsilon))$ in the strongly convex case) while we proved a lower bound of $\Omega(1/\sqrt{\varepsilon})$ (respectively $\Omega(\sqrt{\kappa} \log(1/\varepsilon))$). In this section we close these gaps with the geometric descent method.

### 3.6.1 Warm-up: a geometric alternative to gradient descent

Let $B(x, r^2) := \{y \in \mathbb{R}^n : \|y - x\|^2 \le r^2\}$, and

$$x^+ = x - \frac{1}{\beta}\nabla f(x), \quad x^{++} = x - \frac{1}{\alpha}\nabla f(x).$$

Rewriting the definition of strong convexity (3.13) one obtains an enclosing ball for the minimizer of $f$:

$$x^* \in B\left(x^{++}, \frac{\|\nabla f(x)\|^2}{\alpha^2} - \frac{2}{\alpha}(f(x) - f(x^*))\right).$$

Furthermore recall that by smoothness one has $f(x^+) \le f(x) - \frac{1}{2\beta}\|\nabla f(x)\|^2$ which allows to shrink the above ball by a factor of $1 - \frac{1}{\kappa}$:

$$x^* \in B\left(x^{++}, \frac{\|\nabla f(x)\|^2}{\alpha^2}\left(1 - \frac{1}{\kappa}\right) - \frac{2}{\alpha}(f(x^+) - f(x^*))\right) \tag{3.16}$$

**Lemma 3.16.** Let $a \in \mathbb{R}^n$ and $\varepsilon \in (0,1)$, $g \in \mathbb{R}_+$. Assume that $\|a\| \ge g$. Then there exists $c \in \mathbb{R}^n$ such that for any $\delta \ge 0$,

$$B(0, 1 - \varepsilon g^2 - \delta) \cap B(a, g^2(1 - \varepsilon) - \delta) \subset B(c, 1 - \sqrt{\varepsilon} - \delta).$$

### 3.6.3 The geometric descent method

Let $x_0 \in \mathbb{R}^n$, $c_0 = x_0^{++}$, and $R_0^2 = (1 - \frac{1}{\kappa})\frac{\|\nabla f(x_0)\|^2}{\alpha^2}$. For any $t \ge 0$ let

$$x_{t+1} = \arg\min_{x \in \{(1-\lambda)c_t + \lambda x_t^+, \lambda \in \mathbb{R}\}} f(x),$$

and $c_{t+1}$ (respectively $R_{t+1}^2$) be the center (respectively the squared radius) of the ball given by Lemma 3.16.

**Theorem 3.17.** For any $t \ge 0$, one has $x^* \in B(c_t, R_t^2)$, $R_{t+1}^2 \le (1 - \frac{1}{\sqrt{\kappa}})R_t^2$, and thus

$$\|x^* - c_t\|^2 \le \left(1 - \frac{1}{\sqrt{\kappa}}\right)^t R_0^2.$$

## 3.7 Nesterov's accelerated gradient descent

We describe here the original Nesterov's method which attains the optimal oracle complexity for smooth convex optimization.

### 3.7.1 The smooth and strongly convex case

Nesterov's accelerated gradient descent can be described as follows: Start at an arbitrary initial point $x_1 = y_1$ and then iterate the following equations for $t \ge 1$:

$$y_{t+1} = x_t - \frac{1}{\beta}\nabla f(x_t),$$
$$x_{t+1} = \left(1 + \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)y_{t+1} - \frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}y_t.$$

**Theorem 3.18.** Let $f$ be $\alpha$-strongly convex and $\beta$-smooth, then Nesterov's accelerated gradient descent satisfies

$$f(y_t) - f(x^*) \le \frac{\alpha + \beta}{2}\|x_1 - x^*\|^2 \exp\left(-\frac{t-1}{\sqrt{\kappa}}\right).$$

*Proof.* We define $\alpha$-strongly convex quadratic functions $\Phi_s$, $s \ge 1$ by induction as follows:

$$\Phi_1(x) = f(x_1) + \frac{\alpha}{2}\|x - x_1\|^2,$$
$$\Phi_{s+1}(x) = \left(1 - \frac{1}{\sqrt{\kappa}}\right)\Phi_s(x) + \frac{1}{\sqrt{\kappa}}\left(f(x_s) + \nabla f(x_s)^\top(x - x_s) + \frac{\alpha}{2}\|x - x_s\|^2\right). \tag{3.17}$$

Intuitively $\Phi_s$ becomes a finer and finer approximation (from below) to $f$ in the following sense:

$$\Phi_{s+1}(x) \le f(x) + \left(1 - \frac{1}{\sqrt{\kappa}}\right)^s(\Phi_1(x) - f(x)). \tag{3.18}$$

The above inequality can be proved immediately by induction, using the fact that by $\alpha$-strong convexity one has

$$f(x_s) + \nabla f(x_s)^\top(x - x_s) + \frac{\alpha}{2}\|x - x_s\|^2 \le f(x).$$

Equation (3.18) by itself does not say much, for it to be useful one needs to understand how "far" below $f$ is $\Phi_s$. The following inequality answers this question:

$$f(y_s) \le \min_{x \in \mathbb{R}^n} \Phi_s(x). \tag{3.19}$$

The rest of the proof is devoted to showing that (3.19) holds true, but first let us see how to combine (3.18) and (3.19) to obtain the rate given by the theorem (we use that by $\beta$-smoothness one has $f(x) - f(x^*) \le \frac{\beta}{2}\|x - x^*\|^2$):

$$f(y_t) - f(x^*) \le \Phi_t(x^*) - f(x^*) \le \left(1 - \frac{1}{\sqrt{\kappa}}\right)^{t-1}(\Phi_1(x^*) - f(x^*)) \le \frac{\alpha + \beta}{2}\|x_1 - x^*\|^2 \left(1 - \frac{1}{\sqrt{\kappa}}\right)^{t-1}.$$

We now prove (3.19) by induction (note that it is true at $s = 1$ since $x_1 = y_1$). Let $\Phi_s^* = \min_{x \in \mathbb{R}^n} \Phi_s(x)$. Using the definition of $y_{s+1}$ (and $\beta$-smoothness), convexity, and the induction hypothesis, one gets

$$f(y_{s+1}) \le f(x_s) - \frac{1}{2\beta}\|\nabla f(x_s)\|^2 = \left(1 - \frac{1}{\sqrt{\kappa}}\right)f(y_s) + \left(1 - \frac{1}{\sqrt{\kappa}}\right)(f(x_s) - f(y_s)) + \frac{1}{\sqrt{\kappa}}f(x_s) - \frac{1}{2\beta}\|\nabla f(x_s)\|^2$$
$$\le \left(1 - \frac{1}{\sqrt{\kappa}}\right)\Phi_s^* + \left(1 - \frac{1}{\sqrt{\kappa}}\right)\nabla f(x_s)^\top(x_s - y_s) + \frac{1}{\sqrt{\kappa}}f(x_s) - \frac{1}{2\beta}\|\nabla f(x_s)\|^2.$$

Thus we now have to show that

$$\Phi_{s+1}^* \ge \left(1 - \frac{1}{\sqrt{\kappa}}\right)\Phi_s^* + \left(1 - \frac{1}{\sqrt{\kappa}}\right)\nabla f(x_s)^\top(x_s - y_s) + \frac{1}{\sqrt{\kappa}}f(x_s) - \frac{1}{2\beta}\|\nabla f(x_s)\|^2. \tag{3.20}$$

To prove this inequality we have to understand better the functions $\Phi_s$. First note that $\nabla^2\Phi_s(x) = \alpha I_n$ (immediate by induction) and thus $\Phi_s$ has to be of the following form:

$$\Phi_s(x) = \Phi_s^* + \frac{\alpha}{2}\|x - v_s\|^2,$$

for some $v_s \in \mathbb{R}^n$. Now observe that by differentiating (3.17) and using the above form of $\Phi_s$ one obtains

$$\nabla\Phi_{s+1}(x) = \alpha\left(1 - \frac{1}{\sqrt{\kappa}}\right)(x - v_s) + \frac{1}{\sqrt{\kappa}}\nabla f(x_s) + \frac{\alpha}{\sqrt{\kappa}}(x - x_s).$$

In particular $\Phi_{s+1}$ is by definition minimized at $v_{s+1}$ which can now be defined by induction:

$$v_{s+1} = \left(1 - \frac{1}{\sqrt{\kappa}}\right)v_s + \frac{1}{\sqrt{\kappa}}x_s - \frac{1}{\alpha\sqrt{\kappa}}\nabla f(x_s). \tag{3.21}$$

Using the form of $\Phi_s$ and $\Phi_{s+1}$, as well as the original definition (3.17) one gets the following identity by evaluating $\Phi_{s+1}$ at $x_s$:

$$\Phi_{s+1}^* + \frac{\alpha}{2}\|x_s - v_{s+1}\|^2 = \left(1 - \frac{1}{\sqrt{\kappa}}\right)\Phi_s^* + \frac{\alpha}{2}\left(1 - \frac{1}{\sqrt{\kappa}}\right)\|x_s - v_s\|^2 + \frac{1}{\sqrt{\kappa}}f(x_s). \tag{3.22}$$

Note that thanks to (3.21) one has

$$\|x_s - v_{s+1}\|^2 = \left(1 - \frac{1}{\sqrt{\kappa}}\right)^2\|x_s - v_s\|^2 + \frac{1}{\alpha^2\kappa}\|\nabla f(x_s)\|^2 - \frac{2}{\alpha\sqrt{\kappa}}\left(1 - \frac{1}{\sqrt{\kappa}}\right)\nabla f(x_s)^\top(v_s - x_s),$$

which combined with (3.22) yields

$$\Phi_{s+1}^* = \left(1 - \frac{1}{\sqrt{\kappa}}\right)\Phi_s^* + \frac{1}{\sqrt{\kappa}}f(x_s) + \frac{\alpha}{2\sqrt{\kappa}}\left(1 - \frac{1}{\sqrt{\kappa}}\right)\|x_s - v_s\|^2 - \frac{1}{2\beta}\|\nabla f(x_s)\|^2 + \frac{1}{\sqrt{\kappa}}\left(1 - \frac{1}{\sqrt{\kappa}}\right)\nabla f(x_s)^\top(v_s - x_s).$$

Finally we show by induction that $v_s - x_s = \sqrt{\kappa}(x_s - y_s)$, which concludes the proof of (3.20) and thus also concludes the proof of the theorem:

$$v_{s+1} - x_{s+1} = \left(1 - \frac{1}{\sqrt{\kappa}}\right)v_s + \frac{1}{\sqrt{\kappa}}x_s - \frac{1}{\alpha\sqrt{\kappa}}\nabla f(x_s) - x_{s+1} = \sqrt{\kappa}x_s - (\sqrt{\kappa} - 1)y_s - \frac{\sqrt{\kappa}}{\beta}\nabla f(x_s) - x_{s+1} = \sqrt{\kappa}y_{s+1} - (\sqrt{\kappa} - 1)y_s - x_{s+1} = \sqrt{\kappa}(x_{s+1} - y_{s+1}),$$

where the first equality comes from (3.21), the second from the induction hypothesis, the third from the definition of $y_{s+1}$ and the last one from the definition of $x_{s+1}$.

---

*[End of extracted section containing Theorem 3.18]*
