# All Mathematical Statements from 18.103 Fourier Analysis

## Lecture 1: Introduction

### Theorem (Parseval's formula)
$$\sum |c_n|^2 = \frac{1}{2\pi} \int_{-\pi}^{\pi} |f(x)|^2 dx$$

### Strong Law of Large Numbers
With probability 1, $\lim_{n\to\infty} \frac{S_n}{n} = 0$

## Fourier Series, Part 1

### Proposition 1 (Fourier coefficient decay for C^1)
If $f \in C^1(\mathbf{T})$, then $|\hat{f}(n)| \le C/|n|$.

### Lemma 1 (Riemann-Lebesgue Lemma)
Suppose that $h \in L^1(\mathbf{T})$. Then $\hat{h}(n) \to 0$ as $|n| \to \infty$.

### Theorem 1 (Dini Test)
If $f \in L^1(\mathbf{T})$, and for some fixed x, $\int_{-\pi}^{\pi} \frac{|f(x+y) - f(x)|}{|y|} dy < \infty$, then $s_N(x) \to f(x)$ as $N \to \infty$.

### Corollary 1 (Pointwise and Lp convergence for C^1)
If $f \in C^1(\mathbf{T})$, then (a) $s_N(x) \to f(x)$ as $N \to \infty$ for all $x \in \mathbf{T}$; (b) $||s_N - f||_p \to 0$ as $N \to \infty$, $1 \le p < \infty$.

### Corollary 2 (Orthonormal basis for L^2(T))
The functions $e^{inx}$, $n \in \mathbb{Z}$ form an orthonormal basis for $L^2(\mathbb{T})$. In particular, for all $f \in L^2(\mathbb{T})$, $\lim_{N \to \infty} ||s_N - f||_2 = 0$ and $||f||_2^2 = \sum_{n \in \mathbf{Z}} |\hat{f}(n)|^2$.

## Fourier Series, Part 2

### Theorem 1 (Fejer's Theorem)
Let f be continuous on $\mathbb{R}$ and periodic of period $2\pi$. Then $\max_{x} |\sigma_N(x) - f(x)| \to 0$ as $N \to \infty$ where $\sigma_N(x) = (s_0(x) + \dots + s_{N-1}(x))/N$.

### Corollary 1 (Density of trigonometric polynomials in C(T))
Trigonometric polynomials are dense in continuous, periodic of $2\pi$ functions in the uniform norm.

### Lemma 1 (Approximate Identity Lemma for periodic functions)
Let $f \in C(\mathbb{R}/2\pi\mathbb{Z})$ and let $K_N(x)$ satisfy (i) $\frac{1}{2\pi}\int K_N = 1$, (ii) $\sup_N \int |K_N| \le M$, (iii) for any $\delta > 0$, $\int_{\delta \le |x| \le \pi} |K_N(x)| dx \to 0$ as $N \to \infty$. Then $\max_x |f(x) - f * K_N(x)| \to 0$ as $N \to \infty$.

## Fourier Series, Continued (Part 3)

### Proposition 1 (Young's inequality for convolution on T)
If f and g belong to $L^1(\mathbf{T})$, then $f * g \in L^1(\mathbf{T})$ and $||f * g||_p \le ||f||_p ||g||_1$.

### Theorem 1 (L^1 convergence of Cesaro means)
Let $f \in L^1(\mathbf{T})$. Then $\lim_{N\to\infty} \|f - \sigma_N f\|_1 = 0$. In particular, trigonometric polynomials are dense in $L^1(\mathbf{T})$.

### Corollary 1 (Uniqueness of Fourier Series)
If $f \in L^1(\mathbf{T})$ and $\hat{f}(n) = 0$ for all n, then f(x) = 0 for almost every x.

### Proposition 2 (Fourier transform of derivative)
If $f \in C^1(\mathbf{R}/2\pi \mathbf{Z})$, then $\widehat{f'}(n) = in\widehat{f}(n)$.

### Theorem 2 (Weyl equidistribution theorem)
If $\alpha$ is irrational, and $0 \le a < b \le 1$, then $\lim_{N \to \infty} \frac{\#\{m: 0 \le m \le N-1, a \le \{m\alpha\} \le b\}}{N} = b-a$.

## Fourier Integrals on L^2(R) and L^1(R)

### Theorem 1 (Fourier inversion on Schwartz class)
If $f \in \mathcal{S}(\mathbb{R})$, then $\hat{f} \in \mathcal{S}(\mathbb{R})$ and $f(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \hat{f}(\xi) e^{ix\xi} d\xi$.

### Corollary 1 (Plancherel identity on Schwartz class)
If $f \in \mathcal{S}(\mathbb{R})$, then $2\pi \int_{\mathbb{R}} |f(x)|^2 dx = \int_{\mathbb{R}} |\hat{f}(\xi)|^2 d\xi$.

### Corollary 2 (Extension of Fourier transform to L^2)
Let $f \in L^2(\mathbb{R})$ and let $f_j \in \mathcal{S}(\mathbb{R})$ be such that $||f - f_j||_2 \to 0$. Then there is a unique $\hat{f} \in L^2(\mathbb{R})$ for which $\lim_{j \to \infty} \|\hat{f} - \hat{f}_j\|_2 = 0$. Furthermore, $\|\hat{f}\|_2^2 = 2\pi \|f\|_2^2$.

### Corollary 3 (Injectivity of Fourier transform on L^2)
If $f \in L^2(\mathbb{R})$ and $\hat{f} = 0$ almost everywhere, then f = 0.

### Corollary 4 (Fourier inversion on L^2)
Let $\mathcal{G}(f)(x) = \frac{1}{2\pi}\hat{f}(-x)$. Then for all $f \in L^2(\mathbb{R})$, $\mathcal{G} \circ \mathcal{F}(f) = \mathcal{F} \circ \mathcal{G}(f) = f$.

### Proposition 1 (Consistency of L^1 and L^2 Fourier transforms)
If $f \in L^2(\mathbb{R}) \cap L^1(\mathbb{R})$, then the definition by continuity in Corollary 2 for $\hat{f}$ coincides with the definition by integration.

### Theorem 2 (Fourier inversion via partial sums on L^2)
Suppose that $f \in L^2(\mathbb{R})$. Then $s_N(x) = \frac{1}{2\pi} \int_{-N}^{N} \hat{f}(\xi) e^{ix\xi} d\xi$ satisfies $\lim_{N \to \infty} \|f - s_N\|_{L^2} = 0$.

### Proposition 2 (Consistency of L^1 and L^2 inverse Fourier transforms)
If $h \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$, then the inverse Fourier transform obtained by continuity in the $L^2$ norm coincides with the $L^1$ definition.

### Theorem 3 (Cesaro inversion on L^1(R))
Let $f \in L^1(\mathbb{R})$ and denote $\sigma_N(x) = \frac{1}{2\pi} \int_{-N}^{N} (1 - |\xi/N|)^+ \hat{f}(\xi) e^{ix\xi} d\xi$. Then $\lim_{N\to\infty} \|f - \sigma_N\|_{L^1} = 0$.

### Corollary 5 (Injectivity of Fourier transform on L^1)
If $f \in L^1(\mathbb{R})$ and $\hat{f} = 0$, then f = 0.

### Theorem 4 (Approximate identity on R)
If $K \in L^1(\mathbb{R})$, $K_{\epsilon}(x) = (1/\epsilon)K(x/\epsilon)$, and $\int K(x) dx = 1$, then $||K_{\epsilon} * f - f||_1 \to 0$ for all $f \in L^1(\mathbb{R})$.

## Fourier Integrals of finite measures

### Proposition 1 (Fourier transform of finite measures is bounded continuous)
For $\mu \in M_+(\mathbb{R})$, define $\hat{\mu}(\xi) = \int_{\mathbb{R}} e^{-ix\xi} d\mu(x)$. Then $\mathcal{F}: M_+(\mathbb{R}) \to C_b(\mathbb{R})$.

### Theorem 1 (Uniqueness of Fourier transform of measures)
Let $\mu \in M_+(\mathbb{R})$. Then $\mu$ is uniquely determined by $\hat{\mu}$.

### Proposition 2 (Weak convergence via Fourier transforms)
If $\mu_j$ and $\mu$ belong to $M^+(\mathbb{R})$, and for each $\xi$, $\lim_{j\to\infty}\hat{\mu}_j(\xi)=\hat{\mu}(\xi)$, then $\lim_{j \to \infty} \int f d\mu_j = \int f d\mu$ for all $f \in \mathcal{S}(\mathbb{R})$.

### Proposition 3 (Portmanteau-type result for weak convergence)
If $\lim_{j \to \infty} \int f d\mu_j = \int f d\mu$ for all $f \in C_0^{\infty}(\mathbb{R})$, then $\limsup_{j \to \infty} \mu_j((a, b)) \le \mu([a, b])$ and $\liminf_{j \to \infty} \mu_j((a, b)) \ge \mu((a, b))$. In particular if $\mu$ is continuous then $\mu_j((a,b)) \to \mu((a,b))$.

### Theorem 2 (Central Limit Theorem)
Let $X_1, X_2, \ldots$ be independent, identically distributed random variables such that $\mathbb{E}(X_1) = M$, $\mathbb{E}[(X_1 - M)^2] = \sigma^2$, $\mathbb{E}(|X_1|^{2+\alpha}) = A < \infty$ for some $\alpha > 0$. Then $\mathbb{E}\left(a < \frac{X_1 + \dots + X_n - nM}{\sqrt{n}} < b\right) \longrightarrow \int_a^b g_\sigma(x) dx$.

### Lemma 1 (Taylor expansion of exponential)
$e^{ix} = 1 + ix + (ix)^2/2 + R(x)$ with $|R(x)| \le 4\min(|x|^2, |x|^3) \le 4|x|^{2+\alpha}$ for all $\alpha$, $0 < \alpha < 1$.

## Tempered distributions

### Proposition 4 (Fourier inversion on S'(R))
If $T \in \mathcal{S}'(\mathbb{R})$, define S by $S(\varphi) = T(\check{\varphi})$. Then $S \in \mathcal{S}'(\mathbb{R})$ and $\hat{S} = T$. The mapping $T \mapsto \check{T}$ inverts the Fourier transform on $\mathcal{S}'(\mathbb{R})$.

## Orthonormal Bases

### Proposition 1 (Continuity of inner product)
If $||u_n - u|| \to 0$ and $||v_n - v|| \to 0$, then $||u_n|| \to ||u||$ and $\langle u_n, v_n \rangle \to \langle u, v \rangle$.

### Theorem 1 (Characterization of orthonormal bases in Hilbert spaces)
Suppose that $\varphi_n$ is an orthonormal sequence in a Hilbert space H. The following are equivalent: (a) V is dense in H, (b) If $\langle f, \varphi_n \rangle = 0$ for all n then f = 0, (c) $||s_N - f|| \to 0$, (d) $||f||^2 = \sum |\langle f, \varphi_n \rangle|^2$.

### Proposition 2 (Convergence and inner product of orthonormal expansions)
Let $\varphi_n$ be an orthonormal sequence in a Hilbert space H, with $\sum |a_n|^2 < \infty$ and $\sum |b_n|^2 < \infty$. Then $u = \sum a_n \varphi_n$ and $v = \sum b_n \varphi_n$ converge in H norm and $\langle u, v \rangle = \sum a_n \overline{b_n}$.

### Polarization Formula
$\langle u, v \rangle = a_1 \|u + iv\|^2 + a_2 \|u + v\|^2 + a_3 \|u\|^2 + a_4 \|v\|^2$ with $a_1 = i/2$, $a_2 = 1/2$, $a_3 = -(1+i)/2$, $a_4 = -(i+1)/2$.

## Completeness of L^p

### Theorem 1 (L^p is a Banach space)
For $1 \leq p < \infty$, $L^p(X, \mu)$ is a Banach space.

### Theorem 2 (Density of C_0^infty in L^p)
$C_0^{\infty}(\mathbf{R}^n)$ is dense in $L^p(\mathbf{R}^n)$ for $1 \leq p < \infty$.

## Brownian Motion

### Theorem 1 (Finite-dimensional distributions of rescaled random walk)
Let $0 \le t_0 < t_1 < \dots < t_m$ and let $\sigma_j^2 = t_j - t_{j-1}$. Then $\lim_{n \to \infty} P[(f_n(t_1) - f_n(t_0), \dots, f_n(t_m) - f_n(t_{m-1})) \in I_1 \times \dots \times I_m] = \int_{I_1 \times \dots \times I_m} \prod_{j=1}^m g_{\sigma_j}(x_j) dx_1 \cdots dx_m$.

### Theorem 2 (Wiener's construction of Brownian motion)
Let $W(t) = c_0 a_0 t + c_1 \sum_{k=1}^{\infty} a_k \frac{\sin kt}{k}$ with $c_0 = \sqrt{1/\pi}$ and $c_1 = \sqrt{2/\pi}$. Then (a) B(t) = W(t) satisfies the Brownian motion finite-dimensional distributions on $0 \le t \le \pi$; (b) W is almost surely continuous in t.

### Proposition 1 (Sum of independent Gaussians)
If $X_k$ are independent gaussians with mean 0 and variance $\sigma_k^2$ with $\sum_k \sigma_k^2 < \infty$, then $X_1 + X_2 + \cdots$ converges in $L^2(\Omega)$ to a gaussian random variable with mean zero and variance $\sigma^2 = \sum_k \sigma_k^2$.

### Lemma 1 (Characterization of multivariate Gaussian by linear combinations)
Let $X = (X_1, \ldots, X_m)$ be independent gaussians with mean zero, A an invertible matrix, and $Y_j = \sum_k a_{jk} X_k$. Then $a \cdot Y$ is gaussian with mean 0 for every $a$. Conversely, if Z has the same property and same covariances as Y, then Z has the same joint distribution as Y.

### Proposition 2 (Characterization of Brownian motion by covariance)
Suppose B(t) satisfies B(0) = 0. Then B satisfies the Brownian motion finite-dimensional distributions if and only if (a) $\sum \xi_j B(t_j)$ is Gaussian with mean 0, and (b) $\mathbb{E}(B(s)B(t)) = s \wedge t$.

### Lemma 2 (Fourth moment bound for Gaussians)
If $a_k$ are mean zero variance 1 gaussians, then $\mathbb{E}(|a_{i_1}a_{i_2}a_{i_3}a_{i_4}|) \le \mathbb{E}(|a_1|^4) = 3 < \infty$.

### Lemma 3 (Beta integral bound)
For $m \ge 1$ and $0 \le \beta \le 2$, $R_{\beta}(m) = \int_{0}^{1} r^{m} (1-r)^{\beta} dr \leq 100 m^{-1-\beta}$.

### Lemma 4 (Integrability of gradient of random power series)
For any $\beta > 1$, $\mathbb{E} \int_{0}^{2\pi} \int_{0}^{1} |\nabla F(re^{it})|^{4} (1-r)^{\beta} r dr dt < \infty$, and consequently $\int_0^{2\pi} \int_0^1 |\nabla F(re^{it})|^4 (1-r)^\beta r dr dt < \infty$ almost surely.

### Lemma 5 (Holder continuity from gradient bound)
If F satisfies $|\nabla F(z)| \le C(1-|z|)^{-1+\alpha}$ on $|z| \leq 1$, for some $\alpha$, $0 < \alpha \leq 1$, then $F(e^{it})$ is Holder continuous with exponent $\alpha$: $|F(e^{it_1}) - F(e^{it_2})| \le C|t_1 - t_2|^{\alpha}$.
