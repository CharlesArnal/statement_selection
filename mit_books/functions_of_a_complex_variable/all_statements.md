# All Mathematical Statements in "Functions of a Complex Variable" (18.112)

## Lecture 2: Exponential function & Logarithm for a complex argument

**Theorem 1** (Lecture 2):
$b^x = E(xL(b))$ for all $x \in \mathbb{R}$, where $L(x) = \int_1^x \frac{dt}{t}$ and $E$ is the inverse of $L$.

**Corollary 1** (Lecture 2):
For any $b > 0$, $x, y \in \mathbb{R}$, we have $b^{x+y} = b^x b^y$.

**Proposition 1** (Lecture 2):
$e^{z+w} = e^z e^w$ for all $z, w \in \mathbb{C}$.

**Theorem 2** (Lecture 2):
The roots of $z^n = 1$ are $1, \omega, \omega^2, \cdots, \omega^{n-1}$, where $\omega = \cos\frac{2\pi}{n} + i\sin\frac{2\pi}{n}$.

**Theorem 3** (Lecture 2):
In the slit plane, $\operatorname{Log}(z_1z_2) = \operatorname{Log}(z_1) + \operatorname{Log}(z_2) + n \cdot 2\pi i$, where $n = 0$ or $\pm 1$, and $n = 0$ if $-\pi < \operatorname{Arg}(z_1) + \operatorname{Arg}(z_2) < \pi$.

## Lecture 3: Analytic Functions; Rational Functions

**Theorem 1** (Lecture 3, Gauss-Lucas, stronger version):
The smallest convex set which contains all the zeros of $P(z)$ also contains the zeros of $P'(z)$.

**Proposition 1** (Lecture 3):
Given $a_1, \dots, a_n \in \mathbb{C}$, the set $\{\sum_{i=1}^{n} m_i a_i \mid m_i \ge 0, \sum_{i=1}^{n} m_i = 1\}$ is the convex hull of $a_1, \dots, a_n$.

## Lecture 6: Conformal Maps; Linear Transformations

**Theorem 1** (Lecture 6):
If $A$ and $B$ are two nonintersecting circles, there exists a linear transformation mapping $A$ and $B$ into concentric circles.

## Lecture 8: Line Integrals

**Theorem 1** (Lecture 8, integration by substitution):
Let $w = \varphi(z)$ be a holomorphic function on a region $\Omega$. Let $\gamma$ be a curve in $\Omega$, then $\int_{\varphi(\gamma)} f(w)\, dw = \int_{\gamma} f(\varphi(z)) \varphi'(z)\, dz$.

**Theorem 2** (Lecture 8):
Let $R$ be a rational function on $\mathbb{C}$. Then $\int_{\gamma} R(z^2)\, dz = 0$ for every circle $\gamma$ around the origin provided $R(z^2) \neq 0$ on $\gamma$.

## Lecture 10: The Special Cauchy's Formula and Applications

**Theorem 1** (Lecture 10, Taylor's Theorem):
If $f(z)$ is analytic in a region $\Omega$ containing $a$, one has $f(z) = f(a) + \frac{f'(a)}{1!}(z-a) + \dots + \frac{f^{(n-1)}(a)}{(n-1)!}(z-a)^{n-1} + f_n(z)(z-a)^n$, where $f_n(z)$ is analytic in $\Omega$. Moreover, if $C$ is the boundary of a closed disk contained in $\Omega$ with center $a$, then $f_n(z) = \frac{1}{2\pi i} \int_C \frac{f(\zeta)\, d\zeta}{(\zeta - a)^n (\zeta - z)}$ for $z$ inside $C$.

## Lecture 11: Isolated Singularities

**Theorem 9** (Lecture 11, Casorati-Weierstrass):
A holomorphic function comes arbitrarily close to any complex value in every neighborhood of an essential singularity.

## Lecture 13: The General Cauchy Theorem

**Theorem 1** (Lecture 13, Cauchy's Theorem):
If $f$ is analytic in an open set $\Omega$, then $\int_{\gamma} f(z)\, dz = 0$ for every closed curve $\gamma \subset \Omega$ such that $\gamma \sim 0$ (homologous to zero). In particular, if $\Omega$ is simply connected then $\int_{\gamma} f(z)\, dz = 0$ for every closed $\gamma \subset \Omega$.

**Theorem 2** (Lecture 13, Cauchy's Integral Formula):
Let $f$ be holomorphic in an open set $\Omega$. Then $n(\gamma, z)f(z) = \frac{1}{2\pi i} \int_{\gamma} \frac{f(\zeta)}{\zeta - z}\, d\zeta$ where $\gamma \sim 0$ with respect to $\Omega$.

## Lecture 14: The Residue Theorem and Application

**Theorem 17'** (Lecture 14, Residue Theorem):
Let $f$ be analytic except for isolated singularities $a_j$ in a region $\Omega$. Let $\gamma$ be a simple closed curve which has interior contained in $\Omega$ and $a_j \notin \gamma$ (all $j$). Then $\frac{1}{2\pi i} \int_{\gamma} f(z)\, dz = \sum_{i} \operatorname{Res}_{z=a_i} f(z)$, where the sum ranges over all $a_i$ inside $\gamma$.

**Theorem 18'** (Lecture 14, Argument Principle):
Let $f(z)$ be meromorphic in $\Omega$, $\gamma \subset \Omega$ a simple closed curve with interior inside $\Omega$. Assume $\gamma$ passes through no zeros nor poles of $f$. Then $\frac{1}{2\pi i} \int_{\gamma} \frac{f'(z)}{f(z)}\, dz = N - P$, where $N$ is the number of zeros, $P$ the number of poles inside $\gamma$, all counted with multiplicity.

**Corollary 1** (Lecture 14, Rouche's Theorem):
Let $f$ and $g$ be holomorphic in a region $\Omega$. Let $\gamma$ be a simple closed curve in $\Omega$ with interior $\subset \Omega$. Assume $|f(z) - g(z)| < |f(z)|$ on $\gamma$. Then $f$ and $g$ have the same number of zeros inside $\gamma$.

## Lecture 16: Harmonic Functions

**Theorem 1** (Lecture 16):
If $\Omega$ is simply connected and $u$ harmonic in $\Omega$, there exists a holomorphic function $f(z)$ such that $u(z) = \operatorname{Re} f(z)$.

**Corollary 1** (Lecture 16, Mean value property):
If $u$ is harmonic in $\Omega$, then if the disk $|z - z_0| \le r$ lies in $\Omega$, $u(z_0) = \frac{1}{2\pi} \int_0^{2\pi} u(z_0 + re^{i\theta})\, d\theta$.

**Theorem 20** (Lecture 16):
If $u$ is harmonic in $\Omega$, and $\{z : r_1 \leq |z - z_0| \leq r_2\} \subset \Omega$, then $\frac{1}{2\pi} \int_0^{2\pi} u(z_0 + re^{i\theta})\, d\theta = \alpha \log r + \beta$ for $r_1 \le r \le r_2$, where $\alpha$ and $\beta$ are constants.

**Theorem 2** (Lecture 16, Schwarz' Theorem / Poisson integral):
Let $U$ be a real piecewise continuous function on $|z| = 1$ and define the Poisson integral $u(z) = P_U(z)$ by $u(a) = \frac{1}{2\pi} \int_0^{2\pi} \frac{1 - |a|^2}{|a - e^{i\varphi}|^2} U(e^{i\varphi})\, d\varphi$ for $|a| < 1$. Then $u$ is harmonic, and $\lim_{z \to e^{i\varphi_0}} u(z) = U(e^{i\varphi_0})$ if $U$ is continuous at $e^{i\varphi_0}$.

## Lecture 17: Mittag-Leffler's Theorem

**Theorem 1** (Lecture 17, Mittag-Leffler's Theorem):
Let $\{b_{\nu}\}$ be a sequence in $\mathbb{C}$ such that $\lim_{\nu \to \infty} b_{\nu} = \infty$, and $P_{\nu}(\zeta)$ polynomials without constant term. Then there exist functions $f$ meromorphic in $\mathbb{C}$ with poles at just the points $b_{\nu}$ and corresponding singular parts $P_{\nu}\left(\frac{1}{z-b_{\nu}}\right)$. The most general $f(z)$ of this kind can be written $f(z) = g(z) + \sum_{\nu} \left[ P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) - p_{\nu}(z) \right]$ where $g$ is holomorphic and the $p_{\nu}$ are polynomials.

**Lemma 1** (Lecture 17, Abel's summation / Dirichlet's test):
If $(A_n)$ is bounded, $v_n \to 0$, and $\sum_{n=1}^{\infty} |v_n - v_{n+1}| < \infty$, then $\sum_{n=0}^{\infty} a_n v_n$ converges.

## Lecture 19: Normal Families

**Theorem 1** (Lecture 19, Montel's Theorem):
Let $\Omega \subset \mathbb{C}$ be a region, $\mathcal{F}$ a family of holomorphic functions on $\Omega$ such that for each compact $E \subset \Omega$, $\mathcal{F}$ is uniformly bounded on $E$. Then $\mathcal{F}$ has a subsequence converging uniformly on each compact subset of $\Omega$.

## Lectures 21-22: The Prime Number Theorem

**Theorem 1** (Lectures 21-22, Analytic Theorem / Newman's Tauberian Theorem):
Let $f(t)$ ($t \ge 0$) be bounded and locally integrable and assume the function $g(z) = \int_0^\infty e^{-zt} f(t)\, dt$ (for $\operatorname{Re}(z) > 0$) extends to a holomorphic function on $\operatorname{Re}(z) \geq 0$. Then $\lim_{T \to \infty} \int_0^T f(t)\, dt$ exists and equals $g(0)$.
