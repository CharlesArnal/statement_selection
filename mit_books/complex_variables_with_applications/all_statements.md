# All Formal Mathematical Statements
## Complex Variables with Applications (MIT 18.04, Spring 2018)

---

### Topic 1: Complex Algebra and the Complex Plane

**Definition 1.** The symbols $\pm i$ stand for the solutions to the equation $x^2 = -1$. We call these new numbers complex numbers.

**Theorem 1.** (Fundamental theorem of algebra) A polynomial of degree $n$ has exactly $n$ complex roots (repeated roots are counted with multiplicity).

**Definition 2.** Complex numbers are defined as the set of all numbers $z = x + yi$ where $x$ and $y$ are real numbers. We call $x$ the real part of $z$ (denoted $\operatorname{Re}(z)$) and $y$ the imaginary part (denoted $\operatorname{Im}(z)$).

**Definition 3.** Complex conjugation: $\overline{x + iy} = x - iy$.

**Definition 4.** The magnitude (absolute value, norm, modulus) of the complex number $x + iy$ is $|z| = \sqrt{x^2 + y^2}$.

**Theorem 2.** (Triangle inequality) For complex numbers $z_1, z_2$: $|z_1| + |z_2| \ge |z_1 + z_2|$, with equality only if one is 0 or $\arg(z_1) = \arg(z_2)$.

**Definition 5.** (Euler's formula) $e^{i\theta} = \cos(\theta) + i\sin(\theta)$.

**Theorem 3.** (Properties of complex exponentials) P1: $\frac{d}{dt}e^{it} = ie^{it}$. P2: $e^{i \cdot 0} = 1$. P3: $e^{ia}e^{ib} = e^{i(a+b)}$. P4: The definition is consistent with the power series for $e^x$.

**Theorem 4.** (de Moivre's formula) $(\cos(\theta) + i\sin(\theta))^n = \cos(n\theta) + i\sin(n\theta)$.

**Definition 6.** The complex exponential function: $e^z = e^{x+iy} = e^x(\cos(y) + i\sin(y))$.

**Definition 7.** The punctured plane is the complex plane minus the origin: $\mathbb{C} \setminus \{0\}$.

**Definition 8.** A branch of the argument function is a choice of range so that $\arg(z)$ becomes single-valued.

**Definition 9.** The principal branch of $\arg(z)$ is $-\pi < \arg(z) \le \pi$, denoted $\operatorname{Arg}(z)$.

**Definition 10.** The function $\log(z) = \log(|z|) + i\arg(z)$.

**Definition 11.** Complex powers: $z^a = e^{a\log(z)}$.

---

### Topic 2: Analytic Functions

**Definition 12.** The complex derivative: $f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$.

**Definition 13.** The open disk of radius $r$ around $z_0$: the set $|z - z_0| < r$. The open deleted (punctured) disk: $0 < |z - z_0| < r$.

**Definition 14.** An open region in the complex plane is a set $A$ with the property that every point in $A$ can be surrounded by an open disk entirely in $A$.

**Definition 15.** $\lim_{z \to z_0} f(z) = w_0$ if $f(z) \to w_0$ no matter what direction $z$ approaches $z_0$.

**Definition 16.** $f$ is continuous at $z_0$ if $f$ is defined on an open disk around $z_0$ and $\lim_{z \to z_0} f(z) = f(z_0)$.

**Theorem 2.10.** (Cauchy-Riemann equations) If $f(z) = u(x,y) + iv(x,y)$ is analytic then $u_x = v_y$ and $u_y = -v_x$, and $f'(z) = u_x + iv_x = v_y - iu_y$.

**Theorem 5.** (Converse of Cauchy-Riemann) If $u$ and $v$ satisfy the Cauchy-Riemann equations and have continuous partials, then $f(z) = u + iv$ is differentiable.

**Theorem 6.** If $f(z)$ is differentiable on a disk and $f'(z) = 0$ on the disk then $f(z)$ is constant.

**Theorem 2.13.** If $f(z) = u + iv$ is analytic (assuming continuous second order partials), then $f'(z)$ is also analytic.

**Definition 17.** An entire function is a function that is analytic at every point in the complex plane.

**Definition 18.** $\cos(z) = \frac{e^{iz} + e^{-iz}}{2}$, $\sin(z) = \frac{e^{iz} - e^{-iz}}{2i}$.

**Definition 19.** $\cosh(z) = \frac{e^z + e^{-z}}{2}$, $\sinh(z) = \frac{e^z - e^{-z}}{2}$.

---

### Topic 3: Line Integrals and Cauchy's Theorem

**Definition 20.** Complex line integral: $\int_\gamma f(z)\,dz = \int_a^b f(\gamma(t))\gamma'(t)\,dt$.

**Theorem 3.5.** (Fundamental theorem of complex line integrals) If $f(z)$ is analytic on an open region $A$ and $\gamma$ is a curve in $A$ from $z_0$ to $z_1$ then $\int_\gamma f'(z)\,dz = f(z_1) - f(z_0)$.

**Theorem 3.8.** If $f(z)$ has an antiderivative in an open region $A$, then $\int_\gamma f(z)\,dz$ is path independent for all paths in $A$.

**Theorem 3.9.** Path independence of $\int f(z)\,dz$ is equivalent to $\oint_C f(z)\,dz = 0$ around any closed path.

**Theorem 3.13.** (Cauchy's theorem) If $A$ is a simply connected region, $f(z)$ is analytic on $A$, and $C$ is a simple closed curve in $A$, then: (i) $\oint_C f(z)\,dz = 0$, (ii) integrals are path independent, (iii) $f$ has an antiderivative in $A$.

**Theorem 3.14.** (Extended Cauchy's theorem) If $f(z)$ is analytic on the region $R$ between two simple closed curves $C_1$ and $C_2$, then $\int_{C_1 - C_2} f(z)\,dz = 0$.

**Definition 21.** The winding number of a curve $C$ around a point is the number of times $C$ goes counterclockwise around that point.

---

### Topic 4: Cauchy's Integral Formula

**Theorem 4.1.** (Cauchy's integral formula) If $C$ is a simple closed curve (counterclockwise) and $f(z)$ is analytic on a region containing $C$ and its interior, then for $z_0$ inside $C$: $f(z_0) = \frac{1}{2\pi i}\oint_C \frac{f(z)}{z - z_0}\,dz$.

**Theorem 4.5.** (Cauchy's integral formula for derivatives) Under the same hypotheses: $f^{(n)}(z) = \frac{n!}{2\pi i}\oint_C \frac{f(w)}{(w-z)^{n+1}}\,dw$.

**Theorem 4.11.** (Triangle inequality for integrals) $\left|\int_a^b g(t)\,dt\right| \le \int_a^b |g(t)|\,dt$.

**Theorem 4.12.** (Triangle inequality for integrals II) $\left|\int_\gamma f(z)\,dz\right| \le \int_\gamma |f(z)|\,|dz|$.

**Corollary 1.** If $|f(z)| < M$ on $C$ then $\left|\int_C f(z)\,dz\right| \le M \cdot \text{length}(C)$.

**Theorem 4.14.** (Second extension of Cauchy's theorem) If $g$ is analytic on $A \setminus \{z_0\}$ and continuous on $A$, then $\oint_C g(z)\,dz = 0$ for all closed curves $C$ in $A$.

**Theorem 7.** (Existence of derivatives) If $f(z)$ is analytic on a region $A$, then $f$ has derivatives of all orders.

**Theorem 4.15.** (Cauchy's inequality) If $f(z)$ is analytic on $|z - z_0| \le R$ and $M_R = \max_{|z-z_0|=R} |f(z)|$, then $|f^{(n)}(z_0)| \le \frac{n! M_R}{R^n}$.

**Theorem 4.16.** (Liouville's theorem) If $f(z)$ is entire and bounded, then $f(z)$ is constant.

**Corollary 2.** (Fundamental theorem of algebra, via Liouville) Any polynomial of degree $n \ge 1$ has exactly $n$ roots.

**Theorem 4.17.** (Mean value property) If $f(z)$ is analytic on $|z - z_0| \le r$, then $f(z_0) = \frac{1}{2\pi}\int_0^{2\pi} f(z_0 + re^{i\theta})\,d\theta$.

**Theorem 4.18.** (Maximum modulus principle) If $f(z)$ is analytic in a connected region $A$: (1) If $|f|$ has a relative maximum at $z_0$, then $f$ is constant near $z_0$. (2) If $A$ is bounded and $f$ is continuous on $A$ and its boundary, then either $f$ is constant or $\max |f|$ occurs only on the boundary.

---

### Topic 5: Harmonic Functions

**Definition 5.1.** A function $u(x,y)$ is harmonic if $\nabla^2 u = u_{xx} + u_{yy} = 0$.

**Theorem 5.2.** If $f(z) = u + iv$ is analytic on a region $A$, then both $u$ and $v$ are harmonic on $A$.

**Theorem 5.3.** If $u(x,y)$ is harmonic on a simply connected region $A$, then $u$ is the real part of an analytic function $f(z) = u + iv$.

**Definition 22.** If $u$ and $v$ are the real and imaginary parts of an analytic function, then $u$ and $v$ are called harmonic conjugates.

**Theorem 8.** (Mean value property for harmonic functions) If $u$ is harmonic on and inside a circle of radius $r$ centered at $z_0$, then $u(x_0,y_0) = \frac{1}{2\pi}\int_0^{2\pi} u(z_0 + re^{i\theta})\,d\theta$.

**Theorem 9.** (Maximum principle for harmonic functions) (i) If $u$ has a relative max or min at $z_0$ in $A$, then $u$ is constant near $z_0$. (ii) If $A$ is bounded and connected and $u$ is continuous on $A$ and its boundary, then the absolute max and min occur on the boundary.

**Lemma 5.4.** If $f(z) = u + iv$ is analytic, then $\nabla u \cdot \nabla v = 0$.

**Theorem 10.** (Orthogonality of level curves) If $f(z) = u + iv$ is analytic and $f'(z) \neq 0$, then the level curves of $u$ and $v$ through $(x,y)$ are orthogonal.

---

### Topic 6: Two-Dimensional Hydrodynamics and Complex Potentials

**Theorem 11.** If $\Phi(z) = \phi + i\psi$ is analytic and $\mathbf{F} = \nabla\phi$, then $\mathbf{F}$ is divergence-free and curl-free.

**Theorem 12.** If $\mathbf{F} = (u,v)$ is an incompressible, irrotational field on a simply connected region $A$, then there is an analytic function $\Phi$ which is a complex potential for $\mathbf{F}$.

**Theorem 13.** (Stream function) If $\Phi = \phi + i\psi$ is the complex potential for $\mathbf{F}$, then the fluid flows along the level curves of $\psi$ (streamlines).

---

### Topic 7: Taylor and Laurent Series

**Theorem 14.** (Sum of finite geometric series) $S_n = a(1 + r + \cdots + r^n) = \frac{a(1 - r^{n+1})}{1 - r}$.

**Theorem 15.** (Infinite geometric series) If $|r| < 1$ then $\sum_{j=0}^\infty ar^j = \frac{a}{1-r}$. If $|r| \ge 1$ the series diverges.

**Theorem 7.1.** (Convergence of power series) For $f(z) = \sum a_n(z-z_0)^n$ there exists $R \ge 0$ such that the series converges absolutely for $|z-z_0| < R$ and diverges for $|z-z_0| > R$. Term-by-term differentiation and integration are valid.

**Theorem 7.5.** (Taylor's theorem) If $f(z)$ is analytic in a region $A$ and $z_0 \in A$, then $f(z) = \sum_{n=0}^\infty a_n(z-z_0)^n$ with $a_n = \frac{f^{(n)}(z_0)}{n!}$, converging on any disk $|z-z_0| < r$ in $A$.

**Corollary 3.** The power series representing an analytic function around a point is unique.

**Theorem 7.6.** (Zeros are isolated) If $f(z)$ is analytic and not identically zero then the zeros of $f$ are isolated.

**Definition 23.** The order of a zero of $f$ at $z_0$ is the integer $k$ such that $f(z) = (z-z_0)^k g(z)$ with $g(z_0) \neq 0$.

**Definition 24.** A singularity $z_0$ of $f$ is isolated if $f$ is analytic on $0 < |z-z_0| < r$.

**Theorem 7.19.** (Laurent series) If $f(z)$ is analytic on the annulus $r_1 < |z-z_0| < r_2$, then $f(z) = \sum_{n=1}^\infty \frac{b_n}{(z-z_0)^n} + \sum_{n=0}^\infty a_n(z-z_0)^n$.

**Definition 25.** Poles: If $z_0$ is an isolated singularity and only finitely many $b_n \neq 0$ with $b_k \neq 0$ for $n > k$, then $z_0$ is a pole of order $k$. A pole of order 1 is simple. If infinitely many $b_n \neq 0$, $z_0$ is an essential singularity. If all $b_n = 0$, $z_0$ is a removable singularity.

**Definition 7.31.** The residue of $f$ at $z_0$ is $b_1$ (the coefficient of $1/(z-z_0)$ in the Laurent series), denoted $\operatorname{Res}(f, z_0)$.

---

### Topic 8: Residue Theorem

**Definition 26.** A function analytic on a region $A$ is holomorphic on $A$. A function analytic except for poles of finite order is meromorphic.

**Theorem 16.** (Picard's theorem) If $f(z)$ has an essential singularity at $z_0$, then in every neighborhood of $z_0$, $f(z)$ takes all possible values infinitely many times, with the possible exception of one value.

**Theorem 17.** (Quotients) If $f$ has a zero of order $m$ and $g$ has a zero of order $n$ at $z_0$, then $f/g$ has: a pole of order $n-m$ if $n > m$; a zero of order $m-n$ if $n < m$; is analytic and nonzero if $n = m$.

**Theorem 18.** (Residue at simple poles) Property 5: If $g(z)$ has a simple zero at $z_0$, then $\operatorname{Res}(1/g, z_0) = 1/g'(z_0)$.

**Theorem 19.** (Residues at higher order poles) If $f$ has a pole of order $k$ at $z_0$ and $g(z) = (z-z_0)^k f(z)$, then $\operatorname{Res}(f, z_0) = \frac{g^{(k-1)}(z_0)}{(k-1)!}$.

**Theorem 20.** (Cauchy's residue theorem) If $f(z)$ is analytic in region $A$ except for isolated singularities, and $C$ is a simple closed curve (counterclockwise) in $A$ not through any singularities, then $\oint_C f(z)\,dz = 2\pi i \sum \text{residues of } f \text{ inside } C$.

**Definition 27.** The residue at infinity: $\operatorname{Res}(f, \infty) = -\frac{1}{2\pi i}\oint_C f(z)\,dz$.

**Theorem 21.** $\operatorname{Res}(f, \infty) = -\operatorname{Res}\left(\frac{1}{w^2}f(1/w), 0\right)$.

---

### Topic 9: Definite Integrals Using the Residue Theorem

**Theorem 9.1.** (Estimation on semicircles) If $|f(z)| < M/|z|^a$ for $a > 1$ in the upper (or lower) half-plane, then $\lim_{R \to \infty} \int_{C_R} f(z)\,dz = 0$ where $C_R$ is a semicircle of radius $R$.

**Theorem 9.2.** (Jordan-type lemma) If $|f(z)| < M/|z|$ for large $|z|$ in the upper half-plane, then for $a > 0$, the integral of $f(z)e^{iaz}$ over rectangular paths in the upper half-plane vanishes as the rectangle grows.

**Theorem 9.7.** (Trigonometric integrals) If $R(x,y)$ is rational with no poles on $x^2 + y^2 = 1$, then $\int_0^{2\pi} R(\cos\theta, \sin\theta)\,d\theta = 2\pi i \sum \text{residues of } \frac{1}{iz}R\left(\frac{z+1/z}{2}, \frac{z-1/z}{2i}\right) \text{ inside } |z|=1$.

**Theorem 9.11.** Convergence of an integral implies convergence of the corresponding Cauchy principal value.

**Definition 28.** Cauchy principal value: $\text{p.v.}\int_{-\infty}^\infty f(x)\,dx = \lim_{R \to \infty}\int_{-R}^R f(x)\,dx$.

**Theorem 9.13.** If $f$ has a simple pole at $x_0$ on the real axis, then $\lim_{r \to 0}\int_{C_r} f(z)\,dz = \pi i \operatorname{Res}(f, x_0)$, where $C_r$ is the upper semicircle of radius $r$ around $x_0$.

**Theorem 9.14.** If $f$ has a simple pole at $z_0$ and $C_r$ is a circular arc of angle $\alpha$ centered at $z_0$, then $\lim_{r \to 0}\int_{C_r} f(z)\,dz = i\alpha\operatorname{Res}(f, z_0)$.

**Definition 29.** Fourier transform: $\hat{f}(\omega) = \int_{-\infty}^\infty f(t)e^{-i\omega t}\,dt$.

**Theorem 22.** (Fourier inversion formula) $f(t) = \frac{1}{2\pi}\int_{-\infty}^\infty \hat{f}(\omega)e^{i\omega t}\,d\omega$.

---

### Topic 10: Conformal Transformations

**Definition 30.** A conformal map is one that preserves angles and orientation at a point.

**Theorem 10.3.** A map $w = f(z)$ is conformal if and only if it is locally a multiplication by a nonzero complex number (i.e., it is a nonzero complex linear map at each point).

**Theorem 10.4.** If $f(z)$ is analytic and $f'(z_0) \neq 0$, then $f$ is conformal at $z_0$.

**Theorem 10.9.** If $f = u + iv$ is analytic and $f'(z) \neq 0$, then the level curves of $u$ and $v$ are orthogonal.

**Theorem 10.10.** (Riemann mapping theorem) If $A$ is a simply connected region in $\mathbb{C}$ that is not all of $\mathbb{C}$, then there exists a conformal map from $A$ onto the unit disk.

**Definition 31.** A fractional linear transformation (FLT, or Mobius transformation) is $T(z) = \frac{az + b}{cz + d}$ with $ad - bc \neq 0$.

**Theorem 23.** FLTs map lines and circles to lines and circles.

**Definition 32.** Two points $z$ and $z^*$ are symmetric with respect to a circle $C$ if every line or circle through $z$ and $z^*$ intersects $C$ at right angles.

**Theorem 24.** If $z$ and $z^*$ are symmetric with respect to circle $C$, and $T$ is an FLT, then $T(z)$ and $T(z^*)$ are symmetric with respect to $T(C)$.

**Theorem 25.** (Milne-Thomson circle theorem) If $f(z)$ is a complex potential with no singularities inside or on $|z| = R$, then $\Phi(z) = f(z) + \overline{f(R^2/\bar{z})}$ gives a flow with the circle as a streamline.

---

### Topic 11: Argument Principle

**Theorem 11.1.** If $f$ is meromorphic inside and on $C$ (a simple closed curve), then $\frac{1}{2\pi i}\oint_C \frac{f'(z)}{f(z)}\,dz = Z - P$, where $Z$ = number of zeros and $P$ = number of poles (counted with multiplicity) inside $C$.

**Definition 33.** The winding number of $f(z)$ around $C$ with respect to the origin is $\frac{1}{2\pi i}\oint_C \frac{f'(z)}{f(z)}\,dz$.

**Theorem 11.4.** (Argument principle) If $f$ is meromorphic inside $C$, then the change in $\arg(f(z))$ as $z$ traverses $C$ equals $2\pi(Z - P)$.

**Theorem 11.6.** (Rouche's theorem) If $f$ and $g$ are analytic inside and on a simple closed curve $C$, and $|g(z)| < |f(z)|$ on $C$, then $f$ and $f + g$ have the same number of zeros inside $C$.

**Corollary 4.** (Fundamental theorem of algebra, via Rouche) Every polynomial of degree $n$ has exactly $n$ roots (counted with multiplicity).

**Theorem 11.18.** (Nyquist stability criterion) A linear system with transfer function $G(s) = p(s)/q(s)$ is stable if and only if the Nyquist plot of $1 + G(s)$ does not encircle the origin.

---

### Topic 12: Laplace Transform

**Definition 34.** The Laplace transform: $\mathcal{L}(f(t); s) = F(s) = \int_0^\infty f(t)e^{-st}\,dt$.

**Definition 35.** A function $f(t)$ is of exponential type if $|f(t)| < Me^{ct}$ for constants $M, c$.

**Theorem 26.** If $f(t)$ is of exponential type with $|f(t)| < Me^{ct}$, then $F(s)$ converges for $\operatorname{Re}(s) > c$.

**Theorem 27.** (Properties of Laplace transform) (1) Linearity: $\mathcal{L}(af + bg) = a\mathcal{L}(f) + b\mathcal{L}(g)$. (2) $s$-shift: $\mathcal{L}(e^{at}f(t)) = F(s-a)$. (3) $t$-derivative: $\mathcal{L}(f') = sF(s) - f(0)$. (4) $s$-derivative: $\mathcal{L}(tf(t)) = -F'(s)$.

**Theorem 12.13.** (Substitution rule) If $\mathcal{L}(f(t); s) = F(s)$ then $\mathcal{L}(f(at); s) = \frac{1}{a}F(s/a)$ for $a > 0$.

**Theorem 12.20.** (Laplace inversion 1) $f(t) = \sum \text{residues of } F(s)e^{st}$.

**Theorem 12.21.** (Laplace inversion 2, Bromwich integral) $f(t) = \frac{1}{2\pi i}\int_{\gamma - i\infty}^{\gamma + i\infty} F(s)e^{st}\,ds$ where $\gamma$ is to the right of all singularities of $F$.

---

### Topic 13: Analytic Continuation and the Gamma Function

**Theorem 13.2.** (Uniqueness of analytic continuation) If $f$ and $g$ are analytic on a connected region $A$ and agree on an open subset, then $f = g$ on all of $A$.

**Corollary 5.** There is at most one way to analytically continue a function from a region $A$ to a connected region $B$.

**Definition 36.** The Gamma function: $\Gamma(z) = \int_0^\infty t^{z-1}e^{-t}\,dt$, converging for $\operatorname{Re}(z) > 0$.

**Theorem 28.** (Properties of Gamma) Property 1: $\Gamma(z)$ is analytic for $\operatorname{Re}(z) > 0$.

**Theorem 29.** Property 2: $\Gamma(n+1) = n!$ for integers $n \ge 0$.

**Theorem 30.** Property 3 (Functional equation): $\Gamma(z+1) = z\Gamma(z)$.

**Theorem 31.** Property 4: $\Gamma(z)$ can be analytically continued to a meromorphic function on the entire plane with simple poles at $0, -1, -2, \ldots$ and $\operatorname{Res}(\Gamma, -m) = \frac{(-1)^m}{m!}$.

**Theorem 32.** Property 5 (Weierstrass product): $\Gamma(z) = \left[ze^{\gamma z}\prod_{n=1}^\infty\left(1 + \frac{z}{n}\right)e^{-z/n}\right]^{-1}$.

**Theorem 33.** Property 6 (Reflection formula): $\Gamma(z)\Gamma(1-z) = \frac{\pi}{\sin(\pi z)}$.

**Theorem 34.** Property 7 (Stirling's formula): $\Gamma(z+1) \approx \sqrt{2\pi}z^{z+1/2}e^{-z}$ for $|z|$ large, $\operatorname{Re}(z) > 0$.

**Theorem 35.** Property 8 (Legendre duplication formula): $2^{2z-1}\Gamma(z)\Gamma(z+1/2) = \sqrt{\pi}\Gamma(2z)$.

**Theorem 36.** (Connection to Laplace) For $\operatorname{Re}(z) > 1$ and $\operatorname{Re}(s) > 0$: $\mathcal{L}(t^{z-1}; s) = \frac{\Gamma(z)}{s^z}$.
