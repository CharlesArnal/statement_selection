# All Statements from Introduction to Partial Differential Equations

## Statement 1: Proposition 4.0.1 (Superposition Principle)
If $u_1, \dots, u_M$ are solutions to the linear PDE $\mathcal{L}u = 0$, and $c_1, \dots, c_M \in \mathbb{R}$, then $\sum_{i=1}^M c_i u_i$ is also a solution.

## Statement 2: Proposition 4.0.2 (Relationship between inhomogeneous and homogeneous linear PDE solutions)
Let $S_h$ be the set of all solutions to the homogeneous linear PDE $\mathcal{L}u = 0$, and let $u_I$ be a fixed solution to the inhomogeneous linear PDE $\mathcal{L}u = f(x^1, \cdots, x^n)$. Then the set $S_I$ of all solutions to the inhomogeneous equation is the translation of $S_H$ by $u_I$: $S_I = \{u_I + u_H \mid u_H \in S_H\}$.

## Statement 3: Theorem 7.1 (Divergence Theorem)
Let $\Omega \subset \mathbb{R}^3$ be a domain with boundary $\partial\Omega$. Then $\int_{\Omega} \nabla \cdot \mathbf{F}(x,y,z)\, dxdydz = \int_{\partial\Omega} \mathbf{F}(\sigma) \cdot \hat{\mathbf{N}}(\sigma)\, d\sigma$, where $\hat{\mathbf{N}}(\sigma)$ is the unit outward normal vector to $\partial\Omega$ and $d\sigma$ is the surface measure induced on $\partial\Omega$.

## Statement 4: Theorem 4.1 (Some basic facts from Fourier analysis)
If $f(x)$ is a function such that $\|f\|_{L^2([0,1])}^2 < \infty$, then $f(x)$ can be Fourier-expanded as $f(x) = \sum_{m=1}^{\infty} A_m \sin(m\pi x)$, where $A_m = 2\int_{[0,1]} f(x)\sin(m\pi x)\,dx$. The sum converges in $L^2$ and we have the Parseval identity $\|f\|_{L^2([0,1])}^2 = \sum_{m=1}^{\infty} \frac{1}{2} A_m^2$. If $f$ is continuous, convergence is uniform on closed subintervals of $(0,1)$.

## Statement 5: Theorem 1.1 (Uniqueness for the heat equation on a finite interval)
Solutions $u \in C^{1,2}(\overline{Q}_T)$ to the inhomogeneous heat equation $\partial_t u - D\partial_x^2 u = f(t,x)$ are unique under Dirichlet, Neumann, Robin, or mixed conditions.

## Statement 6: Theorem 1.1 (Weak Maximum Principle)
Let $\Omega \subset \mathbb{R}^n$ be a domain, $Q_T = (0,T) \times \Omega$ a spacetime cylinder, and $\partial_p Q_T$ its parabolic boundary. Let $w \in C^{1,2}(Q_T) \cap C(\overline{Q}_T)$ be a solution to the heat equation. Then $\max_{\overline{Q}_T} w = \max_{\partial_p Q_T} w$ and $\min_{\overline{Q}_T} w = \min_{\partial_p Q_T} w$.

## Statement 7: Corollary 1.0.1 (Comparison Principle and Stability)
Suppose that $v, w$ are solutions to the heat equations with respective data. If the data of $v$ dominate those of $w$ on the parabolic boundary, then $v \ge w$ throughout $\overline{Q}_T$.

## Statement 8: Lemma 1.0.1 (Heat kernel solves the heat equation)
$\Gamma_D(t,x)$ is a solution to the heat equation $\partial_t u - D\Delta u = 0$ for $x \in \mathbb{R}^n, t > 0$.

## Statement 9: Lemma 1.0.2 (Properties of the heat kernel)
$\Gamma_D(t,x)$ has the following properties: (a) $\Gamma_D(t,x) > 0$ for $t > 0$; (b) $\int_{\mathbb{R}^n} \Gamma_D(t,x)\,d^n x = 1$ for $t > 0$; (c) For any $\delta > 0$, $\lim_{t \downarrow 0} \int_{|x| \ge \delta} \Gamma_D(t,x)\,d^n x = 0$.

## Statement 10: Lemma 1.0.3 (Approximation to the identity for the heat kernel)
Suppose that $\phi(x)$ is a continuous function on $\mathbb{R}^n$ and that there exist constants $a, b \ge 0$ such that $|\phi(x)| \le ae^{b|x|^2}$. Then $\lim_{t \downarrow 0} \int_{\mathbb{R}^n} \Gamma_D(t,x-y)\phi(y)\,d^n y = \phi(x)$.

## Statement 11: Proposition 1.0.4 (Properties of the heat kernel)
$\Gamma_D(t,x)$ is a solution to the heat equation (with $f=0$) verifying the initial conditions $\lim_{t \downarrow 0} \Gamma_D(t,\cdot) = \delta(\cdot)$ in the sense of distributions.

## Statement 12: Proposition 1.1.1 (Differentiating under the integral)
Let $I(a,b)$ be a function on $\mathbb{R} \times \mathbb{R}$. Under appropriate continuity and integrability conditions, differentiation and integration can be exchanged.

## Statement 13: Theorem 1.1 (Solving the global Cauchy problem via the fundamental solution)
Assume that $g(x)$ is a continuous function on $\mathbb{R}^n$ that verifies $|g(x)| \le ae^{b|x|^2}$. Then there exists a solution $u(t,x)$ to the homogeneous heat equation with initial data $u(0,x) = g(x)$, given by $u(t,x) = \int_{\mathbb{R}^n} \Gamma_D(t,x-y)g(y)\,d^n y$.

## Statement 14: Theorem 1.2 (Duhamel's Principle)
Under appropriate conditions on $g(x)$ and $f(t,x)$, there exists a unique solution $u(t,x)$ to the inhomogeneous heat equation $\partial_t u - D\Delta u = f(t,x)$ with initial data $u(0,x) = g(x)$, given by $u(t,x) = \int_{\mathbb{R}^n} \Gamma_D(t,x-y)g(y)\,d^n y + \int_0^t \int_{\mathbb{R}^n} \Gamma_D(t-s,x-y)f(s,y)\,d^n y\,ds$.

## Statement 15: Lemma 2.0.2 (Invariance of heat equation under translations and parabolic dilations)
Suppose that $u(t,x)$ is a solution to the heat equation. Let $A, t_0 \in \mathbb{R}$, $x_0 \in \mathbb{R}^n$. Then the amplified and translated function $v(t,x) = Au(t-t_0, x-x_0)$ is also a solution. Similarly, the parabolically dilated function $w(t,x) = u(\lambda^2 t, \lambda x)$ is a solution.

## Statement 16: Lemma 2.0.3 (Conservation of total thermal energy)
Let $u(t,x) \in C^{1,2}([0,\infty) \times \mathbb{R}^n)$ be a solution to the heat equation with appropriate decay. Then the total thermal energy $\int_{\mathbb{R}^n} u(t,x)\,d^n x$ is constant in time.

## Statement 17: Theorem 3.1 (Uniqueness for the Poisson equation)
Let $\Omega \subset \mathbb{R}^n$ be a smooth, bounded domain. Then under Dirichlet, Robin, or mixed boundary conditions, there is at most one solution of regularity $u \in C^2(\Omega) \cap C^1(\overline{\Omega})$ to the Poisson equation.

## Statement 18: Theorem 4.1 (Mean Value Properties for harmonic functions)
Let $u(x)$ be harmonic in the domain $\Omega \subset \mathbb{R}^n$, and let $B_R(x) \subset \Omega$. Then: (a) $u(x) = \frac{1}{|\partial B_R(x)|} \int_{\partial B_R(x)} u(\sigma)\,d\sigma$ (spherical mean value property); (b) $u(x) = \frac{1}{|B_R(x)|} \int_{B_R(x)} u(y)\,d^n y$ (solid mean value property).

## Statement 19: Theorem 5.1 (Strong Maximum Principle)
Let $\Omega \subset \mathbb{R}^n$ be a domain, and assume $u \in C(\Omega)$ verifies the mean value property. Then if $u$ achieves its max or min at a point $p \in \Omega$, then $u$ is constant on $\Omega$. If $\Omega$ is bounded and $u \in C(\overline{\Omega})$ is not constant, then for every $x \in \Omega$, $\min_{\partial\Omega} u < u(x) < \max_{\partial\Omega} u$.

## Statement 20: Corollary 5.0.1 (Uniqueness for Dirichlet problem for the Laplace equation)
Let $\Omega \subset \mathbb{R}^n$ be a bounded domain and let $f \in C(\Omega)$. Then the PDE $\Delta u = f$ in $\Omega$ with $u = g$ on $\partial\Omega$ has at most one solution $u \in C^2(\Omega) \cap C(\overline{\Omega})$.

## Statement 21: Lemma 1.0.1 (Fundamental solution is harmonic away from the origin)
If $x \neq 0$, then $\Delta \Phi(x) = 0$, where $\Phi$ is the fundamental solution of the Laplacian.

## Statement 22: Theorem 1.1 (Solution to Poisson's equation in $\mathbb{R}^n$)
Let $f(x) \in C_0^{\infty}(\mathbb{R}^n)$. Then for $n \ge 3$, the Laplace equation $\Delta u(x) = f(x)$ has a unique smooth solution $u(x)$ that tends to 0 as $|x| \to \infty$, given by $u(x) = \int_{\mathbb{R}^n} \Phi(x-y) f(y)\,d^n y$.

## Statement 23: Theorem 2.1 (Basic existence theorem for the Dirichlet problem)
Let $\Omega$ be a bounded Lipschitz domain, and let $g \in C(\partial\Omega)$. Then the PDE $\Delta u = 0$ in $\Omega$, $u = g$ on $\partial\Omega$ has a unique solution $u \in C^2(\Omega) \cap C(\overline{\Omega})$.

## Statement 24: Proposition 2.0.2 (Decomposition of Green's function)
Let $\Phi$ be the fundamental solution for $\Delta$ in $\mathbb{R}^n$, and let $\Omega \subset \mathbb{R}^n$ be a domain. Then the Green function $G(x,y)$ for $\Omega$ can be decomposed as $G(x,y) = \Phi(x-y) - \phi^x(y)$, where $\phi^x$ is harmonic in $\Omega$ and $\phi^x = \Phi(x-\cdot)$ on $\partial\Omega$.

## Statement 25: Proposition 2.0.3 (Representation formula for harmonic functions)
Let $\Phi$ be the fundamental solution for $\Delta$ in $\mathbb{R}^n$, and let $\Omega \subset \mathbb{R}^n$ be a domain. Assume $u \in C^2(\overline{\Omega})$. Then for every $x \in \Omega$, $u(x) = \int_{\Omega} \Phi(x-y)\Delta u(y)\,d^n y + \int_{\partial\Omega} \left[ u(y)\frac{\partial \Phi}{\partial \nu}(x-y) - \Phi(x-y)\frac{\partial u}{\partial \nu}(y) \right] d\sigma(y)$.

## Statement 26: Theorem 2.2 (Representation formula for solutions to the boundary value Poisson equation)
The solution $u$ to $\Delta u = f$ in $\Omega$, $u = g$ on $\partial\Omega$ can be represented as $u(x) = -\int_{\Omega} G(x,y)f(y)\,d^n y + \int_{\partial\Omega} g(y)\frac{\partial G}{\partial \nu_y}(x,y)\,d\sigma(y)$.

## Statement 27: Theorem 3.1 (Poisson's formula)
Let $B_R(p) \subset \mathbb{R}^3$ be a ball. Then the unique solution $u \in C^2(B_R(p)) \cap C(\overline{B}_R(p))$ of $\Delta u = 0$ in $B_R(p)$, $u = g$ on $\partial B_R(p)$ is given by the Poisson integral formula.

## Statement 28: Theorem 4.1 (Harnack's inequality)
Let $u$ be harmonic and non-negative in the ball $B_R(0) \subset \mathbb{R}^n$. Then for any $x \in B_R(0)$, $\frac{R^{n-2}(R - |x|)}{(R + |x|)^{n-1}} u(0) \le u(x) \le \frac{R^{n-2}(R + |x|)}{(R - |x|)^{n-1}} u(0)$.

## Statement 29: Corollary 4.0.4 (Liouville's theorem)
Suppose that $u \in C^2(\mathbb{R}^n)$ is harmonic on $\mathbb{R}^n$. Suppose there exists a constant $M$ such that $u(x) \ge M$ for all $x \in \mathbb{R}^n$, or $u(x) \le M$ for all $x \in \mathbb{R}^n$. Then $u$ is constant.

## Statement 30: Theorem 1.1 (Basic existence theorem, repeated)
Let $\Omega$ be a bounded Lipschitz domain, and let $g \in C(\partial\Omega)$. Then the PDE $\Delta u = 0$ in $\Omega$, $u = g$ on $\partial\Omega$ has a unique solution $u \in C^2(\Omega) \cap C(\overline{\Omega})$.

## Statement 31: Proposition 1.0.1 (Decomposition of Green's function, repeated)
The Green function $G(x,y)$ for $\Omega$ can be decomposed as $G(x,y) = \Phi(x-y) - \phi^x(y)$.

## Statement 32: Proposition 1.0.2 (Representation formula for u, repeated)
For every $x \in \Omega$, we have $u(x) = \int_{\Omega} \Phi(x-y)\Delta u(y)\,d^n y + \int_{\partial\Omega} [u(y)\frac{\partial\Phi}{\partial\nu}(x-y) - \Phi(x-y)\frac{\partial u}{\partial\nu}(y)]\,d\sigma(y)$.

## Statement 33: Theorem 1.1 (Representation formula for Poisson equation, repeated)
The unique solution $u$ to the boundary value Poisson equation can be represented via the Green function.

## Statement 34: Lemma 2.0.1 (Green function for a ball)
The Green function for a ball $B_R(p) \subset \mathbb{R}^3$ is explicitly given.

## Statement 35: Theorem 2.1 (Poisson's formula, repeated)
Let $B_R(p) \subset \mathbb{R}^3$ and $g \in C(\partial B_R(p))$. Then the unique solution to $\Delta u = 0$ in $B_R(p)$, $u = g$ on $\partial B_R(p)$ is given by the Poisson integral formula.

## Statement 36: Theorem 3.1 (Harnack's inequality, repeated)
Let $u$ be harmonic and non-negative in $B_R(0)$. Then for any $x \in B_R(0)$, Harnack's bounds hold.

## Statement 37: Corollary 3.0.2 (Liouville's theorem, repeated)
Suppose $u \in C^2(\mathbb{R}^n)$ is harmonic on $\mathbb{R}^n$ and bounded from above or below. Then $u$ is constant.

## Statement 38: Theorem 4.1 (d'Alembert's formula)
Assume $f \in C^2(\mathbb{R})$ and $g \in C^1(\mathbb{R})$. Then the unique solution $u(t,x)$ to the 1+1 dimensional wave equation with initial data $u(0,x) = f(x)$, $\partial_t u(0,x) = g(x)$ satisfies $u(t,x) = \frac{1}{2}(f(x+t) + f(x-t)) + \frac{1}{2}\int_{x-t}^{x+t} g(z)\,dz$.

## Statement 39: Corollary 4.0.1 (Wave equation on a half-line)
Let $f \in C^2([0,\infty))$, $g \in C^1([0,\infty))$, and assume $f(0) = g(0) = 0$. Then the unique solution to the 1+1 dimensional initial + boundary value wave equation problem is given by an extension of d'Alembert's formula.

## Statement 40: Proposition 1.0.1 (Spherical averages)
Let $u(t,x) \in C^2([0,\infty) \times \mathbb{R}^3)$ be a solution to the 1+3 dimensional global Cauchy problem for the wave equation. Then the spherical average of $u$ satisfies a 1+1 dimensional wave equation.

## Statement 41: Corollary 1.0.2 (Representation formula for spherical averages)
Under the assumptions of Proposition 1.0.1, the spherical average has a d'Alembert-type representation formula.

## Statement 42: Theorem 1.1 (Kirchhoff's formula)
Assume $f \in C^3(\mathbb{R}^3)$ and $g \in C^2(\mathbb{R}^3)$. Then the unique solution $u(t,x)$ to the 3D wave equation global Cauchy problem is given by Kirchhoff's formula: $u(t,x) = \frac{\partial}{\partial t}\left[\frac{1}{4\pi t}\int_{\partial B_t(x)} f(\sigma)\,d\sigma\right] + \frac{1}{4\pi t}\int_{\partial B_t(x)} g(\sigma)\,d\sigma$.

## Statement 43: Corollary 2.1.1 (Lorentz transformations preserve causal character)
If $X$ is timelike and $\Lambda$ is a Lorentz transformation, then $\Lambda X$ is also timelike. Analogous results hold for spacelike and null vectors.

## Statement 44: Proposition 2.2.1 (Null frame decomposition of the Minkowski metric)
If $\{L, \underline{L}, e_{(1)}, \dots, e_{(n-1)}\}$ is a null frame, then the Minkowski metric $m$ can be decomposed in terms of the null frame.

## Statement 45: Lemma 1.0.2 (Divergence of the energy-momentum tensor)
Let $T_{\mu\nu}$ be the energy-momentum tensor for the wave equation. Then $\partial_\mu T^{\mu\nu} = (\Box_m \phi)\partial^\nu \phi$.

## Statement 46: Corollary 1.0.3 (Divergence-free energy-momentum tensor for solutions)
For solutions $\phi$ to the wave equation $\Box_m \phi = 0$, the energy-momentum tensor is divergence-free: $\partial_\mu T^{\mu\nu} = 0$.

## Statement 47: Theorem 1.1 (Divergence Theorem for the wave equation)
Let $\phi$ be a solution to $\Box_m \phi = 0$, let $X$ be any vectorfield, and let $(X)J$ be the compatible current. Let $\Omega \subset \mathbb{R}^{1+n}$ be a domain with boundary $\partial\Omega$. Then $\int_{\Omega} \partial_\mu {}^{(X)}J^\mu\,d^{1+n}x = \int_{\partial\Omega} {}^{(X)}J^\mu \nu_\mu\,d\sigma$.

## Statement 48: Theorem 2.1 (Energy estimates in a cone)
Let $\phi(t,x)$ be a $C^2$ solution to the 1+n dimensional global Cauchy problem for the linear wave equation. Then energy estimates hold in a truncated cone $C_{p;R}$.

## Statement 49: Corollary 2.0.4 (Uniqueness for the wave equation)
Suppose that two $C^2$ solutions $\phi_1$ and $\phi_2$ to the wave equation have the same initial data on $B_R(p)$. Then the two solutions agree on the solid backwards light cone $C_{p;R}$.

## Statement 50: Theorem 3.1 (Classification of second order constant-coefficient PDEs)
Consider $A^{\alpha\beta}\partial_\alpha\partial_\beta u + B^\alpha\partial_\alpha u + Cu = 0$. There exists a linear change of variables under which: if all eigenvalues of $A$ have the same sign, the equation becomes elliptic ($\Delta u + \cdots = 0$); if $n$ eigenvalues have one sign and one has the opposite, it becomes hyperbolic ($\Box u + \cdots = 0$); if one eigenvalue is zero, it becomes parabolic.

## Statement 51: Lemma 2.0.1 (Properties of the Fourier transform for $L^1$ functions)
Suppose $f \in L^1(\mathbb{R}^n)$. Then $\hat{f}$ is a bounded, continuous function and $\|\hat{f}\|_{L^\infty} \le \|f\|_{L^1}$.

## Statement 52: Theorem 2.1 (Important properties of the Fourier transform)
Assume $f, g \in L^1(\mathbb{R}^n)$. Then: (a) $(\tau_y f)^\wedge(\xi) = e^{-2\pi i\xi\cdot y}\hat{f}(\xi)$; (b) the Fourier transform of a derivative equals multiplication by $2\pi i\xi$; (c) the Fourier transform of a convolution equals the product of Fourier transforms; and other standard properties.

## Statement 53: Proposition 2.0.2 (Rapid decay of Fourier transforms of smooth compactly supported functions)
Let $f \in C_c^{\infty}(\mathbb{R}^n)$. Then $\hat{f}$ is smooth and rapidly decaying: for each $N \ge 0$, there exists $C_N > 0$ such that $|\hat{f}(\xi)| \le C_N(1 + |\xi|)^{-N}$.

## Statement 54: Proposition 3.0.3 (Fourier transform of a Gaussian)
Let $f(x) = \exp(-\pi z|x|^2)$ where $z = a + ib$, $a > 0$. Then $\hat{f}(\xi) = z^{-n/2}\exp(-\pi|\xi|^2/z)$.

## Statement 55: Lemma 4.0.4 (Interaction of Fourier transform with $L^2$ inner product)
Assume $f, g \in L^1$. Then $\langle \hat{f}, g \rangle = \langle f, \hat{g} \rangle$ and $\langle \hat{f}, \bar{g} \rangle = \langle f, \bar{g}^\vee \rangle$.

## Statement 56: Theorem 4.1 (Fourier inversion theorem)
Suppose $f : \mathbb{R}^n \to \mathbb{C}$ is continuous, $f \in L^1$, and $\hat{f} \in L^1$. Then $(\hat{f})^\vee = (f^\vee)^\wedge = f$.

## Statement 57: Theorem 4.2 (The Plancherel theorem)
Suppose $f, g : \mathbb{R}^n \to \mathbb{C}$ are continuous, $f, g \in L^1 \cap L^2$, and $\hat{f}, \hat{g} \in L^1$. Then $\hat{f}, \hat{g} \in L^2$ and $\langle f, g \rangle = \langle \hat{f}, \hat{g} \rangle$. In particular, $\|f\|_{L^2} = \|\hat{f}\|_{L^2}$.

## Statement 58: Proposition 2.0.1 (Fundamental solution for Schrodinger's equation)
Let $\phi(x)$ be a smooth compactly supported function. The fundamental solution $K(t,x)$ for Schrodinger's equation is computed via the Fourier transform.

## Statement 59: Lemma 2.0.2 (K(t,x) verifies the free Schrodinger equation)
For $t > 0$, $K(t,x)$ is a solution to the free Schrodinger equation $i\partial_t \psi + \Delta\psi = 0$.

## Statement 60: Proposition 2.0.3 (Behavior of $K(t,\cdot) * \phi(\cdot)$ as $t \downarrow 0$)
Let $\phi \in C_c^{\infty}(\mathbb{R}^n)$. Then $\lim_{t \downarrow 0} K(t,\cdot) * \phi = \phi$ pointwise.

## Statement 61: Theorem 2.1 (Solution to the global Cauchy problem for Schrodinger's equation)
Let $\phi(x) \in C_c^{\infty}(\mathbb{R}^n)$. Then there exists a unique solution $\psi \in C^{\infty}((0,\infty) \times \mathbb{R}^n)$ to the free Schrodinger equation with $\psi(0,x) = \phi(x)$, and the dispersive estimate $\|\psi(t,\cdot)\|_{L^\infty} \le C t^{-n/2}\|\phi\|_{L^1}$ holds.

## Statement 62: Proposition 2.0.4 (Preservation of $L^2$ norm for Schrodinger)
Under the assumptions of Theorem 2.1, $\|\psi(t,\cdot)\|_{L^2} = \|\phi\|_{L^2}$ for all $t > 0$.

## Statement 63: Theorem 1.1 (The Principle of Stationary Action / Euler-Lagrange equation)
Let $\mathcal{L}(\phi, \nabla\phi, x)$ be a $C^2$ Lagrangian. Then a $C^2$ field $\phi$ is a stationary point of the action if and only if $\nabla_\alpha\left(\frac{\partial\mathcal{L}}{\partial(\nabla_\alpha\phi)}\right) = \frac{\partial\mathcal{L}}{\partial\phi}$.

## Statement 64: Proposition 2.0.1 (Basic facts from ODE theory for autonomous systems)
Let $Y(x)$ be a smooth vectorfield on $\mathbb{R}^{1+n}$ with bounded derivatives. Then the initial value problem $\frac{d}{d\epsilon}\widetilde{x}^\mu = Y^\mu(\widetilde{x})$ has a unique smooth solution, and the flow map is a diffeomorphism satisfying the one-parameter group property $F_{\epsilon_1} \circ F_{\epsilon_2} = F_{\epsilon_1 + \epsilon_2}$.

## Statement 65: Proposition 2.0.2 (Derivatives with respect to the flow parameter)
Under the flow map $F_\epsilon$, the transformed fields satisfy explicit derivative formulas with respect to $\epsilon$.

## Statement 66: Corollary 2.0.3 (Derivative of the Lagrangian with respect to the flow parameter)
Let $\mathcal{L}(\phi, \nabla\phi, m)$ be a $C^2$ Lagrangian. Then the derivative of $\mathcal{L}$ with respect to the flow parameter $\epsilon$ satisfies an explicit identity.

## Statement 67: Theorem 3.1 (Derivation and divergence-free property of the energy-momentum tensor)
Let $\mathcal{L}(\phi, \nabla\phi, m)$ be a coordinate invariant Lagrangian. Then the energy-momentum tensor $T^{\mu\nu}$ is divergence-free for solutions to the Euler-Lagrange equation: $\partial_\mu T^{\mu\nu} = 0$.

## Statement 68: Proposition 1.0.1 (Connection between transport equations and ODEs)
If $u$ solves the transport equation, then $u$ is constant along the integral curves of the transport vector field $X$. More precisely, if $\gamma(s)$ is any solution to the characteristic ODE, then $u(\gamma(s))$ is constant.

## Statement 69: Proposition 2.0.1 (Burger's equation is a conservation law)
Let $u(t,x)$ be a $C^1$ solution to Burger's equation on $[0,T] \times \mathbb{R}$ with $\lim_{x \to \pm\infty} u(t,x) = 0$. Then $\frac{d}{dt}\int_{\mathbb{R}} u^2(t,x)\,dx = 0$.

## Statement 70: Proposition 2.0.2 (Burger solutions are constant along characteristics)
$C^1$ solutions to Burger's equation are constant along the characteristic curves.

## Statement 71: Proposition 2.0.3 (Burger characteristics are straight lines)
The characteristic curves for Burger's equation are straight lines in $\mathbb{R}^{1+1}$.

## Statement 72: Theorem 3.1 (Implicit solution to Burger's equation)
Let $u$ be a $C^1$ solution to Burger's equation, and let $(t,x)$ be a spacetime point. If the implicit equation $x = p + f(p)t$ has a unique solution in $p$, then $u(t,x) = f(p)$.

## Statement 73: Theorem 4.1 (Sharp characterization of singularity formation in Burger's equation)
Let $f \in C^1(\mathbb{R})$ be initial data for Burger's equation. Then the corresponding solution $u(t,x)$ remains $C^1$ for all $(t,x) \in [0,\infty) \times \mathbb{R}$ if and only if $f'(x) \ge 0$ for all $x \in \mathbb{R}$.
