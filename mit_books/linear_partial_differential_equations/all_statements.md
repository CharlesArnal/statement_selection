# All Mathematical Statements

## Statement 1: Theorem (Eigenfunctions of the 1d Laplacian with Dirichlet boundary conditions)
The eigenfunctions of the operator $\hat{A} = d^2/dx^2$ on the space of functions $u(x)$ on $[0,L]$ with $u(0) = u(L) = 0$ (Dirichlet boundary conditions) are $\sin(n\pi x/L)$ with eigenvalues $-(n\pi/L)^2$ for positive integers $n$.

## Statement 2: Theorem (Null space of the 1d Laplacian with Dirichlet boundary conditions)
The null space of $\hat{A} = d^2/dx^2$ on the space of functions $u(x)$ on $[0,L]$ with $u(0) = u(L) = 0$ is $\{0\}$. Consequently, any solution to $\hat{A}u = f$ (Poisson's equation) is unique.

## Statement 3: Theorem (Discrete Laplacian is negative definite)
The discrete Laplacian matrix $A = -D^T D$, obtained by center-difference discretization of $d^2/dx^2$ with Dirichlet boundary conditions on $[0,L]$, is negative definite. This follows from the fact that $D$ is full column rank (as $D^T$ is upper-triangular with nonzero diagonal).

## Statement 4: Theorem (Self-adjointness of the 1d Laplacian)
The operator $d^2/dx^2$ on the space of functions on $[0,L]$ with Dirichlet boundary conditions $u(0) = u(L) = 0$ is self-adjoint (Hermitian) with respect to the inner product $\langle u,v \rangle = \int_0^L \overline{u} v \, dx$. This is proved by integration by parts.

## Statement 5: Theorem (Negative definiteness of the 1d Laplacian)
The operator $d^2/dx^2$ on the space of functions on $[0,L]$ with Dirichlet boundary conditions is negative definite: $\langle u, u'' \rangle = -\int |u'|^2 \, dx \leq 0$, with equality only if $u' = 0$, which for these boundary conditions implies $u = 0$.

## Statement 6: Theorem (Real eigenvalues of self-adjoint operators)
If $\hat{A}$ is a self-adjoint (Hermitian) operator on a Hilbert space, then all eigenvalues of $\hat{A}$ are real. The proof from the finite-dimensional (matrix) case carries over without modification.

## Statement 7: Theorem (Orthogonality of eigenvectors of self-adjoint operators)
If $\hat{A}$ is a self-adjoint (Hermitian) operator, then eigenvectors corresponding to distinct eigenvalues are orthogonal. In particular, the Fourier sine series $\{\sin(n\pi x/L)\}$ forms an orthogonal set.

## Statement 8: Theorem (Self-adjointness of non-uniform 1d Laplacian)
The operator $d/dx [c(x) \, d/dx]$ with $c(x) > 0$ and Dirichlet boundary conditions $u(0) = u(L) = 0$ is self-adjoint and negative definite with respect to the standard $L^2$ inner product.

## Statement 9: Theorem (Self-adjointness under modified inner product)
The operator $c(x) d^2/dx^2$ for real $c(x) > 0$ is self-adjoint under the weighted inner product $\langle u,v \rangle = \int \overline{u}v/c \, dx$, and therefore has real, negative eigenvalues and orthogonal eigenfunctions under this inner product.

## Statement 10: Theorem (Properties of Sturm-Liouville operators)
The Sturm-Liouville operator $\hat{A} = w(x)^{-1} [-d/dx(c(x) \, d/dx) + p(x)]$ with Dirichlet boundary conditions on $[0,L]$ is self-adjoint under the weighted inner product $\langle u,v \rangle = \int w \overline{u} v \, dx$, assuming $w$ is real and positive and $c$ and $p$ are real. If additionally $c \geq 0$ and $p \geq 0$, the operator is positive definite (elliptic).

## Statement 11: Theorem (Self-adjointness of multi-dimensional Sturm-Liouville operators)
The operator $\hat{A} = w(\mathbf{x})^{-1} [-\nabla \cdot (\mathbf{c}(\mathbf{x}) \nabla) + p(\mathbf{x})]$ with Dirichlet boundary conditions on a finite domain $\Omega$ is self-adjoint for real coefficients and $w > 0$, and positive definite (elliptic) for $c \geq 0$ and $p > 0$. The proof uses the divergence theorem.

## Statement 12: Theorem (Conservation law from left null space)
For any equation $\hat{A}u = \partial u/\partial t$, there is a conservation law $\partial/\partial t \, \langle v, u \rangle = 0$ for any $v(\mathbf{x})$ in the left null space $N(\hat{A}^*)$.

## Statement 13: Theorem (Conservation of mass for diffusion with Neumann boundary conditions)
For the diffusion equation $\hat{A}u = \partial u/\partial t$ with $\hat{A} = \nabla \cdot c\nabla$ and Neumann boundary conditions, $\hat{A}$ is self-adjoint and negative semidefinite. The null space $N(\hat{A}) = N(\hat{A}^*)$ contains any constant function. Hence the total mass $\langle 1, u \rangle = \int_\Omega u$ is conserved.

## Statement 14: Theorem (Self-adjointness of the 1d Laplacian with periodic boundary conditions)
The operator $\hat{A} = d^2/dx^2$ on $[0,L]$ with periodic boundary conditions $u(0) = u(L)$ is self-adjoint and negative semidefinite. The eigenfunctions are sines and cosines of $2\pi n x/L$, giving a general Fourier series.

## Statement 15: Theorem (Separability of Laplacian eigenfunctions in a 2d box)
The eigenfunctions of $\nabla^2 u = \lambda u$ in a 2d $L_x \times L_y$ box with Dirichlet boundary conditions are of the form $\sin(n_x \pi x/L_x) \sin(n_y \pi y/L_y)$ with eigenvalues $\lambda = -(n_x \pi/L_x)^2 - (n_y \pi/L_y)^2$, forming a 2d Fourier sine series. These eigenfunctions are real, negative, and orthogonal.

## Statement 16: Theorem (Separability in cylindrical coordinates and Bessel functions)
The Laplacian eigenproblem $\nabla^2 u = \lambda u$ in a cylinder of radius $R$ with Dirichlet boundary conditions is separable into $u(r,\theta) = R(r) \Theta(\theta)$. The angular part gives $\Theta(\theta) = \sin(m\theta)$ or $\cos(m\theta)$ for integer $m$. The radial part satisfies Bessel's equation, with solutions $J_m(kr)$ (finite at $r = 0$) and $Y_m(kr)$ (divergent at $r = 0$). Eigenfunctions require $J_m(kR) = 0$, giving a discrete set of eigenvalues.

## Statement 17: Theorem (Min-max theorem for eigenvalues)
For a self-adjoint positive-definite operator $\hat{A}$ (or equivalently, a self-adjoint negative-definite operator $-\hat{A}$), the eigenvalues can be characterized via the Rayleigh quotient. The smallest eigenvalue equals the minimum of the Rayleigh quotient $\langle u, \hat{A}u \rangle / \langle u, u \rangle$, and higher eigenvalues are obtained by minimizing over subspaces orthogonal to the previously found eigenvectors.

## Statement 18: Theorem (Green's function of $-d^2/dx^2$ with Dirichlet boundaries)
The Green's function $G(x,x')$ of $-d^2/dx^2$ on $[0,L]$ with Dirichlet boundary conditions satisfies $-G''(x,x') = \delta(x - x')$ and $u(x) = \int_0^L G(x,x') f(x') \, dx'$ solves $-u'' = f$. The Green's function is symmetric: $G(x,x') = G(x',x)$ (reciprocity), and positive.

## Statement 19: Theorem (Green's function of $-\nabla^2$ in $\mathbb{R}^3$)
The Green's function of $-\nabla^2$ in $\mathbb{R}^3$ (infinite space, requiring solutions to vanish at infinity) is $G(\mathbf{x}, \mathbf{x}') = 1/(4\pi|\mathbf{x} - \mathbf{x}'|)$. This is derived using translational and rotational invariance, and verified by computing the distributional derivative.

## Statement 20: Theorem (Method of images for half-space)
The Green's function of $-\nabla^2$ in the half-space $z > 0$ with Dirichlet boundary conditions ($u = 0$ at $z = 0$) is $G(\mathbf{x}, \mathbf{x}') = (1/|{\mathbf{x} - \mathbf{x}'}| - 1/|{\mathbf{x} - \mathbf{x}''}|)/(4\pi)$, where $\mathbf{x}''$ is the reflection of $\mathbf{x}'$ across $z = 0$ (i.e., $\mathbf{x}''$ has the sign of the $z$-component of $\mathbf{x}'$ flipped).

## Statement 21: Theorem (Lax equivalence theorem)
For any consistent discretization of a well-posed linear initial-value problem, stability implies convergence and vice versa.

## Statement 22: Theorem (Conditional stability of explicit timestepping for the heat equation)
For explicit (forward-difference) timestepping of the heat equation $\hat{A}u = \partial u/\partial t$ with $\hat{A} = \nabla^2$ discretized by center differences, the scheme $u^{n+1} = (1 + A\Delta t) u^n$ is conditionally stable: $\Delta t < 2/|\lambda_{\max}|$ is required, where $\lambda_{\max}$ is the largest-magnitude eigenvalue of $A$.

## Statement 23: Theorem (Unconditional stability of implicit timestepping)
For implicit (backward-difference) timestepping of the heat equation with a negative-definite operator $A$, the scheme $u^{n+1} = (1 - A\Delta t)^{-1} u^n$ is unconditionally stable (decaying for any $\Delta t > 0$).

## Statement 24: Theorem (Unconditional stability of Crank-Nicolson scheme)
The Crank-Nicolson scheme $u^{n+1} = (1 - A\Delta t/2)^{-1}(1 + A\Delta t/2) u^n$ is unconditionally stable if $A$ is negative definite. It is second-order accurate in both space and time.

## Statement 25: Theorem (Von Neumann analysis of the discrete 1d Laplacian)
For $\hat{A} = d^2/dx^2$ discretized by center differences in infinite space, the eigenvectors are $u_m = e^{ikm}$ with eigenvalues $\lambda(k) = -4\sin^2(k/2)/\Delta x^2$. The maximum $|\lambda|$ occurs at $k = \pi$. For forward-difference timestepping, conditional stability requires $\Delta t < \Delta x^2/2$.

## Statement 26: Theorem (D'Alembert's solution to the 1d wave equation)
For the 1d scalar wave equation $c^2 \partial^2 u/\partial x^2 = \partial^2 u/\partial t^2$ on an infinite domain with constant coefficient $c$, any function $f(x)$ gives solutions $u(x,t) = f(x \pm ct)$. These describe the function $f(x)$ moving to the left or right with speed $c$.

## Statement 27: Theorem (Anti-Hermiticity of the first-order wave equation operator)
Writing the scalar wave equation as a first-order system $\partial \mathbf{w}/\partial t = \hat{A}\mathbf{w}$ where $\mathbf{w} = (u; \mathbf{v})$ and $\hat{A} = \begin{pmatrix} 0 & \nabla \cdot \\ \nabla & 0 \end{pmatrix}$, the operator $\hat{A}$ satisfies $\hat{A}^* = -\hat{A}$ (anti-Hermitian) for Dirichlet or Neumann boundary conditions. Consequently, eigenvalues are purely imaginary, giving oscillating solutions $e^{-i\omega t}$, and $\langle w, w \rangle$ (energy) is conserved.

## Statement 28: Theorem (Snell's Law)
When a plane wave in a region with speed $c_1$ is incident upon an interface to a region with speed $c_2$, the transmitted wave satisfies $(1/c_1)\sin\theta_1 = (1/c_2)\sin\theta_2$ where $\theta_1$ and $\theta_2$ are the angles of incidence and transmission. Also, the reflected angle equals the incident angle (Law of Equal Angles).

## Statement 29: Theorem (Total internal reflection)
If $c_1 < c_2$ (the wave travels faster in the second medium), then for sufficiently large angle of incidence $\theta_1 > \theta_c = \arcsin(c_1/c_2)$, there is no real transmission angle, and total internal reflection occurs. The transmitted wave becomes exponentially decaying (evanescent).

## Statement 30: Theorem (Existence of guided modes from slow regions)
Under very general conditions, any region with a smaller wave speed $c$ in a wave equation system leads to guided-wave (localized) solutions. This is proved using the min-max theorem.

## Statement 31: Theorem (Galerkin discretization preserves operator properties)
In a Galerkin finite-element discretization, if the operator $\hat{A}$ is self-adjoint, then the resulting matrix $A$ is Hermitian; if $\hat{A}$ is positive-definite (or negative-definite), then $A$ is positive-definite (or negative-definite). The Galerkin solution $\tilde{u}$ is the orthogonal projection of the exact solution $u$ onto the finite-element space $\tilde{V}$ in the $\langle \cdot, \cdot \rangle_A$ inner product, minimizing $\|\tilde{u} - u\|_A$.

## Statement 32: Theorem (Hellmann-Feynman theorem and group velocity as energy velocity)
For self-adjoint eigenproblems, first-order perturbation theory yields the Hellmann-Feynman theorem. Applied to waveguide modes, the group velocity $d\omega/dk$ can be evaluated via Hellmann-Feynman, yielding a ratio of energy flux to energy density: an "energy velocity".
