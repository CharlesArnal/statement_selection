# Detailed Assessment

## Statement 1: Theorem (Eigenfunctions of the 1d Laplacian with Dirichlet boundary conditions)
The eigenfunctions of the operator $\hat{A} = d^2/dx^2$ on the space of functions $u(x)$ on $[0,L]$ with $u(0) = u(L) = 0$ (Dirichlet boundary conditions) are $\sin(n\pi x/L)$ with eigenvalues $-(n\pi/L)^2$ for positive integers $n$.

Assessment: non-included

Mathlib has a general definition of the Laplacian in `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` and defines harmonic functions in `Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`, but these work on finite-dimensional inner product spaces without specifying boundary conditions on intervals. Mathlib does not contain a formalization of the eigenvalue problem for the 1d Laplacian on a bounded interval with Dirichlet boundary conditions, nor an explicit identification of the eigenfunctions as sine functions. There is no Sturm-Liouville theory in mathlib. Searched for "Laplacian", "eigenfunction", "Dirichlet", "Sturm-Liouville", and "SturmLiouville" with no relevant results.

## Statement 2: Theorem (Null space of the 1d Laplacian with Dirichlet boundary conditions)
The null space of $\hat{A} = d^2/dx^2$ on the space of functions $u(x)$ on $[0,L]$ with $u(0) = u(L) = 0$ is $\{0\}$. Consequently, any solution to $\hat{A}u = f$ (Poisson's equation) is unique.

Assessment: non-included

Mathlib does not formalize the 1d Laplacian as an operator on function spaces with specific boundary conditions. While mathlib has general results about kernel (null space) of linear maps, the specific PDE statement about the trivial null space of $d^2/dx^2$ with Dirichlet boundary conditions is not present. Searched for "Poisson", "Laplacian", "Dirichlet", "null space" in the Analysis directories with no matching formalization.

## Statement 3: Theorem (Discrete Laplacian is negative definite)
The discrete Laplacian matrix $A = -D^T D$, obtained by center-difference discretization of $d^2/dx^2$ with Dirichlet boundary conditions on $[0,L]$, is negative definite. This follows from the fact that $D$ is full column rank (as $D^T$ is upper-triangular with nonzero diagonal).

Assessment: non-included

This is a numerical analysis statement about a specific matrix discretization. Mathlib does not contain finite-difference discretizations of differential operators. While mathlib has the concept of positive-definite matrices (`Mathlib/LinearAlgebra/Matrix/PosDef.lean`) and can express that $-D^T D$ is negative semidefinite, the specific tridiagonal discrete Laplacian matrix and its negative definiteness are not formalized. Searched for "discrete Laplacian", "finite difference", "tridiagonal" with no results.

## Statement 4: Theorem (Self-adjointness of the 1d Laplacian)
The operator $d^2/dx^2$ on the space of functions on $[0,L]$ with Dirichlet boundary conditions $u(0) = u(L) = 0$ is self-adjoint (Hermitian) with respect to the inner product $\langle u,v \rangle = \int_0^L \overline{u} v \, dx$. This is proved by integration by parts.

Assessment: non-included

Mathlib has extensive theory of symmetric/self-adjoint linear maps on inner product spaces (`Mathlib/Analysis/InnerProductSpace/Symmetric.lean`, `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`), but these are for abstract operators on Hilbert spaces, not for specific differential operators with boundary conditions. The concrete statement that $d^2/dx^2$ with Dirichlet BCs is self-adjoint (requiring integration by parts and boundary term analysis) is not in mathlib. Searched for "Laplacian" combined with "selfAdjoint" or "IsSymmetric" with no results linking them.

## Statement 5: Theorem (Negative definiteness of the 1d Laplacian)
The operator $d^2/dx^2$ on the space of functions on $[0,L]$ with Dirichlet boundary conditions is negative definite: $\langle u, u'' \rangle = -\int |u'|^2 \, dx \leq 0$, with equality only if $u' = 0$, which for these boundary conditions implies $u = 0$.

Assessment: non-included

While mathlib has abstract notions of positive/negative definiteness for operators and bilinear forms, the concrete computation showing that the Laplacian with Dirichlet boundary conditions satisfies $\langle u, u'' \rangle = -\|u'\|^2$ via integration by parts is not formalized. Searched for "NegDef", "negDefinite", "Laplacian" in relevant directories without finding this specific result.

## Statement 6: Theorem (Real eigenvalues of self-adjoint operators)
If $\hat{A}$ is a self-adjoint (Hermitian) operator on a Hilbert space, then all eigenvalues of $\hat{A}$ are real. The proof from the finite-dimensional (matrix) case carries over without modification.

Assessment: included

This is formalized in mathlib at `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` as `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`, which states that if `T` is symmetric and `mu` is an eigenvalue, then `conj mu = mu`, i.e., the eigenvalue is real. The file header explicitly lists this as one of the main results: "the eigenvalues are real." For matrices specifically, `Mathlib/Analysis/Matrix/Spectrum.lean` contains the corresponding matrix version via `IsHermitian`.

## Statement 7: Theorem (Orthogonality of eigenvectors of self-adjoint operators)
If $\hat{A}$ is a self-adjoint (Hermitian) operator, then eigenvectors corresponding to distinct eigenvalues are orthogonal. In particular, the Fourier sine series $\{\sin(n\pi x/L)\}$ forms an orthogonal set.

Assessment: included

This is formalized in mathlib at `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` as `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`, which states that the eigenspaces of a symmetric operator form an orthogonal family. The specific application to Fourier sine series is not formalized, but the abstract orthogonality result for self-adjoint operators is present.

## Statement 8: Theorem (Self-adjointness of non-uniform 1d Laplacian)
The operator $d/dx [c(x) \, d/dx]$ with $c(x) > 0$ and Dirichlet boundary conditions $u(0) = u(L) = 0$ is self-adjoint and negative definite with respect to the standard $L^2$ inner product.

Assessment: non-included

This is a PDE-specific result about a variable-coefficient differential operator with boundary conditions. Mathlib does not formalize differential operators with variable coefficients or their self-adjointness properties. Searched for "Sturm-Liouville", "variable coefficient", and related terms with no results.

## Statement 9: Theorem (Self-adjointness under modified inner product)
The operator $c(x) d^2/dx^2$ for real $c(x) > 0$ is self-adjoint under the weighted inner product $\langle u,v \rangle = \int \overline{u}v/c \, dx$, and therefore has real, negative eigenvalues and orthogonal eigenfunctions under this inner product.

Assessment: non-included

This statement requires defining weighted inner products on function spaces and proving self-adjointness of specific differential operators with respect to such inner products. Mathlib has abstract inner product space theory but does not formalize weighted $L^2$ spaces as inner product spaces for specific differential operators. No relevant results found searching for weighted inner products combined with differential operators.

## Statement 10: Theorem (Properties of Sturm-Liouville operators)
The Sturm-Liouville operator $\hat{A} = w(x)^{-1} [-d/dx(c(x) \, d/dx) + p(x)]$ with Dirichlet boundary conditions on $[0,L]$ is self-adjoint under the weighted inner product $\langle u,v \rangle = \int w \overline{u} v \, dx$, assuming $w$ is real and positive and $c$ and $p$ are real. If additionally $c \geq 0$ and $p \geq 0$, the operator is positive definite (elliptic).

Assessment: non-included

Sturm-Liouville theory is not formalized in mathlib. Searched for "Sturm", "Liouville", "SturmLiouville" across all of mathlib with no results. The general framework of elliptic operators, weighted Sobolev spaces, and their spectral properties is absent from mathlib v4.27.0.

## Statement 11: Theorem (Self-adjointness of multi-dimensional Sturm-Liouville operators)
The operator $\hat{A} = w(\mathbf{x})^{-1} [-\nabla \cdot (\mathbf{c}(\mathbf{x}) \nabla) + p(\mathbf{x})]$ with Dirichlet boundary conditions on a finite domain $\Omega$ is self-adjoint for real coefficients and $w > 0$, and positive definite (elliptic) for $c \geq 0$ and $p > 0$. The proof uses the divergence theorem.

Assessment: non-included

While mathlib has the divergence theorem formalized for box integrals (`Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`) and Bochner integrals (`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`), these are stated for rectangular boxes in $\mathbb{R}^n$, not for general domains with boundary conditions. The multi-dimensional Sturm-Liouville theory connecting the divergence theorem to self-adjointness of elliptic operators is not present. Searched for "elliptic" (only found elliptic functions/curves), "Sturm", "divergence" combined with "selfAdjoint" with no results.

## Statement 12: Theorem (Conservation law from left null space)
For any equation $\hat{A}u = \partial u/\partial t$, there is a conservation law $\partial/\partial t \, \langle v, u \rangle = 0$ for any $v(\mathbf{x})$ in the left null space $N(\hat{A}^*)$.

Assessment: non-included

This is a PDE-specific result relating the adjoint operator's null space to conserved quantities in time-dependent equations. Mathlib does not formalize time-dependent PDE evolution equations or their conservation laws. While mathlib has adjoint operators (`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`), the connection to conservation laws for PDEs is not present. Searched for "conservation", "conserved", "null space" combined with PDE terms with no results.

## Statement 13: Theorem (Conservation of mass for diffusion with Neumann boundary conditions)
For the diffusion equation $\hat{A}u = \partial u/\partial t$ with $\hat{A} = \nabla \cdot c\nabla$ and Neumann boundary conditions, $\hat{A}$ is self-adjoint and negative semidefinite. The null space $N(\hat{A}) = N(\hat{A}^*)$ contains any constant function. Hence the total mass $\langle 1, u \rangle = \int_\Omega u$ is conserved.

Assessment: non-included

This is an application of the conservation law theorem to the specific case of the diffusion equation with Neumann boundary conditions. Mathlib has no formalization of the diffusion/heat equation, Neumann boundary conditions, or mass conservation for parabolic PDEs. Searched for "heat_equation", "diffusion", "Neumann", "conservation" with no relevant results.

## Statement 14: Theorem (Self-adjointness of the 1d Laplacian with periodic boundary conditions)
The operator $\hat{A} = d^2/dx^2$ on $[0,L]$ with periodic boundary conditions $u(0) = u(L)$ is self-adjoint and negative semidefinite. The eigenfunctions are sines and cosines of $2\pi n x/L$, giving a general Fourier series.

Assessment: non-included

While mathlib has Fourier series on the additive circle (`Mathlib/Analysis/Fourier/AddCircle.lean`), including Fourier coefficients and convergence results, it does not formalize the Laplacian $d^2/dx^2$ as an operator on periodic function spaces or establish its self-adjointness and eigenfunction decomposition in this context. The Fourier series machinery is analytic/measure-theoretic rather than spectral-theoretic for differential operators.

## Statement 15: Theorem (Separability of Laplacian eigenfunctions in a 2d box)
The eigenfunctions of $\nabla^2 u = \lambda u$ in a 2d $L_x \times L_y$ box with Dirichlet boundary conditions are of the form $\sin(n_x \pi x/L_x) \sin(n_y \pi y/L_y)$ with eigenvalues $\lambda = -(n_x \pi/L_x)^2 - (n_y \pi/L_y)^2$, forming a 2d Fourier sine series. These eigenfunctions are real, negative, and orthogonal.

Assessment: non-included

This is a multi-dimensional PDE eigenvalue problem with specific domain geometry and boundary conditions. Mathlib does not formalize PDE eigenvalue problems on bounded domains, separation of variables techniques, or multi-dimensional Fourier sine series. Searched for "separation of variables", "Laplacian eigenfunctions", "2d Fourier" with no results.

## Statement 16: Theorem (Separability in cylindrical coordinates and Bessel functions)
The Laplacian eigenproblem $\nabla^2 u = \lambda u$ in a cylinder of radius $R$ with Dirichlet boundary conditions is separable into $u(r,\theta) = R(r) \Theta(\theta)$. The angular part gives $\Theta(\theta) = \sin(m\theta)$ or $\cos(m\theta)$ for integer $m$. The radial part satisfies Bessel's equation, with solutions $J_m(kr)$ (finite at $r = 0$) and $Y_m(kr)$ (divergent at $r = 0$). Eigenfunctions require $J_m(kR) = 0$, giving a discrete set of eigenvalues.

Assessment: non-included

Mathlib does not contain Bessel functions ($J_m$, $Y_m$), Bessel's equation, or separation of variables in cylindrical/polar coordinates. The term "Bessel" appears in mathlib only in `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean` in the context of "Bessel's inequality" (a different result about orthonormal systems), not Bessel functions. Searched for "Bessel", "cylindrical", "polar coordinates" with no relevant results.

## Statement 17: Theorem (Min-max theorem for eigenvalues)
For a self-adjoint positive-definite operator $\hat{A}$ (or equivalently, a self-adjoint negative-definite operator $-\hat{A}$), the eigenvalues can be characterized via the Rayleigh quotient. The smallest eigenvalue equals the minimum of the Rayleigh quotient $\langle u, \hat{A}u \rangle / \langle u, u \rangle$, and higher eigenvalues are obtained by minimizing over subspaces orthogonal to the previously found eigenvectors.

Assessment: included

Mathlib contains the Rayleigh quotient and its variational characterization of eigenvalues in `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`. Specifically, `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and `IsSelfAdjoint.hasEigenvector_of_isMinOn` establish that extrema of the Rayleigh quotient correspond to eigenvectors with eigenvalue equal to the supremum/infimum of the quotient. The file `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` further provides `LinearMap.IsSymmetric.eigenvalues` listing eigenvalues in decreasing order, with the spectral decomposition theorem for finite-dimensional spaces. Together these constitute the min-max characterization of eigenvalues.

## Statement 18: Theorem (Green's function of $-d^2/dx^2$ with Dirichlet boundaries)
The Green's function $G(x,x')$ of $-d^2/dx^2$ on $[0,L]$ with Dirichlet boundary conditions satisfies $-G''(x,x') = \delta(x - x')$ and $u(x) = \int_0^L G(x,x') f(x') \, dx'$ solves $-u'' = f$. The Green's function is symmetric: $G(x,x') = G(x',x)$ (reciprocity), and positive.

Assessment: non-included

Mathlib does not contain Green's functions for differential operators. While mathlib has distributions/tempered distributions (`Mathlib/Analysis/Distribution/TemperedDistribution.lean`) and the Dirac delta measure (`Mathlib/MeasureTheory/Measure/Dirac.lean`), there is no formalization connecting these to Green's functions or inverse operators for boundary value problems. Searched for "GreenFunction", "Green", "inverse" combined with "Laplacian" with no results.

## Statement 19: Theorem (Green's function of $-\nabla^2$ in $\mathbb{R}^3$)
The Green's function of $-\nabla^2$ in $\mathbb{R}^3$ (infinite space, requiring solutions to vanish at infinity) is $G(\mathbf{x}, \mathbf{x}') = 1/(4\pi|\mathbf{x} - \mathbf{x}'|)$. This is derived using translational and rotational invariance, and verified by computing the distributional derivative.

Assessment: non-included

Mathlib does not contain the fundamental solution (Green's function) of the Laplacian in $\mathbb{R}^3$. While the Laplacian is defined in `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` and distributions exist in `Mathlib/Analysis/Distribution/TemperedDistribution.lean`, the specific computation of $1/(4\pi r)$ as the Green's function is not present. Searched for "fundamental solution", "GreenFunction", "$1/(4\pi)$" with no results.

## Statement 20: Theorem (Method of images for half-space)
The Green's function of $-\nabla^2$ in the half-space $z > 0$ with Dirichlet boundary conditions ($u = 0$ at $z = 0$) is $G(\mathbf{x}, \mathbf{x}') = (1/|{\mathbf{x} - \mathbf{x}'}| - 1/|{\mathbf{x} - \mathbf{x}''}|)/(4\pi)$, where $\mathbf{x}''$ is the reflection of $\mathbf{x}'$ across $z = 0$ (i.e., $\mathbf{x}''$ has the sign of the $z$-component of $\mathbf{x}'$ flipped).

Assessment: non-included

The method of images is a technique in potential theory/electrostatics that is not formalized in mathlib. It requires Green's functions (not in mathlib), specific domain geometry with boundary conditions, and the reflection principle. Searched for "method of images", "image charge", "half-space" combined with "Green" with no results.

## Statement 21: Theorem (Lax equivalence theorem)
For any consistent discretization of a well-posed linear initial-value problem, stability implies convergence and vice versa.

Assessment: non-included

The Lax equivalence theorem is a fundamental result in numerical analysis for PDEs. Mathlib does not contain numerical PDE theory. While `Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean` contains the Lax-Milgram theorem (a different result about coercive bilinear forms yielding continuous equivalences in Hilbert spaces), the Lax equivalence theorem (Lax-Richtmyer theorem) about stability-convergence equivalence for numerical discretizations is entirely absent. Searched for "Lax equivalence", "LaxRichtmyer", "consistency", "convergence" in numerical contexts with no results.

## Statement 22: Theorem (Conditional stability of explicit timestepping for the heat equation)
For explicit (forward-difference) timestepping of the heat equation $\hat{A}u = \partial u/\partial t$ with $\hat{A} = \nabla^2$ discretized by center differences, the scheme $u^{n+1} = (1 + A\Delta t) u^n$ is conditionally stable: $\Delta t < 2/|\lambda_{\max}|$ is required, where $\lambda_{\max}$ is the largest-magnitude eigenvalue of $A$.

Assessment: non-included

This is a numerical analysis result about time-stepping schemes for PDEs. Mathlib does not contain any numerical PDE methods, time-stepping schemes, or stability analysis for discretized equations. Searched for "timestep", "explicit", "stability", "CFL", "heat equation" with no results.

## Statement 23: Theorem (Unconditional stability of implicit timestepping)
For implicit (backward-difference) timestepping of the heat equation with a negative-definite operator $A$, the scheme $u^{n+1} = (1 - A\Delta t)^{-1} u^n$ is unconditionally stable (decaying for any $\Delta t > 0$).

Assessment: non-included

Same as Statement 22. Numerical time-stepping and stability analysis for PDEs are entirely absent from mathlib. Searched for "implicit", "backward difference", "unconditionally stable" with no results.

## Statement 24: Theorem (Unconditional stability of Crank-Nicolson scheme)
The Crank-Nicolson scheme $u^{n+1} = (1 - A\Delta t/2)^{-1}(1 + A\Delta t/2) u^n$ is unconditionally stable if $A$ is negative definite. It is second-order accurate in both space and time.

Assessment: non-included

The Crank-Nicolson scheme is a specific numerical method for time-dependent PDEs. It is not formalized in mathlib. Searched for "CrankNicolson", "Crank-Nicolson", "implicit scheme" with no results.

## Statement 25: Theorem (Von Neumann analysis of the discrete 1d Laplacian)
For $\hat{A} = d^2/dx^2$ discretized by center differences in infinite space, the eigenvectors are $u_m = e^{ikm}$ with eigenvalues $\lambda(k) = -4\sin^2(k/2)/\Delta x^2$. The maximum $|\lambda|$ occurs at $k = \pi$. For forward-difference timestepping, conditional stability requires $\Delta t < \Delta x^2/2$.

Assessment: non-included

Von Neumann stability analysis is a numerical analysis technique not present in mathlib. This involves discrete Fourier analysis of finite-difference operators, which is outside the scope of mathlib's current coverage. Searched for "Von Neumann", "vonNeumann" combined with "stability" or "analysis" (only found Von Neumann algebras), and "CFL" with no relevant results.

## Statement 26: Theorem (D'Alembert's solution to the 1d wave equation)
For the 1d scalar wave equation $c^2 \partial^2 u/\partial x^2 = \partial^2 u/\partial t^2$ on an infinite domain with constant coefficient $c$, any function $f(x)$ gives solutions $u(x,t) = f(x \pm ct)$. These describe the function $f(x)$ moving to the left or right with speed $c$.

Assessment: non-included

Mathlib does not formalize the wave equation or its solutions. D'Alembert's solution is a classical PDE result that requires the wave equation as a starting point, which is absent from mathlib. Searched for "wave equation", "D'Alembert", "dAlembert", "traveling wave" with no results. Mathlib's ODE library (`Mathlib/Analysis/ODE/`) contains Picard-Lindelof and Gronwall, but not wave equations.

## Statement 27: Theorem (Anti-Hermiticity of the first-order wave equation operator)
Writing the scalar wave equation as a first-order system $\partial \mathbf{w}/\partial t = \hat{A}\mathbf{w}$ where $\mathbf{w} = (u; \mathbf{v})$ and $\hat{A} = \begin{pmatrix} 0 & \nabla \cdot \\ \nabla & 0 \end{pmatrix}$, the operator $\hat{A}$ satisfies $\hat{A}^* = -\hat{A}$ (anti-Hermitian) for Dirichlet or Neumann boundary conditions. Consequently, eigenvalues are purely imaginary, giving oscillating solutions $e^{-i\omega t}$, and $\langle w, w \rangle$ (energy) is conserved.

Assessment: non-included

This statement combines PDE theory (wave equation formulation), operator theory (anti-Hermiticity), and physics (energy conservation). While mathlib has abstract notions of self-adjoint and anti-self-adjoint operators, the specific wave equation operator and its properties are not formalized. Searched for "anti-Hermitian", "antiSelfAdjoint", "skewAdjoint" combined with wave equation concepts with no relevant PDE results.

## Statement 28: Theorem (Snell's Law)
When a plane wave in a region with speed $c_1$ is incident upon an interface to a region with speed $c_2$, the transmitted wave satisfies $(1/c_1)\sin\theta_1 = (1/c_2)\sin\theta_2$ where $\theta_1$ and $\theta_2$ are the angles of incidence and transmission. Also, the reflected angle equals the incident angle (Law of Equal Angles).

Assessment: non-included

Snell's law is a physical/PDE result about wave propagation across interfaces. Mathlib does not contain wave propagation theory, optics, or interface conditions. The term "Snell" appears in mathlib only in number-theoretic contexts (Snell-related combinatorics), not wave physics. Searched for "Snell", "refraction", "reflection" combined with wave terms with no results.

## Statement 29: Theorem (Total internal reflection)
If $c_1 < c_2$ (the wave travels faster in the second medium), then for sufficiently large angle of incidence $\theta_1 > \theta_c = \arcsin(c_1/c_2)$, there is no real transmission angle, and total internal reflection occurs. The transmitted wave becomes exponentially decaying (evanescent).

Assessment: non-included

Total internal reflection is a wave physics phenomenon not formalized in mathlib. This requires wave equation solutions at interfaces, which mathlib does not have. Searched for "total internal reflection", "evanescent", "critical angle" with no results.

## Statement 30: Theorem (Existence of guided modes from slow regions)
Under very general conditions, any region with a smaller wave speed $c$ in a wave equation system leads to guided-wave (localized) solutions. This is proved using the min-max theorem.

Assessment: non-included

This is a result in waveguide theory combining the min-max theorem with wave equation analysis. While mathlib has the Rayleigh quotient and variational eigenvalue characterization, the application to waveguide modes and localization of wave solutions in regions of reduced speed is not present. Searched for "waveguide", "guided mode", "localized solution" with no results.

## Statement 31: Theorem (Galerkin discretization preserves operator properties)
In a Galerkin finite-element discretization, if the operator $\hat{A}$ is self-adjoint, then the resulting matrix $A$ is Hermitian; if $\hat{A}$ is positive-definite (or negative-definite), then $A$ is positive-definite (or negative-definite). The Galerkin solution $\tilde{u}$ is the orthogonal projection of the exact solution $u$ onto the finite-element space $\tilde{V}$ in the $\langle \cdot, \cdot \rangle_A$ inner product, minimizing $\|\tilde{u} - u\|_A$.

Assessment: non-included

Finite element methods and Galerkin discretizations are not formalized in mathlib. While mathlib has the Lax-Milgram theorem (`Mathlib/Analysis/InnerProductSpace/LaxMilgram.lean`), which is related to the well-posedness of variational problems (a prerequisite for finite element analysis), the actual Galerkin method, its discretization properties, and the Cea lemma (best approximation property) are not present. Searched for "Galerkin", "finite element", "Cea" with no results.

## Statement 32: Theorem (Hellmann-Feynman theorem and group velocity as energy velocity)
For self-adjoint eigenproblems, first-order perturbation theory yields the Hellmann-Feynman theorem. Applied to waveguide modes, the group velocity $d\omega/dk$ can be evaluated via Hellmann-Feynman, yielding a ratio of energy flux to energy density: an "energy velocity".

Assessment: non-included

The Hellmann-Feynman theorem and perturbation theory for eigenvalue problems are not formalized in mathlib. While mathlib has extensive spectral theory for self-adjoint operators, it does not contain perturbation theory (how eigenvalues change under perturbation of the operator). Searched for "Hellmann", "Feynman", "perturbation", "group velocity" with no results. The application to waveguide theory and the energy velocity concept are also absent.
