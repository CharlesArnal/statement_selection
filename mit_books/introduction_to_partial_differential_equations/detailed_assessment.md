# Detailed Assessment: Introduction to Partial Differential Equations Statements in Mathlib

## Statement 1: Proposition 4.0.1 (Superposition Principle)
**Status**: not included
**Explanation**: The superposition principle states that linear combinations of solutions to a linear PDE are again solutions. This is a general, abstract fact about linear operators. While Mathlib has extensive theory of linear maps and vector spaces, the specific notion of a "linear PDE operator" acting on function spaces is not formalized. There is no PDE framework in Mathlib that would express this principle.
**Mathlib references**: None directly applicable. General linear algebra is in `Mathlib/LinearAlgebra/`.

## Statement 2: Proposition 4.0.2 (Inhomogeneous vs homogeneous PDE solutions)
**Status**: not included
**Explanation**: This states that the solution set to an inhomogeneous linear PDE is a coset (affine translate) of the solution set to the corresponding homogeneous PDE. This is a standard fact about affine subspaces of vector spaces. While the abstract algebraic fact is trivially provable in Mathlib's linear algebra library, it is not stated in the context of PDEs. The PDE-specific formulation is absent from Mathlib.
**Mathlib references**: The abstract algebraic structure is captured by `AffineSubspace` in `Mathlib/LinearAlgebra/AffineSpace/`.

## Statement 3: Theorem 7.1 (Divergence Theorem)
**Status**: included
**Explanation**: Mathlib contains a divergence theorem for Bochner integrals on rectangular boxes in $\mathbb{R}^{n+1}$. The theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` states that for a function $f$ continuous on a box $[a,b]$ and differentiable on its interior (except at countably many points), the integral of the divergence equals the sum of integrals over the faces. This is a rigorous version of the divergence theorem, though specialized to boxes rather than general domains with smooth boundaries as stated in the textbook.
**Mathlib references**: `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`). Also includes 2D versions for rectangles.

## Statement 4: Theorem 4.1 (Fourier analysis basics)
**Status**: partially included
**Explanation**: The textbook states $L^2$ convergence of Fourier sine series on $[0,1]$, the Parseval identity, and uniform convergence on compact subintervals for continuous functions. Mathlib has extensive Fourier analysis on the additive circle `AddCircle T`, including the result that Fourier monomials form a Hilbert basis for $L^2$ (`fourierBasis`), the $L^2$ convergence of Fourier series (`hasSum_fourier_series_L2`), and Parseval's identity (`hasSum_sq_fourierCoeff`). However, the specific sine series expansion on $[0,1]$ with Dirichlet boundary conditions (using only sine terms) is not directly available; Mathlib works with the full complex exponential Fourier basis on the circle.
**Mathlib references**: `Mathlib/Analysis/Fourier/AddCircle.lean` (`fourierBasis`, `hasSum_fourier_series_L2`, `hasSum_sq_fourierCoeff`, `span_fourierLp_closure_eq_top`).

## Statement 5: Theorem 1.1 (Uniqueness for heat equation on finite interval)
**Status**: not included
**Explanation**: This is a uniqueness result for the heat equation on a bounded interval under various boundary conditions. Mathlib does not contain any theory of the heat equation, parabolic PDEs, or their well-posedness. There is no formalization of the heat operator $\partial_t - D\partial_x^2$ or its associated boundary value problems.
**Mathlib references**: None.

## Statement 6: Theorem 1.1 (Weak Maximum Principle)
**Status**: not included
**Explanation**: The weak maximum principle for the heat equation states that the maximum of a solution on a spacetime cylinder is attained on the parabolic boundary. This is a fundamental result in parabolic PDE theory. Mathlib has no formalization of parabolic maximum principles. The only maximum-principle-type result in Mathlib is the maximum modulus principle for holomorphic functions, which is a different result for a different class of equations.
**Mathlib references**: None. (The maximum modulus principle for holomorphic functions is in `Mathlib/Analysis/Complex/AbsMax.lean` but this is unrelated.)

## Statement 7: Corollary 1.0.1 (Comparison Principle and Stability)
**Status**: not included
**Explanation**: The comparison principle for the heat equation follows from the weak maximum principle. Since the weak maximum principle is not in Mathlib, neither is this corollary.
**Mathlib references**: None.

## Statement 8: Lemma 1.0.1 (Heat kernel solves the heat equation)
**Status**: not included
**Explanation**: This states that the Gaussian heat kernel $\Gamma_D(t,x) = (4\pi Dt)^{-n/2} \exp(-|x|^2/(4Dt))$ solves the heat equation. While Mathlib has extensive theory of Gaussian functions and their integrals (in `Mathlib/Analysis/SpecialFunctions/Gaussian/`), it does not formalize the heat equation or verify that the Gaussian solves it.
**Mathlib references**: None directly. Gaussian integrals are in `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`.

## Statement 9: Lemma 1.0.2 (Properties of the heat kernel)
**Status**: not included
**Explanation**: Properties of the heat kernel (positivity, total integral equals 1, concentration near the origin) are not in Mathlib. The integral of the Gaussian is computed in Mathlib (`integral_gaussian`), which implicitly gives the normalization, but it is not stated in the context of the heat kernel.
**Mathlib references**: `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` contains the Gaussian integral computation but not in the heat kernel context.

## Statement 10: Lemma 1.0.3 (Approximation to identity for heat kernel)
**Status**: not included
**Explanation**: This states that convolution with the heat kernel converges to the identity as $t \to 0$. Mathlib has some theory of approximate identities (`MeasureTheory.Integral.PeakFunction`) but the heat kernel is not treated as a specific instance of an approximate identity.
**Mathlib references**: `Mathlib/MeasureTheory/Integral/PeakFunction.lean` has general peak function theory but does not specialize to the heat kernel.

## Statement 11: Proposition 1.0.4 (Properties of the heat kernel as approximate identity)
**Status**: not included
**Explanation**: This states that $\Gamma_D(t,\cdot) \to \delta(\cdot)$ in the sense of distributions. Mathlib does not formalize the Dirac delta as a distribution or the heat kernel's convergence to it.
**Mathlib references**: None.

## Statement 12: Proposition 1.1.1 (Differentiating under the integral)
**Status**: included
**Explanation**: Differentiation under the integral sign (Leibniz integral rule) is formalized in Mathlib via the parametric integral results. The main theorem allows differentiation of parameter-dependent integrals under appropriate dominated convergence conditions.
**Mathlib references**: `Mathlib/Analysis/Calculus/ParametricIntegral.lean` (`hasFDerivAt_integral_of_dominated_loc_of_lip`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`), `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`.

## Statement 13: Theorem 1.1 (Solving global Cauchy problem for heat equation)
**Status**: not included
**Explanation**: The existence of solutions to the heat equation initial value problem via convolution with the heat kernel is not in Mathlib. This requires the heat equation framework, which is absent.
**Mathlib references**: None.

## Statement 14: Theorem 1.2 (Duhamel's Principle)
**Status**: not included
**Explanation**: Duhamel's principle provides the solution to the inhomogeneous heat equation as a convolution in time and space. This is a fundamental PDE result that is not in Mathlib.
**Mathlib references**: None.

## Statement 15: Lemma 2.0.2 (Invariance of heat equation under translations and dilations)
**Status**: not included
**Explanation**: Symmetry properties of the heat equation (translation invariance, parabolic scaling invariance) are not formalized in Mathlib.
**Mathlib references**: None.

## Statement 16: Lemma 2.0.3 (Conservation of total thermal energy)
**Status**: not included
**Explanation**: The conservation of $\int u\,dx$ for solutions to the heat equation is not in Mathlib.
**Mathlib references**: None.

## Statement 17: Theorem 3.1 (Uniqueness for Poisson equation)
**Status**: not included
**Explanation**: Uniqueness for the Poisson equation $\Delta u = f$ under various boundary conditions on bounded domains is not in Mathlib. While Mathlib defines the Laplacian operator (`Mathlib/Analysis/InnerProductSpace/Laplacian.lean`) and harmonic functions (`Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`), it does not contain boundary value problem results for the Poisson equation.
**Mathlib references**: None.

## Statement 18: Theorem 4.1 (Mean Value Properties for harmonic functions)
**Status**: not included
**Explanation**: The mean value property for harmonic functions (both spherical and solid mean value formulas) is not in Mathlib. While Mathlib defines harmonic functions (`HarmonicAt` via the vanishing of the Laplacian), the mean value characterization is not formalized. The mean value property for holomorphic functions exists in complex analysis, but not for real harmonic functions in $\mathbb{R}^n$.
**Mathlib references**: `Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean` defines harmonic functions but does not prove the mean value property.

## Statement 19: Theorem 5.1 (Strong Maximum Principle)
**Status**: not included
**Explanation**: The strong maximum principle for harmonic functions (or more generally, functions satisfying the mean value property) is not in Mathlib. Mathlib has a maximum modulus principle for holomorphic functions, but not the maximum principle for real-valued harmonic functions.
**Mathlib references**: None.

## Statement 20: Corollary 5.0.1 (Uniqueness for Dirichlet problem for Laplace equation)
**Status**: not included
**Explanation**: Uniqueness for the Dirichlet problem follows from the strong maximum principle. Since the maximum principle is not in Mathlib, neither is this uniqueness result.
**Mathlib references**: None.

## Statement 21: Lemma 1.0.1 (Fundamental solution is harmonic away from origin)
**Status**: not included
**Explanation**: The fact that the fundamental solution $\Phi(x) = c_n |x|^{2-n}$ (for $n \ge 3$) is harmonic for $x \neq 0$ is not in Mathlib. While Mathlib can express the Laplacian, the explicit computation $\Delta \Phi = 0$ away from the origin is not formalized.
**Mathlib references**: None.

## Statement 22: Theorem 1.1 (Solution to Poisson's equation in $\mathbb{R}^n$)
**Status**: not included
**Explanation**: The existence and uniqueness of solutions to $\Delta u = f$ on $\mathbb{R}^n$ via convolution with the fundamental solution is not in Mathlib.
**Mathlib references**: None.

## Statement 23: Theorem 2.1 (Basic existence theorem for Dirichlet problem)
**Status**: not included
**Explanation**: Existence of solutions to $\Delta u = 0$ with prescribed boundary data on bounded Lipschitz domains is not in Mathlib. This is a deep result in elliptic PDE theory.
**Mathlib references**: None.

## Statement 24: Proposition 2.0.2 (Decomposition of Green's function)
**Status**: not included
**Explanation**: The decomposition of the Green function into the fundamental solution and a corrector term is not in Mathlib. Green's functions for elliptic operators are not formalized.
**Mathlib references**: None.

## Statement 25: Proposition 2.0.3 (Representation formula / Green's identity)
**Status**: not included
**Explanation**: Green's representation formula (expressing a function in terms of its boundary data and the fundamental solution via integration by parts) is not in Mathlib.
**Mathlib references**: None.

## Statement 26: Theorem 2.2 (Representation via Green's function for Poisson equation)
**Status**: not included
**Explanation**: The representation of solutions to the Poisson equation via the Green function is not in Mathlib.
**Mathlib references**: None.

## Statement 27: Theorem 3.1 (Poisson's formula for a ball)
**Status**: not included
**Explanation**: The Poisson integral formula giving the explicit solution to the Dirichlet problem on a ball is not in Mathlib.
**Mathlib references**: None.

## Statement 28: Theorem 4.1 (Harnack's inequality)
**Status**: not included
**Explanation**: Harnack's inequality for harmonic functions is not in Mathlib. This is a fundamental result relating the values of a non-negative harmonic function at different points, and it is not formalized.
**Mathlib references**: None.

## Statement 29: Corollary 4.0.4 (Liouville's theorem for harmonic functions)
**Status**: partially included
**Explanation**: The textbook states Liouville's theorem for real harmonic functions: a harmonic function on $\mathbb{R}^n$ that is bounded from above or below is constant. Mathlib contains Liouville's theorem for complex differentiable (entire) functions: `Differentiable.apply_eq_apply_of_bounded` states that a complex differentiable function with bounded range is constant. The complex version is stronger (bounded entire functions are constant), but the statement for real harmonic functions in $\mathbb{R}^n$ (bounded from one side only) is different and not directly present. The complex version does imply the $n=2$ case via the connection between harmonic and holomorphic functions.
**Mathlib references**: `Mathlib/Analysis/Complex/Liouville.lean` (`Differentiable.apply_eq_apply_of_bounded`, `Differentiable.exists_eq_const_of_bounded`).

## Statement 30: Theorem 1.1 (Basic existence theorem, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 23. Not in Mathlib.
**Mathlib references**: None.

## Statement 31: Proposition 1.0.1 (Green's function decomposition, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 24. Not in Mathlib.
**Mathlib references**: None.

## Statement 32: Proposition 1.0.2 (Representation formula, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 25. Not in Mathlib.
**Mathlib references**: None.

## Statement 33: Theorem 1.1 (Representation formula, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 26. Not in Mathlib.
**Mathlib references**: None.

## Statement 34: Lemma 2.0.1 (Green function for a ball)
**Status**: not included
**Explanation**: The explicit formula for the Green function of a ball in $\mathbb{R}^3$ using the method of images is not in Mathlib.
**Mathlib references**: None.

## Statement 35: Theorem 2.1 (Poisson's formula, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 27. Not in Mathlib.
**Mathlib references**: None.

## Statement 36: Theorem 3.1 (Harnack's inequality, repeated)
**Status**: not included
**Explanation**: Duplicate of Statement 28. Not in Mathlib.
**Mathlib references**: None.

## Statement 37: Corollary 3.0.2 (Liouville's theorem, repeated)
**Status**: partially included
**Explanation**: Duplicate of Statement 29. Complex Liouville's theorem is in Mathlib but the real harmonic version is not.
**Mathlib references**: `Mathlib/Analysis/Complex/Liouville.lean`.

## Statement 38: Theorem 4.1 (d'Alembert's formula)
**Status**: not included
**Explanation**: d'Alembert's formula for the 1+1 dimensional wave equation is not in Mathlib. There is no wave equation theory in Mathlib.
**Mathlib references**: None.

## Statement 39: Corollary 4.0.1 (Wave equation on a half-line)
**Status**: not included
**Explanation**: The extension of d'Alembert's formula to a half-line with Dirichlet boundary conditions is not in Mathlib.
**Mathlib references**: None.

## Statement 40: Proposition 1.0.1 (Spherical averages for wave equation)
**Status**: not included
**Explanation**: The reduction of the 3D wave equation to a 1D problem via spherical averages is not in Mathlib.
**Mathlib references**: None.

## Statement 41: Corollary 1.0.2 (Representation formula for spherical averages)
**Status**: not included
**Explanation**: Not in Mathlib.
**Mathlib references**: None.

## Statement 42: Theorem 1.1 (Kirchhoff's formula)
**Status**: not included
**Explanation**: Kirchhoff's formula for solutions to the 3D wave equation is not in Mathlib. This is a classical representation formula expressing the solution in terms of surface integrals over expanding spheres.
**Mathlib references**: None.

## Statement 43: Corollary 2.1.1 (Lorentz transformations preserve causal character)
**Status**: not included
**Explanation**: The theory of Lorentz transformations and the Minkowski metric is not formalized in Mathlib. There is no special or general relativity framework.
**Mathlib references**: None.

## Statement 44: Proposition 2.2.1 (Null frame decomposition)
**Status**: not included
**Explanation**: Null frames and their decomposition of the Minkowski metric are not in Mathlib.
**Mathlib references**: None.

## Statement 45: Lemma 1.0.2 (Divergence of energy-momentum tensor)
**Status**: not included
**Explanation**: The energy-momentum tensor for the wave equation and its divergence identity are not in Mathlib.
**Mathlib references**: None.

## Statement 46: Corollary 1.0.3 (Divergence-free energy-momentum for wave solutions)
**Status**: not included
**Explanation**: Not in Mathlib. Requires the wave equation framework.
**Mathlib references**: None.

## Statement 47: Theorem 1.1 (Divergence Theorem for wave equation energy currents)
**Status**: not included
**Explanation**: This is a specialized application of the divergence theorem to energy currents associated with the wave equation. While Mathlib has a divergence theorem for boxes (Statement 3), it does not have the wave equation energy current formalism.
**Mathlib references**: None directly applicable.

## Statement 48: Theorem 2.1 (Energy estimates in a cone)
**Status**: not included
**Explanation**: Energy estimates for the wave equation in truncated cones are not in Mathlib. These are fundamental tools in hyperbolic PDE theory.
**Mathlib references**: None.

## Statement 49: Corollary 2.0.4 (Uniqueness for wave equation via finite speed of propagation)
**Status**: not included
**Explanation**: Uniqueness and finite speed of propagation for the wave equation are not in Mathlib.
**Mathlib references**: None.

## Statement 50: Theorem 3.1 (Classification of second order constant-coefficient PDEs)
**Status**: not included
**Explanation**: The classification of second-order constant-coefficient PDEs into elliptic, hyperbolic, and parabolic types via the eigenvalues of the principal symbol matrix is not in Mathlib. While Mathlib has the spectral theory of symmetric matrices, the PDE classification is not formalized.
**Mathlib references**: None.

## Statement 51: Lemma 2.0.1 (Properties of Fourier transform for $L^1$ functions)
**Status**: included
**Explanation**: The fact that the Fourier transform of an $L^1$ function is bounded (with $\|\hat{f}\|_\infty \le \|f\|_{L^1}$) and continuous is in Mathlib. The bound is given by `VectorFourier.norm_fourierIntegral_le_integral_norm`, and continuity is given by `VectorFourier.fourierIntegral_continuous`.
**Mathlib references**: `Mathlib/Analysis/Fourier/FourierTransform.lean` (`VectorFourier.norm_fourierIntegral_le_integral_norm`, `VectorFourier.fourierIntegral_continuous`).

## Statement 52: Theorem 2.1 (Properties of the Fourier transform)
**Status**: partially included
**Explanation**: Some properties of the Fourier transform listed in this theorem are in Mathlib: the interaction with right-translation (`fourierIntegral_comp_add_right`), and the self-adjointness property (`integral_bilin_fourierIntegral_eq_flip`). However, the full list of properties (interaction with derivatives, convolution theorem, etc.) is only partially covered. The Fourier transform of derivatives and the convolution theorem are not fully formalized. The Riemann-Lebesgue lemma ($\hat{f}(\xi) \to 0$ as $|\xi| \to \infty$) is available.
**Mathlib references**: `Mathlib/Analysis/Fourier/FourierTransform.lean` (`VectorFourier.fourierIntegral_comp_add_right`, `VectorFourier.integral_bilin_fourierIntegral_eq_flip`), `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean`.

## Statement 53: Proposition 2.0.2 (Rapid decay of Fourier transforms of smooth compactly supported functions)
**Status**: not included
**Explanation**: The rapid decay of Fourier transforms of $C_c^\infty$ functions is not directly stated in Mathlib in this form. Mathlib has Schwartz space theory and the fact that the Fourier transform maps Schwartz functions to Schwartz functions, but the specific statement about compactly supported smooth functions is not isolated as a lemma.
**Mathlib references**: Schwartz space theory is in `Mathlib/Analysis/Distribution/SchwartzSpace.lean`.

## Statement 54: Proposition 3.0.3 (Fourier transform of a Gaussian)
**Status**: included
**Explanation**: The Fourier transform of a Gaussian is computed in Mathlib. The key result `fourierIntegral_gaussian_pi` gives the Fourier transform of $e^{-\pi b|x|^2}$ as $(1/b)^{n/2} e^{-\pi|\xi|^2/b}$ (suitably interpreted for complex $b$ with positive real part). The result for finite-dimensional inner product spaces is in `fourier_gaussian_innerProductSpace`.
**Mathlib references**: `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` (`fourierIntegral_gaussian_pi`, `fourier_gaussian_innerProductSpace`).

## Statement 55: Lemma 4.0.4 (Interaction of Fourier transform with $L^2$ inner product)
**Status**: included
**Explanation**: The self-adjointness of the Fourier transform ($\langle \hat{f}, g \rangle = \langle f, \hat{g} \rangle$) is formalized in Mathlib as `VectorFourier.integral_fourierIntegral_smul_eq_flip` and related results.
**Mathlib references**: `Mathlib/Analysis/Fourier/FourierTransform.lean` (`VectorFourier.integral_fourierIntegral_smul_eq_flip`, `VectorFourier.integral_bilin_fourierIntegral_eq_flip`).

## Statement 56: Theorem 4.1 (Fourier inversion theorem)
**Status**: included
**Explanation**: The Fourier inversion theorem is fully formalized in Mathlib. The main result `MeasureTheory.Integrable.fourierInv_fourier_eq` states that if $f$ is integrable, $\hat{f}$ is integrable, and $f$ is continuous at $v$, then $\mathcal{F}^{-1}(\mathcal{F}f)(v) = f(v)$. A version for globally continuous $f$ gives $\mathcal{F}^{-1}(\mathcal{F}f) = f$. This matches the textbook statement which assumes $f$ continuous, $f \in L^1$, and $\hat{f} \in L^1$.
**Mathlib references**: `Mathlib/Analysis/Fourier/Inversion.lean` (`MeasureTheory.Integrable.fourierInv_fourier_eq`, `Continuous.fourierInv_fourier_eq`).

## Statement 57: Theorem 4.2 (Plancherel theorem)
**Status**: included
**Explanation**: The Plancherel theorem is formalized in Mathlib. The Fourier transform on $L^2$ is defined as a linear isometry equivalence (`fourierTransformLi`), which immediately gives $\|\hat{f}\|_{L^2} = \|f\|_{L^2}$ (via `norm_fourier_eq`) and inner product preservation $\langle \hat{f}, \hat{g} \rangle = \langle f, g \rangle$ (via `inner_fourier_eq`). The textbook's version, which assumes additional integrability, is a special case.
**Mathlib references**: `Mathlib/Analysis/Fourier/LpSpace.lean` (`MeasureTheory.Lp.fourierTransformLi`, `MeasureTheory.Lp.norm_fourier_eq`, `MeasureTheory.Lp.inner_fourier_eq`).

## Statement 58: Proposition 2.0.1 (Fundamental solution for Schrodinger's equation)
**Status**: not included
**Explanation**: The fundamental solution for the Schrodinger equation and its computation via the Fourier transform are not in Mathlib.
**Mathlib references**: None.

## Statement 59: Lemma 2.0.2 (K verifies free Schrodinger equation)
**Status**: not included
**Explanation**: Not in Mathlib. No Schrodinger equation theory exists.
**Mathlib references**: None.

## Statement 60: Proposition 2.0.3 (Behavior of K*phi as t -> 0)
**Status**: not included
**Explanation**: Not in Mathlib. This is a specific approximate identity result for the Schrodinger kernel.
**Mathlib references**: None.

## Statement 61: Theorem 2.1 (Schrodinger global Cauchy problem)
**Status**: not included
**Explanation**: Existence, uniqueness, and dispersive estimates for the Schrodinger equation are not in Mathlib.
**Mathlib references**: None.

## Statement 62: Proposition 2.0.4 (Preservation of $L^2$ norm for Schrodinger)
**Status**: not included
**Explanation**: The conservation of $L^2$ norm for Schrodinger evolution is not in Mathlib.
**Mathlib references**: None.

## Statement 63: Theorem 1.1 (Euler-Lagrange equation / Principle of Stationary Action)
**Status**: not included
**Explanation**: The Euler-Lagrange equation and the calculus of variations framework are not in Mathlib. While Mathlib has Lagrange multipliers for constrained optimization (`Mathlib/Analysis/Calculus/LagrangeMultipliers.lean`), the variational calculus for field theories (stationary action, Euler-Lagrange PDE) is absent.
**Mathlib references**: None.

## Statement 64: Proposition 2.0.1 (ODE existence/uniqueness for autonomous systems)
**Status**: partially included
**Explanation**: Mathlib contains the Picard-Lindelof theorem for ODEs (`IsPicardLindelof`), which gives local existence and uniqueness of solutions to ODEs with Lipschitz right-hand sides. The textbook's statement about flow maps being diffeomorphisms and satisfying the one-parameter group property is partially addressed: Mathlib proves local existence and uniqueness but does not systematically develop the theory of flow maps as diffeomorphisms or their group properties. The manifold library has some integral curve theory.
**Mathlib references**: `Mathlib/Analysis/ODE/PicardLindelof.lean` (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`), `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`.

## Statement 65: Proposition 2.0.2 (Derivatives w.r.t. flow parameter)
**Status**: not included
**Explanation**: The computation of derivatives of transformed fields with respect to the flow parameter is not in Mathlib. This is part of the calculus of variations / Noether's theorem framework.
**Mathlib references**: None.

## Statement 66: Corollary 2.0.3 (Derivative of Lagrangian w.r.t. flow)
**Status**: not included
**Explanation**: Not in Mathlib. Part of the variational calculus framework that is absent.
**Mathlib references**: None.

## Statement 67: Theorem 3.1 (Energy-momentum tensor is divergence-free)
**Status**: not included
**Explanation**: The derivation of the energy-momentum tensor from a coordinate-invariant Lagrangian and its divergence-free property (a consequence of Noether's theorem applied to spacetime translations) is not in Mathlib.
**Mathlib references**: None.

## Statement 68: Proposition 1.0.1 (Transport equations and ODEs)
**Status**: not included
**Explanation**: The method of characteristics connecting transport equations with ODEs (solutions are constant along characteristic curves) is not in Mathlib.
**Mathlib references**: None.

## Statement 69: Proposition 2.0.1 (Burger's equation is a conservation law)
**Status**: not included
**Explanation**: Burger's equation and the conservation of $L^2$ norm for its solutions are not in Mathlib.
**Mathlib references**: None.

## Statement 70: Proposition 2.0.2 (Burger solutions constant along characteristics)
**Status**: not included
**Explanation**: Not in Mathlib. No theory of characteristics or Burger's equation.
**Mathlib references**: None.

## Statement 71: Proposition 2.0.3 (Burger characteristics are straight lines)
**Status**: not included
**Explanation**: Not in Mathlib.
**Mathlib references**: None.

## Statement 72: Theorem 3.1 (Implicit solution to Burger's equation)
**Status**: not included
**Explanation**: Not in Mathlib.
**Mathlib references**: None.

## Statement 73: Theorem 4.1 (Singularity formation in Burger's equation)
**Status**: not included
**Explanation**: The sharp characterization of singularity formation (blowup occurs if and only if the initial data has a point of strictly decreasing slope) for Burger's equation is not in Mathlib. This is a result in nonlinear hyperbolic PDE theory, which is entirely absent from Mathlib.
**Mathlib references**: None.
